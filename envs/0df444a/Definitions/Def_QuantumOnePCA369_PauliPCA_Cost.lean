-- Prove2me | Definitions.Def_QuantumOnePCA369_PauliPCA_Cost
-- name    : QuantumOnePCA369_PauliPCA_Cost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:44.404868+00:00
-- url     : https://prove2.me/theorems/5e2e946c-8187-49e6-b1e1-7d4de0f5d480
-- title:
--   Unit-cost real RAM: charged primitives on the tick-counting monad
-- statement:
--   Running times in this mission are tick counts of explicit programs in the unit-cost real RAM of §2 (p. 5), built on the published tick-counting monad `Timed` (a value together with a natural-number cost; `bind` adds costs).
--
--   1. One primitive step (one tick): a real, complex, $\mathbb F_2$ or $\mathbb Z/4$ arithmetic operation, a square root, a logarithm, a ceiling, a comparison, or an array read or write.
--   2. A loop over a finite index set charges the cost of every iteration plus one tick per iteration; an accumulation $\sum_i f(i)$ charges each term plus one addition; a sequential fold charges each step plus one tick.
--   3. Matrix sums, scalar multiples, conjugate transposes, products and matrix–vector products are written as such loops of scalar steps, so a $d\times e$ by $e\times f$ product costs $\Theta(def)$.
--   4. The only non-scalar primitive is the exact eigensolver (spectral chooser) on a $d\times d$ matrix, charged $d^3+1$. The spectral extension $g(A)=V\operatorname{diag}(g(\mu))V^\dagger$ of a scalar map and the spectral norm of a Hermitian matrix (largest absolute eigenvalue) are computed from one eigensolver call plus charged loops.
--
--   The cubic charge is a chosen polynomial cost envelope for the idealized eigensolver: the paper omits numerical details of spectral computations (p. 5), and its bounds only use $\mathrm{poly}(d)$. No bit-complexity or numerical-stability claim is made.
--
--   **Formalization Note** No cost is ever charged as a closed-form formula: every tick comes from a primitive step inside the program's actual loops.
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 5, §2 ('we omit numerical details regarding standard spectral computations in the real RAM model'); reuses the published definition MITMSynthesis.Timed

import Mathlib
import Definitions.Def_MITMSynthesis_Timed
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic

namespace QuantumOnePCA369.PauliPCA

open MITMSynthesis

/-! Unit-cost real RAM (§2, p. 5) on top of the published tick-counting monad `Timed`.
Every scalar real/complex/𝔽₂/ℤ₄ arithmetic operation, `√`, `log`, `⌈·⌉`, comparison, and array
read or write is one call of `op` (one tick); loops charge every iteration's own cost plus one tick
per iteration; the only non-scalar primitive is the exact eigensolver `eighC`, charged `d³ + 1`
on a `d × d` input (§2 omits the numerical details of spectral computations). -/

/-- One unit-cost primitive step returning `a`. -/
def op {α : Type} (a : α) : Timed α := ⟨a, 1⟩

/-- A loop over a finite index set whose iterations are independent: the results are tabulated
and the cost is the sum over iterations of (body cost + one loop step). -/
def tab {ι α : Type} [Fintype ι] (f : ι → Timed α) : Timed (ι → α) :=
  ⟨fun i => (f i).val, ∑ i, ((f i).cost + 1)⟩

/-- An accumulation loop `∑_i f i`: each iteration costs its body plus one addition. -/
def sumC {ι β : Type} [Fintype ι] [AddCommMonoid β] (f : ι → Timed β) : Timed β :=
  ⟨∑ i, (f i).val, ∑ i, ((f i).cost + 1)⟩

/-- A sequential left fold over a list, one loop step per element. -/
def foldC {α β : Type} (f : β → α → Timed β) : List α → β → Timed β
  | [], b => pure b
  | a :: as, b => do
      let b' ← f b a
      let _ ← op ()
      foldC f as b'

/-- A loop computing `∀ i, f i` over a finite index set (all iterations executed). -/
def allC {ι : Type} [Fintype ι] (f : ι → Timed Bool) : Timed Bool :=
  ⟨decide (∀ i, (f i).val = true), ∑ i, ((f i).cost + 1)⟩

/-- Linear scan for the least `i ∈ {0, …, N}` with `ok i`, defaulting to `0` if there is none. -/
def findFirstC {N : ℕ} (ok : Fin (N + 1) → Bool) : Timed (Fin (N + 1)) :=
  foldC (fun (acc : Option (Fin (N + 1))) (i : Fin (N + 1)) =>
      op (match acc with
        | some j => some j
        | none => if ok i then some i else none))
    (List.finRange (N + 1)) none >>= fun r => op (r.getD 0)

/-- Entrywise sum of two matrices, one addition per entry. -/
def matAddC {ι κ : Type} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℂ) : Timed (Matrix ι κ ℂ) :=
  tab fun i => tab fun j => op (A i j + B i j)

/-- Entrywise difference of two matrices. -/
def matSubC {ι κ : Type} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℂ) : Timed (Matrix ι κ ℂ) :=
  tab fun i => tab fun j => op (A i j - B i j)

/-- Scalar multiple of a matrix, one multiplication per entry. -/
def smulMatC {ι κ : Type} [Fintype ι] [Fintype κ] (c : ℂ) (A : Matrix ι κ ℂ) :
    Timed (Matrix ι κ ℂ) :=
  tab fun i => tab fun j => op (c * A i j)

/-- Conjugate transpose, one read/conjugation per entry. -/
def conjTransposeC {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    Timed (Matrix κ ι ℂ) :=
  tab fun j => tab fun i => op (star (A i j))

/-- Schoolbook matrix product: one multiplication per term and one addition per term. -/
def matMulC {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ] (A : Matrix ι κ ℂ)
    (B : Matrix κ μ ℂ) : Timed (Matrix ι μ ℂ) :=
  tab fun i => tab fun j => sumC fun l => op (A i l * B l j)

/-- Matrix–vector product. -/
def mulVecC {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) (v : κ → ℂ) :
    Timed (ι → ℂ) :=
  tab fun i => sumC fun l => op (A i l * v l)

/-- The spectral primitive: exact eigenvalues and eigenvector columns of a `d × d` matrix from the
chooser `ch`, charged `d³ + 1` (a polynomial cost envelope for an idealized eigensolver). -/
def eighC (ch : SpectralChooser) {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    Timed ((Fin d → ℝ) × Matrix (Fin d) (Fin d) ℂ) :=
  ⟨ch.eig d A, d ^ 3 + 1⟩

/-- Spectral extension `g(A) = V diag(g(μ)) V†` of a scalar map `g : ℝ → ℝ` to a Hermitian
matrix, computed from one call of the spectral primitive and two charged matrix products. -/
def funCalcC (ch : SpectralChooser) {d : ℕ} (g : ℝ → ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
    Timed (Matrix (Fin d) (Fin d) ℂ) := do
  let e ← eighC ch A
  let gμ ← tab fun i => op (g (e.1 i))
  let W ← tab fun i => tab fun j => op (e.2 i j * (gμ j : ℂ))
  let Vh ← conjTransposeC e.2
  matMulC W Vh

/-- The Schatten-∞ norm of a Hermitian matrix as the largest absolute eigenvalue, computed from one
call of the spectral primitive and a linear scan. -/
def opNormC (ch : SpectralChooser) {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Timed ℝ := do
  let e ← eighC ch A
  foldC (fun (acc : ℝ) (i : Fin d) => op (max acc |e.1 i|)) (List.finRange d) 0

end QuantumOnePCA369.PauliPCA


