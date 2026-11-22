-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_ExactBlock
-- name    : QuantumKtSoI_Supplement_ExactBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:37:43.387807+00:00
-- url     : https://prove2.me/theorems/8e429e27-d662-456d-be27-c2ad00520452
-- title:
--   Circuits, exact and real-encoded blocks (Definition 9.4), universal gate sets and computable entries
-- statement:
--   A **circuit** over a gate set $\mathcal G_h$ on $w$ wires is a finite sequence of gates of $\mathcal G_h$, each applied to an ordered tuple of distinct wires; it acts on $(\mathbb C^2)^{\otimes w}$ as the product of its gates, the first gate being applied first. Let $J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. For a gate $g$ of arity $a$, an **ancilla state** is $\chi=Q|s\rangle$ for $s\in\{0,1\}^b$ and a circuit $Q$ over $\mathcal G_h$ on $b\ge0$ wires.
--
--   1. An **exact $\mathcal G_h$-block** for $g$ consists of an ancilla state $\chi$ on $b$ wires, a real $\varphi$ and a circuit $V$ over $\mathcal G_h$ on $a+b$ wires with $V(|v\rangle\otimes\chi)=e^{i\varphi}(g|v\rangle)\otimes\chi$ for every $v\in\{0,1\}^a$.
--   2. Writing $e^{i\varphi}g=A_g+iB_g$ with real matrices and $\widetilde W_g=A_g\otimes I+B_g\otimes J$ (the last qubit is the flag), a **real-encoded $\mathcal G_h$-block** for $g$ consists of $\chi$ on $b$ wires, a real $\varphi$ and a circuit $V$ over $\mathcal G_h$ on $a+1+b$ wires with $V(u\otimes\chi)=(\widetilde W_gu)\otimes\chi$ for every $u\in(\mathbb C^2)^{\otimes(a+1)}$.
--
--   A finite gate set is **universal** if for every $k\ge1$, every unitary $U$ on $k$ qubits and every $\varepsilon>0$ there are a circuit $C$ over it on the same $k$ qubits and a phase $\lambda$ with $\|C-\lambda U\|\le\varepsilon$. A complex number is **computable** if a deterministic Turing machine, given a positive integer $r$, returns rational real and imaginary parts with error at most $2^{-r}$.
--
--   These notions are the hypotheses of the gate-set comparisons (Theorems D.45, D.47, D.55) and the content of Theorem 9.6.
--
--   **Formalization Note** Vectors are functions on bit strings; the operator-norm bound is written as $\|(C-\lambda U)v\|^2\le\varepsilon^2\|v\|^2$ for every $v$; a phase is a complex number of modulus $1$; "a deterministic Turing machine returns" is Mathlib's `Computable`.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), circuits and Definition 9.4, p.119; universal gate sets and computable numbers, p.120

import Mathlib
import Definitions.Def_QuantumKtSoI_Supplement_GMachine

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- A vector of `(ℂ²)^{⊗w}` in the computational basis. -/
abbrev Vec (w : ℕ) : Type := (Fin w → Bool) → ℂ

/-- A **circuit** over a gate set `H` on `w` wires (p.119 of Myrisiotis, *Failure of Symmetry of
Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…): a
finite sequence of gates of `H`, each applied to an ordered tuple of wires among the `w` wires,
listed in the order of application. -/
abbrev Circ (H : GateLib) (w : ℕ) : Type := List ((g : H.ι) × (Fin (H.arity g) → Fin w))

/-- Each gate of the circuit is applied to *distinct* wires (p.119). -/
def Circ.Distinct {H : GateLib} {w : ℕ} (c : Circ H w) : Prop := ∀ p ∈ c, Function.Injective p.2

/-- The basis string `z` with the bits on the wires `wires` replaced by `ζ`. -/
def overwrite {w a : ℕ} (z : Fin w → Bool) (wires : Fin a → Fin w) (ζ : Fin a → Bool) : Fin w → Bool :=
  fun q => if h : ∃ i, wires i = q then ζ h.choose else z q

/-- The action of the gate `g` on the wires `wires`:
`(gψ)(z) = Σ_ζ g[z|_wires, ζ] ψ(z with ζ on the wires)`. -/
def applyGate (H : GateLib) {w : ℕ} (g : H.ι) (wires : Fin (H.arity g) → Fin w) (ψ : Vec w) : Vec w :=
  fun z => ∑ ζ : Fin (H.arity g) → Bool, H.amp g (fun i => z (wires i)) ζ * ψ (overwrite z wires ζ)

/-- A circuit acts on `(ℂ²)^{⊗w}` as the product of its gates, the first gate of the sequence being
applied first (p.119). -/
def Circ.act {H : GateLib} {w : ℕ} (c : Circ H w) (ψ : Vec w) : Vec w :=
  c.foldl (fun v p => applyGate H p.1 p.2 v) ψ

/-- The basis vector `|s⟩`. -/
def ket {b : ℕ} (s : Fin b → Bool) : Vec b := fun z => if z = s then 1 else 0

/-- The tensor product `ψ ⊗ χ` on `a + b` wires, `ψ` on the first `a` wires. -/
def tensor {a b : ℕ} (ψ : Vec a) (χ : Vec b) : Vec (a + b) :=
  fun z => ψ (fun i => z (Fin.castAdd b i)) * χ (fun j => z (Fin.natAdd a j))

/-- **Definition 9.4** (Blocks, p.119), first item: the gate `g` of arity `a` (given by its matrix)
has an **exact `H`-block**: an ancilla state `χ = Q|s⟩` on `b ≥ 0` wires (`s ∈ {0,1}^b`, `Q` a circuit
over `H` on `b` wires), a real `φ`, and a circuit `V` over `H` on `a + b` wires such that
`V(|v⟩ ⊗ χ) = e^{iφ}(g|v⟩) ⊗ χ` for every `v ∈ {0,1}^a`. -/
def ExactBlock (H : GateLib) {a : ℕ} (g : (Fin a → Bool) → (Fin a → Bool) → ℂ) : Prop :=
  ∃ (b : ℕ) (s : Fin b → Bool) (Q : Circ H b) (φ : ℝ) (V : Circ H (a + b)),
    Q.Distinct ∧ V.Distinct ∧ ∀ v : Fin a → Bool,
      V.act (tensor (ket v) (Q.act (ket s))) =
        tensor (fun o => Complex.exp (φ * Complex.I) * g o v) (Q.act (ket s))

/-- The entry `J[f', f]` of `J = (0 −1; 1 0)`, so that `J|0⟩ = |1⟩` and `J|1⟩ = −|0⟩` (p.119). -/
def Jentry (f' f : Bool) : ℝ :=
  if f' = true ∧ f = false then 1 else if f' = false ∧ f = true then -1 else 0

/-- `W̃_g = A_g ⊗ I + B_g ⊗ J` (Definition 9.4, p.119), where `e^{iφ}g = A_g + iB_g` with real
matrices `A_g, B_g`: a matrix on `a + 1` qubits whose last qubit is the flag, applied to `u`. -/
def realEnc {a : ℕ} (g : (Fin a → Bool) → (Fin a → Bool) → ℂ) (φ : ℝ) (u : Vec (a + 1)) : Vec (a + 1) :=
  fun z' => ∑ z : Fin (a + 1) → Bool,
    (((Complex.exp (φ * Complex.I) * g (fun i => z' i.castSucc) (fun i => z i.castSucc)).re *
          (if z' (Fin.last a) = z (Fin.last a) then 1 else 0) +
        (Complex.exp (φ * Complex.I) * g (fun i => z' i.castSucc) (fun i => z i.castSucc)).im *
          Jentry (z' (Fin.last a)) (z (Fin.last a)) : ℝ) : ℂ) * u z

/-- **Definition 9.4** (Blocks, p.119), second item: the gate `g` of arity `a` has a
**real-encoded `H`-block**: an ancilla state `χ = Q|s⟩` on `b` wires, a real `φ`, and a circuit `V`
over `H` on `a + 1 + b` wires, wire `a + 1` being the flag, such that
`V(u ⊗ χ) = (W̃_g u) ⊗ χ` for every `u ∈ (ℂ²)^{⊗(a+1)}`. -/
def RealBlock (H : GateLib) {a : ℕ} (g : (Fin a → Bool) → (Fin a → Bool) → ℂ) : Prop :=
  ∃ (b : ℕ) (s : Fin b → Bool) (Q : Circ H b) (φ : ℝ) (V : Circ H (a + 1 + b)),
    Q.Distinct ∧ V.Distinct ∧ ∀ u : Vec (a + 1),
      V.act (tensor u (Q.act (ket s))) = tensor (realEnc g φ u) (Q.act (ket s))

/-- A finite gate set is **universal** (p.120): for every integer `k ≥ 1`, every unitary `U` on `k`
qubits and every `ε > 0` there are a circuit `C` over it on the same `k` qubits, with no further
qubits, and a phase `λ` with `‖C − λU‖ ≤ ε` in operator norm.

**Formalization Note** The operator-norm bound is written as `‖(C − λU)v‖² ≤ ε²‖v‖²` for every
vector `v`, with Euclidean norms as sums of squared moduli; a phase is a complex number of modulus
one. -/
def GateLib.Universal (L : GateLib) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ U : Matrix (Fin k → Bool) (Fin k → Bool) ℂ, U ∈ Matrix.unitaryGroup (Fin k → Bool) ℂ →
    ∀ ε : ℝ, 0 < ε → ∃ C : Circ L k, C.Distinct ∧ ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ v : Vec k,
      (∑ z, ‖C.act v z - lam * U.mulVec v z‖ ^ 2) ≤ ε ^ 2 * ∑ z, ‖v z‖ ^ 2

/-- A real number is **computable** (p.120): a deterministic Turing machine, given a positive
integer `r`, returns a rational within `2^{−r}` of it; no running-time bound is included.

**Formalization Note** "A deterministic Turing machine returns" is Mathlib's `Computable`; the
rational returned on `r` is `(f r).1 / ((f r).2 + 1)`. -/
def ComputableReal (x : ℝ) : Prop :=
  ∃ f : ℕ → ℤ × ℕ, Computable f ∧ ∀ r : ℕ, |x - ((f r).1 : ℝ) / (((f r).2 : ℝ) + 1)| ≤ 1 / 2 ^ r

/-- A complex number is **computable** (p.120): rational real and imaginary parts with error at most
`2^{−r}` are returned on input `r`. -/
def ComputableComplex (z : ℂ) : Prop := ComputableReal z.re ∧ ComputableReal z.im

/-- All entries of all gates of the gate set are computable (Theorem 9.6, p.120). -/
def GateLib.ComputableEntries (L : GateLib) : Prop :=
  ∀ (g : L.ι) (o i : Fin (L.arity g) → Bool), ComputableComplex (L.amp g o i)

end QuantumKtSoI.Supplement


