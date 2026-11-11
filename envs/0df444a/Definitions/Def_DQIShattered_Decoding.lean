-- Prove2me | Definitions.Def_DQIShattered_Decoding
-- name    : DQIShattered_Decoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:45.73665+00:00
-- url     : https://prove2.me/theorems/f5bf195d-830f-47c1-a7d3-174a59523797
-- title:
--   The $(B,\gamma,\delta)$-quantum decoding problem, USD measurements and erasures
-- statement:
--   Let $B\in\mathbb F_2^{M\times N}$. The dual code is $C^\perp=\{d\in\mathbb F_2^M: B^{\mathsf T}d=0\}$ (2.2). For $\gamma\in[0,1/2]$, (2.3)–(2.4) define the states
--
--   $$|\psi_{0,\gamma}\rangle=\sqrt{1-\gamma}\,|0\rangle+\sqrt\gamma\,|1\rangle,\qquad |\psi_{1,\gamma}\rangle=\sqrt{1-\gamma}\,|1\rangle+\sqrt\gamma\,|0\rangle,\qquad |\psi_{d,\gamma}\rangle=\bigotimes_{j=1}^M|\psi_{d_j,\gamma}\rangle .$$
--
--   1. A **coherent decoder** is a unitary $U$ on an estimate register $E$ ($M$ qubits), the received register $R$ ($M$ qubits) and a work register $W$ started in $w_0$. Its success on $d$ is the probability $\|\Pi_{E=d}\,U(|0\rangle_E|\psi_{d,\gamma}\rangle_R|w_0\rangle_W)\|^2$ of reading $d$ on $E$.
--   2. $U$ **solves the $(B,\gamma,\delta)$-quantum decoding problem** (Definition 2.2) when its success, averaged over a uniformly random $d\in C^\perp$, is at least $1-\delta$.
--   3. A **USD measurement** for two states $|\psi_0\rangle,|\psi_1\rangle$ (p.14) is a POVM with outcomes "$0$", "$1$" and $\perp$. Outcome "$b$" never occurs on the other state. Its $\perp$ probability under uniform priors is $p_\perp=\frac12\langle\psi_0|E_\perp|\psi_0\rangle+\frac12\langle\psi_1|E_\perp|\psi_1\rangle$.
--   4. $B_S$ **has full row rank** when the rows of $B$ indexed by $S\subseteq\{1,\dots,M\}$ are linearly independent over $\mathbb F_2$.
--   5. Under the erasure law, each coordinate is in $S$ independently with probability $p$. The file also defines the probability, under this law, that $B_S$ is not of full row rank.
--
--   **Formalization Note** States are amplitude vectors on the computational basis $\mathbb F_2^M$. The success probability is averaged over $d\in C^\perp$, as in "for uniformly random $d\in C^\perp$". Unitarity of a decoder is a separate hypothesis wherever the paper says "unitary".
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Definition 2.2, p.5, eqs. (2.2)–(2.4); §3.2, pp.13–14

import Mathlib

namespace DQIShattered

open Finset
open scoped ComplexOrder

/-- An `M`-qubit register, indexed by its computational basis `𝔽₂^M`. -/
abbrev Reg (M : ℕ) := Fin M → ZMod 2

/-- **The dual code** `C^⊥ = {d ∈ 𝔽₂^M : Bᵀ d = 0}` of (2.2) (Zhou, Shutty, Sellke, Jordan,
arXiv:2609.40345, held version sha256 0c7f6fdf…, Definition 2.2, p.5). -/
noncomputable def dualCode {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) : Finset (Reg M) :=
  univ.filter fun d => B.transpose.mulVec d = 0

/-- **The single-qubit states** `|ψ_{0,γ}⟩ = √(1−γ)|0⟩ + √γ|1⟩` and `|ψ_{1,γ}⟩ = √(1−γ)|1⟩ + √γ|0⟩` of (2.3),
p.5, as amplitude vectors on `𝔽₂`: `|ψ_{a,γ}⟩` has amplitude `√(1−γ)` at `a` and `√γ` at `a + 1`. -/
noncomputable def qubitState (a : ZMod 2) (γ : ℝ) : ZMod 2 → ℂ := fun b =>
  if b = a then (Real.sqrt (1 - γ) : ℂ) else (Real.sqrt γ : ℂ)

/-- **The product state** `|ψ_{d,γ}⟩ = ⊗_{j=1}^M |ψ_{d_j,γ}⟩` of (2.4), p.5, as an amplitude vector on
`𝔽₂^M`. -/
noncomputable def psiState {M : ℕ} (d : Reg M) (γ : ℝ) : Reg M → ℂ := fun r =>
  ∏ j, qubitState (d j) γ (r j)

/-- The inner product `⟨ψ|φ⟩ = ∑ᵢ conj(ψᵢ) φᵢ` of two amplitude vectors. -/
noncomputable def ip {ι : Type*} [Fintype ι] (ψ φ : ι → ℂ) : ℂ := ∑ i, star (ψ i) * φ i

/-- The expectation `⟨ψ|E|ψ⟩` of an operator `E` in an (unnormalized) vector `ψ`; for a POVM element and a
unit vector it is the probability of that outcome. -/
noncomputable def expect {ι : Type*} [Fintype ι] (E : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, star (ψ i) * E i j * ψ j

/-- A unit vector: `∑ᵢ |ψᵢ|² = 1`. -/
def IsUnit' {ι : Type*} [Fintype ι] (ψ : ι → ℂ) : Prop := ∑ i, Complex.normSq (ψ i) = 1

/-- **A POVM** with outcomes `O`: positive semidefinite elements summing to the identity. -/
def IsPOVM {ι O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O] (E : O → Matrix ι ι ℂ) : Prop :=
  (∀ o, (E o).PosSemidef) ∧ ∑ o, E o = 1

/-- **An unambiguous state discrimination (USD) measurement** for `|ψ₀⟩, |ψ₁⟩` (p.14): a three-outcome POVM
whose outcome `some b` identifies `b` with certainty and whose outcome `none` is `⊥`. "With certainty" means
that outcome `some b` has probability `0` on the other state: `⟨ψ₁|E_{some 0}|ψ₁⟩ = 0` and
`⟨ψ₀|E_{some 1}|ψ₀⟩ = 0`.

**Formalization Note** The outcome `some false` is "`b = 0`", `some true` is "`b = 1`". -/
def IsUSD {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ₀ ψ₁ : ι → ℂ) (E : Option Bool → Matrix ι ι ℂ) :
    Prop :=
  IsPOVM E ∧ expect (E (some false)) ψ₁ = 0 ∧ expect (E (some true)) ψ₀ = 0

/-- **The `⊥` probability of a USD measurement under uniform priors**,
`p_⊥ = ½ ⟨ψ₀|E_⊥|ψ₀⟩ + ½ ⟨ψ₁|E_⊥|ψ₁⟩` (p.14, (3.20)). -/
noncomputable def pPerp {ι : Type*} [Fintype ι] (ψ₀ ψ₁ : ι → ℂ) (E : Option Bool → Matrix ι ι ℂ) : ℝ :=
  ((expect (E none) ψ₀).re + (expect (E none) ψ₁).re) / 2

/-- **`B_S` has full row rank**: the rows of `B` indexed by `S ⊆ [M]` are linearly independent over `𝔽₂`
(p.14). -/
def FullRowRankOn {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (S : Finset (Fin M)) : Prop :=
  LinearIndependent (ZMod 2) (fun i : S => B i)

/-- **The law of the erased set** `S ⊆ {1, …, M}` of the USD erasure channel (p.14): each coordinate is erased
independently with probability `p`, so `P(S) = p^{|S|} (1 − p)^{M − |S|}`. -/
noncomputable def erasureProb (M : ℕ) (p : ℝ) (S : Finset (Fin M)) : ℝ :=
  p ^ S.card * (1 - p) ^ (M - S.card)

open Classical in
/-- **The probability that `B_S` fails to have full row rank**, `P_S(B_S is not full row rank | B)`, for an
erased set `S` with i.i.d. Bernoulli(`p`) coordinates (proof of Theorem 2.7, p.16). -/
noncomputable def rankFailProb {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (p : ℝ) : ℝ :=
  ∑ S : Finset (Fin M), if FullRowRankOn B S then 0 else erasureProb M p S

/-- **The input of a coherent decoder**: `|0⟩_E ⊗ |ψ_{d,γ}⟩_R ⊗ |w₀⟩_W` on the estimate register `E`
(`M` qubits), the received register `R` (`M` qubits) and a work register `W` started in `w₀`. -/
noncomputable def decoderInput {M : ℕ} {W : Type*} [DecidableEq W] (w₀ : W) (d : Reg M) (γ : ℝ) :
    Reg M × Reg M × W → ℂ := fun t =>
  if t.1 = 0 ∧ t.2.2 = w₀ then psiState d γ t.2.1 else 0

/-- **The success probability of a decoder unitary on the codeword `d`**: the probability
`‖Π_{E = d} U (|0⟩_E ⊗ |ψ_{d,γ}⟩_R ⊗ |w₀⟩_W)‖²` that measuring the estimate register after `U` gives `d`. -/
noncomputable def decoderSuccess {M : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (U : Matrix (Reg M × Reg M × W) (Reg M × Reg M × W) ℂ) (w₀ : W) (γ : ℝ) (d : Reg M) : ℝ :=
  ∑ r : Reg M, ∑ w : W, Complex.normSq ((U.mulVec (decoderInput w₀ d γ)) (d, r, w))

/-- **`U` solves the `(B, γ, δ)`-quantum decoding problem** (Definition 2.2, p.5): for uniformly random
`d ∈ C^⊥`, `U` identifies `d` from `|ψ_{d,γ}⟩` with probability at least `1 − δ`, i.e.
`(1/|C^⊥|) ∑_{d ∈ C^⊥} success(d) ≥ 1 − δ`.

**Formalization Note** A coherent decoder is a unitary on the estimate, received and work registers; its
answer is read on the estimate register. The success probability is averaged over `d ∈ C^⊥`, as in "for
uniformly random `d ∈ C^⊥`", not required for each `d`. Unitarity of `U` is a separate hypothesis wherever the
paper says "unitary". -/
def SolvesDecoding {M N : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (B : Matrix (Fin M) (Fin N) (ZMod 2)) (γ δ : ℝ)
    (U : Matrix (Reg M × Reg M × W) (Reg M × Reg M × W) ℂ) (w₀ : W) : Prop :=
  1 - δ ≤ (∑ d ∈ dualCode B, decoderSuccess U w₀ γ d) / (dualCode B).card

end DQIShattered


