-- Prove2me | Definitions.Def_QuantumStateIdentity321_Schur_Model
-- name    : QuantumStateIdentity321_Schur_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T23:18:22.587658+00:00
-- url     : https://prove2.me/theorems/c63b0775-8d37-4b88-98d5-1ae3e87d56d8
-- title:
--   Pure input states, squared fidelity, the relaxed identity promise, copies of each input and two-outcome testers
-- statement:
--   A pure state of local dimension $d$ is a unit vector $|\psi\rangle\in\mathbb C^d$. The fidelity of two pure states is $F(\psi,\varphi)=|\langle\psi|\varphi\rangle|^2$.
--
--   For $n$ input states $|\psi_1\rangle,\dots,|\psi_n\rangle$ and an overlap parameter $\varepsilon$ (Definition 1.1, QSI$^\varepsilon_n$ under two-sided relaxation):
--
--   - a **yes instance** has $|\langle\psi_i|\psi_j\rangle|^2\ge1-\varepsilon$ for all pairs of distinct indices $i,j\in[n]$;
--   - a **no instance** has at least one pair of distinct indices $a,b\in[n]$ with $|\langle\psi_a|\psi_b\rangle|^2\le\varepsilon$.
--
--   A tester that uses $m$ copies of each input state receives the product state $|\Psi\rangle=\bigotimes_{i=1}^n|\psi_i\rangle^{\otimes m}$ on $nm$ registers of dimension $d$, and outputs accept or reject. Its acceptance probability is $\langle\Psi|A|\Psi\rangle$ for its accept effect $A$, an operator with $0\le A\le I$. The tester is fixed before the unknown states are chosen.
--
--   **Formalization Note** Indices are `Fin n` (label $i$ is the source's $i+1$). The registers are indexed by pairs (state, copy), and the joint space is written in the computational basis `(Fin n × Fin m) → Fin d`, where the product vector has amplitude $\prod_{(i,k)}\psi_i(w(i,k))$. A quantum algorithm on the copies (unitaries, ancillas, intermediate measurements, classical randomness) is represented by the accept effect of its overall two-outcome measurement, positive semidefinite with $I-A$ positive semidefinite; every algorithm induces such an effect and every such effect is a measurement, so this changes no instance. Normalization $\|\psi_i\|=1$ is a hypothesis where the states are quantified.
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Definition 1.1 (PDF/printed p.2) and the copy model of Theorem 1.3 (pp.3–4), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Mathlib

/-!
# Relaxed quantum state identity: pure inputs, promise, copies and testers

Shih-Han Hung, Ming-Hsien Tsai, *Efficient Quantum State Identity Testing*, STOC 2027
submission #321 (October 2026), Definition 1.1 (p.2) and the copy model of Theorem 1.3 (pp.3–4).

Indices `Fin n` stand for the source's `[n] = {1, …, n}` (label `i : Fin n` is the source's
`i + 1`). A tester using `m` copies of each of the `n` input states acts on the registers indexed
by `Fin n × Fin m`, one `d`-dimensional register per copy; the joint input is the product vector
`⊗ᵢ |ψᵢ⟩^{⊗ m}`, written in the computational basis `(Fin n × Fin m) → Fin d`. Any quantum
algorithm on these copies (unitaries, ancillas, intermediate measurements, classical randomness)
ends in accept/reject, so its acceptance probability is `⟨Ψ, A Ψ⟩` for an effect `0 ≤ A ≤ I`;
conversely every such effect is a two-outcome measurement. A `Tester` is that effect.
-/

namespace QuantumStateIdentity321.Schur

open Matrix
open scoped ComplexOrder

/-- A pure state of local dimension `d`: a vector of `ℂᵈ` with the Euclidean inner product
(normalization `‖ψ‖ = 1` is imposed where states are quantified). -/
abbrev State (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Definition 1.1, p.2: the (squared) fidelity `F(ψ, φ) = |⟨ψ|φ⟩|²` of two pure states. -/
noncomputable def fidelity {d : ℕ} (ψ φ : State d) : ℝ :=
  Complex.normSq (inner ℂ ψ φ)

/-- Definition 1.1, p.2, yes instance: `|⟨ψᵢ|ψⱼ⟩|² ≥ 1 − ε` for all pairs of distinct indices. -/
def IsYesInstance {n d : ℕ} (ε : ℝ) (ψ : Fin n → State d) : Prop :=
  ∀ i j : Fin n, i ≠ j → 1 - ε ≤ fidelity (ψ i) (ψ j)

/-- Definition 1.1, p.2, no instance: some pair of distinct indices `a ≠ b` has
`|⟨ψₐ|ψ_b⟩|² ≤ ε`. -/
def IsNoInstance {n d : ℕ} (ε : ℝ) (ψ : Fin n → State d) : Prop :=
  ∃ a b : Fin n, a ≠ b ∧ fidelity (ψ a) (ψ b) ≤ ε

/-- Computational-basis labels of the registers holding `m` copies of each of `n` states:
register `(i, k)` is the `k`-th copy of `|ψᵢ⟩`. -/
abbrev CopyBasis (n m d : ℕ) := (Fin n × Fin m) → Fin d

/-- The joint input `⊗ᵢ |ψᵢ⟩^{⊗ m}` given to a tester using `m` copies of each input state:
the amplitude of the basis word `w` is `∏_{(i,k)} ψᵢ(w(i,k))`. -/
noncomputable def copiesVec {n d : ℕ} (m : ℕ) (ψ : Fin n → State d) : CopyBasis n m d → ℂ :=
  fun w => ∏ p : Fin n × Fin m, ψ p.1 (w p)

/-- A quantum tester using `m` copies of each of `n` states of local dimension `d`: the accept
effect `A` of its final two-outcome measurement, with `0 ≤ A ≤ I`. It is fixed before the
unknown input states are chosen. -/
structure Tester (n m d : ℕ) where
  /-- The accept effect on the joint copy space. -/
  effect : Matrix (CopyBasis n m d) (CopyBasis n m d) ℂ
  /-- `0 ≤ A`. -/
  effect_nonneg : effect.PosSemidef
  /-- `A ≤ I`, so that reject has the effect `I − A ≥ 0`. -/
  effect_le_one : (1 - effect).PosSemidef

/-- The probability that the tester accepts on input states `ψ₁, …, ψₙ`, given `m` copies of
each: the Born probability `⟨Ψ|A|Ψ⟩` for `Ψ = ⊗ᵢ |ψᵢ⟩^{⊗ m}`. -/
noncomputable def acceptProb {n m d : ℕ} (T : Tester n m d) (ψ : Fin n → State d) : ℝ :=
  (star (copiesVec m ψ) ⬝ᵥ (T.effect *ᵥ copiesVec m ψ)).re

/-- The constant tester accepting with effect `0` (never accepts): witnesses that `Tester` is
inhabited, so quantifying over testers is not vacuous. -/
def Tester.reject (n m d : ℕ) : Tester n m d where
  effect := 0
  effect_nonneg := Matrix.PosSemidef.zero
  effect_le_one := by
    rw [sub_zero]
    exact Matrix.PosSemidef.one

end QuantumStateIdentity321.Schur


