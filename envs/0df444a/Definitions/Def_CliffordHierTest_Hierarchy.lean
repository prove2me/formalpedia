-- Prove2me | Definitions.Def_CliffordHierTest_Hierarchy
-- name    : CliffordHierTest_Hierarchy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:55.90129+00:00
-- url     : https://prove2.me/theorems/ba813643-8ac1-46a2-8054-25d084d58868
-- title:
--   Pauli polynomials $\mathcal P^{(k)}$, the Clifford hierarchy $\mathcal C^{(k)}$ and the Clifford fidelity $\mathcal F_{\mathcal C^{(k)}}$
-- statement:
--   Let $\mathcal U(d^n)$ be the $n$-qudit unitaries. The **Pauli polynomials** are
--   $$\mathcal P^{(0)}=\{e^{i\theta}I:\theta\in[0,2\pi)\},\qquad \mathcal P^{(k)}=\{U\in\mathcal U(d^n):\partial_hU\in\mathcal P^{(k-1)}\ \text{for all }h\in\mathbb F_d^{2n}\}\quad(k\ge1).$$
--   The **Clifford hierarchy** is
--   $$\mathcal C^{(0)}=\{I\},\qquad \mathcal C^{(1)}=\{\tau^pW_h:p\in\mathbb Z_D,\ h\in\mathbb F_d^{2n}\},\qquad \mathcal C^{(k)}=\{U\in\mathcal U(d^n):U\mathcal C^{(1)}U^*\subseteq\mathcal C^{(k-1)}\}\quad(k\ge2),$$
--   where $D=2d$ if $d=2$ and $D=d$ otherwise. For a set $\mathcal S$ of unitaries, the **fidelity** of $U$ with $\mathcal S$ is $\max_{V\in\mathcal S}|\langle V,U\rangle|^2$; in particular the **degree-$k$ Clifford fidelity** is
--   $$\mathcal F_{\mathcal C^{(k)}}(U)=\max_{V\in\mathcal C^{(k)}}|\langle V,U\rangle|^2,$$
--   and $\mathcal F_{\mathcal P^{(k)}}$ is defined in the same way.
--
--   $\mathcal C^{(1)}$ is the Pauli group, $\mathcal C^{(2)}$ the Clifford group, and $\mathcal C^{(3)}$, the level tested in the main theorem, contains the $T$ gate.
--
--   **Formalization Note** Both families are sets of elements of `Matrix.unitaryGroup`, defined by recursion on $k$; $\mathcal P^{(0)}$ uses $\theta\in\mathbb R$ (the same set). $\mathcal C^{(1)}$ is the published `cyclicPauliGroup d n`. The fidelity is the supremum (`sSup`) of the values $|\langle V,U\rangle|^2$, $V\in\mathcal S$, which equals the printed maximum for these sets.
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §2.2.2 Definitions 9, 10 and the display after Proposition 11, p.6; (1), p.2

import Mathlib
import Definitions.Def_CliffordHierTest_PauliNorm

open scoped Matrix

namespace CliffordHierTest

/-!
# Pauli polynomials, the Clifford hierarchy and the Clifford fidelity

Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256
610d53a6…), §2.2.2, p.6 (Definitions 9 and 10, the display after Proposition 11); (1), p.2.

**Formalization Note.** Both families are sets of elements of `Matrix.unitaryGroup`, i.e. subsets
of `𝒰(dⁿ)`, defined by recursion on the level. `𝒫^{(0)}` is the set of `e^{iθ} I` with `θ ∈ ℝ`,
the same set as with the printed `θ ∈ [0, 2π)`. `𝒞^{(1)}` is the published finite Pauli group
`cyclicPauliGroup d n = {τ^p W_h : 0 ≤ p < D, h ∈ 𝔽_d^{2n}}` (GNW21 conventions; `phaseModulus d`
is `D` for prime `d`). `𝒞^{(k)}` for `k ≥ 2` is `{U | U P U* ∈ 𝒞^{(k-1)} for all P ∈ 𝒞^{(1)}}`.

The fidelity `ℱ_{𝒮}(U) = max_{V ∈ 𝒮} |⟨V, U⟩|²` of (1) is the supremum (`sSup` in `ℝ`) of the set
of values `|⟨V, U⟩|²`, `V ∈ 𝒮`. For the levels used here that set is nonempty (it contains the
value at `V = I`) and bounded by `1` for unitary `U`, and the supremum is attained, so `sSup` is the
printed maximum.
-/

open QAlgorithms.Papers.Independent.Extend50.P30

variable (d n : ℕ)

/-- The `n`-qudit unitaries `𝒰(dⁿ)`. -/
abbrev QuditUnitary [NeZero d] := Matrix.unitaryGroup (ResidueRegister d n) ℂ

/-- Definition 10 (p.6): `𝒞^{(1)} = {τ^p W_h | p ∈ ℤ_D, h ∈ 𝔽_d^{2n}}`, as a set of unitaries. -/
def pauliGroupSet [NeZero d] : Set (QuditUnitary d n) :=
  {U | (U : QuditOperator d n) ∈ cyclicPauliGroup d n}

/-- Definition 10 (p.6): the Clifford hierarchy, `𝒞^{(0)} = {I}`, `𝒞^{(1)}` the Pauli group, and
`𝒞^{(k)} = {U ∈ 𝒰(dⁿ) | U 𝒞^{(1)} U* ⊆ 𝒞^{(k-1)}}` for `k ≥ 2`. -/
def cliffordLevel [NeZero d] : ℕ → Set (QuditUnitary d n)
  | 0 => {1}
  | 1 => pauliGroupSet d n
  | k + 2 => {U | ∀ P ∈ pauliGroupSet d n, U * P * star U ∈ cliffordLevel (k + 1)}

/-- Definition 9 (p.6): Pauli polynomials, `𝒫^{(0)} = {e^{iθ} I}` and, for `k ≥ 1`,
`𝒫^{(k)} = {U ∈ 𝒰(dⁿ) | ∂_h U ∈ 𝒫^{(k-1)} for all h ∈ 𝔽_d^{2n}}`. -/
def pauliPoly [NeZero d] : ℕ → Set (QuditUnitary d n)
  | 0 => {U | ∃ θ : ℝ, (U : QuditOperator d n) = Complex.exp (θ * Complex.I) • (1 : QuditOperator d n)}
  | k + 1 => {U | ∀ h : DiscretePhaseSpace d n,
      ∃ V ∈ pauliPoly k, (V : QuditOperator d n) = pauliDeriv h (U : QuditOperator d n)}

variable {d n}

/-- The fidelity `max_{V ∈ 𝒮} |⟨V, U⟩|²` of a matrix `U` with a set `𝒮` of unitaries, as the
supremum of the values. -/
noncomputable def setFid [NeZero d] (S : Set (QuditUnitary d n)) (U : QuditOperator d n) : ℝ :=
  sSup ((fun V : QuditUnitary d n => ‖hsInner (V : QuditOperator d n) U‖ ^ 2) '' S)

/-- (1), p.2: the degree-`k` Clifford fidelity `ℱ_{𝒞^{(k)}}(U) = max_{V ∈ 𝒞^{(k)}} |⟨V, U⟩|²`. -/
noncomputable def cliffordFid [NeZero d] (k : ℕ) (U : QuditOperator d n) : ℝ :=
  setFid (cliffordLevel d n k) U

/-- The display after Proposition 11 (p.6): `ℱ_{𝒫^{(k)}}(U) = max_{V ∈ 𝒫^{(k)}} |⟨V, U⟩|²`. -/
noncomputable def polyFid [NeZero d] (k : ℕ) (U : QuditOperator d n) : ℝ :=
  setFid (pauliPoly d n k) U

end CliffordHierTest


