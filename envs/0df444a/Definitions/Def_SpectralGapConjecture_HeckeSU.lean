-- Prove2me | Definitions.Def_SpectralGapConjecture_HeckeSU
-- name    : SpectralGapConjecture_HeckeSU
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-13T02:01:49.780984+00:00
-- url     : https://prove2.me/theorems/c93e8035-7b43-41ea-b142-dd3baee0ecea
-- title:
--   $SU(d)$, its Haar measure, the Hecke operator and the spectral gap property
-- statement:
--   This file fixes the objects in which the spectral gap conjecture is stated.
--
--   1. **The group.** $SU(d)$ is the group of complex $d\times d$ matrices $U$ with $U^*U = UU^* = I$ and $\det U = 1$, with the topology inherited from $\mathbb C^{d\times d}$ and its Borel $\sigma$-algebra. It is shown to be a compact topological group.
--   2. **Haar measure.** $\mu_d$ (`haarSU d`) is the Haar measure on $SU(d)$ normalized so that $\mu_d(SU(d)) = 1$; it is a left-invariant Borel probability measure.
--   3. **Hecke operator.** For a group $G$ and $g = (g_1,\dots,g_n) \in G^n$, the operator $z_g$ acts on $f : G \to \mathbb C$ by
--   $$
--   (z_g f)(x) = \sum_{j=1}^{n}\bigl(f(g_j x) + f(g_j^{-1}x)\bigr).
--   $$
--   4. **Spectral gap.** For a measure $\mu$ on $G$, the tuple $g$ *has a spectral gap* if there is $\varepsilon > 0$ such that for every square-integrable $f : G \to \mathbb C$ with $\int_G f\,d\mu = 0$,
--   $$
--   \operatorname{Re}\int_G \overline{f(x)}\,(z_g f)(x)\,d\mu(x) \;\le\; (2n - \varepsilon)\int_G |f(x)|^2\,d\mu(x).
--   $$
--
--   When $\mu$ is a Haar probability measure, $z_g$ is a bounded self-adjoint operator on $L^2(G,\mu)$ that preserves the mean-zero subspace $L^2_0$, and condition 4 says exactly that the supremum $\lambda_1$ of its spectrum on $L^2_0$ is strictly less than $2n$, the eigenvalue of the constant functions.
--
--   **Formalization Note.** Mean zero is the same as orthogonality to constants because $\mu$ is finite. The spectral gap is one-sided (an upper bound on $\lambda_1$), following Fisher (2006) and Bourgain–Gamburd (2012).
-- source:
--   Wikipedia, "Spectral gap conjecture", section Statement (https://en.wikipedia.org/wiki/Spectral_gap_conjecture); operator and spectral gap as defined in Bourgain–Gamburd, A spectral gap theorem in SU(d), arXiv:1108.6264, §0, p. 1, and Fisher, Out(F_n) and the spectral gap conjecture, arXiv:math/0601050, §1, p. 1

import Mathlib

open MeasureTheory

namespace SpectralGapConjecture

/-- The special unitary group `SU(d)`: complex `d × d` matrices `U` with `U⋆ U = U U⋆ = 1`
and `det U = 1`, with the subspace topology inherited from `Matrix (Fin d) (Fin d) ℂ`. -/
abbrev SU (d : ℕ) := Matrix.specialUnitaryGroup (Fin d) ℂ

/-- `SU(d)` carries its Borel σ-algebra. -/
noncomputable instance (d : ℕ) : MeasurableSpace (SU d) := borel _

instance (d : ℕ) : BorelSpace (SU d) := ⟨rfl⟩

instance (d : ℕ) : IsTopologicalGroup (SU d) where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.matrix_conjTranspose

theorem isClosed_SU (d : ℕ) : IsClosed (SU d : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  have h1 : IsClosed {A : Matrix (Fin d) (Fin d) ℂ |
      (star A * A = 1 ∧ A * star A = 1) ∧ A.det = 1} := by
    refine ((isClosed_eq ?_ continuous_const).inter (isClosed_eq ?_ continuous_const)).inter
      (isClosed_eq ?_ continuous_const)
    · exact continuous_id.matrix_conjTranspose.matrix_mul continuous_id
    · exact continuous_id.matrix_mul continuous_id.matrix_conjTranspose
    · exact continuous_id.matrix_det
  have h2 : (SU d : Set (Matrix (Fin d) (Fin d) ℂ)) =
      {A : Matrix (Fin d) (Fin d) ℂ | (star A * A = 1 ∧ A * star A = 1) ∧ A.det = 1} :=
    Set.ext fun A => by
      rw [SetLike.mem_coe, Matrix.mem_specialUnitaryGroup_iff]
      exact Iff.rfl
  rw [h2]
  exact h1

instance (d : ℕ) : CompactSpace (SU d) := by
  refine isCompact_iff_compactSpace.mp ?_
  have hK : IsCompact (Set.univ.pi fun _ : Fin d => Set.univ.pi fun _ : Fin d =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset (isClosed_SU d) ?_
  intro A hA
  simp only [Set.mem_pi, Set.mem_univ, Metric.mem_closedBall, dist_zero_right, forall_const]
  intro i j
  exact entry_norm_bound_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup hA) i j

/-- The normalized Haar measure on `SU(d)`: the unique left-invariant regular Borel
probability measure. -/
noncomputable def haarSU (d : ℕ) : Measure (SU d) := Measure.haarMeasure ⊤

instance (d : ℕ) : (haarSU d).IsHaarMeasure := by
  unfold haarSU; infer_instance

instance (d : ℕ) : IsProbabilityMeasure (haarSU d) := ⟨by
  unfold haarSU
  simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (SU d)))⟩

/-- The averaging (Hecke) operator attached to `g₁, …, gₙ` in a group `G`, acting on functions
`f : G → ℂ` by `(z f)(x) = ∑ⱼ (f (gⱼ x) + f (gⱼ⁻¹ x))`. -/
noncomputable def heckeOperator {G : Type*} [Group G] {n : ℕ} (g : Fin n → G) (f : G → ℂ) : G → ℂ :=
  fun x => ∑ j, (f (g j * x) + f ((g j)⁻¹ * x))

/-- The Hecke operator of `g₁, …, gₙ` has a spectral gap on `L²(G, μ)`: there is `ε > 0` such
that for every square-integrable `f` with `∫ f dμ = 0` (i.e. `f ⊥` constants),
`Re ⟨z f, f⟩ ≤ (2n - ε) ‖f‖²`. Equivalently, the supremum `λ₁` of the spectrum of the
self-adjoint operator `z` on `L²₀(G, μ)` satisfies `λ₁ < 2n`. -/
def HasSpectralGap {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) {n : ℕ}
    (g : Fin n → G) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ f : G → ℂ, MemLp f 2 μ → ∫ x, f x ∂μ = 0 →
    (∫ x, starRingEnd ℂ (f x) * heckeOperator g f x ∂μ).re ≤
      (2 * n - ε) * ∫ x, ‖f x‖ ^ 2 ∂μ

end SpectralGapConjecture


