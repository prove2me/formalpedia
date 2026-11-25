-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T04:25:38.483009+00:00
-- url     : https://prove2.me/theorems/e0fce6a2-84a6-5c63-9ad3-527aed14b6f3
-- title:
--   Formal Degree Haar Quotient
-- statement:
--   Definitions and structural lemmas for Formal Degree Haar Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/FormalDegreeHaarQuotient.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_cloud
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_node
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_sign_cloud
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_sign_node
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_cloud
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_node
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_cloud
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_node


set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient
open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open PI.BesselMapUniq (psiGen)
abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
variable {k r : ℕ}
def IsClosedMatGroup (U : Set (Mat k r)) : Prop :=
  IsClosed U ∧ (1 : Mat k r) ∈ U ∧ (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧
    ∀ a ∈ U, IsUnit a.det ∧ a⁻¹ ∈ U
def IsHaarOn (U : Set (Mat k r)) (μ : Measure (Mt k r)) : Prop :=
  μ {x | Matrix.of x ∉ U} = 0 ∧ (∀ a ∈ U, μ.map (lmulM a) = μ) ∧
    (∀ C : Set (Mt k r), IsCompact C → (∀ x ∈ C, Matrix.of x ∈ U) → μ C < ⊤) ∧ μ ≠ 0
def IsQuotRep (G : Set (Mat k r)) (μG μS ν : Measure (Mt k r)) : Prop :=
  ν {x | Matrix.of x ∉ G} = 0 ∧
    ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = ∫⁻ g, (∫⁻ s, f (lmulM (Matrix.of s) g) ∂μS) ∂ν
def leviW (k r : ℕ) (s : Mat k r) : Mat k r := fun i j =>
  if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then s i j
  else if i = j then 1 else 0
section Twist
variable {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
def twist (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) (s : Mat k r) : Wp →L[ℂ] Wp :=
  psiGen k r z c ((leviW k r s)⁻¹ * s) • π (leviW k r s)
def twistInv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) (s : Mat k r) : Wp →L[ℂ] Wp :=
  (psiGen k r z c ((leviW k r s)⁻¹ * s))⁻¹ • π (leviW k r s)⁻¹
def IsEquivariant (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) (φ : Mat k r → Wp) : Prop :=
  ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ g ∈ UH (Hpk k r),
    φ (h * n * g) = psiGen k r z c n • π h (φ g)
def sectionL2NormSq (ν : Measure (Mt k r)) (φ : Mat k r → Wp) : ℝ≥0∞ :=
  ∫⁻ g, ‖φ (Matrix.of g)‖ₑ ^ 2 ∂ν
def IsSquareIntegrableEquivariant (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) (ν : Measure (Mt k r)) (φ : Mat k r → Wp) : Prop :=
  IsEquivariant k r z c π φ ∧ AEStronglyMeasurable (fun g : Mt k r => φ (Matrix.of g)) ν ∧
    sectionL2NormSq ν φ < ⊤
end Twist
section Period
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
def coefNormSq (μ : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (w : H) : ℝ≥0∞ :=
  ∫⁻ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ ^ 2 ∂μ
def IsFormalDegreeAt (μ : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (w : H) (d : ℝ) : Prop :=
  w ≠ 0 ∧ 0 < d ∧ coefNormSq μ σ w = ENNReal.ofReal (‖w‖ ^ 4 / d)
def formalDegreeAt (μ : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (w : H) : ℝ :=
  ‖w‖ ^ 4 / (coefNormSq μ σ w).toReal
def periodIntegrand (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Wp →L[ℂ] Wp)) (w v : H) (s : Mt k r) :
    Wp →L[ℂ] Wp :=
  ⟪v, σ (Matrix.of s) w⟫_ℂ • twistInv k r z c π (Matrix.of s)
def period (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (w v : H) :
    Wp →L[ℂ] Wp :=
  ∫ s, periodIntegrand k r z c σ π w v s ∂μS
end Period
def BesselPeriodNeZero : Prop :=
  ∀ (k r : ℕ) (hk : 2 ≤ k), Even k →
    ∀ (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (u : Fin k → ℝ),
      Formalism.QuantumDeterminants.IsHCParam (DecreasingNodeGaps.param r k (by omega) v b) →
      DecreasingNodeGaps.Interlaces r k (DecreasingNodeGaps.param r k (by omega) v b) u →
      DecreasingNodeGaps.Parity r k (DecreasingNodeGaps.param r k (by omega) v b) u →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
      PI.UpqRep.IsDSHpk k r (DecreasingNodeGaps.sign r k (by omega)) (DecreasingNodeGaps.param r k (by omega) v b) σ →
    ∀ (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (π : Mat k r → (Wp →L[ℂ] Wp)),
      PI.UpqRep.IsHCTypeW k r z u π →
    ∀ (c : Fin r → ℂ), (∀ a, c a ≠ 0) →
    ∀ (μS : Measure (Mt k r)), IsHaarOn (Sset k r z) μS →
    ∀ x : H, PI.UpqRep.IsLowUnitH k r (DecreasingNodeGaps.sign r k (by omega))
        (DecreasingNodeGaps.param r k (by omega) v b) σ x →
      ∃ g ∈ UH (Hpk k r), ∃ y ∈ UH (Hpk k r),
        Integrable (periodIntegrand k r z c σ π (σ g x) (σ y x)) μS ∧
          period k r z c σ π μS (σ g x) (σ y x) ≠ 0
theorem measurable_lmulM (a : Mat k r) : Measurable (lmulM a : Mt k r → Mt k r) := by
  apply Continuous.measurable
  exact continuous_const.matrix_mul continuous_id
example : IsHaarOn ({1, -1} : Set (Mat k r))
    (Measure.dirac (Matrix.of.symm (1 : Mat k r) : Mt k r) + Measure.dirac (Matrix.of.symm (-1 : Mat k r) : Mt k r)) := by
  refine ⟨?_, ?_, fun C _ _ => measure_lt_top _ _, ?_⟩
  · rw [Measure.add_apply, Measure.dirac_apply, Measure.dirac_apply,
      Set.indicator_of_notMem, Set.indicator_of_notMem, add_zero]
    · exact fun h => h (Or.inr rfl)
    · exact fun h => h (Or.inl rfl)
  · intro a ha
    rw [Measure.map_add _ _ (measurable_lmulM a), Measure.map_dirac' (measurable_lmulM a),
      Measure.map_dirac' (measurable_lmulM a)]
    have e1 : lmulM a (Matrix.of.symm (1 : Mat k r) : Mt k r) = Matrix.of.symm a := mul_one a
    have e2 : lmulM a (Matrix.of.symm (-1 : Mat k r) : Mt k r) = Matrix.of.symm (-a) := mul_neg_one a
    rw [e1, e2]
    rcases ha with rfl | rfl
    · rfl
    · rw [neg_neg]
      exact add_comm _ _
  · intro h
    have := congrArg (fun m : Measure (Mt k r) => m Set.univ) h
    simp at this
example (G : Set (Mat k r)) (μ : Measure (Mt k r)) (hμ : IsHaarOn G μ) :
    IsQuotRep G μ (Measure.dirac (Matrix.of.symm (1 : Mat k r) : Mt k r)) μ := by
  refine ⟨hμ.1, fun f _ => ?_⟩
  congr 1
  funext g
  rw [lintegral_dirac]
  exact congrArg f (one_mul (Matrix.of g)).symm
end GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient
end


