-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HypsNonvacuous
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HypsNonvacuous
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:41:38.806544+00:00
-- url     : https://prove2.me/theorems/4a089dfe-3635-451e-a35a-ff07e91d640c
-- title:
--   Hyps Nonvacuous
-- statement:
--   Definitions and structural lemmas for Hyps Nonvacuous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HypsNonvacuous.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
namespace PI.ScRefExists.UnitaryGroupMassFormula
variable (I : Formalism.MainNotions.S.AutInst)
theorem hA_zero_left (y : VA I) : hA I 0 y = 0 := by
  simp [hA, Formalism.UG.hform]
theorem zmod_one_of_mem {c : I.E ⊗[I.F] Af I.F} (h : c ∈ IntAf I.F I.E) : ZMod' I 1 c := by
  unfold ZMod'
  exact ⟨c, h, by simp⟩
theorem mL_one : mL I 1 = I.Lf := by
  unfold mL
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨x, hx, rfl⟩
    simpa using hx
  · intro x hx
    exact Submodule.subset_span ⟨x, hx, by simp⟩
theorem ite_mem_int {p : Prop} [Decidable p] (x : I.E ⊗[I.F] Af I.F) (hx : x ∈ IntAf I.F I.E) :
    (if p then x else 0) ∈ IntAf I.F I.E := by
  split_ifs
  · exact hx
  · exact zero_mem _
def frameOne (r k : ℕ) (e f : Fin r → Fin I.n → I.E)
    (he : ∀ a, InAt I 1 1 (incl I (e a)) ∧ InAt I 1 1 (incl I (f a))) : RefData I 1 r k e f where
  e0 := fun _ => 0
  f0 := fun _ => 0
  z0 := 0
  bw := fun _ => 0
  bwd := fun _ => 0
  ew := 0
  vectorsInLattice := ⟨fun _ => ⟨zero_mem _, zero_mem _⟩, zero_mem _, fun _ => ⟨zero_mem _, zero_mem _⟩⟩
  basisApprox := by
    intro a
    constructor
    · obtain ⟨c, hc, hm⟩ := (he a).1
      exact ⟨c, hc, by rw [zero_sub, smul_neg]; exact neg_mem hm⟩
    · obtain ⟨c, hc, hm⟩ := (he a).2
      exact ⟨c, hc, by rw [zero_sub, smul_neg]; exact neg_mem hm⟩
  gramIntegral := by
    intro a b
    refine ⟨zmod_one_of_mem I ?_, zmod_one_of_mem I ?_, zmod_one_of_mem I ?_⟩
    · rw [hA_zero_left]; exact zero_mem _
    · rw [hA_zero_left]; exact zero_mem _
    · rw [hA_zero_left, zero_sub]; exact neg_mem (ite_mem_int I 1 (one_mem _))
  formsAtZero := by
    refine ⟨zmod_one_of_mem I ?_, fun a => ⟨zmod_one_of_mem I ?_, zmod_one_of_mem I ?_⟩⟩
    · rw [hA_zero_left, zero_add]; exact one_mem _
    · rw [hA_zero_left]; exact zero_mem _
    · rw [hA_zero_left]; exact zero_mem _
  weightVectorsIntegral := by
    intro i
    refine ⟨zmod_one_of_mem I ?_, zmod_one_of_mem I ?_, fun a => ⟨zmod_one_of_mem I ?_,
      zmod_one_of_mem I ?_, zmod_one_of_mem I ?_, zmod_one_of_mem I ?_⟩⟩ <;>
      (rw [hA_zero_left]; exact zero_mem _)
  ew_idem := by simp
  ew_orth := by simp
  ew_int := zero_mem _
  ew_full := by
    intro y hy
    rw [map_zero, sub_zero, sub_zero, one_smul, mL_one]
    exact hy
  bw_w := fun _ => by simp
  bwd_w := fun _ => by simp
  bw_dual := by
    intro i j
    apply zmod_one_of_mem
    rw [hA_zero_left, zero_sub]
    exact neg_mem (ite_mem_int I 0 (zero_mem _))
  latticeSpan := by
    intro y hy
    apply Submodule.mem_sup_right
    rw [mL_one]
    exact hy
def TargetTwo : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E), 2 ≤ g →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) →
    I.n = 2 * r + k + 1 →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) →
    Nonempty (RefData I g r k e f)
end PI.ScRefExists.UnitaryGroupMassFormula
end


