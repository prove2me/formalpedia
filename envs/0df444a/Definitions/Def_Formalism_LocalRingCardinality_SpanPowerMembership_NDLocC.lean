-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:53:43.962833+00:00
-- url     : https://prove2.me/theorems/ee1870b7-aa61-50ca-a720-0b431e2e3fb6
-- title:
--   NDLoc C
-- statement:
--   Definitions and structural lemmas for NDLoc C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocC.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_jE_mem_86ded92f8610

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω]
variable [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l)
omit [IsAlgClosure E Ω] [Algebra E Ω] [NumberField E] [Field E] in

def resQ (σ : GQ l) : Ω ≃ₐ[ℚ] Ω :=
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  AlgHom.restrictNormal' ((σ.restrictScalars ℚ : PadicAlgCl l ≃ₐ[ℚ] PadicAlgCl l) :
    PadicAlgCl l →ₐ[ℚ] PadicAlgCl l) Ω
omit [IsAlgClosure E Ω] [Algebra E Ω] [NumberField E] [Field E] in
theorem j_resQ (σ : GQ l) (x : Ω) : j (resQ j σ x) = σ (j x) := by
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  exact AlgHom.restrictNormal_commutes _ Ω x
def resE (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) : G E Ω :=
  AlgEquiv.ofRingEquiv (f := (resQ j σ).toRingEquiv) fun x => j.injective (by
    show j (resQ j σ (algebraMap E Ω x)) = _
    rw [j_resQ]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ (jE_mem j x))
theorem j_resE (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) (x : Ω) :
    j (resE j σ hσ x) = σ (j x) := j_resQ j σ x
variable {j} {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
include hj in
theorem resE_mem (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) :
    resE j σ hσ ∈ Dec (F := E) A := by
  have hiso : ∀ y : PadicAlgCl l, ‖σ y‖ = ‖y‖ := fun y => by
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
    first
      | (simp only [spectralNorm, minpoly.algEquiv_eq]; done)
      | exact (spectralNorm.aut_isom σ y).symm
      | (unfold spectralNorm; rw [minpoly.algEquiv_eq])
      | (unfold spectralNorm; congr 1; exact minpoly.algEquiv_eq σ y)
  have key : ∀ x, resE j σ hσ x ∈ A ↔ x ∈ A := fun x => by
    rw [hj, hj, j_resE, hiso]
  show resE j σ hσ ∈ MulAction.stabilizer _ A
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← key,
    ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
def rHom : ↥(KwF (E := E) j).fixingSubgroup →* ↥(Dec (F := E) A) where
  toFun σ := ⟨resE j σ.1 σ.2, resE_mem hj σ.1 σ.2⟩
  map_one' := Subtype.ext (AlgEquiv.ext fun x => j.injective
    ((j_resE j _ (1 : ↥(KwF (E := E) j).fixingSubgroup).2 x).trans rfl))
  map_mul' σ τ := Subtype.ext (AlgEquiv.ext fun x => j.injective ((j_resE j _ (σ * τ).2 x).trans
    ((congrArg (σ : GQ l) (j_resE j _ τ.2 x)).symm.trans (j_resE j _ σ.2 _).symm)))
end Formalism.BasicNotions.Examples₂.LB


