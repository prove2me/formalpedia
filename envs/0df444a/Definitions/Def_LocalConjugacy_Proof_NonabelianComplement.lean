-- Prove2me | Definitions.Def_LocalConjugacy_Proof_NonabelianComplement
-- name    : LocalConjugacy_Proof_NonabelianComplement
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:44:39.087591+00:00
-- url     : https://prove2.me/theorems/29199fd1-1af9-4285-ab67-ad314afc221e
-- title:
--   The cocycle attached to a complement
-- statement:
--   The complement projection, its continuity and multiplication law, the coefficient conjugation action, and the inverse cocycle associated to a complement of a normal subgroup.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_CocycleZorn
import Definitions.Def_LocalConjugacy_Proof_CocycleProducts
import Definitions.Def_LocalConjugacy_Proof_FiniteCoefficientSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInvarianceSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInjectivity
import Definitions.Def_LocalConjugacy_Proof_CocycleRebase
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
import Definitions.Def_LocalConjugacy_Proof_ProfiniteHall
import Definitions.Def_LocalConjugacy_Proof_ActionProductTopology
import Definitions.Def_LocalConjugacy_Proof_HallCohomology
import Definitions.Def_LocalConjugacy_Proof_SupersolvableRestriction
import Definitions.Def_LocalConjugacy_Proof_NilpotentCoefficients

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
namespace NonabelianComplement
open AbelianComplement

section Algebra
variable {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
  (hc : Subgroup.IsComplement' N H)

/-- The order of the two factors matters for nonabelian coefficients. -/
theorem projection_mul_reverse (x y : G) :
    projection N H hc (x * y) =
      MulAut.conjNormal x (projection N H hc y) * projection N H hc x := by
  let nx := projection N H hc x
  let ny := projection N H hc y
  let hx : H := (hc.equiv x).2
  let hy : H := (hc.equiv y).2
  have hxe : (nx : G) * hx = x := hc.equiv_fst_mul_equiv_snd x
  have hye : (ny : G) * hy = y := hc.equiv_fst_mul_equiv_snd y
  have he : ((MulAut.conjNormal x ny * nx : N) : G) * (hx * hy : H) = x * y := by
    change (x * ny * x⁻¹ * nx) * (hx * hy) = x * y
    calc
      (x * ny * x⁻¹ * nx) * (hx * hy) = x * ny * x⁻¹ * ((nx : G) * hx) * hy := by group
      _ = x * y := by rw [hxe, ← hye]; group
  have hf := congrArg (fun z => (hc.equiv z).1) he
  rw [show ((MulAut.conjNormal x ny * nx : N) : G) * (hx * hy : H) =
      hc.equiv.symm (MulAut.conjNormal x ny * nx, hx * hy) from rfl,
    hc.equiv.apply_symm_apply] at hf
  exact hf.symm





end Algebra

section Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
  (N H : Subgroup G) [N.Normal] (hc : Subgroup.IsComplement' N H)
  (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))

include hN hH in
theorem continuous_projection : Continuous (projection N H hc) := by
  letI := profinite_closed_subgroup N hN
  letI := profinite_closed_subgroup H hH
  have hm : Continuous hc.equiv.symm :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have he : Continuous hc.equiv :=
    (hm.isClosedMap.isQuotientMap hm hc.equiv.symm.surjective).continuous_iff.mpr
      (continuous_id.congr (fun x => (hc.equiv.apply_symm_apply x).symm))
  exact continuous_fst.comp he

@[instance_reducible] def conjugationAction (N : Subgroup G) [N.Normal] : MulDistribMulAction G N :=
  MulDistribMulAction.compHom N (MulAut.conjNormal : G →* MulAut N)

attribute [local instance] conjugationAction

instance conjugationContinuousSMul (N : Subgroup G) [N.Normal] : ContinuousSMul G N where
  continuous_smul := (((continuous_fst : Continuous (Prod.fst : G × N → G)).mul
    (continuous_subtype_val.comp continuous_snd)).mul continuous_fst.inv).subtype_mk _

noncomputable def inverseCocycle (K : Subgroup G) : Cocycle (J := K) (N := N) ⊤ where
  toFun x := (projection N H hc (x : K))⁻¹
  continuous_toFun := ((continuous_projection N H hc hN hH).comp
    (continuous_subtype_val.comp continuous_subtype_val)).inv
  map_mul x y := by
    change (projection N H hc ((x : G) * y))⁻¹ = _
    rw [projection_mul_reverse N H hc, mul_inv_rev, ← map_inv]
    rfl

include hc hN hH





end Topology
end NonabelianComplement
end LocalConjugacy

end LocalConjugacy.Proof

end


