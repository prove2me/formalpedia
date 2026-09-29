-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cceb3895-5c94-5ccd-b0b1-dbc402fef87a

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant.AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant.AlgebraicCurve.TwoChartIntegralModel"

universe u v

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlg mem_chartAlg_iff"
namespace ChartAlgInvariants
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

theorem smul_algebraMap (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    (g : G) (k : K₂) : g • algebraMap K₂ K₁ k = algebraMap K₂ K₁ k := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

theorem smul_algebraMap_base (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    (g : G) (r : R) : g • algebraMap R K₁ r = algebraMap R K₁ r := by
  rw [IsScalarTower.algebraMap_apply R K₂ K₁, smul_algebraMap R K₂ K₁ G]

theorem smul_comm_base (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    (g : G) (r : R) (x : K₁) : g • (r • x) = r • g • x := by
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', smul_algebraMap_base R K₂ K₁ G]

theorem smul_of_mem_adjoin (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    (S₂ : Set K₂) (g : G) {a : K₁}
    (ha : a ∈ Algebra.adjoin R (algebraMap K₂ K₁ '' S₂)) : g • a = a := by
  have h : Algebra.adjoin R (algebraMap K₂ K₁ '' S₂) ≤ (IsScalarTower.toAlgHom R K₂ K₁).range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨s, -, rfl⟩
    exact ⟨s, rfl⟩
  obtain ⟨k, hk⟩ := ((IsScalarTower.toAlgHom R K₂ K₁).mem_range).mp (h ha)
  rw [← hk]
  exact smul_algebraMap R K₂ K₁ G g k

theorem smul_mem_chartAlg (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    (S₂ : Set K₂) (g : G) {x : K₁}
    (hx : x ∈ chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)) :
    g • x ∈ chartAlg R K₁ (algebraMap K₂ K₁ '' S₂) := by
  rw [mem_chartAlg_iff] at hx ⊢
  exact hx.map_of_comp_eq (RingHom.id _) (MulSemiringAction.toRingHom G K₁ g)
    (RingHom.ext fun a => (smul_of_mem_adjoin R K₂ K₁ G S₂ g a.2).symm)

@[reducible] def chartAlgAction (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    (S₂ : Set K₂) :
    MulSemiringAction G ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)) where
  smul g x := ⟨g • (x : K₁), smul_mem_chartAlg R K₂ K₁ G S₂ g x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : K₁))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : K₁))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g (x : K₁) (y : K₁))
  smul_one g := Subtype.ext (smul_one g)
  smul_mul g x y := Subtype.ext (smul_mul' g (x : K₁) (y : K₁))

attribute [local instance] chartAlgAction

private theorem _root_.AlgebraicCurve.TwoChartIntegralModel.ChartAlgInvariants.coe_smul (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    (S₂ : Set K₂) (g : G) (x : ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂))) :
    ((g • x : ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂))) : K₁) = g • (x : K₁) := rfl

p2m_export "AlgebraicCurve.TwoChartIntegralModel.ChartAlgInvariants" "coe_smul"

theorem smulCommClass_base (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    (S₂ : Set K₂) :
    SMulCommClass G R ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)) :=
  ⟨fun g r x => Subtype.ext (by
    rw [coe_smul, Subalgebra.coe_smul, Subalgebra.coe_smul, coe_smul]
    exact smul_comm_base R K₂ K₁ G g r (x : K₁))⟩

theorem smulCommClass_chart (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    (S₂ : Set K₂)
    (ι : ↥(chartAlg R K₂ S₂) →ₐ[R] ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)))
    (hι : ∀ x : ↥(chartAlg R K₂ S₂),
      ((ι x : ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂))) : K₁) = algebraMap K₂ K₁ (x : K₂)) :
    letI : Algebra ↥(chartAlg R K₂ S₂) ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)) :=
      ι.toRingHom.toAlgebra
    SMulCommClass G ↥(chartAlg R K₂ S₂) ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)) := by
  letI : Algebra ↥(chartAlg R K₂ S₂) ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)) :=
    ι.toRingHom.toAlgebra
  refine ⟨fun g a x => Subtype.ext ?_⟩
  change g • (((ι a) * x : ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂))) : K₁) =
    (((ι a) * (g • x) : ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂))) : K₁)
  rw [Subalgebra.coe_mul, Subalgebra.coe_mul, smul_mul', hι, smul_algebraMap R K₂ K₁ G, coe_smul]

theorem isIntegral_adjoin_of_isIntegral_adjoin_image
    (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (S₂ : Set K₂) {x : K₁}
    (hx : IsIntegral ↥(Algebra.adjoin R (algebraMap K₂ K₁ '' S₂)) x) :
    IsIntegral ↥(Algebra.adjoin R S₂) x := by
  have hmap : (Algebra.adjoin R S₂).map (IsScalarTower.toAlgHom R K₂ K₁) =
      Algebra.adjoin R (algebraMap K₂ K₁ '' S₂) := AlgHom.map_adjoin _ _
  have hmem : ∀ b : ↥(Algebra.adjoin R S₂),
      algebraMap K₂ K₁ (b : K₂) ∈ Algebra.adjoin R (algebraMap K₂ K₁ '' S₂) := fun b => by
    rw [← hmap]
    exact Subalgebra.mem_map.mpr ⟨b, b.2, rfl⟩
  let φ : ↥(Algebra.adjoin R S₂) →+* ↥(Algebra.adjoin R (algebraMap K₂ K₁ '' S₂)) :=
    { toFun := fun b => ⟨algebraMap K₂ K₁ (b : K₂), hmem b⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hφ : Function.Surjective φ := by
    rintro ⟨c, hc⟩
    rw [← hmap] at hc
    obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.mp hc
    exact ⟨⟨b, hb⟩, rfl⟩
  have hcomp : (algebraMap ↥(Algebra.adjoin R (algebraMap K₂ K₁ '' S₂)) K₁).comp φ =
      algebraMap ↥(Algebra.adjoin R S₂) K₁ := RingHom.ext fun _ => rfl
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts p).mpr (Polynomial.map_surjective φ hφ p)) hp
  refine ⟨q, hqm, ?_⟩
  rw [← hcomp, ← Polynomial.eval₂_map, hq]
  exact hpx

theorem isInvariant_chart (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    [Algebra.IsInvariant K₂ K₁ G] (S₂ : Set K₂)
    (ι : ↥(chartAlg R K₂ S₂) →ₐ[R] ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)))
    (hι : ∀ x : ↥(chartAlg R K₂ S₂),
      ((ι x : ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂))) : K₁) = algebraMap K₂ K₁ (x : K₂)) :
    letI : Algebra ↥(chartAlg R K₂ S₂) ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)) :=
      ι.toRingHom.toAlgebra
    Algebra.IsInvariant ↥(chartAlg R K₂ S₂) ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)) G := by
  letI : Algebra ↥(chartAlg R K₂ S₂) ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)) :=
    ι.toRingHom.toAlgebra
  refine ⟨fun x hx => ?_⟩
  have hx' : ∀ g : G, g • (x : K₁) = (x : K₁) := fun g => congrArg Subtype.val (hx g)
  have hy := Algebra.IsInvariant.isInvariant (A := K₂) (x : K₁) hx'
  obtain ⟨y, hy⟩ := hy
  have hxint : IsIntegral ↥(Algebra.adjoin R S₂) (x : K₁) :=
    isIntegral_adjoin_of_isIntegral_adjoin_image R K₂ K₁ S₂ ((mem_chartAlg_iff R K₁).mp x.2)
  rw [← hy] at hxint
  have hyint : y ∈ chartAlg R K₂ S₂ :=
    (mem_chartAlg_iff R K₂).mpr (hxint.tower_bot (algebraMap K₂ K₁).injective)
  refine ⟨⟨y, hyint⟩, Subtype.ext ?_⟩
  change ((ι ⟨y, hyint⟩ : ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂))) : K₁) = (x : K₁)
  rw [hι]
  exact hy

theorem faithfulSMul_chart (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    (S₂ : Set K₂) (hf : FaithfulSMul G K₁)
    (hfr : IsFractionRing ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)) K₁) :
    FaithfulSMul G ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)) := by
  haveI := hf
  haveI := hfr
  refine ⟨fun {g₁ g₂} h => toRingHom_injective G K₁ ?_⟩
  refine IsLocalization.ringHom_ext (nonZeroDivisors ↥(chartAlg R K₁ (algebraMap K₂ K₁ '' S₂)))
    (S := K₁) ?_
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
  exact congrArg Subtype.val (h a)

end AlgebraicCurve.TwoChartIntegralModel.ChartAlgInvariants

end

open AlgebraicCurve.TwoChartIntegralModel.ChartAlgInvariants in
theorem solution
    (R : Type u) [CommRing R]
    (K₂ : Type u) [Field K₂] [Algebra R K₂]
    (K₁ : Type u) [Field K₁] [Algebra R K₁] [Algebra K₂ K₁] [IsScalarTower R K₂ K₁]
    (G : Type v) [Group G] [MulSemiringAction G K₁] [SMulCommClass G K₂ K₁]
    [Algebra.IsInvariant K₂ K₁ G]
    (S₂ : Set K₂) (S₁ : Set K₁) (hS : algebraMap K₂ K₁ '' S₂ = S₁)
    (ι : ↥(chartAlg R K₂ S₂) →ₐ[R] ↥(chartAlg R K₁ S₁))
    (hι : ∀ x : ↥(chartAlg R K₂ S₂), ((ι x : ↥(chartAlg R K₁ S₁)) : K₁) = algebraMap K₂ K₁ (x : K₂)) :
    ∃ (_ : MulSemiringAction G ↥(chartAlg R K₁ S₁)),

      (∀ (g : G) (x : ↥(chartAlg R K₁ S₁)), ((g • x : ↥(chartAlg R K₁ S₁)) : K₁) = g • (x : K₁)) ∧

      SMulCommClass G R ↥(chartAlg R K₁ S₁) ∧

      (letI : Algebra ↥(chartAlg R K₂ S₂) ↥(chartAlg R K₁ S₁) := ι.toRingHom.toAlgebra
       SMulCommClass G ↥(chartAlg R K₂ S₂) ↥(chartAlg R K₁ S₁) ∧
         Algebra.IsInvariant ↥(chartAlg R K₂ S₂) ↥(chartAlg R K₁ S₁) G) ∧

      (FaithfulSMul G K₁ → IsFractionRing ↥(chartAlg R K₁ S₁) K₁ → FaithfulSMul G ↥(chartAlg R K₁ S₁)) := by
  subst hS
  exact ⟨chartAlgAction R K₂ K₁ G S₂, fun g x => rfl, smulCommClass_base R K₂ K₁ G S₂,
    ⟨smulCommClass_chart R K₂ K₁ G S₂ ι hι, isInvariant_chart R K₂ K₁ G S₂ ι hι⟩,
    fun hf hfr => faithfulSMul_chart R K₂ K₁ G S₂ hf hfr⟩

end S_AlgebraicCurve_TwoChartIntegralModel_exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant (solution)
