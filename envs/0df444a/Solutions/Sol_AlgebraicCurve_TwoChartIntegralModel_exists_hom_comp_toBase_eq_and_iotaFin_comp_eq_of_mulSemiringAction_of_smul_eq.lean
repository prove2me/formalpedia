-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ba24fcdd-a7da-50c8-956a-ca08b4335a38

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"
p2m_open "AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq.AlgebraicCurve.TwoChartIntegralModel"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlg mem_chartAlg_iff coe_chartIncl chartAlgFin chartAlgInf chartAlgMid inclFin inclInf fFin fInf ιFin ιInf toBase ιFin_toBase ιInf_toBase"
namespace SemilinearTwist
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

section Rings

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F]
variable {Γ : Type v} [Group Γ] [MulSemiringAction Γ R] [MulSemiringAction Γ F]

theorem smul_mem_adjoin (hΓF : ∀ (s : Γ) (r : R), s • algebraMap R F r = algebraMap R F (s • r))
    (s : Γ) (S : Set F) (hS : ∀ x ∈ S, s • x ∈ S) {x : F} (hx : x ∈ Algebra.adjoin R S) :
    s • x ∈ Algebra.adjoin R S := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin (hS y hy)
  | algebraMap r => rw [hΓF]; exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [smul_mul']; exact mul_mem hy hz

theorem smul_mem_chartAlg (hΓF : ∀ (s : Γ) (r : R), s • algebraMap R F r = algebraMap R F (s • r))
    (s : Γ) (S : Set F) (hS : ∀ x ∈ S, s • x ∈ S) {x : F} (hx : x ∈ chartAlg R F S) :
    s • x ∈ chartAlg R F S := by
  rw [mem_chartAlg_iff] at hx ⊢
  set A := Algebra.adjoin R S with hA
  let σ : F →+* F := MulSemiringAction.toRingHom Γ F s
  have hσ : ∀ y : F, σ y = s • y := fun _ => rfl
  have hAA : ∀ a : F, a ∈ A → σ a ∈ A := fun a ha => by rw [hσ]; exact smul_mem_adjoin hΓF s S hS ha
  let eA : A →+* A :=
    { toFun := fun a => ⟨σ a, hAA a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hcomp : σ.comp (algebraMap A F) = (algebraMap A F).comp eA := RingHom.ext fun a => rfl
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map eA, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, ← hcomp, ← hσ]
  have h2 : eval₂ (σ.comp (algebraMap A F)) (σ x) p = σ (eval₂ (algebraMap A F) x p) :=
    (Polynomial.hom_eval₂ p (algebraMap A F) σ x).symm
  exact h2.trans (by rw [hpx, map_zero])

def restr (hΓF : ∀ (s : Γ) (r : R), s • algebraMap R F r = algebraMap R F (s • r))
    (S : Set F) (hS : ∀ (s : Γ), ∀ x ∈ S, s • x ∈ S) (s : Γ) : ↥(chartAlg R F S) ≃+* ↥(chartAlg R F S) where
  toFun x := ⟨s • (x : F), smul_mem_chartAlg hΓF s S (hS s) x.2⟩
  invFun x := ⟨s⁻¹ • (x : F), smul_mem_chartAlg hΓF s⁻¹ S (hS s⁻¹) x.2⟩
  left_inv x := Subtype.ext (inv_smul_smul s (x : F))
  right_inv x := Subtype.ext (smul_inv_smul s (x : F))
  map_mul' x y := Subtype.ext (smul_mul' s (x : F) (y : F))
  map_add' x y := Subtype.ext (smul_add s (x : F) (y : F))

@[scoped simp] theorem coe_restr (hΓF : ∀ (s : Γ) (r : R), s • algebraMap R F r = algebraMap R F (s • r))
    (S : Set F) (hS : ∀ (s : Γ), ∀ x ∈ S, s • x ∈ S) (s : Γ) (x : ↥(chartAlg R F S)) :
    ((restr hΓF S hS s x : ↥(chartAlg R F S)) : F) = s • (x : F) := rfl

theorem restr_one (hΓF : ∀ (s : Γ) (r : R), s • algebraMap R F r = algebraMap R F (s • r))
    (S : Set F) (hS : ∀ (s : Γ), ∀ x ∈ S, s • x ∈ S) :
    (restr hΓF S hS 1).toRingHom = RingHom.id _ :=
  RingHom.ext fun x => Subtype.ext (one_smul Γ (x : F))

theorem restr_mul (hΓF : ∀ (s : Γ) (r : R), s • algebraMap R F r = algebraMap R F (s • r))
    (S : Set F) (hS : ∀ (s : Γ), ∀ x ∈ S, s • x ∈ S) (s s' : Γ) :
    (restr hΓF S hS (s * s')).toRingHom = (restr hΓF S hS s).toRingHom.comp (restr hΓF S hS s').toRingHom :=
  RingHom.ext fun x => Subtype.ext (mul_smul s s' (x : F))

theorem restr_algebraMap (hΓF : ∀ (s : Γ) (r : R), s • algebraMap R F r = algebraMap R F (s • r))
    (S : Set F) (hS : ∀ (s : Γ), ∀ x ∈ S, s • x ∈ S) (s : Γ) (r : R) :
    restr hΓF S hS s (algebraMap R _ r) = algebraMap R _ (s • r) :=
  Subtype.ext (by rw [coe_restr, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, hΓF])

end Rings

section Model

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem exists_hom_of_chartRingHom₃
    (aF : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R F j)) (aI : ↥(chartAlgInf R F j) →+* ↥(chartAlgInf R F j))
    (aM : ↥(chartAlgMid R F j) →+* ↥(chartAlgMid R F j))
    (hcF : ∀ x, (aM (inclFin R F j x) : F) = aF x) (hcI : ∀ x, (aM (inclInf R F j x) : F) = aI x) :
    ∃ φ : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j,
      ιFin R F j ≫ φ = Spec.map (CommRingCat.ofHom aF) ≫ ιFin R F j ∧
      ιInf R F j ≫ φ = Spec.map (CommRingCat.ofHom aI) ≫ ιInf R F j := by
  have eF : (inclFin R F j).toRingHom.comp aF = aM.comp (inclFin R F j).toRingHom :=
    RingHom.ext fun x => Subtype.ext
      (show ((inclFin R F j (aF x) : chartAlgMid R F j) : F) = (aM (inclFin R F j x) : F) by
          rw [hcF, coe_chartIncl])
  have eI : (inclInf R F j).toRingHom.comp aI = aM.comp (inclInf R F j).toRingHom :=
    RingHom.ext fun x => Subtype.ext
      (show ((inclInf R F j (aI x) : chartAlgMid R F j) : F) = (aM (inclInf R F j x) : F) by
          rw [hcI, coe_chartIncl])
  have cF : fFin R F j ≫ Spec.map (CommRingCat.ofHom aF) =
      Spec.map (CommRingCat.ofHom aM) ≫ fFin R F j := by
    simp only [fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp, eF]
  have cI : fInf R F j ≫ Spec.map (CommRingCat.ofHom aI) =
      Spec.map (CommRingCat.ofHom aM) ≫ fInf R F j := by
    simp only [fInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, eI]
  refine ⟨pushout.map _ _ _ _ (Spec.map (CommRingCat.ofHom aF))
    (Spec.map (CommRingCat.ofHom aI)) (Spec.map (CommRingCat.ofHom aM)) cF cI, ?_, ?_⟩
  · exact pushout.inl_desc _ _ _
  · exact pushout.inr_desc _ _ _

variable (Γ : Type v) [Group Γ] [MulSemiringAction Γ R] [MulSemiringAction Γ F]

theorem main
    (hΓF : ∀ (s : Γ) (r : R), s • algebraMap R F r = algebraMap R F (s • r))
    (hΓj : ∀ s : Γ, s • j = j) :
    ∃ (w : Γ → (AlgebraicCurve.TwoChartIntegralModel R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j))
      (θ : Γ → (↥(chartAlgFin R F j) ≃+* ↥(chartAlgFin R F j)))
      (θ' : Γ → (↥(chartAlgInf R F j) ≃+* ↥(chartAlgInf R F j))),
      (∀ s : Γ, w s ≫ toBase R F j = toBase R F j ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ R s))) ∧
      w 1 = 𝟙 (AlgebraicCurve.TwoChartIntegralModel R F j) ∧
      (∀ s s' : Γ, w (s * s') = w s ≫ w s') ∧
      (∀ (s : Γ) (b : ↥(chartAlgFin R F j)), ((θ s b : ↥(chartAlgFin R F j)) : F) = s • (b : F)) ∧
      (∀ (s : Γ) (b : ↥(chartAlgInf R F j)), ((θ' s b : ↥(chartAlgInf R F j)) : F) = s • (b : F)) ∧
      (∀ s : Γ, ιFin R F j ≫ w s = Spec.map (CommRingCat.ofHom (θ s).toRingHom) ≫ ιFin R F j) ∧
      (∀ s : Γ, ιInf R F j ≫ w s = Spec.map (CommRingCat.ofHom (θ' s).toRingHom) ≫ ιInf R F j) ∧
      (∀ s : Γ, (w s) ⁻¹ᵁ (ιFin R F j).opensRange = (ιFin R F j).opensRange) := by

  have hj' : ∀ s : Γ, s • j⁻¹ = j⁻¹ := fun s => by rw [smul_inv'', hΓj]
  have hS1 : ∀ (s : Γ), ∀ x ∈ ({j} : Set F), s • x ∈ ({j} : Set F) := by
    intro s x hx; rw [Set.mem_singleton_iff] at hx ⊢; rw [hx, hΓj]
  have hS2 : ∀ (s : Γ), ∀ x ∈ ({j⁻¹} : Set F), s • x ∈ ({j⁻¹} : Set F) := by
    intro s x hx; rw [Set.mem_singleton_iff] at hx ⊢; rw [hx, hj']
  have hS3 : ∀ (s : Γ), ∀ x ∈ ({j, j⁻¹} : Set F), s • x ∈ ({j, j⁻¹} : Set F) := by
    intro s x hx
    rcases hx with rfl | hx
    · rw [hΓj]; exact Set.mem_insert _ _
    · rw [Set.mem_singleton_iff] at hx; rw [hx, hj']; exact Set.mem_insert_of_mem _ rfl

  let θ : Γ → (↥(chartAlgFin R F j) ≃+* ↥(chartAlgFin R F j)) := restr hΓF {j} hS1
  let θ' : Γ → (↥(chartAlgInf R F j) ≃+* ↥(chartAlgInf R F j)) := restr hΓF {j⁻¹} hS2
  let θM : Γ → (↥(chartAlgMid R F j) ≃+* ↥(chartAlgMid R F j)) := restr hΓF {j, j⁻¹} hS3

  have hex : ∀ s : Γ, ∃ φ : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j,
      ιFin R F j ≫ φ = Spec.map (CommRingCat.ofHom (θ s).toRingHom) ≫ ιFin R F j ∧
      ιInf R F j ≫ φ = Spec.map (CommRingCat.ofHom (θ' s).toRingHom) ≫ ιInf R F j := fun s =>
    exists_hom_of_chartRingHom₃ R F j (θ s).toRingHom (θ' s).toRingHom (θM s).toRingHom
      (fun x => by
        show ((θM s (inclFin R F j x) : chartAlgMid R F j) : F) = ((θ s x : chartAlgFin R F j) : F)
        rw [coe_restr, coe_restr, coe_chartIncl])
      (fun x => by
        show ((θM s (inclInf R F j x) : chartAlgMid R F j) : F) = ((θ' s x : chartAlgInf R F j) : F)
        rw [coe_restr, coe_restr, coe_chartIncl])
  choose w hwF hwI using hex

  have hone : w 1 = 𝟙 _ := by
    apply pushout.hom_ext
    · change ιFin R F j ≫ w 1 = ιFin R F j ≫ 𝟙 _
      rw [hwF, Category.comp_id, show (θ 1).toRingHom = RingHom.id _ from restr_one hΓF {j} hS1,
        CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    · change ιInf R F j ≫ w 1 = ιInf R F j ≫ 𝟙 _
      rw [hwI, Category.comp_id, show (θ' 1).toRingHom = RingHom.id _ from restr_one hΓF {j⁻¹} hS2,
        CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hmul : ∀ s s' : Γ, w (s * s') = w s ≫ w s' := by
    intro s s'
    apply pushout.hom_ext
    · change ιFin R F j ≫ w (s * s') = ιFin R F j ≫ w s ≫ w s'
      rw [hwF, ← Category.assoc, hwF, Category.assoc, hwF, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, show (θ (s * s')).toRingHom = (θ s).toRingHom.comp (θ s').toRingHom from
          restr_mul hΓF {j} hS1 s s']
    · change ιInf R F j ≫ w (s * s') = ιInf R F j ≫ w s ≫ w s'
      rw [hwI, ← Category.assoc, hwI, Category.assoc, hwI, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, show (θ' (s * s')).toRingHom = (θ' s).toRingHom.comp (θ' s').toRingHom from
          restr_mul hΓF {j⁻¹} hS2 s s']
  have hbase : ∀ s : Γ, w s ≫ toBase R F j =
      toBase R F j ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ R s)) := by
    intro s
    apply pushout.hom_ext
    · change ιFin R F j ≫ w s ≫ toBase R F j = ιFin R F j ≫ toBase R F j ≫ Spec.map _
      rw [← Category.assoc, hwF, Category.assoc, ιFin_toBase, ← Category.assoc, ιFin_toBase, ← Spec.map_comp,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun r => restr_algebraMap hΓF {j} hS1 s r
    · change ιInf R F j ≫ w s ≫ toBase R F j = ιInf R F j ≫ toBase R F j ≫ Spec.map _
      rw [← Category.assoc, hwI, Category.assoc, ιInf_toBase, ← Category.assoc, ιInf_toBase, ← Spec.map_comp,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun r => restr_algebraMap hΓF {j⁻¹} hS2 s r

  have himg : ∀ (s : Γ) (y : ↥(Spec (CommRingCat.of ↥(chartAlgFin R F j)))),
      (w s).base ((ιFin R F j).base y) ∈ Set.range (ιFin R F j).base := by
    intro s y
    refine ⟨(Spec.map (CommRingCat.ofHom (θ s).toRingHom)).base y, ?_⟩
    have := congrArg (fun f => f.base y) (hwF s)
    simpa using this.symm
  have hinv : ∀ (s : Γ) (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)),
      (w s⁻¹).base ((w s).base x) = x := by
    intro s x
    have h := hmul s s⁻¹
    rw [mul_inv_cancel, hone] at h
    have := congrArg (fun f => f.base x) h
    simpa using this.symm
  refine ⟨w, θ, θ', hbase, hone, hmul, fun s b => rfl, fun s b => rfl, hwF, hwI, ?_⟩
  intro s
  ext x
  simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.map_coe, Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨z, hz⟩

    obtain ⟨y, hy⟩ := himg s⁻¹ z
    exact ⟨y, by rw [hy, hz, hinv]⟩
  · rintro ⟨y, rfl⟩
    exact himg s y

end Model

end AlgebraicCurve.TwoChartIntegralModel.SemilinearTwist
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq.AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq.AlgebraicCurve.TwoChartIntegralModel.SemilinearTwist"
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq.AlgebraicCurve.TwoChartIntegralModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq.AlgebraicCurve"

open _root_.AlgebraicCurve.TwoChartIntegralModel _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq.AlgebraicCurve.TwoChartIntegralModel in
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (Γ : Type v) [Group Γ] [MulSemiringAction Γ R] [MulSemiringAction Γ F]
    (hΓF : ∀ (s : Γ) (r : R), s • algebraMap R F r = algebraMap R F (s • r))
    (hΓj : ∀ s : Γ, s • j = j) :
    ∃ (w : Γ → (AlgebraicCurve.TwoChartIntegralModel R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j))
      (θ : Γ → (↥(chartAlgFin R F j) ≃+* ↥(chartAlgFin R F j)))
      (θ' : Γ → (↥(chartAlgInf R F j) ≃+* ↥(chartAlgInf R F j))),
      (∀ s : Γ, w s ≫ toBase R F j = toBase R F j ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ R s))) ∧
      w 1 = 𝟙 (AlgebraicCurve.TwoChartIntegralModel R F j) ∧
      (∀ s s' : Γ, w (s * s') = w s ≫ w s') ∧
      (∀ (s : Γ) (b : ↥(chartAlgFin R F j)), ((θ s b : ↥(chartAlgFin R F j)) : F) = s • (b : F)) ∧
      (∀ (s : Γ) (b : ↥(chartAlgInf R F j)), ((θ' s b : ↥(chartAlgInf R F j)) : F) = s • (b : F)) ∧
      (∀ s : Γ, ιFin R F j ≫ w s = Spec.map (CommRingCat.ofHom (θ s).toRingHom) ≫ ιFin R F j) ∧
      (∀ s : Γ, ιInf R F j ≫ w s = Spec.map (CommRingCat.ofHom (θ' s).toRingHom) ≫ ιInf R F j) ∧
      (∀ s : Γ, (w s) ⁻¹ᵁ (ιFin R F j).opensRange = (ιFin R F j).opensRange) :=
  AlgebraicCurve.TwoChartIntegralModel.SemilinearTwist.main R F j Γ hΓF hΓj

end S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq (solution)
