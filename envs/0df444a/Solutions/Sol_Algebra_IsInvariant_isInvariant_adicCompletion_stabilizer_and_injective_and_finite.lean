-- Prove2me | solution 1 for Algebra.IsInvariant.isInvariant_adicCompletion_stabilizer_and_injective_and_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/46eea768-5a8c-5078-9354-305e456829a9

import Mathlib
import Definitions.Def_SemilocalAdicCompletion
import Definitions.Def_AdicCompletionGaloisAction
import Definitions.Def_AdicCompletionRestrictScalars
import Definitions.Def_AdicCompletionLocalRing
import Definitions.Def_AdicCompletionTensorRing

import Theorems.Thm_AdicCompletion_map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant
import Theorems.Thm_AdicCompletion_semilocalComponent_smul_and_injOn_and_surjOn_fixedPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsInvariant_isInvariant_adicCompletion_stabilizer_and_injective_and_finite

set_option autoImplicit false

open scoped Pointwise TensorProduct
open scoped AdicCompletion.GaloisAction

namespace AtomFiniteAux

p2m_open "AdicCompletion P2MW.S_Algebra_IsInvariant_isInvariant_adicCompletion_stabilizer_and_injective_and_finite.AdicCompletion"

theorem semilocalComponent_completionBaseChangeHom {O C : Type*} [CommRing O] [CommRing C]
    [Algebra O C] (p : Ideal O) (𝔫 : Ideal C) [𝔫.LiesOver p]
    (h : p.map (algebraMap O C) ≤ 𝔫) (a : AdicCompletion p O) :
    semilocalComponent (p.map (algebraMap O C)) h (completionBaseChangeHom C p a) =
      algebraMap (AdicCompletion p O) (AdicCompletion 𝔫 C) a := by
  refine ext_evalₐ fun n => ?_
  obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (evalₐ p n a)
  rw [evalₐ_algebraMap_of_liesOver p 𝔫 n o a ho.symm, semilocalComponent, completionBaseChangeHom,
    evalₐ_mapₐ, evalₐ_mapₐ, ← ho, levelMapₐ_mk, levelMapₐ_mk]
  rfl

theorem tensorRingHom_surjective {O : Type*} [CommRing O] (C : Type*) [CommRing C] [Algebra O C]
    [Module.Finite O C] (p : Ideal O) : Function.Surjective (tensorRingHom C p) := by
  intro t
  obtain ⟨z, hz⟩ := ofTensorProduct_surjective_of_finite p C (restrictScalarsEquiv C p t)
  refine ⟨z, (restrictScalarsEquiv C p).injective ?_⟩
  rw [restrictScalarsEquiv_tensorRingHom, hz]

theorem finite_of_semilocalComponent_surjective {O C : Type*} [CommRing O] [CommRing C]
    [Algebra O C] [Module.Finite O C] (p : Ideal O) (𝔫 : Ideal C) [𝔫.LiesOver p]
    (h : p.map (algebraMap O C) ≤ 𝔫)
    (hψ : Function.Surjective (semilocalComponent (p.map (algebraMap O C)) h)) :
    Module.Finite (AdicCompletion p O) (AdicCompletion 𝔫 C) := by
  let θ : (AdicCompletion p O ⊗[O] C) →ₗ[AdicCompletion p O] AdicCompletion 𝔫 C :=
    { toFun := fun z => semilocalComponent (p.map (algebraMap O C)) h (tensorRingHom C p z)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun a z => by
        induction z using TensorProduct.induction_on with
        | zero => simp only [smul_zero, _root_.map_zero]
        | tmul x b =>
          rw [TensorProduct.smul_tmul', smul_eq_mul, tensorRingHom_tmul, tensorRingHom_tmul,
            map_mul (completionBaseChangeHom C p), mul_assoc,
            map_mul (semilocalComponent (p.map (algebraMap O C)) h) (completionBaseChangeHom C p a),
            semilocalComponent_completionBaseChangeHom, RingHom.id_apply, Algebra.smul_def]
        | add u v hu hv => simp only [smul_add, map_add, hu, hv] }
  exact Module.Finite.of_surjective θ (hψ.comp (tensorRingHom_surjective C p))

end AtomFiniteAux

section Atoms
variable {O : Type*} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type*} [CommRing C] [Algebra O C] [Module.Finite O C]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C]

local notation "𝔪" => IsLocalRing.maximalIdeal O

namespace AdicCompletion
p2m_export "AdicCompletion" "evalₐ map eval mk of module mk_surjective map_val_apply map_zero ext evalₐ_of ext_evalₐ induction_on ofTensorProduct_surjective_of_finite congr of_surjective factor_eval_eq_evalₐ semilocalComponent semilocalPiHom_apply semilocalPiHom_surjective levelMapₐ_mk evalₐ_mapₐ stabilizer_smul_of evalₐ_stabilizer_smul evalₐ_map_smul evalₐ_algebraMap_of_liesOver levelRestrictScalarsEquiv levelRestrictScalarsEquiv_mk restrictScalarsEquiv ker_evalₐ_eq_map_pow completionBaseChangeHom tensorRingHom tensorRingHom_tmul restrictScalarsEquiv_tensorRingHom map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant semilocalComponent_smul_and_injOn_and_surjOn_fixedPoints"
p2m_open "AdicCompletion"

theorem evalₐ_eq_mk_of_val_eq_mk {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (y : AdicCompletion I R) (r : R) (hy : y.val n = Submodule.Quotient.mk r) :
    evalₐ I n y = Ideal.Quotient.mk (I ^ n) r := by
  rw [← factor_eval_eq_evalₐ _ _ (le_of_eq (by ext x; simp)),
    show eval I R n y = y.val n from rfl, hy,
    show Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R R)) r =
      Submodule.mkQ (I ^ n • ⊤ : Submodule R R) r from rfl,
    Submodule.factor_mk]
  rfl

omit [IsNoetherianRing O] [IsLocalRing O] [Module.Finite O C] in

theorem evalₐ_restrictScalarsEquiv_symm (J : Ideal O) (n : ℕ) (w : AdicCompletion J C) (c : C)
    (hw : w.val n = Submodule.Quotient.mk c) :
    evalₐ (J.map (algebraMap O C)) n ((restrictScalarsEquiv C J).symm w) =
      Ideal.Quotient.mk _ c := by
  refine evalₐ_eq_mk_of_val_eq_mk _ n _ c ?_
  show (levelRestrictScalarsEquiv C J n).symm (w.val n) = _
  rw [hw, LinearEquiv.symm_apply_eq, levelRestrictScalarsEquiv_mk]

omit [IsNoetherianRing O] [IsLocalRing O] [Module.Finite O C] in

theorem map_val_eq_mk_of_val_eq_mk (J : Ideal O) {M : Type*} [AddCommGroup M] [Module O M]
    (f : M →ₗ[O] C) (n : ℕ) (x : AdicCompletion J M) (m : M)
    (hx : x.val n = Submodule.Quotient.mk m) :
    (map J f x).val n = Submodule.Quotient.mk (f m) := by
  rw [map_val_apply, hx, LinearMap.reduceModIdeal_apply]

end AdicCompletion

p2m_open "AdicCompletion P2MW.S_Algebra_IsInvariant_isInvariant_adicCompletion_stabilizer_and_injective_and_finite.AdicCompletion"

omit [IsNoetherianRing O] [Module.Finite O C] [Finite G] in

theorem atom_bridge (g : G) (x : AdicCompletion (𝔪) C) :
    (AdicCompletion.restrictScalarsEquiv C (𝔪)).symm (AdicCompletion.map (𝔪) (DistribSMul.toLinearMap O C g) x) =
      g • (AdicCompletion.restrictScalarsEquiv C (𝔪)).symm x := by
  refine ext_evalₐ fun n => ?_
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  have h1 : (map (𝔪) (DistribSMul.toLinearMap O C g) x).val n = Submodule.Quotient.mk (g • c) :=
    map_val_eq_mk_of_val_eq_mk (𝔪) _ n x c hc.symm
  rw [evalₐ_restrictScalarsEquiv_symm (𝔪) n _ (g • c) h1,
    evalₐ_map_smul (𝔪) g n c _ (evalₐ_restrictScalarsEquiv_symm (𝔪) n x c hc.symm)]

omit [IsNoetherianRing O] [Module.Finite O C] in

theorem atom_composite
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver 𝔪] (h𝔫 : (𝔪).map (algebraMap O C) ≤ 𝔫)
    (a : AdicCompletion (𝔪) O) :
    AdicCompletion.semilocalComponent ((𝔪).map (algebraMap O C)) h𝔫
        ((AdicCompletion.restrictScalarsEquiv C (𝔪)).symm (AdicCompletion.map (𝔪) (Algebra.linearMap O C) a)) =
      algebraMap (AdicCompletion (𝔪) O) (AdicCompletion 𝔫 C) a := by
  refine ext_evalₐ fun n => ?_
  obtain ⟨o, ho⟩ := Submodule.Quotient.mk_surjective _ (a.val n)
  have ho' : evalₐ (𝔪) n a = Ideal.Quotient.mk _ o := evalₐ_eq_mk_of_val_eq_mk (𝔪) n a o ho.symm
  have h1 : (map (𝔪) (Algebra.linearMap O C) a).val n =
      Submodule.Quotient.mk (algebraMap O C o) :=
    map_val_eq_mk_of_val_eq_mk (𝔪) _ n a o ho.symm
  rw [semilocalComponent, evalₐ_mapₐ, evalₐ_restrictScalarsEquiv_symm (𝔪) n _ _ h1,
    levelMapₐ_mk, AlgHom.coe_id, id_eq, evalₐ_algebraMap_of_liesOver (𝔪) 𝔫 n o a ho']

omit [IsNoetherianRing O] [IsLocalRing O] [Module.Finite O C] [Finite G] [SMulCommClass G O C] in

theorem atom_inertia [IsNoetherianRing C] (𝔫 : Ideal C) [𝔫.IsMaximal] :
    (𝔫.map (algebraMap C (AdicCompletion 𝔫 C))).inertia (MulAction.stabilizer G 𝔫) =
      (𝔫.inertia G).subgroupOf (MulAction.stabilizer G 𝔫) := by
  have hfg : 𝔫.FG := IsNoetherian.noetherian 𝔫
  have hker : ∀ y : AdicCompletion 𝔫 C,
      y ∈ 𝔫.map (algebraMap C (AdicCompletion 𝔫 C)) ↔ evalₐ 𝔫 1 y = 0 := by
    intro y
    rw [← RingHom.mem_ker, AdicCompletion.ker_evalₐ_eq_map_pow 𝔫 hfg 1, pow_one]
  ext d
  simp only [Subgroup.mem_subgroupOf, Ideal.inertia, AddSubgroup.mem_inertia,
    Submodule.mem_toAddSubgroup]
  constructor
  · intro h c
    have h2 : evalₐ 𝔫 1 (d • of 𝔫 C c - of 𝔫 C c) = 0 := (hker _).1 (h (of 𝔫 C c))
    rw [stabilizer_smul_of, map_sub, evalₐ_of, evalₐ_of, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem, pow_one] at h2
    exact h2
  · intro h x
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (evalₐ 𝔫 1 x)
    refine (hker _).2 ?_
    rw [map_sub, evalₐ_stabilizer_smul 𝔫 d 1 c x hc.symm, ← hc, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact h c

omit [IsNoetherianRing O] in

theorem atom_artinian_fibre : IsArtinianRing (C ⧸ (𝔪).map (algebraMap O C)) := by
  letI : Field (O ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Module.Finite (O ⧸ 𝔪) (C ⧸ (𝔪).map (algebraMap O C)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  exact IsArtinianRing.of_finite (O ⧸ 𝔪) _

omit [IsNoetherianRing O] in

theorem atom_under_eq (Q : Ideal C) [Q.IsMaximal] : Q.under O = 𝔪 :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)

theorem atom_finite (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver 𝔪] :
    Module.Finite (AdicCompletion (𝔪) O) (AdicCompletion 𝔫 C) := by
  have h𝔫 : (𝔪).map (algebraMap O C) ≤ 𝔫 := by
    rw [Ideal.map_le_iff_le_comap]
    exact (Ideal.LiesOver.over (P := 𝔫) (p := 𝔪)).le
  haveI : IsNoetherianRing C := isNoetherian_of_tower O (inferInstance : IsNoetherian O C)
  haveI : IsArtinianRing (C ⧸ (𝔪).map (algebraMap O C)) :=
    atom_artinian_fibre
  refine AtomFiniteAux.finite_of_semilocalComponent_surjective (𝔪) 𝔫 h𝔫 ?_
  classical
  intro y
  obtain ⟨x, hx⟩ := AdicCompletion.semilocalPiHom_surjective ((𝔪).map (algebraMap O C))
    (Function.update 0 ⟨𝔫, ‹𝔫.IsMaximal›, h𝔫⟩ y)
  refine ⟨x, ?_⟩
  have hP := congrFun hx ⟨𝔫, ‹𝔫.IsMaximal›, h𝔫⟩
  rw [AdicCompletion.semilocalPiHom_apply, Function.update_self] at hP
  exact hP

end Atoms

theorem solution
    {O : Type*} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type*} [CommRing C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C]
    [Algebra.IsInvariant O C G]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (IsLocalRing.maximalIdeal O)] :
    Algebra.IsInvariant (AdicCompletion (IsLocalRing.maximalIdeal O) O) (AdicCompletion 𝔫 C)
        (MulAction.stabilizer G 𝔫) ∧
    Function.Injective
        (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal O) O) (AdicCompletion 𝔫 C)) ∧
    Module.Finite (AdicCompletion (IsLocalRing.maximalIdeal O) O) (AdicCompletion 𝔫 C) ∧
    (𝔫.map (algebraMap C (AdicCompletion 𝔫 C))).inertia (MulAction.stabilizer G 𝔫) =
        (𝔫.inertia G).subgroupOf (MulAction.stabilizer G 𝔫) := by
  classical
  set 𝔪 := IsLocalRing.maximalIdeal O with h𝔪def
  haveI : IsNoetherianRing C := isNoetherian_of_tower O (S := C) inferInstance
  haveI : IsArtinianRing (C ⧸ 𝔪.map (algebraMap O C)) := atom_artinian_fibre

  have h𝔫 : 𝔪.map (algebraMap O C) ≤ 𝔫 := by
    rw [Ideal.map_le_iff_le_comap]
    exact (Ideal.LiesOver.over (P := 𝔫) (p := 𝔪)).le

  have htrans : ∀ Q : Ideal C, Q.IsMaximal → 𝔪.map (algebraMap O C) ≤ Q → ∃ g : G, Q = g • 𝔫 := by
    intro Q hQ _
    haveI := hQ
    have h1 : Q.under O = 𝔫.under O := by rw [atom_under_eq (O := O) Q, atom_under_eq (O := O) 𝔫]
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq O C G 𝔫 Q h1.symm
    exact ⟨g, hg⟩
  obtain ⟨hπD, hπinj, hπsurj⟩ := AdicCompletion.semilocalComponent_smul_and_injOn_and_surjOn_fixedPoints (O := O) (S := C) (G := G) 𝔪 𝔫 h𝔫 htrans
  set ε := (AdicCompletion.restrictScalarsEquiv C 𝔪).symm with hεdef
  obtain ⟨hinj0, hrange⟩ := AdicCompletion.map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant (G := G) 𝔪 (S := C)
  have hbr : ∀ (g : G) (x : AdicCompletion 𝔪 C),
      ε (AdicCompletion.map 𝔪 (DistribSMul.toLinearMap O C g) x) = g • ε x :=
    fun g x => atom_bridge (O := O) (C := C) g x
  refine ⟨⟨fun x hx => ?_⟩, ?_, atom_finite 𝔫, atom_inertia 𝔫⟩
  ·
    obtain ⟨y, hyG, hyx⟩ := hπsurj x hx

    have hy0 : ∀ g : G, AdicCompletion.map 𝔪 (DistribSMul.toLinearMap O C g) (ε.symm y) = ε.symm y := by
      intro g
      apply ε.injective
      rw [hbr g (ε.symm y), LinearEquiv.apply_symm_apply, hyG g]
    obtain ⟨a, ha⟩ := (hrange (ε.symm y)).2 hy0
    refine ⟨a, ?_⟩
    rw [← atom_composite 𝔫 h𝔫 a, ha, LinearEquiv.apply_symm_apply, hyx]
  ·
    intro a b hab
    apply hinj0
    apply ε.injective
    have hfix : ∀ (c : AdicCompletion 𝔪 O) (g : G),
        g • ε (AdicCompletion.map 𝔪 (Algebra.linearMap O C) c) = ε (AdicCompletion.map 𝔪 (Algebra.linearMap O C) c) := by
      intro c g
      rw [← hbr g]
      congr 1
      exact (hrange _).1 ⟨c, rfl⟩ g
    refine hπinj _ _ (hfix a) (hfix b) ?_
    rw [atom_composite 𝔫 h𝔫 a, atom_composite 𝔫 h𝔫 b, hab]

#print axioms solution
#print axioms atom_finite

end S_Algebra_IsInvariant_isInvariant_adicCompletion_stabilizer_and_injective_and_finite
end P2MW
export P2MW.S_Algebra_IsInvariant_isInvariant_adicCompletion_stabilizer_and_injective_and_finite (solution)
