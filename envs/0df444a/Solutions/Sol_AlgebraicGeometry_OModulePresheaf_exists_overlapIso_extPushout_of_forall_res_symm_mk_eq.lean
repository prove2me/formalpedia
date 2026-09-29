-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_overlapIso_extPushout_of_forall_res_symm_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/fb7ecbb0-e126-5610-b66f-dbcc3800804e

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_LinearMap_ExtPushout
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace X1bOverlapSol

open LinearMap

section Core

variable {B : Type u} [CommRing B] {M N : Type u} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
  {r r' : ℕ}

theorem gamma_mem (p : (Fin r → B) →ₗ[B] M) (p' : (Fin r' → B) →ₗ[B] M) (γ : (Fin r → B) →ₗ[B] (Fin r' → B))
    (hγ : ∀ v, p' (γ v) = p v) (s : ↥(ker p)) : γ s ∈ ker p' := by
  rw [mem_ker, hγ]; exact s.2

noncomputable def coreMap (p : (Fin r → B) →ₗ[B] M) (δ : ↥(ker p) →ₗ[B] N) (p' : (Fin r' → B) →ₗ[B] M)
    (δ' : ↥(ker p') →ₗ[B] N) (γ : (Fin r → B) →ₗ[B] (Fin r' → B)) (φ : (Fin r → B) →ₗ[B] N)
    (hγ : ∀ v, p' (γ v) = p v) (hφ : ∀ s : ↥(ker p), δ' ⟨γ s, gamma_mem p p' γ hγ s⟩ = δ s + φ s) :
    ExtPushout p δ →ₗ[B] ExtPushout p' δ' :=
  ExtPushout.lift p δ (ExtPushout.inl p' δ') (ExtPushout.inr p' δ' ∘ₗ γ - ExtPushout.inl p' δ' ∘ₗ φ) (fun s => by
    have h := ExtPushout.inr_coe p' δ' ⟨γ s, gamma_mem p p' γ hγ s⟩
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [h, hφ, map_add, add_sub_cancel_right])

variable (p : (Fin r → B) →ₗ[B] M) (δ : ↥(ker p) →ₗ[B] N) (p' : (Fin r' → B) →ₗ[B] M)
    (δ' : ↥(ker p') →ₗ[B] N) (γ : (Fin r → B) →ₗ[B] (Fin r' → B)) (φ : (Fin r → B) →ₗ[B] N)
    (hγ : ∀ v, p' (γ v) = p v) (hφ : ∀ s : ↥(ker p), δ' ⟨γ s, gamma_mem p p' γ hγ s⟩ = δ s + φ s)

theorem coreMap_inl (n : N) : coreMap p δ p' δ' γ φ hγ hφ (ExtPushout.inl p δ n) = ExtPushout.inl p' δ' n :=
  ExtPushout.lift_inl _ _ _ _ _ n

theorem coreMap_inr (v : Fin r → B) :
    coreMap p δ p' δ' γ φ hγ hφ (ExtPushout.inr p δ v) = ExtPushout.inr p' δ' (γ v) - ExtPushout.inl p' δ' (φ v) :=
  ExtPushout.lift_inr _ _ _ _ _ v

theorem proj_coreMap (x : ExtPushout p δ) :
    ExtPushout.proj p' δ' (coreMap p δ p' δ' γ φ hγ hφ x) = ExtPushout.proj p δ x := by
  obtain ⟨⟨n, v⟩, rfl⟩ := ExtPushout.mk_surjective p δ x
  simp only [ExtPushout.mk_eq_inl_add_inr, map_add, map_sub, coreMap_inl, coreMap_inr,
    ExtPushout.proj_inl, ExtPushout.proj_inr, hγ, sub_zero, zero_add]

theorem coreMap_injective : Function.Injective (coreMap p δ p' δ' γ φ hγ hφ) := by
  rw [← ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [mem_ker] at hx
  have hpx : ExtPushout.proj p δ x = 0 := by rw [← proj_coreMap p δ p' δ' γ φ hγ hφ x, hx, map_zero]
  have hx' : x ∈ range (ExtPushout.inl p δ) := by rw [ExtPushout.range_inl_eq_ker_proj]; exact hpx
  obtain ⟨n, rfl⟩ := hx'
  rw [coreMap_inl] at hx
  rw [Submodule.mem_bot, ExtPushout.inl_injective p' δ' (hx.trans (map_zero _).symm), map_zero]

theorem coreMap_surjective (hp : Function.Surjective p) : Function.Surjective (coreMap p δ p' δ' γ φ hγ hφ) := by
  intro y
  obtain ⟨x, hx⟩ := ExtPushout.proj_surjective p δ hp (ExtPushout.proj p' δ' y)
  have hy : y - coreMap p δ p' δ' γ φ hγ hφ x ∈ range (ExtPushout.inl p' δ') := by
    rw [ExtPushout.range_inl_eq_ker_proj, mem_ker, map_sub, proj_coreMap, hx, sub_self]
  obtain ⟨n, hn⟩ := hy
  refine ⟨x + ExtPushout.inl p δ n, ?_⟩
  rw [map_add, coreMap_inl, hn, add_sub_cancel]

end Core

section Ext

variable {B : Type u} [CommRing B] {M N : Type u} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] {r : ℕ}

theorem addHom_ext (p : (Fin r → B) →ₗ[B] M) (δ : ↥(ker p) →ₗ[B] N) {Q : Type u} [AddCommGroup Q]
    (f g : ExtPushout p δ → Q) (hf : ∀ x y, f (x + y) = f x + f y) (hg : ∀ x y, g (x + y) = g x + g y)
    (h₁ : ∀ n, f (ExtPushout.inl p δ n) = g (ExtPushout.inl p δ n)) (h₂ : ∀ v, f (ExtPushout.inr p δ v) = g (ExtPushout.inr p δ v))
    (x : ExtPushout p δ) : f x = g x := by
  obtain ⟨⟨n, v⟩, rfl⟩ := ExtPushout.mk_surjective p δ x
  rw [ExtPushout.mk_eq_inl_add_inr, hf, hg, h₁, h₂]

theorem pi_eq_sum_single (v : Fin r → B) : v = ∑ m, v m • (Pi.single m 1 : Fin r → B) := by
  funext m'
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem apply_eq_sum_single {X : Type u} [AddCommGroup X] [Module B X] (g : (Fin r → B) →ₗ[B] X) (v : Fin r → B) :
    g v = ∑ m, v m • g (Pi.single m 1) := by
  conv_lhs => rw [pi_eq_sum_single v]
  rw [map_sum]; simp only [map_smul]

theorem map_single {B' : Type u} [CommRing B'] (ρ : B →+* B') (m : Fin r) :
    (fun m' => ρ ((Pi.single m 1 : Fin r → B) m')) = (Pi.single m 1 : Fin r → B') := by
  funext m'
  by_cases h : m' = m
  · subst h; simp
  · simp [h]

end Ext

section Lin

variable {B : Type u} [CommRing B] {r : ℕ}

noncomputable def lin {X : Type u} [AddCommGroup X] [Module B X] (w : Fin r → X) : (Fin r → B) →ₗ[B] X :=
  ∑ m, (LinearMap.proj m : (Fin r → B) →ₗ[B] B).smulRight (w m)

theorem lin_apply {X : Type u} [AddCommGroup X] [Module B X] (w : Fin r → X) (v : Fin r → B) :
    lin w v = ∑ m, v m • w m := by
  simp only [lin, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]

theorem lin_single {X : Type u} [AddCommGroup X] [Module B X] (w : Fin r → X) (m : Fin r) :
    lin w (Pi.single m (1 : B) : Fin r → B) = w m := by
  rw [lin_apply]
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Lin

section Res

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

noncomputable abbrev ρ {U U' : P.Opens} (h : U' ≤ U) : Γ(P, U) →+* Γ(P, U') := (P.presheaf.map (homOfLE h).op).hom

theorem ρ_ρ {U U' U'' : P.Opens} (h : U' ≤ U) (h' : U'' ≤ U') (a : Γ(P, U)) : ρ h' (ρ h a) = ρ (h'.trans h) a := by
  show (P.presheaf.map (homOfLE h).op ≫ P.presheaf.map (homOfLE h').op).hom a = _
  rw [← P.presheaf.map_comp]; rfl

theorem ρ_refl {U : P.Opens} (a : Γ(P, U)) : ρ (le_refl U) a = a := by
  show (P.presheaf.map (homOfLE (le_refl U)).op).hom a = a
  rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 _), P.presheaf.map_id]; rfl

noncomputable def gammaRes {V W : P.Opens} (h : W ≤ V) {r r' : ℕ} (γ : (Fin r → Γ(P, V)) →ₗ[Γ(P, V)] (Fin r' → Γ(P, V))) :
    (Fin r → Γ(P, W)) →ₗ[Γ(P, W)] (Fin r' → Γ(P, W)) :=
  lin fun m m' => ρ h (γ (Pi.single m (1 : Γ(P, V)) : Fin r → Γ(P, V)) m')

theorem gammaRes_apply {V W : P.Opens} (h : W ≤ V) {r r' : ℕ} (γ : (Fin r → Γ(P, V)) →ₗ[Γ(P, V)] (Fin r' → Γ(P, V)))
    (v : Fin r → Γ(P, W)) :
    gammaRes h γ v = ∑ m, v m • fun m' => ρ h (γ (Pi.single m (1 : Γ(P, V)) : Fin r → Γ(P, V)) m') := lin_apply _ v

noncomputable def phiRes (GK : OModulePresheaf q) {V W : P.Opens} (h : W ≤ V) {r : ℕ} (φ : (Fin r → Γ(P, V)) →ₗ[Γ(P, V)] GK.obj V) :
    (Fin r → Γ(P, W)) →ₗ[Γ(P, W)] GK.obj W :=
  lin fun m => GK.res h (φ (Pi.single m (1 : Γ(P, V)) : Fin r → Γ(P, V)))

theorem phiRes_apply (GK : OModulePresheaf q) {V W : P.Opens} (h : W ≤ V) {r : ℕ} (φ : (Fin r → Γ(P, V)) →ₗ[Γ(P, V)] GK.obj V)
    (v : Fin r → Γ(P, W)) :
    phiRes GK h φ v = ∑ m, v m • GK.res h (φ (Pi.single m (1 : Γ(P, V)) : Fin r → Γ(P, V))) := lin_apply _ v

end Res

section ResTrans

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

theorem gammaRes_res {V W W' : P.Opens} (h : W ≤ V) (h' : W' ≤ W) {r r' : ℕ}
    (γ : (Fin r → Γ(P, V)) →ₗ[Γ(P, V)] (Fin r' → Γ(P, V))) (v : Fin r → Γ(P, W)) :
    gammaRes (h'.trans h) γ (fun m => ρ h' (v m)) = fun m' => ρ h' (gammaRes h γ v m') := by
  funext m'
  simp only [gammaRes_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, ρ_ρ]

theorem phiRes_res (GK : OModulePresheaf q) {V W W' : P.Opens} (h : W ≤ V) (h' : W' ≤ W) {r : ℕ}
    (φ : (Fin r → Γ(P, V)) →ₗ[Γ(P, V)] GK.obj V) (v : Fin r → Γ(P, W)) :
    phiRes GK (h'.trans h) φ (fun m => ρ h' (v m)) = GK.res h' (phiRes GK h φ v) := by
  simp only [phiRes_apply, map_sum, GK.res_smul, GK.res_res]

theorem gammaRes_refl {V : P.Opens} {r r' : ℕ} (γ : (Fin r → Γ(P, V)) →ₗ[Γ(P, V)] (Fin r' → Γ(P, V))) (v : Fin r → Γ(P, V)) :
    gammaRes (le_refl V) γ v = γ v := by
  rw [gammaRes_apply, apply_eq_sum_single γ v]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1; funext m'; exact ρ_refl _

theorem phiRes_refl (GK : OModulePresheaf q) {V : P.Opens} {r : ℕ} (φ : (Fin r → Γ(P, V)) →ₗ[Γ(P, V)] GK.obj V)
    (v : Fin r → Γ(P, V)) : phiRes GK (le_refl V) φ v = φ v := by
  rw [phiRes_apply, apply_eq_sum_single φ v]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [GK.res_refl_apply]

end ResTrans

end X1bOverlapSol

namespace X1bOverlapSol

open LinearMap

theorem map_homOfLE_refl_apply {P : Scheme.{u}} (U : P.Opens) (a : Γ(P, U)) :
    (P.presheaf.map (homOfLE (le_refl U)).op).hom a = a := by
  rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (Opposite.op U)), P.presheaf.map_id]; rfl

theorem exists_lift_corr
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    (GE : OModulePresheaf q) (GK : OModulePresheaf q) (X : OModulePresheaf q)
    (εX : ∀ (W : P.affineOpens) (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1), Function.Surjective p →
        (X.obj W.1 ≃ₗ[Γ(P, W.1)]
          ((↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) ⧸
            LinearMap.range (LinearMap.lcomp (Γ(P, W.1)) (GK.obj W.1) (LinearMap.ker p).subtype))))
    (hXf : ∀ (W W' : P.affineOpens) (h : W'.1 ≤ W.1)
        (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1) (hp : Function.Surjective p)
        (r' : ℕ) (p' : (Fin r' → Γ(P, W'.1)) →ₗ[Γ(P, W'.1)] GE.obj W'.1) (hp' : Function.Surjective p')
        (g : (Fin r → Γ(P, W.1)) →+ (Fin r' → Γ(P, W'.1)))
        (_hg : ∀ (a : Γ(P, W.1)) (v : Fin r → Γ(P, W.1)), g (a • v) = (P.presheaf.map (homOfLE h).op).hom a • g v)
        (hgp : ∀ v : Fin r → Γ(P, W.1), p' (g v) = GE.res h (p v))
        (δ : ↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) (δ' : ↥(LinearMap.ker p') →ₗ[Γ(P, W'.1)] GK.obj W'.1)
        (hδ : ∀ s : ↥(LinearMap.ker p),
          δ' ⟨g s.1, by rw [LinearMap.mem_ker, hgp, (LinearMap.mem_ker.mp s.2), map_zero]⟩ = GK.res h (δ s)),
        X.res h ((εX W r p hp).symm (Submodule.Quotient.mk δ)) = (εX W' r' p' hp').symm (Submodule.Quotient.mk δ'))
    (K : P.OrderedAffineCover) (rk : K.ι → ℕ)
    (pr : ∀ i : K.ι, (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] GE.obj (K.U i))
    (hpr : ∀ i : K.ι, Function.Surjective (pr i))
    (δ : ∀ i : K.ι, ↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i))
    (hδ : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      X.res hi ((εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk (δ i))) =
      X.res hj ((εX ⟨K.U j, K.isAffineOpen j⟩ (rk j) (pr j) (hpr j)).symm (Submodule.Quotient.mk (δ j))))
    (prU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        (Fin (rk i) → Γ(P, U.1.1)) →ₗ[Γ(P, U.1.1)] GE.obj U.1.1)
      (_hprU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (v : Fin (rk i) → Γ(P, K.U i)),
        prU i U (fun m => (P.presheaf.map (homOfLE U.2).op).hom (v m)) = GE.res U.2 (pr i v))
      (_hprUs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (prU i U))
      (_hprUn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (v : Fin (rk i) → Γ(P, U.1.1)),
        prU i U' (fun m => (P.presheaf.map (homOfLE h).op).hom (v m)) = GE.res h (prU i U v))
      (gU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), ↥(LinearMap.ker (pr i)) → ↥(LinearMap.ker (prU i U)))
      (_hgU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (pr i))) (m : Fin (rk i)),
        ((gU i U s : ↥(LinearMap.ker (prU i U))) : Fin (rk i) → Γ(P, U.1.1)) m =
          (P.presheaf.map (homOfLE U.2).op).hom ((s : Fin (rk i) → Γ(P, K.U i)) m))
      (δU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), ↥(LinearMap.ker (prU i U)) →ₗ[Γ(P, U.1.1)] GK.obj U.1.1)
      (_hδU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (pr i))),
        δU i U (gU i U s) = GK.res U.2 (δ i s))
    (i j : K.ι) (V : P.affineOpens) (hi : V.1 ≤ K.U i) (hj : V.1 ≤ K.U j) :
    ∃ (γ : (Fin (rk i) → Γ(P, V.1)) →ₗ[Γ(P, V.1)] (Fin (rk j) → Γ(P, V.1)))
      (hγ : ∀ v, prU j ⟨V, hj⟩ (γ v) = prU i ⟨V, hi⟩ v)
      (φ : (Fin (rk i) → Γ(P, V.1)) →ₗ[Γ(P, V.1)] GK.obj V.1),
      ∀ s : ↥(LinearMap.ker (prU i ⟨V, hi⟩)),
        δU j ⟨V, hj⟩ ⟨γ s, gamma_mem _ _ γ hγ s⟩ = δU i ⟨V, hi⟩ s + φ s := by

  have hc : ∀ m : Fin (rk i), ∃ c : Fin (rk j) → Γ(P, V.1),
      prU j ⟨V, hj⟩ c = prU i ⟨V, hi⟩ (fun k => if m = k then 1 else 0) := fun m => _hprUs j ⟨V, hj⟩ _
  choose c hc using hc
  let γ : (Fin (rk i) → Γ(P, V.1)) →ₗ[Γ(P, V.1)] (Fin (rk j) → Γ(P, V.1)) := Fintype.linearCombination Γ(P, V.1) c
  have hγ : ∀ v, prU j ⟨V, hj⟩ (γ v) = prU i ⟨V, hi⟩ v := fun v => by
    rw [LinearMap.pi_apply_eq_sum_univ (prU i ⟨V, hi⟩) v]
    show prU j ⟨V, hj⟩ (Fintype.linearCombination Γ(P, V.1) c v) = _
    rw [Fintype.linearCombination_apply, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, hc]

  have keyres : ∀ (l : K.ι) (hl : V.1 ≤ K.U l),
      X.res hl ((εX ⟨K.U l, K.isAffineOpen l⟩ (rk l) (pr l) (hpr l)).symm (Submodule.Quotient.mk (δ l))) =
        (εX V (rk l) (prU l ⟨V, hl⟩) (_hprUs l ⟨V, hl⟩)).symm (Submodule.Quotient.mk (δU l ⟨V, hl⟩)) := by
    intro l hl
    refine hXf ⟨K.U l, K.isAffineOpen l⟩ V hl (rk l) (pr l) (hpr l) (rk l) (prU l ⟨V, hl⟩) (_hprUs l ⟨V, hl⟩)
      { toFun := fun v m => (P.presheaf.map (homOfLE hl).op).hom (v m)
        map_zero' := funext fun m => map_zero _
        map_add' := fun v w => funext fun m => map_add _ _ _ } ?_ ?_ (δ l) (δU l ⟨V, hl⟩) ?_
    · intro a v
      funext m
      show (P.presheaf.map (homOfLE hl).op).hom (a * v m) =
        (P.presheaf.map (homOfLE hl).op).hom a * (P.presheaf.map (homOfLE hl).op).hom (v m)
      exact map_mul ((P.presheaf.map (homOfLE hl).op).hom) a (v m)
    · intro v
      exact _hprU l ⟨V, hl⟩ v
    · intro s
      rw [← _hδU l ⟨V, hl⟩ s]
      congr 1
      exact Subtype.ext (funext fun m => (_hgU l ⟨V, hl⟩ s m).symm)
  have hV : (εX V (rk i) (prU i ⟨V, hi⟩) (_hprUs i ⟨V, hi⟩)).symm (Submodule.Quotient.mk (δU i ⟨V, hi⟩)) =
      (εX V (rk j) (prU j ⟨V, hj⟩) (_hprUs j ⟨V, hj⟩)).symm (Submodule.Quotient.mk (δU j ⟨V, hj⟩)) :=
    ((keyres i hi).symm.trans (hδ i j V hi hj)).trans (keyres j hj)

  obtain ⟨δ', hδ'⟩ : ∃ δ' : ↥(LinearMap.ker (prU i ⟨V, hi⟩)) →ₗ[Γ(P, V.1)] GK.obj V.1,
      ∀ s, δ' s = δU j ⟨V, hj⟩ ⟨γ s, gamma_mem _ _ γ hγ s⟩ :=
    ⟨δU j ⟨V, hj⟩ ∘ₗ LinearMap.codRestrict (LinearMap.ker (prU j ⟨V, hj⟩)) (γ ∘ₗ (LinearMap.ker (prU i ⟨V, hi⟩)).subtype)
      (fun s => gamma_mem _ _ γ hγ s), fun s => rfl⟩
  have h3 := hXf V V le_rfl (rk i) (prU i ⟨V, hi⟩) (_hprUs i ⟨V, hi⟩) (rk j) (prU j ⟨V, hj⟩) (_hprUs j ⟨V, hj⟩)
    γ.toAddMonoidHom
    (fun a v => by
      rw [map_homOfLE_refl_apply]
      exact map_smul γ a v)
    (fun v => by
      rw [OModulePresheaf.res_refl_apply GE]
      exact hγ v)
    δ' (δU j ⟨V, hj⟩)
    (fun s => by
      rw [hδ', OModulePresheaf.res_refl_apply GK]
      rfl)
  have h4 : (Submodule.Quotient.mk δ' :
        _ ⧸ LinearMap.range (LinearMap.lcomp (Γ(P, V.1)) (GK.obj V.1) (LinearMap.ker (prU i ⟨V, hi⟩)).subtype)) =
      Submodule.Quotient.mk (δU i ⟨V, hi⟩) :=
    (εX V (rk i) (prU i ⟨V, hi⟩) (_hprUs i ⟨V, hi⟩)).symm.injective
      (((OModulePresheaf.res_refl_apply X V.1 _).symm.trans h3).trans hV.symm)
  obtain ⟨φ, hφ⟩ := (Submodule.Quotient.eq _).mp h4
  refine ⟨γ, hγ, φ, fun s => ?_⟩
  have h5 := LinearMap.congr_fun hφ s
  rw [LinearMap.lcomp_apply, Submodule.subtype_apply, LinearMap.sub_apply, hδ'] at h5
  rw [h5, add_sub_cancel]

end X1bOverlapSol

namespace X1bOverlapSol

open LinearMap

section PortPiece3

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

theorem port_gammaRes_rho {V W : P.Opens} (h : W ≤ V) {r r' : ℕ}
    (γ : (Fin r → Γ(P, V)) →ₗ[Γ(P, V)] (Fin r' → Γ(P, V))) (w : Fin r → Γ(P, V)) :
    gammaRes h γ (fun m => ρ h (w m)) = fun m' => ρ h (γ w m') := by
  funext m'
  rw [gammaRes_apply]
  conv_rhs => rw [apply_eq_sum_single γ w]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]

theorem port_phiRes_rho (GK : OModulePresheaf q) {V W : P.Opens} (h : W ≤ V) {r : ℕ}
    (φ : (Fin r → Γ(P, V)) →ₗ[Γ(P, V)] GK.obj V) (w : Fin r → Γ(P, V)) :
    phiRes GK h φ (fun m => ρ h (w m)) = GK.res h (φ w) := by
  rw [phiRes_apply]
  conv_rhs => rw [apply_eq_sum_single φ w, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [GK.res_smul]

end PortPiece3

theorem prU_gammaRes
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    (GE : OModulePresheaf q) (GK : OModulePresheaf q) (X : OModulePresheaf q)
    (K : P.OrderedAffineCover) (rk : K.ι → ℕ)
    (pr : ∀ i : K.ι, (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] GE.obj (K.U i))
    (hpr : ∀ i : K.ι, Function.Surjective (pr i))
    (δ : ∀ i : K.ι, ↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i))
    (prU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        (Fin (rk i) → Γ(P, U.1.1)) →ₗ[Γ(P, U.1.1)] GE.obj U.1.1)
      (_hprU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (v : Fin (rk i) → Γ(P, K.U i)),
        prU i U (fun m => (P.presheaf.map (homOfLE U.2).op).hom (v m)) = GE.res U.2 (pr i v))
      (_hprUs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (prU i U))
      (_hprUn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (v : Fin (rk i) → Γ(P, U.1.1)),
        prU i U' (fun m => (P.presheaf.map (homOfLE h).op).hom (v m)) = GE.res h (prU i U v))
      (gU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), ↥(LinearMap.ker (pr i)) → ↥(LinearMap.ker (prU i U)))
      (_hgU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (pr i))) (m : Fin (rk i)),
        ((gU i U s : ↥(LinearMap.ker (prU i U))) : Fin (rk i) → Γ(P, U.1.1)) m =
          (P.presheaf.map (homOfLE U.2).op).hom ((s : Fin (rk i) → Γ(P, K.U i)) m))
      (δU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), ↥(LinearMap.ker (prU i U)) →ₗ[Γ(P, U.1.1)] GK.obj U.1.1)
      (_hδU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (pr i))),
        δU i U (gU i U s) = GK.res U.2 (δ i s))
      (_hgUspan : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        Submodule.span Γ(P, U.1.1)
            (Set.range fun s : ↥(LinearMap.ker (pr i)) =>
              ((gU i U s : ↥(LinearMap.ker (prU i U))) : Fin (rk i) → Γ(P, U.1.1))) =
          LinearMap.ker (prU i U))
      (_hδUn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1)
        (s : ↥(LinearMap.ker (prU i U))) (s' : ↥(LinearMap.ker (prU i U'))),
        (∀ m : Fin (rk i), (s' : Fin (rk i) → Γ(P, U'.1.1)) m = (P.presheaf.map (homOfLE h).op).hom ((s : Fin (rk i) → Γ(P, U.1.1)) m)) →
        δU i U' s' = GK.res h (δU i U s))
    (i j : K.ι) (V : P.affineOpens) (hi : V.1 ≤ K.U i) (hj : V.1 ≤ K.U j)
    (γ : (Fin (rk i) → Γ(P, V.1)) →ₗ[Γ(P, V.1)] (Fin (rk j) → Γ(P, V.1)))
    (hγ : ∀ v, prU j ⟨V, hj⟩ (γ v) = prU i ⟨V, hi⟩ v)
    (W : P.affineOpens) (h : W.1 ≤ V.1) (v : Fin (rk i) → Γ(P, W.1)) :
    prU j ⟨W, h.trans hj⟩ (gammaRes h γ v) = prU i ⟨W, h.trans hi⟩ v := by
  have key : ∀ m : Fin (rk i),
      prU j ⟨W, h.trans hj⟩ (gammaRes h γ (Pi.single m 1)) = prU i ⟨W, h.trans hi⟩ (Pi.single m 1) := by
    intro m
    have e1 : gammaRes h γ (Pi.single m 1) = fun m' => ρ h (γ (Pi.single m 1) m') := by
      rw [← port_gammaRes_rho h γ (Pi.single m 1), map_single]
    rw [e1, _hprUn j ⟨V, hj⟩ ⟨W, h.trans hj⟩ h (γ (Pi.single m 1)), hγ,
      ← _hprUn i ⟨V, hi⟩ ⟨W, h.trans hi⟩ h (Pi.single m 1), map_single]
  rw [← LinearMap.comp_apply, apply_eq_sum_single (prU j ⟨W, h.trans hj⟩ ∘ₗ gammaRes h γ) v,
    apply_eq_sum_single (prU i ⟨W, h.trans hi⟩) v]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [LinearMap.comp_apply, key]

theorem deltaU_gammaRes
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    (GE : OModulePresheaf q) (GK : OModulePresheaf q) (X : OModulePresheaf q)
    (K : P.OrderedAffineCover) (rk : K.ι → ℕ)
    (pr : ∀ i : K.ι, (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] GE.obj (K.U i))
    (hpr : ∀ i : K.ι, Function.Surjective (pr i))
    (δ : ∀ i : K.ι, ↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i))
    (prU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        (Fin (rk i) → Γ(P, U.1.1)) →ₗ[Γ(P, U.1.1)] GE.obj U.1.1)
      (_hprU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (v : Fin (rk i) → Γ(P, K.U i)),
        prU i U (fun m => (P.presheaf.map (homOfLE U.2).op).hom (v m)) = GE.res U.2 (pr i v))
      (_hprUs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (prU i U))
      (_hprUn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (v : Fin (rk i) → Γ(P, U.1.1)),
        prU i U' (fun m => (P.presheaf.map (homOfLE h).op).hom (v m)) = GE.res h (prU i U v))
      (gU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), ↥(LinearMap.ker (pr i)) → ↥(LinearMap.ker (prU i U)))
      (_hgU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (pr i))) (m : Fin (rk i)),
        ((gU i U s : ↥(LinearMap.ker (prU i U))) : Fin (rk i) → Γ(P, U.1.1)) m =
          (P.presheaf.map (homOfLE U.2).op).hom ((s : Fin (rk i) → Γ(P, K.U i)) m))
      (δU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), ↥(LinearMap.ker (prU i U)) →ₗ[Γ(P, U.1.1)] GK.obj U.1.1)
      (_hδU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (pr i))),
        δU i U (gU i U s) = GK.res U.2 (δ i s))
      (_hgUspan : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        Submodule.span Γ(P, U.1.1)
            (Set.range fun s : ↥(LinearMap.ker (pr i)) =>
              ((gU i U s : ↥(LinearMap.ker (prU i U))) : Fin (rk i) → Γ(P, U.1.1))) =
          LinearMap.ker (prU i U))
      (_hδUn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1)
        (s : ↥(LinearMap.ker (prU i U))) (s' : ↥(LinearMap.ker (prU i U'))),
        (∀ m : Fin (rk i), (s' : Fin (rk i) → Γ(P, U'.1.1)) m = (P.presheaf.map (homOfLE h).op).hom ((s : Fin (rk i) → Γ(P, U.1.1)) m)) →
        δU i U' s' = GK.res h (δU i U s))
    (i j : K.ι) (V : P.affineOpens) (hi : V.1 ≤ K.U i) (hj : V.1 ≤ K.U j)
    (γ : (Fin (rk i) → Γ(P, V.1)) →ₗ[Γ(P, V.1)] (Fin (rk j) → Γ(P, V.1)))
    (hγ : ∀ v, prU j ⟨V, hj⟩ (γ v) = prU i ⟨V, hi⟩ v)
    (φ : (Fin (rk i) → Γ(P, V.1)) →ₗ[Γ(P, V.1)] GK.obj V.1)
    (hφ : ∀ s : ↥(LinearMap.ker (prU i ⟨V, hi⟩)), δU j ⟨V, hj⟩ ⟨γ s, gamma_mem _ _ γ hγ s⟩ = δU i ⟨V, hi⟩ s + φ s)
    (W : P.affineOpens) (h : W.1 ≤ V.1) (s : ↥(LinearMap.ker (prU i ⟨W, h.trans hi⟩))) :
    δU j ⟨W, h.trans hj⟩ ⟨gammaRes h γ s, gamma_mem _ _ (gammaRes h γ)
        (prU_gammaRes q GE GK X K rk pr hpr δ prU _hprU _hprUs _hprUn gU _hgU δU _hδU _hgUspan _hδUn i j V hi hj γ hγ W h) s⟩ =
      δU i ⟨W, h.trans hi⟩ s + phiRes GK h φ s := by
  have hγW := prU_gammaRes q GE GK X K rk pr hpr δ prU _hprU _hprUs _hprUn gU _hgU δU _hδU _hgUspan _hδUn
    i j V hi hj γ hγ W h

  let L₁ : ↥(ker (prU i ⟨W, h.trans hi⟩)) →ₗ[Γ(P, W.1)] GK.obj W.1 :=
    δU j ⟨W, h.trans hj⟩ ∘ₗ
      LinearMap.codRestrict (ker (prU j ⟨W, h.trans hj⟩)) (gammaRes h γ ∘ₗ (ker (prU i ⟨W, h.trans hi⟩)).subtype)
        (fun s => gamma_mem _ _ (gammaRes h γ) hγW s)
  let L₂ : ↥(ker (prU i ⟨W, h.trans hi⟩)) →ₗ[Γ(P, W.1)] GK.obj W.1 :=
    δU i ⟨W, h.trans hi⟩ + phiRes GK h φ ∘ₗ (ker (prU i ⟨W, h.trans hi⟩)).subtype
  suffices hL : L₁ = L₂ from LinearMap.congr_fun hL s
  have hspan_top : Submodule.span Γ(P, W.1) (Set.range (gU i ⟨W, h.trans hi⟩)) = ⊤ := by
    apply Submodule.map_injective_of_injective (ker (prU i ⟨W, h.trans hi⟩)).injective_subtype
    rw [Submodule.map_subtype_top, Submodule.map_span, ← Set.range_comp]
    exact _hgUspan i ⟨W, h.trans hi⟩
  refine LinearMap.ext_on_range hspan_top fun s₀ => ?_

  have hsW : ((gU i ⟨W, h.trans hi⟩ s₀ : ↥(ker (prU i ⟨W, h.trans hi⟩))) : Fin (rk i) → Γ(P, W.1)) =
      fun m => ρ h (((gU i ⟨V, hi⟩ s₀ : ↥(ker (prU i ⟨V, hi⟩))) : Fin (rk i) → Γ(P, V.1)) m) := by
    funext m
    rw [_hgU i ⟨W, h.trans hi⟩ s₀ m, _hgU i ⟨V, hi⟩ s₀ m]
    exact (ρ_ρ hi h _).symm
  have hcoords : ∀ m' : Fin (rk j),
      (gammaRes h γ ((gU i ⟨W, h.trans hi⟩ s₀ : ↥(ker (prU i ⟨W, h.trans hi⟩))) : Fin (rk i) → Γ(P, W.1))) m' =
        (P.presheaf.map (homOfLE h).op).hom
          ((γ ((gU i ⟨V, hi⟩ s₀ : ↥(ker (prU i ⟨V, hi⟩))) : Fin (rk i) → Γ(P, V.1))) m') := by
    intro m'
    rw [hsW, port_gammaRes_rho]
  show δU j ⟨W, h.trans hj⟩ ⟨gammaRes h γ ((gU i ⟨W, h.trans hi⟩ s₀ : ↥(ker (prU i ⟨W, h.trans hi⟩))) : _), _⟩ =
    δU i ⟨W, h.trans hi⟩ (gU i ⟨W, h.trans hi⟩ s₀) +
      phiRes GK h φ ((gU i ⟨W, h.trans hi⟩ s₀ : ↥(ker (prU i ⟨W, h.trans hi⟩))) : Fin (rk i) → Γ(P, W.1))
  rw [_hδUn j ⟨V, hj⟩ ⟨W, h.trans hj⟩ h ⟨γ (gU i ⟨V, hi⟩ s₀ : _), gamma_mem _ _ γ hγ (gU i ⟨V, hi⟩ s₀)⟩ _ hcoords,
    hφ (gU i ⟨V, hi⟩ s₀), map_add, _hδU i ⟨V, hi⟩ s₀, GK.res_res, _hδU i ⟨W, h.trans hi⟩ s₀, hsW, port_phiRes_rho]

end X1bOverlapSol

namespace X1bOverlapAsm

open LinearMap X1bOverlapSol

section Rebase

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C] (alg : Algebra A C)
  {M N : Type u} [AddCommGroup M] [Module C M] [AddCommGroup N] [Module C N]

noncomputable def rebase (f : M →ₗ[C] N) :
    letI : Module A M := Module.compHom M alg.algebraMap
    letI : Module A N := Module.compHom N alg.algebraMap
    M →ₗ[A] N :=
  letI : Module A M := Module.compHom M alg.algebraMap
  letI : Module A N := Module.compHom N alg.algebraMap
  { toFun := f
    map_add' := f.map_add
    map_smul' := fun a x => by
      change f (alg.algebraMap a • x) = alg.algebraMap a • f x
      exact f.map_smul _ x }

theorem rebase_apply (f : M →ₗ[C] N) (x : M) : rebase alg f x = f x := rfl

theorem coe_rebase (f : M →ₗ[C] N) : ⇑(rebase alg f) = ⇑f := rfl

end Rebase

end X1bOverlapAsm

open X1bOverlapSol X1bOverlapAsm in
theorem solution
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsLocallyNoetherian P] [IsSeparated q]
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)

    (X : OModulePresheaf q) (hXc : X.IsCoherent) (hXq : X.IsQuasicoherent)
    (εX : ∀ (W : P.affineOpens) (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1), Function.Surjective p →
        (X.obj W.1 ≃ₗ[Γ(P, W.1)]
          ((↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) ⧸
            LinearMap.range (LinearMap.lcomp (Γ(P, W.1)) (GK.obj W.1) (LinearMap.ker p).subtype))))
    (hXf : ∀ (W W' : P.affineOpens) (h : W'.1 ≤ W.1)
        (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1) (hp : Function.Surjective p)
        (r' : ℕ) (p' : (Fin r' → Γ(P, W'.1)) →ₗ[Γ(P, W'.1)] GE.obj W'.1) (hp' : Function.Surjective p')
        (g : (Fin r → Γ(P, W.1)) →+ (Fin r' → Γ(P, W'.1)))
        (_hg : ∀ (a : Γ(P, W.1)) (v : Fin r → Γ(P, W.1)), g (a • v) = (P.presheaf.map (homOfLE h).op).hom a • g v)
        (hgp : ∀ v : Fin r → Γ(P, W.1), p' (g v) = GE.res h (p v))
        (δ : ↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) (δ' : ↥(LinearMap.ker p') →ₗ[Γ(P, W'.1)] GK.obj W'.1)
        (hδ : ∀ s : ↥(LinearMap.ker p),
          δ' ⟨g s.1, by rw [LinearMap.mem_ker, hgp, (LinearMap.mem_ker.mp s.2), map_zero]⟩ = GK.res h (δ s)),
        X.res h ((εX W r p hp).symm (Submodule.Quotient.mk δ)) = (εX W' r' p' hp').symm (Submodule.Quotient.mk δ'))

    (K : P.OrderedAffineCover) (rk : K.ι → ℕ)
    (pr : ∀ i : K.ι, (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] GE.obj (K.U i))
    (hpr : ∀ i : K.ι, Function.Surjective (pr i))
    (δ : ∀ i : K.ι, ↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i))
    (hδ : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      X.res hi ((εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk (δ i))) =
      X.res hj ((εX ⟨K.U j, K.isAffineOpen j⟩ (rk j) (pr j) (hpr j)).symm (Submodule.Quotient.mk (δ j))))

    (prU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        (Fin (rk i) → Γ(P, U.1.1)) →ₗ[Γ(P, U.1.1)] GE.obj U.1.1)
      (_hprU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (v : Fin (rk i) → Γ(P, K.U i)),
        prU i U (fun m => (P.presheaf.map (homOfLE U.2).op).hom (v m)) = GE.res U.2 (pr i v))
      (_hprUs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (prU i U))
      (_hprUn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (v : Fin (rk i) → Γ(P, U.1.1)),
        prU i U' (fun m => (P.presheaf.map (homOfLE h).op).hom (v m)) = GE.res h (prU i U v))
      (gU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), ↥(LinearMap.ker (pr i)) → ↥(LinearMap.ker (prU i U)))
      (_hgU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (pr i))) (m : Fin (rk i)),
        ((gU i U s : ↥(LinearMap.ker (prU i U))) : Fin (rk i) → Γ(P, U.1.1)) m =
          (P.presheaf.map (homOfLE U.2).op).hom ((s : Fin (rk i) → Γ(P, K.U i)) m))
      (δU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), ↥(LinearMap.ker (prU i U)) →ₗ[Γ(P, U.1.1)] GK.obj U.1.1)
      (_hδU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (pr i))),
        δU i U (gU i U s) = GK.res U.2 (δ i s))
      (_hgUspan : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        Submodule.span Γ(P, U.1.1)
            (Set.range fun s : ↥(LinearMap.ker (pr i)) =>
              ((gU i U s : ↥(LinearMap.ker (prU i U))) : Fin (rk i) → Γ(P, U.1.1))) =
          LinearMap.ker (prU i U))
      (_hδUn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1)
        (s : ↥(LinearMap.ker (prU i U))) (s' : ↥(LinearMap.ker (prU i U'))),
        (∀ m : Fin (rk i), (s' : Fin (rk i) → Γ(P, U'.1.1)) m = (P.presheaf.map (homOfLE h).op).hom ((s : Fin (rk i) → Γ(P, U.1.1)) m)) →
        δU i U' s' = GK.res h (δU i U s))

      (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 →
        LinearMap.ExtPushout (prU i U) (δU i U) → LinearMap.ExtPushout (prU i U') (δU i U'))
      (res_add : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (x y : LinearMap.ExtPushout (prU i U) (δU i U)),
        res i h (x + y) = res i h x + res i h y)
      (res_inl : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (n : GK.obj U.1.1),
        res i h (LinearMap.ExtPushout.inl (prU i U) (δU i U) n) = LinearMap.ExtPushout.inl (prU i U') (δU i U') (GK.res h n))
      (res_inr : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (v : Fin (rk i) → Γ(P, U.1.1)),
        res i h (LinearMap.ExtPushout.inr (prU i U) (δU i U) v) =
          LinearMap.ExtPushout.inr (prU i U') (δU i U') (fun m => (P.presheaf.map (homOfLE h).op).hom (v m))) :
    letI : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (LinearMap.ExtPushout (prU i U) (δU i U)) :=
      fun i U => Module.compHom _ (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1).algebraMap
    ∃ (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), LinearMap.ExtPushout (prU i W) (δU i W) →ₗ[A] LinearMap.ExtPushout (prU j ⟨W.1, hj⟩) (δU j ⟨W.1, hj⟩))
      (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
      (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : LinearMap.ExtPushout (prU i W) (δU i W)),
          u i j W hj (a • x) = a • u i j W hj x)
      (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : LinearMap.ExtPushout (prU i W) (δU i W)),
          u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x)),
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
          u i j W hj (LinearMap.ExtPushout.inl (prU i W) (δU i W) x) = LinearMap.ExtPushout.inl (prU j ⟨W.1, hj⟩) (δU j ⟨W.1, hj⟩) x) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : LinearMap.ExtPushout (prU i W) (δU i W)),
        LinearMap.ExtPushout.proj (prU j ⟨W.1, hj⟩) (δU j ⟨W.1, hj⟩) (u i j W hj x) = LinearMap.ExtPushout.proj (prU i W) (δU i W) x) := by

  have hVaff : ∀ i j : K.ι, IsAffineOpen (K.U i ⊓ K.U j) := fun i j =>
    Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated q (K.isAffineOpen i) (K.isAffineOpen j)

  have hch : ∀ i j : K.ι, ∃ (γ : (Fin (rk i) → Γ(P, K.U i ⊓ K.U j)) →ₗ[Γ(P, K.U i ⊓ K.U j)] (Fin (rk j) → Γ(P, K.U i ⊓ K.U j)))
      (hγ : ∀ v, prU j ⟨⟨K.U i ⊓ K.U j, hVaff i j⟩, inf_le_right⟩ (γ v) = prU i ⟨⟨K.U i ⊓ K.U j, hVaff i j⟩, inf_le_left⟩ v)
      (φ : (Fin (rk i) → Γ(P, K.U i ⊓ K.U j)) →ₗ[Γ(P, K.U i ⊓ K.U j)] GK.obj (K.U i ⊓ K.U j)),
      ∀ s : ↥(LinearMap.ker (prU i ⟨⟨K.U i ⊓ K.U j, hVaff i j⟩, inf_le_left⟩)),
        δU j ⟨⟨K.U i ⊓ K.U j, hVaff i j⟩, inf_le_right⟩ ⟨γ s, gamma_mem _ _ γ hγ s⟩ =
          δU i ⟨⟨K.U i ⊓ K.U j, hVaff i j⟩, inf_le_left⟩ s + φ s := fun i j =>
    exists_lift_corr q GE GK X εX hXf K rk pr hpr δ hδ prU _hprU _hprUs _hprUn gU _hgU δU _hδU i j
      ⟨K.U i ⊓ K.U j, hVaff i j⟩ inf_le_left inf_le_right
  choose γ hγ φ hφ using hch

  have hWV : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j),
      W.1.1 ≤ (⟨K.U i ⊓ K.U j, hVaff i j⟩ : P.affineOpens).1 := fun i j W hj => le_inf W.2 hj
  have hγW : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (v : Fin (rk i) → Γ(P, W.1.1)),
      prU j ⟨W.1, hj⟩ (gammaRes (hWV i j W hj) (γ i j) v) = prU i W v := fun i j W hj v =>
    prU_gammaRes q GE GK X K rk pr hpr δ prU _hprU _hprUs _hprUn gU _hgU δU _hδU _hgUspan _hδUn i j
      ⟨K.U i ⊓ K.U j, hVaff i j⟩ inf_le_left inf_le_right (γ i j) (hγ i j) W.1 (hWV i j W hj) v
  have hφW : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j)
      (s : ↥(LinearMap.ker (prU i W))),
      δU j ⟨W.1, hj⟩ ⟨gammaRes (hWV i j W hj) (γ i j) s, gamma_mem _ _ _ (hγW i j W hj) s⟩ =
        δU i W s + phiRes GK (hWV i j W hj) (φ i j) s := fun i j W hj s =>
    deltaU_gammaRes q GE GK X K rk pr hpr δ prU _hprU _hprUs _hprUn gU _hgU δU _hδU _hgUspan _hδUn i j
      ⟨K.U i ⊓ K.U j, hVaff i j⟩ inf_le_left inf_le_right (γ i j) (hγ i j) (φ i j) (hφ i j) W.1 (hWV i j W hj) s
  let uC := fun (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) =>
    coreMap (prU i W) (δU i W) (prU j ⟨W.1, hj⟩) (δU j ⟨W.1, hj⟩)
      (gammaRes (hWV i j W hj) (γ i j)) (phiRes GK (hWV i j W hj) (φ i j)) (hγW i j W hj) (hφW i j W hj)
  refine ⟨fun i j W hj => rebase (Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1) (uC i j W hj), ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i j W hj
    rw [coe_rebase]
    exact ⟨coreMap_injective _ _ _ _ _ _ _ _, coreMap_surjective _ _ _ _ _ _ _ _ (_hprUs i W)⟩
  ·
    intro i j W hj a x
    rw [rebase_apply, rebase_apply]
    exact map_smul (uC i j W hj) a x
  ·
    intro i j W W' hj h x
    rw [rebase_apply, rebase_apply]
    have hsub : ∀ (x y : LinearMap.ExtPushout (prU j ⟨W.1, hj⟩) (δU j ⟨W.1, hj⟩)),
        res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (x - y) =
          res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h x - res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h y :=
      fun x y => (AddMonoidHom.mk' _ (res_add j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h)).map_sub x y
    refine addHom_ext (prU i W) (δU i W)
      (fun x => uC i j W' (h.trans hj) (res i h x))
      (fun x => res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (uC i j W hj x))
      (fun x y => by beta_reduce; rw [res_add, map_add]) (fun x y => by beta_reduce; rw [map_add, res_add]) ?_ ?_ x
    · intro n
      show uC i j W' (h.trans hj) (res i h (LinearMap.ExtPushout.inl (prU i W) (δU i W) n)) =
        res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (uC i j W hj (LinearMap.ExtPushout.inl (prU i W) (δU i W) n))
      rw [res_inl, coreMap_inl, coreMap_inl, res_inl]
    · intro v
      show uC i j W' (h.trans hj) (res i h (LinearMap.ExtPushout.inr (prU i W) (δU i W) v)) =
        res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (uC i j W hj (LinearMap.ExtPushout.inr (prU i W) (δU i W) v))
      rw [res_inr, coreMap_inr, coreMap_inr, hsub, res_inr, res_inl, ← gammaRes_res, ← phiRes_res]
  ·
    intro i j W hj x
    rw [rebase_apply]
    exact coreMap_inl _ _ _ _ _ _ _ _ x
  ·
    intro i j W hj x
    rw [rebase_apply]
    exact proj_coreMap _ _ _ _ _ _ _ _ x

end S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq (solution)
