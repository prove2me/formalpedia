-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/22d5c839-6896-538e-9ee0-5be9bc2a7f0e

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_LinearMap_ExtPushout
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_chartModels_extPushout_of_forall_res_symm_mk_eq
import Theorems.Thm_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace RedX1

theorem mem_smul_top_map {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (I : Ideal R) (f : M →ₗ[R] M') {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) : f x ∈ I • (⊤ : Submodule R M') := by
  have h : f x ∈ (I • (⊤ : Submodule R M)).map f := Submodule.mem_map_of_mem hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem mem_map_pow_smul_top_iff {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] (I : Ideal R) (m : ℕ) (x : M) :
    x ∈ (I.map (algebraMap R S)) ^ m • (⊤ : Submodule S M) ↔ x ∈ I ^ m • (⊤ : Submodule R M) := by
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

theorem mem_smul_top_sup_of_mkQ {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (p : Submodule R M) (x : M) (h : p.mkQ x ∈ I • (⊤ : Submodule R (M ⧸ p))) : x ∈ I • (⊤ : Submodule R M) ⊔ p := by
  have e : (I • (⊤ : Submodule R (M ⧸ p))) = (I • (⊤ : Submodule R M)).map p.mkQ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [e] at h
  have h' : x ∈ (Submodule.map p.mkQ (I • ⊤)).comap p.mkQ := h
  rw [Submodule.comap_map_mkQ] at h'
  rwa [sup_comm]

def e {B : Type*} [CommRing B] {r : ℕ} (m : Fin r) : Fin r → B := fun j => if m = j then 1 else 0

theorem e_map {B C : Type*} [CommRing B] [CommRing C] (f : B →+* C) {r : ℕ} (m j : Fin r) :
    f (e m j) = e m j := by
  unfold e; split_ifs <;> simp

theorem apply_eq_sum_e {B : Type*} [CommRing B] {r : ℕ} {N : Type*} [AddCommGroup N] [Module B N]
    (g : (Fin r → B) →ₗ[B] N) (v : Fin r → B) : g v = ∑ m, v m • g (e m) :=
  LinearMap.pi_apply_eq_sum_univ g v

section Theta

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C]
variable {GEU GKU FU : Type u} [AddCommGroup GEU] [Module C GEU] [AddCommGroup GKU] [Module C GKU]
  [AddCommGroup FU] [Module C FU] [Module A FU]
variable {r : ℕ} (pU : (Fin r → C) →ₗ[C] GEU) (dU : ↥(LinearMap.ker pU) →ₗ[C] GKU)
  (lamC : GKU →ₗ[C] FU) (w : Fin r → FU)
  (h : ∀ s : ↥(LinearMap.ker pU), lamC (dU s) = Fintype.linearCombination C w (s : Fin r → C))

noncomputable def thetaC : LinearMap.ExtPushout pU dU →ₗ[C] FU :=
  LinearMap.ExtPushout.lift pU dU lamC (Fintype.linearCombination C w) h

theorem thetaC_inl (n : GKU) : thetaC pU dU lamC w h (LinearMap.ExtPushout.inl pU dU n) = lamC n :=
  LinearMap.ExtPushout.lift_inl pU dU _ _ h n

theorem thetaC_inr (v : Fin r → C) : thetaC pU dU lamC w h (LinearMap.ExtPushout.inr pU dU v) = ∑ m, v m • w m := by
  rw [thetaC, LinearMap.ExtPushout.lift_inr, Fintype.linearCombination_apply]

variable (alg : Algebra A C)

noncomputable def theta (hst : letI := alg; IsScalarTower A C FU) :
    letI : Module A (LinearMap.ExtPushout pU dU) := Module.compHom _ alg.algebraMap
    LinearMap.ExtPushout pU dU →ₗ[A] FU :=
  letI : Module A (LinearMap.ExtPushout pU dU) := Module.compHom _ alg.algebraMap
  letI := alg
  { toFun := thetaC pU dU lamC w h
    map_add' := (thetaC pU dU lamC w h).map_add
    map_smul' := fun a x => by
      change thetaC pU dU lamC w h (alg.algebraMap a • x) = a • thetaC pU dU lamC w h x
      rw [map_smul]
      exact algebraMap_smul C a _ }

theorem theta_apply (hst : letI := alg; IsScalarTower A C FU) (x : LinearMap.ExtPushout pU dU) :
    theta pU dU lamC w h alg hst x = thetaC pU dU lamC w h x := rfl

end Theta

theorem isScalarTower_compHom {A C M : Type*} [CommRing A] [CommRing C] (alg : Algebra A C)
    [AddCommGroup M] [Module C M] :
    letI : Module A M := Module.compHom M alg.algebraMap
    letI := alg
    IsScalarTower A C M :=
  letI : Module A M := Module.compHom M alg.algebraMap
  letI := alg
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

section Simplices

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

abbrev vtx (i : K.ι) : K.Idx 0 :=
  ⟨fun _ => i, fun a b hab => absurd (Fin.lt_def.mp hab) (by have ha := a.isLt; have hb := b.isLt; omega)⟩

theorem le_inter_vtx (i : K.ι) : K.U i ≤ K.inter (vtx K i) := le_iInf fun _ => le_rfl

theorem strictMono_pair {i j : K.ι} (hij : i < j) : StrictMono ![i, j] := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact absurd hab (lt_irrefl _)
  · simpa using hij
  · exact absurd hab (by decide)
  · exact absurd hab (lt_irrefl _)

def edge {i j : K.ι} (hij : i < j) : K.Idx 1 := ⟨![i, j], strictMono_pair K hij⟩

theorem edge_val_zero {i j : K.ι} (hij : i < j) : (edge K hij).1 0 = i := rfl
theorem edge_val_one {i j : K.ι} (hij : i < j) : (edge K hij).1 1 = j := rfl

theorem face_edge_zero {i j : K.ι} (hij : i < j) : K.face (edge K hij) 0 = vtx K j :=
  Subtype.ext (funext fun k => by fin_cases k; rfl)

theorem face_edge_one {i j : K.ι} (hij : i < j) : K.face (edge K hij) 1 = vtx K i :=
  Subtype.ext (funext fun k => by fin_cases k; rfl)

theorem le_inter_edge {i j : K.ι} (hij : i < j) {W : V.Opens} (hi : W ≤ K.U i) (hj : W ≤ K.U j) :
    W ≤ K.inter (edge K hij) :=
  le_iInf fun k => by
    fin_cases k
    · exact hi
    · exact hj

end Simplices

theorem res_vtx_eq_of_d_eq_zero {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (X : OModulePresheaf π) (K : V.OrderedAffineCover) (a : X.cochain K 0) (hda : X.d K 0 a = 0)
    (i j : K.ι) {W : V.Opens} (hi : W ≤ K.inter (vtx K i)) (hj : W ≤ K.inter (vtx K j)) :
    X.res hi (a (vtx K i)) = X.res hj (a (vtx K j)) := by
  have tr : ∀ {s s' : K.Idx 0} (_ : s = s') {W : V.Opens} (h : W ≤ K.inter s) (h' : W ≤ K.inter s'),
      X.res h (a s) = X.res h' (a s') := by
    intro s s' e; subst e; intro W h h'; rfl
  have key : ∀ (i j : K.ι) (hij : i < j) {W : V.Opens} (hi : W ≤ K.inter (vtx K i)) (hj : W ≤ K.inter (vtx K j)),
      X.res hi (a (vtx K i)) = X.res hj (a (vtx K j)) := by
    intro i j hij W hi hj
    have h0 := congr_fun hda (edge K hij)
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two, Pi.zero_apply] at h0
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, add_neg_eq_zero] at h0
    have hW : W ≤ K.inter (edge K hij) :=
      le_inter_edge K hij (hi.trans (K.inter_le (vtx K i) 0)) (hj.trans (K.inter_le (vtx K j) 0))
    have h1 := congrArg (X.res hW) h0
    rw [X.res_res, X.res_res] at h1
    exact (tr (face_edge_one K hij) _ hi).symm.trans (h1.symm.trans (tr (face_edge_zero K hij) _ hj))
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact key i j hij hi hj
  · rfl
  · exact (key j i hji hj hi).symm

set_option maxHeartbeats 4000000 in
theorem stageA
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] [IsLocallyNoetherian P]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))

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
        X.res h ((εX W r p hp).symm (Submodule.Quotient.mk δ)) = (εX W' r' p' hp').symm (Submodule.Quotient.mk δ')) :
    ∃ (K : P.OrderedAffineCover) (rk : K.ι → ℕ)
      (pr : ∀ i : K.ι, (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] GE.obj (K.U i))
      (hpr : ∀ i : K.ι, Function.Surjective (pr i))
      (δ : ∀ i : K.ι, ↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i))
      (ℓ' : ∀ (i : K.ι) (k : ℕ), (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] (F k).obj (K.U i)),
      (∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
        X.res hi ((εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk (δ i))) =
        X.res hj ((εX ⟨K.U j, K.isAffineOpen j⟩ (rk j) (pr j) (hpr j)).symm (Submodule.Quotient.mk (δ j)))) ∧
      (∀ (i : K.ι) (k : ℕ) (v : Fin (rk i) → Γ(P, K.U i)),
        (φ k).app ⟨K.U i, K.isAffineOpen i⟩ (ℓ' i (k + 1) v) = ℓ' i k v) ∧
      (∀ (i : K.ι) (k : ℕ) (v : Fin (rk i) → Γ(P, K.U i)),
        (ε k).app ⟨K.U i, K.isAffineOpen i⟩ (ℓ' i k v) = (ψE k).app ⟨K.U i, K.isAffineOpen i⟩ (pr i v)) ∧
      (∀ (i : K.ι) (k : ℕ) (s : ↥(LinearMap.ker (pr i))),
        ℓ' i k (s : Fin (rk i) → Γ(P, K.U i)) = (lam k).app ⟨K.U i, K.isAffineOpen i⟩ (δ i s)) := by
  classical
  obtain ⟨K, rk, pr, hpr, ℓ, δs, t, ha, hb, hc, hd, he, hf, hg⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq
      lam hlamc hlamr hlami X hXc hXq εX hXf
  have hFF := AlgebraicGeometry.OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
      I q X hXc hXq K t hf hg
  obtain ⟨a, ha', _⟩ := hFF
  have hda : X.d K 0 a = 0 := ha'.1
  have hat : ∀ n : ℕ, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (X.cochain K 0)) := ha'.2

  have hrep : ∀ i : K.ι, ∃ δi : ↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i),
      (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk δi) =
        X.res (le_inter_vtx K i) (a (vtx K i)) := fun i => by
    obtain ⟨δi, hδi⟩ := Quotient.exists_rep
      (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i) (X.res (le_inter_vtx K i) (a (vtx K i))))
    exact ⟨δi, by rw [LinearEquiv.symm_apply_eq]; exact hδi⟩
  choose δ hδa using hrep

  have hX1c : ∀ i : K.ι, ∃ ℓ' : ∀ k : ℕ, (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] (F k).obj (K.U i),
      (∀ k, ((φ k).appSections ⟨K.U i, K.isAffineOpen i⟩) ∘ₗ ℓ' (k + 1) = ℓ' k) ∧
      (∀ k, ((ε k).appSections ⟨K.U i, K.isAffineOpen i⟩) ∘ₗ ℓ' k = ((ψE k).appSections ⟨K.U i, K.isAffineOpen i⟩) ∘ₗ pr i) ∧
      (∀ k, ℓ' k ∘ₗ (LinearMap.ker (pr i)).subtype = ((lam k).appSections ⟨K.U i, K.isAffineOpen i⟩) ∘ₗ δ i) := by
    intro i
    letI algi : Algebra A Γ(P, K.U i) := Scheme.TwoAffineOpenCover.algebraOfHom q (K.U i)
    haveI : IsNoetherianRing Γ(P, K.U i) := IsLocallyNoetherian.component_noetherian ⟨K.U i, K.isAffineOpen i⟩
    haveI : Module.Finite Γ(P, K.U i) (GK.obj (K.U i)) := hGKc ⟨K.U i, K.isAffineOpen i⟩
    refine LinearMap.exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
      (I.map (Scheme.TwoAffineOpenCover.algebraOfHom q (K.U i)).algebraMap) (pr i) (hpr i)
      (fun k => (F k).obj (K.U i)) (fun k => (E k).obj (K.U i))
      (fun k => (φ k).appSections ⟨K.U i, K.isAffineOpen i⟩) (fun k => hφs k ⟨K.U i, K.isAffineOpen i⟩) ?_
      (fun k => (ε k).appSections ⟨K.U i, K.isAffineOpen i⟩) (fun k => (ψE k).appSections ⟨K.U i, K.isAffineOpen i⟩)
      (fun k => (lam k).appSections ⟨K.U i, K.isAffineOpen i⟩) ?_ ?_
      (ℓ i) (fun n => LinearMap.ext fun v => ha i n v) (fun n => LinearMap.ext fun v => hb i n v)
      (δs i) (fun n => LinearMap.ext fun s => hc i n s) (hd i) (δ i) ?_
    ·
      intro k
      ext x
      rw [LinearMap.mem_ker, OModulePresheaf.AffHom.appSections_apply, ← LinearMap.mem_ker, hφk k ⟨K.U i, K.isAffineOpen i⟩]
      exact (mem_map_pow_smul_top_iff I (k + 1) x).symm
    · intro k
      exact LinearMap.ext fun x => LinearMap.congr_fun (hlamc k ⟨K.U i, K.isAffineOpen i⟩) x
    · intro k
      ext x
      have h := SetLike.ext_iff.mp (hlamr k ⟨K.U i, K.isAffineOpen i⟩) x
      simp only [LinearMap.mem_range, LinearMap.mem_ker] at h
      simp only [LinearMap.mem_range, LinearMap.mem_ker, OModulePresheaf.AffHom.appSections_apply]
      exact h
    ·
      intro n
      have h1 : (a - t n) (vtx K i) ∈ I ^ (n + 1) • (⊤ : Submodule A (X.obj (K.inter (vtx K i)))) :=
        mem_smul_top_map (I ^ (n + 1)) (LinearMap.proj (vtx K i)) (hat n)
      have e1 : X.res (le_inter_vtx K i) (t n (vtx K i)) =
          (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk (δs i n)) := by
        rw [he n (vtx K i), X.res_res]
        exact X.res_refl_apply _ _
      have h3 : (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk (δ i)) -
          (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk (δs i n)) ∈
          I ^ (n + 1) • (⊤ : Submodule A (X.obj (K.U i))) := by
        rw [hδa i, ← e1, ← map_sub]
        exact mem_smul_top_map _ _ h1
      have h4 : (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm
          (Submodule.Quotient.mk (δ i) - Submodule.Quotient.mk (δs i n)) ∈
          (I.map (Scheme.TwoAffineOpenCover.algebraOfHom q (K.U i)).algebraMap) ^ (n + 1) •
            (⊤ : Submodule Γ(P, K.U i) (X.obj (K.U i))) := by
        rw [map_sub]
        exact (mem_map_pow_smul_top_iff I (n + 1) _).mpr h3
      have h5 := mem_smul_top_map _ (εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).toLinearMap h4
      rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, ← Submodule.Quotient.mk_sub] at h5
      exact mem_smul_top_sup_of_mkQ _ _ _ h5
  choose ℓ' hℓ'1 hℓ'2 hℓ'3 using hX1c
  refine ⟨K, rk, pr, hpr, δ, ℓ', ?_, ?_, ?_, ?_⟩
  · intro i j W hi hj
    rw [hδa i, hδa j, X.res_res, X.res_res]
    exact res_vtx_eq_of_d_eq_zero X K a hda i j _ _
  · intro i k v; exact LinearMap.congr_fun (hℓ'1 i k) v
  · intro i k v; exact LinearMap.congr_fun (hℓ'2 i k) v
  · intro i k s; exact LinearMap.congr_fun (hℓ'3 i k) s

end RedX1

open RedX1 in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (K : P.OrderedAffineCover)
      (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
      (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U))
      (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U))
      (iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U))
      (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
          letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U))
      (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
      (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : M i U),
          res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
      (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i U), res i (le_refl U.1.1) x = x)
      (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
          (x : M i U), res i (h.trans h') x = res i h (res i h' x))
      (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
          (∀ y : M i Ug, ∃ (n : ℕ) (x : M i U),
              res i (hUg.trans_le (P.basicOpen_le g)) x =
                (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
          (∀ x : M i U, res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (M i U))
      (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
      (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
      (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
      (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
      (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
      (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
          θF i k U (a • x) = a • θF i k U x)
      (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
          ϑ i U' (GK.res h x) = res i h (ϑ i U x))
      (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
          θE i U' (res i h x) = GE.res h (θE i U x))
      (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
          θF i k U' (res i h x) = (F k).res h (θF i k U x))
      (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
      (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
      (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
      (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
      (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
      (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)
      (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
      (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
      (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
          letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
          u i j W hj (a • x) = a • u i j W hj x)
      (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
          u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
      (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
          u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x),
      ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x := by
  classical
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨X, εX, hXc, hXq, hXf⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_extQuot_of_isCoherent q GE GK hGEc hGEq hGKc hGKq
  obtain ⟨K, rk, pr, hpr, δ, ℓ', hδ, hℓ'φ, hℓ'ε, hℓ'δ⟩ :=
    RedX1.stageA I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc
      GK hGKc hGKq lam hlamc hlamr hlami X hXc hXq εX hXf
  obtain ⟨prU, hprU, hprUs, gU, hgU, δU, hδU, hgUspan, hst, res, res_smul, res_refl, res_comp, hqc, hfg, ϑ, θE,
      hϑs, hθEs, hϑn, hθEn, hexact, hsurj, hϑi, u, hub, hus, hun, huϑ, huθE, hϑinl, hθEproj, hresinl, hresinr⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_chartModels_extPushout_of_forall_res_symm_mk_eq
      q GE hGEc hGEq GK hGKc hGKq X hXc hXq εX hXf K rk pr hpr δ hδ
  letI instA : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
      Module A (LinearMap.ExtPushout (prU i U) (δU i U)) :=
    fun i U => Module.compHom _ (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1).algebraMap

  have split : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : LinearMap.ExtPushout (prU i U) (δU i U)),
      ∃ (n : GK.obj U.1.1) (v : Fin (rk i) → Γ(P, U.1.1)),
        x = LinearMap.ExtPushout.inl (prU i U) (δU i U) n + LinearMap.ExtPushout.inr (prU i U) (δU i U) v := by
    intro i U x
    obtain ⟨⟨n, v⟩, rfl⟩ := LinearMap.ExtPushout.mk_surjective (prU i U) (δU i U) x
    exact ⟨n, v, LinearMap.ExtPushout.mk_eq_inl_add_inr _ _ n v⟩

  have hprUe : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (m : Fin (rk i)),
      prU i U (e m) = GE.res U.2 (pr i (e m)) := by
    intro i U m
    have h := hprU i U (e m)
    rwa [show (fun m' => (P.presheaf.map (homOfLE U.2).op).hom (e m m')) = e m from
      funext fun m' => e_map _ m m'] at h

  have hspan_top : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
      Submodule.span Γ(P, U.1.1) (Set.range (gU i U)) = ⊤ := by
    intro i U
    apply Submodule.map_injective_of_injective (LinearMap.ker (prU i U)).injective_subtype
    rw [Submodule.map_subtype_top, Submodule.map_span, ← Set.range_comp]
    exact hgUspan i U

  let w : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Fin (rk i) → (F k).obj U.1.1 :=
    fun i k U m => (F k).res U.2 (ℓ' i k (e m))
  have w_def : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (m : Fin (rk i)),
      w i k U m = (F k).res U.2 (ℓ' i k (e m)) := fun _ _ _ _ => rfl

  have compat' : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
      ((lam k).appSections U.1) ∘ₗ (δU i U) =
        (Fintype.linearCombination _ (w i k U)) ∘ₗ (LinearMap.ker (prU i U)).subtype := by
    intro i k U
    refine LinearMap.ext_on_range (hspan_top i U) fun s₀ => ?_
    simp only [LinearMap.comp_apply, OModulePresheaf.AffHom.appSections_apply, Submodule.subtype_apply,
      Fintype.linearCombination_apply]
    rw [hδU, (lam k).naturality_apply (U := U.1) (U' := ⟨K.U i, K.isAffineOpen i⟩) U.2, ← hℓ'δ,
      apply_eq_sum_e (ℓ' i k) (s₀ : Fin (rk i) → Γ(P, K.U i)), map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [w_def, hgU, (F k).res_smul]
  have compat : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (prU i U))),
      (lam k).appSections U.1 (δU i U s) = Fintype.linearCombination _ (w i k U) (s : Fin (rk i) → Γ(P, U.1.1)) :=
    fun i k U s => LinearMap.congr_fun (compat' i k U) s

  let θF := fun (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) =>
    theta (prU i U) (δU i U) ((lam k).appSections U.1) (w i k U) (compat i k U)
      (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1) ((F k).isScalarTower U.1.1)
  have θF_apply : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : LinearMap.ExtPushout (prU i U) (δU i U)),
      θF i k U x = thetaC (prU i U) (δU i U) ((lam k).appSections U.1) (w i k U) (compat i k U) x := fun _ _ _ _ => rfl
  have θinl : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (n : GK.obj U.1.1),
      θF i k U (LinearMap.ExtPushout.inl (prU i U) (δU i U) n) = (lam k).app U.1 n := by
    intro i k U n; rw [θF_apply, thetaC_inl]; rfl
  have θinr : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (v : Fin (rk i) → Γ(P, U.1.1)),
      θF i k U (LinearMap.ExtPushout.inr (prU i U) (δU i U) v) = ∑ m, v m • (F k).res U.2 (ℓ' i k (e m)) := by
    intro i k U v; rw [θF_apply, thetaC_inr]
  refine ⟨K, fun i U => LinearMap.ExtPushout (prU i U) (δU i U), fun i U => inferInstance,
    instA, fun i U => inferInstance,
    fun i U => isScalarTower_compHom (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1), res, res_smul, res_refl, res_comp, hqc, hfg, ϑ, θE, θF,
    hϑs, hθEs, ?_, hϑn, hθEn, ?_, hexact, hsurj, hϑi, ?_, ?_, ?_, u, hub, hus, hun, huϑ, huθE⟩
  ·
    intro i k U a x
    rw [θF_apply, θF_apply]
    exact map_smul _ a x
  ·
    intro i k U U' h x
    obtain ⟨n, v, rfl⟩ := split i U x
    simp only [map_add, hresinl, hresinr, θinl, θinr]
    rw [(lam k).naturality_apply (U := U'.1) (U' := U.1) h, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [(F k).res_smul, (F k).res_res]
  ·
    intro i k U
    apply LinearMap.ext
    intro x
    obtain ⟨n, v, rfl⟩ := split i U x
    simp only [LinearMap.comp_apply, map_add, θinl, θinr]
    have h1 := LinearMap.congr_fun (hlamc k U.1) n
    rw [LinearMap.comp_apply] at h1
    rw [h1, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [(φ k).app_smul, (φ k).naturality_apply (U := U.1) (U' := ⟨K.U i, K.isAffineOpen i⟩) U.2, hℓ'φ]
  ·
    intro i k U
    exact LinearMap.ext fun x => by rw [LinearMap.comp_apply, hϑinl, θinl]
  ·
    intro i k U
    apply LinearMap.ext
    intro x
    obtain ⟨n, v, rfl⟩ := split i U x
    simp only [LinearMap.comp_apply, map_add, θinl, θinr, hθEproj, LinearMap.ExtPushout.proj_inl,
      LinearMap.ExtPushout.proj_inr, map_zero, zero_add]
    have h0 : (ε k).app U.1 ((lam k).app U.1 n) = 0 := by
      have hm : (lam k).app U.1 n ∈ LinearMap.range ((lam k).app U.1) := ⟨n, rfl⟩
      rw [hlamr k U.1] at hm
      exact hm
    rw [h0, zero_add, map_sum, apply_eq_sum_e (prU i U) v, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [(ε k).app_smul, (ψE k).app_smul, (ε k).naturality_apply (U := U.1) (U' := ⟨K.U i, K.isAffineOpen i⟩) U.2, hℓ'ε,
      ← (ψE k).naturality_apply (U := U.1) (U' := ⟨K.U i, K.isAffineOpen i⟩) U.2, hprUe]

end S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete (solution)
