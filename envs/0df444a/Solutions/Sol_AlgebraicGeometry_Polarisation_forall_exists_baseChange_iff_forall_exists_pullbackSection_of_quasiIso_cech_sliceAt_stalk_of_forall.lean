-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.forall_exists_baseChange_iff_forall_exists_pullbackSection_of_quasiIso_cech_sliceAt_stalk_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/fe6610f6-6c16-597d-9278-a3da50328921

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_forall_exists_baseChange_iff_forall_exists_pullbackSection_of_quasiIso_cech_sliceAt_stalk_of_forall

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation Opposite TopologicalSpace TensorProduct"

noncomputable section

namespace S32WB

section AC3
variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) (M : V.Modules)
  (K : V.OrderedAffineCover)

def chain0 (i : K.ι) : K.Idx 0 := ⟨fun _ => i, fun a b h => absurd h (by omega)⟩

theorem idx0_eq (t : K.Idx 0) : t = chain0 K (t.1 0) := by
  apply Subtype.ext
  funext j
  show t.1 j = t.1 0
  exact congrArg t.1 (Fin.eq_zero j)

theorem U_le_inter_chain0 (i : K.ι) : K.U i ≤ K.inter (chain0 K i) :=
  le_iInf fun _ => le_refl _

theorem inter_le_U (t : K.Idx 0) : K.inter t ≤ K.U (t.1 0) := K.inter_le t 0

def chain1 {i j : K.ι} (h : i < j) : K.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr (fun k => by fin_cases k; simpa using h)⟩

theorem inf_le_inter_chain1 {i j : K.ι} (h : i < j) : K.U i ⊓ K.U j ≤ K.inter (chain1 K h) := by
  apply le_iInf
  intro k
  fin_cases k
  · exact inf_le_left
  · exact inf_le_right

abbrev F : OModulePresheaf π := OModulePresheaf.ofModules π M

theorem res_mem_H0 (x : (F π M).obj ⊤) : (fun s : K.Idx 0 => (F π M).res (le_top : K.inter s ≤ ⊤) x) ∈ (F π M).H0 K := by
  rw [LinearMap.mem_ker]
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, OModulePresheaf.res_res]
  exact add_neg_cancel _

def toH0 : (F π M).obj ⊤ →ₗ[R] (F π M).H0 K :=
  LinearMap.codRestrict ((F π M).H0 K) (LinearMap.pi fun s : K.Idx 0 => (F π M).res (le_top : K.inter s ≤ ⊤))
    (res_mem_H0 π M K)

theorem toH0_apply (x : (F π M).obj ⊤) (s : K.Idx 0) : (toH0 π M K x : (F π M).cochain K 0) s = (F π M).res le_top x := rfl

def shf : TopCat.Sheaf Ab V.toTopCat := ⟨M.presheaf, Scheme.Modules.isSheaf M⟩

theorem toH0_injective : Function.Injective (toH0 π M K) := by
  intro x y hxy
  apply TopCat.Sheaf.eq_of_locally_eq' (shf M) K.U ⊤ (fun i => homOfLE le_top) (K.iSup_eq_top ▸ le_refl _)
  intro i
  show (F π M).res (le_top : K.U i ≤ ⊤) x = (F π M).res le_top y
  have := congrArg (fun c : (F π M).H0 K => (F π M).res (U_le_inter_chain0 K i) ((c : (F π M).cochain K 0) (chain0 K i))) hxy
  simp only [toH0_apply, OModulePresheaf.res_res] at this
  exact this

theorem toH0_surjective : Function.Surjective (toH0 π M K) := by
  intro c
  let sf : ∀ i : K.ι, (F π M).obj (K.U i) := fun i => (F π M).res (U_le_inter_chain0 K i) ((c : (F π M).cochain K 0) (chain0 K i))
  have hsf : ∀ i, sf i = (F π M).res (U_le_inter_chain0 K i) ((c : (F π M).cochain K 0) (chain0 K i)) := fun _ => rfl
  have hker : ∀ s : K.Idx 1, (F π M).d K 0 (c : (F π M).cochain K 0) s = 0 := fun s => by
    have := c.2; rw [LinearMap.mem_ker] at this; exact congrFun this s
  have key : ∀ (W : V.Opens) (t : K.Idx 0) (i₀ : K.ι) (ht : t = chain0 K i₀) (hle : W ≤ K.inter t)
      (hle' : W ≤ K.inter (chain0 K i₀)),
      (F π M).res hle ((c : (F π M).cochain K 0) t) = (F π M).res hle' ((c : (F π M).cochain K 0) (chain0 K i₀)) := by
    intro W t i₀ ht hle hle'; subst ht; rfl
  have hcompat_lt : ∀ {i j : K.ι} (h : i < j),
      (F π M).res (inf_le_left : K.U i ⊓ K.U j ≤ K.U i) (sf i) = (F π M).res (inf_le_right : K.U i ⊓ K.U j ≤ K.U j) (sf j) := by
    intro i j h
    have h0 := hker (chain1 K h)
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two] at h0
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at h0
    rw [add_neg_eq_zero] at h0
    have hf0 : K.face (chain1 K h) 0 = chain0 K j := by
      apply Subtype.ext; funext k; show ![i, j] (Fin.succAbove 0 k) = j
      rw [Fin.eq_zero k]; rfl
    have hf1 : K.face (chain1 K h) 1 = chain0 K i := by
      apply Subtype.ext; funext k; show ![i, j] (Fin.succAbove 1 k) = i
      rw [Fin.eq_zero k]; rfl
    have h1 := congrArg ((F π M).res (inf_le_inter_chain1 K h)) h0
    rw [OModulePresheaf.res_res, OModulePresheaf.res_res] at h1
    rw [hsf, hsf, OModulePresheaf.res_res, OModulePresheaf.res_res]
    rw [key _ _ j hf0 _ ((inf_le_right).trans (U_le_inter_chain0 K j)),
      key _ _ i hf1 _ ((inf_le_left).trans (U_le_inter_chain0 K i))] at h1
    exact h1.symm
  have hcompat : TopCat.Presheaf.IsCompatible (shf M).obj K.U sf := by
    intro i j
    show (F π M).res (inf_le_left : K.U i ⊓ K.U j ≤ K.U i) (sf i) = (F π M).res (inf_le_right : K.U i ⊓ K.U j ≤ K.U j) (sf j)
    rcases lt_trichotomy i j with hij | hij | hji
    · exact hcompat_lt hij
    · subst hij; rfl
    · have := hcompat_lt hji
      have e1 : ∀ (k : K.ι) (hk : K.U i ⊓ K.U j ≤ K.U k) (hk' : K.U j ⊓ K.U i ≤ K.U k) (z : (F π M).obj (K.U k)),
          (F π M).res hk z = (F π M).res (le_of_eq (inf_comm (K.U i) (K.U j))) ((F π M).res hk' z) := by
        intro k hk hk' z; rw [OModulePresheaf.res_res]
      rw [e1 i inf_le_left inf_le_right, e1 j inf_le_right inf_le_left, this]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (shf M) K.U ⊤ (fun i => homOfLE le_top)
    (K.iSup_eq_top ▸ le_refl _) sf hcompat
  refine ⟨s, ?_⟩
  apply Subtype.ext
  funext t
  rw [toH0_apply, idx0_eq K t]
  have hst : (F π M).res (le_top : K.U (t.1 0) ≤ ⊤) s = sf (t.1 0) := hs (t.1 0)
  have e2 : (F π M).res (le_top : K.inter (chain0 K (t.1 0)) ≤ ⊤) s =
      (F π M).res (inter_le_U K (chain0 K (t.1 0))) ((F π M).res (le_top : K.U (t.1 0) ≤ ⊤) s) :=
    ((F π M).res_res (inter_le_U K (chain0 K (t.1 0))) le_top s).symm
  rw [e2, hst, hsf]
  exact ((F π M).res_res (inter_le_U K (chain0 K (t.1 0))) (U_le_inter_chain0 K (t.1 0)) _).trans
    ((F π M).res_refl_apply _ _)

end AC3

section Sec

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) (M : V.Modules)
  (K : V.OrderedAffineCover)

theorem app_map {M' N : V.Modules} (s : M' ⟶ N) {U W : V.Opens} (i : W ⟶ U) (x : Γ(M', U)) :
    N.presheaf.map i.op (s.app U x) = s.app W (M'.presheaf.map i.op x) := by
  have h := s.mapPresheaf.naturality i.op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M', U) → Γ(N, W))) h) x).symm

theorem app_eq_smul_res (s : 𝟙_ V.Modules ⟶ M) (U : V.Opens) (r : Γ(𝟙_ V.Modules, U)) :
    s.app U r = (Scheme.Modules.ofUnitSection U r) •
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) := by
  rw [app_map, ← Scheme.Modules.Hom.app_smul]
  congr 1
  show r = Scheme.Modules.ofUnitSection U r * (V.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) 1
  rw [map_one, mul_one]; rfl

theorem hom_unit_ext {s s' : 𝟙_ V.Modules ⟶ M}
    (h : s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = s'.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) : s = s' := by
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  rw [app_eq_smul_res M s U r, app_eq_smul_res M s' U r, h]

def secH0 (s : 𝟙_ V.Modules ⟶ M) : (F π M).cochain K 0 :=
  fun t => s.app (K.inter t) (Scheme.Modules.toUnitSection _ 1)

theorem secH0_apply (s : 𝟙_ V.Modules ⟶ M) (t : K.Idx 0) :
    secH0 π M K s t = s.app (K.inter t) (Scheme.Modules.toUnitSection _ 1) := rfl

theorem secH0_eq_toH0 (s : 𝟙_ V.Modules ⟶ M) :
    secH0 π M K s = (toH0 π M K (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) : (F π M).cochain K 0) := by
  funext t
  rw [secH0_apply, toH0_apply, app_eq_smul_res, Scheme.Modules.ofUnitSection_toUnitSection, one_smul]
  rfl

theorem secH0_mem (s : 𝟙_ V.Modules ⟶ M) : secH0 π M K s ∈ (F π M).H0 K := by
  rw [secH0_eq_toH0]; exact (toH0 π M K _).2

theorem secH0_injective : Function.Injective (secH0 π M K) := by
  intro s s' h
  apply hom_unit_ext
  apply toH0_injective π M K
  apply Subtype.ext
  rw [← secH0_eq_toH0, ← secH0_eq_toH0, h]

theorem secH0_surjective (c : (F π M).H0 K) : ∃ s : 𝟙_ V.Modules ⟶ M, secH0 π M K s = (c : (F π M).cochain K 0) := by
  obtain ⟨m, hm⟩ := toH0_surjective π M K c

  let σ : M.val.sections := PresheafOfModules.sectionsMk
    (fun U => (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m : Γ(M, U.unop)))
    (by
      intro U W i
      show M.presheaf.map i (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m) = M.presheaf.map _ m
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl)
  refine ⟨(SheafOfModules.unitHomEquiv M).symm σ, ?_⟩
  rw [← hm]
  funext t
  rw [secH0_apply, toH0_apply]
  have h := SheafOfModules.unitHomEquiv_apply_coe M ((SheafOfModules.unitHomEquiv M).symm σ) (op (K.inter t))
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end Sec

end S32WB

namespace WB

open S32WB

theorem S1_rTensor_baseChange {R : Type u} [CommRing R] {B k : Type u} [CommRing B] [CommRing k] [Algebra R B] [Algebra R k]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (δ : M →ₗ[R] N) (uₗ : B →ₗ[R] k) (w : B ⊗[R] M) :
    (δ.baseChange k) (uₗ.rTensor M w) = uₗ.rTensor N ((δ.baseChange B) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => simp [LinearMap.rTensor_tmul, LinearMap.baseChange_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem S2_bijective_ker {A : Type u} [CommRing A] {X0 X1 C0 C1 : Type u}
    [AddCommGroup X0] [Module A X0] [AddCommGroup X1] [Module A X1] [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1]
    (δ : X0 →ₗ[A] X1) (d : C0 →ₗ[A] C1) (Θ0 : X0 →ₗ[A] C0) (Θ1 : X1 →ₗ[A] C1)
    (ha : Θ1 ∘ₗ δ = d ∘ₗ Θ0)
    (hinj : ∀ x : X0, δ x = 0 → Θ0 x = 0 → x = 0)
    (hsurj : ∀ y : C0, d y = 0 → ∃ x : X0, δ x = 0 ∧ Θ0 x = y) :
    ∃ θ : LinearMap.ker δ → LinearMap.ker d, Function.Bijective θ ∧ ∀ x : LinearMap.ker δ, (θ x : C0) = Θ0 x := by
  have hmem : ∀ x : LinearMap.ker δ, Θ0 (x : X0) ∈ LinearMap.ker d := by
    intro x
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← ha, LinearMap.comp_apply, LinearMap.mem_ker.mp x.2, map_zero]
  refine ⟨fun x => ⟨Θ0 (x : X0), hmem x⟩, ⟨?_, ?_⟩, fun x => rfl⟩
  · intro x y hxy
    have h1 : Θ0 ((x : X0) - (y : X0)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact congrArg Subtype.val hxy
    have h2 : δ ((x : X0) - (y : X0)) = 0 := by
      rw [map_sub, LinearMap.mem_ker.mp x.2, LinearMap.mem_ker.mp y.2, sub_zero]
    exact Subtype.ext (sub_eq_zero.mp (hinj _ h2 h1))
  · intro y
    obtain ⟨x, hx, hxy⟩ := hsurj (y : C0) (LinearMap.mem_ker.mp y.2)
    exact ⟨⟨x, LinearMap.mem_ker.mpr hx⟩, Subtype.ext hxy⟩

theorem S3_factor_eq {R : Type u} [CommRing R] {J J' : Ideal R} (h : J' ≤ J) (b : R ⧸ J') :
    Submodule.factor h b = Ideal.Quotient.factor h b := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rfl

theorem S4_surj_iff {KB Kk SB Sk : Type u} (L : KB → Kk) (Rm : SB → Sk) (TB : SB → KB) (Tk : Sk → Kk)
    (hTB : Function.Bijective TB) (hTk : Function.Bijective Tk) (hsq : ∀ s, L (TB s) = Tk (Rm s)) :
    Function.Surjective L ↔ Function.Surjective Rm := by
  constructor
  · intro hL s'
    obtain ⟨kb, hkb⟩ := hL (Tk s')
    obtain ⟨sb, rfl⟩ := hTB.2 kb
    rw [hsq] at hkb
    exact ⟨sb, hTk.1 hkb⟩
  · intro hR kk
    obtain ⟨sk, rfl⟩ := hTk.2 kk
    obtain ⟨sb, rfl⟩ := hR sk
    exact ⟨TB sb, hsq sb⟩

section Rho

variable {XB Xk : Scheme.{0}} (G : Xk ⟶ XB) {FB : XB.Modules} {Fk : Xk.Modules}
  (e : (Scheme.Modules.pullback G).obj FB ≅ Fk)

def rho {UB : XB.Opens} {Uk : Xk.Opens} (hle : Uk ≤ G ⁻¹ᵁ UB) (x : Γ(FB, UB)) : Γ(Fk, Uk) :=
  Fk.presheaf.map (homOfLE hle).op (e.hom.app _ (Scheme.Modules.pullbackLocalSection G x))

theorem rho_add {UB : XB.Opens} {Uk : Xk.Opens} (hle : Uk ≤ G ⁻¹ᵁ UB) (x y : Γ(FB, UB)) :
    rho G e hle (x + y) = rho G e hle x + rho G e hle y := by
  simp only [rho, Scheme.Modules.pullbackLocalSection_add, map_add]

theorem rho_zero {UB : XB.Opens} {Uk : Xk.Opens} (hle : Uk ≤ G ⁻¹ᵁ UB) :
    rho G e hle (0 : Γ(FB, UB)) = 0 := by
  simp only [rho, Scheme.Modules.pullbackLocalSection_zero, map_zero]

theorem iso_inv_hom_app {Y : Scheme.{0}} {M N : Y.Modules} (i : M ≅ N) (U : Y.Opens) (x : Γ(M, U)) :
    i.inv.app U (i.hom.app U x) = x := by
  have h := congrArg (fun φ : M ⟶ M => (Scheme.Modules.Hom.app φ U) x) i.hom_inv_id
  simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, CategoryTheory.comp_apply,
    CategoryTheory.id_apply] using h

theorem comp_app_apply {Y : Scheme.{0}} {M N P : Y.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (U : Y.Opens) (x : Γ(M, U)) :
    (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := by
  rw [Scheme.Modules.Hom.comp_app]; rfl

theorem map_toUnitSection_one {Y : Scheme.{0}} {U W : Y.Opens} (i : W ⟶ U) :
    (𝟙_ Y.Modules).presheaf.map i.op (Scheme.Modules.toUnitSection U 1) = Scheme.Modules.toUnitSection W 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
    Scheme.Modules.ofUnitSection_toUnitSection, map_one]

theorem pullbackSection_app_apply {X' Y' : Scheme.{0}} (G' : X' ⟶ Y') {M : Y'.Modules} (s : 𝟙_ Y'.Modules ⟶ M)
    (U : X'.Opens) (x : Γ(𝟙_ X'.Modules, U)) :
    (Scheme.Modules.pullbackSection G' s).app U x =
      ((Scheme.Modules.pullback G').map s).app U ((Scheme.Modules.pullbackUnitIso G').inv.app U x) := by
  rw [Scheme.Modules.pullbackSection_def]
  rfl

theorem pullbackLocalSection_toUnitSection {X' Y' : Scheme.{0}} (g : X' ⟶ Y') (U : Y'.Opens) (r : Γ(Y', U)) :
    Scheme.Modules.pullbackLocalSection g (Scheme.Modules.toUnitSection U r) =
      (Scheme.Modules.pullbackUnitIso g).inv.app (g ⁻¹ᵁ U) (Scheme.Modules.toUnitSection (g ⁻¹ᵁ U) (g.app U r)) := by
  have h := Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2 g U r
  exact (iso_inv_hom_app (Scheme.Modules.pullbackUnitIso g) (g ⁻¹ᵁ U) _).symm.trans
    (congrArg (fun y => (Scheme.Modules.pullbackUnitIso g).inv.app (g ⁻¹ᵁ U) y) h)

theorem rho_app_one (s : 𝟙_ XB.Modules ⟶ FB) {UB : XB.Opens} {Uk : Xk.Opens} (hle : Uk ≤ G ⁻¹ᵁ UB) :
    rho G e hle (s.app UB (Scheme.Modules.toUnitSection UB 1)) =
      (Scheme.Modules.pullbackSection G s ≫ e.hom).app Uk (Scheme.Modules.toUnitSection Uk 1) := by
  rw [← map_toUnitSection_one (homOfLE hle),
    ← app_map (Scheme.Modules.pullbackSection G s ≫ e.hom) (homOfLE hle) (Scheme.Modules.toUnitSection _ 1),
    comp_app_apply, pullbackSection_app_apply, rho, Scheme.Modules.pullbackLocalSection_app,
    pullbackLocalSection_toUnitSection, map_one]

end Rho

end WB

namespace WBFix

theorem app_map' {Y : Scheme.{0}} {M' N : Y.Modules} (s : M' ⟶ N) {U W : Y.Opens} (i : W ⟶ U) (x : Γ(M', U)) :
    N.presheaf.map i.op (s.app U x) = s.app W (M'.presheaf.map i.op x) := by
  have h := s.mapPresheaf.naturality i.op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M', U) → Γ(N, W))) h) x).symm

theorem map_map_eq {Y : Scheme.{0}} (M : Y.Modules) {U V W : Y.Opensᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (l : U ⟶ W) (x : Γ(M, U.unop)) :
    M.presheaf.map j (M.presheaf.map i x) = M.presheaf.map l x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, Subsingleton.elim (i ≫ j) l]

theorem map_endo_eq {Y : Scheme.{0}} (M : Y.Modules) {U : Y.Opensᵒᵖ} (i : U ⟶ U) (x : Γ(M, U.unop)) :
    M.presheaf.map i x = x := by
  rw [Subsingleton.elim i (𝟙 U), M.presheaf.map_id]; rfl

theorem comp_congr_hom_app_pullbackLocalSection {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (g' : X ⟶ Z)
    (h : f ≫ g = g') (L : Z.Modules) (U : Z.Opens) (y : Γ(L, U)) :
    (((Scheme.Modules.pullbackComp f g).app L ≪≫ (Scheme.Modules.pullbackCongr h).app L :
        (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ≅ (Scheme.Modules.pullback g').obj L)).hom.app
        (f ⁻¹ᵁ (g ⁻¹ᵁ U))
        (Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g y)) =
      ((Scheme.Modules.pullback g').obj L).presheaf.map
        (eqToHom (show f ⁻¹ᵁ (g ⁻¹ᵁ U) = g' ⁻¹ᵁ U by rw [← h]; rfl)).op
        (Scheme.Modules.pullbackLocalSection g' y) := by
  subst h
  show ((Scheme.Modules.pullbackComp f g).app L ≪≫ (Scheme.Modules.pullbackCongr rfl).app L).hom.app
      (f ⁻¹ᵁ (g ⁻¹ᵁ U)) (Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g y)) = _
  rw [Iso.trans_hom, Iso.app_hom, Iso.app_hom, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection]
  have hc : Scheme.Modules.pullbackCongr (rfl : f ≫ g = f ≫ g) = Iso.refl _ := by
    show eqToIso _ = _; rw [eqToIso_refl]
  rw [hc]
  simp only [Iso.refl_hom, NatTrans.id_app, Scheme.Modules.Hom.id_app]
  exact (map_endo_eq ((Scheme.Modules.pullback (f ≫ g)).obj L) _ _).symm

theorem rho_res {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (g' : X ⟶ Z) (h : f ≫ g = g')
    (L : Z.Modules) (W : Z.Opens) (AY : Y.Opens) (AX : X.Opens) (hY : AY ≤ g ⁻¹ᵁ W) (hX : AX ≤ g' ⁻¹ᵁ W)
    (eX : AX = f ⁻¹ᵁ AY) (y : Γ(L, W)) :
    ((Scheme.Modules.pullback g').obj L).presheaf.map (eqToHom eX).op
      ((((Scheme.Modules.pullbackComp f g).app L ≪≫ (Scheme.Modules.pullbackCongr h).app L :
          (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ≅ (Scheme.Modules.pullback g').obj L)).hom.app
        (f ⁻¹ᵁ AY)
        (Scheme.Modules.pullbackLocalSection f
          (((Scheme.Modules.pullback g).obj L).presheaf.map (homOfLE hY).op (Scheme.Modules.pullbackLocalSection g y)))) =
      ((Scheme.Modules.pullback g').obj L).presheaf.map (homOfLE hX).op (Scheme.Modules.pullbackLocalSection g' y) := by
  have hle : f ⁻¹ᵁ AY ≤ g' ⁻¹ᵁ W := by rw [← h]; exact fun _ hx => hY hx
  rw [← Scheme.Modules.map_homOfLE_pullbackLocalSection, ← app_map', comp_congr_hom_app_pullbackLocalSection f g g' h]
  rw [map_map_eq _ _ _ (homOfLE hle).op, map_map_eq _ _ _ (homOfLE hX).op]

end WBFix

namespace WBFix

theorem rho_res_le {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (g' : X ⟶ Z) (h : f ≫ g = g')
    (L : Z.Modules) (W : Z.Opens) (AY : Y.Opens) (AX : X.Opens) (hY : AY ≤ g ⁻¹ᵁ W) (hX : AX ≤ g' ⁻¹ᵁ W)
    (hXY : AX ≤ f ⁻¹ᵁ AY) (y : Γ(L, W)) :
    ((Scheme.Modules.pullback g').obj L).presheaf.map (homOfLE hXY).op
      ((((Scheme.Modules.pullbackComp f g).app L ≪≫ (Scheme.Modules.pullbackCongr h).app L :
          (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ≅ (Scheme.Modules.pullback g').obj L)).hom.app
        (f ⁻¹ᵁ AY)
        (Scheme.Modules.pullbackLocalSection f
          (((Scheme.Modules.pullback g).obj L).presheaf.map (homOfLE hY).op (Scheme.Modules.pullbackLocalSection g y)))) =
      ((Scheme.Modules.pullback g').obj L).presheaf.map (homOfLE hX).op (Scheme.Modules.pullbackLocalSection g' y) := by
  have hle : f ⁻¹ᵁ AY ≤ g' ⁻¹ᵁ W := by rw [← h]; exact fun _ hx => hY hx
  rw [← Scheme.Modules.map_homOfLE_pullbackLocalSection, ← app_map', comp_congr_hom_app_pullbackLocalSection f g g' h]
  rw [map_map_eq _ _ _ (homOfLE hle).op, map_map_eq _ _ _ (homOfLE hX).op]

theorem transition_tmul' {X XB Xk : Scheme.{0}} {B kk : Type} [CommRing B] [CommRing kk]
    (pB : XB ⟶ X) (pk : Xk ⟶ X) (qB : XB ⟶ Spec (CommRingCat.of B)) (qk : Xk ⟶ Spec (CommRingCat.of kk))
    (G : Xk ⟶ XB) (u : B →+* kk) (hG1 : G ≫ pB = pk)
    (FR : X.Modules) (V : X.Opens) (UB : XB.Opens) (hUB : UB ≤ pB ⁻¹ᵁ V) (Uk : Xk.Opens) (hUk : Uk ≤ pk ⁻¹ᵁ V)
    (hW : Uk ≤ G ⁻¹ᵁ UB) (c : Γ(FR, V)) (a : B)
    (hS : Xk.presheaf.map (homOfLE hW).op
        (G.app UB (qB.appLE ⊤ UB le_top ((Scheme.ΓSpecIso (CommRingCat.of B)).inv a))) =
      qk.appLE ⊤ Uk le_top ((Scheme.ΓSpecIso (CommRingCat.of kk)).inv (u a))) :
    ((Scheme.Modules.pullback pk).obj FR).presheaf.map (homOfLE hW).op
      ((((Scheme.Modules.pullbackComp G pB).app FR ≪≫ (Scheme.Modules.pullbackCongr hG1).app FR :
          (Scheme.Modules.pullback G).obj ((Scheme.Modules.pullback pB).obj FR) ≅ (Scheme.Modules.pullback pk).obj FR)).hom.app
        (G ⁻¹ᵁ UB)
        (Scheme.Modules.pullbackLocalSection G
          ((qB.appLE ⊤ UB le_top ((Scheme.ΓSpecIso (CommRingCat.of B)).inv a)) •
            ((Scheme.Modules.pullback pB).obj FR).presheaf.map (homOfLE hUB).op (Scheme.Modules.pullbackLocalSection pB c)))) =
      (qk.appLE ⊤ Uk le_top ((Scheme.ΓSpecIso (CommRingCat.of kk)).inv (u a))) •
        ((Scheme.Modules.pullback pk).obj FR).presheaf.map (homOfLE hUk).op (Scheme.Modules.pullbackLocalSection pk c) := by
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul, Scheme.Modules.map_smul, hS,
    rho_res_le G pB pk hG1 FR V UB Uk hUB hUk hW c]

theorem transition_tmul_datum {X XB Xk : Scheme.{0}} {B kk : Type} [CommRing B] [CommRing kk]
    (pB : XB ⟶ X) (pk : Xk ⟶ X) (qB : XB ⟶ Spec (CommRingCat.of B)) (qk : Xk ⟶ Spec (CommRingCat.of kk))
    (G : Xk ⟶ XB) (u : B →+* kk) (hG1 : G ≫ pB = pk)
    (FR : X.Modules) (V : X.Opens) (UB : XB.Opens) (hUB : UB ≤ pB ⁻¹ᵁ V) (Uk : Xk.Opens) (hUk : Uk ≤ pk ⁻¹ᵁ V)
    (hW : Uk ≤ G ⁻¹ᵁ UB) (c : Γ(FR, V)) (a : B)
    (hS : Xk.presheaf.map (homOfLE hW).op
        (G.app UB (qB.appLE ⊤ UB le_top ((Scheme.ΓSpecIso (CommRingCat.of B)).inv a))) =
      qk.appLE ⊤ Uk le_top ((Scheme.ΓSpecIso (CommRingCat.of kk)).inv (u a)))
    (e : (Scheme.Modules.pullback G).obj ((Scheme.Modules.pullback pB).obj FR) ≅ (Scheme.Modules.pullback pk).obj FR)
    (he : e = (Scheme.Modules.pullbackComp G pB).app FR ≪≫ (Scheme.Modules.pullbackCongr hG1).app FR) :
    ((Scheme.Modules.pullback pk).obj FR).presheaf.map (homOfLE hW).op
      (e.hom.app (G ⁻¹ᵁ UB)
        (Scheme.Modules.pullbackLocalSection G
          (a • (OModulePresheaf.ofModules qB ((Scheme.Modules.pullback pB).obj FR)).res hUB
            ((((Scheme.Modules.pullbackPushforwardAdjunction pB).unit.app FR).app V).hom c)))) =
      (u a) • (OModulePresheaf.ofModules qk ((Scheme.Modules.pullback pk).obj FR)).res hUk
        ((((Scheme.Modules.pullbackPushforwardAdjunction pk).unit.app FR).app V).hom c) := by
  subst he
  rw [OModulePresheaf.ofModules_algebraMap_smul, OModulePresheaf.ofModules_algebraMap_smul,
    Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
    OModulePresheaf.ofModules_res_apply, OModulePresheaf.ofModules_res_apply]
  exact transition_tmul' pB pk qB qk G u hG1 FR V UB hUB Uk hUk hW c a hS

end WBFix

namespace WB

open S32WB

theorem S5_appLE_transition {XB Xk : Scheme.{0}} {B kk : Type} [CommRing B] [CommRing kk]
    (qB : XB ⟶ Spec (CommRingCat.of B)) (qk : Xk ⟶ Spec (CommRingCat.of kk)) (G : Xk ⟶ XB) (u : B →+* kk)
    (hG : G ≫ qB = qk ≫ Spec.map (CommRingCat.ofHom u))
    (U : XB.Opens) (W : Xk.Opens) (hW : W ≤ G ⁻¹ᵁ U) (a : B) :
    Xk.presheaf.map (homOfLE hW).op (G.app U (qB.appLE ⊤ U le_top ((Scheme.ΓSpecIso (CommRingCat.of B)).inv a))) =
      qk.appLE ⊤ W le_top ((Scheme.ΓSpecIso (CommRingCat.of kk)).inv (u a)) := by
  have h1 : G.app U ≫ Xk.presheaf.map (homOfLE hW).op = G.appLE U W hW := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have h2 : qB.appLE ⊤ U le_top ≫ G.appLE U W hW = (G ≫ qB).appLE ⊤ W le_top := by
    rw [Scheme.Hom.appLE_comp_appLE]
  have h3 : (Spec.map (CommRingCat.ofHom u)).appLE ⊤ ⊤ le_top ≫ qk.appLE ⊤ W le_top =
      (qk ≫ Spec.map (CommRingCat.ofHom u)).appLE ⊤ W le_top := by
    rw [Scheme.Hom.appLE_comp_appLE]
  have h4 : (Spec.map (CommRingCat.ofHom u)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom u)).appTop := by
    show _ = (Spec.map (CommRingCat.ofHom u)).app ⊤
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  have hφ : ∀ (φ ψ : Xk ⟶ Spec (CommRingCat.of B)) (h : φ = ψ) (e : W ≤ φ ⁻¹ᵁ ⊤) (e' : W ≤ ψ ⁻¹ᵁ ⊤),
      φ.appLE ⊤ W e = ψ.appLE ⊤ W e' := by
    intro φ ψ h e e'; subst h; rfl
  have key : qB.appLE ⊤ U le_top ≫ (G.app U ≫ Xk.presheaf.map (homOfLE hW).op) =
      (Spec.map (CommRingCat.ofHom u)).appTop ≫ qk.appLE ⊤ W le_top := by
    rw [h1, h2, ← h4, h3]
    exact hφ _ _ hG _ _
  have h5 : (Scheme.ΓSpecIso (CommRingCat.of kk)).inv (u a) =
      (Spec.map (CommRingCat.ofHom u)).appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv a) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    rfl
  rw [h5]
  have e := congrArg (fun φ : Γ(Spec (CommRingCat.of B), ⊤) ⟶ Γ(Xk, W) => φ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv a)) key
  simpa only [CommRingCat.comp_apply] using e

section Bridge

variable {R : Type} [CommRing R] {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of R)) (FR : X.Modules)
  (𝒦R : X.OrderedAffineCover) (J I : Ideal R) (hJI : J ≤ I)

theorem inter_le_of
    (G : pullback π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)) ⟶ pullback π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))
    (hG1 : G ≫ pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)) = pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))
    (t : 𝒦R.Idx 0) :
    (𝒦R.baseChange π (R ⧸ I)).inter t ≤ G ⁻¹ᵁ ((𝒦R.baseChange π (R ⧸ J)).inter t) := by
  rw [Scheme.OrderedAffineCover.baseChange_inter, Scheme.OrderedAffineCover.baseChange_inter,
    ← Scheme.Hom.comp_preimage, hG1]

theorem wbridge_core
    (G : pullback π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)) ⟶ pullback π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))
    (e : (Scheme.Modules.pullback G).obj
        ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).obj FR) ≅
      (Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))).obj FR)
    (hG1 : G ≫ pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)) =
      pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))
    (hG2 : G ≫ pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)) =
      pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJI)))
    (he : e = (Scheme.Modules.pullbackComp G (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).app FR ≪≫
      (Scheme.Modules.pullbackCongr hG1).app FR)
    (Kc0 Kc1 : Type) [AddCommGroup Kc0] [Module R Kc0] [AddCommGroup Kc1] [Module R Kc1]
    (δ0 : Kc0 →ₗ[R] Kc1) (φ0 : Kc0 →ₗ[R] (OModulePresheaf.ofModules π FR).cochain 𝒦R 0)
    (ΘB0 : (R ⧸ J) ⊗[R] Kc0 →ₗ[R ⧸ J] (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).obj FR)).cochain (𝒦R.baseChange π (R ⧸ J)) 0)
    (ΘB1 : (R ⧸ J) ⊗[R] Kc1 →ₗ[R ⧸ J] (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).obj FR)).cochain (𝒦R.baseChange π (R ⧸ J)) 1)
    (haB : ΘB1 ∘ₗ δ0.baseChange (R ⧸ J) = (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).obj FR)).d (𝒦R.baseChange π (R ⧸ J)) 0 ∘ₗ ΘB0)
    (hbB : (∀ (a : R ⧸ J) (k : Kc0) (s : 𝒦R.Idx 0),
      ΘB0 (a ⊗ₜ[R] k) s
        = a • (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).obj FR)).res
            (𝒦R.baseChange_inter_le π (R ⧸ J) s)
            ((((Scheme.Modules.pullbackPushforwardAdjunction
              (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).unit.app FR).app
              (𝒦R.inter s)).hom (φ0 k s))))
    (hc1B : ∀ x : (R ⧸ J) ⊗[R] Kc0, δ0.baseChange (R ⧸ J) x = 0 → ΘB0 x = 0 → x = 0)
    (hc2B : ∀ y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).obj FR)).cochain (𝒦R.baseChange π (R ⧸ J)) 0,
      (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).obj FR)).d (𝒦R.baseChange π (R ⧸ J)) 0 y = 0 → ∃ x : (R ⧸ J) ⊗[R] Kc0, δ0.baseChange (R ⧸ J) x = 0 ∧ ΘB0 x = y)
    (Θk0 : (R ⧸ I) ⊗[R] Kc0 →ₗ[R ⧸ I] (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))).obj FR)).cochain (𝒦R.baseChange π (R ⧸ I)) 0)
    (Θk1 : (R ⧸ I) ⊗[R] Kc1 →ₗ[R ⧸ I] (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))).obj FR)).cochain (𝒦R.baseChange π (R ⧸ I)) 1)
    (hak : Θk1 ∘ₗ δ0.baseChange (R ⧸ I) = (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))).obj FR)).d (𝒦R.baseChange π (R ⧸ I)) 0 ∘ₗ Θk0)
    (hbk : (∀ (a : R ⧸ I) (k : Kc0) (s : 𝒦R.Idx 0),
      Θk0 (a ⊗ₜ[R] k) s
        = a • (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))).obj FR)).res
            (𝒦R.baseChange_inter_le π (R ⧸ I) s)
            ((((Scheme.Modules.pullbackPushforwardAdjunction
              (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))).unit.app FR).app
              (𝒦R.inter s)).hom (φ0 k s))))
    (hc1k : ∀ x : (R ⧸ I) ⊗[R] Kc0, δ0.baseChange (R ⧸ I) x = 0 → Θk0 x = 0 → x = 0)
    (hc2k : ∀ y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))).obj FR)).cochain (𝒦R.baseChange π (R ⧸ I)) 0,
      (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))).obj FR)).d (𝒦R.baseChange π (R ⧸ I)) 0 y = 0 → ∃ x : (R ⧸ I) ⊗[R] Kc0, δ0.baseChange (R ⧸ I) x = 0 ∧ Θk0 x = y)
    :
    ((∀ z : (R ⧸ I) ⊗[R] Kc0, δ0.baseChange (R ⧸ I) z = 0 →
        ∃ w : (R ⧸ J) ⊗[R] Kc0, δ0.baseChange (R ⧸ J) w = 0 ∧ LinearMap.rTensor Kc0 (Submodule.factor hJI) w = z) ↔
      (∀ sk : 𝟙_ (pullback π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I))).Modules ⟶
          (Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))).obj FR,
        ∃ s : 𝟙_ (pullback π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J))).Modules ⟶
          (Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).obj FR,
          Scheme.Modules.pullbackSection G s ≫ e.hom = sk)) := by
  have hle : ∀ t : 𝒦R.Idx 0, (𝒦R.baseChange π (R ⧸ I)).inter t ≤ G ⁻¹ᵁ ((𝒦R.baseChange π (R ⧸ J)).inter t) :=
    inter_le_of π 𝒦R J I G hG1

  have hN1 : ∀ (w : (R ⧸ J) ⊗[R] Kc0) (t : 𝒦R.Idx 0),
      rho G e (hle t) (ΘB0 w t) = Θk0 (LinearMap.rTensor Kc0 (Submodule.factor hJI) w) t := by
    intro w t
    induction w using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, map_zero, map_zero]
      exact rho_zero G e (hle t)
    | add x y hx hy =>
      rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, ← hx, ← hy]
      exact rho_add G e (hle t) _ _
    | tmul a k =>
      rw [hbB, LinearMap.rTensor_tmul, hbk, S3_factor_eq]
      exact WBFix.transition_tmul_datum (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))
        (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))
        (pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))
        (pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))
        G (Ideal.Quotient.factor hJI) hG1 FR (𝒦R.inter t)
        ((𝒦R.baseChange π (R ⧸ J)).inter t) (𝒦R.baseChange_inter_le π (R ⧸ J) t)
        ((𝒦R.baseChange π (R ⧸ I)).inter t) (𝒦R.baseChange_inter_le π (R ⧸ I) t)
        (hle t) (φ0 k t) a
        (S5_appLE_transition _ _ _ (Ideal.Quotient.factor hJI) hG2 _ _ _ a) e he

  obtain ⟨θB, hθB, hθBval⟩ := S2_bijective_ker _ _ ΘB0 ΘB1 haB hc1B hc2B
  obtain ⟨θk, hθk, hθkval⟩ := S2_bijective_ker _ _ Θk0 Θk1 hak hc1k hc2k
  let EB := Equiv.ofBijective θB hθB
  let Ek := Equiv.ofBijective θk hθk

  let πB := pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J))
  let πk := pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I))
  let FB := (Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).obj FR
  let Fk := (Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))).obj FR
  let σB : (𝟙_ _ ⟶ FB) → LinearMap.ker ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).obj FR)).d (𝒦R.baseChange π (R ⧸ J)) 0) :=
    fun s => ⟨secH0 πB FB (𝒦R.baseChange π (R ⧸ J)) s, secH0_mem πB FB _ s⟩
  let σk : (𝟙_ _ ⟶ Fk) → LinearMap.ker ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ I)))).obj FR)).d (𝒦R.baseChange π (R ⧸ I)) 0) :=
    fun s => ⟨secH0 πk Fk (𝒦R.baseChange π (R ⧸ I)) s, secH0_mem πk Fk _ s⟩
  have hσB : Function.Bijective σB := by
    refine ⟨fun s s' h => secH0_injective πB FB _ (congrArg Subtype.val h), fun c => ?_⟩
    obtain ⟨s, hs⟩ := secH0_surjective πB FB _ c
    exact ⟨s, Subtype.ext hs⟩
  have hσk : Function.Bijective σk := by
    refine ⟨fun s s' h => secH0_injective πk Fk _ (congrArg Subtype.val h), fun c => ?_⟩
    obtain ⟨s, hs⟩ := secH0_surjective πk Fk _ c
    exact ⟨s, Subtype.ext hs⟩

  let TB : (𝟙_ _ ⟶ FB) → LinearMap.ker (δ0.baseChange (R ⧸ J)) := fun s => EB.symm (σB s)
  let Tk : (𝟙_ _ ⟶ Fk) → LinearMap.ker (δ0.baseChange (R ⧸ I)) := fun s => Ek.symm (σk s)
  have hTB : Function.Bijective TB := EB.symm.bijective.comp hσB
  have hTk : Function.Bijective Tk := Ek.symm.bijective.comp hσk
  have hLmem : ∀ w : LinearMap.ker (δ0.baseChange (R ⧸ J)),
      LinearMap.rTensor Kc0 (Submodule.factor hJI) (w : (R ⧸ J) ⊗[R] Kc0) ∈ LinearMap.ker (δ0.baseChange (R ⧸ I)) := by
    intro w
    rw [LinearMap.mem_ker, S1_rTensor_baseChange, LinearMap.mem_ker.mp w.2, map_zero]
  let Lm : LinearMap.ker (δ0.baseChange (R ⧸ J)) → LinearMap.ker (δ0.baseChange (R ⧸ I)) :=
    fun w => ⟨_, hLmem w⟩
  let Rm : (𝟙_ _ ⟶ FB) → (𝟙_ _ ⟶ Fk) := fun s => Scheme.Modules.pullbackSection G s ≫ e.hom

  have hsq : ∀ s, Lm (TB s) = Tk (Rm s) := by
    intro s
    apply Ek.injective
    show θk (Lm (TB s)) = Ek (Ek.symm (σk (Rm s)))
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    rw [hθkval]
    funext t
    show Θk0 (LinearMap.rTensor Kc0 (Submodule.factor hJI) (TB s : (R ⧸ J) ⊗[R] Kc0)) t = secH0 πk Fk _ (Rm s) t
    rw [← hN1, secH0_apply, ← rho_app_one G e s (hle t)]
    congr 1
    have h1 : (θB (TB s) : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R (R ⧸ J)))).obj FR)).cochain (𝒦R.baseChange π (R ⧸ J)) 0) = ΘB0 (TB s : (R ⧸ J) ⊗[R] Kc0) := hθBval _
    have h2 : θB (TB s) = σB s := by
      show EB (EB.symm (σB s)) = σB s
      rw [Equiv.apply_symm_apply]
    rw [← h1, h2]
    rfl
  have key := S4_surj_iff Lm Rm TB Tk hTB hTk hsq
  constructor
  · intro H sk
    have hL : Function.Surjective Lm := by
      intro z
      obtain ⟨w, hw, hwz⟩ := H z (LinearMap.mem_ker.mp z.2)
      exact ⟨⟨w, LinearMap.mem_ker.mpr hw⟩, Subtype.ext hwz⟩
    obtain ⟨s, hs⟩ := key.mp hL sk
    exact ⟨s, hs⟩
  · intro H z hz
    have hR : Function.Surjective Rm := fun sk => H sk
    obtain ⟨w, hw⟩ := key.mpr hR ⟨z, LinearMap.mem_ker.mpr hz⟩
    exact ⟨w, LinearMap.mem_ker.mp w.2, congrArg Subtype.val hw⟩

end Bridge

end WB

set_option maxHeartbeats 1600000 in
open S32WB WB in
open TensorProduct in
theorem solution
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover) (h𝒦 : Fintype.card 𝒦.ι = g + 1) (y : A) :
    letI R : Type := ↥(A.presheaf.stalk y)
    letI bR : Spec (CommRingCat.of R) ⟶ A := A.fromSpecStalk y
    letI tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K) := bR ≫ f
    letI xR : SchemeHomOver tR f := ⟨bR, rfl⟩
    letI π : pullback f tR ⟶ Spec (CommRingCat.of R) := pullback.snd f tR
    letI FR : (pullback f tR).Modules :=
      (Scheme.Modules.pullback (sliceAt f xR)).obj
        (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)
    letI _ : IsAffineHom (pullback.fst f tR) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒦R : (pullback f tR).OrderedAffineCover := 𝒦.comap (pullback.fst f tR)
    letI G := OModulePresheaf.ofModules π FR
        ∀ (Kc : ℕ → Type) [∀ i, AddCommGroup (Kc i)] [∀ i, Module R (Kc i)]
        [∀ i, Module.Finite R (Kc i)] [∀ i, Module.Free R (Kc i)]
        (δ : ∀ i, Kc i →ₗ[R] Kc (i + 1)) (_ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (_ : ∀ i, g < i → Subsingleton (Kc i))
        (φ : ∀ i, Kc i →ₗ[R] (OModulePresheaf.ofModules π FR).cochain 𝒦R i)
        (_ : ∀ i, (OModulePresheaf.ofModules π FR).d 𝒦R i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
        (Θ : ∀ (B : Type) [CommRing B] [Algebra R B] (i : ℕ), B ⊗[R] Kc i →ₗ[B]
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).cochain (𝒦R.baseChange π B) i),
        (((Nonempty (LinearMap.ker (δ 0) ≃ₗ[R] G.H0 𝒦R) ∧
          ∀ i : ℕ, Nonempty
            ((LinearMap.ker (δ (i + 1)) ⧸ (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) ≃ₗ[R]
              G.HSucc 𝒦R i)) ∧
        ∀ (B : Type) [CommRing B] [Algebra R B],
          (∀ i : ℕ, Θ B (i + 1) ∘ₗ (δ i).baseChange B
            = (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
                ((Scheme.Modules.pullback
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) i
              ∘ₗ Θ B i) ∧
          (∀ (i : ℕ) (a : B) (k : Kc i) (s : 𝒦R.Idx i),
            Θ B i (a ⊗ₜ[R] k) s
              = a • (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
                  ((Scheme.Modules.pullback
                    (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).res
                  (𝒦R.baseChange_inter_le π B s)
                  ((((Scheme.Modules.pullbackPushforwardAdjunction
                    (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).unit.app FR).app
                    (𝒦R.inter s)).hom (φ i k s))) ∧
          (∀ x : B ⊗[R] Kc 0, (δ 0).baseChange B x = 0 → Θ B 0 x = 0 → x = 0) ∧
          (∀ y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).cochain (𝒦R.baseChange π B) 0,
            (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) 0 y = 0 →
            ∃ x : B ⊗[R] Kc 0, (δ 0).baseChange B x = 0 ∧ Θ B 0 x = y) ∧
          (∀ (i : ℕ) (x : B ⊗[R] Kc (i + 1)), (δ (i + 1)).baseChange B x = 0 →
            Θ B (i + 1) x ∈ LinearMap.range
              ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
                ((Scheme.Modules.pullback
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) i) →
            x ∈ LinearMap.range ((δ i).baseChange B)) ∧
          (∀ (i : ℕ) (y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).cochain (𝒦R.baseChange π B) (i + 1)),
            (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) (i + 1) y = 0 →
            ∃ x : B ⊗[R] Kc (i + 1), (δ (i + 1)).baseChange B x = 0 ∧
              Θ B (i + 1) x - y ∈ LinearMap.range
                ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
                  ((Scheme.Modules.pullback
                    (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) i)))) →
      ∀ (J' : Ideal R) (hJ' : J' ≤ IsLocalRing.maximalIdeal R), (∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ J') →
        letI X := pullback f tR
        letI B : Type := R ⧸ J'
        letI kk : Type := R ⧸ IsLocalRing.maximalIdeal R
        letI XB := pullback π (Scheme.TwoAffineOpenCover.specMap R B)
        letI Xk := pullback π (Scheme.TwoAffineOpenCover.specMap R kk)
        letI FB : XB.Modules := (Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR
        letI Fk : Xk.Modules := (Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R kk))).obj FR
        letI u : B →+* kk := Ideal.Quotient.factor hJ'
        letI hfac : Scheme.TwoAffineOpenCover.specMap R kk =
            Spec.map (CommRingCat.ofHom u) ≫ Scheme.TwoAffineOpenCover.specMap R B := by
          rw [Scheme.TwoAffineOpenCover.specMap, Scheme.TwoAffineOpenCover.specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2
        letI gq : Xk ⟶ XB := pullback.lift (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R kk))
            (pullback.snd π (Scheme.TwoAffineOpenCover.specMap R kk) ≫ Spec.map (CommRingCat.ofHom u))
            (by rw [pullback.condition, Category.assoc, ← hfac])
        letI e : (Scheme.Modules.pullback gq).obj FB ≅ Fk :=
          (Scheme.Modules.pullbackComp gq (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).app FR ≪≫
            (Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _)).app FR
        ((∀ z : kk ⊗[R] Kc 0, (δ 0).baseChange kk z = 0 →
            ∃ w : B ⊗[R] Kc 0, (δ 0).baseChange B w = 0 ∧ LinearMap.rTensor (Kc 0) (Submodule.factor hJ') w = z) ↔
          (∀ sk : 𝟙_ Xk.Modules ⟶ Fk, ∃ s : 𝟙_ XB.Modules ⟶ FB, Scheme.Modules.pullbackSection gq s ≫ e.hom = sk)) := by
  intro Kc iAC iMod iFin iFree δ hδδ hbdd φ hφ Θ hblock J' hJ' hJ'N
  have hBJ := hblock.2 (↥(A.presheaf.stalk y) ⧸ J')
  have hBk := hblock.2 (↥(A.presheaf.stalk y) ⧸ IsLocalRing.maximalIdeal ↥(A.presheaf.stalk y))
  refine WB.wbridge_core _ _ _ J' _ hJ' _ _ ?_ ?_ ?_
    (Kc 0) (Kc 1) (δ 0) (φ 0) (Θ _ 0) (Θ _ 1) (hBJ.1 0) (hBJ.2.1 0) hBJ.2.2.1 hBJ.2.2.2.1
    (Θ _ 0) (Θ _ 1) (hBk.1 0) (hBk.2.1 0) hBk.2.2.1 hBk.2.2.2.1
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _
  · rfl

end

end S_AlgebraicGeometry_Polarisation_forall_exists_baseChange_iff_forall_exists_pullbackSection_of_quasiIso_cech_sliceAt_stalk_of_forall
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_forall_exists_baseChange_iff_forall_exists_pullbackSection_of_quasiIso_cech_sliceAt_stalk_of_forall (solution)
