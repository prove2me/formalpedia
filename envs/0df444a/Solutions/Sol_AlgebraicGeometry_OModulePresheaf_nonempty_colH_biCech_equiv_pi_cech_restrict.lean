-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.nonempty_colH_biCech_equiv_pi_cech_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/fb4b7c71-00c4-510b-bfd9-727ce0948c58

import Mathlib
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_colH_biCech_equiv_pi_cech_restrict

set_option autoImplicit false

universe u

noncomputable section
namespace S32CM

section ColAlg

variable {R : Type u} [CommRing R] {ι : Type u}
  {X : ℕ → Type u} [∀ q, AddCommGroup (X q)] [∀ q, Module R (X q)]
  {Y : ι → ℕ → Type u} [∀ s q, AddCommGroup (Y s q)] [∀ s q, Module R (Y s q)]
  (dX : ∀ q, X q →ₗ[R] X (q + 1)) (dY : ∀ s q, Y s q →ₗ[R] Y s (q + 1))
  (Φ : ∀ q, X q ≃ₗ[R] (∀ s, Y s q))
  (hΦ : ∀ q (x : X q) (s : ι), Φ (q + 1) (dX q x) s = dY s q (Φ q x s))

include hΦ in
lemma Φ_symm_d (q : ℕ) (y : ∀ s, Y s q) :
    dX q ((Φ q).symm y) = (Φ (q + 1)).symm (fun s => dY s q (y s)) := by
  apply (Φ (q + 1)).injective
  funext s
  rw [hΦ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

def ker0Map : LinearMap.ker (dX 0) →ₗ[R] (∀ s, LinearMap.ker (dY s 0)) :=
  LinearMap.pi fun s => (LinearMap.proj s ∘ₗ (Φ 0).toLinearMap).restrict (p := LinearMap.ker (dX 0))
    (q := LinearMap.ker (dY s 0)) (fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      show dY s 0 (Φ 0 x s) = 0
      rw [← hΦ, hx, map_zero]; rfl)

lemma ker0Map_apply (x : LinearMap.ker (dX 0)) (s : ι) : (ker0Map dX dY Φ hΦ x s : Y s 0) = Φ 0 x s := rfl

lemma ker0Map_bijective : Function.Bijective (ker0Map dX dY Φ hΦ) := by
  constructor
  · intro x x' h
    apply Subtype.ext
    apply (Φ 0).injective
    funext s
    have := congrArg (fun f => ((f s : LinearMap.ker (dY s 0)) : Y s 0)) h
    simpa only [ker0Map_apply] using this
  · intro y
    refine ⟨⟨(Φ 0).symm (fun s => (y s : Y s 0)), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, Φ_symm_d dX dY Φ hΦ]
      have : (fun s => dY s 0 (y s : Y s 0)) = 0 := funext fun s => (LinearMap.mem_ker.1 (y s).2)
      rw [this, map_zero]
    · funext s
      apply Subtype.ext
      rw [ker0Map_apply, LinearEquiv.apply_symm_apply]

def col0Equiv : (LinearMap.ker (dX 0) ⧸ (⊥ : Submodule R (LinearMap.ker (dX 0)))) ≃ₗ[R] (∀ s, LinearMap.ker (dY s 0)) :=
  (Submodule.quotEquivOfEqBot ⊥ rfl).trans (LinearEquiv.ofBijective _ (ker0Map_bijective dX dY Φ hΦ))

abbrev HB (q : ℕ) : Submodule R (LinearMap.ker (dX (q + 1))) :=
  (LinearMap.range (dX q)).comap (LinearMap.ker (dX (q + 1))).subtype

abbrev HBY (s : ι) (q : ℕ) : Submodule R (LinearMap.ker (dY s (q + 1))) :=
  (LinearMap.range (dY s q)).comap (LinearMap.ker (dY s (q + 1))).subtype

def kerSuccMap (q : ℕ) : LinearMap.ker (dX (q + 1)) →ₗ[R] (∀ s, LinearMap.ker (dY s (q + 1)) ⧸ HBY dY s q) :=
  LinearMap.pi fun s => (HBY dY s q).mkQ ∘ₗ
    ((LinearMap.proj s ∘ₗ (Φ (q + 1)).toLinearMap).restrict (p := LinearMap.ker (dX (q + 1)))
      (q := LinearMap.ker (dY s (q + 1))) (fun x hx => by
        rw [LinearMap.mem_ker] at hx ⊢
        show dY s (q + 1) (Φ (q + 1) x s) = 0
        rw [← hΦ, hx, map_zero]; rfl))

lemma kerSuccMap_apply (q : ℕ) (x : LinearMap.ker (dX (q + 1))) (s : ι) :
    kerSuccMap dX dY Φ hΦ q x s = Submodule.Quotient.mk ⟨Φ (q + 1) x s, by
      rw [LinearMap.mem_ker, ← hΦ, LinearMap.mem_ker.1 x.2, map_zero]; rfl⟩ := rfl

lemma HB_le_ker (q : ℕ) : HB dX q ≤ LinearMap.ker (kerSuccMap dX dY Φ hΦ q) := by
  rintro x ⟨w, hw⟩
  rw [LinearMap.mem_ker]
  funext s
  rw [kerSuccMap_apply]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  refine Submodule.mem_comap.2 ⟨Φ q w s, ?_⟩
  rw [Submodule.coe_subtype] at hw
  rw [Submodule.coe_subtype, ← hΦ, hw]

def colSuccMap (q : ℕ) : (LinearMap.ker (dX (q + 1)) ⧸ HB dX q) →ₗ[R] (∀ s, LinearMap.ker (dY s (q + 1)) ⧸ HBY dY s q) :=
  (HB dX q).liftQ (kerSuccMap dX dY Φ hΦ q) (HB_le_ker dX dY Φ hΦ q)

lemma colSuccMap_bijective (q : ℕ) : Function.Bijective (colSuccMap dX dY Φ hΦ q) := by
  classical
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.mem_ker, colSuccMap, Submodule.liftQ_apply] at hz
      have hs : ∀ s, ∃ w : Y s q, dY s q w = Φ (q + 1) x s := by
        intro s
        have h1 := congrFun hz s
        rw [kerSuccMap_apply] at h1
        have h2 := Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h1)
        rw [Submodule.coe_subtype, LinearMap.mem_range] at h2
        exact h2
      choose w hw using hs
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
      refine ⟨(Φ q).symm w, ?_⟩
      rw [Φ_symm_d dX dY Φ hΦ]
      apply (Φ (q + 1)).injective
      rw [LinearEquiv.apply_symm_apply]
      funext s
      exact hw s
  · intro z
    have hz : ∀ s, ∃ y : LinearMap.ker (dY s (q + 1)), Submodule.Quotient.mk y = z s :=
      fun s => Submodule.Quotient.mk_surjective _ (z s)
    choose y hy using hz
    have hx : (Φ (q + 1)).symm (fun s => (y s : Y s (q + 1))) ∈ LinearMap.ker (dX (q + 1)) := by
      rw [LinearMap.mem_ker, Φ_symm_d dX dY Φ hΦ]
      have : (fun s => dY s (q + 1) (y s : Y s (q + 1))) = 0 := funext fun s => LinearMap.mem_ker.1 (y s).2
      rw [this, map_zero]
    refine ⟨Submodule.Quotient.mk ⟨_, hx⟩, ?_⟩
    rw [colSuccMap, Submodule.liftQ_apply]
    funext s
    rw [kerSuccMap_apply, ← hy s]
    congr 1
    apply Subtype.ext
    show Φ (q + 1) ((Φ (q + 1)).symm fun s => (y s : Y s (q + 1))) s = y s
    rw [LinearEquiv.apply_symm_apply]

def colSuccEquiv (q : ℕ) : (LinearMap.ker (dX (q + 1)) ⧸ HB dX q) ≃ₗ[R] (∀ s, LinearMap.ker (dY s (q + 1)) ⧸ HBY dY s q) :=
  LinearEquiv.ofBijective _ (colSuccMap_bijective dX dY Φ hΦ q)

end ColAlg

end S32CM

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.OModulePresheaf Opposite"

namespace S32CM

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (.of R)) (N : Z.Modules)
variable (W : Z.Opens) (𝔘 : Z.OrderedOpenFamily) (O : (p : ℕ) → 𝔘.Idx p → Z.Opens)
variable (hOface : ∀ (p : ℕ) (s : 𝔘.Idx (p + 1)) (j : Fin (p + 2)), O (p + 1) s ≤ O p (𝔘.face s j))

noncomputable def δ (p : ℕ) (c : ∀ s : 𝔘.Idx p, (ofModules π N).obj (O p s)) :
    ∀ s : 𝔘.Idx (p + 1), (ofModules π N).obj (O (p + 1) s) :=
  fun s => ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • (ofModules π N).res (hOface p s j) (c (𝔘.face s j))

theorem δ_apply (p : ℕ) (c : ∀ s : 𝔘.Idx p, (ofModules π N).obj (O p s)) (s : 𝔘.Idx (p + 1)) :
    δ π N 𝔘 O hOface p c s
      = ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • (ofModules π N).res (hOface p s j) (c (𝔘.face s j)) :=
  rfl

section transport

theorem map_map_eq {A B B' C : Z.Opens} (f : A ⟶ B) (g : B ⟶ C) (f' : A ⟶ B') (g' : B' ⟶ C)
    (x : Γ(N, C)) :
    N.presheaf.map f.op (N.presheaf.map g.op x) = N.presheaf.map f'.op (N.presheaf.map g'.op x) := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
    ← op_comp, ← op_comp, Subsingleton.elim (f ≫ g) (f' ≫ g')]

theorem scalar_eq (V : (W : Scheme.{u}).Opens) (r : R) :
    (W.ι.appIso V).inv.hom ((Scheme.TwoAffineOpenCover.algebraOfHom (W.ι ≫ π) V).algebraMap r) =
      (Scheme.TwoAffineOpenCover.algebraOfHom π (W.ι ''ᵁ V)).algebraMap r := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
    Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, Scheme.Hom.comp_appLE]
  have h1 : W.ι.appLE (π ⁻¹ᵁ ⊤) V
      (show V ≤ W.ι ⁻¹ᵁ (π ⁻¹ᵁ ⊤) from le_top) =
      Z.presheaf.map (homOfLE (le_top : W.ι ''ᵁ V ≤ ⊤)).op ≫ (W.ι.appIso V).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    rfl
  rw [h1]
  exact Iso.hom_inv_id_apply (W.ι.appIso V) _

theorem smul_eq (V : (W : Scheme.{u}).Opens) (r : R) (y : Γ(N, W.ι ''ᵁ V)) :
    (letI : Module R Γ(N, W.ι ''ᵁ V) :=
        (OModulePresheaf.ofModules (W.ι ≫ π) (N.restrict W.ι)).module V; r • y) =
    (letI : Module R Γ(N, W.ι ''ᵁ V) := (OModulePresheaf.ofModules π N).module (W.ι ''ᵁ V); r • y) := by
  show ((W.ι.appIso V).inv.hom ((Scheme.TwoAffineOpenCover.algebraOfHom (W.ι ≫ π) V).algebraMap r)) • y =
    ((Scheme.TwoAffineOpenCover.algebraOfHom π (W.ι ''ᵁ V)).algebraMap r) • y
  rw [scalar_eq]

def eEntry (V₂ : (W : Scheme.{u}).Opens) (V₁ : Z.Opens) (h : W.ι ''ᵁ V₂ = V₁) :
    (OModulePresheaf.ofModules π N).obj V₁ ≃ₗ[R]
      (OModulePresheaf.ofModules (W.ι ≫ π) (N.restrict W.ι)).obj V₂ := by
  subst h
  exact
    { toFun := fun x => x
      invFun := fun y => y
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => (smul_eq π N W V₂ r x).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem eEntry_apply (V₂ : (W : Scheme.{u}).Opens) (V₁ : Z.Opens) (h : W.ι ''ᵁ V₂ = V₁)
    (x : Γ(N, V₁)) :
    (show Γ(N, W.ι ''ᵁ V₂) from eEntry π N W V₂ V₁ h x) = N.presheaf.map (eqToHom h).op x := by
  subst h
  rw [eqToHom_refl, op_id, N.presheaf.map_id]
  rfl

theorem eEntry_apply_res (V₂ : (W : Scheme.{u}).Opens) (V₁ : Z.Opens) (h : W.ι ''ᵁ V₂ = V₁)
    (x : Γ(N, V₁)) :
    (show Γ(N, W.ι ''ᵁ V₂) from eEntry π N W V₂ V₁ h x) = (OModulePresheaf.ofModules π N).res h.le x := by
  refine (eEntry_apply π N W V₂ V₁ h x).trans ?_
  change N.presheaf.map _ x = N.presheaf.map _ x
  exact congrArg (fun φ => N.presheaf.map (Quiver.Hom.op φ) x) (Subsingleton.elim _ _)

end transport

section reindex

variable {W : Z.Opens} (𝔅 : Z.OrderedOpenFamily) (𝔚 : (W : Scheme.{u}).OrderedAffineCover) (e : 𝔅.ι ≃o 𝔚.ι)
  (h𝔚 : ∀ j : 𝔅.ι, W.ι ''ᵁ 𝔚.U (e j) = W ⊓ 𝔅.U j)

def idxE (q : ℕ) : 𝔅.Idx q ≃ 𝔚.Idx q where
  toFun t := ⟨e ∘ t.1, e.strictMono.comp t.2⟩
  invFun t' := ⟨e.symm ∘ t'.1, e.symm.strictMono.comp t'.2⟩
  left_inv t := Subtype.ext (funext fun j => e.symm_apply_apply (t.1 j))
  right_inv t' := Subtype.ext (funext fun j => e.apply_symm_apply (t'.1 j))

theorem idxE_symm_val (q : ℕ) (t' : 𝔚.Idx q) : ((idxE 𝔅 𝔚 e q).symm t').1 = e.symm ∘ t'.1 := rfl

theorem idxE_symm_face (q : ℕ) (t' : 𝔚.Idx (q + 1)) (j : Fin (q + 2)) :
    (idxE 𝔅 𝔚 e q).symm (𝔚.face t' j) = 𝔅.face ((idxE 𝔅 𝔚 e (q + 1)).symm t') j := rfl

include h𝔚 in
theorem U_eq (j : 𝔅.ι) : 𝔚.U (e j) = W.ι ⁻¹ᵁ (W ⊓ 𝔅.U j) := by
  rw [← h𝔚 j, Scheme.Hom.preimage_image_eq]

include h𝔚 in

theorem image_inter (q : ℕ) (t' : 𝔚.Idx q) :
    W.ι ''ᵁ 𝔚.inter t' = W ⊓ 𝔅.inter ((idxE 𝔅 𝔚 e q).symm t') := by
  have hU : ∀ j : Fin (q + 1), 𝔚.U (t'.1 j) = W.ι ⁻¹ᵁ (W ⊓ 𝔅.U (e.symm (t'.1 j))) := fun j => by
    rw [← U_eq 𝔅 𝔚 e h𝔚 (e.symm (t'.1 j)), OrderIso.apply_symm_apply]
  apply le_antisymm
  · refine le_inf ((Scheme.Hom.image_le_opensRange _ _).trans (Scheme.Opens.opensRange_ι W).le) (le_iInf fun j => ?_)
    refine (Scheme.Hom.image_mono _ (𝔚.inter_le t' j)).trans ?_
    rw [hU j]
    exact (Scheme.Hom.image_preimage_le _ _).trans inf_le_right
  · have hle : W ⊓ 𝔅.inter ((idxE 𝔅 𝔚 e q).symm t') ≤ W := inf_le_left
    have h1 : W.ι ⁻¹ᵁ (W ⊓ 𝔅.inter ((idxE 𝔅 𝔚 e q).symm t')) ≤ 𝔚.inter t' := by
      refine le_iInf fun j => ?_
      rw [hU j]
      exact Scheme.Hom.preimage_mono _ (inf_le_inf_left W (𝔅.inter_le _ j))
    calc W ⊓ 𝔅.inter ((idxE 𝔅 𝔚 e q).symm t')
        = W.ι ''ᵁ (W.ι ⁻¹ᵁ (W ⊓ 𝔅.inter ((idxE 𝔅 𝔚 e q).symm t'))) := by
          rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hle]
      _ ≤ W.ι ''ᵁ 𝔚.inter t' := Scheme.Hom.image_mono _ h1

def Ψ (q : ℕ) : (∀ t : 𝔅.Idx q, (OModulePresheaf.ofModules π N).obj (W ⊓ 𝔅.inter t)) ≃ₗ[R]
    (OModulePresheaf.ofModules (W.ι ≫ π) (N.restrict W.ι)).cochain 𝔚 q :=
  (LinearEquiv.piCongrLeft' R (fun t : 𝔅.Idx q => (OModulePresheaf.ofModules π N).obj (W ⊓ 𝔅.inter t))
      (idxE 𝔅 𝔚 e q)).trans
    (LinearEquiv.piCongrRight fun t' => eEntry π N W (𝔚.inter t') _ (image_inter 𝔅 𝔚 e h𝔚 q t'))

theorem Ψ_apply (q : ℕ) (c : ∀ t : 𝔅.Idx q, (OModulePresheaf.ofModules π N).obj (W ⊓ 𝔅.inter t)) (t' : 𝔚.Idx q) :
    Ψ π N 𝔅 𝔚 e h𝔚 q c t' = eEntry π N W (𝔚.inter t') _ (image_inter 𝔅 𝔚 e h𝔚 q t') (c ((idxE 𝔅 𝔚 e q).symm t')) :=
  rfl

theorem Ψ_δ (q : ℕ) (c : ∀ t : 𝔅.Idx q, (OModulePresheaf.ofModules π N).obj (W ⊓ 𝔅.inter t)) (t' : 𝔚.Idx (q + 1)) :
    Ψ π N 𝔅 𝔚 e h𝔚 (q + 1) (δ π N 𝔅 (fun q t => W ⊓ 𝔅.inter t) (fun q t j => inf_le_inf_left W (𝔅.inter_le_inter_face t j)) q c) t' =
      (OModulePresheaf.ofModules (W.ι ≫ π) (N.restrict W.ι)).d 𝔚 q (Ψ π N 𝔅 𝔚 e h𝔚 q c) t' := by
  rw [Ψ_apply]
  change (show Γ(N, W.ι ''ᵁ _) from eEntry π N W _ _ _ (δ π N 𝔅 (fun q t => W ⊓ 𝔅.inter t) _ q c _)) = _
  rw [eEntry_apply_res, δ_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  rw [Ψ_apply]
  change N.presheaf.map _ (N.presheaf.map _ _) =
    N.presheaf.map _ (show Γ(N, W.ι ''ᵁ _) from eEntry π N W _ _ _ (c _))
  rw [eEntry_apply_res]
  exact map_map_eq N _ _ _ _ (c (𝔅.face ((idxE 𝔅 𝔚 e (q + 1)).symm t') j))

end reindex

end S32CM

namespace S32CM

section assemble

variable {R : Type u} [CommRing R]

def curryEquiv {α β : Type u} (M : α × β → Type u) [∀ ab, AddCommGroup (M ab)] [∀ ab, Module R (M ab)] :
    (∀ ab, M ab) ≃ₗ[R] (∀ a b, M (a, b)) where
  toFun c a b := c (a, b)
  invFun C ab := C ab.1 ab.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable {Z : Scheme.{u}} (π : Z ⟶ Spec (.of R)) (N : Z.Modules) (𝔄 𝔅 : Z.OrderedOpenFamily) (p : ℕ)
  (𝔚 : ∀ s : 𝔄.Idx p, ((𝔄.inter s : Z.Opens) : Scheme.{u}).OrderedAffineCover)
  (e : ∀ s : 𝔄.Idx p, 𝔅.ι ≃o (𝔚 s).ι)
  (h𝔚 : ∀ (s : 𝔄.Idx p) (j : 𝔅.ι), (𝔄.inter s).ι ''ᵁ (𝔚 s).U (e s j) = 𝔄.inter s ⊓ 𝔅.U j)

def colΦ (q : ℕ) : OModulePresheaf.BiCech.C (OModulePresheaf.ofModules π N) 𝔄 𝔅 p q ≃ₗ[R]
    (∀ s : 𝔄.Idx p, (OModulePresheaf.ofModules ((𝔄.inter s).ι ≫ π) (N.restrict (𝔄.inter s).ι)).cochain (𝔚 s) q) :=
  (curryEquiv (R := R) (fun st : 𝔄.Idx p × 𝔅.Idx q => (OModulePresheaf.ofModules π N).obj (𝔄.inter st.1 ⊓ 𝔅.inter st.2))).trans
    (LinearEquiv.piCongrRight fun s => Ψ π N 𝔅 (𝔚 s) (e s) (h𝔚 s) q)

theorem colΦ_apply (q : ℕ) (x : OModulePresheaf.BiCech.C (OModulePresheaf.ofModules π N) 𝔄 𝔅 p q) (s : 𝔄.Idx p) :
    colΦ π N 𝔄 𝔅 p 𝔚 e h𝔚 q x s = Ψ π N 𝔅 (𝔚 s) (e s) (h𝔚 s) q (fun t => x (s, t)) := rfl

theorem colΦ_dV (q : ℕ) (x : OModulePresheaf.BiCech.C (OModulePresheaf.ofModules π N) 𝔄 𝔅 p q) (s : 𝔄.Idx p) :
    colΦ π N 𝔄 𝔅 p 𝔚 e h𝔚 (q + 1) (OModulePresheaf.BiCech.dV (OModulePresheaf.ofModules π N) 𝔄 𝔅 p q x) s =
      (OModulePresheaf.ofModules ((𝔄.inter s).ι ≫ π) (N.restrict (𝔄.inter s).ι)).d (𝔚 s) q
        (colΦ π N 𝔄 𝔅 p 𝔚 e h𝔚 q x s) := by
  rw [colΦ_apply, colΦ_apply]
  funext t'
  have hδ : (fun t => OModulePresheaf.BiCech.dV (OModulePresheaf.ofModules π N) 𝔄 𝔅 p q x (s, t)) =
      δ π N 𝔅 (fun q t => 𝔄.inter s ⊓ 𝔅.inter t) (fun q t j => inf_le_inf_left (𝔄.inter s) (𝔅.inter_le_inter_face t j))
        q (fun t => x (s, t)) := by
    funext t
    rw [OModulePresheaf.BiCech.dV_apply, δ_apply]
  rw [hδ, Ψ_δ]

end assemble

end S32CM

open S32CM in
theorem solution
    {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of R)) (N : Z.Modules)
    (𝔄 𝔅 : Z.OrderedOpenFamily) (p : ℕ)
    (𝔚 : ∀ s : 𝔄.Idx p, ((𝔄.inter s : Z.Opens) : Scheme.{u}).OrderedAffineCover)
    (e : ∀ s : 𝔄.Idx p, 𝔅.ι ≃o (𝔚 s).ι)
    (h𝔚 : ∀ (s : 𝔄.Idx p) (j : 𝔅.ι), (𝔄.inter s).ι ''ᵁ (𝔚 s).U (e s j) = 𝔄.inter s ⊓ 𝔅.U j) :
    Nonempty (DoubleComplex.colH ((OModulePresheaf.ofModules π N).biCech 𝔄 𝔅) p 0 ≃ₗ[R]
        (∀ s : 𝔄.Idx p, ↥((OModulePresheaf.ofModules ((𝔄.inter s).ι ≫ π) (N.restrict (𝔄.inter s).ι)).H0 (𝔚 s)))) ∧
      ∀ q : ℕ, Nonempty (DoubleComplex.colH ((OModulePresheaf.ofModules π N).biCech 𝔄 𝔅) p (q + 1) ≃ₗ[R]
        (∀ s : 𝔄.Idx p, (OModulePresheaf.ofModules ((𝔄.inter s).ι ≫ π) (N.restrict (𝔄.inter s).ι)).HSucc (𝔚 s) q)) :=
  ⟨⟨S32CM.col0Equiv (fun q => OModulePresheaf.BiCech.dV (OModulePresheaf.ofModules π N) 𝔄 𝔅 p q)
      (fun s q => (OModulePresheaf.ofModules ((𝔄.inter s).ι ≫ π) (N.restrict (𝔄.inter s).ι)).d (𝔚 s) q)
      (S32CM.colΦ π N 𝔄 𝔅 p 𝔚 e h𝔚) (fun q x s => S32CM.colΦ_dV π N 𝔄 𝔅 p 𝔚 e h𝔚 q x s)⟩,
    fun q => ⟨S32CM.colSuccEquiv (fun q => OModulePresheaf.BiCech.dV (OModulePresheaf.ofModules π N) 𝔄 𝔅 p q)
      (fun s q => (OModulePresheaf.ofModules ((𝔄.inter s).ι ≫ π) (N.restrict (𝔄.inter s).ι)).d (𝔚 s) q)
      (S32CM.colΦ π N 𝔄 𝔅 p 𝔚 e h𝔚) (fun q x s => S32CM.colΦ_dV π N 𝔄 𝔅 p 𝔚 e h𝔚 q x s) q⟩⟩

end

end S_AlgebraicGeometry_OModulePresheaf_nonempty_colH_biCech_equiv_pi_cech_restrict
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_colH_biCech_equiv_pi_cech_restrict (solution)
