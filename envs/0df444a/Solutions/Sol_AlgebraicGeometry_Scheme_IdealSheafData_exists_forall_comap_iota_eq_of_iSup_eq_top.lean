-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.exists_forall_comap_iota_eq_of_iSup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/452a5283-f29c-5eeb-a116-cb03b42397f2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace P2mGlue

section Maps

variable {X : Scheme.{u}}

theorem pmap_congr {U V : X.Opens} (i j : op U ⟶ op V) (s : Γ(X, U)) :
    X.presheaf.map i s = X.presheaf.map j s := by
  rw [Subsingleton.elim i j]

theorem pmap_pmap {U V W : X.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (s : Γ(X, U)) :
    X.presheaf.map j (X.presheaf.map i s) = X.presheaf.map (i ≫ j) s := by
  rw [CategoryTheory.Functor.map_comp]
  rfl

theorem pmap_self {U : X.Opens} (i : op U ⟶ op U) (s : Γ(X, U)) : X.presheaf.map i s = s := by
  rw [Subsingleton.elim i (𝟙 _), CategoryTheory.Functor.map_id]
  rfl

theorem ideal_cast (K : X.IdealSheafData) {U₁ U₂ : X.affineOpens} (e : U₁ = U₂)
    (i : op U₂.1 ⟶ op U₁.1) (x : Γ(X, U₂.1)) :
    X.presheaf.map i x ∈ K.ideal U₁ ↔ x ∈ K.ideal U₂ := by
  subst e
  rw [pmap_self]

theorem ideal_res (K : X.IdealSheafData) {U₁ U₂ : X.affineOpens} (h : U₁ ≤ U₂)
    (i : op U₂.1 ⟶ op U₁.1) {x : Γ(X, U₂.1)} (hx : x ∈ K.ideal U₂) :
    X.presheaf.map i x ∈ K.ideal U₁ := by
  have := K.ideal_le_comap_ideal h hx
  rw [Ideal.mem_comap] at this
  rw [pmap_congr i (homOfLE h).op]
  exact this

end Maps

section Locality

variable {X : Scheme.{u}}

theorem mem_ideal_of_forall_basicOpen (K : X.IdealSheafData) (V : X.affineOpens)
    {σ : Type*} (f : σ → Γ(X, V.1)) (hf : Ideal.span (Set.range f) = ⊤) (x : Γ(X, V.1))
    (hx : ∀ i, X.presheaf.map (homOfLE (X.basicOpen_le (f i))).op x ∈ K.ideal (X.affineBasicOpen (f i))) :
    x ∈ K.ideal V := by
  have inst := V.2.isLocalization_basicOpen
  refine Submodule.mem_of_isLocalized_span (Set.range f) hf (fun r => Γ(X, X.basicOpen r.1))
    (fun r => Algebra.linearMap Γ(X, V.1) Γ(X, X.basicOpen r.1)) ?_
  rintro ⟨_, i, rfl⟩
  simp +instances only [← Submodule.restrictScalars_localized' Γ(X, X.basicOpen (f i)),
    Ideal.localized'_eq_map, RingHom.algebraMap_toAlgebra, Submodule.restrictScalars_mem]
  erw [K.map_ideal (U := X.affineBasicOpen (f i)) (V := V) (X.basicOpen_le (f i))]
  exact hx i

theorem forall_basicOpen_of_mem_ideal (K : X.IdealSheafData) (V : X.affineOpens)
    (f : Γ(X, V.1)) {x : Γ(X, V.1)} (hx : x ∈ K.ideal V) :
    X.presheaf.map (homOfLE (X.basicOpen_le f)).op x ∈ K.ideal (X.affineBasicOpen f) :=
  ideal_res K (X.basicOpen_le f) _ hx

end Locality

section T

variable {Y : Scheme.{u}} {V : Y.Opens} (K : (V : Scheme.{u}).IdealSheafData)

def pre (W : Y.affineOpens) (h : W.1 ≤ V) : (V : Scheme.{u}).affineOpens :=
  ⟨V.ι ⁻¹ᵁ W.1, W.2.preimage_of_isOpenImmersion V.ι (by rw [Scheme.Opens.opensRange_ι]; exact h)⟩

def T (W : Y.affineOpens) (h : W.1 ≤ V) : Ideal Γ(Y, W.1) :=
  (K.ideal (pre W h)).comap (V.ι.app W.1).hom

theorem mem_T {W : Y.affineOpens} {h : W.1 ≤ V} {x : Γ(Y, W.1)} :
    x ∈ T K W h ↔ V.ι.app W.1 x ∈ K.ideal (pre W h) := Ideal.mem_comap

private theorem _root_.P2mGlue.isIso_app (W : Y.affineOpens) (h : W.1 ≤ V) : IsIso (V.ι.app W.1) :=
  V.ι.isIso_app W.1 (by rw [Scheme.Opens.opensRange_ι]; exact h)

p2m_export "P2mGlue" "isIso_app"

theorem app_pmap {W W' : Y.Opens} (i : op W ⟶ op W') (x : Γ(Y, W)) :
    V.ι.app W' (Y.presheaf.map i x) =
      (V : Scheme.{u}).presheaf.map (homOfLE (Scheme.Hom.preimage_mono V.ι (leOfHom i.unop))).op (V.ι.app W x) := by
  have h := ConcreteCategory.congr_hom (Scheme.Hom.naturality V.ι i) x
  change V.ι.app W' (Y.presheaf.map i x) = (V : Scheme.{u}).presheaf.map _ (V.ι.app W x) at h
  rw [h]
  exact pmap_congr _ _ _

theorem mem_T_cast {W₁ W₂ : Y.affineOpens} (e : W₁ = W₂) (h₁ : W₁.1 ≤ V) (h₂ : W₂.1 ≤ V)
    (i : op W₂.1 ⟶ op W₁.1) (x : Γ(Y, W₂.1)) :
    Y.presheaf.map i x ∈ T K W₁ h₁ ↔ x ∈ T K W₂ h₂ := by
  subst e
  rw [pmap_self]

theorem T_res {W₁ W₂ : Y.affineOpens} (hle : W₁ ≤ W₂) (h₁ : W₁.1 ≤ V) (h₂ : W₂.1 ≤ V)
    (i : op W₂.1 ⟶ op W₁.1) {x : Γ(Y, W₂.1)} (hx : x ∈ T K W₂ h₂) :
    Y.presheaf.map i x ∈ T K W₁ h₁ := by
  rw [mem_T] at hx ⊢
  rw [app_pmap]
  exact ideal_res K (show pre W₁ h₁ ≤ pre W₂ h₂ from Scheme.Hom.preimage_mono V.ι hle) _ hx

theorem T_basicOpen (W : Y.affineOpens) (h : W.1 ≤ V) (f : Γ(Y, W.1)) :
    T K (Y.affineBasicOpen f) ((Y.basicOpen_le f).trans h) =
      (T K W h).map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom := by

  set φ := V.ι.app W.1 with hφ
  set ψ := V.ι.app (Y.basicOpen f) with hψ
  set r := Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op with hr
  have hle : pre (Y.affineBasicOpen f) ((Y.basicOpen_le f).trans h) ≤ pre W h :=
    Scheme.Hom.preimage_mono V.ι (Y.basicOpen_le f)
  set r' := (V : Scheme.{u}).presheaf.map (homOfLE hle).op with hr'
  haveI : IsIso φ := isIso_app W h
  haveI : IsIso ψ := isIso_app (Y.affineBasicOpen f) ((Y.basicOpen_le f).trans h)

  have sq : ∀ x, ψ (r x) = r' (φ x) := fun x => app_pmap _ x

  have hK : K.ideal (pre (Y.affineBasicOpen f) ((Y.basicOpen_le f).trans h)) = (K.ideal (pre W h)).map r'.hom :=
    (K.map_ideal hle).symm
  apply le_antisymm
  ·
    intro y hy
    rw [mem_T, hK] at hy
    have hyy : inv ψ (ψ y) = y := by
      have := ConcreteCategory.congr_hom (IsIso.hom_inv_id ψ) y
      exact this
    rw [← hyy]
    have hsub : (K.ideal (pre W h)).map r'.hom ≤ (((T K W h).map r.hom).comap (inv ψ).hom) := by
      refine Ideal.map_le_iff_le_comap.mpr fun z hz => ?_
      have hzz : φ (inv φ z) = z := ConcreteCategory.congr_hom (IsIso.inv_hom_id φ) z
      have h1 : r' z = ψ (r (inv φ z)) := by
        rw [sq, hzz]
      have h2 : inv ψ (ψ (r (inv φ z))) = r (inv φ z) := ConcreteCategory.congr_hom (IsIso.hom_inv_id ψ) _
      refine Ideal.mem_comap.mpr (Ideal.mem_comap.mpr ?_)
      change inv ψ (r' z) ∈ (T K W h).map r.hom
      rw [h1, h2]
      exact Ideal.mem_map_of_mem _ ((mem_T K).mpr (by change φ (inv φ z) ∈ _; rw [hzz]; exact hz))
    exact hsub hy
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx => Ideal.mem_comap.mpr ((mem_T K).mpr ?_)
    rw [hK]
    change ψ (r x) ∈ _
    rw [sq]
    exact Ideal.mem_map_of_mem _ ((mem_T K).mp hx)

end T

section T2

variable {Y : Scheme.{u}} {V : Y.Opens} (K : (V : Scheme.{u}).IdealSheafData)

theorem resV_eq {A B : (V : Scheme.{u}).Opens} (hAB : A ≤ B) (i : op (V.ι ''ᵁ B) ⟶ op (V.ι ''ᵁ A))
    (x : Γ(Y, V.ι ''ᵁ B)) :
    Y.presheaf.map i x = (V : Scheme.{u}).presheaf.map (homOfLE hAB).op x := by
  rw [Scheme.Opens.toScheme_presheaf_map]
  exact pmap_congr _ _ _

theorem app_eq (W : Y.Opens) (x : Γ(Y, W)) (i : op W ⟶ op (V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    V.ι.app W x = Y.presheaf.map i x := by
  rw [Scheme.Opens.ι_app]
  exact pmap_congr _ _ _

def toTop (W : Y.affineOpens) (x : Γ(Y, W.1)) : Γ(Y, W.1.ι ''ᵁ ⊤) :=
  Y.presheaf.map (homOfLE (W.1.ι_image_le ⊤)).op x

theorem isAffineOpen_top' (W : Y.affineOpens) : IsAffineOpen (⊤ : (W.1 : Scheme.{u}).Opens) :=
  @isAffineOpen_top (W.1 : Scheme.{u}) W.2

theorem mem_T_iff_comap_homOfLE (W : Y.affineOpens) (h : W.1 ≤ V) (x : Γ(Y, W.1)) :
    x ∈ T K W h ↔ toTop W x ∈ (K.comap (Y.homOfLE h)).ideal ⟨⊤, isAffineOpen_top' W⟩ := by

  have hA : V.ι ''ᵁ (Y.homOfLE h) ''ᵁ ⊤ = W.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.opensRange_homOfLE,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
    exact h
  have hB : W.1.ι ''ᵁ (Y.homOfLE h) ⁻¹ᵁ (Y.homOfLE h) ''ᵁ ⊤ = W.1 := by
    rw [Scheme.Hom.preimage_image_eq, Scheme.Opens.ι_image_top]
  have hpre : pre W h = ⟨(Y.homOfLE h) ''ᵁ ⊤, (isAffineOpen_top' W).image_of_isOpenImmersion _⟩ := by
    apply Subtype.ext
    change V.ι ⁻¹ᵁ W.1 = (Y.homOfLE h) ''ᵁ ⊤
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.opensRange_homOfLE]
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, mem_T]

  have key : ((Y.homOfLE h).appIso ⊤).inv (toTop W x) = Y.presheaf.map (homOfLE hA.le).op x := by
    have h1 := ConcreteCategory.congr_hom (Scheme.Hom.appIso_inv_app (Y.homOfLE h) ⊤) (toTop W x)
    change (Y.homOfLE h).app ((Y.homOfLE h) ''ᵁ ⊤) (((Y.homOfLE h).appIso ⊤).inv (toTop W x)) =
      (W.1 : Scheme.{u}).presheaf.map _ (toTop W x) at h1
    rw [Scheme.homOfLE_app, Scheme.Opens.toScheme_presheaf_map] at h1

    have h2 := congrArg (Y.presheaf.map (homOfLE (hA.trans hB.symm).le).op) h1
    erw [pmap_pmap, pmap_self, pmap_pmap] at h2
    erw [h2, toTop, pmap_pmap]
    exact pmap_congr _ _ _
  have step : toTop W x ∈ Ideal.comap ((Y.homOfLE h).appIso ⊤).inv.hom
      (K.ideal ⟨(Y.homOfLE h) ''ᵁ ⊤, (isAffineOpen_top' W).image_of_isOpenImmersion _⟩) ↔
      Y.presheaf.map (homOfLE hA.le).op x ∈
        K.ideal ⟨(Y.homOfLE h) ''ᵁ ⊤, (isAffineOpen_top' W).image_of_isOpenImmersion _⟩ := by
    refine Ideal.mem_comap.trans ?_
    exact Iff.of_eq (congrArg (fun t => t ∈ K.ideal ⟨(Y.homOfLE h) ''ᵁ ⊤,
      (isAffineOpen_top' W).image_of_isOpenImmersion _⟩) key)
  have hpre1 : (pre W h).1 = (Y.homOfLE h) ''ᵁ ⊤ := congrArg Subtype.val hpre
  have hle1 : V.ι ''ᵁ (pre W h).1 ≤ V.ι ''ᵁ (Y.homOfLE h) ''ᵁ ⊤ := (congrArg (fun O => V.ι ''ᵁ O) hpre1).le
  have helt : V.ι.app W.1 x =
      (V : Scheme.{u}).presheaf.map (homOfLE hpre1.le).op (Y.presheaf.map (homOfLE hA.le).op x) := by
    rw [← resV_eq hpre1.le (homOfLE hle1).op, pmap_pmap]
    exact app_eq _ x _
  rw [step, helt]
  exact ideal_cast K hpre _ _

theorem T_congr {V' : Y.Opens} (K' : (V' : Scheme.{u}).IdealSheafData) (W : Y.affineOpens)
    (h : W.1 ≤ V) (h' : W.1 ≤ V')
    (e : K.comap (Y.homOfLE h) = K'.comap (Y.homOfLE h')) : T K W h = T K' W h' := by
  ext x
  rw [mem_T_iff_comap_homOfLE, mem_T_iff_comap_homOfLE, e]

theorem mem_T_image (W₁ : (V : Scheme.{u}).affineOpens) (x : Γ(Y, V.ι ''ᵁ W₁.1)) :
    x ∈ T K ⟨V.ι ''ᵁ W₁.1, W₁.2.image_of_isOpenImmersion V.ι⟩ (V.ι_image_le W₁.1) ↔
      x ∈ K.ideal W₁ := by
  have hpre : pre ⟨V.ι ''ᵁ W₁.1, W₁.2.image_of_isOpenImmersion V.ι⟩ (V.ι_image_le W₁.1) = W₁ :=
    Subtype.ext (V.ι.preimage_image_eq W₁.1)
  rw [mem_T, app_eq _ x (homOfLE (by rw [V.ι.preimage_image_eq])).op]
  erw [resV_eq (show (pre ⟨V.ι ''ᵁ W₁.1, W₁.2.image_of_isOpenImmersion V.ι⟩ (V.ι_image_le W₁.1)).1 ≤ W₁.1
      from hpre.le)]
  exact ideal_cast K hpre _ x

end T2

section Glue

variable {Y : Scheme.{u}} {ι : Type u} (𝒰 : ι → Y.Opens)
  (I : ∀ j, (𝒰 j : Scheme.{u}).IdealSheafData)

theorem basicOpen_pmap_le {U U' : Y.Opens} (i : op U ⟶ op U') (g : Γ(Y, U)) :
    Y.basicOpen (Y.presheaf.map i g) ≤ Y.basicOpen g := by
  rw [Scheme.basicOpen_res]
  exact inf_le_right

theorem pmap_pmap_congr {U V V' W : Y.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W)
    (i' : op U ⟶ op V') (j' : op V' ⟶ op W) (s : Γ(Y, U)) :
    Y.presheaf.map j (Y.presheaf.map i s) = Y.presheaf.map j' (Y.presheaf.map i' s) := by
  rw [pmap_pmap, pmap_pmap]
  exact pmap_congr _ _ _

theorem T_compat
    (hI : ∀ j k, (I j).comap (Y.homOfLE (inf_le_left : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 j)) =
      (I k).comap (Y.homOfLE (inf_le_right : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 k)))
    (W : Y.affineOpens) {j k : ι} (hj : W.1 ≤ 𝒰 j) (hk : W.1 ≤ 𝒰 k) :
    T (I j) W hj = T (I k) W hk := by
  apply T_congr
  have e1 : Y.homOfLE hj = Y.homOfLE (le_inf hj hk) ≫ Y.homOfLE inf_le_left :=
    (Y.homOfLE_homOfLE _ _).symm
  have e2 : Y.homOfLE hk = Y.homOfLE (le_inf hj hk) ≫ Y.homOfLE inf_le_right :=
    (Y.homOfLE_homOfLE _ _).symm
  rw [e1, e2, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hI]

def glueIdeal (U : Y.affineOpens) : Ideal Γ(Y, U.1) :=
  ⨅ (W : Y.affineOpens), ⨅ (j : ι), ⨅ (hWU : W ≤ U), ⨅ (hWj : W.1 ≤ 𝒰 j),
    (T (I j) W hWj).comap (Y.presheaf.map (homOfLE hWU).op).hom

theorem mem_glueIdeal {U : Y.affineOpens} {x : Γ(Y, U.1)} :
    x ∈ glueIdeal 𝒰 I U ↔ ∀ (W : Y.affineOpens) (j : ι) (hWU : W ≤ U) (hWj : W.1 ≤ 𝒰 j),
      Y.presheaf.map (homOfLE hWU).op x ∈ T (I j) W hWj := by
  refine Iff.trans (Submodule.mem_iInf _) (forall_congr' fun W => ?_)
  refine Iff.trans (Submodule.mem_iInf _) (forall_congr' fun j => ?_)
  refine Iff.trans (Submodule.mem_iInf _) (forall_congr' fun hWU => ?_)
  refine Iff.trans (Submodule.mem_iInf _) (forall_congr' fun hWj => ?_)
  exact Ideal.mem_comap

theorem exists_pow_mul_mem_T {V : Y.Opens} (K : (V : Scheme.{u}).IdealSheafData)
    (W : Y.affineOpens) (h : W.1 ≤ V) (r x : Γ(Y, W.1))
    (hx : Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op x ∈
      T K (Y.affineBasicOpen r) ((Y.basicOpen_le r).trans h)) :
    ∃ n : ℕ, r ^ n * x ∈ T K W h := by
  have inst := W.2.isLocalization_basicOpen r
  rw [T_basicOpen K W h r] at hx
  obtain ⟨m, hm, hmx⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers r)
      (S := Γ(Y, Y.basicOpen r)) (T K W h) x).mp hx
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hm
  exact ⟨n, hn ▸ hmx⟩

theorem exists_finset_subordinate (h𝒰 : ⨆ j, 𝒰 j = ⊤) (U : Y.affineOpens) :
    ∃ s : Finset Γ(Y, U.1), Ideal.span (s : Set Γ(Y, U.1)) = ⊤ ∧
      ∀ f ∈ s, ∃ j, Y.basicOpen f ≤ 𝒰 j := by
  classical
  have hspan : Ideal.span {f : Γ(Y, U.1) | ∃ j, Y.basicOpen f ≤ 𝒰 j} = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro x hx
    have hx' : x ∈ ⨆ j, 𝒰 j := by rw [h𝒰]; trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx'
    obtain ⟨f, hf, hxf⟩ := U.2.exists_basicOpen_le (V := 𝒰 j) ⟨x, hj⟩ hx
    exact Opens.mem_iSup.mpr ⟨⟨f, j, hf⟩, hxf⟩
  obtain ⟨s, hs, hs'⟩ := (Ideal.span_eq_top_iff_finite _).mp hspan
  exact ⟨s, hs', fun f hf => hs hf⟩

theorem map_glueIdeal_le (U : Y.affineOpens) (g : Γ(Y, U.1)) :
    (glueIdeal 𝒰 I U).map (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom ≤
      glueIdeal 𝒰 I (Y.affineBasicOpen g) := by
  refine Ideal.map_le_iff_le_comap.mpr fun x hx => Ideal.mem_comap.mpr ?_
  refine (mem_glueIdeal 𝒰 I).mpr fun W j hWU hWj => ?_
  have h := (mem_glueIdeal 𝒰 I).mp hx W j (le_trans hWU (Y.affineBasicOpen_le g)) hWj
  have e : Y.presheaf.map (homOfLE hWU).op (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op x) =
      Y.presheaf.map (homOfLE (le_trans hWU (Y.affineBasicOpen_le g))).op x :=
    (pmap_pmap _ _ _).trans (pmap_congr _ _ _)
  rw [← e] at h
  exact h

theorem exists_pow_mul_res_mem_T {U : Y.affineOpens} (g : Γ(Y, U.1))
    {y : Γ(Y, Y.basicOpen g)} (hy : y ∈ glueIdeal 𝒰 I (Y.affineBasicOpen g))
    {a₀ : Γ(Y, U.1)} {n : ℕ}
    (hy0 : y * Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op (g ^ n) =
      Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op a₀)
    (f : Γ(Y, U.1)) {j : ι} (hf : Y.basicOpen f ≤ 𝒰 j) :
    ∃ e : ℕ, Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (g ^ e * a₀) ∈
      T (I j) (Y.affineBasicOpen f) hf := by

  let rg : Γ(Y, (Y.affineBasicOpen f).1) := Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op g
  have hW₀U : Y.affineBasicOpen rg ≤ Y.affineBasicOpen g := basicOpen_pmap_le _ g
  have hW₀j : (Y.affineBasicOpen rg).1 ≤ 𝒰 j := (Y.basicOpen_le rg).trans hf
  have h1 := (mem_glueIdeal 𝒰 I).mp hy (Y.affineBasicOpen rg) j hW₀U hW₀j
  have h2 : Y.presheaf.map (homOfLE hW₀U).op (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op a₀) ∈
      T (I j) (Y.affineBasicOpen rg) hW₀j := by
    rw [← hy0, map_mul]
    exact Ideal.mul_mem_right _ _ h1
  have h3 : Y.presheaf.map (homOfLE (Y.basicOpen_le rg)).op
      (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op a₀) ∈
      T (I j) (Y.affineBasicOpen rg) ((Y.basicOpen_le rg).trans hf) := by
    have e : Y.presheaf.map (homOfLE (Y.basicOpen_le rg)).op
        (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op a₀) =
        Y.presheaf.map (homOfLE hW₀U).op (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op a₀) :=
      pmap_pmap_congr _ _ _ _ _
    rw [← e] at h2
    exact h2
  obtain ⟨e, he⟩ := exists_pow_mul_mem_T (I j) (Y.affineBasicOpen f) hf rg _ h3
  refine ⟨e, ?_⟩
  rw [map_mul, map_pow]
  exact he

theorem glueIdeal_basicOpen_le (h𝒰 : ⨆ j, 𝒰 j = ⊤)
    (hI : ∀ j k, (I j).comap (Y.homOfLE (inf_le_left : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 j)) =
      (I k).comap (Y.homOfLE (inf_le_right : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 k)))
    (U : Y.affineOpens) (g : Γ(Y, U.1)) (y : Γ(Y, Y.basicOpen g))
    (hy : y ∈ glueIdeal 𝒰 I (Y.affineBasicOpen g)) :
    y ∈ (glueIdeal 𝒰 I U).map (algebraMap Γ(Y, U.1) Γ(Y, Y.basicOpen g)) := by
  classical
  have inst := U.2.isLocalization_basicOpen g

  obtain ⟨⟨a₀, m⟩, hy0⟩ := IsLocalization.surj (Submonoid.powers g) (S := Γ(Y, Y.basicOpen g)) y
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp m.2
  dsimp only at hy0
  rw [← hn] at hy0
  have hy0' : y * Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op (g ^ n) =
      Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op a₀ := hy0

  obtain ⟨s, hspan, hsub⟩ := exists_finset_subordinate 𝒰 h𝒰 U
  choose jOf hjOf using hsub
  have key : ∀ f (hf : f ∈ s), ∃ e : ℕ,
      Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (g ^ e * a₀) ∈
        T (I (jOf f hf)) (Y.affineBasicOpen f) (hjOf f hf) :=
    fun f hf => exists_pow_mul_res_mem_T 𝒰 I g hy hy0' f (hjOf f hf)
  choose e he using key
  let M : ℕ := s.attach.sup fun f => e f.1 f.2
  have hMe : ∀ f (hf : f ∈ s), e f hf ≤ M := fun f hf =>
    Finset.le_sup (f := fun f : {x // x ∈ s} => e f.1 f.2) (Finset.mem_attach s ⟨f, hf⟩)

  have ha : g ^ M * a₀ ∈ glueIdeal 𝒰 I U := by
    refine (mem_glueIdeal 𝒰 I).mpr fun W j hWU hWj => ?_
    have hWU' : W.1 ≤ U.1 := hWU
    have hspanW : Ideal.span ((Y.presheaf.map (homOfLE hWU').op).hom '' (s : Set Γ(Y, U.1))) = ⊤ := by
      rw [← Ideal.map_span, hspan, Ideal.map_top]
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hspanW
    rintro ⟨_, f, hf, rfl⟩
    have hf' : f ∈ s := hf

    have haf : Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (g ^ M * a₀) ∈
        T (I (jOf f hf')) (Y.affineBasicOpen f) (hjOf f hf') := by
      have : g ^ M * a₀ = g ^ (M - e f hf') * (g ^ (e f hf') * a₀) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hMe f hf')]
      rw [this, map_mul]
      exact Ideal.mul_mem_left _ _ (he f hf')

    let rf : Γ(Y, W.1) := Y.presheaf.map (homOfLE hWU').op f
    have hW'f : Y.affineBasicOpen rf ≤ Y.affineBasicOpen f := basicOpen_pmap_le _ f
    have hW'j : (Y.affineBasicOpen rf).1 ≤ 𝒰 j := (Y.basicOpen_le rf).trans hWj
    have hW'jf : (Y.affineBasicOpen rf).1 ≤ 𝒰 (jOf f hf') :=
      le_trans (show (Y.affineBasicOpen rf).1 ≤ (Y.affineBasicOpen f).1 from hW'f) (hjOf f hf')
    have h1 : Y.presheaf.map (homOfLE hW'f).op
        (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (g ^ M * a₀)) ∈
        T (I (jOf f hf')) (Y.affineBasicOpen rf) hW'jf :=
      T_res (I (jOf f hf')) hW'f hW'jf (hjOf f hf') _ haf
    rw [T_compat 𝒰 I hI (Y.affineBasicOpen rf) hW'jf hW'j] at h1
    have h2 : Y.presheaf.map (homOfLE (Y.basicOpen_le rf)).op
        (Y.presheaf.map (homOfLE hWU').op (g ^ M * a₀)) ∈
        T (I j) (Y.affineBasicOpen rf) ((Y.basicOpen_le rf).trans hWj) := by
      have e' : Y.presheaf.map (homOfLE (Y.basicOpen_le rf)).op
          (Y.presheaf.map (homOfLE hWU').op (g ^ M * a₀)) =
          Y.presheaf.map (homOfLE hW'f).op
            (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (g ^ M * a₀)) :=
        pmap_pmap_congr _ _ _ _ _
      rw [← e'] at h1
      exact h1
    obtain ⟨k, hk⟩ := exists_pow_mul_mem_T (I j) W hWj rf _ h2
    exact ⟨k, by rw [smul_eq_mul]; exact hk⟩

  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g)]
  refine ⟨⟨⟨g ^ M * a₀, ha⟩, ⟨g ^ (M + n), M + n, rfl⟩⟩, ?_⟩
  dsimp only
  rw [pow_add, map_mul, map_mul, ← hy0]
  ring

def glue (h𝒰 : ⨆ j, 𝒰 j = ⊤)
    (hI : ∀ j k, (I j).comap (Y.homOfLE (inf_le_left : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 j)) =
      (I k).comap (Y.homOfLE (inf_le_right : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 k))) : Y.IdealSheafData where
  ideal := glueIdeal 𝒰 I
  map_ideal_basicOpen U g :=
    le_antisymm (map_glueIdeal_le 𝒰 I U g) (fun y hy => glueIdeal_basicOpen_le 𝒰 I h𝒰 hI U g y hy)

theorem comap_glue_ι (h𝒰 : ⨆ j, 𝒰 j = ⊤)
    (hI : ∀ j k, (I j).comap (Y.homOfLE (inf_le_left : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 j)) =
      (I k).comap (Y.homOfLE (inf_le_right : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 k))) (j : ι) :
    (glue 𝒰 I h𝒰 hI).comap (𝒰 j).ι = I j := by
  refine Scheme.IdealSheafData.ext (funext fun W₁ => ?_)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have hx : ∀ x : Γ(𝒰 j, W₁.1), ((𝒰 j).ι.appIso W₁.1).inv.hom x = x := fun x => by
    rw [Scheme.Opens.ι_appIso]
    rfl
  have hVj : (𝒰 j).ι ''ᵁ W₁.1 ≤ 𝒰 j := (𝒰 j).ι_image_le W₁.1
  ext x
  rw [Ideal.mem_comap, hx]
  change x ∈ glueIdeal 𝒰 I ⟨(𝒰 j).ι ''ᵁ W₁.1, W₁.2.image_of_isOpenImmersion (𝒰 j).ι⟩ ↔
    x ∈ (I j).ideal W₁
  constructor
  · intro h
    have h1 := (mem_glueIdeal 𝒰 I).mp h
      ⟨(𝒰 j).ι ''ᵁ W₁.1, W₁.2.image_of_isOpenImmersion (𝒰 j).ι⟩ j le_rfl hVj
    rw [pmap_self] at h1
    exact (mem_T_image (I j) W₁ x).mp h1
  · intro h
    have h0 := (mem_T_image (I j) W₁ x).mpr h
    refine (mem_glueIdeal 𝒰 I).mpr fun W k hWU hWk => ?_
    have hWj : W.1 ≤ 𝒰 j :=
      le_trans (show W.1 ≤ (𝒰 j).ι ''ᵁ W₁.1 from hWU) hVj
    have h1 := T_res (I j) hWU hWj hVj (homOfLE hWU).op h0
    rwa [T_compat 𝒰 I hI W hWj hWk] at h1

end Glue

end P2mGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue"

theorem solution
    {Y : Scheme.{u}} {ι : Type u} (𝒰 : ι → Y.Opens) (h𝒰 : ⨆ j, 𝒰 j = ⊤)
    (I : ∀ j, (𝒰 j : Scheme.{u}).IdealSheafData)
    (hI : ∀ j k, (I j).comap (Y.homOfLE (inf_le_left : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 j)) =
      (I k).comap (Y.homOfLE (inf_le_right : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 k))) :
    ∃ I₀ : Y.IdealSheafData, ∀ j, I₀.comap (𝒰 j).ι = I j :=
  ⟨P2mGlue.glue 𝒰 I h𝒰 hI, P2mGlue.comap_glue_ι 𝒰 I h𝒰 hI⟩

end S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top (solution)
