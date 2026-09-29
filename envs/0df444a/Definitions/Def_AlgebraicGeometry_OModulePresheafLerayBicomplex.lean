-- Prove2me | Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex
-- name    : AlgebraicGeometry_OModulePresheafLerayBicomplex
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/2552f3ca-38cd-508e-b95c-e72e2fb2b81a
-- title:
--   Čech–Leray bicomplex of a morphism of schemes
-- statement:
--   Fix a commutative ring $R$, schemes $V', Z$, a morphism $p : V' \to Z$ and a structure morphism $\pi_Z : Z \to \operatorname{Spec} R$, and finite ordered affine open covers $K$ of $Z$ and $K'$ of $V'$ (each given by a finite linearly ordered index type, affine opens covering the whole scheme; the $a$-simplices $\mathrm{Idx}\,a$ are strictly monotone maps $\mathrm{Fin}(a+1) \to \iota$, with $\mathrm{inter}$ the corresponding intersection and $\mathrm{face}$ the omission of a vertex).
--
--   The first item is a separatedness lemma: if $\pi_Z$ is separated, $W \subseteq V'$ and $U \subseteq Z$ are affine opens, then $W \sqcap p^{-1}U$ is affine (proved by pasting the pullback squares for $W \sqcap p^{-1}U$ and for the restriction of $p$ over $U$, and using that the diagonal of $\pi_Z$ is a closed, hence affine, immersion). From it, `restrictToPreimage` is the finite ordered affine cover $(K'_i \sqcap p^{-1}U)_i$ of the open $p^{-1}U$.
--
--   Next, $\mathrm{biC}\,a\,b$ is the product of $\Gamma(V', K'(\tau) \sqcap p^{-1}K(\sigma))$ over pairs of simplices $(\sigma, \tau)$ of $K$ and $K'$, an $R$-module through $p$ followed by $\pi_Z$, with the two alternating Čech differentials `dH` (in $\sigma$) and `dV` (in $\tau$), described explicitly on components; $\mathrm{biC}\,a\,b$ is subsingleton as soon as $a$ or $b$ is at least the maximum of the two index cardinalities, the index type then being empty.
--
--   For an arbitrary open $U \subseteq Z$, `relAltC` is the relative alternating complex $\prod_\tau \Gamma(V', K'(\tau) \sqcap p^{-1}U)$ with differential `relAltd`; `relAltHB` is the submodule of coboundaries inside the cocycles, defined as $\bot$ in degree $0$ and as the preimage of the range of the previous differential under the inclusion of the kernel (so no vanishing of $d \circ d$ is needed), and `relAltH` is the quotient. Two auxiliary presheaves of modules are defined: `pushOpen` sends $W \subseteq V'$ to $\Gamma(V', W \sqcap p^{-1}U)$ over $p$ followed by $\pi_Z$, with `relAltd` equal to its Čech differential for $K'$; `pullOpen` sends $U \subseteq Z$ to $\Gamma(V', W \sqcap p^{-1}U)$ over $\pi_Z$, with $\Gamma(Z,U)$ acting through $p^\#$. These supply $\Gamma(Z,U)$-module and scalar-tower structures on `relAltC`, on the cocycles and on `relAltH`; together with the restriction maps `relRes`, their restrictions `relResKer` to cocycles, commutation with the differential and the inclusion `relAltHB_res_le` of coboundaries, they assemble the presheaf `relHPresheaf` of $\mathcal O_Z$-modules, $U \mapsto \mathrm{relAltH}\,U\,b$. Finally `biC_uncurry` and `biC_uncurry'` identify the bicomplex, as an $R$-module, with the product over $\sigma$ of the relative complexes over $K(\sigma)$, respectively with the product over $\tau$ of the Čech cochains on $K$ of `pullOpen` at $K'(\tau)$, and `dV_uncurry`, `dH_uncurry` record that these identifications carry `dV`, `dH` to the corresponding differentials.
--
--   **Relation to Mathlib.** The affineness of $W \sqcap p^{-1}U$ is deduced from Mathlib's pullback, separatedness and affine/closed-immersion API; the covers, the presheaf-of-modules datum `OModulePresheaf`, the alternating Čech complexes and the bicomplex here are the project's own constructions, not built on Mathlib's `HomologicalComplex` or sheaf-cohomology machinery.
--
--   **Where it is used.** These definitions provide the vocabulary for the Čech–Leray double complex attached to a morphism $p$, whose rows are complexes of sections over the affine opens $K'(\tau) \sqcap p^{-1}K(\sigma)$ and whose horizontal cohomology presheaf is `relHPresheaf`. They serve the finiteness statements for Čech cohomology of coherent sheaves on proper schemes, reduced via a Chow modification to the projective case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafLerayBicomplex.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry.OModulePresheaf.Leray

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

section FiberAffine

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}

theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.fiberAffineOpen
    (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ]
    {W : V'.Opens} (hW : IsAffineOpen W) {U : Z.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (W ⊓ (Opens.map p.base).obj U) := by
  have hpb₁ := isPullback_opens_inf W ((Opens.map p.base).obj U)
  have hpb₂ := isPullback_morphismRestrict p U
  have hpb : IsPullback (V'.homOfLE (inf_le_left : W ⊓ (Opens.map p.base).obj U ≤ W))
      (V'.homOfLE inf_le_right ≫ (p ∣_ U)) (W.ι ≫ p) U.ι :=
    (hpb₁.flip.paste_horiz hpb₂).flip
  haveI : IsAffine (W : Scheme.{u}) := hW
  haveI : IsAffine (U : Scheme.{u}) := hU
  haveI haffSR : IsAffine (pullback ((W.ι ≫ p) ≫ πZ) (U.ι ≫ πZ)) := inferInstance
  haveI hcl : IsClosedImmersion (pullback.mapDesc (W.ι ≫ p) U.ι πZ) := inferInstance
  haveI : IsAffine (pullback (W.ι ≫ p) U.ι) :=
    isAffine_of_isAffineHom (pullback.mapDesc (W.ι ≫ p) U.ι πZ)
  exact .of_isIso hpb.isoPullback.hom

def restrictToPreimage
    (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ]
    (K' : Scheme.OrderedAffineCover V') {U : Z.Opens} (hU : IsAffineOpen U) :
    Scheme.OrderedAffineCoverOf ((Opens.map p.base).obj U) where
  ι := K'.ι
  U := fun i => K'.U i ⊓ (Opens.map p.base).obj U
  isAffineOpen := fun i => Scheme.OrderedAffineCover.fiberAffineOpen p πZ (K'.isAffineOpen i) hU
  le := fun _ => inf_le_right
  iSup_eq := by rw [← iSup_inf_eq, K'.iSup_eq_top, top_inf_eq]

@[simp] theorem restrictToPreimage_U
    (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ]
    (K' : Scheme.OrderedAffineCover V') {U : Z.Opens} (hU : IsAffineOpen U) (i : K'.ι) :
    (restrictToPreimage p πZ K' hU).U i = K'.U i ⊓ (Opens.map p.base).obj U := rfl

end FiberAffine

section LerayDC

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

abbrev HIdx (a : ℕ) := K.Idx a

abbrev VIdx (b : ℕ) := K'.Idx b

abbrev biOpen (a b : ℕ)
    (σ : HIdx K a) (τ : VIdx K' b) : V'.Opens :=
  K'.inter τ ⊓ (Opens.map p.base).obj (K.inter σ)

abbrev BiIdx (a b : ℕ) : Type u :=
  HIdx K a × VIdx K' b

abbrev biC (a b : ℕ) : Type u :=
  ∀ στ : BiIdx K K' a b,
    (OModulePresheaf.unit (p ≫ πZ)).obj (biOpen p K K' a b στ.1 στ.2)

instance biC_abGrp (a b : ℕ) :
    AddCommGroup (biC p πZ K K' a b) :=
  inferInstanceAs (AddCommGroup (∀ στ : BiIdx K K' a b,
    (OModulePresheaf.unit (p ≫ πZ)).obj (biOpen p K K' a b στ.1 στ.2)))

instance biC_module (a b : ℕ) :
    Module R (biC p πZ K K' a b) :=
  inferInstanceAs (Module R (∀ στ : BiIdx K K' a b,
    (OModulePresheaf.unit (p ≫ πZ)).obj (biOpen p K K' a b στ.1 στ.2)))

def dH (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    biC p πZ K K' a b →ₗ[R] biC p πZ K K' (a + 1) b :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.pi fun στ => ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
      (inf_le_inf_left _ ((Opens.map p.base).monotone
        (K.inter_le_inter_face στ.1 j)))).comp
      (LinearMap.proj (R := R) (⟨K.face στ.1 j, στ.2⟩ :
        BiIdx K K' a b)))

def dV (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    biC p πZ K K' a b →ₗ[R] biC p πZ K K' a (b + 1) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.pi fun στ => ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
      (inf_le_inf_right _ (K'.inter_le_inter_face στ.2 j))).comp
      (LinearMap.proj (R := R) (⟨στ.1, K'.face στ.2 j⟩ :
        BiIdx K K' a b)))

theorem dH_apply (a b : ℕ) (f : biC p πZ K K' a b)
    (στ : BiIdx K K' (a + 1) b) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    dH p πZ K K' a b f στ
      = ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
            (inf_le_inf_left _ ((Opens.map p.base).monotone
              (K.inter_le_inter_face στ.1 j)))
            (f ⟨K.face στ.1 j, στ.2⟩) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  simp only [dH, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

theorem dH_apply' (a b : ℕ) (f : biC p πZ K K' a b)
    (στ : BiIdx K K' (a + 1) b) :
    dH p πZ K K' a b f στ
      = ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (V'.presheaf.map (homOfLE (inf_le_inf_left (K'.inter στ.2)
            ((Opens.map p.base).monotone (K.inter_le_inter_face στ.1 j)))).op).hom
            (f ⟨K.face στ.1 j, στ.2⟩) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  simp only [dH, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

theorem dV_apply (a b : ℕ) (f : biC p πZ K K' a b)
    (στ : BiIdx K K' a (b + 1)) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    dV p πZ K K' a b f στ
      = ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
            (inf_le_inf_right _ (K'.inter_le_inter_face στ.2 j))
            (f ⟨στ.1, K'.face στ.2 j⟩) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  simp only [dV, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

theorem dV_apply' (a b : ℕ) (f : biC p πZ K K' a b)
    (στ : BiIdx K K' a (b + 1)) :
    dV p πZ K K' a b f στ
      = ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (V'.presheaf.map (homOfLE (inf_le_inf_right
            ((Opens.map p.base).obj (K.inter στ.1))
            (K'.inter_le_inter_face στ.2 j))).op).hom
            (f ⟨στ.1, K'.face στ.2 j⟩) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  simp only [dV, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

theorem biC_subsingleton (a b : ℕ)
    (h : max (Fintype.card K.ι) (Fintype.card K'.ι) ≤ a
          ∨ max (Fintype.card K.ι) (Fintype.card K'.ι) ≤ b) :
    Subsingleton (biC p πZ K K' a b) := by
  have hempty : IsEmpty (BiIdx K K' a b) := by
    rcases h with ha | hb
    · exact ⟨fun στ => absurd
        (Fintype.card_fin (a + 1) ▸ Fintype.card_le_of_injective στ.1.1 στ.1.2.injective)
        (by omega)⟩
    · exact ⟨fun στ => absurd
        (Fintype.card_fin (b + 1) ▸ Fintype.card_le_of_injective στ.2.1 στ.2.2.injective)
        (by omega)⟩
  exact ⟨fun f g => funext fun στ => (hempty.false στ).elim⟩

end LerayDC

section RelAlt

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K' : Scheme.OrderedAffineCover V')

abbrev relAltC (U : Z.Opens) (b : ℕ) : Type u :=
  ∀ τ : K'.Idx b,
    (OModulePresheaf.unit (p ≫ πZ)).obj (K'.inter τ ⊓ (Opens.map p.base).obj U)

def relAltd (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relAltC p πZ K' U b →ₗ[R] relAltC p πZ K' U (b + 1) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.pi fun τ => ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
      (inf_le_inf_right _ (K'.inter_le_inter_face τ j))).comp
      (LinearMap.proj (R := R) (K'.face τ j)))

theorem relAltd_apply' (U : Z.Opens) (b : ℕ)
    (f : relAltC p πZ K' U b) (τ : K'.Idx (b + 1)) :
    relAltd p πZ K' U b f τ
      = ∑ j : Fin (b + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (V'.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj U)
            (K'.inter_le_inter_face τ j))).op).hom
            (f (K'.face τ j)) := by
  simp only [relAltd, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

def relAltHB (U : Z.Opens) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (b : ℕ) → Submodule R (LinearMap.ker (relAltd p πZ K' U b)) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  fun b => match b with
  | 0 => ⊥
  | b' + 1 => (LinearMap.range (relAltd p πZ K' U b')).comap
      (LinearMap.ker (relAltd p πZ K' U (b' + 1))).subtype

abbrev relAltH (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    Type u :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.ker (relAltd p πZ K' U b) ⧸ relAltHB p πZ K' U b

def pushOpen (U : Z.Opens) : OModulePresheaf (p ≫ πZ) where
  obj W := Γ(V', W ⊓ (Opens.map p.base).obj U)
  addCommGroup _ := inferInstance
  module W := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ) _
  moduleSections W := Module.compHom _
    (V'.presheaf.map (homOfLE (inf_le_left : W ⊓ (Opens.map p.base).obj U ≤ W)).op).hom
  isScalarTower W := by
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ) W
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ) (W ⊓ (Opens.map p.base).obj U)
    letI : Module Γ(V', W) Γ(V', W ⊓ (Opens.map p.base).obj U) := Module.compHom _
      (V'.presheaf.map (homOfLE (inf_le_left : W ⊓ (Opens.map p.base).obj U ≤ W)).op).hom
    refine ⟨fun r a x => ?_⟩
    show (V'.presheaf.map (homOfLE (inf_le_left (b := (Opens.map p.base).obj U))).op).hom
          ((V'.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
            ((p ≫ πZ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) * a) * x
      = (V'.presheaf.map (homOfLE (le_top : W ⊓ (Opens.map p.base).obj U ≤ ⊤)).op).hom
            ((p ≫ πZ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
          * ((V'.presheaf.map (homOfLE inf_le_left).op).hom a * x)
    rw [map_mul, ← mul_assoc, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
      homOfLE_comp]
  res h := Scheme.OrderedAffineCoverOf.res (p ≫ πZ) (inf_le_inf_right _ h)
  res_smul {W W'} h a x := by
    show (V'.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj U) h)).op).hom
          ((V'.presheaf.map (homOfLE inf_le_left).op).hom a * x)
      = (V'.presheaf.map (homOfLE inf_le_left).op).hom ((V'.presheaf.map (homOfLE h).op).hom a)
          * (V'.presheaf.map (homOfLE (inf_le_inf_right _ h)).op).hom x
    rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, homOfLE_comp, homOfLE_comp]
  res_refl W := (OModulePresheaf.unit (p ≫ πZ)).res_refl _
  res_comp h h' := (OModulePresheaf.unit (p ≫ πZ)).res_comp _ _

theorem relAltd_eq_d (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relAltd p πZ K' U b
      = OModulePresheaf.d (pushOpen p πZ U) K' b := rfl

def pullOpen (W : V'.Opens) : OModulePresheaf πZ where
  obj U := Γ(V', W ⊓ (Opens.map p.base).obj U)
  addCommGroup _ := inferInstance
  module U := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ) _
  moduleSections U := Module.compHom _
    (p.appLE U (W ⊓ (Opens.map p.base).obj U) inf_le_right).hom
  isScalarTower U := by
    letI := Scheme.OrderedAffineCoverOf.moduleSections πZ U
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ) (W ⊓ (Opens.map p.base).obj U)
    letI : Module Γ(Z, U) Γ(V', W ⊓ (Opens.map p.base).obj U) :=
      Module.compHom _ (p.appLE U (W ⊓ (Opens.map p.base).obj U) inf_le_right).hom
    refine ⟨fun r a x => ?_⟩

    show (p.appLE U (W ⊓ (Opens.map p.base).obj U) inf_le_right).hom
          ((Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
            ((πZ.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) * a) * x
      = (V'.presheaf.map (homOfLE (le_top : W ⊓ (Opens.map p.base).obj U ≤ ⊤)).op).hom
            (((p ≫ πZ).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
          * ((p.appLE U (W ⊓ (Opens.map p.base).obj U) inf_le_right).hom a * x)
    rw [map_mul, ← mul_assoc]
    congr 2

    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  res h := Scheme.OrderedAffineCoverOf.res (p ≫ πZ) (inf_le_inf_left W ((Opens.map p.base).monotone h))
  res_smul {U U'} h a x := by
    show (V'.presheaf.map (homOfLE (inf_le_inf_left W ((Opens.map p.base).monotone h))).op).hom
          ((p.appLE U' (W ⊓ (Opens.map p.base).obj U') inf_le_right).hom a * x)
      = (p.appLE U (W ⊓ (Opens.map p.base).obj U) inf_le_right).hom
            ((Z.presheaf.map (homOfLE h).op).hom a)
          * (V'.presheaf.map (homOfLE (inf_le_inf_left W ((Opens.map p.base).monotone h))).op).hom x
    rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply (f := Z.presheaf.map _),
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  res_refl U := (OModulePresheaf.unit (p ≫ πZ)).res_refl _
  res_comp h h' := (OModulePresheaf.unit (p ≫ πZ)).res_comp _ _

instance relAltC_modΓ (U : Z.Opens) (b : ℕ) :
    Module Γ(Z, U) (relAltC p πZ K' U b) :=
  @Pi.module _ _ _ _ _ fun τ => (pullOpen p πZ (K'.inter τ)).moduleSections U

theorem relAltd_Γsmul (U : Z.Opens) (b : ℕ) (a : Γ(Z, U))
    (f : relAltC p πZ K' U b) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relAltd p πZ K' U b (a • f) = a • relAltd p πZ K' U b f := by

  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  have hstep : ∀ (W₁ W₂ : V'.Opens) (h : W₁ ≤ W₂)
      (e₁ : W₁ ⊓ (Opens.map p.base).obj U ≤ p ⁻¹ᵁ U)
      (e₂ : W₂ ⊓ (Opens.map p.base).obj U ≤ p ⁻¹ᵁ U)
      (x : Γ(V', W₂ ⊓ (Opens.map p.base).obj U)),
      (V'.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj U) h)).op).hom
          ((p.appLE U (W₂ ⊓ (Opens.map p.base).obj U) e₂).hom a * x)
        = (p.appLE U (W₁ ⊓ (Opens.map p.base).obj U) e₁).hom a
          * (V'.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj U) h)).op).hom x :=
    fun _ _ _ _ _ _ => by rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  funext τ
  refine (relAltd_apply' p πZ K' U b (a • f) τ).trans
    ((Finset.sum_congr rfl fun (j : Fin (b + 2)) _ =>
      (congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·)
        (hstep (K'.inter τ) (K'.inter (K'.face τ j))
          (K'.inter_le_inter_face τ j) inf_le_right inf_le_right
          (f (K'.face τ j)))).trans (mul_smul_comm _ _ _).symm).trans ?_)
  rw [← Finset.mul_sum, ← relAltd_apply' p πZ K' U b f τ]
  rfl

instance relAltC_scalarTower (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections πZ U
    IsScalarTower R Γ(Z, U) (relAltC p πZ K' U b) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections πZ U
  exact ⟨fun r a f => funext fun τ =>
    ((pullOpen p πZ (K'.inter τ)).isScalarTower U).smul_assoc
      r a (f τ)⟩

instance ker_relAltd_smul (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    SMul Γ(Z, U) ↥(LinearMap.ker (relAltd p πZ K' U b)) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  ⟨fun a x => ⟨a • x.1, LinearMap.mem_ker.mpr <| by
    rw [relAltd_Γsmul, LinearMap.mem_ker.mp x.2, smul_zero]⟩⟩

instance ker_relAltd_modΓ (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    Module Γ(Z, U) ↥(LinearMap.ker (relAltd p πZ K' U b)) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  Function.Injective.module Γ(Z, U) ⟨⟨Subtype.val, rfl⟩, fun _ _ => rfl⟩
    Subtype.val_injective (fun _ _ => rfl)

theorem relAltHB_Γsmul (U : Z.Opens) (b : ℕ) (a : Γ(Z, U))
    (x : letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
      ↥(LinearMap.ker (relAltd p πZ K' U b)))
    (hx : x ∈ relAltHB p πZ K' U b) :
    a • x ∈ relAltHB p πZ K' U b := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  rcases b with _ | b'
  · exact (Submodule.mem_bot R).mpr (by rw [(Submodule.mem_bot R).mp hx, smul_zero])
  · obtain ⟨y, hy⟩ := hx
    exact ⟨a • y, (relAltd_Γsmul p πZ K' U b' a y).trans
      (congrArg (a • ·) hy)⟩

instance relAltH_smul (U : Z.Opens) (b : ℕ) :
    SMul Γ(Z, U) (relAltH p πZ K' U b) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  ⟨fun a => Quotient.map' (a • ·) fun x y h => (Submodule.quotientRel_def _).mpr <| by
    show a • x - a • y ∈ _
    rw [show a • x - a • y = a • (x - y) from Subtype.ext (smul_sub a x.1 y.1).symm]
    exact relAltHB_Γsmul p πZ K' U b a (x - y)
      ((Submodule.quotientRel_def _).mp h)⟩

instance relAltH_modΓ (U : Z.Opens) (b : ℕ) :
    Module Γ(Z, U) (relAltH p πZ K' U b) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  Function.Surjective.module Γ(Z, U)
    ⟨⟨Submodule.Quotient.mk, rfl⟩, fun _ _ => rfl⟩
    (Submodule.Quotient.mk_surjective _) (fun _ _ => rfl)

instance relAltH_scalarTower (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections πZ U
    IsScalarTower R Γ(Z, U) (relAltH p πZ K' U b) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections πZ U
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine ⟨fun r a => Quotient.ind' fun x => congrArg Submodule.Quotient.mk
    (Subtype.ext ?_)⟩
  exact (relAltC_scalarTower p πZ K' U b).smul_assoc r a x.1

def relRes {U U' : Z.Opens} (h : U ≤ U') (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relAltC p πZ K' U' b →ₗ[R] relAltC p πZ K' U b :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.pi fun τ => (Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
    (inf_le_inf_left (K'.inter τ) ((Opens.map p.base).monotone h))).comp (LinearMap.proj τ)

theorem relRes_apply {U U' : Z.Opens} (h : U ≤ U') (b : ℕ) (f : relAltC p πZ K' U' b) (τ : K'.Idx b) :
    relRes p πZ K' h b f τ
      = (V'.presheaf.map (homOfLE (inf_le_inf_left (K'.inter τ) ((Opens.map p.base).monotone h))).op).hom
          (f τ) := rfl

theorem relRes_comm {U U' : Z.Opens} (h : U ≤ U') (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relRes p πZ K' h (b + 1) ∘ₗ relAltd p πZ K' U' b = relAltd p πZ K' U b ∘ₗ relRes p πZ K' h b := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine LinearMap.ext fun f => funext fun τ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, relRes_apply, relAltd_apply', relAltd_apply', map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, relRes_apply]
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  rfl

def relResKer {U U' : Z.Opens} (h : U ≤ U') (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    LinearMap.ker (relAltd p πZ K' U' b) →ₗ[R] LinearMap.ker (relAltd p πZ K' U b) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  (relRes p πZ K' h b).restrict fun f hf => LinearMap.mem_ker.mpr <| by
    rw [← LinearMap.comp_apply, ← relRes_comm, LinearMap.comp_apply, LinearMap.mem_ker.mp hf, map_zero]

theorem relResKer_coe {U U' : Z.Opens} (h : U ≤ U') (b : ℕ)
    (x : letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ); ↥(LinearMap.ker (relAltd p πZ K' U' b))) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (relResKer p πZ K' h b x : relAltC p πZ K' U b) = relRes p πZ K' h b x := rfl

theorem relAltHB_res_le {U U' : Z.Opens} (h : U ≤ U') (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relAltHB p πZ K' U' b
      ≤ (relAltHB p πZ K' U b).comap
          (relResKer p πZ K' h b) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  rcases b with _ | b'
  · exact bot_le
  · rintro x ⟨y, hy⟩
    exact ⟨relRes p πZ K' h b' y,
      (LinearMap.congr_fun (relRes_comm p πZ K' h b') y).symm.trans
        (congrArg (relRes p πZ K' h (b' + 1)) hy)⟩

def relHPresheaf (b : ℕ) : OModulePresheaf πZ where
  obj U := relAltH p πZ K' U b
  addCommGroup _ :=
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    inferInstance
  module U :=
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    inferInstance
  moduleSections U := relAltH_modΓ p πZ K' U b
  isScalarTower U := relAltH_scalarTower p πZ K' U b
  res {U U'} h :=
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    Submodule.mapQ _ _ (relResKer p πZ K' h b) (relAltHB_res_le p πZ K' h b)
  res_smul {U U'} h a z := by

    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    induction z using Quotient.inductionOn' with | _ x => ?_
    exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun τ =>
      (pullOpen p πZ (K'.inter τ)).res_smul h a (x.1 τ)))
  res_refl U := by
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    refine LinearMap.ext fun z => z.inductionOn' fun x =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun τ => ?_))
    exact LinearMap.congr_fun ((OModulePresheaf.unit (p ≫ πZ)).res_refl _) (x.1 τ)
  res_comp {U U' U''} h h' := by
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    refine LinearMap.ext fun z => z.inductionOn' fun x =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun τ => ?_))
    exact LinearMap.congr_fun ((OModulePresheaf.unit (p ≫ πZ)).res_comp
      (inf_le_inf_left _ ((Opens.map p.base).monotone h))
      (inf_le_inf_left _ ((Opens.map p.base).monotone h'))) (x.1 τ)

end RelAlt

section E2Iso

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

def biC_uncurry (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    biC p πZ K K' a b ≃ₗ[R]
      ∀ σ : K.Idx a,
        relAltC p πZ K' (K.inter σ) b :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  { toFun := fun f σ τ => f (σ, τ)
    invFun := fun g στ => g στ.1 στ.2
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem dV_uncurry (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    ∀ x σ, biC_uncurry p πZ K K' a (b + 1)
        (dV p πZ K K' a b x) σ
      = relAltd p πZ K' (K.inter σ) b
          (biC_uncurry p πZ K K' a b x σ) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  intro x σ; funext τ
  simp only [biC_uncurry, dV, relAltd,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.pi_apply,
    LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun d _ => rfl

def biC_uncurry' (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    biC p πZ K K' a b ≃ₗ[R]
      ∀ τ : K'.Idx b,
        OModulePresheaf.cochain (pullOpen p πZ (K'.inter τ))
          K a :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  { toFun := fun f τ σ => f (σ, τ)
    invFun := fun g στ => g στ.2 στ.1
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem dH_uncurry (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    ∀ x τ, biC_uncurry' p πZ K K' (a + 1) b
        (dH p πZ K K' a b x) τ
      = OModulePresheaf.d (pullOpen p πZ (K'.inter τ))
          K a (biC_uncurry' p πZ K K' a b x τ) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  intro x τ; funext σ
  simp only [biC_uncurry', dH, OModulePresheaf.d,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.pi_apply,
    LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun d _ => rfl

end E2Iso

end AlgebraicGeometry.OModulePresheaf.Leray

end


