-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC2_005
-- name    : RPLib_FX_EtPBCC2_005
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-27T01:05:17.801782+00:00
-- url     : https://prove2.me/theorems/0ba08b4b-b42c-5144-89e6-33de3eadeef8
-- title:
--   Sheaf-level proper base change with compact supports, library file 005
-- statement:
--   File 005 of the library for sheaf-level proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_C1_Paste`: S4-EtPBC-C1, part 21: pasting of base change morphisms (generic)
--   * `S4.Def_RP_EtPBC_C1_TrG`: S4-EtPBC-C1, part 22: base change morphisms under morphisms of squares (generic)
--   * `S4.Def_RP_EtPBC_C1_PasteC`: S4-EtPBC-C1, part 24: pasting of base change morphisms for composite squares (BC-MOR (1c))
--   * `S4.Def_RP_EtPBC_C1_PbcSqA`: S4-EtPBC-C1, part 29a: morphisms of `(g, s)`-squares, the fibre map and the pastings
--   * `S4.Def_RP_EtPBC_C1_StkTr`: S4-EtPBC-C1, part 29d: stalk transport along a morphism of (g, s)-squares
--   * `S4.Def_RP_EtPBC_C1_PbcSqB`: S4-EtPBC-C1, part 29b: naturality of `pbcEquivS` under morphisms of `(g, s)`-squares
--
--   **Formalization note.** One file of a library formalizing sheaf-level proper base change for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ a tower of projective-line bundles over a noetherian $S$ of finite type over an algebraically closed field), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and any $g : S' \to S$ of finite type, the base change morphism $g^* R^q f_! F \to R^q f'_! (g_X^* F)$ is an isomorphism for every sheaf $F$ of $\Lambda$-modules ($\Lambda$ finite, $\ell$-power torsion). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`), for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`) and for the stalks of $R^q f_!$ (`RPLib_FX_EtPBCC1_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_009
import Definitions.Def_RPLib_FX_EtPBCC2_002

/-!
# Sheaf-level proper base change with compact supports, library file 005

Declarations of the formalization of sheaf-level proper base change for compactly supported étale
cohomology: for a compactified X ⟶ S whose proper part is an iterated projective-line bundle (a tower)
and any g : S' ⟶ S of finite type, the base change morphism g^* R^q f_! F ⟶ R^q f'_! (g_X^* F) is an
isomorphism, re-hosted declaration by declaration from the library modules below, on top of the proper
base change libraries RPLib_FX_EtPBC, RPLib_FX_EtPBCB and RPLib_FX_EtPBCC1. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_C1_Paste`: S4-EtPBC-C1, part 21: pasting of base change morphisms (generic)
* `S4.Def_RP_EtPBC_C1_TrG`: S4-EtPBC-C1, part 22: base change morphisms under morphisms of squares (generic)
* `S4.Def_RP_EtPBC_C1_PasteC`: S4-EtPBC-C1, part 24: pasting of base change morphisms for composite squares (BC-MOR (1c))
* `S4.Def_RP_EtPBC_C1_PbcSqA`: S4-EtPBC-C1, part 29a: morphisms of `(g, s)`-squares, the fibre map and the pastings
* `S4.Def_RP_EtPBC_C1_StkTr`: S4-EtPBC-C1, part 29d: stalk transport along a morphism of (g, s)-squares
* `S4.Def_RP_EtPBC_C1_PbcSqB`: S4-EtPBC-C1, part 29b: naturality of `pbcEquivS` under morphisms of `(g, s)`-squares
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_C1_Paste =====
section

/-!
# S4-EtPBC-C1, part 21: pasting of base change morphisms (generic)

For two squares `β : R ⋙ Ld ⟶ Lc ⋙ R'` and `β' : R' ⋙ Ld' ⟶ Lc' ⋙ R''`, the pasted square
`pasteβ : R ⋙ (Ld ⋙ Ld') ⟶ (Lc ⋙ Lc') ⋙ R''` (`Ld' β ≫ β' Lc`) has base change morphism
**`bcMorGen_paste`**: `bcMorGen (pasteβ) q X = Ld' (bcMorGen β q X) ≫ bcMorGen β' q (Lc X)`
(`homologyMapIso_inv_comp`: `homologyMapIso` of a composite functor).
-/

set_option autoImplicit false

open CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] {D' : Type u₄} [Category.{v₄} D'] [Abelian D']
  {C'' : Type u₅} [Category.{v₅} C''] [Abelian C''] {D'' : Type u₆} [Category.{v₆} D''] [Abelian D'']

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section HMI

end HMI

variable (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive] (R'' : C'' ⥤ D'') [R''.Additive]
  (Lc : C ⥤ C') [Lc.Additive] [Lc.PreservesHomology] [Lc.PreservesMonomorphisms]
  (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology] (β : R ⋙ Ld ⟶ Lc ⋙ R')
  (Lc' : C' ⥤ C'') [Lc'.Additive] [Lc'.PreservesHomology] [Lc'.PreservesMonomorphisms]
  (Ld' : D' ⥤ D'') [Ld'.Additive] [Ld'.PreservesHomology] (β' : R' ⋙ Ld' ⟶ Lc' ⋙ R'')

variable [HasInjectiveResolutions C] [HasInjectiveResolutions C'] [HasInjectiveResolutions C'']
  [(Lc ⋙ Lc').PreservesHomology] [(Ld ⋙ Ld').PreservesHomology]

/-- **Pasting** (any resolutions `I`, `J`, `K`). -/
theorem bcMorRes_paste (q : ℕ) {X : C} (I : InjectiveResolution X) (J : InjectiveResolution (Lc.obj X))
    (K : InjectiveResolution (Lc'.obj (Lc.obj X))) :
    bcMorRes R R'' (Lc ⋙ Lc') (Ld ⋙ Ld') (pasteβ R R' R'' Lc Ld β Lc' Ld' β') q I K =
      Ld'.map (bcMorRes R R' Lc Ld β q I J) ≫ bcMorRes R' R'' Lc' Ld' β' q J K := by
  have hom : Homotopy ((Lc'.mapHomologicalComplex _).map (liftLc Lc I J) ≫ liftLc Lc' J K)
      (liftLc (Lc ⋙ Lc') I K) :=
    descRHomotopy (E := (ExRes.ofInj I).map (Lc ⋙ Lc')) _ _ (by
      change Lc'.map (Lc.map (I.ι.f 0)) ≫ (Lc'.map ((liftLc Lc I J).f 0) ≫ (liftLc Lc' J K).f 0) =
        (Lc ⋙ Lc').map (I.ι.f 0) ≫ (liftLc (Lc ⋙ Lc') I K).f 0
      rw [liftLc_f_zero, ← Lc'.map_comp_assoc, liftLc_f_zero, liftLc_f_zero])
  have chain : (Ld'.mapHomologicalComplex _).map (betaCx R R' Lc Ld β I.cocomplex ≫
        (R'.mapHomologicalComplex _).map (liftLc Lc I J)) ≫
      betaCx R' R'' Lc' Ld' β' J.cocomplex ≫ (R''.mapHomologicalComplex _).map (liftLc Lc' J K) =
      betaCx R R'' (Lc ⋙ Lc') (Ld ⋙ Ld') (pasteβ R R' R'' Lc Ld β Lc' Ld' β') I.cocomplex ≫
        (R''.mapHomologicalComplex _).map ((Lc'.mapHomologicalComplex _).map (liftLc Lc I J) ≫
          liftLc Lc' J K) := by
    ext n
    have h := β'.naturality ((liftLc Lc I J).f n)
    simp only [Functor.comp_map] at h
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, betaCx_f, pasteβ_app,
      Functor.map_comp, Category.assoc]
    rw [reassoc_of% h]
    rfl
  have hH : HomologicalComplex.homologyMap
      (betaCx R R'' (Lc ⋙ Lc') (Ld ⋙ Ld') (pasteβ R R' R'' Lc Ld β Lc' Ld' β') I.cocomplex ≫
        (R''.mapHomologicalComplex _).map (liftLc (Lc ⋙ Lc') I K)) q =
      HomologicalComplex.homologyMap ((Ld'.mapHomologicalComplex _).map (betaCx R R' Lc Ld β I.cocomplex ≫
        (R'.mapHomologicalComplex _).map (liftLc Lc I J))) q ≫
      HomologicalComplex.homologyMap (betaCx R' R'' Lc' Ld' β' J.cocomplex ≫
        (R''.mapHomologicalComplex _).map (liftLc Lc' J K)) q := by
    rw [← HomologicalComplex.homologyMap_comp, chain]
    exact (((R''.mapHomotopy hom).compLeft _).homologyMap_eq q).symm
  simp only [bcMorRes, Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [homologyMapIso_inv_comp, reassoc_of% (homologyMapIso_inv_nat Ld' (betaCx R R' Lc Ld β I.cocomplex ≫
    (R'.mapHomologicalComplex _).map (liftLc Lc I J)) q), hH, Functor.comp_map]
  simp only [Category.assoc]

/-- **Pasting of base change morphisms**: `bcMorGen (pasteβ) = Ld' (bcMorGen β) ≫ bcMorGen β' (Lc X)`. -/
theorem bcMorGen_paste (q : ℕ) (X : C) :
    bcMorGen R R'' (Lc ⋙ Lc') (Ld ⋙ Ld') (pasteβ R R' R'' Lc Ld β Lc' Ld' β') q X =
      Ld'.map (bcMorGen R R' Lc Ld β q X) ≫ bcMorGen R' R'' Lc' Ld' β' q (Lc.obj X) :=
  (bcMorGen_eq R R'' (Lc ⋙ Lc') (Ld ⋙ Ld') (pasteβ R R' R'' Lc Ld β Lc' Ld' β') q (injectiveResolution X)
    (injectiveResolution (Lc'.obj (Lc.obj X)))).trans
    (bcMorRes_paste R R' R'' Lc Ld β Lc' Ld' β' q (injectiveResolution X) (injectiveResolution (Lc.obj X))
      (injectiveResolution (Lc'.obj (Lc.obj X))))

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_TrG =====
section

/-!
# S4-EtPBC-C1, part 22: base change morphisms under morphisms of squares (generic)

For `θc : Lc ⟶ Lc₂`, `θd : Ld ⟶ Ld₂` and squares `β`, `β₂` with `θd_R ≫ β₂ = β ≫ R' θc`
(**`SqHom`**), **`bcMorGen_transport`**: `θd ≫ bcMorGen β₂ q X = bcMorGen β q X ≫ R'^q (θc X)`
(`homologyMapIso_inv_natTrans`: `homologyMapIso` is natural in the functor).
-/

set_option autoImplicit false

open CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] {D' : Type u₄} [Category.{v₄} D'] [Abelian D']

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section HMI

end HMI

variable (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive]
  {Lc Lc₂ : C ⥤ C'} [Lc.Additive] [Lc.PreservesHomology] [Lc.PreservesMonomorphisms]
  [Lc₂.Additive] [Lc₂.PreservesHomology] [Lc₂.PreservesMonomorphisms]
  {Ld Ld₂ : D ⥤ D'} [Ld.Additive] [Ld.PreservesHomology] [Ld₂.Additive] [Ld₂.PreservesHomology]
  (β : R ⋙ Ld ⟶ Lc ⋙ R') (β₂ : R ⋙ Ld₂ ⟶ Lc₂ ⋙ R') (θc : Lc ⟶ Lc₂) (θd : Ld ⟶ Ld₂)

variable [HasInjectiveResolutions C] [HasInjectiveResolutions C']

/-- **Base change morphisms under a morphism of squares**: `θd ≫ bcMorGen β₂ = bcMorGen β ≫ R'^q (θc X)`. -/
theorem bcMorGen_transport (h : SqHom R R' β β₂ θc θd) (q : ℕ) (X : C) :
    θd.app ((R.rightDerived q).obj X) ≫ bcMorGen R R' Lc₂ Ld₂ β₂ q X =
      bcMorGen R R' Lc Ld β q X ≫ (R'.rightDerived q).map (θc.app X) :=
  bcMorRes_transport R R' β β₂ θc θd h q (injectiveResolution X) (injectiveResolution (Lc.obj X))
    (injectiveResolution (Lc₂.obj X))

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_PasteC =====
section

/-!
# S4-EtPBC-C1, part 24: pasting of base change morphisms for composite squares (BC-MOR (1c))

For squares `sq₁ = (ιX₁, ιY₁, h, h', w₁)`, `sq₂ = (ιX₂, ιY₂, h', h'', w₂)` and their composite
`(ιX, ιY, h, h'', w)` with flexible composites `hX : ιX = ιX₂ ≫ ιX₁`, `hY : ιY = ιY₂ ≫ ιY₁`:

* `pullCompIso' Λ g f gf e : pull gf ≅ pull f ⋙ pull g` (`pullCongr e ≪≫ pullCompIso g f`);
* `sqHom_paste`: the composite cell `bcCell (ιX, ιY)` maps to the pasted cell `pasteβ (bcCell₁) (bcCell₂)`
  along `pullCompIso'` (a morphism of squares, `SqHom`);
* **`bcMorSq_paste`**: `θ_Y ≫ ιY₂^*(bcMorSq₁ q G) ≫ bcMorSq₂ q (ιX₁^* G) = bcMorSq q G ≫ R^q h''_*(θ_X G)`,
  `θ = (pullCompIso' ..).hom` (REMEDY_v5 row BC-MOR, item (1c)).
* generic: `sqHom_paste_of`, `bcMorGen_paste_tr`; sections: `pull_hom_ext` (maps out of `f^*F` are determined
  on pulled-back sections); site: `etPull3_hom_ext`, nested-typed `etPullCompHom'`, `bcSite`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.EtMV

universe u

section Site

end Site

section Gen

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] {D' : Type u₄} [Category.{v₄} D'] [Abelian D']
  {C'' : Type u₅} [Category.{v₅} C''] [Abelian C''] {D'' : Type u₆} [Category.{v₆} D''] [Abelian D'']
  (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive] (R'' : C'' ⥤ D'') [R''.Additive]
  (Lc : C ⥤ C') [Lc.Additive] [Lc.PreservesHomology] [Lc.PreservesMonomorphisms]
  (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology] (β : R ⋙ Ld ⟶ Lc ⋙ R')
  (Lc' : C' ⥤ C'') [Lc'.Additive] [Lc'.PreservesHomology] [Lc'.PreservesMonomorphisms]
  (Ld' : D' ⥤ D'') [Ld'.Additive] [Ld'.PreservesHomology] (β' : R' ⋙ Ld' ⟶ Lc' ⋙ R'')
  [(Lc ⋙ Lc').PreservesHomology] [(Ld ⋙ Ld').PreservesHomology]
  {Lc₀ : C ⥤ C''} [Lc₀.Additive] [Lc₀.PreservesHomology] [Lc₀.PreservesMonomorphisms]
  {Ld₀ : D ⥤ D''} [Ld₀.Additive] [Ld₀.PreservesHomology]
  (β₀ : R ⋙ Ld₀ ⟶ Lc₀ ⋙ R'') (θc : Lc₀ ⟶ Lc ⋙ Lc') (θd : Ld₀ ⟶ Ld ⋙ Ld')

variable [HasInjectiveResolutions C] [HasInjectiveResolutions C'] [HasInjectiveResolutions C'']

/-- **Pasting + transport** (generic): a morphism of squares from `β₀` to the pasted square gives
`θd ≫ Ld' (bcMorGen β) ≫ bcMorGen β' = bcMorGen β₀ ≫ R''^q (θc)`. -/
theorem bcMorGen_paste_tr (hs : SqHom R R'' β₀ (pasteβ R R' R'' Lc Ld β Lc' Ld' β') θc θd) (q : ℕ) (W : C) :
    θd.app ((R.rightDerived q).obj W) ≫ Ld'.map (bcMorGen R R' Lc Ld β q W) ≫
        bcMorGen R' R'' Lc' Ld' β' q (Lc.obj W) =
      bcMorGen R R'' Lc₀ Ld₀ β₀ q W ≫ (R''.rightDerived q).map (θc.app W) := by
  rw [← bcMorGen_paste]
  exact bcMorGen_transport R R'' β₀ _ θc θd hs q W

end Gen

variable {Λ : Type u} [CommRing Λ]

section Paste

variable {X Y X' Y' X'' Y'' : Scheme.{u}}
  (ιX₁ : X' ⟶ X) (ιY₁ : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y') (w₁ : h' ≫ ιY₁ = ιX₁ ≫ h)
  (ιX₂ : X'' ⟶ X') (ιY₂ : Y'' ⟶ Y') (h'' : X'' ⟶ Y'') (w₂ : h'' ≫ ιY₂ = ιX₂ ≫ h')
  (ιX : X'' ⟶ X) (ιY : Y'' ⟶ Y) (hX : ιX = ιX₂ ≫ ιX₁) (hY : ιY = ιY₂ ≫ ιY₁) (w : h'' ≫ ιY = ιX ≫ h)

/-- **Pasting of base change morphisms for composite squares** (BC-MOR (1c)):
`θ_Y ≫ ιY₂^*(bcMorSq₁) ≫ bcMorSq₂ = bcMorSq (composite) ≫ R^q h''_*(θ_X)`, with `θ = pullCompIso'`. -/
theorem bcMorSq_paste (q : ℕ) (G : EtSh Λ X) :
    (pullCompIso' Λ ιY₂ ιY₁ ιY hY).hom.app (((push h Λ).rightDerived q).obj G) ≫
        (pull ιY₂ Λ).map (bcMorSq Λ ιX₁ ιY₁ h h' w₁ q G) ≫ bcMorSq Λ ιX₂ ιY₂ h' h'' w₂ q ((pull ιX₁ Λ).obj G) =
      bcMorSq Λ ιX ιY h h'' w q G ≫
        ((push h'' Λ).rightDerived q).map ((pullCompIso' Λ ιX₂ ιX₁ ιX hX).hom.app G) :=
  bcMorGen_paste_tr (push h Λ) (push h' Λ) (push h'' Λ) (pull ιX₁ Λ) (pull ιY₁ Λ) (bcCell Λ ιX₁ ιY₁ h h' w₁)
    (pull ιX₂ Λ) (pull ιY₂ Λ) (bcCell Λ ιX₂ ιY₂ h' h'' w₂) (bcCell Λ ιX ιY h h'' w)
    (pullCompIso' Λ ιX₂ ιX₁ ιX hX).hom (pullCompIso' Λ ιY₂ ιY₁ ιY hY).hom
    (sqHom_paste ιX₁ ιY₁ h h' w₁ ιX₂ ιY₂ h'' w₂ ιX ιY hX hY w) q G

end Paste

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_PbcSqA =====
section

/-!
# S4-EtPBC-C1, part 29a: morphisms of `(g, s)`-squares, the fibre map and the pastings

* `nestComp`, **`sqNatAbs`**: nested-typed comparisons and squares of squares with abstract functors (kernel-cheap);
* `fibHGen`, **`natS_gen`**, **`nat0_gen`**: generic naturality of `absRelR` / the degree-`0` description under
  base change followed by a coefficient map (HasExt instances implicit, unified from the concrete statement);
* **`SqMor g₁ g₂ s₁ s₂`**: `eP : P₂ ⟶ P₁`, `eS : S₂ ⟶ S₁` with `g₂ ≫ eS = eP ≫ g₁`, and `σ : Spec Ω₂ ⟶ Spec Ω₁` with
  `s₂ ≫ eS = σ ≫ s₁` (any morphisms of schemes, not over a base field); `fibMap : P₂_{s₂} ⟶ P₁_{s₁}`;
  `κApp`, `θApp` (coefficient and point comparisons); **`fibH`**: pull-back on fibre cohomology;
* **`sqNat_fib`**: the two pastings of the fibre squares with `m` (`sqNatAbs` of two `bcMorSq_paste`);
  `keyMor`: its stalk-section form.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec

universe u

section Abs

end Abs

section GenNat

universe w

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {C' : Type*} [Category C'] [Abelian C'] {D' : Type*} [Category D'] [Abelian D']
  (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive]
  (Lc : C ⥤ C') [Lc.Additive] [PreservesFiniteLimits Lc] [PreservesFiniteColimits Lc]
  (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology]
  (β : R ⋙ Ld ⟶ Lc ⋙ R') [HasInjectiveResolutions C] [HasInjectiveResolutions C']
  {L₁ : D ⥤ C} (adj₁ : L₁ ⊣ R) {A₁ : D} {X₁ : C} (e₁ : L₁.obj A₁ ≅ X₁)
  {L₂ : D' ⥤ C'} (adj₂ : L₂ ⊣ R') {A₂ : D'} {X₂ : C'} (e₂ : L₂.obj A₂ ≅ X₂)
  (a : A₂ ⟶ Ld.obj A₁) (u : X₂ ⟶ Lc.obj X₁)

/-- **Generic naturality, degrees `p + 1`** (HasExt instances implicit: unified from the concrete statement). -/
theorem natS_gen {hC : HasExt.{w} C} {hC' : HasExt.{w} C'} (h : UnitCell R R' Lc Ld β adj₁ e₁ adj₂ e₂ a u)
    [Projective A₁] [Projective A₂] {Y : C} {Y' : C'} (I : InjectiveResolution Y)
    (J : InjectiveResolution (Lc.obj Y)) (J' : InjectiveResolution Y') (p : ℕ) (κ : Lc.obj Y ⟶ Y')
    {x : Abelian.Ext.{w} X₁ Y (p + 1)} {x' : Abelian.Ext.{w} X₂ Y' (p + 1)}
    {M : A₂ ⟶ (R'.rightDerived (p + 1)).obj Y'} {M₁ : A₁ ⟶ (R.rightDerived (p + 1)).obj Y}
    (hx' : absRelR adj₂ e₂ J' p x' = M) (hx : absRelR adj₁ e₁ I p x = M₁)
    (hM : M = a ≫ Ld.map M₁ ≫ bcMorGen R R' Lc Ld β (p + 1) Y ≫ (R'.rightDerived (p + 1)).map κ) :
    x' = fibHGen Lc u κ (p + 1) x := by
  rw [fibHGen]
  apply (absRelR adj₂ e₂ J' p).injective
  rw [hx', absRelR_natural adj₂ e₂ J J' p κ, absRelR_bcGen R R' Lc Ld β adj₁ e₁ adj₂ e₂ a u h I J p x, hx, hM]
  simp only [Category.assoc]

/-- **Generic naturality, degree `0`.** -/
theorem nat0_gen {hC : HasExt.{w} C} {hC' : HasExt.{w} C'} [PreservesFiniteLimits R']
    (h : UnitCell R R' Lc Ld β adj₁ e₁ adj₂ e₂ a u) {Y : C} {Y' : C'} (κ : Lc.obj Y ⟶ Y')
    {x : Abelian.Ext.{w} X₁ Y 0} {x' : Abelian.Ext.{w} X₂ Y' 0}
    {M : A₂ ⟶ (R'.rightDerived 0).obj Y'} {M₁ : A₁ ⟶ (R.rightDerived 0).obj Y}
    (hx' : adj₂.homEquiv _ _ (e₂.hom ≫ Abelian.Ext.addEquiv₀ x') ≫ R'.toRightDerivedZero.app Y' = M)
    (hx : adj₁.homEquiv _ _ (e₁.hom ≫ Abelian.Ext.addEquiv₀ x) ≫ R.toRightDerivedZero.app Y = M₁)
    (hM : M = a ≫ Ld.map M₁ ≫ bcMorGen R R' Lc Ld β 0 Y ≫ (R'.rightDerived 0).map κ) :
    x' = fibHGen Lc u κ 0 x := by
  rw [fibHGen]
  apply abs0_injective adj₂ e₂.hom
  rw [hx', abs0_natural adj₂ e₂.hom κ, addEquiv₀_bc Lc u, abs0_bc R R' Lc Ld β adj₁ e₁ adj₂ e₂ a u h, hx, hM]
  simp only [Category.assoc]

end GenNat

variable {Λ : Type u} [CommRing Λ]

namespace SqMor

variable {P₁ S₁ P₂ S₂ : Scheme.{u}} {g₁ : P₁ ⟶ S₁} {g₂ : P₂ ⟶ S₂} {s₁ : GeomPt S₁} {s₂ : GeomPt S₂}
  (m : SqMor g₁ g₂ s₁ s₂)

/-- **The two pastings** of the fibre squares with `m`. -/
theorem sqNat_fib (q : ℕ) (F : EtSh Λ P₁) :
    (pull m.σ Λ).map (bcMorSq Λ (fibι g₁ s₁) s₁.pt g₁ (pullback.snd g₁ s₁.pt)
        (pullback.condition (f := g₁) (g := s₁.pt)).symm q F) ≫
      bcMorSq Λ m.fibMap m.σ (pullback.snd g₁ s₁.pt) (pullback.snd g₂ s₂.pt) m.fibMap_π.symm q
        ((pull (fibι g₁ s₁) Λ).obj F) ≫
      ((push (X := fib g₂ s₂) (pullback.snd g₂ s₂.pt) Λ).rightDerived q).map (m.κApp F) =
    m.θApp (((push g₁ Λ).rightDerived q).obj F) ≫ (pull s₂.pt Λ).map (bcMorSq Λ m.eP m.eS g₁ g₂ m.wE q F) ≫
      bcMorSq Λ (fibι g₂ s₂) s₂.pt g₂ (pullback.snd g₂ s₂.pt) (pullback.condition (f := g₂) (g := s₂.pt)).symm q
        ((pull m.eP Λ).obj F) :=
  sqNatAbs (pullCompIso' Λ m.fibMap (fibι g₁ s₁) (fibι g₂ s₂ ≫ m.eP) m.fibMap_ι.symm)
    (pullCompIso' Λ (fibι g₂ s₂) m.eP (fibι g₂ s₂ ≫ m.eP) rfl)
    (pullCompIso' Λ m.σ s₁.pt (s₂.map m.eS).pt m.wσ) (pullCompIso' Λ s₂.pt m.eS (s₂.map m.eS).pt rfl)
    (bcMorSq_paste (fibι g₁ s₁) s₁.pt g₁ (pullback.snd g₁ s₁.pt) (pullback.condition (f := g₁) (g := s₁.pt)).symm
      m.fibMap m.σ (pullback.snd g₂ s₂.pt) m.fibMap_π.symm (fibι g₂ s₂ ≫ m.eP) (s₂.map m.eS).pt
      m.fibMap_ι.symm m.wσ m.wc q F)
    (bcMorSq_paste m.eP m.eS g₁ g₂ m.wE (fibι g₂ s₂) s₂.pt (pullback.snd g₂ s₂.pt)
      (pullback.condition (f := g₂) (g := s₂.pt)).symm (fibι g₂ s₂ ≫ m.eP) (s₂.map m.eS).pt rfl rfl m.wc q F)

/-- **`sqNat_fib` in stalk-section form**: for `z` whose section is the `σ`-pull-back of that of `y₁`. -/
theorem keyMor (F : EtSh Λ P₁) (q : ℕ) (y₁ : (s₁.stalkF Λ).obj (((push g₁ Λ).rightDerived q).obj F))
    (z : (s₂.stalkF Λ).obj ((pull m.eS Λ).obj (((push g₁ Λ).rightDerived q).obj F)))
    (hz : stalkSec s₂ _ z = (pullUnit Λ m.σ).hom ≫ (pull m.σ Λ).map (stalkSec s₁ _ y₁) ≫
      m.θApp (((push g₁ Λ).rightDerived q).obj F)) :
    (stalkSec s₂ _ z ≫ (pull s₂.pt Λ).map (bcMorSq Λ m.eP m.eS g₁ g₂ m.wE q F)) ≫
      bcMorSq Λ (fibι g₂ s₂) s₂.pt g₂ (pullback.snd g₂ s₂.pt) (pullback.condition (f := g₂) (g := s₂.pt)).symm q
        ((pull m.eP Λ).obj F) =
    (pullUnit Λ m.σ).hom ≫ (pull m.σ Λ).map (stalkSec s₁ _ y₁ ≫ bcMorSq Λ (fibι g₁ s₁) s₁.pt g₁
        (pullback.snd g₁ s₁.pt) (pullback.condition (f := g₁) (g := s₁.pt)).symm q F) ≫
      bcMorSq Λ m.fibMap m.σ (pullback.snd g₁ s₁.pt) (pullback.snd g₂ s₂.pt) m.fibMap_π.symm q
        ((pull (fibι g₁ s₁) Λ).obj F) ≫
      ((push (X := fib g₂ s₂) (pullback.snd g₂ s₂.pt) Λ).rightDerived q).map (m.κApp F) := by
  rw [hz]
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rw [sqNat_fib]

end SqMor

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_StkTr =====
section

/-! # S4-EtPBC-C1, part 29d: stalk transport along a morphism of (g, s)-squares -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec

universe u

section NestIso
end NestIso

section NestTr
end NestTr

section PullOfSec

end PullOfSec

section Pt

end Pt

namespace SqMor

variable {Λ : Type u} [CommRing Λ]
variable {P₁ S₁ P₂ S₂ : Scheme.{u}} {g₁ : P₁ ⟶ S₁} {g₂ : P₂ ⟶ S₂} {s₁ : GeomPt S₁} {s₂ : GeomPt S₂}
  (m : SqMor g₁ g₂ s₁ s₂)

/-- The transported stalk element satisfies the section compatibility `hz` of `pbcEquiv_sq`. -/
theorem stalkSec_stalkTr (G : EtSh Λ S₁) (y₁ : (s₁.stalkF Λ).obj G) :
    stalkSec s₂ _ ((m.stalkTr G).hom y₁) =
      (pullUnit Λ m.σ).hom ≫ (pull m.σ Λ).map (stalkSec s₁ _ y₁) ≫ m.θApp G := by
  rw [stalkTr, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact nestComp_tr (pullCompIso' Λ m.σ s₁.pt (s₂.map m.eS).pt m.wσ)
    (pullCompIso' Λ s₂.pt m.eS (s₂.map m.eS).pt rfl) G (stalkSec_pullStalk m.eS s₂ G _)
    (stalkSec_stalkMor s₁ (s₂.map m.eS) m.σ m.wσ.symm Λ G y₁)

end SqMor

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_PbcSqB =====
section

/-!
# S4-EtPBC-C1, part 29b: naturality of `pbcEquivS` under morphisms of `(g, s)`-squares

**`pbcEquivS_sq`** (degrees `p + 1`): for `z` in the stalk at `s₂` of `eS^* R^(p+1) g₁_* F` whose section over
`Spec Ω₂` is the `σ`-pull-back of that of `y₁` (hypothesis `hz`),
`pbcEquivS (stalk of bcMorSq(m) z) = m.fibH (pbcEquivS y₁)` (`natS_gen` with `pbcEquivS_spec` and `keyMor`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec

universe u

variable {Λ : Type u} [CommRing Λ]

namespace SqMor

variable {P₁ S₁ P₂ S₂ : Scheme.{u}} {g₁ : P₁ ⟶ S₁} {g₂ : P₂ ⟶ S₂} {s₁ : GeomPt S₁} {s₂ : GeomPt S₂}
  (m : SqMor g₁ g₂ s₁ s₂)

/-- **Naturality of `pbcEquivS` under a morphism of `(g, s)`-squares** (degrees `p + 1`). -/
theorem pbcEquivS_sq (F : EtSh Λ P₁) (p : ℕ) (hI₁ : BCInj Λ g₁ s₁ (p + 1) F) (hS₁ : BCSurj Λ g₁ s₁ (p + 1) F)
    (hI₂ : BCInj Λ g₂ s₂ (p + 1) ((pull m.eP Λ).obj F)) (hS₂ : BCSurj Λ g₂ s₂ (p + 1) ((pull m.eP Λ).obj F))
    (y₁ : (s₁.stalkF Λ).obj (((push g₁ Λ).rightDerived (p + 1)).obj F))
    (z : (s₂.stalkF Λ).obj ((pull m.eS Λ).obj (((push g₁ Λ).rightDerived (p + 1)).obj F)))
    (hz : stalkSec s₂ _ z = (pullUnit Λ m.σ).hom ≫ (pull m.σ Λ).map (stalkSec s₁ _ y₁) ≫
      m.θApp (((push g₁ Λ).rightDerived (p + 1)).obj F)) :
    pbcEquivS g₂ s₂ ((pull m.eP Λ).obj F) p hI₂ hS₂
        (((s₂.stalkF Λ).map (bcMorSq Λ m.eP m.eS g₁ g₂ m.wE (p + 1) F)).hom z) =
      m.fibH F (p + 1) (pbcEquivS g₁ s₁ F p hI₁ hS₁ y₁) := by
  have := unitSh_projective_spec s₁.Ω Λ
  have := unitSh_projective_spec s₂.Ω Λ
  exact natS_gen _ _ _ _ _ _ _ _ _ _ _
    (unitCell_sq Λ m.fibMap m.σ (pullback.snd g₁ s₁.pt) (pullback.snd g₂ s₂.pt) m.fibMap_π.symm)
    (injectiveResolution ((pull (fibι g₁ s₁) Λ).obj F))
    (injectiveResolution ((pull m.fibMap Λ).obj ((pull (fibι g₁ s₁) Λ).obj F)))
    (injectiveResolution ((pull (fibι g₂ s₂) Λ).obj ((pull m.eP Λ).obj F))) p (m.κApp F)
    (pbcEquivS_spec g₂ s₂ _ p _ hI₂ hS₂ _) (pbcEquivS_spec g₁ s₁ F p _ hI₁ hS₁ y₁)
    (by rw [stalkSec_natural]; exact m.keyMor F (p + 1) y₁ z hz)

end SqMor

end RamanujanPetersson.EtPBC.C1

end

end


