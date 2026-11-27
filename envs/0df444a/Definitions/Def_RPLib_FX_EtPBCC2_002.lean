-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC2_002
-- name    : RPLib_FX_EtPBCC2_002
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-27T00:56:11.348097+00:00
-- url     : https://prove2.me/theorems/bbfd1566-d7fd-52f3-bb1e-96b526f833c3
-- title:
--   Sheaf-level proper base change with compact supports, library file 002
-- statement:
--   File 002 of the library for sheaf-level proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_C1_Mor`: S4-EtPBC-C1, part 3: the base change morphism `g^* R^q f_! F ⟶ R^q f'_! g'^* F`
--   * `S4.Def_RP_EtPBC_C1_AbsBC`: S4-EtPBC-C1, part 27: `absRelR` under base change (generic)
--   * `S4.Def_RP_EtPBC_C1_Paste`: S4-EtPBC-C1, part 21: pasting of base change morphisms (generic)
--   * `S4.Def_RP_EtPBC_C1_TrG`: S4-EtPBC-C1, part 22: base change morphisms under morphisms of squares (generic)
--   * `S4.Def_RP_EtPBC_C1_PasteC`: S4-EtPBC-C1, part 24: pasting of base change morphisms for composite squares (BC-MOR (1c))
--   * `S4.Def_RP_EtPBC_C1_SqNat`: S4-EtPBC-C1, part 28: squares of squares and the unit cell of a square
--   * `S4.Def_RP_EtPBC_C1_PbcSqA`: S4-EtPBC-C1, part 29a: morphisms of `(g, s)`-squares, the fibre map and the pastings
--   * `S4.Def_RP_EtPBC_C1_StkTr`: S4-EtPBC-C1, part 29d: stalk transport along a morphism of (g, s)-squares
--   * `S4.Def_RP_EtPBC_C2_BcIso`: S4-EtPBC-C2, part 3: the base change morphism is an isomorphism (generic, closed-point form)
--   * `S4.Def_RP_EtPBC_C2_Tow`: S4-EtPBC-C2, part 2: tower maps (iterated `P^1`-bundles up to isomorphism)
--
--   **Formalization note.** One file of a library formalizing sheaf-level proper base change for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ a tower of projective-line bundles over a noetherian $S$ of finite type over an algebraically closed field), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and any $g : S' \to S$ of finite type, the base change morphism $g^* R^q f_! F \to R^q f'_! (g_X^* F)$ is an isomorphism for every sheaf $F$ of $\Lambda$-modules ($\Lambda$ finite, $\ell$-power torsion). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`), for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`) and for the stalks of $R^q f_!$ (`RPLib_FX_EtPBCC1_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC2_001

/-!
# Sheaf-level proper base change with compact supports, library file 002

Declarations of the formalization of sheaf-level proper base change for compactly supported étale
cohomology: for a compactified X ⟶ S whose proper part is an iterated projective-line bundle (a tower)
and any g : S' ⟶ S of finite type, the base change morphism g^* R^q f_! F ⟶ R^q f'_! (g_X^* F) is an
isomorphism, re-hosted declaration by declaration from the library modules below, on top of the proper
base change libraries RPLib_FX_EtPBC, RPLib_FX_EtPBCB and RPLib_FX_EtPBCC1. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_C1_Mor`: S4-EtPBC-C1, part 3: the base change morphism `g^* R^q f_! F ⟶ R^q f'_! g'^* F`
* `S4.Def_RP_EtPBC_C1_AbsBC`: S4-EtPBC-C1, part 27: `absRelR` under base change (generic)
* `S4.Def_RP_EtPBC_C1_Paste`: S4-EtPBC-C1, part 21: pasting of base change morphisms (generic)
* `S4.Def_RP_EtPBC_C1_TrG`: S4-EtPBC-C1, part 22: base change morphisms under morphisms of squares (generic)
* `S4.Def_RP_EtPBC_C1_PasteC`: S4-EtPBC-C1, part 24: pasting of base change morphisms for composite squares (BC-MOR (1c))
* `S4.Def_RP_EtPBC_C1_SqNat`: S4-EtPBC-C1, part 28: squares of squares and the unit cell of a square
* `S4.Def_RP_EtPBC_C1_PbcSqA`: S4-EtPBC-C1, part 29a: morphisms of `(g, s)`-squares, the fibre map and the pastings
* `S4.Def_RP_EtPBC_C1_StkTr`: S4-EtPBC-C1, part 29d: stalk transport along a morphism of (g, s)-squares
* `S4.Def_RP_EtPBC_C2_BcIso`: S4-EtPBC-C2, part 3: the base change morphism is an isomorphism (generic, closed-point form)
* `S4.Def_RP_EtPBC_C2_Tow`: S4-EtPBC-C2, part 2: tower maps (iterated `P^1`-bundles up to isomorphism)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_C1_Mor =====
section

/-!
# S4-EtPBC-C1, part 3: the base change morphism `g^* R^q f_! F ⟶ R^q f'_! g'^* F`

* `bcCell`: for a commutative square `h' ≫ ιY = ιX ≫ h` of schemes, the base change 2-cell
  `ιY^* h_* ⟶ h'_* ιX^*` (the mate of `sqQ`); `bcCell_counit`, `bcCell_app` (mate formula); `bcCell` is an iso for closed squares.
* `bcMorSq q G : ιY^* R^q h_* G ⟶ R^q h'_* ιX^* G` (`bcMorGen` for push/pull), natural in `G`.
* `itCpt c g`: the base change of a compactification `c : Cpt f` along ANY `g : B' ⟶ B` (iterated pullbacks;
  for `g = s.pt` it is `fibCpt c s`); `itExtNat : c.ext ⋙ gP^* ≅ gX^* ⋙ (itCpt c g).ext`.
* **`bcMor c g q F : g^* R^q f_! F ⟶ R^q f'_! gX^* F`**, natural in `F` (`bcMor_natural`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ]

section Sq

end Sq

section Closed

end Closed

section It

variable {X B B' : Scheme.{u}} {f : X ⟶ B} (c : Cpt f) (g : B' ⟶ B)

/-- `bcMor` unfolded: `bcMorSq` on `c.ext F`, then `R^q f'_*` of the extension iso. (Term-mode via the generic
`idSand`: the kernel checks one unfolding instead of one per `simp` motive; 21 -> 14 s laptop, s14.) -/
theorem bcMor_eq (q : ℕ) (F : EtSh Λ X) :
    bcMor Λ c g q F = bcMorSq Λ (itgP c g) g c.fbar (pullback.snd c.fbar g) pullback.condition.symm q
      ((c.ext Λ).obj F) ≫ ((push (pullback.snd c.fbar g) Λ).rightDerived q).map ((itExtNat Λ c g).hom.app F) :=
  idSand (bcMorSq Λ (itgP c g) g c.fbar (pullback.snd c.fbar g) pullback.condition.symm q ((c.ext Λ).obj F))
    (((push (pullback.snd c.fbar g) Λ).rightDerived q).map ((itExtNat Λ c g).hom.app F))

end It

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_AbsBC =====
section

/-!
# S4-EtPBC-C1, part 27: `absRelR` under base change (generic)

Two adjunctions `adj₁ : L₁ ⊣ R`, `adj₂ : L₂ ⊣ R'`, exact `Lc : C ⥤ C'`, `Ld : D ⥤ D'`, a base-change cell
`β : R ⋙ Ld ⟶ Lc ⋙ R'`, "unit" objects `e₁ : L₁ A₁ ≅ X₁`, `e₂ : L₂ A₂ ≅ X₂` and comparison maps
`a : A₂ ⟶ Ld A₁`, `u : X₂ ⟶ Lc X₁` satisfying the cell condition `UnitCell`:
* **`absRelR_bc`**: `absRelR₂ (mk₀ u ∘ Lc x) = a ≫ Ld (absRelR₁ x) ≫ bcMorRes β` (degrees `p + 1`);
* **`abs0_bc`**: the degree-`0` form (`homEquiv` and `toRightDerivedZero`), and `addEquiv₀_bc`;
* **`unitCell_of_mate`**: `UnitCell` from the transposed condition when `β` is the mate of `γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

universe w

section Cell

end Cell

section BC

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {C' : Type*} [Category C'] [Abelian C'] {D' : Type*} [Category D'] [Abelian D']
  (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive]
  (Lc : C ⥤ C') [Lc.Additive] [PreservesFiniteLimits Lc] [PreservesFiniteColimits Lc]
  (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology]
  (β : R ⋙ Ld ⟶ Lc ⋙ R') [HasInjectiveResolutions C] [HasInjectiveResolutions C']
  [HasExt.{w} C] [HasExt.{w} C']
  {L₁ : D ⥤ C} (adj₁ : L₁ ⊣ R) {A₁ : D} {X₁ : C} (e₁ : L₁.obj A₁ ≅ X₁)
  {L₂ : D' ⥤ C'} (adj₂ : L₂ ⊣ R') {A₂ : D'} {X₂ : C'} (e₂ : L₂.obj A₂ ≅ X₂)
  (a : A₂ ⟶ Ld.obj A₁) (u : X₂ ⟶ Lc.obj X₁)

set_option backward.isDefEq.respectTransparency false in
/-- **`absRelR` under base change** (degrees `p + 1`, any injective resolutions `I`, `J`). -/
theorem absRelR_bc (h : UnitCell R R' Lc Ld β adj₁ e₁ adj₂ e₂ a u) [Projective A₁] [Projective A₂]
    {Y : C} (I : InjectiveResolution Y) (J : InjectiveResolution (Lc.obj Y)) (p : ℕ)
    (x : Abelian.Ext.{w} X₁ Y (p + 1)) :
    absRelR adj₂ e₂ J p ((Abelian.Ext.mk₀ u).comp (x.mapExactFunctor Lc) (zero_add (p + 1))) =
      a ≫ Ld.map (absRelR adj₁ e₁ I p x) ≫ bcMorRes R R' Lc Ld β (p + 1) I J := by
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective x (p + 1 + 1) rfl
  rw [mapExactFunctor_extMk Lc I J (liftLc Lc I J) (liftLc_f_zero Lc I J) f (p + 1 + 1) rfl hf,
    InjectiveResolution.mk₀_comp_extMk, absRelR_apply, absRelR_apply, absRelGen_extMk adj₁ e₁ I p f hf]
  exact glue_gen R R' Lc Ld β adj₂ e₂ p I J a (adj₁.homEquiv _ _ (e₁.hom ≫ f))
    (EtCompact.flat_cocycle adj₁ e₁ I hf) u f (unitCell_comp R R' Lc Ld β adj₁ e₁ adj₂ e₂ a u h f) _

/-- **`absRelR` under base change**, `bcMorGen` form. -/
theorem absRelR_bcGen (h : UnitCell R R' Lc Ld β adj₁ e₁ adj₂ e₂ a u) [Projective A₁] [Projective A₂]
    {Y : C} (I : InjectiveResolution Y) (J : InjectiveResolution (Lc.obj Y)) (p : ℕ)
    (x : Abelian.Ext.{w} X₁ Y (p + 1)) :
    absRelR adj₂ e₂ J p ((Abelian.Ext.mk₀ u).comp (x.mapExactFunctor Lc) (zero_add (p + 1))) =
      a ≫ Ld.map (absRelR adj₁ e₁ I p x) ≫ bcMorGen R R' Lc Ld β (p + 1) Y := by
  rw [absRelR_bc R R' Lc Ld β adj₁ e₁ adj₂ e₂ a u h I J p x, bcMorGen_eq R R' Lc Ld β (p + 1) I J]

/-- **Degree `0`**: the class `homEquiv (e ≫ x₀) ≫ toRightDerivedZero` under base change. -/
theorem abs0_bc (h : UnitCell R R' Lc Ld β adj₁ e₁ adj₂ e₂ a u) {Y : C} (x₀ : X₁ ⟶ Y) :
    adj₂.homEquiv _ _ (e₂.hom ≫ u ≫ Lc.map x₀) ≫ R'.toRightDerivedZero.app (Lc.obj Y) =
      a ≫ Ld.map (adj₁.homEquiv _ _ (e₁.hom ≫ x₀) ≫ R.toRightDerivedZero.app Y) ≫
        bcMorGen R R' Lc Ld β 0 Y := by
  rw [Ld.map_comp, Category.assoc, bcMorGen_zero, ← unitCell_comp R R' Lc Ld β adj₁ e₁ adj₂ e₂ a u h x₀]
  simp only [Category.assoc]

end BC

end RamanujanPetersson.EtPBC.C1

end

end

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

@[simp] theorem pasteβ_app (X : C) :
    (pasteβ R R' R'' Lc Ld β Lc' Ld' β').app X = Ld'.map (β.app X) ≫ β'.app (Lc.obj X) :=
  rfl

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

/-- **Base change morphisms under a morphism of squares** (any resolutions). -/
theorem bcMorRes_transport (h : SqHom R R' β β₂ θc θd) (q : ℕ) {X : C} (I : InjectiveResolution X)
    (J : InjectiveResolution (Lc.obj X)) (J₂ : InjectiveResolution (Lc₂.obj X)) :
    θd.app ((R.rightDerived q).obj X) ≫ bcMorRes R R' Lc₂ Ld₂ β₂ q I J₂ =
      bcMorRes R R' Lc Ld β q I J ≫ (R'.rightDerived q).map (θc.app X) := by
  have hom : Homotopy ((NatTrans.mapHomologicalComplex θc _).app I.cocomplex ≫ liftLc Lc₂ I J₂)
      (liftLc Lc I J ≫ InjectiveResolution.desc (θc.app X) J₂ J) :=
    descRHomotopy (E := (ExRes.ofInj I).map Lc) _ _ (by
      change Lc.map (I.ι.f 0) ≫ (θc.app (I.cocomplex.X 0) ≫ (liftLc Lc₂ I J₂).f 0) =
        Lc.map (I.ι.f 0) ≫ ((liftLc Lc I J).f 0 ≫ (InjectiveResolution.desc (θc.app X) J₂ J).f 0)
      rw [← Category.assoc, θc.naturality, Category.assoc, liftLc_f_zero, liftLc_f_zero_assoc,
        InjectiveResolution.desc_commutes_zero]
      rfl)
  have chain : (NatTrans.mapHomologicalComplex θd _).app ((R.mapHomologicalComplex _).obj I.cocomplex) ≫
      betaCx R R' Lc₂ Ld₂ β₂ I.cocomplex ≫ (R'.mapHomologicalComplex _).map (liftLc Lc₂ I J₂) =
      betaCx R R' Lc Ld β I.cocomplex ≫ (R'.mapHomologicalComplex _).map
        ((NatTrans.mapHomologicalComplex θc _).app I.cocomplex ≫ liftLc Lc₂ I J₂) := by
    ext n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, betaCx_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.map_comp]
    exact (reassoc_of% (h (I.cocomplex.X n))) (R'.map ((liftLc Lc₂ I J₂).f n))
  have hH : HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex θd _).app
      ((R.mapHomologicalComplex _).obj I.cocomplex)) q ≫
      HomologicalComplex.homologyMap (betaCx R R' Lc₂ Ld₂ β₂ I.cocomplex ≫
        (R'.mapHomologicalComplex _).map (liftLc Lc₂ I J₂)) q =
      HomologicalComplex.homologyMap (betaCx R R' Lc Ld β I.cocomplex ≫
        (R'.mapHomologicalComplex _).map (liftLc Lc I J)) q ≫
      HomologicalComplex.homologyMap ((R'.mapHomologicalComplex _).map
        (InjectiveResolution.desc (θc.app X) J₂ J)) q := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, chain, Category.assoc,
      ← Functor.map_comp]
    exact ((R'.mapHomotopy hom).compLeft _).homologyMap_eq q
  simp only [bcMorRes, Category.assoc]
  rw [← θd.naturality_assoc]
  erw [reassoc_of% (homologyMapIso_inv_natTrans θd ((R.mapHomologicalComplex _).obj
    I.cocomplex) q)]
  rw [reassoc_of% hH, InjectiveResolution.isoRightDerivedObj_inv_naturality (θc.app X) J J₂
    (InjectiveResolution.desc (θc.app X) J₂ J) (InjectiveResolution.desc_commutes_zero _ _ _) R' q]
  rfl

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

end Gen

variable {Λ : Type u} [CommRing Λ]

section Paste

variable {X Y X' Y' X'' Y'' : Scheme.{u}}
  (ιX₁ : X' ⟶ X) (ιY₁ : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y') (w₁ : h' ≫ ιY₁ = ιX₁ ≫ h)
  (ιX₂ : X'' ⟶ X') (ιY₂ : Y'' ⟶ Y') (h'' : X'' ⟶ Y'') (w₂ : h'' ≫ ιY₂ = ιX₂ ≫ h')
  (ιX : X'' ⟶ X) (ιY : Y'' ⟶ Y) (hX : ιX = ιX₂ ≫ ιX₁) (hY : ιY = ιY₂ ≫ ιY₁) (w : h'' ≫ ιY = ιX ≫ h)

/-- The pasting identity on nested objects. -/
theorem paste_nested (G : EtSh Λ X) :
    CategoryStruct.comp (X := (pull ιY Λ).obj ((push h Λ).obj G))
        (Y := (pull ιY₂ Λ).obj ((pull ιY₁ Λ).obj ((push h Λ).obj G)))
        (Z := (push h'' Λ).obj ((pull ιX₂ Λ).obj ((pull ιX₁ Λ).obj G)))
      ((pullCompIso' Λ ιY₂ ιY₁ ιY hY).hom.app ((push h Λ).obj G))
      (CategoryStruct.comp (X := (pull ιY₂ Λ).obj ((pull ιY₁ Λ).obj ((push h Λ).obj G)))
          (Y := (pull ιY₂ Λ).obj ((push h' Λ).obj ((pull ιX₁ Λ).obj G)))
          (Z := (push h'' Λ).obj ((pull ιX₂ Λ).obj ((pull ιX₁ Λ).obj G)))
        ((pull ιY₂ Λ).map (X := (pull ιY₁ Λ).obj ((push h Λ).obj G))
          (Y := (push h' Λ).obj ((pull ιX₁ Λ).obj G)) ((bcCell Λ ιX₁ ιY₁ h h' w₁).app G))
        ((bcCell Λ ιX₂ ιY₂ h' h'' w₂).app ((pull ιX₁ Λ).obj G))) =
    CategoryStruct.comp (X := (pull ιY Λ).obj ((push h Λ).obj G)) (Y := (push h'' Λ).obj ((pull ιX Λ).obj G))
        (Z := (push h'' Λ).obj ((pull ιX₂ Λ).obj ((pull ιX₁ Λ).obj G)))
      ((bcCell Λ ιX ιY h h'' w).app G)
      ((push h'' Λ).map (X := (pull ιX Λ).obj G) (Y := (pull ιX₂ Λ).obj ((pull ιX₁ Λ).obj G))
        ((pullCompIso' Λ ιX₂ ιX₁ ιX hX).hom.app G)) := by
  refine pull_hom_ext ιY (fun V x => ?_)
  rw [sh_comp_apply, sh_comp_apply, sh_comp_apply]
  rw [pullCompIso'_pbSecN ιY₂ ιY₁ ιY hY _ rfl]
  rw [pullMap_pbSecO (F := (pull ιY₁ Λ).obj ((push h Λ).obj G)) (G := (push h' Λ).obj ((pull ιX₁ Λ).obj G)) ιY₂
    ((bcCell Λ ιX₁ ιY₁ h h' w₁).app G)]
  rw [bcCell_pbSecN ιX₁ ιY₁ h h' w₁ G _ rfl]
  rw [natApplyP (F := (pull ιY₂ Λ).obj ((push h' Λ).obj ((pull ιX₁ Λ).obj G)))
    (G := (push h'' Λ).obj ((pull ιX₂ Λ).obj ((pull ιX₁ Λ).obj G))) ((bcCell Λ ιX₂ ιY₂ h' h'' w₂).app _)]
  rw [bcCell_pbSecN ιX₂ ιY₂ h' h'' w₂ ((pull ιX₁ Λ).obj G) _ rfl]
  rw [bcCell_pbSecN ιX ιY h h'' w G _ rfl]
  rw [push_map_app_apply (Q := (pull ιX Λ).obj G) (Q' := (pull ιX₂ Λ).obj ((pull ιX₁ Λ).obj G)) h'']
  rw [pullCompIso'_pbSecON (Λ := Λ) ιX₂ ιX₁ ιX hX _ rfl]
  rw [push_obj_map_apply, pbSec_restrict, ← mapO_comp_apply, ← mapO_comp_apply]
  exact map_congr_apply _ (site_paste ιX₁ ιY₁ h h' w₁ ιX₂ ιY₂ h'' w₂ ιX ιY hX hY w V) _

/-- **The base change cell of a composite square is the pasted cell** (up to `pullCompIso'`). -/
theorem sqHom_paste :
    SqHom (push h Λ) (push h'' Λ) (bcCell Λ ιX ιY h h'' w)
      (pasteβ (push h Λ) (push h' Λ) (push h'' Λ) (pull ιX₁ Λ) (pull ιY₁ Λ) (bcCell Λ ιX₁ ιY₁ h h' w₁)
        (pull ιX₂ Λ) (pull ιY₂ Λ) (bcCell Λ ιX₂ ιY₂ h' h'' w₂))
      (pullCompIso' Λ ιX₂ ιX₁ ιX hX).hom (pullCompIso' Λ ιY₂ ιY₁ ιY hY).hom :=
  sqHom_paste_of (push h Λ) (push h' Λ) (push h'' Λ) (pull ιX₁ Λ) (pull ιY₁ Λ)
    (bcCell Λ ιX₁ ιY₁ h h' w₁) (pull ιX₂ Λ) (pull ιY₂ Λ) (bcCell Λ ιX₂ ιY₂ h' h'' w₂)
    (bcCell Λ ιX ιY h h'' w) (pullCompIso' Λ ιX₂ ιX₁ ιX hX).hom (pullCompIso' Λ ιY₂ ιY₁ ιY hY).hom
    (fun G => paste_nested ιX₁ ιY₁ h h' w₁ ιX₂ ιY₂ h'' w₂ ιX ιY hX hY w G)

end Paste

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_SqNat =====
section

/-!
# S4-EtPBC-C1, part 28: squares of squares and the unit cell of a square

* **`sqNat`**: two ways of pasting a 2×2 block of squares with the same outer square give the same base change
  morphism, up to the `pullCompIso'` comparisons (both equal the composite square's `bcMorSq`, by
  `bcMorSq_paste` twice). This is the sheaf-level naturality of `bcMorSq` under morphisms of squares.
* `pullUnit_congr`, **`sqQ_unit`**: `sqQ` respects the unit sheaves; **`unitCell_sq`**: the cell condition
  `UnitCell` of `AbsBC` for the base change cell `bcCell` of any square, with `pullUnit` comparisons.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.EtMV

universe u

variable {Λ : Type u} [CommRing Λ]

section Block

end Block

section Unit

variable {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y) (h' : Xs ⟶ Ys)
  (w : h' ≫ ιY = ιX ≫ h)

variable (Λ) in
/-- **The unit cell of a square**: `UnitCell` (file `AbsBC`) for `bcCell` with the `pullUnit` comparisons. -/
theorem unitCell_sq :
    UnitCell (push h Λ) (push h' Λ) (pull ιX Λ) (pull ιY Λ) (bcCell Λ ιX ιY h h' w) (pullAdj h Λ)
      (pullUnit Λ h).symm (pullAdj h' Λ) (pullUnit Λ h').symm (pullUnit Λ ιY).hom (pullUnit Λ ιX).hom :=
  unitCell_of_mate _ _ _ _ _ _ _ _ _ _ _ (Mate.sqQ (Λ := Λ) ιX ιY h h' w).hom (bcCell_counit Λ ιX ιY h h' w)
    (sqQ_unit Λ ιX ιY h h' w)

end Unit

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

end GenNat

variable {Λ : Type u} [CommRing Λ]

namespace SqMor

variable {P₁ S₁ P₂ S₂ : Scheme.{u}} {g₁ : P₁ ⟶ S₁} {g₂ : P₂ ⟶ S₂} {s₁ : GeomPt S₁} {s₂ : GeomPt S₂}
  (m : SqMor g₁ g₂ s₁ s₂)

/-- **The morphism of fibres** `P₂_{s₂} ⟶ P₁_{s₁}`. -/
def fibMap : fib g₂ s₂ ⟶ fib g₁ s₁ := pullback.map g₂ s₂.pt g₁ s₁.pt m.eP m.σ m.eS m.wE m.wσ

theorem fibMap_ι : m.fibMap ≫ fibι g₁ s₁ = fibι g₂ s₂ ≫ m.eP :=
  pullback.lift_fst _ _ _

theorem fibMap_π : m.fibMap ≫ pullback.snd g₁ s₁.pt = pullback.snd g₂ s₂.pt ≫ m.σ :=
  pullback.lift_snd _ _ _

/-- The coefficient comparison `fibMap^* ι₁^* F ⟶ ι₂^* eP^* F`. -/
def κApp (F : EtSh Λ P₁) :
    (pull m.fibMap Λ).obj ((pull (fibι g₁ s₁) Λ).obj F) ⟶ (pull (fibι g₂ s₂) Λ).obj ((pull m.eP Λ).obj F) :=
  nestComp (pullCompIso' Λ m.fibMap (fibι g₁ s₁) (fibι g₂ s₂ ≫ m.eP) m.fibMap_ι.symm)
    (pullCompIso' Λ (fibι g₂ s₂) m.eP (fibι g₂ s₂ ≫ m.eP) rfl) F

/-- The point comparison `σ^* s₁^* G ⟶ s₂^* eS^* G`. -/
def θApp (G : EtSh Λ S₁) : (pull m.σ Λ).obj ((pull s₁.pt Λ).obj G) ⟶ (pull s₂.pt Λ).obj ((pull m.eS Λ).obj G) :=
  nestComp (pullCompIso' Λ m.σ s₁.pt (s₂.map m.eS).pt m.wσ) (pullCompIso' Λ s₂.pt m.eS (s₂.map m.eS).pt rfl) G

theorem wc : pullback.snd g₂ s₂.pt ≫ (s₂.map m.eS).pt = (fibι g₂ s₂ ≫ m.eP) ≫ g₁ := by
  change pullback.snd g₂ s₂.pt ≫ (s₂.pt ≫ m.eS) = _
  rw [← Category.assoc, ← pullback.condition, Category.assoc, m.wE, ← Category.assoc]

/-- **Pull-back on fibre cohomology** `H^q(P₁_{s₁}, ι₁^* F) ⟶ H^q(P₂_{s₂}, ι₂^* eP^* F)` along `m.fibMap`
(`(mk₀ pullUnit).comp (x.mapExactFunctor fibMap^*)` then the coefficient comparison `κApp`). -/
def fibH (F : EtSh Λ P₁) (q : ℕ) (x : H Λ ((pull (fibι g₁ s₁) Λ).obj F) q) :
    H Λ ((pull (fibι g₂ s₂) Λ).obj ((pull m.eP Λ).obj F)) q :=
  fibHGen (pull m.fibMap Λ) (pullUnit Λ m.fibMap).hom (m.κApp F) q x

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
variable {𝒳 𝒳₁ 𝒵 𝒳₂ : Type*} [Category 𝒳] [Category 𝒳₁] [Category 𝒵] [Category 𝒳₂]
theorem nestComp_tr {F : 𝒳 ⥤ 𝒳₂} {A₁ : 𝒳 ⥤ 𝒳₁} {A₂ : 𝒳₁ ⥤ 𝒳₂} {B₁ : 𝒳 ⥤ 𝒵} {B₂ : 𝒵 ⥤ 𝒳₂}
    (e₁ : F ≅ A₁ ⋙ A₂) (e₂ : F ≅ B₁ ⋙ B₂) (G : 𝒳) {U V : 𝒳₂} {S₂ : U ⟶ B₂.obj (B₁.obj G)}
    {St : U ⟶ F.obj G} {W₁ : U ⟶ V} {W₂ : V ⟶ A₂.obj (A₁.obj G)}
    (h2 : S₂ = St ≫ isoHomN e₂ G) (h1 : St ≫ isoHomN e₁ G = W₁ ≫ W₂) :
    S₂ = W₁ ≫ W₂ ≫ nestComp e₁ e₂ G := by
  rw [h2, ← reassoc_of% h1]
  simp only [isoHomN, nestComp, Iso.hom_inv_id_app_assoc]
end NestTr

section PullOfSec
variable {Λ : Type u} [CommRing Λ]

/-- Site identity: the point section of `s ≫ f` at `w` followed by the comparison is the point section of `s` at the
transported point. -/
theorem ptSec_map {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeomPt X) (W : Y.Etale) (w : (s.map f).point.fiber.obj W) :
    ptSec (s.map f) W w ≫ etPullCompHom' s.pt f (s.map f).pt rfl W =
      ptSec s ((etPull f).obj W) ((fiberMapIso f s).hom.app W w) := by
  apply etPull2_hom_ext s.pt f
  rw [etLeft_comp, Category.assoc, etPullCompHom'_fst, ptSec_left_fst, ← Category.assoc, ptSec_left_fst]
  conv_lhs => rw [← fiberMapIso_inv_hom f s W w]
  exact left_fiberMapIso_inv f s W _

/-- **(ii)** The section of a stalk of a pull-back, through `pullStalkIso`. -/
theorem stalkSec_pullStalk {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeomPt X) (G : EtSh Λ Y)
    (y : ((s.map f).stalkF Λ).obj G) :
    stalkSec s ((pull f Λ).obj G) ((isoInvN (pullStalkIso f Λ s) G).hom y) =
      stalkSec (s.map f) G y ≫ isoHomN (pullCompIso' Λ s.pt f (s.map f).pt rfl) G := by
  obtain ⟨j, z, rfl⟩ := exists_germ (s.map f) G.obj y
  have hb : (isoInvN (pullStalkIso f Λ s) G).hom (((s.map f).point.toPresheafFiber j.1 j.2 G.obj).hom z) =
      (s.point.toPresheafFiber ((etPull f).obj j.1) ((fiberMapIso f s).hom.app j.1 j.2)
        ((pull f Λ).obj G).obj).hom (pbSec f z) := by
    apply pullStalkIso_inj f s G
    rw [show pbSec f z = (((pullAdj f Λ).unit.app G).hom.app (op j.1)).hom z from rfl,
      pullStalkIso_germ (f := f) (s := s), fiberMapIso_inv_hom]
    change ((pullStalkIso f Λ s).inv.app G ≫ (pullStalkIso f Λ s).hom.app G).hom _ = _
    rw [Iso.inv_hom_id_app]
    rfl
  rw [hb, stalkSec_germ, stalkSec_germ, ofSec_comp]
  refine congrArg ofSec (Eq.trans (map_congr_apply _ ?_ _)
    (pullCompIso'_pbSecON s.pt f (s.map f).pt rfl (isoHomN (pullCompIso' Λ s.pt f (s.map f).pt rfl) G) rfl
      (ptSec (s.map f) j.1 j.2).op z).symm)
  rw [← op_comp, ptSec_map]

end PullOfSec

section Pt
variable {S : Scheme.{u}} (s t : GeomPt S) (σ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of s.Ω))
  (hσ : σ ≫ s.pt = t.pt)

theorem ptSec_ptMor (U : S.Etale) (a : s.point.fiber.obj U) :
    ptSec t U ((ptMor s t σ hσ).hom.app U a) ≫ etPullCompHom' σ s.pt t.pt hσ.symm U =
      (etIdPull σ).hom ≫ (etPull σ).map (ptSec s U a) := by
  apply etPull2_hom_ext σ s.pt
  rw [etLeft_comp, etLeft_comp, Category.assoc, etPullCompHom'_fst, ptSec_left_fst, Category.assoc,
    reassoc_of% (etPull_map_left_fst σ (ptSec s U a)), reassoc_of% (etIdPull_hom_left_fst σ), ptSec_left_fst]
  rfl

variable (Λ : Type u) [CommRing Λ]

/-- The stalk map `s^* ⟶ t^*` along `σ`. -/
def stalkMor : s.stalkF Λ ⟶ t.stalkF Λ :=
  GrothendieckTopology.Point.Hom.sheafFiber (A := ModuleCat.{u} Λ) (ptMor s t σ hσ)

theorem stalkMor_germ (H : EtSh Λ S) (U : S.Etale) (a : s.point.fiber.obj U) (z : H.obj.obj (op U)) :
    ((stalkMor s t σ hσ Λ).app H).hom ((s.point.toPresheafFiber U a H.obj).hom z) =
      (t.point.toPresheafFiber U ((ptMor s t σ hσ).hom.app U a) H.obj).hom z := by
  change (s.point.toPresheafFiber U a H.obj ≫ (ptMor s t σ hσ).presheafFiber.app H.obj).hom z = _
  rw [GrothendieckTopology.Point.Hom.presheafFiber_app,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc (hφ := _)]

/-- **(i)** The section of the transported stalk element along `σ`. -/
theorem stalkSec_stalkMor (H : EtSh Λ S) (y : (s.stalkF Λ).obj H) :
    stalkSec t H (((stalkMor s t σ hσ Λ).app H).hom y) ≫ isoHomN (pullCompIso' Λ σ s.pt t.pt hσ.symm) H =
      (pullUnit Λ σ).hom ≫ (pull σ Λ).map (stalkSec s H y) := by
  obtain ⟨j, z, rfl⟩ := exists_germ s H.obj y
  rw [stalkMor_germ, stalkSec_germ, stalkSec_germ, ofSec_comp, pull_ofSec,
    pullCompIso'_pbSecON σ s.pt t.pt hσ.symm (isoHomN (pullCompIso' Λ σ s.pt t.pt hσ.symm) H) rfl,
    pbSec_restrict, ← mapO_comp_apply]
  refine congrArg ofSec (map_congr_apply _ ?_ _)
  rw [← op_comp, ← op_comp, ptSec_ptMor]

end Pt

namespace SqMor

variable {Λ : Type u} [CommRing Λ]
variable {P₁ S₁ P₂ S₂ : Scheme.{u}} {g₁ : P₁ ⟶ S₁} {g₂ : P₂ ⟶ S₂} {s₁ : GeomPt S₁} {s₂ : GeomPt S₂}
  (m : SqMor g₁ g₂ s₁ s₂)

/-- **Stalk transport** `s₁^* G ⟶ s₂^* eS^* G` along a morphism of `(g, s)`-squares. -/
def stalkTr (G : EtSh Λ S₁) : (s₁.stalkF Λ).obj G ⟶ (s₂.stalkF Λ).obj ((pull m.eS Λ).obj G) :=
  (stalkMor s₁ (s₂.map m.eS) m.σ m.wσ.symm Λ).app G ≫ isoInvN (pullStalkIso m.eS Λ s₂) G

end SqMor

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C2_BcIso =====
section

/-! # S4-EtPBC-C2, part 3: the base change morphism is an isomorphism (generic, closed-point form)

For `g₁ : P ⟶ S` universally closed and `g : S' ⟶ S` with `S'` of finite type over a field, `bcMorSq` of the
base-change square `P ×_S S'` is an isomorphism as soon as `g₁` and `pullback.snd g₁ g` are `PBCGood` at the closed
points (`isIso_bcMorSq_bc`); proof: closed-point test, `SqMor.pbcEquiv_sqTr` for the square of `(g, s)`-squares with
`σ = 𝟙`, bijectivity of the stalk transport and of the fibre pull-back.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.C2

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.C1

universe u

section PtId
variable {S : Scheme.{u}} (s : GeomPt S) (h : 𝟙 (Spec (CommRingCat.of s.Ω)) ≫ s.pt = s.pt)

theorem stalkMor_id (Λ : Type u) [CommRing Λ] : stalkMor s s (𝟙 _) h Λ = 𝟙 _ := by
  unfold stalkMor
  rw [ptMor_id]
  exact GrothendieckTopology.Point.Hom.sheafFiber_id _

end PtId

section Gen

end Gen

section Sq
variable {Λ : Type u} [CommRing Λ] {P S S' : Scheme.{u}} (g₁ : P ⟶ S) (g : S' ⟶ S) (s₂ : GeomPt S')

instance isIso_bcSq_fibMap : IsIso (bcSq g₁ g s₂).fibMap := by
  have : (bcSq g₁ g s₂).fibMap = (pullbackLeftPullbackSndIso g₁ g s₂.pt).hom := by
    apply pullback.hom_ext
    · rw [SqMor.fibMap_ι]; exact (pullbackLeftPullbackSndIso_hom_fst g₁ g s₂.pt).symm
    · rw [SqMor.fibMap_π]
      exact (Category.comp_id _).trans (pullbackLeftPullbackSndIso_hom_snd g₁ g s₂.pt).symm
  exact ⟨⟨(pullbackLeftPullbackSndIso g₁ g s₂.pt).inv,
    by rw [this]; exact (pullbackLeftPullbackSndIso g₁ g s₂.pt).hom_inv_id,
    by rw [this]; exact (pullbackLeftPullbackSndIso g₁ g s₂.pt).inv_hom_id⟩⟩

theorem bcSq_stalkTr_bijective (G : EtSh Λ S) : Function.Bijective ((bcSq g₁ g s₂).stalkTr G).hom := by
  have : IsIso ((bcSq g₁ g s₂).stalkTr G) := by
    unfold SqMor.stalkTr isoInvN
    have h0 : stalkMor (GeomPt.map g s₂) (GeomPt.map (bcSq g₁ g s₂).eS s₂) (bcSq g₁ g s₂).σ
        (bcSq g₁ g s₂).wσ.symm Λ = 𝟙 _ := stalkMor_id (s₂.map g) _ Λ
    rw [h0]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

end Sq

section Main

end Main

end RamanujanPetersson.EtPBC.C2

end

end

-- ===== S4.Def_RP_EtPBC_C2_Tow =====
section

/-! # S4-EtPBC-C2, part 2: tower maps (iterated `P^1`-bundles up to isomorphism)

`IsTower K gS h` for `h : Y ⟶ S`: generated by `qV K gS : P^1_S ⟶ S`, `qV K (h ≫ gS) ≫ h` and precomposition
with isomorphisms. Tower maps are proper, have Noetherian source over a Noetherian `S`, are `PBCGood` at every
`K`-rational geometric point (`IsTower.good`), are stable under base change (`IsTower.baseChange`) and under
composition of towers (`IsTower.comp`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C2

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.Z3

section Def
variable (K : Type) [Field K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))

variable {K gS}

theorem IsTower.isNoetherian [IsNoetherian S] {Y : Scheme.{0}} {h : Y ⟶ S} (hh : IsTower K gS h) :
    IsNoetherian Y := by
  induction hh with
  | base => exact (inferInstance : IsNoetherian (PV K gS))
  | step h _ ih => exact (inferInstance : IsNoetherian (PV K (h ≫ gS)))
  | @iso Y' Y e _ h _ ih =>
    have : IsLocallyNoetherian Y' := isLocallyNoetherian_of_isOpenImmersion e
    have : CompactSpace Y' := (Scheme.homeoOfIso (asIso e)).symm.compactSpace
    exact { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

end Def

section Good

end Good

section BC

end BC

section Shapes

end Shapes

end RamanujanPetersson.EtPBC.C2

end

end


