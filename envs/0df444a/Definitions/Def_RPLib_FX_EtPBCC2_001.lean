-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC2_001
-- name    : RPLib_FX_EtPBCC2_001
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-27T00:52:53.270526+00:00
-- url     : https://prove2.me/theorems/bb1d3e0d-78a1-5eb0-a5cb-e3200e773fcc
-- title:
--   Sheaf-level proper base change with compact supports, library file 001
-- statement:
--   File 001 of the library for sheaf-level proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_C1_Gen`: S4-EtPBC-C1, part 2: the generic degree-`q` base change morphism
--   * `S4.Def_RP_EtPBC_C1_Mor`: S4-EtPBC-C1, part 3: the base change morphism `g^* R^q f_! F ⟶ R^q f'_! g'^* F`
--   * `S4.Def_RP_EtPBC_C1_AbsBC`: S4-EtPBC-C1, part 27: `absRelR` under base change (generic)
--   * `S4.Def_RP_EtPBC_C1_Paste`: S4-EtPBC-C1, part 21: pasting of base change morphisms (generic)
--   * `S4.Def_RP_EtPBC_C1_TrG`: S4-EtPBC-C1, part 22: base change morphisms under morphisms of squares (generic)
--   * `S4.Def_RP_EtPBC_C1_PasteC`: S4-EtPBC-C1, part 24: pasting of base change morphisms for composite squares (BC-MOR (1c))
--   * `S4.Def_RP_EtPBC_C1_SqNat`: S4-EtPBC-C1, part 28: squares of squares and the unit cell of a square
--   * `S4.Def_RP_EtPBC_C1_PbcSqA`: S4-EtPBC-C1, part 29a: morphisms of `(g, s)`-squares, the fibre map and the pastings
--   * `S4.Def_RP_EtPBC_C1_StkTr`: S4-EtPBC-C1, part 29d: stalk transport along a morphism of (g, s)-squares
--   * `S4.Def_RP_EtPBC_C2_BcIso`: S4-EtPBC-C2, part 3: the base change morphism is an isomorphism (generic, closed-point form)
--   * `S4.Def_RP_EtPBC_C2_GoodIso`: S4-EtPBC-C2, part 1: `PBCGood` is invariant under isomorphisms of the source
--   * `S4.Def_RP_EtPBC_C2_Tow`: S4-EtPBC-C2, part 2: tower maps (iterated `P^1`-bundles up to isomorphism)
--
--   **Formalization note.** One file of a library formalizing sheaf-level proper base change for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ a tower of projective-line bundles over a noetherian $S$ of finite type over an algebraically closed field), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and any $g : S' \to S$ of finite type, the base change morphism $g^* R^q f_! F \to R^q f'_! (g_X^* F)$ is an isomorphism for every sheaf $F$ of $\Lambda$-modules ($\Lambda$ finite, $\ell$-power torsion). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`), for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`) and for the stalks of $R^q f_!$ (`RPLib_FX_EtPBCC1_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_010

/-!
# Sheaf-level proper base change with compact supports, library file 001

Declarations of the formalization of sheaf-level proper base change for compactly supported étale
cohomology: for a compactified X ⟶ S whose proper part is an iterated projective-line bundle (a tower)
and any g : S' ⟶ S of finite type, the base change morphism g^* R^q f_! F ⟶ R^q f'_! (g_X^* F) is an
isomorphism, re-hosted declaration by declaration from the library modules below, on top of the proper
base change libraries RPLib_FX_EtPBC, RPLib_FX_EtPBCB and RPLib_FX_EtPBCC1. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_C1_Gen`: S4-EtPBC-C1, part 2: the generic degree-`q` base change morphism
* `S4.Def_RP_EtPBC_C1_Mor`: S4-EtPBC-C1, part 3: the base change morphism `g^* R^q f_! F ⟶ R^q f'_! g'^* F`
* `S4.Def_RP_EtPBC_C1_AbsBC`: S4-EtPBC-C1, part 27: `absRelR` under base change (generic)
* `S4.Def_RP_EtPBC_C1_Paste`: S4-EtPBC-C1, part 21: pasting of base change morphisms (generic)
* `S4.Def_RP_EtPBC_C1_TrG`: S4-EtPBC-C1, part 22: base change morphisms under morphisms of squares (generic)
* `S4.Def_RP_EtPBC_C1_PasteC`: S4-EtPBC-C1, part 24: pasting of base change morphisms for composite squares (BC-MOR (1c))
* `S4.Def_RP_EtPBC_C1_SqNat`: S4-EtPBC-C1, part 28: squares of squares and the unit cell of a square
* `S4.Def_RP_EtPBC_C1_PbcSqA`: S4-EtPBC-C1, part 29a: morphisms of `(g, s)`-squares, the fibre map and the pastings
* `S4.Def_RP_EtPBC_C1_StkTr`: S4-EtPBC-C1, part 29d: stalk transport along a morphism of (g, s)-squares
* `S4.Def_RP_EtPBC_C2_BcIso`: S4-EtPBC-C2, part 3: the base change morphism is an isomorphism (generic, closed-point form)
* `S4.Def_RP_EtPBC_C2_GoodIso`: S4-EtPBC-C2, part 1: `PBCGood` is invariant under isomorphisms of the source
* `S4.Def_RP_EtPBC_C2_Tow`: S4-EtPBC-C2, part 2: tower maps (iterated `P^1`-bundles up to isomorphism)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_C1_Gen =====
section

/-!
# S4-EtPBC-C1, part 2: the generic degree-`q` base change morphism

`R : C ⥤ D`, `R' : C' ⥤ D'` additive, `Lc : C ⥤ C'`, `Ld : D ⥤ D'` exact, `β : R ⋙ Ld ⟶ Lc ⋙ R'`.
`bcMorRes q I J : Ld (R^q X) ⟶ R'^q (Lc X)` for injective resolutions `I` of `X` and `J` of `Lc X`:
`Ld H^q(R I) ≅ H^q(Ld R I) ⟶ H^q(R' Lc I) ⟶ H^q(R' J)` (`β` degreewise, then `R'` of the lift `descR` of
`Lc I` into `J`). **`bcMorRes_natural`** (naturality in `X`, any resolutions), `bcMorRes_indep`, `bcMorGen`.
-/

set_option autoImplicit false

open CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] {D' : Type u₄} [Category.{v₄} D'] [Abelian D']

section HMI

end HMI

variable (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive]
  (Lc : C ⥤ C') [Lc.Additive] [Lc.PreservesHomology] [Lc.PreservesMonomorphisms]
  (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology]
  (β : R ⋙ Ld ⟶ Lc ⋙ R')

variable [HasInjectiveResolutions C] [HasInjectiveResolutions C']

/-- `bcMorGen` as a natural transformation `R^q ⋙ Ld ⟶ Lc ⋙ R'^q`. -/
def bcNat (q : ℕ) : R.rightDerived q ⋙ Ld ⟶ Lc ⋙ R'.rightDerived q where
  app X := bcMorGen R R' Lc Ld β q X
  naturality _ _ f := bcMorGen_natural R R' Lc Ld β q f

end RamanujanPetersson.EtPBC.C1

end

end

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

/-- `𝟙 ≫ x ≫ 𝟙 ≫ y ≫ 𝟙 = x ≫ y` (generic; used term-mode by `bcMor_eq`). -/
theorem idSand {𝒞 : Type*} [Category 𝒞] {A B D : 𝒞} (x : A ⟶ B) (y : B ⟶ D) :
    𝟙 A ≫ x ≫ 𝟙 B ≫ y ≫ 𝟙 D = x ≫ y := by
  rw [Category.id_comp, Category.id_comp, Category.comp_id]

section It

variable {X B B' : Scheme.{u}} {f : X ⟶ B} (c : Cpt f) (g : B' ⟶ B)

/-- **The base change morphism** as a natural transformation `R^q f_! ⋙ g^* ⟶ gX^* ⋙ R^q f'_!`. -/
def bcNatMor (q : ℕ) : c.Rshriek Λ q ⋙ pull g Λ ⟶ pull (itgX c g) Λ ⋙ (itCpt c g).Rshriek Λ q :=
  (Functor.associator (c.ext Λ) ((push c.fbar Λ).rightDerived q) (pull g Λ)).hom ≫
    Functor.whiskerLeft (c.ext Λ) (bcNat (push c.fbar Λ) (push (pullback.snd c.fbar g) Λ) (pull (itgP c g) Λ)
      (pull g Λ) (bcCell Λ (itgP c g) g c.fbar (pullback.snd c.fbar g) pullback.condition.symm) q) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (itExtNat Λ c g).hom ((push (pullback.snd c.fbar g) Λ).rightDerived q) ≫
    (Functor.associator _ _ _).hom

/-- **The base change morphism** `g^* R^q f_! F ⟶ R^q f'_! gX^* F` (`f' = itf c g`, compactified by `itCpt`). -/
def bcMor (q : ℕ) (F : EtSh Λ X) :
    (pull g Λ).obj ((c.Rshriek Λ q).obj F) ⟶ ((itCpt c g).Rshriek Λ q).obj ((pull (itgX c g) Λ).obj F) :=
  (bcNatMor Λ c g q).app F

/-- **Naturality of `bcMor` in `F`.** -/
@[reassoc]
theorem bcMor_natural (q : ℕ) {F F' : EtSh Λ X} (φ : F ⟶ F') :
    (pull g Λ).map ((c.Rshriek Λ q).map φ) ≫ bcMor Λ c g q F' =
      bcMor Λ c g q F ≫ ((itCpt c g).Rshriek Λ q).map ((pull (itgX c g) Λ).map φ) :=
  (bcNatMor Λ c g q).naturality φ

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

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {C' : Type*} [Category C'] [Abelian C'] {D' : Type*} [Category D'] [Abelian D']
  (R : C ⥤ D) (R' : C' ⥤ D') (Lc : C ⥤ C') (Ld : D ⥤ D') (β : R ⋙ Ld ⟶ Lc ⋙ R')
  {L₁ : D ⥤ C} (adj₁ : L₁ ⊣ R) {A₁ : D} {X₁ : C} (e₁ : L₁.obj A₁ ≅ X₁)
  {L₂ : D' ⥤ C'} (adj₂ : L₂ ⊣ R') {A₂ : D'} {X₂ : C'} (e₂ : L₂.obj A₂ ≅ X₂)
  (a : A₂ ⟶ Ld.obj A₁) (u : X₂ ⟶ Lc.obj X₁)

/-- **The unit cell condition**: `a ≫ Ld(adj₁-transpose of e₁) ≫ β = adj₂-transpose of (e₂ ≫ u)`. -/
def UnitCell : Prop :=
  a ≫ Ld.map (adj₁.homEquiv _ _ e₁.hom) ≫ β.app X₁ = adj₂.homEquiv _ _ (e₂.hom ≫ u)

theorem unitCell_comp (h : UnitCell R R' Lc Ld β adj₁ e₁ adj₂ e₂ a u) {Z : C} (f : X₁ ⟶ Z) :
    (a ≫ Ld.map (adj₁.homEquiv _ _ (e₁.hom ≫ f))) ≫ β.app Z = adj₂.homEquiv _ _ (e₂.hom ≫ u ≫ Lc.map f) := by
  have hn := β.naturality f
  simp only [Functor.comp_map] at hn
  calc (a ≫ Ld.map (adj₁.homEquiv _ _ (e₁.hom ≫ f))) ≫ β.app Z
      = (a ≫ Ld.map (adj₁.homEquiv _ _ e₁.hom) ≫ β.app X₁) ≫ R'.map (Lc.map f) := by
        rw [Adjunction.homEquiv_naturality_right, Ld.map_comp]
        simp only [Category.assoc]
        rw [hn]
    _ = adj₂.homEquiv _ _ (e₂.hom ≫ u) ≫ R'.map (Lc.map f) := by rw [h]
    _ = adj₂.homEquiv _ _ (e₂.hom ≫ u ≫ Lc.map f) := by
        rw [← Adjunction.homEquiv_naturality_right, Category.assoc]

/-- **`UnitCell` for a mate**: if `β` has the counit property of the mate of `γ : Ld ⋙ L₂ ⟶ L₁ ⋙ Lc`, the cell
condition is the transposed identity `L₂ a ≫ γ ≫ Lc e₁ = e₂ ≫ u`. -/
theorem unitCell_of_mate (γ : Ld ⋙ L₂ ⟶ L₁ ⋙ Lc)
    (hβ : ∀ G : C, L₂.map (β.app G) ≫ adj₂.counit.app (Lc.obj G) = γ.app (R.obj G) ≫ Lc.map (adj₁.counit.app G))
    (h : L₂.map a ≫ γ.app A₁ ≫ Lc.map e₁.hom = e₂.hom ≫ u) :
    UnitCell R R' Lc Ld β adj₁ e₁ adj₂ e₂ a u := by
  unfold UnitCell
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, hβ]
  have hn := γ.naturality (adj₁.homEquiv _ _ e₁.hom)
  simp only [Functor.comp_map] at hn
  have hc : L₁.map (adj₁.homEquiv _ _ e₁.hom) ≫ adj₁.counit.app X₁ = e₁.hom := by
    simp [Adjunction.homEquiv_unit]
  rw [← Category.assoc (L₂.map (Ld.map _)), hn, Category.assoc, ← Lc.map_comp, hc, h]

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

omit [HasInjectiveResolutions C] [HasInjectiveResolutions C'] in
/-- `addEquiv₀` of a base-changed degree-`0` class. -/
theorem addEquiv₀_bc {Y : C} (x : Abelian.Ext.{w} X₁ Y 0) :
    Abelian.Ext.addEquiv₀ ((Abelian.Ext.mk₀ u).comp (x.mapExactFunctor Lc) (zero_add 0)) =
      u ≫ Lc.map (Abelian.Ext.addEquiv₀ x) := by
  conv_lhs => rw [← Abelian.Ext.mk₀_addEquiv₀_apply x]
  rw [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  exact Abelian.Ext.addEquiv₀.apply_symm_apply _

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

variable (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology] (Ld' : D' ⥤ D'') [Ld'.Additive]
  [Ld'.PreservesHomology] [(Ld ⋙ Ld').PreservesHomology]

/-- `homologyMapIso` of a composite functor. -/
theorem homologyMapIso_inv_comp (K : CochainComplex D ℕ) (q : ℕ) :
    (EtLeray.homologyMapIso (Ld ⋙ Ld') K q).inv =
      Ld'.map (EtLeray.homologyMapIso Ld K q).inv ≫
        (EtLeray.homologyMapIso Ld' ((Ld.mapHomologicalComplex _).obj K) q).inv := by
  rw [← cancel_epi ((Ld ⋙ Ld').map (K.homologyπ q))]
  have h0 : K.liftCycles (K.iCycles q) (q + 1) (CochainComplex.next ℕ q) (K.iCycles_d q (q + 1)) = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles q)]
    simp
  have e1 := map_liftCycles_homologyπ_cx (Ld ⋙ Ld') K q (q + 1) (CochainComplex.next ℕ q) (K.iCycles q)
    (K.iCycles_d q (q + 1)) (by
      rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp, K.iCycles_d, Functor.map_zero])
  have e2 := map_liftCycles_homologyπ_cx Ld K q (q + 1) (CochainComplex.next ℕ q) (K.iCycles q)
    (K.iCycles_d q (q + 1)) (by
      rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp, K.iCycles_d, Functor.map_zero])
  have e3 := map_liftCycles_homologyπ_cx Ld' ((Ld.mapHomologicalComplex _).obj K) q (q + 1)
    (CochainComplex.next ℕ q) (Ld.map (K.iCycles q)) (by
      rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp, K.iCycles_d, Functor.map_zero]) (by
      rw [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp,
        ← Functor.map_comp, K.iCycles_d, Functor.map_zero, Functor.map_zero])
  rw [h0, Category.id_comp] at e1 e2
  rw [e1]
  show _ = Ld'.map (Ld.map (K.homologyπ q)) ≫ _
  rw [← Ld'.map_comp_assoc, e2, e3]
  rfl

end HMI

variable (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive] (R'' : C'' ⥤ D'') [R''.Additive]
  (Lc : C ⥤ C') [Lc.Additive] [Lc.PreservesHomology] [Lc.PreservesMonomorphisms]
  (Ld : D ⥤ D') [Ld.Additive] [Ld.PreservesHomology] (β : R ⋙ Ld ⟶ Lc ⋙ R')
  (Lc' : C' ⥤ C'') [Lc'.Additive] [Lc'.PreservesHomology] [Lc'.PreservesMonomorphisms]
  (Ld' : D' ⥤ D'') [Ld'.Additive] [Ld'.PreservesHomology] (β' : R' ⋙ Ld' ⟶ Lc' ⋙ R'')

/-- **The pasted square** `R ⋙ (Ld ⋙ Ld') ⟶ (Lc ⋙ Lc') ⋙ R''`: `Ld' β ≫ β' Lc`. -/
def pasteβ : R ⋙ (Ld ⋙ Ld') ⟶ (Lc ⋙ Lc') ⋙ R'' where
  app X := Ld'.map (β.app X) ≫ β'.app (Lc.obj X)
  naturality X Y f := by
    have h1 := β.naturality f
    have h2 := β'.naturality (Lc.map f)
    simp only [Functor.comp_map] at h1 h2 ⊢
    rw [← Ld'.map_comp_assoc, h1, Ld'.map_comp, Category.assoc, h2, Category.assoc]

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

variable {Ld Ld₂ : D ⥤ D'} [Ld.Additive] [Ld.PreservesHomology] [Ld₂.Additive] [Ld₂.PreservesHomology]
  (θd : Ld ⟶ Ld₂)

/-- `homologyMapIso` is natural in the functor. -/
theorem homologyMapIso_inv_natTrans (K : CochainComplex D ℕ) (q : ℕ) :
    θd.app (K.homology q) ≫ (EtLeray.homologyMapIso Ld₂ K q).inv =
      (EtLeray.homologyMapIso Ld K q).inv ≫
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex θd _).app K) q := by
  rw [← cancel_epi (Ld.map (K.homologyπ q))]
  have h0 : K.liftCycles (K.iCycles q) (q + 1) (CochainComplex.next ℕ q) (K.iCycles_d q (q + 1)) = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles q)]
    simp
  have e1 := map_liftCycles_homologyπ_cx Ld K q (q + 1) (CochainComplex.next ℕ q) (K.iCycles q)
    (K.iCycles_d q (q + 1)) (by
      rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp, K.iCycles_d, Functor.map_zero])
  have e2 := map_liftCycles_homologyπ_cx Ld₂ K q (q + 1) (CochainComplex.next ℕ q) (K.iCycles q)
    (K.iCycles_d q (q + 1)) (by
      rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp, K.iCycles_d, Functor.map_zero])
  rw [h0, Category.id_comp] at e1 e2
  rw [θd.naturality_assoc, e2, reassoc_of% e1, liftCycles_homologyπ_homologyMap _ q (q + 1)
    (CochainComplex.next ℕ q) _ _ (by
      rw [NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_obj_d, Category.assoc,
        ← θd.naturality, ← Category.assoc, ← Functor.map_comp, K.iCycles_d, Functor.map_zero, zero_comp]),
    HomologicalComplex.comp_liftCycles_assoc]
  simp only [NatTrans.mapHomologicalComplex_app_f, NatTrans.naturality]

end HMI

variable (R : C ⥤ D) [R.Additive] (R' : C' ⥤ D') [R'.Additive]
  {Lc Lc₂ : C ⥤ C'} [Lc.Additive] [Lc.PreservesHomology] [Lc.PreservesMonomorphisms]
  [Lc₂.Additive] [Lc₂.PreservesHomology] [Lc₂.PreservesMonomorphisms]
  {Ld Ld₂ : D ⥤ D'} [Ld.Additive] [Ld.PreservesHomology] [Ld₂.Additive] [Ld₂.PreservesHomology]
  (β : R ⋙ Ld ⟶ Lc ⋙ R') (β₂ : R ⋙ Ld₂ ⟶ Lc₂ ⋙ R') (θc : Lc ⟶ Lc₂) (θd : Ld ⟶ Ld₂)

/-- A morphism of squares: `θd_{R X} ≫ β₂ X = β X ≫ R' (θc X)`. -/
def SqHom : Prop := ∀ X : C, θd.app (R.obj X) ≫ β₂.app X = β.app X ≫ R'.map (θc.app X)

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

theorem etLeft_comp {A : Scheme.{u}} {P Q R : A.Etale} (x : P ⟶ Q) (y : Q ⟶ R) :
    (x ≫ y).left = x.left ≫ y.left := rfl

theorem etPull3_hom_ext {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) {Z : A.Etale}
    {T : D.Etale} {m₁ m₂ : Z ⟶ (etPull a).obj ((etPull b).obj ((etPull c).obj T))}
    (H : m₁.left ≫ pullback.fst _ a ≫ pullback.fst _ b ≫ pullback.fst T.hom c =
      m₂.left ≫ pullback.fst _ a ≫ pullback.fst _ b ≫ pullback.fst T.hom c) : m₁ = m₂ := by
  have k2 : ∀ m : Z ⟶ (etPull a).obj ((etPull b).obj ((etPull c).obj T)),
      m.left ≫ pullback.fst _ a ≫ pullback.snd (((etPull c).obj T).hom) b = Z.hom ≫ a := fun m =>
    (whisker_eq _ pullback.condition).trans (MorphismProperty.Over.w_assoc m _)
  have k3 : ∀ m : Z ⟶ (etPull a).obj ((etPull b).obj ((etPull c).obj T)),
      m.left ≫ pullback.fst _ a ≫ pullback.fst _ b ≫ pullback.snd T.hom c = Z.hom ≫ a ≫ b := fun m => by
    have e1 : pullback.fst (((etPull c).obj T).hom) b ≫ pullback.snd T.hom c =
        pullback.snd (((etPull c).obj T).hom) b ≫ b := pullback.condition
    rw [e1]
    exact (reassoc_of% (k2 m)) b
  refine etPull_hom_ext a (pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_)
  · simpa only [Category.assoc] using H
  · simp only [Category.assoc]
    exact (k3 m₁).trans (k3 m₂).symm
  · simp only [Category.assoc]
    exact (k2 m₁).trans (k2 m₂).symm

/-- Nested-typed `(gf)⁻¹ V ⟶ g⁻¹ f⁻¹ V` for a flexible composite `gf = g ≫ f`. -/
def etPullCompHom' {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (gf : A ⟶ C) (e : gf = g ≫ f) (V : C.Etale) :
    (etPull gf).obj V ⟶ (etPull g).obj ((etPull f).obj V) :=
  etPullCongr e V ≫ (etPullCompIso g f).hom.app V

theorem etPullCompHom'_fst_r {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (gf : A ⟶ C) (e : gf = g ≫ f)
    (V : C.Etale) {W : Scheme.{u}} (k : V.left ⟶ W) :
    (etPullCompHom' g f gf e V).left ≫ pullback.fst ((etPull f).obj V).hom g ≫ pullback.fst V.hom f ≫ k =
      pullback.fst V.hom gf ≫ k := by
  simp only [etPullCompHom', etLeft_comp, Category.assoc, etPullCompIso_hom_fst_fst_r, etPullCongr_left_fst_assoc]

theorem etPullCompHom'_fst {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (gf : A ⟶ C) (e : gf = g ≫ f)
    (V : C.Etale) :
    (etPullCompHom' g f gf e V).left ≫ pullback.fst ((etPull f).obj V).hom g ≫ pullback.fst V.hom f =
      pullback.fst V.hom gf := by
  simp only [etPullCompHom', etLeft_comp, Category.assoc, etPullCompIso_hom_fst_fst, etPullCongr_left_fst]

/-- Nested-typed canonical map `h'⁻¹ ιY⁻¹ V ⟶ ιX⁻¹ h⁻¹ V` of a commutative square. -/
def bcSite {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y) (h' : Xs ⟶ Ys)
    (w : h' ≫ ιY = ιX ≫ h) (V : Y.Etale) : (etPull h').obj ((etPull ιY).obj V) ⟶ (etPull ιX).obj ((etPull h).obj V) :=
  (etPullCompIso h' ιY).inv.app V ≫ etPullCongr w V ≫ (etPullCompIso ιX h).hom.app V

theorem bcSite_fst_r {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y) (h' : Xs ⟶ Ys)
    (w : h' ≫ ιY = ιX ≫ h) (V : Y.Etale) {W : Scheme.{u}} (k : V.left ⟶ W) :
    (bcSite ιX ιY h h' w V).left ≫ pullback.fst ((etPull h).obj V).hom ιX ≫ pullback.fst V.hom h ≫ k =
      pullback.fst ((etPull ιY).obj V).hom h' ≫ pullback.fst V.hom ιY ≫ k := by
  simp only [bcSite, etLeft_comp, Category.assoc, etPullCompIso_hom_fst_fst_r, etPullCongr_left_fst_assoc,
    etPullCompIso_inv_fst_r]

theorem bcSite_fst {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y) (h' : Xs ⟶ Ys)
    (w : h' ≫ ιY = ιX ≫ h) (V : Y.Etale) :
    (bcSite ιX ιY h h' w V).left ≫ pullback.fst ((etPull h).obj V).hom ιX ≫ pullback.fst V.hom h =
      pullback.fst ((etPull ιY).obj V).hom h' ≫ pullback.fst V.hom ιY := by
  simp only [bcSite, etLeft_comp, Category.assoc, etPullCompIso_hom_fst_fst, etPullCongr_left_fst,
    etPullCompIso_inv_fst]

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

/-- `SqHom` for a pasted square from a pointwise identity whose composites run through the nested objects
`Ld' (Ld (R W))`, `Ld' (R' (Lc W))`, `R'' (Lc' (Lc W))` (keeps concrete instances kernel-cheap). -/
theorem sqHom_paste_of
    (H : ∀ W : C,
      CategoryStruct.comp (X := Ld₀.obj (R.obj W)) (Y := Ld'.obj (Ld.obj (R.obj W)))
          (Z := R''.obj (Lc'.obj (Lc.obj W))) (θd.app (R.obj W))
          (CategoryStruct.comp (X := Ld'.obj (Ld.obj (R.obj W))) (Y := Ld'.obj (R'.obj (Lc.obj W)))
            (Z := R''.obj (Lc'.obj (Lc.obj W)))
            (Ld'.map (X := Ld.obj (R.obj W)) (Y := R'.obj (Lc.obj W)) (β.app W)) (β'.app (Lc.obj W))) =
        CategoryStruct.comp (X := Ld₀.obj (R.obj W)) (Y := R''.obj (Lc₀.obj W))
          (Z := R''.obj (Lc'.obj (Lc.obj W)))
          (β₀.app W) (R''.map (X := Lc₀.obj W) (Y := Lc'.obj (Lc.obj W)) (θc.app W))) :
    SqHom R R'' β₀ (pasteβ R R' R'' Lc Ld β Lc' Ld' β') θc θd :=
  fun W => H W

end Gen

variable {Λ : Type u} [CommRing Λ]

theorem pull_hom_ext {X Y : Scheme.{u}} (k : X ⟶ Y) {F : EtSh Λ Y} {T : EtSh Λ X}
    {φ ψ : (pull k Λ).obj F ⟶ T}
    (H : ∀ (V : Y.Etale) (x : F.obj.obj (op V)),
      (φ.hom.app (op ((etPull k).obj V))).hom (pbSec k x) =
        (ψ.hom.app (op ((etPull k).obj V))).hom (pbSec k x)) : φ = ψ := by
  apply ((pullAdj k Λ).homEquiv F T).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V x
  exact H V.unop x

theorem push_obj_map_apply {A B : Scheme.{u}} (f : A ⟶ B) (Q : EtSh Λ A) {U U' : B.Etale} (r : U' ⟶ U)
    (s : ((push f Λ).obj Q).obj.obj (op U)) :
    (((push f Λ).obj Q).obj.map r.op).hom s = (Q.obj.map ((etPull f).map r).op).hom s := rfl

theorem push_map_app_apply {A B : Scheme.{u}} (f : A ⟶ B) {Q Q' : EtSh Λ A} (φ : Q ⟶ Q') (U : B.Etale)
    (s : ((push f Λ).obj Q).obj.obj (op U)) :
    (((push f Λ).map φ).hom.app (op U)).hom s = (φ.hom.app (op ((etPull f).obj U))).hom s := rfl

theorem natApplyP {Z : Scheme.{u}} {F G : EtSh Λ Z} (τ : F ⟶ G) {U U' : Z.Etaleᵒᵖ} (f : U ⟶ U')
    (x : F.obj.obj U) : (τ.hom.app U').hom ((F.obj.map f).hom x) = (G.obj.map f).hom ((τ.hom.app U).hom x) :=
  congrArg (fun m => m.hom x) (τ.hom.naturality f)

variable (Λ) in
/-- `pull` along a flexible composite `gf = g ≫ f`: `gf^* ≅ f^* ⋙ g^*`. -/
def pullCompIso' {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (gf : A ⟶ C) (e : gf = g ≫ f) :
    pull gf Λ ≅ pull f Λ ⋙ pull g Λ :=
  pullCongr Λ e ≪≫ pullCompIso Λ g f

theorem pullCompIso'_pbSecO {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (gf : A ⟶ C) (e : gf = g ≫ f)
    {F : EtSh Λ C} {V : C.Etale} {Z : A.Etale} (a : op ((etPull gf).obj V) ⟶ op Z) (x : F.obj.obj (op V)) :
    (((pullCompIso' Λ g f gf e).hom.app F).hom.app (op Z)).hom
        ((((pull gf Λ).obj F).obj.map a).hom (pbSec gf x)) =
      ((((pull g Λ).obj ((pull f Λ).obj F)).obj.map
        (((etPullCompIso g f).hom.app V).op ≫ (etPullCongr e V).op ≫ a)).hom (pbSec g (pbSec f x))) := by
  rw [pullCompIso', Iso.trans_hom, NatTrans.comp_app, sh_comp_apply, pullCongr_pbSecO]
  exact pullCompHom_pbSecO g f _ x

theorem pullCompIso'_pbSec {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (gf : A ⟶ C) (e : gf = g ≫ f)
    {F : EtSh Λ C} {V : C.Etale} (x : F.obj.obj (op V)) :
    (((pullCompIso' Λ g f gf e).hom.app F).hom.app (op ((etPull gf).obj V))).hom (pbSec gf x) =
      ((((pull g Λ).obj ((pull f Λ).obj F)).obj.map
        (((etPullCompIso g f).hom.app V).op ≫ (etPullCongr e V).op)).hom (pbSec g (pbSec f x))) := by
  have h0 := pullCompIso'_pbSecO g f gf e (F := F) (𝟙 _) x
  rwa [map_id_apply', Category.comp_id] at h0

theorem pullCompIso'_pbSecN {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (gf : A ⟶ C) (e : gf = g ≫ f)
    {F : EtSh Λ C} {V : C.Etale} (φ : (pull gf Λ).obj F ⟶ (pull g Λ).obj ((pull f Λ).obj F))
    (hφ : φ = (pullCompIso' Λ g f gf e).hom.app F) (x : F.obj.obj (op V)) :
    (φ.hom.app (op ((etPull gf).obj V))).hom (pbSec gf x) =
      ((((pull g Λ).obj ((pull f Λ).obj F)).obj.map (etPullCompHom' g f gf e V).op).hom (pbSec g (pbSec f x))) := by
  subst hφ
  refine (pullCompIso'_pbSec g f gf e x).trans (map_congr_apply _ ?_ _)
  rw [etPullCompHom', op_comp]

theorem pullCompIso'_pbSecON {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (gf : A ⟶ C) (e : gf = g ≫ f)
    {F : EtSh Λ C} {V : C.Etale} {Z : A.Etale} (φ : (pull gf Λ).obj F ⟶ (pull g Λ).obj ((pull f Λ).obj F))
    (hφ : φ = (pullCompIso' Λ g f gf e).hom.app F) (a : op ((etPull gf).obj V) ⟶ op Z) (x : F.obj.obj (op V)) :
    (φ.hom.app (op Z)).hom ((((pull gf Λ).obj F).obj.map a).hom (pbSec gf x)) =
      ((((pull g Λ).obj ((pull f Λ).obj F)).obj.map
        ((etPullCompHom' g f gf e V).op ≫ a)).hom (pbSec g (pbSec f x))) := by
  subst hφ
  refine (pullCompIso'_pbSecO g f gf e a x).trans (map_congr_apply _ ?_ _)
  rw [etPullCompHom', op_comp, Category.assoc]

theorem bcCell_pbSecN {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y) (h' : Xs ⟶ Ys)
    (w : h' ≫ ιY = ιX ≫ h) (G : EtSh Λ X) {V : Y.Etale}
    (τ : (pull ιY Λ).obj ((push h Λ).obj G) ⟶ (push h' Λ).obj ((pull ιX Λ).obj G))
    (hτ : τ = (bcCell Λ ιX ιY h h' w).app G) (x : ((push h Λ).obj G).obj.obj (op V)) :
    (τ.hom.app (op ((etPull ιY).obj V))).hom (pbSec ιY x) =
      ((((pull ιX Λ).obj G).obj.map (bcSite ιX ιY h h' w V).op).hom (pbSec ιX (V := (etPull h).obj V) x)) := by
  subst hτ
  refine (bcCell_pbSec ιX ιY h h' w G x).trans (map_congr_apply _ ?_ _)
  simp only [bcSite, op_comp, Category.assoc]

section Paste

variable {X Y X' Y' X'' Y'' : Scheme.{u}}
  (ιX₁ : X' ⟶ X) (ιY₁ : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y') (w₁ : h' ≫ ιY₁ = ιX₁ ≫ h)
  (ιX₂ : X'' ⟶ X') (ιY₂ : Y'' ⟶ Y') (h'' : X'' ⟶ Y'') (w₂ : h'' ≫ ιY₂ = ιX₂ ≫ h')
  (ιX : X'' ⟶ X) (ιY : Y'' ⟶ Y) (hX : ιX = ιX₂ ≫ ιX₁) (hY : ιY = ιY₂ ≫ ιY₁) (w : h'' ≫ ιY = ιX ≫ h)

/-- The site identity behind `paste_nested`. -/
theorem site_paste (V : Y.Etale) :
    ((etPull ιX₂).map (bcSite ιX₁ ιY₁ h h' w₁ V)).op ≫ ((bcSite ιX₂ ιY₂ h' h'' w₂ ((etPull ιY₁).obj V)).op ≫
      ((etPull h'').map (etPullCompHom' ιY₂ ιY₁ ιY hY V)).op) =
    (etPullCompHom' ιX₂ ιX₁ ιX hX ((etPull h).obj V)).op ≫ (bcSite ιX ιY h h'' w V).op := by
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  refine etPull3_hom_ext ιX₂ ιX₁ h ?_
  simp only [etLeft_comp, Category.assoc, etPull_map_left_fst_r, bcSite_fst_r, bcSite_fst, etPullCompHom'_fst_r,
    etPullCompHom'_fst]

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
theorem pullUnit_congr {A B : Scheme.{u}} {f f' : A ⟶ B} (e : f = f') :
    (pullUnit Λ f).hom ≫ (pullCongr Λ e).hom.app (unitSh Λ B) = (pullUnit Λ f').hom := by
  subst e
  simp [pullCongr]

variable (Λ) in
/-- **`sqQ` respects the unit sheaves.** -/
theorem sqQ_unit :
    (pull h' Λ).map (pullUnit Λ ιY).hom ≫ (Mate.sqQ (Λ := Λ) ιX ιY h h' w).hom.app (unitSh Λ Y) ≫
        (pull ιX Λ).map (pullUnit Λ h).inv = (pullUnit Λ h').inv ≫ (pullUnit Λ ιX).hom := by
  rw [← cancel_epi (pullUnit Λ h').hom, Iso.hom_inv_id_assoc, ← Category.assoc, ← pullUnit_comp,
    Mate.sqQ_hom_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc (pullUnit Λ (h' ≫ ιY)).hom, pullUnit_congr Λ w, ← Category.assoc (pullUnit Λ (ιX ≫ h)).hom,
    pullUnit_comp, Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

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

variable {𝒳 𝒳₁ 𝒵 𝒳₂ 𝒴 𝒴₁ 𝒲 𝒴₂ : Type*} [Category 𝒳] [Category 𝒳₁] [Category 𝒵] [Category 𝒳₂]
  [Category 𝒴] [Category 𝒴₁] [Category 𝒲] [Category 𝒴₂]

/-- The **nested-typed comparison** `e₁⁻¹ ≫ e₂ : A₂ (A₁ G) ⟶ B₂ (B₁ G)` between two factorizations of a functor
(kernel-friendly: its type never mentions `A₁ ⋙ A₂`). -/
def nestComp {F : 𝒳 ⥤ 𝒳₂} {A₁ : 𝒳 ⥤ 𝒳₁} {A₂ : 𝒳₁ ⥤ 𝒳₂} {B₁ : 𝒳 ⥤ 𝒵} {B₂ : 𝒵 ⥤ 𝒳₂}
    (e₁ : F ≅ A₁ ⋙ A₂) (e₂ : F ≅ B₁ ⋙ B₂) (G : 𝒳) : A₂.obj (A₁.obj G) ⟶ B₂.obj (B₁.obj G) :=
  e₁.inv.app G ≫ e₂.hom.app G

/-- **Squares of squares, abstract form**: two pasting identities `P1`, `P2` with a common composite `d` give the
nested-form identity between the two pastings (all functors abstract, so the kernel never unfolds them). -/
theorem sqNatAbs {A₁ : 𝒳 ⥤ 𝒳₁} {A₂ : 𝒳₁ ⥤ 𝒳₂} {B₁ : 𝒳 ⥤ 𝒵} {B₂ : 𝒵 ⥤ 𝒳₂} {A : 𝒳 ⥤ 𝒳₂}
    {P₁ : 𝒴 ⥤ 𝒴₁} {P₂ : 𝒴₁ ⥤ 𝒴₂} {Q₁ : 𝒴 ⥤ 𝒲} {Q₂ : 𝒲 ⥤ 𝒴₂} {P : 𝒴 ⥤ 𝒴₂} {R₂ : 𝒳₂ ⥤ 𝒴₂}
    (eX : A ≅ A₁ ⋙ A₂) (eX' : A ≅ B₁ ⋙ B₂) (eY : P ≅ P₁ ⋙ P₂) (eY' : P ≅ Q₁ ⋙ Q₂)
    {G : 𝒳} {M : 𝒴} {N₁ : 𝒴₁} {N₂ : 𝒲}
    {b₁ : P₁.obj M ⟶ N₁} {b₂ : P₂.obj N₁ ⟶ R₂.obj (A₂.obj (A₁.obj G))}
    {c₁ : Q₁.obj M ⟶ N₂} {c₂ : Q₂.obj N₂ ⟶ R₂.obj (B₂.obj (B₁.obj G))} {d : P.obj M ⟶ R₂.obj (A.obj G)}
    (P1 : eY.hom.app M ≫ P₂.map b₁ ≫ b₂ = d ≫ R₂.map (eX.hom.app G))
    (P2 : eY'.hom.app M ≫ Q₂.map c₁ ≫ c₂ = d ≫ R₂.map (eX'.hom.app G)) :
    P₂.map b₁ ≫ b₂ ≫ R₂.map (nestComp eX eX' G) = nestComp eY eY' M ≫ Q₂.map c₁ ≫ c₂ := by
  rw [← cancel_epi (eY.hom.app M)]
  simp only [nestComp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% P1, P2, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]

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

omit [HasInjectiveResolutions C] [HasInjectiveResolutions C'] in
/-- The generic pull-back on `Ext` along `Lc`, `u`, then `κ` (HasExt instances implicit). -/
def fibHGen {hC : HasExt.{w} C} {hC' : HasExt.{w} C'} {Y : C} {Y' : C'} (κ : Lc.obj Y ⟶ Y') (q : ℕ)
    (x : Abelian.Ext.{w} X₁ Y q) : Abelian.Ext.{w} X₂ Y' q :=
  ((Abelian.Ext.mk₀ u).comp (x.mapExactFunctor Lc) (zero_add q)).comp (Abelian.Ext.mk₀ κ) (add_zero q)

end GenNat

variable {Λ : Type u} [CommRing Λ]

/-- **A morphism of `(g, s)`-squares**: `eP`, `eS` with `g₂ ≫ eS = eP ≫ g₁` and `σ : Spec Ω₂ ⟶ Spec Ω₁` with
`s₂ ≫ eS = σ ≫ s₁` (not necessarily over a base). -/
structure SqMor {P₁ S₁ P₂ S₂ : Scheme.{u}} (g₁ : P₁ ⟶ S₁) (g₂ : P₂ ⟶ S₂) (s₁ : GeomPt S₁) (s₂ : GeomPt S₂) where
  eP : P₂ ⟶ P₁
  eS : S₂ ⟶ S₁
  wE : g₂ ≫ eS = eP ≫ g₁
  σ : Spec (CommRingCat.of s₂.Ω) ⟶ Spec (CommRingCat.of s₁.Ω)
  wσ : s₂.pt ≫ eS = σ ≫ s₁.pt

namespace SqMor

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
variable {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]
def isoHomN {F : 𝒞 ⥤ ℰ} {A : 𝒞 ⥤ 𝒟} {B : 𝒟 ⥤ ℰ} (e : F ≅ A ⋙ B) (X : 𝒞) : F.obj X ⟶ B.obj (A.obj X) :=
  e.hom.app X
def isoInvN {F : 𝒞 ⥤ ℰ} {A : 𝒞 ⥤ 𝒟} {B : 𝒟 ⥤ ℰ} (e : A ⋙ B ≅ F) (X : 𝒞) : F.obj X ⟶ B.obj (A.obj X) :=
  e.inv.app X
end NestIso

section NestTr
end NestTr

theorem etPull2_hom_ext {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) {Z : A.Etale} {T : C.Etale}
    {m₁ m₂ : Z ⟶ (etPull a).obj ((etPull b).obj T)}
    (H : m₁.left ≫ pullback.fst _ a ≫ pullback.fst T.hom b = m₂.left ≫ pullback.fst _ a ≫ pullback.fst T.hom b) :
    m₁ = m₂ := by
  have k2 : ∀ m : Z ⟶ (etPull a).obj ((etPull b).obj T),
      m.left ≫ pullback.fst _ a ≫ pullback.snd T.hom b = Z.hom ≫ a := fun m =>
    (whisker_eq _ pullback.condition).trans (MorphismProperty.Over.w_assoc m _)
  refine etPull_hom_ext a (pullback.hom_ext ?_ ?_)
  · simpa only [Category.assoc] using H
  · simp only [Category.assoc]
    exact (k2 m₁).trans (k2 m₂).symm

section PullOfSec
variable {Λ : Type u} [CommRing Λ]

/-- Pulling back a global-section morphism `ofSec q` along `f`. -/
theorem pull_ofSec {X Y : Scheme.{u}} (f : X ⟶ Y) {F : EtSh Λ Y} (q : F.obj.obj (op (etId Y))) :
    (pullUnit Λ f).hom ≫ (pull f Λ).map (ofSec q) =
      ofSec ((((pull f Λ).obj F).obj.map (etIdPull f).hom.op).hom (pbSec f q)) := by
  refine (ofSec_sc _).symm.trans (congrArg ofSec ?_)
  rw [Supp.sc_comp]
  change (((pull f Λ).map (ofSec q)).hom.app (op (etId X))).hom
    (((pullUnit Λ f).hom.hom.app (op (etId X))).hom (oneSec Λ X)) = _
  rw [pullUnit_one, pullMap_pbSecO,
    show ((ofSec q).hom.app (op (etId Y))).hom (oneSec Λ Y) = q from sc_ofSec q]

end PullOfSec

section Pt
variable {S : Scheme.{u}} (s t : GeomPt S) (σ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of s.Ω))
  (hσ : σ ≫ s.pt = t.pt)

/-- The morphism of points `t ⟶ s` induced by `σ` over `S` (lifts `a ↦ σ ≫ a`). -/
def ptMor : t.point ⟶ s.point :=
  ⟨Functor.whiskerLeft (Scheme.Etale.forget S)
    (coyoneda.map (CategoryTheory.Over.homMk σ hσ :
      CategoryTheory.Over.mk t.pt ⟶ CategoryTheory.Over.mk s.pt).op)⟩

end Pt

namespace SqMor

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

theorem ptMor_id : ptMor s s (𝟙 _) h = 𝟙 _ := by
  apply GrothendieckTopology.Point.hom_ext
  ext U a
  first
  | (apply CategoryTheory.Over.OverMorphism.ext; simp; done)
  | (apply CategoryTheory.Over.OverMorphism.ext; exact Category.id_comp _)

end PtId

section Gen
variable {C C' : Type*} [Category C] [Category C'] [Abelian C] [Abelian C'] [HasExt.{u} C] [HasExt.{u} C']
  (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- `fibHGen` is bijective when `Ext.mapExactFunctor L` is and `u`, `κ` are isomorphisms. -/
theorem fibHGen_bijective {X₁ Y : C} {X₂ Y' : C'} (u : X₂ ⟶ L.obj X₁) [IsIso u] (κ : L.obj Y ⟶ Y') [IsIso κ]
    (q : ℕ) (hL : Function.Bijective (fun x : Ext.{u} X₁ Y q => x.mapExactFunctor L)) :
    Function.Bijective (fun x : Ext.{u} X₁ Y q =>
      ((Ext.mk₀ u).comp (x.mapExactFunctor L) (zero_add q)).comp (Ext.mk₀ κ) (add_zero q)) := by
  have h1 : Function.Bijective (fun y : Ext.{u} (L.obj X₁) (L.obj Y) q => (Ext.mk₀ u).comp y (zero_add q)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun z => (Ext.mk₀ (inv u)).comp z (zero_add q), ?_, ?_⟩
    · intro y; simp only [Ext.mk₀_comp_mk₀_assoc, IsIso.inv_hom_id, Ext.mk₀_id_comp]
    · intro z; simp only [Ext.mk₀_comp_mk₀_assoc, IsIso.hom_inv_id, Ext.mk₀_id_comp]
  have h2 : Function.Bijective (fun y : Ext.{u} X₂ (L.obj Y) q => y.comp (Ext.mk₀ κ) (add_zero q)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun z => z.comp (Ext.mk₀ (inv κ)) (add_zero q), ?_, ?_⟩
    · intro y
      simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, IsIso.hom_inv_id, Ext.comp_mk₀_id]
    · intro z
      simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, IsIso.inv_hom_id, Ext.comp_mk₀_id]
  exact h2.comp (h1.comp hL)

end Gen

section Sq
variable {Λ : Type u} [CommRing Λ] {P S S' : Scheme.{u}} (g₁ : P ⟶ S) (g : S' ⟶ S) (s₂ : GeomPt S')

/-- The morphism of `(g, s)`-squares of the base change `P ×_S S' ⟶ S'` at `s₂` over `s₂ ≫ g`. -/
abbrev bcSq : SqMor g₁ (pullback.snd g₁ g) (s₂.map g) s₂ where
  eP := pullback.fst g₁ g
  eS := g
  wE := pullback.condition.symm
  σ := 𝟙 _
  wσ := (Category.id_comp _).symm

end Sq

section Main

end Main

end RamanujanPetersson.EtPBC.C2

end

end

-- ===== S4.Def_RP_EtPBC_C2_GoodIso =====
section

/-! # S4-EtPBC-C2, part 1: `PBCGood` is invariant under isomorphisms of the source -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.C2

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.Mate

universe u

variable {Λ : Type u} [CommRing Λ]

section Sq
variable {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y) (h' : Xs ⟶ Ys)
  (w : h' ≫ ιY = ιX ≫ h)

/-- The base change map of a square whose horizontal maps are isomorphisms is an isomorphism. -/
theorem isIso_vMapG_of_iso [IsIso h] [IsIso h'] (G : EtSh Λ X) :
    IsIso (vMapG (Λ := Λ) ιX ιY h h' w G) := by
  have e := mateG (Λ := Λ) ιX ιY h h' w G
  have h1 : IsIso ((pull h' Λ).map (vMapG ιX ιY h h' w G) ≫
      (pullAdj h' Λ).counit.app ((pull ιX Λ).obj G)) := by
    rw [e]; infer_instance
  have h2 : IsIso ((pull h' Λ).map (vMapG ιX ιY h h' w G)) :=
    IsIso.of_isIso_comp_right _ ((pullAdj h' Λ).counit.app ((pull ιX Λ).obj G))
  exact isIso_of_reflects_iso _ (pull h' Λ)

end Sq

section Fib
variable {Y' Y S : Scheme.{u}} (e : Y' ⟶ Y) (g : Y ⟶ S) (s : GeomPt S)

instance isIso_fibCompH [IsIso e] : IsIso (fibCompH e g s) := by
  refine ⟨⟨pullback.lift (fibι g s ≫ inv e) (pullback.snd g s.pt) ?_, ?_, ?_⟩⟩
  · rw [Category.assoc, IsIso.inv_hom_id_assoc]; exact pullback.condition
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, fibCompH_ι, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact pullback.lift_snd _ _ _
  · apply pullback.hom_ext
    · rw [Category.assoc, fibCompH_ι, pullback.lift_fst_assoc, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, Category.id_comp]
      erw [pullback.lift_snd, pullback.lift_snd]

end Fib

section HZero
variable {W' W : Scheme.{u}}

theorem H_zero_of_iso {A B : EtSh Λ W} (φ : A ≅ B) {n : ℕ} (hA : ∀ x : H Λ A n, x = 0)
    (y : H Λ B n) : y = 0 := by
  have : y = (y.comp (Ext.mk₀ φ.inv) (add_zero n)).comp (Ext.mk₀ φ.hom) (add_zero n) := by
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id, Ext.comp_mk₀_id]
  rw [this, hA (y.comp (Ext.mk₀ φ.inv) (add_zero n)), Ext.zero_comp]

theorem H_zero_pull (k : W' ⟶ W) [IsIso k] (M : EtSh Λ W) {n : ℕ} (hM : ∀ x : H Λ M n, x = 0)
    (y : H Λ ((pull k Λ).obj M) n) : y = 0 := by
  obtain ⟨x, hx⟩ := (pull_ext_bijective (Λ := Λ) k (unitSh Λ W) M n).2
    ((Ext.mk₀ (pullUnit Λ k).inv).comp y (zero_add n))
  have hx' : x.mapExactFunctor (pull k Λ) = (Ext.mk₀ (pullUnit Λ k).inv).comp y (zero_add n) := hx
  have : y = (Ext.mk₀ (pullUnit Λ k).hom).comp ((Ext.mk₀ (pullUnit Λ k).inv).comp y (zero_add n))
      (zero_add n) := by
    rw [Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp]
  rw [this, ← hx', hM x, Ext.mapExactFunctor_zero, Ext.comp_zero]

end HZero

section Good
variable (Λ) {Y' Y S : Scheme.{u}} (e : Y' ⟶ Y) [IsIso e] (g : Y ⟶ S) (s : GeomPt S)

theorem bcSurj_iso (hg : ∀ G : EtSh Λ Y, BCSurj Λ g s 0 G) (G : EtSh Λ Y') :
    BCSurj Λ (e ≫ g) s 0 G := by
  have := isIso_vMapG_of_iso (Λ := Λ) (fibι (e ≫ g) s) (fibι g s) e (fibCompH e g s)
    (fibCompH_ι e g s) G
  exact bcSurj_comp_of_iso e g s G (hg _)

/-- `ι'^* I ≅ k^* ι^* (e_* I)` for the fibre isomorphism `k = fibCompH`. -/
def fibPullIso (I : EtSh Λ Y') :
    (pull (fibι (e ≫ g) s) Λ).obj I ≅
      (pull (fibCompH e g s) Λ).obj ((pull (fibι g s) Λ).obj ((push e Λ).obj I)) :=
  (pull (fibι (e ≫ g) s) Λ).mapIso (asIso ((pullAdj e Λ).counit.app I)).symm ≪≫
    (pullCompIso Λ (fibι (e ≫ g) s) e).symm.app _ ≪≫
    (pullCongr Λ (fibCompH_ι e g s).symm).app _ ≪≫
    (pullCompIso Λ (fibCompH e g s) (fibι g s)).app _

end Good

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

/-- **Tower maps** over `S` (with `gS : S ⟶ Spec K`): iterated `P^1`-bundles up to isomorphism. -/
inductive IsTower : {Y : Scheme.{0}} → (Y ⟶ S) → Prop
  | base : IsTower (qV K gS)
  | step {Y : Scheme.{0}} (h : Y ⟶ S) : IsTower h → IsTower (qV K (h ≫ gS) ≫ h)
  | iso {Y' Y : Scheme.{0}} (e : Y' ⟶ Y) [IsIso e] (h : Y ⟶ S) : IsTower h → IsTower (e ≫ h)

variable {K gS}

theorem IsTower.step_of_eq {Y : Scheme.{0}} {h : Y ⟶ S} (hh : IsTower K gS h)
    (x : Y ⟶ Spec (CommRingCat.of K)) (hx : x = h ≫ gS) : IsTower K gS (qV K x ≫ h) := by
  subst hx; exact IsTower.step h hh

theorem IsTower.of_iso {Y' Y : Scheme.{0}} {h : Y ⟶ S} (hh : IsTower K gS h) (e : Y' ⟶ Y) [IsIso e]
    (h' : Y' ⟶ S) (he : e ≫ h = h') : IsTower K gS h' := by
  subst he; exact IsTower.iso e h hh

theorem IsTower.isProper {Y : Scheme.{0}} {h : Y ⟶ S} (hh : IsTower K gS h) : IsProper h := by
  induction hh with
  | base => exact (inferInstance : IsProper (qV K gS))
  | step h _ ih => exact (inferInstance : IsProper (qV K (h ≫ gS) ≫ h))
  | iso e h _ ih => exact (inferInstance : IsProper (e ≫ h))

end Def

section Good

end Good

section BC
variable {K : Type} [Field K] {S : Scheme.{0}} {gS : S ⟶ Spec (CommRingCat.of K)}

/-- **Base change of a tower** along any `g : S' ⟶ S` is a tower over `S'`. -/
theorem IsTower.baseChange {S' : Scheme.{0}} (g : S' ⟶ S) {Y : Scheme.{0}} {h : Y ⟶ S}
    (hh : IsTower K gS h) : IsTower K (g ≫ gS) (pullback.snd h g) := by
  induction hh with
  | base =>
    exact (IsTower.base (K := K) (gS := g ≫ gS)).of_iso (pullbackLeftPullbackSndIso _ _ g).hom _
      (pullbackLeftPullbackSndIso_hom_snd _ _ _)
  | step h _ ih =>
    have h1 : IsTower K (g ≫ gS) (qV K (pullback.fst h g ≫ h ≫ gS) ≫ pullback.snd h g) :=
      ih.step_of_eq _ (by rw [← Category.assoc, pullback.condition, Category.assoc])
    have h2 := h1.of_iso (pullbackLeftPullbackSndIso (P1.toSpecK K) (h ≫ gS) (pullback.fst h g)).hom _
      rfl
    refine h2.of_iso (pullbackRightPullbackFstIso h g (qV K (h ≫ gS))).inv _ ?_
    rw [Iso.inv_comp_eq, pullbackRightPullbackFstIso_hom_snd, ← Category.assoc,
      pullbackLeftPullbackSndIso_hom_snd]
  | iso e h _ ih =>
    have h1 := ih.of_iso (pullback.snd e (pullback.fst h g)) _ rfl
    refine h1.of_iso (pullbackRightPullbackFstIso h g e).inv _ ?_
    rw [Iso.inv_comp_eq, pullbackRightPullbackFstIso_hom_snd]

end BC

section Shapes

end Shapes

end RamanujanPetersson.EtPBC.C2

end

end


