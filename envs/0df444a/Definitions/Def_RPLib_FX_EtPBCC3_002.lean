-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC3_002
-- name    : RPLib_FX_EtPBCC3_002
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-27T04:31:57.759175+00:00
-- url     : https://prove2.me/theorems/979cf9e7-9214-5526-bdb6-cd99b034c3da
-- title:
--   Compactly supported étale cohomology of affine space with Tate twists, library file 002
-- statement:
--   File 002 of the library for compactly supported étale cohomology of affine space with Tate twists: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_RDer`: S4-EtCompact, part 10: `R^n f_!` is independent of a closed change of ambient
--   * `S4.Def_RP_EtLeray_ResDer`: S4-EtLeray, part 8: étale restriction commutes with `R^q h_*`
--   * `S4.Def_RP_EtPBC_B_BCc`: S4-EtPBC-B, D1a: base change for extension by zero and for closed push-forward
--   * `S4.Def_RP_EtCompact_An`: S4-EtCompact, part 16: affine spaces `A^n ⊆ (P^1)^n` (O6, explicit compactifications)
--   * `S4.Def_RP_EtLeray_Shift`: S4-EtLeray, part 2: shifting an injective resolution (dimension shift for `R^q`)
--   * `S4.Def_RP_EtLeray_Low`: S4-EtLeray, part 3: `R¹ N` as a cokernel, and the low-degree consequences
--   * `S4.Def_RP_EtLeray_BCo`: S4-EtLeray, part 10: base change along arbitrary pullback squares
--
--   **Formalization note.** One file of a library formalizing the étale cohomology with compact supports of affine space over an algebraically closed field $K$ with Tate-twisted coefficients: for $\Lambda$ a finite ring with $\ell^m \Lambda = 0$ ($\ell$ invertible in $K$) and $\Lambda(k)$ the constant sheaf $(\Lambda \otimes \mu_{\ell^m})^{\otimes k}$, $H^q_c(\mathbb{A}^{n+1}_K, \Lambda(k)) = 0$ for $q \ne 2n+2$ and $H^{2n+2}_c(\mathbb{A}^{n+1}_K, \Lambda(n+1)) \cong \Lambda$ $\Lambda$-linearly, via $R^q \mathrm{pr}_!$ of the relative affine line and induction on the dimension. It builds on the proper base change libraries (`RPLib_FX_EtPBC_*`, `RPLib_FX_EtPBCB_*`, `RPLib_FX_EtPBCC1_*`, `RPLib_FX_EtPBCC2_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XVII (P. Deligne, cohomologie à supports propres) and Exposé XVIII, 2.9 (P. Deligne, morphisme trace), Lecture Notes in Math. 305, Springer (1973); P. Deligne, SGA 4 1/2, [Arcata], Lecture Notes in Math. 569 (1977); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_003

/-!
# Sheaf-level proper base change with compact supports, library file 002

Declarations of the formalization of sheaf-level proper base change for compactly supported étale
cohomology: for a compactified X ⟶ S whose proper part is an iterated projective-line bundle (a tower)
and any g : S' ⟶ S of finite type, the base change morphism g^* R^q f_! F ⟶ R^q f'_! (g_X^* F) is an
isomorphism, re-hosted declaration by declaration from the library modules below, on top of the proper
base change libraries RPLib_FX_EtPBC, RPLib_FX_EtPBCB and RPLib_FX_EtPBCC1. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_RDer`: S4-EtCompact, part 10: `R^n f_!` is independent of a closed change of ambient
* `S4.Def_RP_EtLeray_ResDer`: S4-EtLeray, part 8: étale restriction commutes with `R^q h_*`
* `S4.Def_RP_EtPBC_B_BCc`: S4-EtPBC-B, D1a: base change for extension by zero and for closed push-forward
* `S4.Def_RP_EtCompact_An`: S4-EtCompact, part 16: affine spaces `A^n ⊆ (P^1)^n` (O6, explicit compactifications)
* `S4.Def_RP_EtLeray_Shift`: S4-EtLeray, part 2: shifting an injective resolution (dimension shift for `R^q`)
* `S4.Def_RP_EtLeray_Low`: S4-EtLeray, part 3: `R¹ N` as a cokernel, and the low-degree consequences
* `S4.Def_RP_EtLeray_BCo`: S4-EtLeray, part 10: base change along arbitrary pullback squares
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_RDer =====
section

/-!
# S4-EtCompact, part 10: `R^n f_!` is independent of a closed change of ambient

An exact functor that preserves injective objects sends injective resolutions to injective
resolutions (`injResMap`). Every `push g` preserves injectives (its left adjoint `pull g` is exact),
and `push ι` is exact for a closed immersion `ι`. Hence for `ι ≫ g' = g`:
`R^n g'_* (ι_* Y) ≅ R^n g_* Y` (`rightDerivedPushIso`), and `R^n f_!` computed with
`c.pushAlong ι fbar' h` agrees with `R^n f_!` computed with `c` (`Cpt.rshriekPushAlongIso`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section MapRes

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  (G : C ⥤ D) [G.Additive] [G.PreservesHomology] [G.PreservesInjectiveObjects]

/-- An exact functor preserving injectives maps an injective resolution of `Y` to one of `G Y`. -/
def injResMap {Y : C} (I : InjectiveResolution Y) : InjectiveResolution (G.obj Y) where
  cocomplex := (G.mapHomologicalComplex _).obj I.cocomplex
  injective n := G.injective_obj (I.cocomplex.X n)
  ι := (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app Y ≫
    (G.mapHomologicalComplex _).map I.ι
  quasiIso := inferInstance

end MapRes

variable {Λ : Type u} [CommRing Λ]

/-- **`R^n g'_* ∘ ι_* ≅ R^n g_*`** for a closed immersion `ι` with `ι ≫ g' = g`. -/
def rightDerivedPushIso {P P' B : Scheme.{u}} (ι : P ⟶ P') [IsClosedImmersion ι] (g' : P' ⟶ B)
    (g : P ⟶ B) (h : ι ≫ g' = g) (n : ℕ) (Y : EtSh Λ P) :
    ((push g' Λ).rightDerived n).obj ((push ι Λ).obj Y) ≅ ((push g Λ).rightDerived n).obj Y :=
  (injResMap (push ι Λ) (injectiveResolution Y)).isoRightDerivedObj (push g' Λ) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((Functor.mapHomologicalComplexCompIso
        (pushCompIso Λ ι g' ≪≫ eqToIso (by rw [h])) _).app (injectiveResolution Y).cocomplex) ≪≫
    ((injectiveResolution Y).isoRightDerivedObj (push g Λ) n).symm

namespace Cpt

end Cpt

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtLeray_ResDer =====
section

/-!
# S4-EtLeray, part 8: étale restriction commutes with `R^q h_*`

* `homologyMapIso` (generic): an exact functor commutes with the homology of a cochain complex;
* `rderCompExactIso` (generic): `R^q(F ⋙ G) ≅ G ∘ R^q F` for `G` exact;
* **`resRDerIso`**: for `c : V ⟶ X` étale and `h : P ⟶ X`,
  `c^* (R^q h_* Y) ≅ R^q (pullback.fst c h)_* ((pullback.snd c h)^* Y)`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtLeray

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

section Gen

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (G : C ⥤ D) [G.Additive]
  [G.PreservesHomology]

variable {E : Type*} [Category E] [Abelian E] (F : E ⥤ C) [F.Additive]
  [HasInjectiveResolutions E]

/-- `R^q(F ⋙ G) ≅ G ∘ R^q F` for an exact `G`. -/
def rderCompExactIso (q : ℕ) (Y : E) :
    ((F ⋙ G).rightDerived q).obj Y ≅ G.obj ((F.rightDerived q).obj Y) :=
  (injectiveResolution Y).isoRightDerivedObj (F ⋙ G) q ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) _).symm.app
        (injectiveResolution Y).cocomplex) ≪≫
    homologyMapIso G _ q ≪≫
    G.mapIso ((injectiveResolution Y).isoRightDerivedObj F q).symm

end Gen

variable {Λ : Type u} [CommRing Λ] {V X P : Scheme.{u}} (c : V ⟶ X) [Etale c] (h : P ⟶ X)

/-- **Étale restriction commutes with `R^q h_*`.** -/
def resRDerIso (q : ℕ) (Y : EtSh Λ P) :
    (res c Λ).obj (((push h Λ).rightDerived q).obj Y) ≅
      ((push (pullback.fst c h) Λ).rightDerived q).obj ((res (pullback.snd c h) Λ).obj Y) :=
  (res c Λ).mapIso ((injectiveResolution Y).isoRightDerivedObj (push h Λ) q) ≪≫
    (homologyMapIso (res c Λ) (((push h Λ).mapHomologicalComplex _).obj (injectiveResolution Y).cocomplex)
      q).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso
      ((Functor.mapHomologicalComplexCompIso (PushBC.pushResBC c h Λ) _).app (injectiveResolution Y).cocomplex ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm.app (injectiveResolution Y).cocomplex) ≪≫
    ((injResMap (res (pullback.snd c h) Λ) (injectiveResolution Y)).isoRightDerivedObj
      (push (pullback.fst c h) Λ) q).symm

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtPBC_B_BCc =====
section

/-!
# S4-EtPBC-B, D1a: base change for extension by zero and for closed push-forward

* **`lshPullBC`**: for `c : V ⟶ X` étale and any `j : U ⟶ X`,
  `j^* ∘ c_! ≅ c'_! ∘ j'^*` (`c' = pullback.snd c j`, `j' = pullback.fst c j`), by uniqueness of left
  adjoints from the base change `pushResBC : c^* ∘ j_* ≅ j'_* ∘ c'^*`;
* **`closedBC`**: for `i : Z ⟶ P` a closed immersion and any `ιP : P' ⟶ P`,
  `ιP^* i_* M ≅ i'_* ιZ^* M` (`i' = pullback.snd i ιP`, `ιZ = pullback.fst i ιP`): the unit of `i'` is an
  isomorphism on `ιP^* i_* M` (stalks at `cutPts i'`), then `i^* i_* ≅ id`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Mate

universe u

section Lsh

end Lsh

section Closed

variable {Λ : Type u} [CommRing Λ] {Z P P' : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i] (ιP : P' ⟶ P)

/-- **Base change for a closed push-forward**: `ιP^* i_* M ≅ i'_* ιZ^* M`. -/
def closedBC (M : EtSh Λ Z) : (pull ιP Λ).obj ((push i Λ).obj M) ≅
    (push (pullback.snd i ιP) Λ).obj ((pull (pullback.fst i ιP) Λ).obj M) :=
  haveI := isIso_unit_closedBC i ιP M
  haveI := isIso_closed_counit Λ i
  asIso ((pullAdj (pullback.snd i ιP) Λ).unit.app ((pull ιP Λ).obj ((push i Λ).obj M))) ≪≫
    (push (pullback.snd i ιP) Λ).mapIso
      ((sqQ (Λ := Λ) (pullback.fst i ιP) ιP i (pullback.snd i ιP) pullback.condition.symm).app
          ((push i Λ).obj M) ≪≫
        (pull (pullback.fst i ιP) Λ).mapIso (asIso ((pullAdj i Λ).counit.app M)))

end Closed

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtCompact_An =====
section

/-!
# S4-EtCompact, part 16: affine spaces `A^n ⊆ (P^1)^n` (O6, explicit compactifications)

`Cpt.ofProper f`: the trivial compactification of a proper map. `AnData K n` builds, by induction,
`A^(n+1) := A^1 ×_K A^n` with its structure map to `Spec K` and the product compactification
`A^(n+1) ⊆ P^1 ×_K (P^1)^n` (`Cpt.prod`). `An K n`, `An.toSpecK K n`, `An.cpt K n`; the coordinate projection
`An.proj K n : A^(n+1) ⟶ A^n` (forgetting the new coordinate) is compactified by the `P^1`-bundle
`An.projCpt K n : Cpt (An.proj K n)` (`A1.cptOver`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

universe u

namespace Cpt

/-- The trivial compactification of a proper map. -/
def ofProper {X B : Scheme.{u}} (f : X ⟶ B) [IsProper f] : Cpt f where
  P := X
  Z := X
  j := 𝟙 X
  i := 𝟙 X
  fbar := f
  isOpenImmersion_j := inferInstance
  isClosedImmersion_i := inferInstance
  isProper_fbar := inferInstance
  comm := by rw [Category.id_comp, Category.id_comp]

end Cpt

variable (K : Type u) [Field K]

instance isProper_id_specK : IsProper (𝟙 (Spec (CommRingCat.of K))) := inferInstance

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtLeray_Shift =====
section

/-!
# S4-EtLeray, part 2: shifting an injective resolution (dimension shift for `R^q`)

For an injective resolution `P` of `N` put `Qc P := coker(N → P⁰)`. Then `P^(•+1)` with the induced
`Qc P ↪ P¹` is an injective resolution `shRes P` of `Qc P`, and for any additive `R`
* **`dsIso P R q`**: `R^(q+1)(Qc P) ≅ R^(q+2) N`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtLeray

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {N : C} (P : InjectiveResolution N)

/-- `Qc P = coker(N → P⁰)`. -/
abbrev Qc : C := cokernel (P.ι.f 0)

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtLeray_Low =====
section

/-!
# S4-EtLeray, part 3: `R¹ N` as a cokernel, and the low-degree consequences

`P` an injective resolution of `N`, `R` additive and left exact. With `Rπ := R(P⁰ → Qc P)`:
* **`r1Iso P R`**: `R¹ N ≅ coker(Rπ)` (via left homology data of `R P⁰ → R P¹ → R P²` with cycles `R(Qc P)`);
* `baseSC`: `0 → im(Rπ) → R(Qc P) → coker(Rπ) → 0` short exact;
* `imSC`: `0 → R N → R P⁰ → im(Rπ) → 0` short exact;
* **`presQ_map_shortExact`**: `R¹ N = 0` ⇒ `R(N → P⁰ → Qc P)` short exact;
* `injective_im`, **`injective_RQc`**: `R N` injective ⇒ `im(Rπ)` injective, and with `R¹ N = 0`, `R(Qc P)` injective.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtLeray

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
variable [HasInjectiveResolutions C] {N : C} (P : InjectiveResolution N) (R : C ⥤ D) [R.Additive]
  [PreservesFiniteLimits R]

/-- `R(P⁰) → R(P¹) → R(P²)`. -/
abbrev S01 : ShortComplex D := ((R.mapHomologicalComplex _).obj P.cocomplex).sc' 0 1 2

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtLeray_BCo =====
section

/-!
# S4-EtLeray, part 10: base change along arbitrary pullback squares

For a pullback square `IsPullback a b f g` (`a ≫ f = b ≫ g`):
* **`pullPushSq`** (`f` a closed immersion): `g^* f_* M ≅ b_* a^* M`;
* **`pullLshSq`** (`f` étale): `g^* f_! F ≅ b_! a^* F`;
* **`pullRDerSq`** (`g` étale): `g^* (R^q f_* Y) ≅ R^q b_* (a^* Y)`.
Helpers: `pushPullIso`/`lshPullIso` (`e_* e^* ≅ 𝟭`, `e_! e^* ≅ 𝟭` for an isomorphism `e`), `lshCompIso`.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtLeray

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC

universe u

variable {Λ : Type u} [CommRing Λ]

section Iso

variable {W W' : Scheme.{u}} (e : W ⟶ W') [IsIso e]

/-- `e_* e^* X ≅ X` for an isomorphism `e`. -/
def pushPullIso (X : EtSh Λ W') : (push e Λ).obj ((pull e Λ).obj X) ≅ X :=
  (asIso ((pullAdj e Λ).unit.app X)).symm

end Iso

end RamanujanPetersson.EtLeray

end

end


