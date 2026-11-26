-- Prove2me | Definitions.Def_RPLib_FX_EtPBCB_001
-- name    : RPLib_FX_EtPBCB_001
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T01:30:27.239696+00:00
-- url     : https://prove2.me/theorems/9a3d8217-a6d5-5b1a-b904-147bf2e38457
-- title:
--   Proper base change for iterated projective-line bundles, library file 001
-- statement:
--   File 001 of the proper base change library for iterated projective-line bundles: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
--   * `S4.Def_RP_EtSheaves_Cons`: S4-EtSheaves, part 20: constructible sheaves
--   * `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
--   * `S4.Def_RP_EtPBC_A_StkBCd0`: S4-EtPBC-A, L1f part 4a: `stalkBC` is bijective; the bare equivalence `stalkEquivE`
--   * `S4.Def_RP_EtCompact_RDer`: S4-EtCompact, part 10: `R^n f_!` is independent of a closed change of ambient
--   * `S4.Def_RP_EtPBC_B_Mate`: S4-EtPBC-B, C4 part 1: the base change square and its mate identity
--   * `S4.Def_RP_EtPBC_B_RatPt`: S4-EtPBC-B, R1: closed points give `K`-rational geometric points (`K = K̄`)
--   * `S4.Def_RP_EtPBC_B_Jac`: S4-EtPBC-B, B1: sheaves on schemes of finite type over a field are detected at closed points
--   * `S4.Def_RP_EtPBC_B_VanA`: S4-EtPBC-B, A2: proper base change from vanishing on injectives (effaceability)
--   * `S4.Def_RP_EtPBC_B_C1`: S4-EtPBC-B, C1: higher direct images of `ι_* ι^* I` along the `P^1`-bundle vanish
--   * `S4.Def_RP_EtPBC_B_NatZ`: S4-EtPBC-B, C2a: naturality of degree-0 base change, and closed-point isomorphism test
--   * `S4.Def_RP_EtPBC_B_C2`: S4-EtPBC-B, C2 + C3: fibre vanishing for `P^1_Y ⟶ Y ⟶ S`
--   * `S4.Def_RP_EtPBC_B_Sec`: S4-EtPBC-B, C4 part 2: the degree-0 base change unit of a composite
--   * `S4.Def_RP_EtPBC_B_Tower`: S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line
--
--   **Formalization note.** One file of a library formalizing proper base change for iterated projective-line bundles: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the tower $X_0 = \mathbf P^1_S$, $X_{k+1} = \mathbf P^1_{X_k}$ with structure maps $f_k : X_k \to S$ (so $X_n = (\mathbf P^1)^{n+1}_S$) and a $K$-point $s$ of $S$, the stalk of $R^q f_{n*} F$ at $s$ is the étale cohomology $H^q(X_{n,s}, F|_{X_{n,s}})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. It builds on the proper base change library for the projective line (`RPLib_FX_EtPBC_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_195

/-!
# Proper base change for iterated projective-line bundles, library file 001

Declarations of the formalization of proper base change for the étale cohomology of the iterated
projective-line bundles (P¹)^(n+1)_S → S (geometric stalks of the higher direct images are the étale
cohomology of the geometric fibres), re-hosted declaration by declaration from the library modules
below, on top of the proper base change library for the projective line (RPLib_FX_EtPBC). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
* `S4.Def_RP_EtSheaves_Cons`: S4-EtSheaves, part 20: constructible sheaves
* `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
* `S4.Def_RP_EtPBC_A_StkBCd0`: S4-EtPBC-A, L1f part 4a: `stalkBC` is bijective; the bare equivalence `stalkEquivE`
* `S4.Def_RP_EtCompact_RDer`: S4-EtCompact, part 10: `R^n f_!` is independent of a closed change of ambient
* `S4.Def_RP_EtPBC_B_Mate`: S4-EtPBC-B, C4 part 1: the base change square and its mate identity
* `S4.Def_RP_EtPBC_B_RatPt`: S4-EtPBC-B, R1: closed points give `K`-rational geometric points (`K = K̄`)
* `S4.Def_RP_EtPBC_B_Jac`: S4-EtPBC-B, B1: sheaves on schemes of finite type over a field are detected at closed points
* `S4.Def_RP_EtPBC_B_VanA`: S4-EtPBC-B, A2: proper base change from vanishing on injectives (effaceability)
* `S4.Def_RP_EtPBC_B_C1`: S4-EtPBC-B, C1: higher direct images of `ι_* ι^* I` along the `P^1`-bundle vanish
* `S4.Def_RP_EtPBC_B_NatZ`: S4-EtPBC-B, C2a: naturality of degree-0 base change, and closed-point isomorphism test
* `S4.Def_RP_EtPBC_B_C2`: S4-EtPBC-B, C2 + C3: fibre vanishing for `P^1_Y ⟶ Y ⟶ S`
* `S4.Def_RP_EtPBC_B_Sec`: S4-EtPBC-B, C4 part 2: the degree-0 base change unit of a composite
* `S4.Def_RP_EtPBC_B_Tower`: S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtSheaves_Closed =====
section

/-!
# S4-EtSheaves, part 14: `i_*` vanishes off `Z`

For `i : Z ⟶ X` and an etale `j : U ⟶ X` whose image misses the image of `i`, the restriction
`j^* i_* G` is the zero sheaf: its values are those of `G` on the empty schemes `W ×_X Z`.
Hence the stalks of `i_* G` vanish at geometric points outside the (closed) image of `i`, every
map `j_! G' ⟶ i_* G` is zero, and `j_! j^* F ⟶ F ⟶ i_* i^* F` is a complex.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [Etale j]

/-- **Stalks of `i_* G` vanish off the image of a closed immersion `i`.** -/
theorem push_stalk_isZero_of_not_mem [IsClosedImmersion i] (s : GeomPt X)
    (hs : s.center ∉ Set.range i) (G : EtSh Λ Z) : IsZero ((s.stalkF Λ).obj ((push i Λ).obj G)) := by
  obtain ⟨t, rfl⟩ := exists_map_eq (complOpens i).ι s (by rw [range_complOpens_ι]; exact hs)
  exact push_stalk_isZero Λ i (complOpens i).ι (disjoint_complOpens i) t G

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_Cons =====
section

/-!
# S4-EtSheaves, part 20: constructible sheaves

`IsLisseOn Λ F S` (`F` is lisse along a subset `S`): every point of `S` has an etale neighbourhood `U` with a map
`M_U ⟶ F|_U` from a finite constant sheaf that is an isomorphism on the stalks at all geometric points of `U`
over `S`. For `S` locally closed this is `F|_S` lisse on `S` (any subscheme structure): the map of lisse sheaves
`M ⟶ F|_S` on `U ×_X S` is an isomorphism on all stalks, and conversely etale neighbourhoods in `S` come from `X`
(part 18) and an isomorphism at one stalk spreads out. So no subscheme structure is needed.
`IsCons Λ F`: a finite partition of `X` into locally closed subsets along each of which `F` is lisse.
Lisse ⇒ constructible; `f^*` and `⊗` preserve constructibility.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ]

theorem GeomPt.center_map {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeomPt X) :
    (s.map f).center = f s.center := rfl

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB2a =====
section

/-!
# S4-EtPBC-A, L3b (TB2a): section calculus for base change

* `etPull_hom_ext`: maps into `X ×_Y T` agree if their first components agree;
* `etIdPull g : etId X ≅ X ×_Y Y`, `pullUnit g : Λ_X ≅ g^*Λ_Y`, `pullUnit_one`;
* `unit_hom_ext`: maps out of `Λ_X` are determined by the image of `1`;
* transport of pulled-back sections along `pullIsoRes`, `pullCompIso`, `pullCongr`, `(pull g).map`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

section TB2

variable {Λ : Type u} [CommRing Λ]

theorem pullMap_pbSec {X Y : Scheme.{u}} (g : X ⟶ Y) {F G : EtSh Λ Y} (φ : F ⟶ G) {V : Y.Etale} {Z : X.Etale}
    (a : Z ⟶ (etPull g).obj V) (z : F.obj.obj (op V)) :
    ((((pull g Λ).map φ).hom.app (op Z)).hom ((((pull g Λ).obj F).obj.map a.op).hom (pbSec g z))) =
      ((((pull g Λ).obj G).obj.map a.op).hom (pbSec g ((φ.hom.app (op V)).hom z))) := by
  rw [pbSec_natural]
  exact congrArg (fun ψ => ψ.hom (pbSec g z)) ((((pull g Λ).map φ).hom.naturality a.op))

end TB2

section TB2o

/-! Op-form section calculus: restriction maps are op-morphisms `a : op T ⟶ op Z` that are passed through
unchanged, so consecutive steps meet in syntactically equal terms (this keeps kernel checks cheap). -/

end TB2o

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_StkBCd0 =====
section

/-!
# S4-EtPBC-A, L1f part 4a: `stalkBC` is bijective; the bare equivalence `stalkEquivE`

(Split from `StkBCd` for the file time limit: each declaration mentioning these types costs 10-30 s of kernel time.)
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

variable (F : EtSh Λ P) (n : ℕ) (Q : (S.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ)
  (e : ∀ V : S.Etale, Q.obj (op V) ≃+ Ext.{u} (freeSh Λ ((etPull g).obj V)) F n)

variable {Λ g s F n Q e}

variable (s)

theorem stalkEquivE_apply (he : GermNat Λ g F n Q e) (hI : BCInj Λ g s n F) (hS : BCSurj Λ g s n F)
    (x : ToType (s.point.presheafFiber.obj Q)) : stalkEquivE s he hI hS x = stalkBC s he x :=
  Equiv.ofBijective_apply _ _ x

end RamanujanPetersson.EtPBC

end

end

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

end MapRes

variable {Λ : Type u} [CommRing Λ]

instance push_preservesInjectiveObjects {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (push g Λ).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (pullAdj g Λ)

namespace Cpt

end Cpt

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtPBC_B_Mate =====
section

/-!
# S4-EtPBC-B, C4 part 1: the base change square and its mate identity

For a commutative square `h' ≫ ιY = ιX ≫ h` of schemes:
* `pullComp_counit(')`: the counit of `(a ≫ b)^* ⊣ (a ≫ b)_*` through `a^* b^*` and `a_* ⋙ b_*`
  (`pullCompIso` is the left adjoint uniqueness iso of `pushCompIso`);
* `pullCongr_counit`: transport of counits along `k = k'`;
* `sqP : h_* ιX_* ≅ ιY_* h'_*`, `sqQ : h'^* ιY^* ≅ ιX^* h^*`, `vMap : ιY^* h_* ⟶ h'_* ιX^*`
  (`ιY^*` of `h_*` of the unit of `ιX`, then `sqP`, then the counit of `ιY`);
* `sq_tail`: the counit of `h'^* ιY^*` through the square (first half of the mate identity).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.Mate

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ]

section A

variable {W X Y : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Y)

theorem pullComp_counit (M : EtSh Λ W) :
    (pullCompIso Λ a b).hom.app ((push (a ≫ b) Λ).obj M) ≫
      (pull a Λ).map ((pull b Λ).map ((pushCompIso Λ a b).inv.app M)) ≫
      (pull a Λ).map ((pullAdj b Λ).counit.app ((push a Λ).obj M)) ≫ (pullAdj a Λ).counit.app M =
    (pullAdj (a ≫ b) Λ).counit.app M := by
  have e := Adjunction.leftAdjointUniq_hom_app_counit (pullAdj (a ≫ b) Λ)
    (((pullAdj b Λ).comp (pullAdj a Λ)).ofNatIsoRight (pushCompIso Λ a b)) M
  have e2 : (((pullAdj b Λ).comp (pullAdj a Λ)).ofNatIsoRight (pushCompIso Λ a b)).counit.app M =
      (pull a Λ).map ((pull b Λ).map ((pushCompIso Λ a b).inv.app M)) ≫
      (pull a Λ).map ((pullAdj b Λ).counit.app ((push a Λ).obj M)) ≫ (pullAdj a Λ).counit.app M := by
    first
    | simp [Adjunction.comp_counit_app]
    | (rw [Adjunction.ofNatIsoRight_counit]; simp [Adjunction.comp_counit_app])
    | simp [Adjunction.ofNatIsoRight, Adjunction.ofNatIsoLeft, Adjunction.comp_counit_app]
  rw [e2] at e
  exact e

@[reassoc]
theorem pullComp_counit' (M : EtSh Λ W) :
    (pull a Λ).map ((pull b Λ).map ((pushCompIso Λ a b).inv.app M)) ≫
      (pull a Λ).map ((pullAdj b Λ).counit.app ((push a Λ).obj M)) ≫ (pullAdj a Λ).counit.app M =
    (pullCompIso Λ a b).inv.app ((push (a ≫ b) Λ).obj M) ≫ (pullAdj (a ≫ b) Λ).counit.app M := by
  rw [← pullComp_counit a b M, Iso.inv_hom_id_app_assoc]

end A

theorem pullCongr_counit {X Y : Scheme.{u}} {k k' : X ⟶ Y} (e : k = k') (M : EtSh Λ X)
    (p : (push k' Λ).obj M = (push k Λ).obj M) :
    (pull k Λ).map (eqToHom p) ≫ (pullAdj k Λ).counit.app M =
      (pullCongr Λ e).hom.app ((push k' Λ).obj M) ≫ (pullAdj k' Λ).counit.app M := by
  subst e
  simp [pullCongr]

section Sq

variable {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y) (h' : Xs ⟶ Ys)
  (w : h' ≫ ιY = ιX ≫ h)

/-- `h_* ιX_* M ≅ ιY_* h'_* M`. -/
def sqP (M : EtSh Λ Xs) : (push h Λ).obj ((push ιX Λ).obj M) ≅ (push ιY Λ).obj ((push h' Λ).obj M) :=
  (pushCompIso Λ ιX h).app M ≪≫ eqToIso (by rw [w]) ≪≫ ((pushCompIso Λ h' ιY).app M).symm

/-- `h'^* ιY^* ≅ ιX^* h^*`. -/
def sqQ : pull ιY Λ ⋙ pull h' Λ ≅ pull h Λ ⋙ pull ιX Λ :=
  (pullCompIso Λ h' ιY).symm ≪≫ pullCongr Λ w ≪≫ pullCompIso Λ ιX h

@[reassoc]
theorem sqQ_hom_app (F : EtSh Λ Y) : (sqQ ιX ιY h h' w).hom.app F =
    (pullCompIso Λ h' ιY).inv.app F ≫ (pullCongr Λ w).hom.app F ≫ (pullCompIso Λ ιX h).hom.app F := rfl

theorem sq_tail (M : EtSh Λ Xs) (p : (push (ιX ≫ h) Λ).obj M = (push (h' ≫ ιY) Λ).obj M) :
    (pull h' Λ).map ((pull ιY Λ).map (eqToHom p)) ≫
      (pull h' Λ).map ((pull ιY Λ).map ((pushCompIso Λ h' ιY).inv.app M)) ≫
      (pull h' Λ).map ((pullAdj ιY Λ).counit.app ((push h' Λ).obj M)) ≫ (pullAdj h' Λ).counit.app M =
    (pullCompIso Λ h' ιY).inv.app ((push (ιX ≫ h) Λ).obj M) ≫
      (pullCongr Λ w).hom.app ((push (ιX ≫ h) Λ).obj M) ≫ (pullAdj (ιX ≫ h) Λ).counit.app M := by
  have n2 := (pullCompIso Λ h' ιY).inv.naturality (eqToHom p)
  simp only [Functor.comp_map] at n2
  rw [pullComp_counit' h' ιY M, reassoc_of% n2, pullCongr_counit w M p]

end Sq

end RamanujanPetersson.EtPBC.Mate

end

end

-- ===== S4.Def_RP_EtPBC_B_RatPt =====
section

/-!
# S4-EtPBC-B, R1: closed points give `K`-rational geometric points (`K = K̄`)

For `gY : Y ⟶ Spec K` locally of finite type, `K` algebraically closed:
* `isAlgClosed_residue_of_closed`: `κ(y) ≅ K` is algebraically closed at closed `y`;
* **`isIso_geomPtAt`**: `(geomPtAt y).pt ≫ gY` is an isomorphism at closed `y` (so `pbc_P1` applies at `geomPtAt y`);
* `isClosed_center`: the center of a `K`-rational geometric point is closed;
* **`pt_factor_of_center`**: two `K`-rational geometric points with the same center: `t.pt` factors through `s.pt`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

theorem isAlgClosed_residue_of_closed {Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType gY] (y : Y) (hy : IsClosed ({y} : Set Y)) : IsAlgClosed (Y.residueField y) :=
  IsAlgClosed.of_ringEquiv K _ (residueFieldIsoBase gY y hy).symm.commRingCatIsoToRingEquiv

theorem geomPtAt_pt {Y : Scheme.{u}} (y : Y) : (geomPtAt y).pt =
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (SeparableClosure (Y.residueField y)))) ≫
      Y.fromSpecResidueField y := rfl

/-- **Closed points give `K`-rational geometric points.** -/
theorem isIso_geomPtAt {Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gY]
    (y : Y) (hy : IsClosed ({y} : Set Y)) : IsIso ((geomPtAt y).pt ≫ gY) := by
  have := isAlgClosed_residue_of_closed gY y hy
  have hb : IsIso (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (SeparableClosure (Y.residueField y)))) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (algebraMap (Y.residueField y) (SeparableClosure (Y.residueField y)))
    exact ⟨(algebraMap (Y.residueField y) (SeparableClosure (Y.residueField y))).injective,
      IsSepClosed.algebraMap_surjective (Y.residueField y) (SeparableClosure (Y.residueField y))⟩
  have e : (geomPtAt y).pt ≫ gY = Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (SeparableClosure (Y.residueField y)))) ≫
        Spec.map (residueFieldIsoBase gY y hy).inv := by
    rw [SpecMap_residueFieldIsoBase_inv, ← Category.assoc]; rfl
  rw [e]
  have h1 : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (SeparableClosure (Y.residueField y))))) :=
    (inferInstance : IsIso (Spec.map (asIso (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (SeparableClosure (Y.residueField y))))).hom))
  exact IsIso.comp_isIso' h1 inferInstance

variable {S : Scheme.{u}} (gS : S ⟶ Spec (CommRingCat.of K))

omit [IsAlgClosed K] in

/-- The center of a `K`-rational geometric point is closed. -/
theorem isClosed_center (s : GeomPt S) [IsIso (s.pt ≫ gS)] : IsClosed ({s.center} : Set S) := by
  have : IsClosedImmersion s.pt := T3d.isClosedImmersion_of_isIso_comp gS s.pt
  have hr := s.pt.isClosedEmbedding.isClosed_range
  have he : Set.range s.pt = {s.center} := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact congrArg (fun b => s.pt b) (Subsingleton.elim a _)
    · rintro rfl
      exact ⟨_, rfl⟩
  rwa [he] at hr

/-- **Two `K`-rational geometric points with the same center**: `t.pt` factors through `s.pt`. -/
theorem pt_factor_of_center [LocallyOfFiniteType gS] (s t : GeomPt S) [IsIso (s.pt ≫ gS)]
    (hst : t.center = s.center) : t.pt = (t.pt ≫ gS ≫ inv (s.pt ≫ gS)) ≫ s.pt := by
  have hz := isClosed_center gS s
  have e1 := EtMV.pt_factor gS s.center hz s.pt (congrArg (fun b => s.pt b) (Subsingleton.elim _ _))
  have e2 := EtMV.pt_factor gS s.center hz t.pt
    ((congrArg (fun b => t.pt b) (Subsingleton.elim _ _)).trans hst)
  have e3 : inv (s.pt ≫ gS) ≫ s.pt = pointOfClosedPoint gS s.center hz := by
    rw [IsIso.inv_comp_eq]
    exact e1
  rw [Category.assoc, Category.assoc, e3]
  simpa only [Category.assoc] using e2

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_Jac =====
section

/-!
# S4-EtPBC-B, B1: sheaves on schemes of finite type over a field are detected at closed points

For `X` locally of finite type over a field `K` (a Jacobson scheme) and an etale sheaf `F` of `Λ`-modules:
* `isClosed_hom_of_isClosed`: closed points of an etale `X`-object lie over closed points of `X`;
* `supp_eq_empty_of_closed`: if the germ modules `F_x̄` vanish at every closed point, every section has empty
  support (supports are closed, and a nonempty closed set of a Jacobson space has a closed point);
* **`isZero_of_closed`**: then `F = 0`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Topology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {K : Type u} [Field K] {X : Scheme.{u}}
  (gX : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gX]

include gX

/-- Closed points of an etale `X`-object lie over closed points of `X`. -/
theorem isClosed_hom_of_isClosed (T : X.Etale) {t : T.left} (ht : IsClosed ({t} : Set T.left)) :
    IsClosed ({T.hom t} : Set X) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace gX
  have : Etale T.hom := T.prop
  exact Scheme.Hom.closePoints_subset_preimage_closedPoints (Y := X) (T.hom : T.left ⟶ X) ht

/-- If the germ modules vanish at closed points, every section has empty support. -/
theorem supp_eq_empty_of_closed (F : EtSh Λ X) (h : ∀ x : X, IsClosed ({x} : Set X) → IsZero (Mx F x))
    {T : X.Etale} (σ : F.obj.obj (op T)) : supp F σ = ∅ := by
  have : Etale T.hom := T.prop
  have : JacobsonSpace T.left := LocallyOfFiniteType.jacobsonSpace (T.hom ≫ gX)
  by_contra hne
  obtain ⟨t, ht, htc⟩ := nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.2 hne)
    (isClosed_supp F σ).isLocallyClosed
  obtain ⟨y, a, rfl, hy⟩ := ht
  have hyc : IsClosed ({y} : Set X) := by
    have := isClosed_hom_of_isClosed gX T htc
    rwa [fib_over] at this
  have := ModuleCat.subsingleton_of_isZero (h y hyc)
  exact hy (Subsingleton.elim _ _)

/-- **A sheaf whose germ modules vanish at all closed points is zero.** -/
theorem isZero_of_closed (F : EtSh Λ X) (h : ∀ x : X, IsClosed ({x} : Set X) → IsZero (Mx F x)) :
    IsZero F := by
  rw [isZero_iff_stalk]
  intro x
  change IsZero (Mx F x)
  have h0 : ∀ p : ToType (Mx F x), p = 0 := by
    intro p
    obtain ⟨T, a, z, rfl⟩ := (geomPtAt x).point.toPresheafFiber_jointly_surjective p
    exact germ_eq_zero_of_not_mem_supp F z x a
      (by rw [supp_eq_empty_of_closed gX F h z]; exact Set.notMem_empty _)
  exact ModuleCat.isZero_iff_subsingleton.2 ⟨fun p q => (h0 p).trans (h0 q).symm⟩

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_VanA =====
section

/-!
# S4-EtPBC-B, A2: proper base change from vanishing on injectives (effaceability)

Abstract `δ`-functor setting of `Delta`:
* **`Delta.surjAt_of_vanish`**: if base change is surjective on germs in degree `0` for every object and
  `Ext^(q+1)(B, L I) = 0` for every injective `I`, then it is surjective on germs in every degree.

Sheaves (`g : P ⟶ S`, `s` a geometric point of `S`):
* `FibVan Λ g s`: `H^(q+1)(P_s, I|P_s) = 0` for every injective `I` on `P`;
* **`pbc_of_van`**: for `g` universally closed, `BCSurj 0` + `FibVan` give `(R^q g_* F)_s ≃ H^q(P_s, F|P_s)`;
* **`van_of_pbc`**: conversely proper base change gives `FibVan`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {J : Type u₃} [Category.{v₃} J]
  {L : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {A : J ⥤ C} {B : D} {u : ∀ j, B ⟶ L.obj (A.obj j)}

/-- **Surjectivity on germs in all degrees from degree `0` and vanishing on injectives.** -/
theorem surjAt_of_vanish [EnoughInjectives C] (h0 : ∀ F, SurjAt L A B u 0 F)
    (hv : ∀ (I : C) [Injective I] (q : ℕ) (β : Ext B (L.obj I) (q + 1)), β = 0) :
    ∀ (q : ℕ) (F : C), SurjAt L A B u q F
  | 0, F => h0 F
  | q + 1, F => fun β =>
    have ip : InjectivePresentation F := (EnoughInjectives.presentation F).some
    have : Injective ip.J := ip.injective
    exists_bc_of_kill ip.shortExact_shortComplex (surjAt_of_vanish h0 hv q _) β (hv ip.J q _)

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- `H^(q+1)(P_s, I|P_s) = 0` for every injective sheaf `I` on `P`. -/
def FibVan : Prop :=
  ∀ (I : EtSh Λ P) [Injective I] (q : ℕ) (β : H Λ ((pull (fibι g s) Λ).obj I) (q + 1)), β = 0

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_C1 =====
section

/-!
# S4-EtPBC-B, C1: higher direct images of `ι_* ι^* I` along the `P^1`-bundle vanish

For `h = qV K gY : PV K gY ⟶ Y` (`gY = g ≫ gS`), `f = h ≫ g`, a `K`-rational point `s` of `S`, the closed
fibre inclusion `ι : X_s ⟶ X` of `f` and an injective sheaf `I` on `X = PV K gY`:
* `fibMap`, `fibMap_ι`: if `t.pt ≫ g = a ≫ s.pt`, the fibre `X_t` of `h` maps to `X_s` over `X`;
* `pullNIso`: then `ι_t^* ι_* ι^* I ≅ ι_t^* I` (closed counit);
* `isZero_pull_push`: if `g t̄ ≠ s̄`, `ι_t^* ι_* G = 0` (stalks);
* **`rDer_N_isZero`**: `R^(n+1) h_* (ι_* ι^* I) = 0` (closed points of `Y` + `pbc_P1` + Jacobson).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.Z3

universe u

section Fib

variable {Λ : Type u} [CommRing Λ]

variable {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) (s : GeomPt S) (t : GeomPt Y)

section Map

variable (a : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (ha : t.pt ≫ g = a ≫ s.pt)

/-- The fibre map `X_t ⟶ X_s` over `a`. -/
def fibMap : fib h t ⟶ fib (h ≫ g) s :=
  pullback.lift (fibι h t) (pullback.snd h t.pt ≫ a) (by
    rw [Category.assoc, ← ha]
    exact pullback.condition_assoc g)

@[reassoc]
theorem fibMap_ι : fibMap h g s t a ha ≫ fibι (h ≫ g) s = fibι h t := pullback.lift_fst _ _ _

/-- `ι_t^* F ≅ k^* ι^* F`. -/
def pullFibIso (F : EtSh Λ X) : (pull (fibι h t) Λ).obj F ≅
    (pull (fibMap h g s t a ha) Λ).obj ((pull (fibι (h ≫ g) s) Λ).obj F) :=
  eqToIso (by rw [fibMap_ι]) ≪≫ (pullCompIso Λ (fibMap h g s t a ha) (fibι (h ≫ g) s)).app F

variable [IsClosedImmersion (fibι (h ≫ g) s)]

/-- **`ι_t^* ι_* ι^* I ≅ ι_t^* I`** when `X_t` maps to `X_s`. -/
def pullNIso (I : EtSh Λ X) : (pull (fibι h t) Λ).obj
    ((push (fibι (h ≫ g) s) Λ).obj ((pull (fibι (h ≫ g) s) Λ).obj I)) ≅ (pull (fibι h t) Λ).obj I :=
  pullFibIso h g s t a ha _ ≪≫ (pull (fibMap h g s t a ha) Λ).mapIso
    (asIso ((pullAdj (fibι (h ≫ g) s) Λ).counit.app ((pull (fibι (h ≫ g) s) Λ).obj I))) ≪≫
      (pullFibIso h g s t a ha I).symm

end Map

/-- **Off the fibre**: if `g t̄ ≠ s̄`, then `ι_t^* ι_* G = 0`. -/
theorem isZero_pull_push [IsClosedImmersion (fibι (h ≫ g) s)] (hne : g t.center ≠ s.center)
    (G : EtSh Λ (fib (h ≫ g) s)) :
    IsZero ((pull (fibι h t) Λ).obj ((push (fibι (h ≫ g) s) Λ).obj G)) := by
  rw [isZero_iff_stalk]
  intro x
  refine IsZero.of_iso (push_stalk_isZero_of_not_mem Λ (fibι (h ≫ g) s) ((geomPtAt x).map (fibι h t))
    ?_ G) ((pullStalkIso (fibι h t) Λ (geomPtAt x)).app _)
  rintro ⟨z, hz⟩
  rw [GeomPt.center_map, center_geomPtAt] at hz
  have e1 : g (h (fibι (h ≫ g) s z)) = s.center := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact congrArg s.pt (Subsingleton.elim _ _)
  have e2 : h (fibι h t x) = t.center := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact congrArg t.pt (Subsingleton.elim _ _)
  apply hne
  rw [← e2, ← hz, e1]

end Fib

section C1

end C1

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_NatZ =====
section

/-!
# S4-EtPBC-B, C2a: naturality of degree-0 base change, and closed-point isomorphism test

* `sec0Ext_natural`, `stalkBC0_natural`, **`stalkEquiv0_natural`**: the degree-0 stalk base change equivalence
  `(g_* F)_s̄ ≃ H^0(P_s̄, ι^* F)` is natural in `F`;
* **`bijective_stalk_push`**: if `ι^* φ` is an isomorphism, `(g_* φ)_s̄` is bijective (given the degree-0 germ
  conditions); **`bijective_stalk_push_qV`** for `P^1_V ⟶ V` at a `K`-rational point;
* **`isIso_of_closed`**: on `X` locally of finite type over a field, a map of sheaves whose stalk maps at the closed
  points are bijective is an isomorphism (Jacobson).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.Z3

universe u

section Nat

end Nat

section Closed

variable {Λ : Type u} [CommRing Λ] {K : Type u} [Field K] {X : Scheme.{u}}
  (gX : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gX]

include gX in
/-- **Closed-point isomorphism test** (Jacobson). -/
theorem isIso_of_closed {F G : EtSh Λ X} (φ : F ⟶ G)
    (h : ∀ x : X, IsClosed ({x} : Set X) → Function.Bijective (((geomPtAt x).stalkF Λ).map φ).hom) :
    IsIso φ := by
  have hK : IsZero (kernel φ) := isZero_of_closed gX _ fun x hx => by
    change IsZero (((geomPtAt x).stalkF Λ).obj (kernel φ))
    have hm : Function.Injective (((geomPtAt x).stalkF Λ).map (kernel.ι φ)).hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    have e : ((geomPtAt x).stalkF Λ).map (kernel.ι φ) ≫ ((geomPtAt x).stalkF Λ).map φ = 0 := by
      rw [← Functor.map_comp, kernel.condition, Functor.map_zero]
    have ea : ∀ c, (((geomPtAt x).stalkF Λ).map φ).hom
        ((((geomPtAt x).stalkF Λ).map (kernel.ι φ)).hom c) = 0 := fun c => by
      simpa using congrArg (fun χ => χ.hom c) e
    exact ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b => hm ((h x hx).1 (by rw [ea, ea]))⟩
  have hC : IsZero (cokernel φ) := isZero_of_closed gX _ fun x hx => by
    change IsZero (((geomPtAt x).stalkF Λ).obj (cokernel φ))
    have he : Function.Surjective (((geomPtAt x).stalkF Λ).map (cokernel.π φ)).hom :=
      (ModuleCat.epi_iff_surjective _).1 inferInstance
    have h0 : ∀ c : ToType (((geomPtAt x).stalkF Λ).obj (cokernel φ)), c = 0 := fun c => by
      obtain ⟨y, rfl⟩ := he c
      obtain ⟨w, rfl⟩ := (h x hx).2 y
      have e : ((geomPtAt x).stalkF Λ).map φ ≫ ((geomPtAt x).stalkF Λ).map (cokernel.π φ) = 0 := by
        rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
      simpa using congrArg (fun χ => χ.hom w) e
    exact ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b => (h0 a).trans (h0 b).symm⟩
  have := Preadditive.mono_of_isZero_kernel φ hK
  have := Preadditive.epi_of_isZero_cokernel φ hC
  exact isIso_of_mono_of_epi φ

end Closed

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_C2 =====
section

/-!
# S4-EtPBC-B, C2 + C3: fibre vanishing for `P^1_Y ⟶ Y ⟶ S`

`h = qV K gY : X = P^1_Y ⟶ Y` (`gY = g ≫ gS`), `f = h ≫ g`, `s` a `K`-rational point of `S`,
`ι_X : X_s ⟶ X`, `ι_Y : Y_s ⟶ Y`, `h' : X_s ⟶ Y_s`, `N = ι_X* ι_X^* I`:
* `fibCompH`, `fibCompH_ι`, `pushNIso`: `h_* ι_X* G ≅ ι_Y* h'_* G`;
* `isIso_pullFib_unit`, `isIso_pullt_unit`: `ι_t^*` of the unit `I ⟶ N` is an isomorphism if `X_t ⟶ X` factors
  through `X_s`;
* **`isIso_v`**: `ι_Y^* (h_* I) ⟶ ι_Y^* (h_* N)` is an isomorphism (closed points of `Y_s`, `NatZ`);
* **`H_pushN_eq_zero`**: `H^(n+1)(Y, h_* N) = 0` if `g` has fibre vanishing at `s` (`I` injective);
* **`fibVan_comp`** (C3): fibre vanishing for `f = h ≫ g` at `s` (C1 + degenerate Leray + closed pushforward).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.Z3

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) (s : GeomPt S)

/-- The fibre map `h' : X_s ⟶ Y_s`. -/
def fibCompH : fib (h ≫ g) s ⟶ fib g s :=
  pullback.lift (fibι (h ≫ g) s ≫ h) (pullback.snd (h ≫ g) s.pt) (by
    rw [Category.assoc]; exact pullback.condition)

@[reassoc]
theorem fibCompH_ι : fibCompH h g s ≫ fibι g s = fibι (h ≫ g) s ≫ h := pullback.lift_fst _ _ _

/-- `h_* ι_X* G ≅ ι_Y* h'_* G`. -/
def pushNIso (G : EtSh Λ (fib (h ≫ g) s)) : (push h Λ).obj ((push (fibι (h ≫ g) s) Λ).obj G) ≅
    (push (fibι g s) Λ).obj ((push (fibCompH h g s) Λ).obj G) :=
  (pushCompIso Λ (fibι (h ≫ g) s) h).app G ≪≫ eqToIso (by rw [fibCompH_ι]) ≪≫
    ((pushCompIso Λ (fibCompH h g s) (fibι g s)).app G).symm

variable [IsClosedImmersion (fibι (h ≫ g) s)]

theorem isIso_pullFib_unit (I : EtSh Λ X) :
    IsIso ((pull (fibι (h ≫ g) s) Λ).map ((pullAdj (fibι (h ≫ g) s) Λ).unit.app I)) := by
  have e := (pullAdj (fibι (h ≫ g) s) Λ).left_triangle_components I
  rw [IsIso.eq_inv_of_inv_hom_id e]
  infer_instance

theorem isIso_pullt_unit (t : GeomPt Y) (a : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of s.Ω))
    (ha : t.pt ≫ g = a ≫ s.pt) (I : EtSh Λ X) :
    IsIso ((pull (fibι h t) Λ).map ((pullAdj (fibι (h ≫ g) s) Λ).unit.app I)) := by
  have := isIso_pullFib_unit h g s I
  have h2 : IsIso ((pull (fibMap h g s t a ha ≫ fibι (h ≫ g) s) Λ).map
      ((pullAdj (fibι (h ≫ g) s) Λ).unit.app I)) := by
    rw [NatIso.isIso_map_iff (pullCompIso Λ (fibMap h g s t a ha) (fibι (h ≫ g) s))]
    change IsIso ((pull (fibMap h g s t a ha) Λ).map ((pull (fibι (h ≫ g) s) Λ).map _))
    infer_instance
  rwa [fibMap_ι] at h2

end Gen

section V

end V

section C3

end C3

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_Sec =====
section

/-!
# S4-EtPBC-B, C4 part 2: the degree-0 base change unit of a composite

For `f = h ≫ g` and a neighbourhood `j` of `s`, `nbhdPsi : Λ[f⁻¹ V] ⟶ h^* Λ[g⁻¹ V]` and
**`bcUnit_psi`**: `bcUnit f ≫ ιX^*(nbhdPsi) = pullUnit h' ≫ h'^*(bcUnit g) ≫ sqQ` (an identity of global
sections over `X_s`: both are restrictions of `ιX^* h^*` of the tautological section, along two sections
`etId X_s ⟶ ιX⁻¹ h⁻¹ g⁻¹ V` that agree by `etPull3_hom_ext`).
Proofs about the components are term-mode chains: the objects `((etPull f).obj V).left` and
`pullback V.hom f` are only defeq, so `simp`/`rw` with `Category.assoc` do not see through them.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp RamanujanPetersson.EtCompact.PtSec RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.Mate

universe u

section Ext

end Ext

section Comp

theorem nbhdSec_fst_assoc {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) (j : Nbhd s) {W : Scheme.{u}}
    (k : ((etPull g).obj j.1).left ⟶ W) :
    (nbhdSec g s j).left ≫ pullback.fst ((etPull g).obj j.1).hom (fibι g s) ≫ k = fibToNbhd g s j ≫ k :=
  secL_fst_assoc g s j k

/-! Right-associated forms (the lib `_assoc` forms are left-associated). -/

theorem etPullCompIso_inv_fst_r {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (V : C.Etale)
    {W : Scheme.{u}} (k : V.left ⟶ W) :
    ((etPullCompIso g f).inv.app V).left ≫ pullback.fst V.hom (g ≫ f) ≫ k =
      pullback.fst ((etPull f).obj V).hom g ≫ pullback.fst V.hom f ≫ k :=
  (Category.assoc ((etPullCompIso g f).inv.app V).left (pullback.fst V.hom (g ≫ f)) k).symm.trans
    ((eq_whisker (etPullCompIso_inv_fst g f V) k).trans
      (Category.assoc (pullback.fst ((etPull f).obj V).hom g) (pullback.fst V.hom f) k))

theorem etPull_map_left_fst_r {X Y : Scheme.{u}} (f : X ⟶ Y) {V' V : Y.Etale} (m : V' ⟶ V)
    {W : Scheme.{u}} (k : V.left ⟶ W) :
    ((etPull f).map m).left ≫ pullback.fst V.hom f ≫ k = pullback.fst V'.hom f ≫ m.left ≫ k :=
  (Category.assoc ((etPull f).map m).left (pullback.fst V.hom f) k).symm.trans
    ((eq_whisker (etPull_map_left_fst f m) k).trans (Category.assoc (pullback.fst V'.hom f) m.left k))

variable {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) (s : GeomPt S) (j : Nbhd s)

theorem fibCompH_snd : fibCompH h g s ≫ pullback.snd g s.pt = pullback.snd (h ≫ g) s.pt :=
  pullback.lift_snd _ _ _

theorem fibCompH_snd_r {W : Scheme.{u}} (k : Spec (CommRingCat.of s.Ω) ⟶ W) :
    fibCompH h g s ≫ pullback.snd g s.pt ≫ k = pullback.snd (h ≫ g) s.pt ≫ k :=
  (Category.assoc (fibCompH h g s) (pullback.snd g s.pt) k).symm.trans (eq_whisker (fibCompH_snd h g s) k)

end Comp

section SqN

end SqN

section Psi

variable {Λ : Type u} [CommRing Λ]

variable {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) (s : GeomPt S) (j : Nbhd s)

variable (Λ) in
/-- The tautological section of `Λ[g⁻¹ V]`, typed as a section of `nbhdSys` over `g⁻¹ V`. -/
def tautN : ((nbhdSys Λ g s).obj j).obj.obj (op ((etPull g).obj j.1)) := GenAlg.taut Λ ((etPull g).obj j.1)

/-- `Λ[(h ≫ g)⁻¹ V] ⟶ h^* Λ[g⁻¹ V]`. -/
def nbhdPsi : (nbhdSys Λ (h ≫ g) s).obj j ⟶ (pull h Λ).obj ((nbhdSys Λ g s).obj j) :=
  freeMap Λ ((etPullCompIso h g).hom.app j.1) ≫ pullFreeHom Λ h ((etPull g).obj j.1)

theorem freeEquiv_nbhdPsi :
    freeEquiv Λ ((etPull (h ≫ g)).obj j.1) ((pull h Λ).obj ((nbhdSys Λ g s).obj j)) (nbhdPsi h g s j) =
      ((((pull h Λ).obj ((nbhdSys Λ g s).obj j)).obj.map ((etPullCompIso h g).hom.app j.1).op).hom
        (pbSec h (tautN Λ g s j))) := by
  have e1 := freeEquiv_freeMap Λ ((etPullCompIso h g).hom.app j.1) ((pull h Λ).obj ((nbhdSys Λ g s).obj j))
    (pullFreeHom Λ h ((etPull g).obj j.1))
  have e2 : freeEquiv Λ ((etPull h).obj ((etPull g).obj j.1)) ((pull h Λ).obj ((nbhdSys Λ g s).obj j))
      (pullFreeHom Λ h ((etPull g).obj j.1)) =
      pbSec h (tautN Λ g s j) :=
    AddEquiv.apply_symm_apply _ _
  exact e1.trans (congrArg (ModuleCat.Hom.hom (((pull h Λ).obj ((nbhdSys Λ g s).obj j)).obj.map
    ((etPullCompIso h g).hom.app j.1).op)) e2)

theorem unitSec_eq : unitSec Λ g s j =
    pbSec (fibι g s) (tautN Λ g s j) :=
  freeEquiv_unit (Λ := Λ) (fibι g s) ((etPull g).obj j.1)

end Psi

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_Tower =====
section

/-!
# S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line

* `PBCGood Λ g s`: `BCSurj 0` for every sheaf plus fibre vanishing `FibVan`; it gives proper base change
  in all degrees for `g` universally closed (`pbc_of_good`);
* `good_qV`: `P^1_S ⟶ S` (`bcSurj_zero_qV` + `pbc_P1`);
* `good_comp`: `PBCGood g ⟹ PBCGood (P^1_Y ⟶ Y ⟶ S)` for `g` proper (`bcSurj_comp` + `fibVan_comp`);
* `towerP K gS n : Σ Y, Y ⟶ S` is `(P^1)^{n+1}_S` as an iterated `P^1`-bundle; **`pbc_towerP`**: proper
  base change `(R^q f_* F)_s ≃+ H^q(X_s, F|X_s)` for its structure map `f`, at `K`-rational `s`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

section Good

variable (Λ : Type u) [CommRing Λ] {Y S : Scheme.{u}} (g : Y ⟶ S) (s : GeomPt S)

/-- Degree-0 germ surjectivity for all sheaves plus fibre vanishing. -/
def PBCGood : Prop := (∀ G : EtSh Λ Y, BCSurj Λ g s 0 G) ∧ FibVan Λ g s

end Good

section Step

end Step

section Tower

end Tower

section Main

end Main

end RamanujanPetersson.EtPBC

end

end


