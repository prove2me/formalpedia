-- Prove2me | Definitions.Def_RPLib_FX_EtPBCB_003
-- name    : RPLib_FX_EtPBCB_003
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T03:17:02.71893+00:00
-- url     : https://prove2.me/theorems/9e2b88f3-02a4-5633-a564-da9e98d483c1
-- title:
--   Proper base change for iterated projective-line bundles, library file 003
-- statement:
--   File 003 of the proper base change library for iterated projective-line bundles: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_B_DLeray`: S4-EtPBC-B, A1: the degenerate Leray argument (vanishing form)
--   * `S4.Def_RP_EtPBC_B_Sec`: S4-EtPBC-B, C4 part 2: the degree-0 base change unit of a composite
--   * `S4.Def_RP_EtPBC_B_MateB`: S4-EtPBC-B, C4 part 1b: the mate identity
--   * `S4.Def_RP_EtPBC_B_BC0`: S4-EtPBC-B, C4: degree-0 base change surjectivity for `P^1_Y ⟶ Y ⟶ S`
--
--   **Formalization note.** One file of a library formalizing proper base change for iterated projective-line bundles: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the tower $X_0 = \mathbf P^1_S$, $X_{k+1} = \mathbf P^1_{X_k}$ with structure maps $f_k : X_k \to S$ (so $X_n = (\mathbf P^1)^{n+1}_S$) and a $K$-point $s$ of $S$, the stalk of $R^q f_{n*} F$ at $s$ is the étale cohomology $H^q(X_{n,s}, F|_{X_{n,s}})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. It builds on the proper base change library for the projective line (`RPLib_FX_EtPBC_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCB_001
import Definitions.Def_RPLib_FX_EtPBCB_002

/-!
# Proper base change for iterated projective-line bundles, library file 003

Declarations of the formalization of proper base change for the étale cohomology of the iterated
projective-line bundles (P¹)^(n+1)_S → S (geometric stalks of the higher direct images are the étale
cohomology of the geometric fibres), re-hosted declaration by declaration from the library modules
below, on top of the proper base change library for the projective line (RPLib_FX_EtPBC). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_B_DLeray`: S4-EtPBC-B, A1: the degenerate Leray argument (vanishing form)
* `S4.Def_RP_EtPBC_B_Sec`: S4-EtPBC-B, C4 part 2: the degree-0 base change unit of a composite
* `S4.Def_RP_EtPBC_B_MateB`: S4-EtPBC-B, C4 part 1b: the mate identity
* `S4.Def_RP_EtPBC_B_BC0`: S4-EtPBC-B, C4: degree-0 base change surjectivity for `P^1_Y ⟶ Y ⟶ S`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_B_DLeray =====
section

/-!
# S4-EtPBC-B, A1: the degenerate Leray argument (vanishing form)

Generic (`adj : L ⊣ R` between abelian categories, `L` preserving monomorphisms, `P` an injective resolution of
`N`, `R^(n+1) N = 0` for all `n`):
* `pushCx P = R(P)`, `pushCx_exactAt`: exact in degrees `≥ 1`;
* **`pushRes adj P hR`**: `R(P)` is an injective resolution of `R N`;
* **`ext_eq_zero_of_push`**: for `e : L A ≅ B`, `Ext^(n+1)(A, R N) = 0` implies `Ext^(n+1)(B, N) = 0`.
Sheaves: **`H_eq_zero_of_push`**: if `R^(p+1) h_* N = 0` for all `p` and `H^(n+1)(Y, h_* N) = 0`, then
`H^(n+1)(X, N) = 0`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.DLeray

universe w v₁ u₁ v₂ u₂

end RamanujanPetersson.EtPBC.DLeray

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable {Λ : Type u} [CommRing Λ]

/-- **Degenerate Leray for `h_*`, vanishing form.** -/
theorem H_eq_zero_of_push {X Y : AlgebraicGeometry.Scheme.{u}} (h : X ⟶ Y) (N : EtSh Λ X)
    (hR : ∀ n : ℕ, IsZero (((push h Λ).rightDerived (n + 1)).obj N)) (n : ℕ)
    (hA : ∀ α : H Λ ((push h Λ).obj N) (n + 1), α = 0) (β : H Λ N (n + 1)) : β = 0 :=
  DLeray.ext_eq_zero_of_push (pullAdj h Λ) (EtMV.pullUnit Λ h).symm hR n hA β

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

/-! Right-associated forms (the lib `_assoc` forms are left-associated). -/

variable {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) (s : GeomPt S) (j : Nbhd s)

/-- The `U`-component of the section `nbhdSec (h ≫ g) ≫ ιX^*(cmp)`. -/
theorem psiSec_comp :
    (nbhdSec (h ≫ g) s j ≫ (etPull (fibι (h ≫ g) s)).map ((etPullCompIso h g).hom.app j.1)).left ≫
      pullback.fst ((etPull g ⋙ etPull h).obj j.1).hom (fibι (h ≫ g) s) ≫
      pullback.fst ((etPull g).obj j.1).hom h ≫ pullback.fst j.1.hom g =
    pullback.snd (h ≫ g) s.pt ≫ j.2.left :=
  Eq.trans (etComp_left_assoc (nbhdSec (h ≫ g) s j)
      ((etPull (fibι (h ≫ g) s)).map ((etPullCompIso h g).hom.app j.1))
      (pullback.fst ((etPull g ⋙ etPull h).obj j.1).hom (fibι (h ≫ g) s) ≫
        pullback.fst ((etPull g).obj j.1).hom h ≫ pullback.fst j.1.hom g)) <|
  Eq.trans (whisker_eq (nbhdSec (h ≫ g) s j).left (etPull_map_left_fst_assoc (fibι (h ≫ g) s)
      ((etPullCompIso h g).hom.app j.1) (pullback.fst ((etPull g).obj j.1).hom h ≫ pullback.fst j.1.hom g))) <|
  Eq.trans (whisker_eq (nbhdSec (h ≫ g) s j).left
      (whisker_eq (pullback.fst ((etPull (h ≫ g)).obj j.1).hom (fibι (h ≫ g) s))
        (etPullCompIso_hom_fst_fst' h g j.1))) <|
  Eq.trans (nbhdSec_fst_assoc (h ≫ g) s j (pullback.fst j.1.hom (h ≫ g))) (fibToNbhd_fst (h ≫ g) s j)

/-- The `U`-component of the section coming from `pullUnit`, `h'^* nbhdSec g` and `sqN`. -/
theorem sqSec_comp :
    (((((etIdPull (fibCompH h g s)).hom ≫ (etPull (fibCompH h g s)).map (nbhdSec g s j)) ≫
      (etPullCompIso (fibCompH h g s) (fibι g s)).inv.app ((etPull g).obj j.1)) ≫
      etPullCongr (fibCompH_ι h g s) ((etPull g).obj j.1)) ≫
      (etPullCompIso (fibι (h ≫ g) s) h).hom.app ((etPull g).obj j.1)).left ≫
      pullback.fst (((etPull h).obj ((etPull g).obj j.1)).hom) (fibι (h ≫ g) s) ≫
      pullback.fst ((etPull g).obj j.1).hom h ≫ pullback.fst j.1.hom g =
    pullback.snd (h ≫ g) s.pt ≫ j.2.left :=
  Eq.trans (etComp_left_assoc ((((etIdPull (fibCompH h g s)).hom ≫ (etPull (fibCompH h g s)).map (nbhdSec g s j)) ≫
        (etPullCompIso (fibCompH h g s) (fibι g s)).inv.app ((etPull g).obj j.1)) ≫
        etPullCongr (fibCompH_ι h g s) ((etPull g).obj j.1))
      ((etPullCompIso (fibι (h ≫ g) s) h).hom.app ((etPull g).obj j.1))
      (pullback.fst (((etPull h).obj ((etPull g).obj j.1)).hom) (fibι (h ≫ g) s) ≫
        pullback.fst ((etPull g).obj j.1).hom h ≫ (pullback.fst j.1.hom g))) <|
  Eq.trans (whisker_eq ((((etIdPull (fibCompH h g s)).hom ≫ (etPull (fibCompH h g s)).map (nbhdSec g s j)) ≫
        (etPullCompIso (fibCompH h g s) (fibι g s)).inv.app ((etPull g).obj j.1)) ≫
        etPullCongr (fibCompH_ι h g s) ((etPull g).obj j.1)).left
      (etPullCompIso_hom_fst_fst_r (fibι (h ≫ g) s) h ((etPull g).obj j.1) (pullback.fst j.1.hom g))) <|
  Eq.trans (etComp_left_assoc (((etIdPull (fibCompH h g s)).hom ≫ (etPull (fibCompH h g s)).map (nbhdSec g s j)) ≫
        (etPullCompIso (fibCompH h g s) (fibι g s)).inv.app ((etPull g).obj j.1))
      (etPullCongr (fibCompH_ι h g s) ((etPull g).obj j.1))
      (pullback.fst ((etPull g).obj j.1).hom (fibι (h ≫ g) s ≫ h) ≫ (pullback.fst j.1.hom g))) <|
  Eq.trans (whisker_eq (((etIdPull (fibCompH h g s)).hom ≫ (etPull (fibCompH h g s)).map (nbhdSec g s j)) ≫
        (etPullCompIso (fibCompH h g s) (fibι g s)).inv.app ((etPull g).obj j.1)).left
      (etPullCongr_left_fst_r (fibCompH_ι h g s) ((etPull g).obj j.1) (pullback.fst j.1.hom g))) <|
  Eq.trans (etComp_left_assoc ((etIdPull (fibCompH h g s)).hom ≫ (etPull (fibCompH h g s)).map (nbhdSec g s j))
      ((etPullCompIso (fibCompH h g s) (fibι g s)).inv.app ((etPull g).obj j.1))
      (pullback.fst ((etPull g).obj j.1).hom (fibCompH h g s ≫ fibι g s) ≫ (pullback.fst j.1.hom g))) <|
  Eq.trans (whisker_eq ((etIdPull (fibCompH h g s)).hom ≫ (etPull (fibCompH h g s)).map (nbhdSec g s j)).left
      (etPullCompIso_inv_fst_r (fibCompH h g s) (fibι g s) ((etPull g).obj j.1) (pullback.fst j.1.hom g))) <|
  Eq.trans (etComp_left_assoc (etIdPull (fibCompH h g s)).hom ((etPull (fibCompH h g s)).map (nbhdSec g s j))
      (pullback.fst ((etPull (fibι g s)).obj ((etPull g).obj j.1)).hom (fibCompH h g s) ≫
        pullback.fst ((etPull g).obj j.1).hom (fibι g s) ≫ (pullback.fst j.1.hom g))) <|
  Eq.trans (whisker_eq (etIdPull (fibCompH h g s)).hom.left
      (etPull_map_left_fst_r (fibCompH h g s) (nbhdSec g s j) (pullback.fst ((etPull g).obj j.1).hom (fibι g s) ≫ (pullback.fst j.1.hom g)))) <|
  Eq.trans (whisker_eq (etIdPull (fibCompH h g s)).hom.left
      (whisker_eq (pullback.fst (etId (fib g s)).hom (fibCompH h g s)) (nbhdSec_fst_assoc g s j (pullback.fst j.1.hom g)))) <|
  Eq.trans (whisker_eq (etIdPull (fibCompH h g s)).hom.left
      (whisker_eq (pullback.fst (etId (fib g s)).hom (fibCompH h g s)) (fibToNbhd_fst g s j))) <|
  Eq.trans (etIdPull_hom_left_fst_r (fibCompH h g s) (pullback.snd g s.pt ≫ j.2.left))
    (fibCompH_snd_r h g s j.2.left)

/-- The two sections `etId X_s ⟶ ιX⁻¹ h⁻¹ g⁻¹ V` agree. -/
theorem psiSec_eq :
    nbhdSec (h ≫ g) s j ≫ (etPull (fibι (h ≫ g) s)).map ((etPullCompIso h g).hom.app j.1) =
    ((((etIdPull (fibCompH h g s)).hom ≫ (etPull (fibCompH h g s)).map (nbhdSec g s j)) ≫
      (etPullCompIso (fibCompH h g s) (fibι g s)).inv.app ((etPull g).obj j.1)) ≫
      etPullCongr (fibCompH_ι h g s) ((etPull g).obj j.1)) ≫
      (etPullCompIso (fibι (h ≫ g) s) h).hom.app ((etPull g).obj j.1) :=
  etPull3_hom_ext (fibι (h ≫ g) s) h g j.1 ((psiSec_comp h g s j).trans (sqSec_comp h g s j).symm)

end Comp

section SqN

variable {Λ : Type u} [CommRing Λ] {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y)
  (h' : Xs ⟶ Ys) (w : h' ≫ ιY = ιX ≫ h)

theorem sqN_eq (F : EtSh Λ Y) : sqN ιX ιY h h' w F = (sqQ ιX ιY h h' w).hom.app F :=
  (sqQ_hom_app ιX ιY h h' w F).symm

end SqN

section Psi

variable {Λ : Type u} [CommRing Λ]

variable {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) (s : GeomPt S) (j : Nbhd s)

theorem sc_psi :
    sc (bcUnit Λ (h ≫ g) s j ≫ (pull (fibι (h ≫ g) s) Λ).map (nbhdPsi h g s j)) (etId (fib (h ≫ g) s)) =
      ((((pull (fibι (h ≫ g) s) Λ).obj ((pull h Λ).obj ((nbhdSys Λ g s).obj j))).obj.map
        (nbhdSec (h ≫ g) s j ≫ (etPull (fibι (h ≫ g) s)).map ((etPullCompIso h g).hom.app j.1)).op).hom
        (pbSec (fibι (h ≫ g) s)
          (pbSec h (tautN Λ g s j)))) := by
  rw [sc_bcUnit_comp, freeEquiv_nbhdPsi, unit_pbSec, pbSec_restrict, mapMapApply]

theorem sc_unit_bc :
    sc ((pullUnit Λ (fibCompH h g s)).hom ≫ (pull (fibCompH h g s) Λ).map (bcUnit Λ g s j))
        (etId (fib (h ≫ g) s)) =
      ((((pull (fibCompH h g s) Λ).obj ((pull (fibι g s) Λ).obj ((nbhdSys Λ g s).obj j))).obj.map
        ((etIdPull (fibCompH h g s)).hom ≫ (etPull (fibCompH h g s)).map (nbhdSec g s j)).op).hom
        (pbSec (fibCompH h g s)
          (pbSec (fibι g s) (tautN Λ g s j)))) := by
  have s1 : sc (pullUnit Λ (fibCompH h g s)).hom (etId (fib (h ≫ g) s)) =
      ((((pull (fibCompH h g s) Λ).obj (unitSh Λ (fib g s))).obj.map
        (etIdPull (fibCompH h g s)).hom.op).hom (pbSec (fibCompH h g s) (oneSec Λ (fib g s)))) :=
    pullUnit_one (Λ := Λ) (fibCompH h g s)
  have s2 : (((bcUnit Λ g s j).hom.app (op (etId (fib g s)))).hom (oneSec Λ (fib g s))) =
      fibSec Λ g s j := sc_ofSec (fibSec Λ g s j)
  rw [sc_comp, s1, pullMap_pbSec, s2, fibSec, unitSec_eq, pbSec_restrict, mapMapApply]

/-- **The base change unit of `h ≫ g` through that of `g`** (nested-typed `sqN`). -/
theorem bcUnit_psiN :
    bcUnit Λ (h ≫ g) s j ≫ (pull (fibι (h ≫ g) s) Λ).map (nbhdPsi h g s j) =
      (pullUnit Λ (fibCompH h g s)).hom ≫ (pull (fibCompH h g s) Λ).map (bcUnit Λ g s j) ≫
        sqN (fibι (h ≫ g) s) (fibι g s) h (fibCompH h g s) (fibCompH_ι h g s) ((nbhdSys Λ g s).obj j) := by
  refine (ofSec_sc _).symm.trans ((congrArg ofSec ?_).trans (ofSec_sc _))
  rw [sc_psi, ← Category.assoc (pullUnit Λ (fibCompH h g s)).hom, sc_comp, sc_unit_bc, sqN_pbSec]
  exact map_congr_apply _ (congrArg Quiver.Hom.op (psiSec_eq h g s j)) _

/-- **The base change unit of `h ≫ g` through that of `g`.** -/
theorem bcUnit_psi :
    bcUnit Λ (h ≫ g) s j ≫ (pull (fibι (h ≫ g) s) Λ).map (nbhdPsi h g s j) =
      (pullUnit Λ (fibCompH h g s)).hom ≫ (pull (fibCompH h g s) Λ).map (bcUnit Λ g s j) ≫
        (sqQ (fibι (h ≫ g) s) (fibι g s) h (fibCompH h g s) (fibCompH_ι h g s)).hom.app
          ((nbhdSys Λ g s).obj j) := by
  rw [← sqN_eq]
  exact bcUnit_psiN h g s j

end Psi

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_MateB =====
section

/-!
# S4-EtPBC-B, C4 part 1b: the mate identity

Kernel note: `sqQ.hom.app` must only ever be applied to one spelling of an object (`(push h).obj
((push ιX).obj M)` versus `(push ιX ⋙ push h).obj M` makes the kernel unfold `pullCompIso`), so the
components of `pushCompIso` and of the unit are used through the nested-typed `pc` and `unitN`.
* `sq_counit`: `h'^* ιY^*(sqP) ≫ h'^*(ε_{ιY}) ≫ ε_{h'} = sqQ ≫ ιX^*(ε_h) ≫ ε_{ιX}`;
* `vMapG G : ιY^* h_* G ⟶ h'_* ιX^* G` and **`mateG`**: `h'^*(vMapG G) ≫ ε_{h'} = sqQ ≫ ιX^*(ε_h G)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.Mate

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ]

section Sq

variable {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y) (h' : Xs ⟶ Ys)
  (w : h' ≫ ιY = ιX ≫ h)

theorem sq_counit (M : EtSh Λ Xs) :
    (pull h' Λ).map ((pull ιY Λ).map (sqP ιX ιY h h' w M).hom) ≫
      (pull h' Λ).map ((pullAdj ιY Λ).counit.app ((push h' Λ).obj M)) ≫ (pullAdj h' Λ).counit.app M =
    (sqQ ιX ιY h h' w).hom.app ((push h Λ).obj ((push ιX Λ).obj M)) ≫
      (pull ιX Λ).map ((pullAdj h Λ).counit.app ((push ιX Λ).obj M)) ≫ (pullAdj ιX Λ).counit.app M := by
  have p : (push (ιX ≫ h) Λ).obj M = (push (h' ≫ ιY) Λ).obj M := by rw [w]
  have eP : (sqP ιX ιY h h' w M).hom = (pc ιX h M).hom ≫ eqToHom p ≫
      (pushCompIso Λ h' ιY).inv.app M := rfl
  rw [eP]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [sq_tail ιX ιY h h' w M p, ← pullComp_counit ιX h M, ← sqQ_hom_app_assoc]
  have n5 := (sqQ ιX ιY h h' w).hom.naturality (pc ιX h M).hom
  simp only [Functor.comp_map] at n5
  have n6 : (pull ιX Λ).map ((pull h Λ).map (pc ιX h M).hom) ≫
      (pull ιX Λ).map ((pull h Λ).map ((pushCompIso Λ ιX h).inv.app M)) = 𝟙 _ := by
    simp only [← CategoryTheory.Functor.map_comp]
    rw [show (pc ιX h M).hom ≫ (pushCompIso Λ ιX h).inv.app M = 𝟙 _ from
      (pushCompIso Λ ιX h).hom_inv_id_app M]
    simp only [CategoryTheory.Functor.map_id]
  rw [reassoc_of% n5, reassoc_of% n6]

/-- The base change map `ιY^* h_* G ⟶ h'_* ιX^* G` (through `N = ιX_* ιX^* G`). -/
def vMapG (G : EtSh Λ X) : (pull ιY Λ).obj ((push h Λ).obj G) ⟶ (push h' Λ).obj ((pull ιX Λ).obj G) :=
  (pull ιY Λ).map ((push h Λ).map (unitN ιX G) ≫ (sqP ιX ιY h h' w ((pull ιX Λ).obj G)).hom) ≫
    (pullAdj ιY Λ).counit.app _

/-- **The mate identity** `h'^*(vMapG G) ≫ ε_{h'} = sqQ ≫ ιX^*(ε_h G)`. -/
theorem mateG (G : EtSh Λ X) :
    (pull h' Λ).map (vMapG ιX ιY h h' w G) ≫ (pullAdj h' Λ).counit.app ((pull ιX Λ).obj G) =
      (sqQ ιX ιY h h' w).hom.app ((push h Λ).obj G) ≫ (pull ιX Λ).map ((pullAdj h Λ).counit.app G) := by
  have e1 := sq_counit ιX ιY h h' w ((pull ιX Λ).obj G)
  simp only [vMapG, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [e1]
  have n := (sqQ ιX ιY h h' w).hom.naturality ((push h Λ).map (unitN ιX G))
  simp only [Functor.comp_map] at n
  have n2 := (pullAdj h Λ).counit_naturality (unitN ιX G)
  rw [reassoc_of% n, ← CategoryTheory.Functor.map_comp_assoc, n2, CategoryTheory.Functor.map_comp_assoc,
    unitN_triangle, Category.comp_id]

end Sq

end RamanujanPetersson.EtPBC.Mate

end

end

-- ===== S4.Def_RP_EtPBC_B_BC0 =====
section

/-!
# S4-EtPBC-B, C4: degree-0 base change surjectivity for `P^1_Y ⟶ Y ⟶ S`

* `bcSurj_comp_of_iso`: for `f = h ≫ g`, if the base change map `vMapG : ιY^* h_* I ⟶ h'_* ιX^* I` is an
  isomorphism and `BCSurj 0` holds for `g` at `h_* I`, then `BCSurj 0` holds for `f` at `I`
  (`bcUnit_psi` + naturality of `sqQ` + the mate identity `mateG`);
* `isIso_vMap_qV`: `vMapG` is an isomorphism for `h = qV K (g ≫ gS)` (`isIso_v`);
* **`bcSurj_comp`**: `BCSurj 0` for `qV K (g ≫ gS) ≫ g` from `BCSurj 0` for `g` (all sheaves, via an
  injective envelope and `bcSurj_of_mono`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.Mate RamanujanPetersson.EtPBC.Z3

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) (s : GeomPt S)

/-- **`BCSurj 0` for a composite** from `BCSurj 0` for `g` at `h_* I` and an invertible `vMapG`. -/
theorem bcSurj_comp_of_iso (I : EtSh Λ X)
    [IsIso (vMapG (fibι (h ≫ g) s) (fibι g s) h (fibCompH h g s) (fibCompH_ι h g s) I)]
    (hg : BCSurj Λ g s 0 ((push h Λ).obj I)) : BCSurj Λ (h ≫ g) s 0 I := by
  apply bcSurj_zero_of_hom (h ≫ g) s
  intro b
  obtain ⟨j, φ', hφ'⟩ := hom_of_bcSurj_zero g s hg
    ((pullAdj (fibCompH h g s) Λ).homEquiv _ _ ((pullUnit Λ (fibCompH h g s)).inv ≫ b) ≫
      inv (vMapG (fibι (h ≫ g) s) (fibι g s) h (fibCompH h g s) (fibCompH_ι h g s) I))
  refine ⟨j, nbhdPsi h g s j ≫ (pull h Λ).map φ' ≫ (pullAdj h Λ).counit.app I, ?_⟩
  have key : bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map φ' ≫
      vMapG (fibι (h ≫ g) s) (fibι g s) h (fibCompH h g s) (fibCompH_ι h g s) I =
      (pullAdj (fibCompH h g s) Λ).homEquiv _ _ ((pullUnit Λ (fibCompH h g s)).inv ≫ b) := by
    rw [reassoc_of% hφ', IsIso.inv_hom_id, Category.comp_id]
  have key' : (pull (fibCompH h g s) Λ).map (bcUnit Λ g s j) ≫
      (pull (fibCompH h g s) Λ).map ((pull (fibι g s) Λ).map φ') ≫
      (pull (fibCompH h g s) Λ).map
        (vMapG (fibι (h ≫ g) s) (fibι g s) h (fibCompH h g s) (fibCompH_ι h g s) I) =
      (pull (fibCompH h g s) Λ).map
        ((pullAdj (fibCompH h g s) Λ).homEquiv _ _ ((pullUnit Λ (fibCompH h g s)).inv ≫ b)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, key]
  have k2 : (pull (fibCompH h g s) Λ).map
        ((pullAdj (fibCompH h g s) Λ).homEquiv _ _ ((pullUnit Λ (fibCompH h g s)).inv ≫ b)) ≫
      (pullAdj (fibCompH h g s) Λ).counit.app ((pull (fibι (h ≫ g) s) Λ).obj I) =
      (pullUnit Λ (fibCompH h g s)).inv ≫ b :=
    ((pullAdj (fibCompH h g s) Λ).homEquiv_counit _ _ _).symm.trans (Equiv.symm_apply_apply _ _)
  have nq := (sqQ (fibι (h ≫ g) s) (fibι g s) h (fibCompH h g s) (fibCompH_ι h g s)).hom.naturality φ'
  simp only [Functor.comp_map] at nq
  simp only [CategoryTheory.Functor.map_comp]
  rw [reassoc_of% (bcUnit_psi h g s j), ← reassoc_of% nq,
    ← mateG (fibι (h ≫ g) s) (fibι g s) h (fibCompH h g s) (fibCompH_ι h g s) I,
    reassoc_of% key', k2, Iso.hom_inv_id_assoc]

end Gen

section P1

end P1

end RamanujanPetersson.EtPBC

end

end


