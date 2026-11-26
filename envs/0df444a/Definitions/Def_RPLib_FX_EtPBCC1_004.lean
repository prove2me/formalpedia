-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC1_004
-- name    : RPLib_FX_EtPBCC1_004
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T18:47:07.118101+00:00
-- url     : https://prove2.me/theorems/7115ad45-d5e3-572c-9e37-5184d7eccbd9
-- title:
--   Proper base change with compact supports, library file 004
-- statement:
--   File 004 of the library for proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Coh`: S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf
--   * `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
--   * `S4.Def_RP_EtPBC_C1_Mor`: S4-EtPBC-C1, part 3: the base change morphism `g^* R^q f_! F ⟶ R^q f'_! g'^* F`
--   * `S4.Def_RP_EtPBC_C1_StkHom`: S4-EtPBC-C1, part 12: a cocycle class in the stalk of `R^(p+1) g_* F`
--   * `S4.Def_RP_EtPBC_C1_PsiCore`: S4-EtPBC-C1, part 14c: the cocycle-level comparison `psi_core`
--   * `S4.Def_RP_EtPBC_C1_Psi0a`: S4-EtPBC-C1, part 18a: degree `0` on germs
--   * `S4.Def_RP_EtPBC_C1_PbcG`: S4-EtPBC-C1, part 20a: the named equivalence `pbcEquiv` in every degree
--
--   **Formalization note.** One file of a library formalizing the canonical proper base change isomorphism for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ proper), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and a geometric point $s$ of $S$ at which $\bar f$ satisfies proper base change, the stalk $(R^q f_! F)_s$ is identified with $H^q_c(X_s, F|_{X_s})$ by a named isomorphism that is natural in the sheaf $F$ of $\Lambda$-modules (built from the base change morphism of the fibre square). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`) and for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_002
import Definitions.Def_RPLib_FX_EtPBCC1_003

/-!
# Proper base change with compact supports, library file 004

Declarations of the formalization of the canonical proper base change isomorphism for compactly
supported étale cohomology (R^q f_! F)_s ≃ H^q_c(X_s, F|X_s), natural in F, for compactified X ⟶ S
(the base change morphism, its stalk form and its naturality), re-hosted declaration by declaration
from the library modules below, on top of the proper base change libraries RPLib_FX_EtPBC and
RPLib_FX_EtPBCB (projective line and iterated projective-line bundles). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Coh`: S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf
* `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
* `S4.Def_RP_EtPBC_C1_Mor`: S4-EtPBC-C1, part 3: the base change morphism `g^* R^q f_! F ⟶ R^q f'_! g'^* F`
* `S4.Def_RP_EtPBC_C1_StkHom`: S4-EtPBC-C1, part 12: a cocycle class in the stalk of `R^(p+1) g_* F`
* `S4.Def_RP_EtPBC_C1_PsiCore`: S4-EtPBC-C1, part 14c: the cocycle-level comparison `psi_core`
* `S4.Def_RP_EtPBC_C1_Psi0a`: S4-EtPBC-C1, part 18a: degree `0` on germs
* `S4.Def_RP_EtPBC_C1_PbcG`: S4-EtPBC-C1, part 20a: the named equivalence `pbcEquiv` in every degree
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_Coh =====
section

/-!
# S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf

`H Λ F n := Ext^n(Λ_X, F)` in `EtSh Λ X` (a Grothendieck abelian category, so `Ext` exists and
there are enough injectives). Long exact sequences in `F` are Mathlib's
`Ext.covariant_sequence_exact₁/₂/₃` (E0Probe amendment A7).

Comparisons (via `extAdjEquiv`):
* `closedH`: for a closed immersion `i : Z ⟶ X`, `H^n(X, i_* G) ≃ H^n(Z, G)`;
* `openH`: for an open immersion `j : U ⟶ X`, `Ext^n_X(j_! Λ_U, F) ≃ H^n(U, F|_U)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe w v u

section ExtIso

end ExtIso

variable (Λ : Type u) [CommRing Λ]

theorem Hmap_apply {X : Scheme.{u}} {F G : EtSh Λ X} (φ : F ⟶ G) (n : ℕ) (x : H Λ F n) :
    Hmap Λ φ n x = x.comp (Ext.mk₀ φ) (add_zero n) :=
  rfl

section Closed

end Closed

section Open

end Open

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Exc =====
section

/-!
# S4-EtCompact, part 5: the excision sequence (compact supports, subset model)

On an ambient scheme `P` (the compactification), cohomology with compact supports of the
locally closed set `W ∩ Vᶜ` (`W, V` open) is `HcWV W V F n := H^n(P, cutWV W V F)`.
For opens `V ≤ V'` the set `S = W ∩ Vᶜ` splits into the relatively open `U = (W ⊓ V') ∩ Vᶜ`
and the relatively closed `Z = W ∩ V'ᶜ`, and
`0 ⟶ cutWV (W ⊓ V') V F ⟶ cutWV W V F ⟶ cutWV W V' F ⟶ 0`
is short exact (checked on stalks). Hence the **excision long exact sequence**
`… ⟶ H^n_c(U) ⟶ H^n_c(S) ⟶ H^n_c(Z) ⟶ H^(n+1)_c(U) ⟶ …` (E0Probe P2a).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

variable {Λ} (W : X.Opens) {V V' : X.Opens} (h : V ≤ V') (F : EtSh Λ X)

theorem excComplex_g : (excComplex W h F).g = openCutMap W (quotCutLe h F) :=
  rfl

end RamanujanPetersson.EtCompact

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

variable {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y) (h' : Xs ⟶ Ys)
  (w : h' ≫ ιY = ιX ≫ h)

@[reassoc]
theorem bcMorSq_natural (q : ℕ) {G G' : EtSh Λ X} (φ : G ⟶ G') :
    (pull ιY Λ).map (((push h Λ).rightDerived q).map φ) ≫ bcMorSq Λ ιX ιY h h' w q G' =
      bcMorSq Λ ιX ιY h h' w q G ≫ ((push h' Λ).rightDerived q).map ((pull ιX Λ).map φ) :=
  bcMorGen_natural _ _ _ _ _ q φ

end Sq

section Closed

end Closed

section It

end It

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_StkHom =====
section

/-!
# S4-EtPBC-C1, part 12: a cocycle class in the stalk of `R^(p+1) g_* F`

For a complex `K` of etale sheaves on `P`, `g : P ⟶ S`, `V : S.Etale` and a cycle `cyc` of the section complex
`K(g⁻¹ V)` in degree `p + 1`:
* `freeCoc cyc : Λ[V] ⟶ (g_* K)^(p+1)` (the cocycle as a map from the free sheaf) and
  **`cocCls cyc : Λ[V] ⟶ H^(p+1)(g_* K)`** (its class);
* **`stalkHom_germ`**: `stalkHomologyIso` sends the germ of `cocCls cyc (taut)` to the germ of `[cyc]`;
* `stalkSec_germ_taut`: `stalkSec (germ μ(taut)) = ptUnit ≫ s^* μ`;
* **`stalkSec_rd`**: for `K = I^•`, `stalkSec (stalkRDIso⁻¹ (germ [cyc])) = ptUnit ≫ s^*(cocCls cyc ≫ isoRD⁻¹)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.PtSec RamanujanPetersson.EtCompact.Supp RamanujanPetersson.EtPBC.GenAlg
  RamanujanPetersson.EtCompact.GalTrE

universe u

section Gen

end Gen

set_option backward.isDefEq.respectTransparency false

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)
  (K : CochainComplex (EtSh Λ P) ℕ) (p : ℕ) {V : S.Etale}

/-- **`stalkSec (stalkRDIso⁻¹ (germ [cyc])) = ptUnit ≫ s^*(cocCls cyc ≫ isoRD⁻¹)`**. -/
theorem stalkSec_rd {F : EtSh Λ P} (I : InjectiveResolution F) (v : s.point.fiber.obj V)
    (cyc : ((secCx Λ I.cocomplex ((etPull g).obj V)).sc (p + 1)).cycles) :
    stalkSec s (((push g Λ).rightDerived (p + 1)).obj F) ((stalkRDIso Λ g s I (p + 1)).inv.hom
        ((s.point.toPresheafFiber V v ((preCx Λ g I.cocomplex).homology (p + 1))).hom
          ((preHomologyObjIso Λ g I.cocomplex (p + 1) V).inv.hom
            (((secCx Λ I.cocomplex ((etPull g).obj V)).sc (p + 1)).homologyπ.hom cyc)))) =
      ptUnit s V v ≫ (pull s.pt Λ).map (cocCls g I.cocomplex p cyc ≫ (I.isoRightDerivedObj (push g Λ) (p + 1)).inv) := by
  rw [← stalkHom_germ g s I.cocomplex p v cyc]
  have e : (stalkRDIso Λ g s I (p + 1)).inv = (stalkHomologyIso Λ g s I.cocomplex (p + 1)).inv ≫
      (s.stalkF Λ).map (I.isoRightDerivedObj (push g Λ) (p + 1)).inv := rfl
  have e2 : ∀ x, (stalkRDIso Λ g s I (p + 1)).inv.hom ((stalkHomologyIso Λ g s I.cocomplex (p + 1)).hom.hom x) =
      ((s.stalkF Λ).map (I.isoRightDerivedObj (push g Λ) (p + 1)).inv).hom x := by
    intro x
    have e3 : (stalkHomologyIso Λ g s I.cocomplex (p + 1)).inv.hom
        ((stalkHomologyIso Λ g s I.cocomplex (p + 1)).hom.hom x) = x := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id, ModuleCat.hom_id, LinearMap.id_apply]
    rw [e]
    exact congrArg (((s.stalkF Λ).map (I.isoRightDerivedObj (push g Λ) (p + 1)).inv).hom) e3
  rw [e2, stalkSec_natural]
  refine (congrArg (fun m => m ≫ (pull s.pt Λ).map (I.isoRightDerivedObj (push g Λ) (p + 1)).inv)
    (stalkSec_germ_taut v (cocCls g I.cocomplex p cyc))).trans ?_
  simp only [Functor.map_comp, Category.assoc]

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_PsiCore =====
section

/-!
# S4-EtPBC-C1, part 14c: the cocycle-level comparison `psi_core`

* `psi_core`: for a section cocycle `cyc` over a neighbourhood `j` of `s`, `absRelGen` of the class
  `J.extMk (u_j ≫ ι^* ĉ ≫ lift)` is `ptUnit ≫ s^*([cyc] ≫ isoRD⁻¹) ≫ bcMorRes`.

Kernel note: `psi_core` instantiates `glue3` and `coc_gen` with the fibre written uniformly as `fib g s`
(named arguments `(X := fib g s)`), and lets the hypothesis of `glue3` be unified, so that the kernel sees
syntactically equal terms (mixing `fib g s` with `pullback g s.pt` made the kernel unfold `bcCell`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec

universe u

set_option backward.isDefEq.respectTransparency false

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) {F : EtSh Λ P}
  (I : InjectiveResolution F) (J : InjectiveResolution ((pull (fibι g s) Λ).obj F)) (p : ℕ)

/-- The comparison on the cocycle level: `glue3` for the fibre square with the hypothesis from `coc_gen`. -/
theorem psi_core (j : Nbhd s) (cyc : ((secCx Λ I.cocomplex ((etPull g).obj j.1)).sc (p + 1)).cycles) :
    haveI := unitSh_projective_spec s.Ω Λ
    absRelGen (pullAdj (X := fib g s) (pullback.snd g s.pt) Λ) (pullUnit (X := fib g s) Λ (pullback.snd g s.pt)).symm
        J p (J.extMk (bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map (freeCocP g I p cyc) ≫
          (liftLc (pull (fibι g s) Λ) I J).f (p + 1)) (p + 1 + 1) rfl (freeCocP_cond g s I J p j cyc)) ≫
        (J.isoRightDerivedObj (push (X := fib g s) (pullback.snd g s.pt) Λ) (p + 1)).inv =
      (ptUnit s j.1 j.2 ≫ (pull s.pt Λ).map (cocCls g I.cocomplex p cyc ≫
          (I.isoRightDerivedObj (push g Λ) (p + 1)).inv)) ≫
        bcMorRes (push g Λ) (push (X := fib g s) (pullback.snd g s.pt) Λ) (pull (fibι g s) Λ) (pull s.pt Λ)
          (bcCell Λ (fibι g s) s.pt g (pullback.snd g s.pt) (pullback.condition (f := g) (g := s.pt)).symm)
          (p + 1) I J := by
  have := unitSh_projective_spec s.Ω Λ
  refine glue3 (push g Λ) (push (X := fib g s) (pullback.snd g s.pt) Λ) (pull (fibι g s) Λ) (pull s.pt Λ)
    (bcCell Λ (fibι g s) s.pt g (pullback.snd g s.pt) (pullback.condition (f := g) (g := s.pt)).symm)
    (pullAdj (X := fib g s) (pullback.snd g s.pt) Λ) (pullUnit (X := fib g s) Λ (pullback.snd g s.pt)) p I J
    (ptUnit s j.1 j.2) (freeCoc g I.cocomplex p cyc) (freeCoc_d g I.cocomplex p cyc)
    (bcUnit Λ g s j) (freeCocP g I p cyc) ?H _ ?hfu (freeCocP_cond g s I J p j cyc) _ ?hm
  case H =>
    refine coc_gen (fibι g s) s.pt g (pullback.snd g s.pt) (pullback.condition (f := g) (g := s.pt)).symm _ j.1 ?c
      (ptSec s j.1 j.2) (nbhdSec g s j) (ptSec_kappa g s j) _ ?ha _ ?hb
    case c => exact ((secCx Λ I.cocomplex ((etPull g).obj j.1)).sc (p + 1)).iCycles.hom cyc
    case ha =>
      rw [sc_ptUnit_comp, freeCoc]
      erw [RamanujanPetersson.EtCompact.GalTrE.freeEquiv_symm_taut]
    case hb =>
      rw [sc_bcUnit_comp, unit_pbSec, freeCocP]
      erw [AddEquiv.apply_symm_apply]
      rfl
  case hfu => rfl
  case hm => rfl

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_Psi0a =====
section

/-!
# S4-EtPBC-C1, part 18a: degree `0` on germs

For `g : P ⟶ S`, a geometric point `s` and `F` on `P`, with `ι : P_s ⟶ P`, `π : P_s ⟶ Spec Ω`:
* `coc0`: the cochain identity `ptUnit ≫ s^* ẑ ≫ bcCell = homEquiv (u_j ≫ ι^* ẑ)` for a section `z` of `g_* F`
  (in the uniform `(X := fib g s)` form);
* `pbc0_germ`: `pbcEquivZero` of the germ of `z` is `mk₀ (u_j ≫ ι^* ẑ)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec RamanujanPetersson.EtCompact.GalTrE

universe u

set_option backward.isDefEq.respectTransparency false

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) (F : EtSh Λ P)

/-- The degree-`0` cochain identity for the fibre square (uniform `(X := fib g s)` form). -/
theorem coc0 (j : Nbhd s) (z : ((push g Λ).obj F).obj.obj (op j.1)) :
    (ptUnit s j.1 j.2 ≫ (pull s.pt Λ).map ((freeEquiv Λ j.1 ((push g Λ).obj F)).symm z)) ≫
        (bcCell Λ (fibι g s) s.pt g (pullback.snd g s.pt) (pullback.condition (f := g) (g := s.pt)).symm).app F =
      (pullAdj (X := fib g s) (pullback.snd g s.pt) Λ).homEquiv _ _
        ((pullUnit (X := fib g s) Λ (pullback.snd g s.pt)).inv ≫
          (bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map ((freeEquiv Λ ((etPull g).obj j.1) F).symm z))) := by
  refine coc_gen (fibι g s) s.pt g (pullback.snd g s.pt) (pullback.condition (f := g) (g := s.pt)).symm F j.1 z
    (ptSec s j.1 j.2) (nbhdSec g s j) (ptSec_kappa g s j) _ ?ha _ ?hb
  case ha =>
    rw [sc_ptUnit_comp]
    erw [freeEquiv_symm_taut]
  case hb =>
    rw [sc_bcUnit_comp, unit_pbSec]
    erw [AddEquiv.apply_symm_apply]

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_PbcG =====
section

/-!
# S4-EtPBC-C1, part 20a: the named equivalence `pbcEquiv` in every degree

* `bcSurj_of_good`, `bcInj_of_good`: `PBCGood` gives the hypotheses of `pbcEquivZero` / `pbcEquivS` in every degree;
* **`pbcEquiv g s hg F q : (R^q g_* F)_s ≃+ H^q(P_s, ι^* F)`** (named; `pbcEquivZero` in degree `0`, `pbcEquivS` in
  degrees `p + 1`, by the equation lemmas of `pbcEquiv`) and **`pbcEquiv_natural`** (naturality in `F`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact

universe u

set_option backward.isDefEq.respectTransparency false

section Good

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) [UniversallyClosed g]

/-- **`pbcEquiv g s hg F q : (R^q g_* F)_s ≃+ H^q(P_s, ι^* F)`**, the named proper-base-change equivalence in every
degree (`pbcEquivZero` in degree `0`, `pbcEquivS` in degrees `p + 1`). -/
def pbcEquiv (hg : PBCGood Λ g s) (F : EtSh Λ P) :
    (q : ℕ) → (ToType ((s.stalkF Λ).obj (((push g Λ).rightDerived q).obj F)) ≃+ H Λ ((pull (fibι g s) Λ).obj F) q)
  | 0 => pbcEquivZero Λ g s F (bcInj_of_good g s hg 0 F) (bcSurj_of_good g s hg 0 F)
  | p + 1 => pbcEquivS g s F p (bcInj_of_good g s hg (p + 1) F) (bcSurj_of_good g s hg (p + 1) F)

end Good

end RamanujanPetersson.EtPBC.C1

end

end


