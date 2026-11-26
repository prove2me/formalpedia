-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC1_002
-- name    : RPLib_FX_EtPBCC1_002
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T18:40:36.654825+00:00
-- url     : https://prove2.me/theorems/58fc6ab5-29d8-5da5-9a0a-c78e81ccfd53
-- title:
--   Proper base change with compact supports, library file 002
-- statement:
--   File 002 of the library for proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_C1_Psi0a`: S4-EtPBC-C1, part 18a: degree `0` on germs
--   * `S4.Def_RP_EtPBC_C1_NatF`: S4-EtPBC-C1, part 19: naturality in `F` of the named proper-base-change equivalences
--   * `S4.Def_RP_EtPBC_C1_PbcG`: S4-EtPBC-C1, part 20a: the named equivalence `pbcEquiv` in every degree
--
--   **Formalization note.** One file of a library formalizing the canonical proper base change isomorphism for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ proper), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and a geometric point $s$ of $S$ at which $\bar f$ satisfies proper base change, the stalk $(R^q f_! F)_s$ is identified with $H^q_c(X_s, F|_{X_s})$ by a named isomorphism that is natural in the sheaf $F$ of $\Lambda$-modules (built from the base change morphism of the fibre square). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`) and for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCB_004

/-!
# Proper base change with compact supports, library file 002

Declarations of the formalization of the canonical proper base change isomorphism for compactly
supported étale cohomology (R^q f_! F)_s ≃ H^q_c(X_s, F|X_s), natural in F, for compactified X ⟶ S
(the base change morphism, its stalk form and its naturality), re-hosted declaration by declaration
from the library modules below, on top of the proper base change libraries RPLib_FX_EtPBC and
RPLib_FX_EtPBCB (projective line and iterated projective-line bundles). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_C1_Psi0a`: S4-EtPBC-C1, part 18a: degree `0` on germs
* `S4.Def_RP_EtPBC_C1_NatF`: S4-EtPBC-C1, part 19: naturality in `F` of the named proper-base-change equivalences
* `S4.Def_RP_EtPBC_C1_PbcG`: S4-EtPBC-C1, part 20a: the named equivalence `pbcEquiv` in every degree
-/

set_option autoImplicit false

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

/-- **`pbcEquivZero` on the germ of a section `z` of `g_* F`**. -/
theorem pbc0_germ (hI : BCInj Λ g s 0 F) (hS : BCSurj Λ g s 0 F) (j : Nbhd s)
    (z : ((sheafToPresheaf _ _).obj ((push g Λ).obj F)).obj (op j.1)) :
    pbcEquivZero Λ g s F hI hS (((s.stalkF Λ).map (((push g Λ).rightDerivedZeroIsoSelf).inv.app F)).hom
      ((s.point.toPresheafFiber j.1 j.2 ((sheafToPresheaf _ _).obj ((push g Λ).obj F))).hom z)) =
      Abelian.Ext.mk₀ (bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map ((freeEquiv Λ ((etPull g).obj j.1) F).symm z)) := by
  have e1 : ((s.stalkF Λ).map (((push g Λ).rightDerivedZeroIsoSelf).hom.app F)).hom
      (((s.stalkF Λ).map (((push g Λ).rightDerivedZeroIsoSelf).inv.app F)).hom
        ((s.point.toPresheafFiber j.1 j.2 ((sheafToPresheaf _ _).obj ((push g Λ).obj F))).hom z)) =
      (s.point.toPresheafFiber j.1 j.2 ((sheafToPresheaf _ _).obj ((push g Λ).obj F))).hom z := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      ModuleCat.hom_id, LinearMap.id_apply]
  refine (congrArg (stalkEquiv s (sec0Ext_map Λ g F) hI hS) e1).trans ?_
  refine (stalkEquivE_apply s (sec0Ext_map Λ g F) hI hS _).trans ?_
  refine (stalkBC_germ s (sec0Ext_map Λ g F) j.1 j.2 _).trans ?_
  change germBC Λ g s F 0 _ (sec0Ext Λ g F) j z = _
  change Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j F 0
    (sec0Ext Λ g F j.1 z) = _
  rw [Delta.bc_apply, sec0Ext, AddEquiv.trans_apply, Abelian.Ext.addEquiv₀_symm_apply,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  rfl

end RamanujanPetersson.EtPBC.C1

end

end

-- ===== S4.Def_RP_EtPBC_C1_NatF =====
section

/-!
# S4-EtPBC-C1, part 19: naturality in `F` of the named proper-base-change equivalences

* (generic) **`absRelR_natural`**: `absRelR I' (x ∘ ψ) = absRelR I x ≫ R^(p+1)(ψ)`; **`abs0_natural`** and
  **`abs0_injective`**: the same for the degree-`0` description `x ↦ adj.homEquiv (u ≫ x) ≫ R.toRD₀`;
* **`pbcEquivS_natural`**, **`pbcEquivZero_natural`**: `pbcEquiv (stalk of R^q g_*(φ) y) = H^q(ι^* φ) (pbcEquiv y)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.C1

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.PtSec

set_option backward.isDefEq.respectTransparency false

section GenN

universe w v₁ v₂ u₁ u₂

variable {D : Type u₂} [Category.{v₂} D] [Abelian D] {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  [HasInjectiveResolutions C] {L : D ⥤ C} {R : C ⥤ D} [R.Additive] (adj : L ⊣ R)
  {A : D} {X : C} {Y Y' : C}

/-- **Naturality of the degree-`0` description** `x ↦ adj.homEquiv (u ≫ x) ≫ R.toRD₀`. -/
theorem abs0_natural (u : L.obj A ⟶ X) (ψ : Y ⟶ Y') (x : Abelian.Ext X Y 0) :
    adj.homEquiv _ _ (u ≫ Abelian.Ext.addEquiv₀ (x.comp (Abelian.Ext.mk₀ ψ) (add_zero 0))) ≫
        R.toRightDerivedZero.app Y' =
      (adj.homEquiv _ _ (u ≫ Abelian.Ext.addEquiv₀ x) ≫ R.toRightDerivedZero.app Y) ≫ (R.rightDerived 0).map ψ := by
  obtain ⟨a, rfl⟩ := Abelian.Ext.addEquiv₀.symm.surjective x
  rw [Abelian.Ext.addEquiv₀_symm_apply, Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.addEquiv₀_symm_apply,
    ← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, Category.assoc,
    ← R.toRightDerivedZero.naturality]
  simp only [Functor.map_comp, Category.assoc, Adjunction.homEquiv_naturality_right]

/-- The degree-`0` description is injective (`R` left exact, `u` epi). -/
theorem abs0_injective [PreservesFiniteLimits R] (u : L.obj A ⟶ X) [Epi u] {x x' : Abelian.Ext X Y 0}
    (h : adj.homEquiv _ _ (u ≫ Abelian.Ext.addEquiv₀ x) ≫ R.toRightDerivedZero.app Y =
      adj.homEquiv _ _ (u ≫ Abelian.Ext.addEquiv₀ x') ≫ R.toRightDerivedZero.app Y) : x = x' := by
  rw [cancel_mono, Equiv.apply_eq_iff_eq, cancel_epi] at h
  exact Abelian.Ext.addEquiv₀.injective h

end GenN

universe u

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

omit [UniversallyClosed g] in
theorem bcSurj_of_good (hg : PBCGood Λ g s) (q : ℕ) (G : EtSh Λ P) : BCSurj Λ g s q G :=
  bcSurj_of_van Λ g s hg.1 hg.2 q G

theorem bcInj_of_good (hg : PBCGood Λ g s) (q : ℕ) (G : EtSh Λ P) : BCInj Λ g s q G :=
  Delta.injAt_all (bcUnit_comp Λ g s) (fun G => bcInj_zero Λ g s G) (bcSurj_of_good g s hg) q G

end Good

end RamanujanPetersson.EtPBC.C1

end

end


