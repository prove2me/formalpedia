-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC1_009
-- name    : RPLib_FX_EtPBCC1_009
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T19:06:11.007437+00:00
-- url     : https://prove2.me/theorems/d796d9fd-4d9b-5eb8-bd3b-4bc6090f7534
-- title:
--   Proper base change with compact supports, library file 009
-- statement:
--   File 009 of the library for proper base change with compact supports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_C1_Psi0`: S4-EtPBC-C1, part 18b: the comparison in degree `0`
--   * `S4.Def_RP_EtPBC_C1_NatF`: S4-EtPBC-C1, part 19: naturality in `F` of the named proper-base-change equivalences
--
--   **Formalization note.** One file of a library formalizing the canonical proper base change isomorphism for étale cohomology with compact supports: for $f : X \to S$ with a compactification $X \xrightarrow{j} Z \xrightarrow{i} P \xrightarrow{\bar f} S$ ($j$ an open immersion, $i$ a closed immersion, $\bar f$ proper), $R^q f_! = R^q \bar f_* \circ i_* j_!$, and a geometric point $s$ of $S$ at which $\bar f$ satisfies proper base change, the stalk $(R^q f_! F)_s$ is identified with $H^q_c(X_s, F|_{X_s})$ by a named isomorphism that is natural in the sheaf $F$ of $\Lambda$-modules (built from the base change morphism of the fibre square). It builds on the proper base change libraries for the projective line (`RPLib_FX_EtPBC_*`) and for iterated projective-line bundles (`RPLib_FX_EtPBCB_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre) and Exposé XVII, 5.2.8 (P. Deligne, changement de base pour R f_!), Lecture Notes in Math. 269, 270, 305, Springer (1972-73); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2-§3

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCC1_004

/-!
# Proper base change with compact supports, library file 009

Declarations of the formalization of the canonical proper base change isomorphism for compactly
supported étale cohomology (R^q f_! F)_s ≃ H^q_c(X_s, F|X_s), natural in F, for compactified X ⟶ S
(the base change morphism, its stalk form and its naturality), re-hosted declaration by declaration
from the library modules below, on top of the proper base change libraries RPLib_FX_EtPBC and
RPLib_FX_EtPBCB (projective line and iterated projective-line bundles). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_C1_Psi0`: S4-EtPBC-C1, part 18b: the comparison in degree `0`
* `S4.Def_RP_EtPBC_C1_NatF`: S4-EtPBC-C1, part 19: naturality in `F` of the named proper-base-change equivalences
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_C1_Psi0 =====
section

/-!
# S4-EtPBC-C1, part 18b: the comparison in degree `0`

* **`psi0_all`**: `stalkSec y ≫ bcMorSq 0 = homEquiv (π-unit ≫ pbcEquivZero y) ≫ π_*.toRightDerivedZero`: in degree
  `0`, `pbcEquivZero` is the base-change morphism of the fibre square followed by sections over `Spec Ω`.
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

/-- **The comparison in degree `0`**: `stalkSec y ≫ bcMorSq 0 = homEquiv (π-unit ≫ pbcEquivZero y) ≫ π_*.toRD₀`. -/
theorem psi0_all (hI : BCInj Λ g s 0 F) (hS : BCSurj Λ g s 0 F)
    (y : (s.stalkF Λ).obj (((push g Λ).rightDerived 0).obj F)) :
    stalkSec s (((push g Λ).rightDerived 0).obj F) y ≫ bcMorSq Λ (fibι g s) s.pt g (pullback.snd g s.pt)
        (pullback.condition (f := g) (g := s.pt)).symm 0 F =
      (pullAdj (X := fib g s) (pullback.snd g s.pt) Λ).homEquiv _ _
        ((pullUnit (X := fib g s) Λ (pullback.snd g s.pt)).inv ≫ Abelian.Ext.addEquiv₀ (pbcEquivZero Λ g s F hI hS y)) ≫
        (push (X := fib g s) (pullback.snd g s.pt) Λ).toRightDerivedZero.app ((pull (fibι g s) Λ).obj F) := by
  obtain ⟨y', rfl⟩ : ∃ y', ((s.stalkF Λ).map (((push g Λ).rightDerivedZeroIsoSelf).inv.app F)).hom y' = y :=
    ⟨((s.stalkF Λ).map (((push g Λ).rightDerivedZeroIsoSelf).hom.app F)).hom y, by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
        ModuleCat.hom_id, LinearMap.id_apply]⟩
  obtain ⟨j, z, rfl⟩ := exists_germ s ((sheafToPresheaf _ _).obj ((push g Λ).obj F)) y'
  rw [pbc0_germ g s F hI hS j z, ← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply, ← coc0 g s F j z,
    stalkSec_natural]
  have hφ : ((push g Λ).rightDerivedZeroIsoSelf).inv.app F = (push g Λ).toRightDerivedZero.app F := rfl
  have h0 := bcMorGen_zero (push g Λ) (push (X := fib g s) (pullback.snd g s.pt) Λ) (pull (fibι g s) Λ) (pull s.pt Λ)
    (bcCell Λ (fibι g s) s.pt g (pullback.snd g s.pt) (pullback.condition (f := g) (g := s.pt)).symm) F
  have ht : stalkSec s ((push g Λ).obj F)
      ((s.point.toPresheafFiber j.1 j.2 ((sheafToPresheaf _ _).obj ((push g Λ).obj F))).hom z) =
      ptUnit s j.1 j.2 ≫ (pull s.pt Λ).map ((freeEquiv Λ j.1 ((push g Λ).obj F)).symm z) := by
    have h := stalkSec_germ_taut (s := s) j.2 (M := (push g Λ).obj F) ((freeEquiv Λ j.1 ((push g Λ).obj F)).symm z)
    erw [freeEquiv_symm_taut] at h
    exact h
  rw [hφ, ht, Category.assoc, bcMorSq]
  erw [h0]
  simp only [Category.assoc]

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

end GenN

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) {F F' : EtSh Λ P} (φ : F ⟶ F')

/-- **Naturality in `F` of `pbcEquivZero`** (degree `0`). -/
theorem pbcEquivZero_natural (hI : BCInj Λ g s 0 F) (hS : BCSurj Λ g s 0 F)
    (hI' : BCInj Λ g s 0 F') (hS' : BCSurj Λ g s 0 F')
    (y : (s.stalkF Λ).obj (((push g Λ).rightDerived 0).obj F)) :
    pbcEquivZero Λ g s F' hI' hS' (((s.stalkF Λ).map (((push g Λ).rightDerived 0).map φ)).hom y) =
      Hmap Λ ((pull (fibι g s) Λ).map φ) 0 (pbcEquivZero Λ g s F hI hS y) := by
  have : PreservesFiniteLimits (push (X := fib g s) (pullback.snd g s.pt) Λ) := inferInstance
  apply abs0_injective (pullAdj (X := fib g s) (pullback.snd g s.pt) Λ) (pullUnit (X := fib g s) Λ (pullback.snd g s.pt)).inv
  rw [← psi0_all g s F' hI' hS', stalkSec_natural, Hmap_apply, abs0_natural, ← psi0_all g s F hI hS,
    Category.assoc, Category.assoc, bcMorSq_natural]

end RamanujanPetersson.EtPBC.C1

end

end


