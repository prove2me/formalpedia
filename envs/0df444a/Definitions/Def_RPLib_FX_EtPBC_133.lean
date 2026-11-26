-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_133
-- name    : RPLib_FX_EtPBC_133
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:01:16.018151+00:00
-- url     : https://prove2.me/theorems/513dd38a-d85f-5d71-b03c-77103a44237b
-- title:
--   Proper base change for the projective line, library file 133
-- statement:
--   File 133 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_124

/-!
# Proper base change for the projective line, library file 133

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2TB3 =====
section

/-!
# S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`

* `pullH Λ g n κ := u ∘ g^*κ ∘ u⁻¹ ∈ H^n(X, Λ)` for `κ ∈ H^n(Y, Λ)` and any `g : X ⟶ Y` (`u := pullUnit Λ g`);
* `secMap_id`, `diagSec_pull` (the KEY identity at `m = 𝟙`);
* **`thetaM_pull`**: `Λ[f⁻¹W] ⟶ f^*Λ[W]` followed by `f^*(thetaM m 1 κ)` equals
  `thetaM (f⁻¹ m) 1 (pullH f_W 1 κ)` followed by `Λ[f⁻¹T] ⟶ f^*Λ[T]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenAlg

universe u

section TB3

variable {Λ : Type u} [CommRing Λ]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section GenPL

universe w' v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

end GenPL

theorem thetaM_pull_R {W T : Y.Etale} (m : W ⟶ T) (κ : H Λ (unitSh Λ W.left) 1) :
    (extFree Λ ((etPull f).obj W) ((pull f Λ).obj (freeSh Λ T)) 1
        ((thetaM Λ ((etPull f).map m) 1 (pullH Λ (fW f W) 1 κ)).comp (Ext.mk₀ (pullFreeHom Λ f T))
          (add_zero 1))).comp (Ext.mk₀ ((tauIso Λ f W).hom.app (freeSh Λ T))) (add_zero 1) =
      (Ext.mk₀ (pullUnit Λ (fW f W)).hom).comp ((κ.mapExactFunctor (pull (fW f W) Λ)).comp
        (Ext.mk₀ ((pull (fW f W) Λ).map (secMap Λ m))) (add_zero 1)) (zero_add 1) := by
  rw [extFree_comp_mk₀, extFree_thetaM]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc]
  rw [show (tauIso Λ f W).hom.app (freeSh Λ T) = tauApp2 Λ f W (freeSh Λ T) from rfl, secMap_pull, pullH]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id_assoc]

end TB3

end RamanujanPetersson.EtPBC.EtMV

end

end


