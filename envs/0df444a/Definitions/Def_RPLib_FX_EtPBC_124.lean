-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_124
-- name    : RPLib_FX_EtPBC_124
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:56:25.391799+00:00
-- url     : https://prove2.me/theorems/e310145d-5f53-5be9-b24f-4ea62fd6752e
-- title:
--   Proper base change for the projective line, library file 124
-- statement:
--   File 124 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2T4a0`: S4-EtPBC-A, O2 S5d (O2T4a0): `extFree_thetaM`, `thetaM_comp`, `thetaM_add` (`thetaM` itself is in O2T4a00)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_112

/-!
# Proper base change for the projective line, library file 124

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2T4a0`: S4-EtPBC-A, O2 S5d (O2T4a0): `extFree_thetaM`, `thetaM_comp`, `thetaM_add` (`thetaM` itself is in O2T4a00)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2T4a0 =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4a0): `extFree_thetaM`, `thetaM_comp`, `thetaM_add` (`thetaM` itself is in O2T4a00)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}}

theorem extFree_thetaM {W T : P.Etale} (m : W ⟶ T) (n : ℕ) (κ : H Λ (unitSh Λ W.left) n) :
    extFree Λ W (freeSh Λ T) n (thetaM Λ m n κ) = κ.comp (Ext.mk₀ (secMap Λ m)) (add_zero n) := by
  rw [thetaM_eq]
  exact AddEquiv.apply_symm_apply _ _

theorem thetaM_add {W T : P.Etale} (m : W ⟶ T) (n : ℕ) (κ κ' : H Λ (unitSh Λ W.left) n) :
    thetaM Λ m n (κ + κ') = thetaM Λ m n κ + thetaM Λ m n κ' := by
  rw [thetaM_eq, thetaM_eq, thetaM_eq, Ext.add_comp, map_add]

end Theta

end RamanujanPetersson.EtPBC.EtMV

end

end


