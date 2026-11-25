-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_069
-- name    : RPLib_FX_EtPBC_069
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:10:07.648825+00:00
-- url     : https://prove2.me/theorems/2c33bfcd-ad1b-5c22-81e2-29af8c9b87bf
-- title:
--   Proper base change for the projective line, library file 069
-- statement:
--   File 069 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2E6b`: S4-EtPBC-A, O2 C-plan S4d1 (part 2): `extFreeU` is natural in the etale object
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_040
import Definitions.Def_RPLib_FX_EtPBC_045
import Definitions.Def_RPLib_FX_EtPBC_060

/-!
# Proper base change for the projective line, library file 069

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2E6b`: S4-EtPBC-A, O2 C-plan S4d1 (part 2): `extFreeU` is natural in the etale object
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2E6b =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d1 (part 2): `extFreeU` is natural in the etale object

* `resHE_comp_mk₀`, `freeEquiv_unitRes`, `unitRes_one`;
* `unitRes_comp`: `1 ↦ 1` along `m.left`, then along `W.hom`, is `1 ↦ 1` along `W'.hom`; `resCompIso_unit`;
* **`extFreeU_natural`**: `extFreeU W' (ξ ∘ Λ[m]) = resLE m.left (extFreeU W ξ)` in degree `1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

/-- **`extFreeU` is natural in the etale object** (degree `1`): `Λ[m]^*` is `resLE m.left`. -/
theorem extFreeU_natural {W W' : P.Etale} (m : W' ⟶ W) (ξ : Ext.{u} (freeSh Λ W) (unitSh Λ P) 1) :
    extFreeU Λ W' 1 ((Ext.mk₀ (freeMap Λ m)).comp ξ (zero_add 1)) = resLE m.left 1 (extFreeU Λ W 1 ξ) := by
  rw [extFreeU_apply, extFreeU_apply, extFree_natural, resLE_apply, resHE_comp_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀,
    resCompIso_unit]

end RamanujanPetersson.EtPBC.EtMV

end

end


