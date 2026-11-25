-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_060
-- name    : RPLib_FX_EtPBC_060
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:38:50.622795+00:00
-- url     : https://prove2.me/theorems/284b237d-d393-55c6-964f-15a27c9ea764
-- title:
--   Proper base change for the projective line, library file 060
-- statement:
--   File 060 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2E6`: S4-EtPBC-A, O2 C-plan S4d1: `extFree` with constant coefficients, natural in the etale object
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_046

/-!
# Proper base change for the projective line, library file 060

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2E6`: S4-EtPBC-A, O2 C-plan S4d1: `extFree` with constant coefficients, natural in the etale object
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2E6 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d1: `extFree` with constant coefficients, natural in the etale object

* `extFreeU Λ W n : Ext_P(Λ[W], Λ_P) ≃+ H^n(W, Λ)` (`extFree`, then `(Λ_P)|_W ≅ Λ_W`), `extFreeU_apply`;
* naturality and the `1 ↦ 1` lemmas are in `O2E6b` (split for compile time).
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

theorem extFreeU_apply (W : P.Etale) (n : ℕ) (ξ : Ext.{u} (freeSh Λ W) (unitSh Λ P) n) :
    extFreeU Λ W n ξ = (extFree Λ W (unitSh Λ P) n ξ).comp (Ext.mk₀ (unitResIso W.hom Λ).inv) (add_zero n) :=
  rfl

end RamanujanPetersson.EtPBC.EtMV

end

end


