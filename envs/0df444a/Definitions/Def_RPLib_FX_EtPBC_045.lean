-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_045
-- name    : RPLib_FX_EtPBC_045
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:58:06.404811+00:00
-- url     : https://prove2.me/theorems/73c59c87-4385-5fa6-9c2a-0195670c3815
-- title:
--   Proper base change for the projective line, library file 045
-- statement:
--   File 045 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2E5b`: S4-EtPBC-A, O2 C-plan S4d0b: `extFree` is natural in the etale object (degree 1)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_034
import Definitions.Def_RPLib_FX_EtPBC_037

/-!
# Proper base change for the projective line, library file 045

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2E5b`: S4-EtPBC-A, O2 C-plan S4d0b: `extFree` is natural in the etale object (degree 1)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2E5b =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d0b: `extFree` is natural in the etale object (degree 1)

**`extFree_natural`**: for `m : W' ⟶ W` in `P.Etale` and `ξ : Ext¹_P(Λ[W], F)`,
`extFree W' (ξ ∘ Λ[m]) = (resHE m.left (extFree W ξ)) ∘ (resCompIso m)_F`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg

section Gen

universe w v₁ u₁ v₂ u₂ v₃ u₃

end Gen

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {W W' : P.Etale} (m : W' ⟶ W)

/-- **`extFree` is natural in the etale object** (degree `1`). -/
theorem extFree_natural (F : EtSh Λ P) (ξ : Ext.{u} (freeSh Λ W) F 1) :
    extFree Λ W' F 1 ((Ext.mk₀ (freeMap Λ m)).comp ξ (zero_add 1)) =
      (resHE (U := (𝟭 Scheme).obj W'.left) (X := (𝟭 Scheme).obj W.left) m.left ((res W.hom Λ).obj F) 1
        (extFree Λ W F 1 ξ)).comp
        (Ext.mk₀ ((resCompIso Λ m).hom.app F)) (add_zero 1) :=
  extFree_natural_gen (lshAdj W.hom Λ) (lshAdj W'.hom Λ)
    (res (U := (𝟭 Scheme).obj W'.left) (X := (𝟭 Scheme).obj W.left) m.left Λ) (resCompIso Λ m) (freeLshIso Λ W)
    (freeLshIso Λ W') (freeMap Λ m) (unitRes m.left Λ) (diagSec_natural m) ξ

end RamanujanPetersson.EtPBC.EtMV

end

end


