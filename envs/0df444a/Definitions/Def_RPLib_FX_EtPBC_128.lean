-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_128
-- name    : RPLib_FX_EtPBC_128
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:55:10.221855+00:00
-- url     : https://prove2.me/theorems/107d7682-adab-4b6a-8575-28d47a9ffe3c
-- title:
--   Proper base change for the projective line, library file 128
-- statement:
--   File 128 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Th1c`: S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_115
import Definitions.Def_RPLib_FX_EtPBC_116

/-!
# Proper base change for the projective line, library file 128

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Th1c`: S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Th1c =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`

For `τ : T ⟶ D₀` (`W₀ := D₀ ×_P R ⟶ D₀` quasi-compact, separated, of constant degree `n`):
* `theta_apply`: `θ_τ x = extFreeU (thX x)` (via `thXE`, `theta_eq_thXE`, `thXE_eq`);
* **`theta_natural`**: for `m : T₁ ⟶ T₂` with `m ≫ τ₂ = τ₁`,
  `θ_{τ₁}(Λ[m]^* x) = resLE (wm m) (θ_{τ₂} x)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.GalTrE

universe u

section Gen

end Gen

section GenNat

universe w₁ v₁ u₁

end GenNat

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}} {D₀ : P.Etale} (R : P.Etale)

variable [QuasiCompact ((etPull D₀.hom).obj R).hom] [IsSeparated ((etPull D₀.hom).obj R).hom]
  (n : ℕ) (hn : ∀ y : D₀.left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull D₀.hom).obj R)) = n)

theorem theta_apply {T : P.Etale} (τ : T ⟶ D₀) (x : Ext.{u} (freeSh Λ T) (freeSh Λ R) 1) :
    theta Λ R n hn τ x = extFreeU Λ (ovrW R τ) 1 (thX Λ R n hn τ x) :=
  (DFunLike.congr_fun (theta_eq_thXE Λ R n hn τ) x).trans
    ((AddEquiv.trans_apply _ _ x).trans (congrArg (extFreeU Λ (ovrW R τ) 1) (thXE_eq Λ R n hn τ x)))

end Theta

end RamanujanPetersson.EtPBC.EtShap

end

end


