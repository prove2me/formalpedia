-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_135
-- name    : RPLib_FX_EtPBC_135
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:29:20.954097+00:00
-- url     : https://prove2.me/theorems/ee8d3865-cd32-588a-860c-4732ca0c965c
-- title:
--   Proper base change for the projective line, library file 135
-- statement:
--   File 135 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Th1c`: S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_105
import Definitions.Def_RPLib_FX_EtPBC_126

/-!
# Proper base change for the projective line, library file 135

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

/-- **Naturality of `thX`.** -/
theorem thX_natural {T₁ T₂ : P.Etale} (m : T₁ ⟶ T₂) {τ₁ : T₁ ⟶ D₀} {τ₂ : T₂ ⟶ D₀} (h : m ≫ τ₂ = τ₁)
    (x : Ext.{u} (freeSh Λ T₂) (freeSh Λ R) 1) :
    (Ext.mk₀ (freeMap Λ (ovrMapW R m h))).comp (thX Λ R n hn τ₂ x) (zero_add 1) =
      thX Λ R n hn τ₁ ((Ext.mk₀ (freeMap Λ m)).comp x (zero_add 1)) :=
  thX_natural_gen (freeMap Λ (ovrMapW R m h)) (freeMap Λ (ovrι R τ₁).inv) (freeMap Λ (ovrι R τ₂).inv)
    (freeMap Λ ((etPull ((etPull D₀.hom).obj R).hom).map (ovrMap m h)))
    (pullFreeHom Λ ((etPull D₀.hom).obj R).hom (ovr τ₁)) (pullFreeHom Λ ((etPull D₀.hom).obj R).hom (ovr τ₂))
    ((pull ((etPull D₀.hom).obj R).hom Λ).map (freeMap Λ (ovrMap m h)))
    ((shapExt Λ ((etPull D₀.hom).obj R) n hn (freeSh Λ (ovr τ₁)) 1).symm
      (thZ Λ R τ₁ ((Ext.mk₀ (freeMap Λ m)).comp x (zero_add 1))))
    ((shapExt Λ ((etPull D₀.hom).obj R) n hn (freeSh Λ (ovr τ₂)) 1).symm (thZ Λ R τ₂ x))
    (thX_natural_h1 Λ R m h)
    (pullFreeHom_natural (Λ := Λ) (f := ((etPull D₀.hom).obj R).hom) (ovrMap m h))
    (thX_natural_h3 Λ R n hn m h x)

end Theta

end RamanujanPetersson.EtPBC.EtShap

end

end


