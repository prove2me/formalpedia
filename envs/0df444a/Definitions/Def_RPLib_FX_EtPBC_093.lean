-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_093
-- name    : RPLib_FX_EtPBC_093
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:26:38.120831+00:00
-- url     : https://prove2.me/theorems/171ff073-2d55-5492-9bfd-df9b68143122
-- title:
--   Proper base change for the projective line, library file 093
-- statement:
--   File 093 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Th1b`: S4-EtPBC-A, O2 M6 (O2Th1b): Shapiro over a FIXED base `D₀` (definitions `thetaV`, `theta`, `thX`)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_032
import Definitions.Def_RPLib_FX_EtPBC_081

/-!
# Proper base change for the projective line, library file 093

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Th1b`: S4-EtPBC-A, O2 M6 (O2Th1b): Shapiro over a FIXED base `D₀` (definitions `thetaV`, `theta`, `thX`)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Th1b =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Th1b): Shapiro over a FIXED base `D₀` (definitions `thetaV`, `theta`, `thX`)

For `τ : T ⟶ D₀` (`W₀ := D₀ ×_P R ⟶ D₀` quasi-compact, separated, of constant degree `n`):
* **`theta Λ R n hn τ : Ext¹_P(Λ[T], Λ[R]) ≃+ H¹(T ×_P R, Λ)`**;
* `thX`: the `W₀`-level class (`theta_apply`, naturality: O2Th1c).
* (surgery) `theta := thetaGen ..` with generic `thXEGen`/`thetaGen` and `extFreeUT`.
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

section GenTheta

universe w₁ v₁ u₁ v₂ u₂ u₃

end GenTheta

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}} {D₀ : P.Etale} (R : P.Etale)

variable [QuasiCompact ((etPull D₀.hom).obj R).hom] [IsSeparated ((etPull D₀.hom).obj R).hom]
  (n : ℕ) (hn : ∀ y : D₀.left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull D₀.hom).obj R)) = n)

variable (D₀) in
/-- **Shapiro over `D₀`, source form**: `Ext¹_P(Λ[D₀ ∘ V], Λ[R]) ≃+ Ext¹_{W₀}(Λ[V ×_{D₀} W₀], Λ)`. -/
def thetaV (V : D₀.left.Etale) :
    Ext.{u} (freeSh Λ ((etComp D₀.hom).obj V)) (freeSh Λ R) 1 ≃+
      Ext.{u} (freeSh Λ ((etPull ((etPull D₀.hom).obj R).hom).obj V)) (unitSh Λ ((etPull D₀.hom).obj R).left) 1 :=
  (((extFreeV Λ D₀ V (freeSh Λ R) 1).trans (extIsoRight _ (resFreeIso Λ D₀.hom R).symm 1)).trans
    (shapExt Λ ((etPull D₀.hom).obj R) n hn (freeSh Λ V) 1).symm).trans
      (extIsoLeft (pullFreeIso Λ ((etPull D₀.hom).obj R).hom V) _ 1)

end Theta

end RamanujanPetersson.EtPBC.EtShap

end

end


