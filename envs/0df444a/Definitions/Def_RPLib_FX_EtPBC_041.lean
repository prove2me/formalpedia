-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_041
-- name    : RPLib_FX_EtPBC_041
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:58:12.589855+00:00
-- url     : https://prove2.me/theorems/072a3e97-0f47-5d98-a17d-a5a8c6949d46
-- title:
--   Proper base change for the projective line, library file 041
-- statement:
--   File 041 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Th1a`: S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_032

/-!
# Proper base change for the projective line, library file 041

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Th1a`: S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Th1a =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality

Fix `D₀ R : P.Etale` with `W₀ := D₀ ×_P R ⟶ D₀` quasi-compact, separated, of constant degree `n`.
For `τ : T ⟶ D₀` (any `T : P.Etale` over `D₀`):
* **`theta Λ D₀ R n hn τ : Ext¹_P(Λ[T], Λ[R]) ≃+ H¹(T ×_P R, Λ)`** (extension by zero to `D₀`, Shapiro for
  `W₀ ⟶ D₀`, pullback of free sheaves, `T ×_{D₀} W₀ ≅ T ×_P R`);
* **`theta_natural`**: for `m : T₁ ⟶ T₂` with `m ≫ τ₂ = τ₁`,
  `θ_{τ₁}(Λ[m]^* x) = resLE (wm R m) (θ_{τ₂} x)` (`wm R m : T₁ ×_P R ⟶ T₂ ×_P R`);
* `extFreeV_natural` (naturality of `extFreeV` in `V`), `shapExt_symm_natural`.
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

section ExtV

end ExtV

section ShapNat

end ShapNat

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}} (D₀ R : P.Etale)

variable {D₀} in
/-- The `D₀`-level class. -/
def thZ {T : P.Etale} (τ : T ⟶ D₀) (x : Ext.{u} (freeSh Λ T) (freeSh Λ R) 1) :
    Ext.{u} (freeSh Λ (ovr τ)) (freeSh Λ ((etPull D₀.hom).obj R)) 1 :=
  (extFreeV Λ D₀ (ovr τ) (freeSh Λ R) 1 ((Ext.mk₀ (freeMap Λ (ovrIso τ).hom)).comp x (zero_add 1))).comp
    (Ext.mk₀ (resFreeIso Λ D₀.hom R).inv) (add_zero 1)

end Theta

end RamanujanPetersson.EtPBC.EtShap

end

end


