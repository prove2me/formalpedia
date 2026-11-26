-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_148
-- name    : RPLib_FX_EtPBC_148
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:11:03.359564+00:00
-- url     : https://prove2.me/theorems/ec0ff908-b0e0-5d26-8daf-b3e955aefe62
-- title:
--   Proper base change for the projective line, library file 148
-- statement:
--   File 148 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
--   * `S4.Def_RP_EtPBC_A_O2L4a`: S4-EtPBC-A, L4a: base change of the MV-theta classes `ε ∘ thetaM m 1 κ ∘ Λ[r]`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_133
import Definitions.Def_RPLib_FX_EtPBC_142

/-!
# Proper base change for the projective line, library file 148

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
* `S4.Def_RP_EtPBC_A_O2L4a`: S4-EtPBC-A, L4a: base change of the MV-theta classes `ε ∘ thetaM m 1 κ ∘ Λ[r]`
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

/-- **TB (`thetaM` base change)**: `Λ[f⁻¹W] ⟶ f^*Λ[W]` followed by `f^*(thetaM m 1 κ)` is
`thetaM (f⁻¹ m) 1 (pullH f_W 1 κ)` followed by `Λ[f⁻¹T] ⟶ f^*Λ[T]`. -/
theorem thetaM_pull {W T : Y.Etale} (m : W ⟶ T) (κ : H Λ (unitSh Λ W.left) 1) :
    (Ext.mk₀ (pullFreeHom Λ f W)).comp ((thetaM Λ m 1 κ).mapExactFunctor (pull f Λ)) (zero_add 1) =
      (thetaM Λ ((etPull f).map m) 1 (pullH Λ (fW f W) 1 κ)).comp (Ext.mk₀ (pullFreeHom Λ f T)) (add_zero 1) :=
  (extFree Λ ((etPull f).obj W) ((pull f Λ).obj (freeSh Λ T)) 1).injective
    (ext_comp_iso_cancel ((tauIso Λ f W).app (freeSh Λ T))
      ((thetaM_pull_L f m κ).trans (thetaM_pull_R f m κ).symm))

end TB3

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L4a =====
section

/-!
# S4-EtPBC-A, L4a: base change of the MV-theta classes `ε ∘ thetaM m 1 κ ∘ Λ[r]`

* `thetaR_pull f m r κ`: `Λ[f⁻¹W] ⟶ f^*Λ[W]` followed by `f^*(thetaM m 1 κ ∘ Λ[r])` equals
  `thetaM (f⁻¹ m) 1 (pullH f_W 1 κ) ∘ (Λ[f⁻¹ r] ≫ (Λ[f⁻¹R] ⟶ f^*Λ[R]))`;
* `mvThetaR_pull f hS hS' m r κ`: the same for `ε(MV) ∘ thetaM m 1 κ ∘ Λ[r]` (degree 2);
* **`bc_mvThetaR`**: the base change map `bc j` on germs sends `ε ∘ thetaM m 1 κ ∘ Λ[r]` to
  `Λ[nbhdSec j] ∘ ε' ∘ thetaM (ι⁻¹ m) 1 (pullH ι_W 1 κ) ∘ (Λ[ι⁻¹ r] ≫ (Λ[ι⁻¹R] ⟶ ι^*Λ[R]))`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact

universe u

section PullR

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem thetaR_pull {W T R : Y.Etale} (m : W ⟶ T) (r : T ⟶ R) (κ : H Λ (unitSh Λ W.left) 1) :
    (Ext.mk₀ (pullFreeHom Λ f W)).comp
        (((thetaM Λ m 1 κ).comp (Ext.mk₀ (freeMap Λ r)) (add_zero 1)).mapExactFunctor (pull f Λ)) (zero_add 1) =
      (thetaM Λ ((etPull f).map m) 1 (pullH Λ (fW f W) 1 κ)).comp
        (Ext.mk₀ (freeMap Λ ((etPull f).map r) ≫ pullFreeHom Λ f R)) (add_zero 1) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ← Ext.comp_assoc_of_third_deg_zero, thetaM_pull,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, pullFreeHom_natural]

theorem mvThetaR_pull {W' W U Z T R : Y.Etale} {p₁ : W' ⟶ W} {p₂ : W' ⟶ U} {w : W ⟶ Z} {v : U ⟶ Z}
    {hsq : p₁ ≫ w = p₂ ≫ v} (hS : (mvC Λ p₁ p₂ w v hsq).ShortExact)
    (hS' : (mvC Λ ((etPull f).map p₁) ((etPull f).map p₂) ((etPull f).map w) ((etPull f).map v)
      (pull_sq f p₁ p₂ w v hsq)).ShortExact)
    (m : W' ⟶ T) (r : T ⟶ R) (κ : H Λ (unitSh Λ W'.left) 1) :
    (Ext.mk₀ (pullFreeHom Λ f Z)).comp ((hS.extClass.comp ((thetaM Λ m 1 κ).comp (Ext.mk₀ (freeMap Λ r))
        (add_zero 1)) (show 1 + 1 = 2 from rfl)).mapExactFunctor (pull f Λ)) (zero_add 2) =
      hS'.extClass.comp ((thetaM Λ ((etPull f).map m) 1 (pullH Λ (fW f W') 1 κ)).comp
        (Ext.mk₀ (freeMap Λ ((etPull f).map r) ≫ pullFreeHom Λ f R)) (add_zero 1)) (show 1 + 1 = 2 from rfl) := by
  rw [mapExact_mv f hS hS' (freeSh Λ R) _ (show 1 + 1 = 2 from rfl), thetaR_pull]

end PullR

section BC

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} {g : P ⟶ S} {s : GeomPt S}

/-- **Base change of an MV-theta class** on germs. -/
theorem bc_mvThetaR (j : Nbhd s) {W' W U T R : P.Etale} {p₁ : W' ⟶ W} {p₂ : W' ⟶ U}
    {w : W ⟶ (etPull g).obj j.1} {v : U ⟶ (etPull g).obj j.1} {hsq : p₁ ≫ w = p₂ ≫ v}
    (hS : (mvC Λ p₁ p₂ w v hsq).ShortExact)
    (hS' : (mvC Λ ((etPull (fibι g s)).map p₁) ((etPull (fibι g s)).map p₂) ((etPull (fibι g s)).map w)
      ((etPull (fibι g s)).map v) (pull_sq (fibι g s) p₁ p₂ w v hsq)).ShortExact)
    (m : W' ⟶ T) (r : T ⟶ R) (κ : H Λ (unitSh Λ W'.left) 1) :
    Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j (freeSh Λ R) 2
        (hS.extClass.comp ((thetaM Λ m 1 κ).comp (Ext.mk₀ (freeMap Λ r)) (add_zero 1))
          (show 1 + 1 = 2 from rfl)) =
      (Ext.mk₀ ((unitIso Λ (fib g s)).inv ≫ freeMap Λ (nbhdSec g s j))).comp
        (hS'.extClass.comp ((thetaM Λ ((etPull (fibι g s)).map m) 1 (pullH Λ (fW (fibι g s) W') 1 κ)).comp
          (Ext.mk₀ (freeMap Λ ((etPull (fibι g s)).map r) ≫ pullFreeHom Λ (fibι g s) R)) (add_zero 1))
          (show 1 + 1 = 2 from rfl)) (zero_add 2) := by
  rw [bc_mv (freeSh Λ R) j hS hS' _ (show 1 + 1 = 2 from rfl), thetaR_pull]

end BC

end RamanujanPetersson.EtPBC.EtMV

end

end


