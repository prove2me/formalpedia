-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_066
-- name    : RPLib_FX_EtPBC_066
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:46:25.992606+00:00
-- url     : https://prove2.me/theorems/28a7093f-4883-50b2-86fc-8fef79527dc3
-- title:
--   Proper base change for the projective line, library file 066
-- statement:
--   File 066 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2T4c`: S4-EtPBC-A, O2 S5d (O2T4c): `clsD_add`, `cls_eq_clsD`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_050
import Definitions.Def_RPLib_FX_EtPBC_055

/-!
# Proper base change for the projective line, library file 066

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2T4c`: S4-EtPBC-A, O2 S5d (O2T4c): `clsD_add`, `cls_eq_clsD`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2T4c =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4c): `clsD_add`, `cls_eq_clsD`
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

section ClsD

variable {k : Type} [Field k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact)

set_option backward.isDefEq.respectTransparency false in
/-- **Every one-point class through `Spec B` is a `clsD`** (with `f = 𝟙`). -/
theorem cls_eq_clsD {F : EtSh Λ P} {Uo : P.Opens} (h : Uo ≤ Uz)
    (hUo : ∀ u : Spec B, (chEt c φ).hom u ∈ Uo ↔ φ.hom (X - C a) ∉ u.asIdeal)
    (hSo : (locC Λ (chEt c φ) h).ShortExact) (κ : Ext.{0} (freeSh Λ (prd (chEt c φ) (opEt Uo))) F 1) :
    hSo.extClass.comp κ (show 1 + 1 = 2 from rfl) =
      clsD c φ a hUz hS (𝟙 _) ((extFree Λ (W1 c φ a) F 1 ((Ext.mk₀ (freeMap Λ (isoT c φ hUo).hom)).comp κ
        (zero_add 1))).comp (Ext.mk₀ ((resCompIso Λ (toD1 c φ a)).inv.app F)) (add_zero 1)) := by
  rw [locT_cls c φ hUo h hSo κ, uChange c φ h hUo hUz hSo hS, clsD_eq]
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.inv_hom_id_app, Ext.comp_mk₀_id, AddEquiv.symm_apply_apply]

end ClsD

end RamanujanPetersson.EtPBC.EtMV

end

end


