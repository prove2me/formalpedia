-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_187
-- name    : RPLib_FX_EtPBC_187
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:13:36.147219+00:00
-- url     : https://prove2.me/theorems/f3611e07-f315-5296-8c09-38bcc2c3faae
-- title:
--   Proper base change for the projective line, library file 187
-- statement:
--   File 187 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2T4d`: S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_182

/-!
# Proper base change for the projective line, library file 187

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2T4d`: S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2T4d =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
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

section Pc

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P)
  [IsOpenImmersion c] {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0)
  {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact)

set_option backward.isDefEq.respectTransparency false in
theorem clsD_sec_tail {T : P.Etale} (s : chEt c φ ⟶ T) (κ0 : H Λ (unitSh Λ (chEt c φ).left) 1) (c' : Λ) :
    (hS.extClass.comp (Ext.mk₀ (freeMap Λ (isoT c φ hUz).inv)) (add_zero 1)).comp
      (thetaM Λ (toD1 c φ a ≫ s) 1 (resLE (toD1 c φ a).left 1 κ0 + resLE (toWa c a φ).left 1 (xiA a hN Λ hΛ c')))
      (show 1 + 1 = 2 from rfl) =
    (pcD c φ a hN hΛ hUz hS c').comp (Ext.mk₀ (freeMap Λ s)) (add_zero 2) := by
  rw [thetaM_add, Ext.comp_add, clsD_sec_ta c φ a hUz hS s κ0, clsD_sec_tb c φ a hN hΛ hUz hS s c', zero_add]

end Pc

end RamanujanPetersson.EtPBC.EtMV

end

end


