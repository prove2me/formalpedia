-- Prove2me | Definitions.Def_RPLib_FX_EtP1_33
-- name    : RPLib_FX_EtP1_33
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:12:57.1541+00:00
-- url     : https://prove2.me/theorems/3b5100e0-a689-56f9-826c-738dbb45233a
-- title:
--   Étale cohomology of the projective line, library file 33 of 34
-- statement:
--   File 33 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_P1Clo`: S4-EtCompact, E3 (O7b): sheaves on `P¹` with zero generic stalk are acyclic
--   * `S4.Def_RP_EtCompact_P1H3`: S4-EtCompact, E4 (O7b): `H^(n+3)(P¹, F) = 0` for every sheaf `F`
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_32

/-!
# Étale cohomology of the projective line, library file 33 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_P1Clo`: S4-EtCompact, E3 (O7b): sheaves on `P¹` with zero generic stalk are acyclic
* `S4.Def_RP_EtCompact_P1H3`: S4-EtCompact, E4 (O7b): `H^(n+3)(P¹, F) = 0` for every sheaf `F`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_P1Clo =====
section

/-!
# S4-EtCompact, E3 (O7b): sheaves on `P¹` with zero generic stalk are acyclic

* `chart_hF`, **`chart_H`**: for an affine chart `f : Spec A ⟶ P¹` (`A` of finite type over `k = k̄`, dimension `≤ 1`),
  `H^(n+1)(Spec A, f^* Z) = 0` when `Z_η̄ = 0` (`Cech.H_eq_zero_of_closed` + `StkTr.isZero_res`);
* **`P1.H_closed`**: `H^(m+1)(P¹, Z) = 0` when `Z` has zero stalk at the generic point (`m = 0`: `P1.H1_closed`;
  `m ≥ 1`: Mayer-Vietoris over the two `A¹` charts and `G_m`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ]

/-- **`H^(m+1)(P¹, Z) = 0`** when `Z` has zero stalk at the generic point. -/
theorem P1.H_closed (Z : EtSh Λ (P1 k)) (hη : IsZero (Cech.Mx Z (P1.genPt k))) :
    ∀ (m : ℕ) (e : H Λ Z (m + 1)), e = 0
  | 0, e => P1.H1_closed k Z hη e
  | n + 1, e => by
    have hS := mvS_shortExact (F := unitSh Λ (P1 k)) (P1.cover k)
    have h2 := P1.H_closed_X₂ k Z hη n
    obtain ⟨x₁, hx₁⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Z e (Subsingleton.elim _ _)
      (show 1 + (n + 1) = n + 1 + 1 by omega)
    rw [← hx₁, P1.H_closed_X₁ k Z hη n x₁, Abelian.Ext.comp_zero]

end RamanujanPetersson.EtCompact.CurveHn

end

end

-- ===== S4.Def_RP_EtCompact_P1H3 =====
section

/-!
# S4-EtCompact, E4 (O7b): `H^(n+3)(P¹, F) = 0` for every sheaf `F`

`j = chartA1 : A¹ ⟶ P¹`, `g = gen k[X]` the generic point of `A¹`.
* `P1.H_of_lsh`: `0 → j_! j^* F → F → Q → 0` with `Q` point-supported (E3) reduces to `j_! j^* F`;
* `P1.lsh_H`: `j_! Y ≅ j_! j^* j_* Y ↪ j_* Y` in `H^(n+3)` (the cokernel is point-supported);
* `P1.isZero_R1_gen`, `P1.isZero_R1_qt`, **`P1.H_push_eq_zero`**: `H^(n+3)(P¹, (g ≫ j)_* N) = 0` (Leray-lite);
* **`P1.H_add_three_eq_zero_all`**: dévissage along `j_!` of the unit `G ⟶ g_* g^* G` (kernel and cokernel vanish at
  the generic point, so they are acyclic by E3).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ]

section H3

open RamanujanPetersson.CdOne RamanujanPetersson.Tsen RamanujanPetersson.EtCompact.GenFrac

/-- `H^(n+3)(P¹, F) = 0` follows from `H^(n+3)(P¹, j_! j^* F) = 0` (the cokernel of the counit is point-supported). -/
theorem P1.H_of_lsh (F : EtSh Λ (P1 k)) (n : ℕ)
    (h : ∀ e : H Λ ((lsh (chartA1 k) Λ).obj ((res (chartA1 k) Λ).obj F)) (n + 3), e = 0) (e : H Λ F (n + 3)) :
    e = 0 := by
  have hm := mono_lshAdj_counit (chartA1 k) Λ F
  have hS := @Cech.cokSC_shortExact _ _ _ _ _ _ hm
  have hQ : IsZero (Cech.Mx (cokernel ((lshAdj (chartA1 k) Λ).counit.app F)) (P1.genPt k)) := by
    rw [← map_genPt k k[X] (chartA1 k)]
    exact StkTr.isZero_cokernel_counit (chartA1 k) F _
  obtain ⟨x₁, hx₁⟩ := Abelian.Ext.covariant_sequence_exact₂ _ hS e (P1.H_closed k _ hQ (n + 2) _)
  rw [← hx₁, h x₁, Abelian.Ext.zero_comp]

variable (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)

include hl hΛ

/-- **`H^(n+3)(P¹, (g ≫ j)_* N) = 0`** (Leray-lite: `H²(η, -) = 0`, `R²= 0`, `R¹` point-supported). -/
theorem P1.H_push_eq_zero (N : EtSh Λ (Spec ((Spec (CommRingCat.of k[X])).residueField (GenBr.genPt k[X]))))
    (n : ℕ) (e : H Λ ((push (gen k[X] ≫ chartA1 k) Λ).obj N) (n + 3)) : e = 0 :=
  H_push_eq_zero_of_R1 (fun M e => H_genPt_eq_zero k l hl m hΛ 0 M e) (P1.isZero_R1_qt k l hl m hΛ) n N
    (fun e => P1.H_closed k _ (P1.isZero_R1_gen k N) n e) e

end H3

end RamanujanPetersson.EtCompact.CurveHn

end

end


