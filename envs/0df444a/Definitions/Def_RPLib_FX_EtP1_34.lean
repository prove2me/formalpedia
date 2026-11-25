-- Prove2me | Definitions.Def_RPLib_FX_EtP1_34
-- name    : RPLib_FX_EtP1_34
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:32:15.59231+00:00
-- url     : https://prove2.me/theorems/f1535ee9-a649-5d4b-8d9f-76e6bdfc5773
-- title:
--   Étale cohomology of the projective line, library file 34 of 34
-- statement:
--   File 34 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_P1H3`: S4-EtCompact, E4 (O7b): `H^(n+3)(P¹, F) = 0` for every sheaf `F`
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_33

/-!
# Étale cohomology of the projective line, library file 34 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_P1H3`: S4-EtCompact, E4 (O7b): `H^(n+3)(P¹, F) = 0` for every sheaf `F`
-/

set_option autoImplicit false

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

/-- `H^(n+3)(P¹, j_! Y) = 0` follows from `H^(n+3)(P¹, j_* Y) = 0`. -/
theorem P1.lsh_H (Y : EtSh Λ (A1 k)) (n : ℕ) (h : ∀ e : H Λ ((push (chartA1 k) Λ).obj Y) (n + 3), e = 0)
    (e : H Λ ((lsh (chartA1 k) Λ).obj Y) (n + 3)) : e = 0 := by
  have hm := mono_lshAdj_counit (chartA1 k) Λ ((push (chartA1 k) Λ).obj Y)
  have hS := @Cech.cokSC_shortExact _ _ _ _ _ _ hm
  have hQ : IsZero (Cech.Mx (cokernel ((lshAdj (chartA1 k) Λ).counit.app ((push (chartA1 k) Λ).obj Y)))
      (P1.genPt k)) := by
    rw [← map_genPt k k[X] (chartA1 k)]
    exact StkTr.isZero_cokernel_counit (chartA1 k) _ _
  let ι : (lsh (chartA1 k) Λ).obj ((res (chartA1 k) Λ).obj ((push (chartA1 k) Λ).obj Y)) ≅
      (lsh (chartA1 k) Λ).obj Y :=
    (lsh (chartA1 k) Λ).mapIso ((asIso (resAdj (chartA1 k) Λ).counit).app Y)
  refine (Hiso Λ ι.symm (n + 3)).injective ?_
  rw [map_zero]
  obtain ⟨x₃, hx₃⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS (Hiso Λ ι.symm (n + 3) e) (h _)
    (show n + 2 + 1 = n + 3 from rfl)
  rw [← hx₃, P1.H_closed k _ hQ (n + 1) x₃, Abelian.Ext.zero_comp]

variable (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)

include hl hΛ

/-- **`H^(n+3)(P¹, F) = 0`** for every sheaf `F` (`k = k̄`, `ℓ ≠ char k`, `ℓ^m Λ = 0`). -/
theorem P1.H_add_three_eq_zero_all (F : EtSh Λ (P1 k)) (n : ℕ) (e : H Λ F (n + 3)) : e = 0 := by
  refine P1.H_of_lsh k F n (fun e' => ?_) e
  refine ext_eq_zero_of_map ((lsh (chartA1 k) Λ).map ((pullAdj (gen k[X]) Λ).unit.app ((res (chartA1 k) Λ).obj F)))
    (unitSh Λ (P1 k)) (n + 1) (fun e₁ => ?_) (fun e₂ => ?_) (fun e₃ => ?_) e'
  · refine P1.H_closed k _ ?_ (n + 2) e₁
    rw [← map_genPt k k[X] (chartA1 k)]
    exact StkTr.isZero_lsh_kernel (chartA1 k) _ _ (GenUnit.isZero_stalk_kernel_unit _)
  · refine P1.H_closed k _ ?_ (n + 1) e₂
    rw [← map_genPt k k[X] (chartA1 k)]
    exact StkTr.isZero_lsh_cokernel (chartA1 k) _ _ (GenUnit.isZero_stalk_cokernel_unit _)
  · refine P1.lsh_H k _ n (fun e₄ => ?_) e₃
    refine (Hiso Λ ((pushCompIso Λ (gen k[X]) (chartA1 k)).app _) (n + 3)).injective ?_
    rw [map_zero]
    exact P1.H_push_eq_zero k l hl m hΛ _ n _

end H3

end RamanujanPetersson.EtCompact.CurveHn

end

end


