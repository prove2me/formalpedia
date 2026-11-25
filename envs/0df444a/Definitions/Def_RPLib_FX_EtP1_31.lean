-- Prove2me | Definitions.Def_RPLib_FX_EtP1_31
-- name    : RPLib_FX_EtP1_31
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T16:09:33.295399+00:00
-- url     : https://prove2.me/theorems/239c295c-2fd4-52ca-ab2f-a1abf504696e
-- title:
--   Étale cohomology of the projective line, library file 31 of 34
-- statement:
--   File 31 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_P1Clo`: S4-EtCompact, E3 (O7b): sheaves on `P¹` with zero generic stalk are acyclic
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_30

/-!
# Étale cohomology of the projective line, library file 31 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_P1Clo`: S4-EtCompact, E3 (O7b): sheaves on `P¹` with zero generic stalk are acyclic
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

/-- The middle Mayer-Vietoris term of `P¹` has no `Ext^(n+2)` into `Z` when `Z_η̄ = 0`. -/
theorem P1.H_closed_X₂ (Z : EtSh Λ (P1 k)) (hη : IsZero (Cech.Mx Z (P1.genPt k))) (n : ℕ) :
    Subsingleton (Abelian.Ext (mvS (unitSh Λ (P1 k)) (chartA1 k).opensRange (chartA1' k).opensRange).X₂
        Z (n + 1 + 1)) := by
      refine subsingleton_ext_biprod ?_ ?_
      · refine ⟨fun a b => (cutExt (chartA1 k) Z (n + 1 + 1)).injective ?_⟩
        rw [chart_H k k[X] (chartA1 k) Z hη (n + 1) (cutExt (chartA1 k) Z (n + 1 + 1) a),
          chart_H k k[X] (chartA1 k) Z hη (n + 1) (cutExt (chartA1 k) Z (n + 1 + 1) b)]
      · refine ⟨fun a b => (cutExt (chartA1' k) Z (n + 1 + 1)).injective ?_⟩
        rw [chart_H k k[X] (chartA1' k) Z hη (n + 1) (cutExt (chartA1' k) Z (n + 1 + 1) a),
          chart_H k k[X] (chartA1' k) Z hη (n + 1) (cutExt (chartA1' k) Z (n + 1 + 1) b)]

end RamanujanPetersson.EtCompact.CurveHn

end

end


