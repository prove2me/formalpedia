-- Prove2me | Definitions.Def_RPLib_FX_EtP1_25
-- name    : RPLib_FX_EtP1_25
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T13:30:27.610128+00:00
-- url     : https://prove2.me/theorems/dc1d4759-8cf9-51df-8074-792d2a8feb28
-- title:
--   Étale cohomology of the projective line, library file 25 of 34
-- statement:
--   File 25 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_P1H2`: S4-EtCompact: `H^2(P^1, Λ) ≃ Λ` and `H^2_c(A^1, Λ) ≃ Λ` (O8c, file M6)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_40

/-!
# Étale cohomology of the projective line, library file 25 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_P1H2`: S4-EtCompact: `H^2(P^1, Λ) ≃ Λ` and `H^2_c(A^1, Λ) ≃ Λ` (O8c, file M6)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_P1H2 =====
section

/-!
# S4-EtCompact: `H^2(P^1, Λ) ≃ Λ` and `H^2_c(A^1, Λ) ≃ Λ` (O8c, file M6)

`k` algebraically closed, `l` prime invertible in `k`, `lⁿ • Λ = 0` (`n > 0`).

* `A1.subsingleton_h2`: `H^2(A^1, Λ) = 0` (`H2Pid.H_A1_two_eq_zero`);
* **`P1.nonempty_h2Equiv`**: `H^2(P^1, Λ) ≃+ Λ` (Mayer-Vietoris `P1.h2EquivGm` + `Gm.nonempty_h1Equiv`);
* **`A1.nonempty_hc2Equiv`**: `H^2_c(A^1, Λ) ≃+ Λ` (`A1.hcEquivP1`).
-/

set_option autoImplicit false

open Polynomial AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {l n : ℕ} [Fact l.Prime]

/-- **`H^2(P^1_k, Λ) ≃ Λ`.** -/
theorem P1.nonempty_h2Equiv (hn : 0 < n) (hl : (l : k) ≠ 0) (hΛ : ((l ^ n : ℕ) : Λ) = 0) :
    Nonempty (H Λ (unitSh Λ (P1 k)) 2 ≃+ Λ) := by
  have hN : ((l ^ n : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  have h1 : Subsingleton (H Λ (unitSh Λ (A1 k)) 1) := A1.subsingleton_h1 k hN hΛ
  obtain ⟨e⟩ := Gm.nonempty_h1Equiv k hn hl hΛ
  exact ⟨(P1.h2EquivGm k h1 (A1.subsingleton_h2 k hl hΛ)).trans e⟩

end RamanujanPetersson.EtCompact

end

end


