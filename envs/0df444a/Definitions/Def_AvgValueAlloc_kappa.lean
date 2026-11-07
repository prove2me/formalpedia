-- Prove2me | Definitions.Def_AvgValueAlloc_kappa
-- name    : AvgValueAlloc_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:22.411385+00:00
-- url     : https://prove2.me/theorems/c31788ef-7b1f-407a-b864-52c47a36cefd
-- title:
--   Threshold crowding $\kappa(\rho)$
-- statement:
--   For thresholds $\rho\in\mathbb Q^n_{>0}$,
--   $$
--   \kappa(\rho)=\max_{a>0}\bigl|\{j:\ a\le\rho_j<2a\}\bigr|,\tag{2}
--   $$
--   the size of the most crowded half-open factor-two interval of thresholds. Thresholds $1,2,4,\dots$ have crowding one.
--
--   It is the range $1\le d\le\kappa(\rho)$ of ambiguities in the lower bounds.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.2, p.2, eq. (2)

import Mathlib

namespace AvgValueAlloc

open scoped Classical in
/-- **Threshold crowding `κ(ρ)`.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.2, p.2, (2):
"κ(ρ) = max_{a>0} |{j : a ≤ ρ_j < 2a}|".

`kappa ρ` is the largest number of thresholds in one half-open factor-two interval `[a, 2a)`,
`a > 0`.

**Formalization Note.** The maximum is a `sSup` in `ℕ` of a nonempty set bounded by `n`, hence
attained; `a` ranges over positive reals. For `n = 0` it is `0`. -/
noncomputable def kappa {n : ℕ} (ρ : Fin n → ℚ) : ℕ :=
  sSup {c : ℕ | ∃ a : ℝ, 0 < a ∧
    c = (Finset.univ.filter fun j => a ≤ (ρ j : ℝ) ∧ (ρ j : ℝ) < 2 * a).card}

end AvgValueAlloc


