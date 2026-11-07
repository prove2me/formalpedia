-- Prove2me | Definitions.Def_AvgValueAlloc_routBank
-- name    : AvgValueAlloc_routBank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:07.334031+00:00
-- url     : https://prove2.me/theorems/602ab586-ddda-470d-b07b-a621fd3820db
-- title:
--   Routings and earned banks $B(X)$
-- statement:
--   A **routing** $X$ of funding items $M=(v_1,\dots,v_m)$ chooses for each item at most one positive recipient $j\in J(v_t)$. Its earned bank is
--   $$
--   B_j(X)=\sum_{t:\ X_t=j}(v_{tj}-\rho_j)\ \ge 0,
--   $$
--   and $B^{<t}(X)$ is the bank earned before position $t$.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2.1, p.5

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec

namespace AvgValueAlloc

/-- **Routings of funding items, their earned banks.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.1, p.5: "An actual routing X chooses at most one
positive recipient per funding item. Its original welfare is W(X) and its earned surplus is B(X)".

For funding items `M t` (`t : Fin m`), `IsRouting ρ M X` says each `X t` is either `none` or a
positive alternative `j ∈ J(M t)`. `routBank ρ M X` is the earned surplus
`B_j(X) = Σ_{t : X t = j} (v_{tj} − ρ_j)`; `prefBank ρ M X t` is the same sum over the items before
position `t`. -/
def IsRouting {n m : ℕ} (ρ : Fin n → ℚ) (M : Fin m → Vec n) (X : Fin m → Option (Fin n)) : Prop :=
  ∀ t j, X t = some j → ρ j ≤ (M t j : ℚ)

/-- `B(X)`: the earned bank of a routing. -/
noncomputable def routBank {n m : ℕ} (ρ : Fin n → ℚ) (M : Fin m → Vec n)
    (X : Fin m → Option (Fin n)) : Fin n → ℝ :=
  fun j => ∑ t ∈ Finset.univ.filter (fun t => X t = some j), (((M t j : ℚ≥0) : ℝ) - ρ j)

/-- The bank earned by the items before position `t`. -/
noncomputable def prefBank {n m : ℕ} (ρ : Fin n → ℚ) (M : Fin m → Vec n)
    (X : Fin m → Option (Fin n)) (t : ℕ) : Fin n → ℝ :=
  fun j => ∑ s ∈ Finset.univ.filter (fun s : Fin m => s.val < t ∧ X s = some j),
    (((M s j : ℚ≥0) : ℝ) - ρ j)

end AvgValueAlloc


