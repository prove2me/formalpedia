-- Prove2me | Definitions.Def_AvoidPlast_DiagHard
-- name    : AvoidPlast_DiagHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:49:25.413196+00:00
-- url     : https://prove2.me/theorems/6392d365-08d7-4438-8d38-87e88f3d25f3
-- title:
--   Item 3 of Theorem 5.14
-- statement:
--   For every constant $\varepsilon\in(0,1)$ and every deterministic polynomial-time machine $B$, for every sufficiently large $n$,
--
--   $$\Pr_{x\in\{0,1\}^n}[B(x)\in\mathrm{Diag}_\varepsilon(x)]\le n^{-\omega(1)}.$$
--
--   This is the hardness of the low-space diagonalization problem for polynomial time.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.14, item 3, p.29

import Mathlib
import Definitions.Def_QuantumPRC_Negligible
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_PolyTime
import Definitions.Def_AvoidPlast_Diag

namespace AvoidPlast

/-- Item 3 of Theorem 5.14 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.29): for every constant `ε ∈ (0,1)` and every deterministic
polynomial-time machine `B`, for every sufficiently large `n`,
`Pr_x[B(x) ∈ Diag_ε(x)] ≤ n^{-ω(1)}`. -/
def DiagHard : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ B : Machine 1, PolyTime B →
    ∃ ν : ℕ → ℝ, QuantumPRC.Negligible ν ∧ ∀ᶠ n : ℕ in Filter.atTop,
      prob n (fun x => output B ![x] ∈ Diag ε x) ≤ ν n

end AvoidPlast


