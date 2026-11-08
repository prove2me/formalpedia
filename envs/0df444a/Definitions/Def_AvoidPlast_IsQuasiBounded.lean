-- Prove2me | Definitions.Def_AvoidPlast_IsQuasiBounded
-- name    : AvoidPlast_IsQuasiBounded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:10.006232+00:00
-- url     : https://prove2.me/theorems/67aa8f1a-cdee-4962-8ac9-479851e577d9
-- title:
--   Soundness errors $s\ge2^{-\mathrm{polylog}(n)}$
-- statement:
--   A soundness error $s:\mathbb N\to\mathbb R$ with $s(n)\ge2^{-\mathrm{polylog}(n)}$: for some $e$, $s(n)\ge2^{-e(\log_2(n+2))^e}$ for every $n$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.1, p.17

import Mathlib
import Definitions.Def_AvoidPlast_lg

namespace AvoidPlast

/-- A soundness error `s ≥ 2^{-polylog(n)}` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 4.1, p.17). -/
def IsQuasiBounded (s : ℕ → ℝ) : Prop :=
  ∃ e : ℕ, ∀ n : ℕ, (2 : ℝ) ^ (-((e : ℝ) * (lg n) ^ e)) ≤ s n

end AvoidPlast


