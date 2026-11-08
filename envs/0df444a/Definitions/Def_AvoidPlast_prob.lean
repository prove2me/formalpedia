-- Prove2me | Definitions.Def_AvoidPlast_prob
-- name    : AvoidPlast_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:02.088205+00:00
-- url     : https://prove2.me/theorems/a9c6b0df-44d2-42d4-8cb4-9b27ababdc83
-- title:
--   Probability over uniform strings
-- statement:
--   For a predicate $P$ on bit strings, $\mathrm{prob}(n,P)=\Pr_{x\in\{0,1\}^n}[P(x)]=|\{x\in\{0,1\}^n:P(x)\}|/2^n$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.14, p.29

import Mathlib

namespace AvoidPlast

open Classical in
/-- The probability of a predicate over a uniform string `x ∈ {0,1}^n` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 5.14, p.29,
`Pr_{x∈{0,1}^n}`). -/
noncomputable def prob (n : ℕ) (P : List Bool → Prop) : ℝ :=
  ((Finset.univ.filter fun x : Fin n → Bool => P (List.ofFn x)).card : ℝ) / 2 ^ n

end AvoidPlast


