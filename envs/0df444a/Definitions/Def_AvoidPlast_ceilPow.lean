-- Prove2me | Definitions.Def_AvoidPlast_ceilPow
-- name    : AvoidPlast_ceilPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:27.098306+00:00
-- url     : https://prove2.me/theorems/28ddd565-34d0-4a84-8aa1-6dab586f5eaf
-- title:
--   The length $\lceil n^\varepsilon\rceil$
-- statement:
--   The integer length $\lceil n^\varepsilon\rceil$, for a real exponent. So $m_\varepsilon(n)$ of Definition 5.13 is `ceilPow (ε ^ 2) n`.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 5.13, p.29; Assumption 1.1, p.3

import Mathlib

namespace AvoidPlast

/-- The length `⌈n^ε⌉` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 5.13, p.29, `m_ε(n) = ⌈n^{ε²}⌉`; Assumption 1.1, p.3). -/
noncomputable def ceilPow (ε : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ ε⌉₊

end AvoidPlast


