-- Prove2me | Definitions.Def_AvoidPlast_Supplement_padExp
-- name    : AvoidPlast_Supplement_padExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:00:33.86041+00:00
-- url     : https://prove2.me/theorems/52a897ea-4dea-48c6-a99a-546f595a1cd8
-- title:
--   The padding length $T(n)^{1/\varepsilon}$
-- statement:
--   $\lceil T(n)^{1/\varepsilon}\rceil$, the length of the padding in Theorem 5.4.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.4, p.23

import Mathlib

namespace AvoidPlast.Supplement

/-- The padding length `T(n)^{1/ε}` of Theorem 5.4 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.23), rounded up: `⌈T(n)^{1/ε}⌉`
(reading R3). -/
noncomputable def padExp (T : ℕ → ℕ) (ε : ℝ) (n : ℕ) : ℕ := ⌈(T n : ℝ) ^ (1 / ε)⌉₊

end AvoidPlast.Supplement


