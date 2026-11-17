-- Prove2me | Definitions.Def_AvoidPlast_Supplement_expBound
-- name    : AvoidPlast_Supplement_expBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:09:33.075552+00:00
-- url     : https://prove2.me/theorems/a9461b04-e8e2-473e-b5e5-32ad396a5cb7
-- title:
--   The bound $2^{n^\rho}$
-- statement:
--   $\lceil 2^{n^\rho}\rceil$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 6.10, p.38; Theorems 6.9, 6.11, 7.11

import Mathlib

namespace AvoidPlast.Supplement

/-- The sub-exponential bound `⌈2^{n^ρ}⌉` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 6.10, p.38; Theorems 6.9, 6.11,
7.11). -/
noncomputable def expBound (ρ : ℝ) (n : ℕ) : ℕ := ⌈(2 : ℝ) ^ ((n : ℝ) ^ ρ)⌉₊

end AvoidPlast.Supplement


