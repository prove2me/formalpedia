-- Prove2me | Definitions.Def_AvoidPlast_padLen
-- name    : AvoidPlast_padLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:10.363095+00:00
-- url     : https://prove2.me/theorems/7abe5c98-c79e-4957-bad8-7f1dda7aacb5
-- title:
--   The padding length
-- statement:
--   The padding length $\ell=\lceil n^{k/\alpha}\rceil$ of the proof of Theorem 5.14.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Proof of Theorem 5.14, (2)⇒(1), p.30

import Mathlib

namespace AvoidPlast

/-- The padding length `ℓ = ⌈n^{k/α}⌉` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), proof of Theorem 5.14, (2)⇒(1), p.30). -/
noncomputable def padLen (k : ℕ) (α : ℚ) (n : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ ((k : ℝ) / (α : ℝ))⌉₊

end AvoidPlast


