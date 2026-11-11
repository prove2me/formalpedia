-- Prove2me | Definitions.Def_PermInvCC_Phi
-- name    : PermInvCC_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:06.537394+00:00
-- url     : https://prove2.me/theorems/29d963b5-c05c-4e45-9e57-1399cb1a3580
-- title:
--   Cost function $\Phi_n(s)=s\log(2+n/s)$
-- statement:
--   For $s>0$,
--   $$\Phi_n(s):=s\log(2+n/s),$$
--   with logarithms base two. It is the shape of the bound in Theorems 1.1 and 3.1.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 2.7, p.11

import Mathlib

namespace PermInvCC

/-- The **communication cost function** `Φₙ(s) := s log(2 + n/s)` (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, Lemma 2.7, p.11); logarithms are base two
(p.9). Used for `s > 0`. -/
noncomputable def Phi (n : ℕ) (s : ℝ) : ℝ := s * Real.logb 2 (2 + n / s)

end PermInvCC


