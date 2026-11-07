-- Prove2me | Definitions.Def_ContinualCounting_median3
-- name    : ContinualCounting_median3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:57.983254+00:00
-- url     : https://prove2.me/theorems/fc652eac-da29-406a-84b9-644df8b7e4ce
-- title:
--   The median of three real numbers
-- statement:
--   The median of three real numbers $a,b,c$ is $\max\{\min\{a,b\},\min\{\max\{a,b\},c\}\}$. It enters Corollary 1 and the derived mechanism $\widehat M_s$.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Corollary 1, p.10 (PDF p.11)

import Mathlib

set_option autoImplicit false

namespace ContinualCounting

/-- The median of three real numbers, as in `median{Z1, Z2, Z3}` of Corollary 1 (Bairaktari, Dahl,
Larsen, arXiv:2607.00876, sha256 986e6426…, p.10). -/
noncomputable def median3 (a b c : ℝ) : ℝ := max (min a b) (min (max a b) c)

end ContinualCounting


