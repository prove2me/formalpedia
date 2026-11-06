-- Prove2me | Definitions.Def_TIESharp_marg
-- name    : TIESharp_marg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:42.842199+00:00
-- url     : https://prove2.me/theorems/febfa8e1-ef14-453c-9e7f-04382450565d
-- title:
--   Marginal assignment probability $q^m_{ij}(b)$
-- statement:
--   The **marginal probability** of assigning job $j$ to machine $i$ at bids $b$ is
--   $$q^m_{ij}(b)=\Pr_{A\sim y^m(b)}[A(j)=i]=\sum_{A\in\mathcal A_{m,n},\,A(j)=i}y^m_A(b).$$
--   Machine $i$'s expected processing cost at true type $t_i$ is $t_i\cdot q^m_i(b)=\sum_j t_{ij}q^m_{ij}(b)$.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §2, p.3

import Mathlib
import Definitions.Def_TIESharp_Family

set_option autoImplicit false

namespace TIESharp

/-- The **marginal probability** of assigning job `j` to machine `i` (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §2, p.3):
`q^m_ij(b) = P_{A ∼ y^m(b)}[A(j) = i] = Σ_{A : A(j) = i} y^m_A(b)`. -/
def marg {n : ℕ} (F : Family n) (m : ℕ) (b : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i), F.alloc m b A

end TIESharp


