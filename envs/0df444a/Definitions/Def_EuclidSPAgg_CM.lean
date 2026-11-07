-- Prove2me | Definitions.Def_EuclidSPAgg_CM
-- name    : EuclidSPAgg_CM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:37.851991+00:00
-- url     : https://prove2.me/theorems/2beac430-4b19-4fa9-a3aa-e52625cfda78
-- title:
--   Coordinate-wise median $\mathrm{CM}_{n,d}$
-- statement:
--   Let $\mathcal B_0$ be the standard basis of $\mathbb R^d$. The **coordinate-wise median** $\mathrm{CM}_{n,d}$ is the rule $Q_{\mathcal B_0,k}$ that uses rank $(n+1)/2$ in every coordinate when $n$ is odd and rank $n/2$ in every coordinate when $n$ is even, i.e. rank $\lceil n/2\rceil$ (the lower middle rank).
--
--   **Formalization Note** The standard basis is `EuclideanSpace.basisFun`. The rank $\lceil n/2\rceil$ is the $0$-based index $\lfloor (n-1)/2\rfloor$. For $n=0$ there are no ranks and the rule is a placeholder constant; every statement using it has $n\ge2$.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidSPAgg_Q
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- The coordinate-wise median `CM_{n,d}` (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11)): the rule
`Q_{B₀,k}` in the standard basis `B₀` of `ℝᵈ` using rank `(n+1)/2` in every coordinate when `n` is
odd and rank `n/2` when `n` is even.

**Formalization Note** `B₀` is `EuclideanSpace.basisFun (Fin d) ℝ`. The paper's rank `⌈n/2⌉`
(= `(n+1)/2` for odd `n`, `n/2` for even `n`) is the 0-based index `(n − 1)/2` (natural-number
division). For `n = 0` there are no ranks and the value `0` is a placeholder; every statement
using `CM` has `n ≥ 2`. -/
noncomputable def CM (n d : ℕ) : Mech n d :=
  if h : 0 < n then Q (EuclideanSpace.basisFun (Fin d) ℝ) (fun _ => ⟨(n - 1) / 2, by omega⟩)
  else fun _ => 0

end EuclidSPAgg


