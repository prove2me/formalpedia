-- Prove2me | Definitions.Def_PrefixVR_prefixGrad
-- name    : PrefixVR_prefixGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:48.638413+00:00
-- url     : https://prove2.me/theorems/dad769f6-417b-46d5-82fe-9c5f6476fc3e
-- title:
--   Prefix gradient $P_r(x)=\frac1n\sum_{i=1}^r\nabla f_i(x)$
-- statement:
--   For component gradient maps $g_i=\nabla f_i$ and $r\ge0$, the **prefix gradient** is
--   $$
--   P_r(x)=\frac1n\sum_{i=1}^r\nabla f_i(x),\qquad P_0(x)=0 .
--   $$
--   The normalization is $1/n$ even when $r<n$, so $P_n=\nabla f$. The prefix accumulator $h_{s,r}$ of Algorithm 1 estimates $P_r$ at the current point; its error $a_{s,r}=h_{s,r}-P_r(x_{sn+r+1})$ is controlled by (32).
--
--   **Formalization Note** Components are `Fin n`; the paper's indices $1,\dots,r$ are the Lean indices $i$ with $i<r$. For $r\ge n$ the sum runs over all components.
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), §3.1, p.5 (PDF p.5), definition of P_r before (4)

import Mathlib

namespace PrefixVR

/-- **The prefix gradient** `P_r(x) := (1/n) ∑_{i=1}^r ∇fᵢ(x)`, `P₀(x) := 0`.
Jiang, Wang, Yang, Li, Zhang (manuscript, sha256 ed33106a…), §3.1, p.5: "The normalization is
1/n, including when r < n." `P_n = ∇f`.

**Formalization Note.** Components are `Fin n`; the paper's index `i ∈ {1, …, r}` is the Lean
index `i.val < r`. The maps `g i` stand for `∇fᵢ`. For `r ≥ n` the sum is over all components. -/
noncomputable def prefixGrad {n d : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r), g i x

end PrefixVR


