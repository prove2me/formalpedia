-- Prove2me | Definitions.Def_MatchedUCLB_OracleAlg
-- name    : MatchedUCLB_OracleAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:21.967096+00:00
-- url     : https://prove2.me/theorems/9012ccb2-5109-4a72-b568-aa289b71afc0
-- title:
--   Deterministic algorithm with $p$th-order oracle access
-- statement:
--   A **deterministic algorithm with $p$th-order oracle access** on $\mathbb R^d$ is given by two families of maps on histories. After $s$ oracle calls the available information is the history $H_s=((x_\ell,O_\ell))_{\ell=1}^s$ of evaluation points and oracle outputs ($H_0=\emptyset$). The algorithm chooses
--
--   $$
--   x_{s+1}=\mathcal A_{s+1}(H_s),\qquad \hat x_s=\hat{\mathcal A}_s(H_s),
--   $$
--
--   the next evaluation point and the candidate solution after $s$ calls. Both are arbitrary deterministic functions of the history: they may have any norm, the candidate need not be an evaluation point, a candidate $\hat x_0$ before the first call is allowed, and no restriction to the span of earlier gradients is imposed.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, with the Euclidean inner product and norm. A history of length $s$ is a map from $\{0,\dots,s-1\}$ to pairs (point, oracle output). Dependence on the prescribed parameters and on the initialization comes from quantifying the algorithm after them.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Definition B.1, p.17; Eqs. (F.1)–(F.2), p.98

import Mathlib
import Definitions.Def_MatchedUCLB_OracleOut

namespace MatchedUCLB

/-- **Deterministic algorithm with pth-order oracle access.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Definition B.1, p.17: "Each
evaluation point is a deterministic function of the prescribed parameters, initialization, and
preceding evaluation points and oracle outputs. After `s` calls, a candidate solution `x̂_s` is any
deterministic function of this information; it need not be an evaluation point. A candidate
solution `x̂_0` before the first oracle call is also allowed." (F.1)–(F.2), p.98:
`H_s = ((x_ℓ, O_ℓ))_{ℓ=1}^s`, `H_0 = ∅`, `x_{s+1} = A_{s+1}(H_s)`, `x̂_s = Â_s(H_s)`.

An algorithm consists of two families of maps on histories: `next s H` is the evaluation point
`x_{s+1}` chosen after `s` calls with history `H`, and `cand s H` is the candidate solution `x̂_s`.

**Formalization Note.** A history of length `s` is a map `Fin s → ℝ^d × OracleOut d p`; entry
`ℓ` (0-based) is the pair `(x_{ℓ+1}, O_{ℓ+1})`. Any Lean function is allowed, so evaluation
points and candidates are arbitrary deterministic functions of the history, with arbitrary norms
and no span restriction. Dependence on the prescribed parameters and on the initialization `x_0`
comes from quantifying the algorithm after them. -/
structure OracleAlg (d p : ℕ) where
  /-- `next s H = x_{s+1}`, the evaluation point of call `s + 1`. -/
  next : (s : ℕ) → (Fin s → EuclideanSpace ℝ (Fin d) × OracleOut d p) → EuclideanSpace ℝ (Fin d)
  /-- `cand s H = x̂_s`, the candidate solution after `s` calls. -/
  cand : (s : ℕ) → (Fin s → EuclideanSpace ℝ (Fin d) × OracleOut d p) → EuclideanSpace ℝ (Fin d)

end MatchedUCLB


