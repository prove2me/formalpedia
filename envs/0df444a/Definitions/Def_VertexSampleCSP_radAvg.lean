-- Prove2me | Definitions.Def_VertexSampleCSP_radAvg
-- name    : VertexSampleCSP_radAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:28.778465+00:00
-- url     : https://prove2.me/theorems/46de09f0-b518-42ca-9138-91ae57c26682
-- title:
--   Expectation over independent Rademacher signs
-- statement:
--   A Rademacher sign is uniform on $\{-1,1\}$. For a finite index set $J$, the expectation of $X(\epsilon)$ over a family $\epsilon=(\epsilon_j)_{j\in J}$ of independent Rademacher signs is the average of $X$ over the $2^{|J|}$ sign vectors.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "Notation", p.13 (PDF p.15); Lemma A.3, p.14 (PDF p.16)

import Mathlib

namespace VertexSampleCSP

/-- **Expectation over independent Rademacher signs.** Chang, *Optimal Vertex Sampling for
Constraint Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A,
"Notation", p.13 (PDF p.15): "A Rademacher sign is a random variable uniform on {−1, 1}"; Lemma A.3,
p.14.

`radAvg X` is the expectation of `X(ϵ)` for a family `ϵ = (ϵ_j)_{j ∈ J}` of independent Rademacher
signs: the average of `X` over the `2^{|J|}` sign vectors, written as the average over `s : J → Bool`
with `true ↦ 1` and `false ↦ −1`. -/
noncomputable def radAvg {J : Type*} [Fintype J] [DecidableEq J] (X : (J → ℝ) → ℝ) : ℝ :=
  (∑ s : J → Bool, X (fun j => if s j then 1 else -1)) / 2 ^ Fintype.card J

end VertexSampleCSP


