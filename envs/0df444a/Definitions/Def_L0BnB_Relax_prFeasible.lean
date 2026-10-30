-- Prove2me | Definitions.Def_L0BnB_Relax_prFeasible
-- name    : L0BnB_Relax_prFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:43:39.04844+00:00
-- url     : https://prove2.me/theorems/7c5cb782-fc55-4bb7-b1b9-21f596c4d7fb
-- title:
--   Feasible set of the interval relaxation of PR(∞)
-- statement:
--   A triple $(\beta,z,s)\in(\mathbb R^p)^3$ is **feasible for the interval relaxation of the perspective formulation** PR$(\infty)$ if for every $i\in[p]$
--
--   $$0\le z_i\le 1,\qquad s_i\ge 0,\qquad \beta_i^2\le s_iz_i .$$
--
--   This is the constraint set of (3) with $M=\infty$ (the Big-M constraints dropped) and the binaries $z_i$ relaxed to $[0,1]$.
--
--   **Formalization Note** The rotated second-order cone constraint is written multiplicatively, as in (3); with $z_i=0$ it forces $\beta_i=0$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, eq. (3) and the M = ∞ remark, p. 5; §2.2, p. 6

import Mathlib

namespace L0BnB.Relax

/-- **Feasible set of the interval relaxation of the perspective formulation PR(∞).**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, eq. (3), p. 5 ("`s.t. β²i ≤ sizi, i ∈ [p]`, `−Mzi ≤ βi ≤ Mzi, i ∈ [p]`,
`zi ∈ {0, 1}, si ≥ 0, i ∈ [p]`"), with `M = ∞` ("If we set M = ∞ in (3), then the constraints
βi ∈ [−Mzi, Mzi], i ∈ [p] can be dropped", p. 5) and `zᵢ` relaxed to `[0, 1]` (§2.2, p. 6).

`prFeasible β z s` holds iff for every `i`: `0 ≤ zᵢ ≤ 1`, `0 ≤ sᵢ` and `βᵢ² ≤ sᵢ zᵢ`.

**Formalization Note.** The rotated second-order cone constraint is written multiplicatively,
as printed in (3); with `zᵢ = 0` it forces `βᵢ = 0` (checked in the verification file). The
proof convention "`β²ᵢ/sᵢ = 0` when `βᵢ = sᵢ = 0`" (p. 28) is not used. -/
def prFeasible {p : ℕ} (β z s : Fin p → ℝ) : Prop :=
  ∀ i, 0 ≤ z i ∧ z i ≤ 1 ∧ 0 ≤ s i ∧ β i ^ 2 ≤ s i * z i

end L0BnB.Relax


