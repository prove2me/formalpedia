-- Prove2me | Definitions.Def_OrderedExperts_phi
-- name    : OrderedExperts_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:43.278736+00:00
-- url     : https://prove2.me/theorems/c0142cc9-0e4a-40d5-b382-72a62ecc6afc
-- title:
--   Closed-form flows $\varphi_j$
-- statement:
--   For a vector $\pi$ on ranks and a target rank $j$, the **flows** used by the endpoint flow estimator are
--   $$
--   \varphi_j(0,a)=\frac{\pi(a)}{\Pi[1,j]}\quad(1\le a\le j),\qquad
--   \varphi_j(a,b)=\frac{\pi(a)\pi(b)}{\Pi[a,j]\,\Pi(a,j]}\quad(1\le a<b\le j),
--   $$
--   and $\varphi_j(a,b)=0$ for all edges outside $0\le a<b\le j$. Edge $(0,a)$ is an anchor edge and $(a,b)$ with $a\ge1$ an interval edge.
--
--   These are the edge-use probabilities of the random increasing path (Lemma 7); Algorithm 1's estimate weights the revealed increments by them.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 3.3, p.8

import Definitions.Def_OrderedExperts_massCC
import Definitions.Def_OrderedExperts_massOC

namespace OrderedExperts

/-- **Closed-form flows `φj`.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 3.3, p.8: "Its edge-use
probabilities, computed in Appendix A, are `φj(0, a) = π(a)/Π[1, j]` (`a ≤ j`),
`φj(a, b) = π(a)π(b)/(Π[a, j]Π(a, j])` (`1 ≤ a < b ≤ j`). Set `φj(a, b) = 0` for all edges outside
`0 ≤ a < b ≤ j`."

`phi π j a b` is the anchor flow `π(b)/Π[1, j]` when `a = 0` and `1 ≤ b ≤ j`, the interval flow
`π(a)π(b)/(Π[a, j]Π(a, j])` when `1 ≤ a < b ≤ j`, and `0` otherwise. These are the flows the
endpoint-flow estimate of Algorithm 1 uses. -/
noncomputable def phi (π : ℕ → ℝ) (j a b : ℕ) : ℝ :=
  if a = 0 ∧ 1 ≤ b ∧ b ≤ j then π b / massCC π 1 j
  else if 1 ≤ a ∧ a < b ∧ b ≤ j then π a * π b / (massCC π a j * massOC π a j)
  else 0

end OrderedExperts


