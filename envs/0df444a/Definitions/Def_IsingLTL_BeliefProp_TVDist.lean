-- Prove2me | Definitions.Def_IsingLTL_BeliefProp_TVDist
-- name    : IsingLTL_BeliefProp_TVDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:49.753568+00:00
-- url     : https://prove2.me/theorems/9735044f-8cba-4ace-841a-c01ca6ec1839
-- title:
--   Distributions on a finite set, the pairing $\langle \nu, f\rangle$ and the total variation distance
-- statement:
--   Let $\mathcal X$ be a finite set. A **distribution** on $\mathcal X$ is a function $p:\mathcal X\to\mathbb R$ with $p(x)\ge 0$ for all $x$ and $\sum_x p(x)=1$. For a distribution $\nu$ and a function $f$ on $\mathcal X$, the **pairing** is
--   $$\langle \nu, f\rangle = \sum_{x\in\mathcal X} f(x)\,\nu(x).$$
--   The **total variation distance** between two distributions $p,q$ on $\mathcal X$ is
--   $$\|p-q\|_{\mathrm{TV}} = \frac12\sum_{x\in\mathcal X}|p(x)-q(x)|.$$
--
--   These three notions are used by every statement of the mission: the BP convergence bound (2.11), the marginal approximation (2.13), Lemma 3.3 and the boundary-effect bound (4.4).
--
--   **Formalization Note** The normalization of the total variation distance is $\tfrac12\ell^1$, the one under which the paper's proofs of Lemma 3.3 and Theorem 2.7 are correct. For two distributions on $\{+1,-1\}$ it equals $|p(+1)-q(+1)|$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 7 (total variation distance) and §3, p. 9 (the pairing ⟨ν, f⟩)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_IsingModel

namespace IsingLTL.BeliefProp

/-- A **distribution** on a finite set `X` (Dembo–Montanari, *Ising Models on Locally Tree-Like
Graphs*, arXiv:0804.4726v3, §3, p. 9): a function `p : X → ℝ` with nonnegative values summing
to `1`. -/
def IsDistribution {X : Type*} [Fintype X] (p : X → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- The **total variation distance** `‖p − q‖_TV = ½ ∑ₓ |p(x) − q(x)|` between two functions
(distributions) on a finite set (arXiv:0804.4726v3, p. 7, used in (2.11), (2.13), (3.3), (4.4)).

Formalization Note: the normalization is `½ ℓ¹`, the one under which the proof of Lemma 3.3
(`|⟨ν,f⟩ − ⟨ν′,f⟩| ≤ f_max ‖ν − ν′‖_TV`) and the proof of Theorem 2.7 are correct. For two
distributions on `{+1, −1}` it equals `|p(+1) − q(+1)|`. -/
noncomputable def tvDist {X : Type*} [Fintype X] (p q : X → ℝ) : ℝ :=
  (∑ x, |p x - q x|) / 2

end IsingLTL.BeliefProp


