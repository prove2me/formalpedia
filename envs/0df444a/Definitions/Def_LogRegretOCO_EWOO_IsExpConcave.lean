-- Prove2me | Definitions.Def_LogRegretOCO_EWOO_IsExpConcave
-- name    : LogRegretOCO_EWOO_IsExpConcave
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:42:19.776987+00:00
-- url     : https://prove2.me/theorems/6652fb68-194f-4626-b37b-9cd407cc67d1
-- title:
--   α-exp-concavity: exp(−α f) is concave on P (§2.2)
-- statement:
--   Let $P \subseteq \mathbb{R}^n$ and let $g : \mathbb{R}^n \to \mathbb{R}$. For a real number $\alpha$, the function $g$ is called **$\alpha$-exp-concave on $P$** if the function
--
--   $$
--   x \longmapsto e^{-\alpha g(x)}
--   $$
--
--   is concave on $P$, that is, $e^{-\alpha g(\lambda x + (1-\lambda) y)} \ge \lambda e^{-\alpha g(x)} + (1-\lambda) e^{-\alpha g(y)}$ for all $x, y \in P$ and $\lambda \in [0,1]$ (this presupposes that $P$ is convex).
--
--   This is the curvature condition under which Exponentially Weighted Online Optimization attains logarithmic regret. It is weaker than strong convexity with bounded gradients, and it is satisfied by the log-loss $-\log(a^\top x)$ of universal portfolio selection with $\alpha = 1$.
--
--   **Formalization Note** The paper's definition also requires $\alpha > 0$; here the positivity of $\alpha$ is kept as a separate hypothesis in every theorem that uses the predicate. Points live in `EuclideanSpace ℝ (Fin n)`, so $\|\cdot\|$ is the Euclidean norm, and $g$ is defined on the whole space; only its values on $P$ matter.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 173, §2.2 (α-exp-concavity: "there is an α > 0 such that exp(−αf_t(x)) is a concave function of x ∈ P, for all t")

import Mathlib

namespace LogRegretOCO.EWOO

/-- α-exp-concavity on `P` (Hazan–Agarwal–Kale 2007, §2.2, p. 173): the function
`x ↦ exp(-α g(x))` is concave on `P`. The positivity `α > 0` of the paper's definition is a
separate hypothesis wherever this predicate is used. -/
def IsExpConcave {n : ℕ} (α : ℝ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ConcaveOn ℝ P (fun x => Real.exp (-α * g x))

end LogRegretOCO.EWOO


