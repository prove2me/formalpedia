-- Prove2me | Definitions.Def_ImpactCopula_restrInvE
-- name    : ImpactCopula_restrInvE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:06.071205+00:00
-- url     : https://prove2.me/theorems/3bead8ac-6c7f-4493-b98e-5af432d9e94f
-- title:
--   Restricted inverse $\underline f^{-1}(w) = \inf\{v \in S : f(v) \ge w\}$
-- statement:
--   For a set $S \subseteq \mathbb R$ and a function $f : \mathbb R \to \mathbb R$, the **restricted inverse** of Lemma 2 is
--
--   $$
--   \underline f^{-1}(w) = \inf\{v \in S : f(v) \ge w\} \in [-\infty, +\infty],
--   $$
--
--   with $\inf\emptyset = +\infty$. In Lemma 2 and in (A.71)–(A.72), $S = \overline{\mathcal R}_\theta$.
--
--   **Formalization Note** The infimum is taken in `EReal`. With the real convention $\inf\emptyset = 0$, part (ii) of Lemma 2 would fail (take $f = \mathbf 1_{[2,\infty)}$, $w = v = 1/2$).
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Lemma 2, p.75 (PDF p.78)

import Mathlib

namespace ImpactCopula

/-- The restricted inverse of Lemma 2, Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.75 (PDF p.78):
`f̲⁻¹(w) = inf {v : f(v) ≥ w, v ∈ S}` (in the paper `S = R̄_θ`), computed in the extended reals.

**Formalization Note.** The infimum is taken in `EReal`, so the empty set gives `+∞`, the
paper's convention; with Lean's real `sInf ∅ = 0` part (ii) of Lemma 2 would be false
(`f = 1_{[2, ∞)}`, `w = v = 1/2`). -/
noncomputable def restrInvE (S : Set ℝ) (f : ℝ → ℝ) (w : ℝ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' {v : ℝ | v ∈ S ∧ w ≤ f v})

end ImpactCopula


