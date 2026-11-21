-- Prove2me | Definitions.Def_mcorr_similarity
-- name    : mcorr_similarity
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T23:20:17.599108+00:00
-- url     : https://prove2.me/theorems/e2647b23-3623-4dde-8324-074e328887fe
-- title:
--   Asymptotic self-similarity and similarity in the Hausdorff topology
-- statement:
--   For a set $A\subseteq\mathbb{C}$ and $r>0$, the compact truncation is $A_r=(A\cap\overline{\mathbb{D}}_r)\cup\partial\mathbb{D}_r$ (`truncSet`). $A$ is self-similar about $c$ with scale $\lambda$ (`IsSelfSimilar`) if $(\lambda T_{-c}A)_r=(T_{-c}A)_r$ for some $r>0$. It is asymptotically $\lambda$-self-similar about $c$ with limit model $B$ (`IsAsymptoticallySelfSimilar`) if $(\lambda^n T_{-c}A)_r\to B_r$ in Hausdorff distance for some $r>0$; the standing assumptions (nonempty closed sets, $c\in A$, $|\lambda|>1$) are included. Two sets are asymptotically similar about $c$ (`IsAsymptoticallySimilar`) if $d_H((\lambda T_{-c}A)_r,(\lambda T_{-c}B)_r)\to0$ as $|\lambda|\to\infty$. `Xfiber` is the fiber $X(c)=\{x:(c,x)\in X\}$.
-- source:
--   C. Siqueira, Similarity between the Multibrot set and the Julia set of correspondences at Misiurewicz points, https://arxiv.org/abs/2509.07266, Section 2.2 (eq. 2.4, 2.5); Theorem 5.1.

import Mathlib

open Set Filter Topology Finset

namespace MultibrotCorr


/-- The compact truncation A_r = (A intersect closed disk of radius r) union (circle of radius r)
(paper, Section 2.2). -/
def truncSet (A : Set ℂ) (r : ℝ) : Set ℂ :=
  (A ∩ Metric.closedBall (0 : ℂ) r) ∪ Metric.sphere (0 : ℂ) r

/-- A is self-similar about c with scale lam (lam-self-similar): (lam T_{-c} A)_r = (T_{-c} A)_r
for some r > 0 (paper, Section 2.2, eq. (2.4)). -/
def IsSelfSimilar (A : Set ℂ) (c lam : ℂ) : Prop :=
  IsClosed A ∧ A.Nonempty ∧ c ∈ A ∧ 1 < ‖lam‖ ∧
  ∃ r : ℝ, 0 < r ∧
    truncSet ((fun z => lam * z) '' ((fun z => z - c) '' A)) r =
      truncSet ((fun z => z - c) '' A) r

/-- A is asymptotically lam-self-similar about c with limit model B: the sets (lam^n T_{-c} A)_r
converge to B_r in the Hausdorff topology of compact sets, for some r > 0 (paper, Section 2.2). -/
def IsAsymptoticallySelfSimilar (A : Set ℂ) (c lam : ℂ) (B : Set ℂ) : Prop :=
  IsClosed A ∧ A.Nonempty ∧ c ∈ A ∧ 1 < ‖lam‖ ∧ IsClosed B ∧ B.Nonempty ∧
  ∃ r : ℝ, 0 < r ∧
    Filter.Tendsto (fun k : ℕ =>
      Metric.hausdorffDist
        (truncSet ((fun z => lam ^ k * z) '' ((fun z => z - c) '' A)) r)
        (truncSet B r)) Filter.atTop (nhds 0)

/-- A and B are asymptotically similar about c: d_H((lam T_{-c} A)_r, (lam T_{-c} B)_r) tends to 0
as |lam| tends to infinity (paper, Section 2.2, eq. (2.5)). -/
def IsAsymptoticallySimilar (A B : Set ℂ) (c : ℂ) : Prop :=
  IsClosed A ∧ A.Nonempty ∧ IsClosed B ∧ B.Nonempty ∧ c ∈ A ∧ c ∈ B ∧
  ∃ r : ℝ, 0 < r ∧
    Filter.Tendsto (fun lam : ℂ =>
      Metric.hausdorffDist
        (truncSet ((fun z => lam * z) '' ((fun z => z - c) '' A)) r)
        (truncSet ((fun z => lam * z) '' ((fun z => z - c) '' B)) r))
      (Filter.comap (fun lam : ℂ => ‖lam‖) Filter.atTop) (nhds 0)

/-- The fiber X(c) = {x : (c, x) in X} of a subset X of C x C (paper, Theorem 5.1). -/
def Xfiber (X : Set (ℂ × ℂ)) (c : ℂ) : Set ℂ :=
  {x | (c, x) ∈ X}

end MultibrotCorr


