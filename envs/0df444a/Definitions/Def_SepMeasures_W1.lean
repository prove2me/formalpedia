-- Prove2me | Definitions.Def_SepMeasures_W1
-- name    : SepMeasures_W1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:33.216455+00:00
-- url     : https://prove2.me/theorems/f8d90980-02ae-4345-86ae-990463b25b46
-- title:
--   §2.4, p.14 — the 1-Wasserstein distance $W_1(\mu,\mu\')$
-- statement:
--   For probability measures $\mu,\mu'$ on $\mathbb R^d$, let $\Pi(\mu,\mu')$ be the set of probability measures on $\mathbb R^d\times\mathbb R^d$ with marginals $\mu$ and $\mu'$ (couplings). The **1-Wasserstein distance** with respect to a norm $\|\cdot\|$ is
--   $$W_1(\mu,\mu')=\inf_{\pi\in\Pi(\mu,\mu')}\int\!\!\int\|x-x'\|\,d\pi(x,x').$$
--   It is the least average distance that mass must move to turn $\mu$ into $\mu'$, and controls how much $L_{\mu,\nu}$ changes when the measures are replaced (Lemma 2.6).
--
--   **Formalization Note** $W_1$ is the published platform optimal transport cost `ShapleyNV.transportCost` with ground cost $c(x,x')=N(x-x')$; its couplings $\Pi(\mu,\mu')$ are the published platform definition `WassersteinDRO.StrongDuality.couplings`. The norm is a seminorm $N$; the value is taken in $[0,\infty]$ with a lower Lebesgue integral, so it has no junk values, and it is finite for measures with finite first moments.
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), §2.4, p.14

import Mathlib
import Definitions.Def_SepMeasures_Hyp
import Definitions.Def_ShapleyNV_transportCost

open MeasureTheory

namespace SepMeasures

/-- The 1-Wasserstein distance
`W₁(μ, μ′) := inf_{π ∈ Π(μ, μ′)} ∫∫ ‖x − x′‖ dπ(x, x′)` (Correa et al., manuscript sha256
96a86924…fa82f, §2.4, p.14), where `Π(μ, μ′)` is the set of probability measures on
`ℝ^d × ℝ^d` with marginals `μ` and `μ′`.

**Formalization Note.** This is the published platform optimal transport cost
`ShapleyNV.transportCost c μ μ′ = inf_{π ∈ couplings μ μ′} ∫⁻ ofReal (c x x′) dπ` with the ground
cost `c x x′ = N (x − x′)`, where `couplings` is the published
`WassersteinDRO.StrongDuality.couplings` (probability measures with the two push-forward
marginals). The norm is an arbitrary `N : Seminorm ℝ (E d)`. The value lives in `ℝ≥0∞` and the
integral is a lower Lebesgue integral, so there are no junk values (the cost is non-negative);
for measures with finite first moments it is finite. -/
noncomputable def W1 {d : ℕ} (N : Seminorm ℝ (E d)) (μ μ' : Measure (E d)) : ENNReal :=
  ShapleyNV.transportCost (fun x x' => N (x - x')) μ μ'

end SepMeasures


