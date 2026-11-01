-- Prove2me | Definitions.Def_SelfGuidedALP_IsAlgorithm2Run
-- name    : SelfGuidedALP_IsAlgorithm2Run
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:34.16437+00:00
-- url     : https://prove2.me/theorems/aef6806e-bf6b-426e-a2cf-b0b926476aae
-- title:
--   A run of Algorithm 2 (self-guided FALP)
-- statement:
--   Fix a batch size $b$, a state-relevance distribution $\nu_0$ and a sample stream $\theta^1,\theta^2,\dots$. A sequence $\beta^{\mathrm{SG}}_{b},\beta^{\mathrm{SG}}_{2b},\dots,\beta^{\mathrm{SG}}_{nb}$ with $\beta^{\mathrm{SG}}_{kb}\in\mathbb R^{kb+1}$ is a **run of Algorithm 2** when
--
--   1. $\beta^{\mathrm{SG}}_{b}$ is an optimal solution of $\mathrm{FALP}_b$ formulated with the first $b$ samples;
--   2. for $1\le k<n$, $\beta^{\mathrm{SG}}_{(k+1)b}$ is an optimal solution of $\mathrm{FALP}^{\mathrm{SG}}_{(k+1)b}$ formulated with the first $(k+1)b$ samples, $\nu_0$ and the VFA $V(\cdot;\beta^{\mathrm{SG}}_{kb})$.
--
--   **Formalization Note** The paper's convention $V(s;\beta^{\mathrm{SG}}_{0})=-\infty$ makes (9) redundant in the first iteration, which is item 1. The sample stream is fixed: this records one realization of the algorithm.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Algorithm 2, p.17

import Mathlib
import Definitions.Def_SelfGuidedALP_IsFALPOptimal
import Definitions.Def_SelfGuidedALP_IsFALPSGOptimal

open MeasureTheory

namespace SelfGuidedALP

/-- `iter` is a run of Algorithm 2 (self-guided FALP) with batch size `b`, state-relevance
distribution `ν₀` and sample stream `θ`, through iteration `n`: `iter k` is the vector `β^SG_{kb}`,
the first iterate solves `FALP_b` (the paper's convention `V(·;β^SG_0) = −∞` makes (9) redundant
there), and for `1 ≤ k < n` the iterate `iter (k + 1)` solves `FALP^SG_{(k+1)b}`, formulated with the
first `(k + 1) b` samples, `ν₀` and the VFA `V(·;β^SG_{kb})`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Algorithm 2, p.17).

**Formalization Note.** `iter k` has `k * b + 1` entries, and the first `k * b` samples are the
restriction of `θ` to `Fin (k * b)`. -/
def IsAlgorithm2Run {d m : ℕ} (M : MDP d m) (R : RBClass d)
    (ν₀ : Measure (EuclideanSpace ℝ (Fin d))) (θ : ℕ → EuclideanSpace ℝ (Fin (d + 1))) (b n : ℕ)
    (iter : (k : ℕ) → Fin (k * b + 1) → ℝ) : Prop :=
  IsFALPOptimal M R ν₀ (fun i : Fin (1 * b) => θ i) (iter 1) ∧
    ∀ k, 1 ≤ k → k < n →
      IsFALPSGOptimal M R ν₀ (fun i : Fin ((k + 1) * b) => θ i)
        (vfa R (fun i : Fin (k * b) => θ i) (iter k)) (iter (k + 1))

end SelfGuidedALP


