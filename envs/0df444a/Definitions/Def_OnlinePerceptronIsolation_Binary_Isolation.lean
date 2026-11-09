-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Isolation
-- name    : OnlinePerceptronIsolation_Binary_Isolation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:34.149+00:00
-- url     : https://prove2.me/theorems/5368a30f-f122-4980-976f-34ed4f890866
-- title:
--   Closed Hamming-ball isolation and deterministic success
-- statement:
--   For sign vectors $\sigma,\tau\in\{-1,+1\}^n$, their Hamming distance $d(\sigma,\tau)$ counts unequal coordinates. For a real radius $h$, a solution $\sigma$ is $h$-isolated when
--   $$S(G,\kappa)\cap\{\tau:d(\sigma,\tau)\le h\}=\{\sigma\}.$$
--   For a deterministic output map $A$, its success probability is $\mathbb P_G(A(G)\in S^h(G,\kappa))$, under the referenced independent standard Gaussian matrix law. Isolation quantifies over every signing, including those no algorithm outputs. The equality includes the center: a negative radius gives no isolated solutions. This layer supplies the event used by both deterministic and randomized hardness results.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Definition 2.2, Eq. (2.3), printed p.6, PDF p.8; Eq. (3.13), printed p.11, PDF p.13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Solutions
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- Definition 2.2: the number of unequal coordinates. -/
noncomputable def hamming {n : ℕ} (σ τ : Fin n → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => σ i ≠ τ i).card

/-- Definition 2.2, equation (2.3). The biconditional includes membership of the center;
thus negative radii give no isolated points, just as the set equality in the source. -/
def IsIsolated {m n : ℕ} (G : Fin m × Fin n → ℝ) (κ h : ℝ)
    (σ : Fin n → ℝ) : Prop :=
  IsSolution G κ σ ∧ ∀ τ : Fin n → ℝ,
    (IsSolution G κ τ ∧ (hamming σ τ : ℝ) ≤ h) ↔ τ = σ

/-- Gaussian probability that the actual deterministic output is isolated. -/
noncomputable def detSuccess {m n : ℕ}
    (A : Fin n → (Fin m × Fin n → ℝ) → ℝ) (κ h : ℝ) : ℝ :=
  (ABPOnline.gaussMat m n).real {G | IsIsolated G κ h (fun i => A i G)}

end OnlinePerceptronIsolation.Binary


