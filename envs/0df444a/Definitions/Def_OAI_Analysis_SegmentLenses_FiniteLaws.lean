-- Prove2me | Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
-- name    : OAI_Analysis_SegmentLenses_FiniteLaws
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:54:03.956402+00:00
-- url     : https://prove2.me/theorems/a6e141d9-2943-4f0a-be8f-cfe3ca9130b2
-- title:
--   Finite probability laws and their means
-- statement:
--   Let $\Omega$ be a finite set.
--
--   1. **Finite law.** A finite law $\mu$ on $\Omega$ is a weight function $\mu:\Omega\to\mathbb{R}$ with $\mu(\omega)\ge0$ for every $\omega$ and $\sum_{\omega\in\Omega}\mu(\omega)=1$. In other words, it is a probability distribution on $\Omega$.
--   2. **Mean.** The mean of a real function $f:\Omega\to\mathbb{R}$ under $\mu$ is
--   $$
--   \mathbb{E}_\mu f=\sum_{\omega\in\Omega}\mu(\omega)\,f(\omega).
--   $$
--   The file also records that the mean is normalized and linear: $\mathbb{E}_\mu c=c$ for constant functions, $\mathbb{E}_\mu(f+g)=\mathbb{E}_\mu f+\mathbb{E}_\mu g$, $\mathbb{E}_\mu(f-g)=\mathbb{E}_\mu f-\mathbb{E}_\mu g$, and $\mathbb{E}_\mu(cf)=c\,\mathbb{E}_\mu f$.
--
--   Finite laws are a lightweight replacement for probability measures on finite sets. They are used to average finitely many coefficient representations of dual functionals, and to compare squared means with means of squares in the energy budgets of the segment-norm estimates.
--
--   **Formalization Note** `FiniteLaw Ω` is a structure with fields `weight`, `nonneg` and `total` over a `Fintype`. The four algebraic identities are the simp lemmas `mean_const`, `mean_add`, `mean_sub` and `mean_mul`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/FiniteLaws.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/FiniteLaws.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MidpointLenses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry

namespace OAI

/-!
# Finite probability laws and joint square-root budgets
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

def mean (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * f ω

@[simp] theorem mean_const (μ : FiniteLaw Ω) (c : ℝ) : μ.mean (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, μ.total]

@[simp] theorem mean_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.mean (fun ω => f ω + g ω) = μ.mean f + μ.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

@[simp] theorem mean_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.mean (fun ω => f ω - g ω) = μ.mean f - μ.mean g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem mean_mul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.mean (fun ω => c * f ω) = c * μ.mean f := by
  simp [mean, Finset.mul_sum, mul_left_comm]

end FiniteLaw

end SegmentLenses

end

end OAI


