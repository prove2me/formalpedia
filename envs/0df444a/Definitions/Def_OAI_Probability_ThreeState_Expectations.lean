-- Prove2me | Definitions.Def_OAI_Probability_ThreeState_Expectations
-- name    : OAI_Probability_ThreeState_Expectations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:28:39.145618+00:00
-- url     : https://prove2.me/theorems/76032791-f037-49ec-a334-b8a289d5c98f
-- title:
--   Expectations, integrability and first and second moments for discrete probability laws
-- statement:
--   Let $p$ be a discrete probability distribution on a type $\alpha$ and $f:\alpha\to\mathbb{R}$ a function.
--
--   1. **Expectation.**
--   $$
--   \mathbb{E}_p[f]=\sum_{a\in\alpha}p(a)\,f(a).
--   $$
--   2. **Integrability.** $f$ has a mean under $p$ if the family $a\mapsto p(a)f(a)$ is summable, equivalently $\sum_{a}p(a)\,|f(a)|<\infty$.
--   3. **Prescribed moments.** For $m,s\in\mathbb{R}$, the statement that $f$ has moments $(m,s)$ under $p$ means three things: $f^2$ has a mean under $p$, $\mathbb{E}_p[f]=m$, and $\mathbb{E}_p[f^2]=s$.
--
--   The moment predicate packages the bookkeeping for first- and second-moment computations of tree statistics, such as random sums over a random number of offspring.
--
--   **Formalization Note** The expectation is the real `tsum`, which Lean sets to $0$ for a non-summable family; this is why integrability is tracked separately by `HasMean`. For real-valued families, summability is the same as absolute summability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/Expectations.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Expectations.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic

namespace OAI

/-! Expectations, second moments and the regular and Poisson offspring laws. -/

namespace ThreeState
open scoped Classical

 
noncomputable def mean {α : Type*} (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑' a, mass p a * f a

def HasMean {α : Type*} (p : PMF α) (f : α → ℝ) : Prop :=
  Summable (fun a => mass p a * f a)

end ThreeState
namespace ThreeState
open scoped Classical

 

structure Moments {α : Type*} (p : PMF α) (f : α → ℝ) (m s : ℝ) : Prop where
  square : HasMean p (fun a => (f a)^2)
  first : mean p f = m
  second : mean p (fun a => (f a)^2) = s

end ThreeState
namespace ThreeState

 
end ThreeState

namespace ThreeState

 
end ThreeState

end OAI


