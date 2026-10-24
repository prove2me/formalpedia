-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
-- name    : KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:49:40.466636+00:00
-- url     : https://prove2.me/theorems/ff220e91-cb11-49c7-a285-637516aefb91
-- title:
--   Extended-real convex potentials and Legendre transforms
-- statement:
--   For a real inner-product space $E$ and $\varphi:E\to\overline{\mathbb{R}}$, `ConvexPotential φ` means that $\varphi$ never equals $-\infty$ and that its real epigraph is convex, while `ProperPotential φ` additionally requires at least one finite value. `legendre φ y` is the extended-real supremum $\sup_x(\langle x,y\rangle-\varphi(x))$, and `lowerTruncate φ M` is $\max(\varphi(x),-M)$ pointwise; the module includes order, convexity, semicontinuity, and truncation auxiliary results.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L35-L105 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Legendre`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre`; the repository is private at upload time).

import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
namespace FunctionalInequalities
namespace Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Convexity of an extended-real potential, expressed through its real epigraph. -/
def ConvexPotential (φ : E → EReal) : Prop :=
  (∀ x, φ x ≠ ⊥) ∧ Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}
/-- The actual extended-real Legendre transform; no selected maximizers are assumed. -/
def legendre (φ : E → EReal) (y : E) : EReal :=
  ⨆ x : E, (inner ℝ x y : EReal) - φ x
/-- A finite-value witness as well as exclusion of `-∞`, rather than a desired conclusion. -/
def ProperPotential (φ : E → EReal) : Prop :=
  (∀ x, φ x ≠ ⊥) ∧ ∃ x, φ x ≠ ⊤
/-- The actual lower truncation in CEK equation (61). -/
def lowerTruncate (φ : E → EReal) (M : ℝ) : E → EReal :=
  fun x => max (φ x) ((-M : ℝ) : EReal)
end Analysis
end FunctionalInequalities


