-- Prove2me | Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_OrderTopology
-- name    : MonotoneCompStatics_QSMChar_Supplement_OrderTopology
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:06:21.748802+00:00
-- url     : https://prove2.me/theorems/5c79f8db-73d9-47f6-a5c1-5c73e2ad1e87
-- title:
--   Order interval topology and two-sided chain upper semicontinuity
-- statement:
--   For a partially ordered set $X$, give $X$ the topology whose closed subbasis consists of the principal rays $[a,\infty)$ and $(-\infty,a]$; their intersections include all order intervals. For $f:X\to\mathbb R$, chain upper semicontinuity means that every upper level cut is closed under every existing supremum and infimum of a nonempty chain:
--   $$C\subseteq\{f\ge a\},\quad z=\sup C\text{ or }z=\inf C\quad\Longrightarrow\quad f(z)\ge a.$$
--   Quantification is over all chains and all real levels. This is the cut form of both chain limsup conditions and makes sense without completeness of $X$ or boundedness of $f$.
--
--   **Formalization Note** Supremum and infimum are witnessed by `IsLUB` and `IsGLB`; nonexistent endpoints impose no condition. This encoding does not use totalized real suprema or sequence-only limits. The topology is specified explicitly, without assuming it is Hausdorff.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), DOI 10.2307/2951479, p.179, PDF 24, Appendix definition and chain assumptions of A3/A4

import Mathlib

namespace MonotoneCompStatics.QSMChar.Supplement

/-- The principal rays (and hence closed order intervals) form a closed subbasis. -/
@[instance_reducible]
def intervalTopology (X : Type*) [PartialOrder X] : TopologicalSpace X :=
  TopologicalSpace.generateFrom {V | ∃ a : X, V = (Set.Ici a)ᶜ ∨ V = (Set.Iic a)ᶜ}

/-- Closure of every upper level cut under actual suprema and infima of nonempty
chains. This is the two-sided chain-limsup formulation, with no totalized extrema. -/
def ChainUpperSemicontinuous {X : Type*} [PartialOrder X] (f : X → ℝ) : Prop :=
  ∀ (C : Set X), C.Nonempty → IsChain (· ≤ ·) C → ∀ (z : X) (a : ℝ),
    (∀ x ∈ C, a ≤ f x) →
    (IsLUB C z → a ≤ f z) ∧ (IsGLB C z → a ≤ f z)

end MonotoneCompStatics.QSMChar.Supplement


