-- Prove2me | Definitions.Def_GraphonCheeger_InWc
-- name    : GraphonCheeger_InWc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:44:21.344412+00:00
-- url     : https://prove2.me/theorems/180fac01-5b4c-4a7e-b903-40673a152d27
-- title:
--   The class $\mathcal W_c$ of graphons with $k_W\ge c$ a.e.
-- statement:
--   For $c\in[0,1]$, $\mathcal W_c$ is the class of all graphons $W$, on any probability space $(\Omega,\mathcal F,\mu)$, whose degree function satisfies
--
--   $$k_W(x)\ge c\quad\text{for }\mu\text{-a.e. }x\in\Omega .$$
--
--   A positive lower bound on the degrees is the condition under which the Cheeger constant is continuous in the cut distance.
--
--   **Formalization Note** Membership is the predicate `InWc μ W c`. The range $c\in[0,1]$ of the definition is a hypothesis of the statements that use the class.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Definition 4.28, p.48

import Mathlib
import Definitions.Def_GraphonCheeger_IsGraphon

open MeasureTheory

namespace GraphonCheeger

/-!
# The class `W_c` of graphons with degrees at least `c`

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…), Definition 4.28, p.48.

**Formalization Note.** `W_c` is a class of graphons on all probability spaces; membership is the
predicate `InWc μ W c`, "`k_W ≥ c` `µ`-a.e.". The paper's range `c ∈ [0, 1]` is a hypothesis of
the statements that use the class.
-/

universe u

/-- `W ∈ W_c` (Def. 4.28, p.48): the degree function satisfies `k_W(x) ≥ c` for `µ`-a.e. `x`. -/
def InWc {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (W : Ω → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ᵐ x ∂μ, c ≤ degFun μ W x

end GraphonCheeger


