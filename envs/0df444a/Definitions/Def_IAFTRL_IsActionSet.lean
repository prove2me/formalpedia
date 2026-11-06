-- Prove2me | Definitions.Def_IAFTRL_IsActionSet
-- name    : IAFTRL_IsActionSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:37.320835+00:00
-- url     : https://prove2.me/theorems/9fe295d7-2955-4806-9c37-582cd089eff8
-- title:
--   Finite spanning action set in the unit ball
-- statement:
--   A list $a_1,\dots,a_K\in\mathbb R^d$ is a **finite action set** $\mathcal A=\{a_1,\dots,a_K\}$ in the sense of the paper if
--   1. the actions are distinct (so $K=|\mathcal A|$);
--   2. every action lies in the closed Euclidean unit ball: $\|a_j\|_2\le 1$;
--   3. the actions span $\mathbb R^d$: $\operatorname{span}(\mathcal A)=\mathbb R^d$.
--
--   These are the standing assumptions of Section 1.1 on a finite action set: the action set is a known subset of the unit ball $\mathbb B_d$, spanning without loss of generality.
--
--   **Formalization Note** The action set is an injective list `arms : Fin K → Fin d → ℝ`; vectors are `Fin d → ℝ` with the dot product. The "fixed ordering" used by the algorithm to break ties is the order of `Fin K`.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 1.1, p.5

import Mathlib

namespace IAFTRL

open Matrix

/-- **Finite action set.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 1.1, p.5: "there is a known compact action set
`𝒜 ⊆ 𝔹_d`, where `𝔹_d := {x ∈ ℝ^d : ‖x‖₂ ≤ 1}` is the Euclidean unit ball. We assume without loss
of generality that `span(𝒜) = ℝ^d` and denote by `K := |𝒜|` the size of `𝒜`".

`IsActionSet arms` says that the list `arms : Fin K → ℝ^d` enumerates a set of `K` distinct actions
(injectivity), that every action lies in the closed Euclidean unit ball, and that the actions span
`ℝ^d`.

**Formalization Note.** A finite action set `𝒜 = {a_1, …, a_K}` is the injective list
`arms : Fin K → Fin d → ℝ`; vectors are `Fin d → ℝ` with the dot product `⬝ᵥ`. The "fixed
ordering" the paper uses to break ties is the order of `Fin K`. -/
def IsActionSet {d K : ℕ} (arms : Fin K → Fin d → ℝ) : Prop :=
  Function.Injective arms ∧ (∀ j, arms j ⬝ᵥ arms j ≤ 1) ∧
    Submodule.span ℝ (Set.range arms) = ⊤

end IAFTRL


