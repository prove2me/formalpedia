-- Prove2me | Definitions.Def_WhittFLT_FirstPassage_FirstPassage
-- name    : WhittFLT_FirstPassage_FirstPassage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:20.633894+00:00
-- url     : https://prove2.me/theorems/75c1d0e7-3a35-4cd2-8b67-8b830d93da46
-- title:
--   The supremum x↑, the set E and the first passage time x⁻¹(t) = inf{s ≥ 0 : x(s) > t}
-- statement:
--   Paths are real-valued, $x:\mathbb R\to\mathbb R$, and only their values on $[0,\infty)$ matter.
--
--   1. **Supremum function (§6, p. 80).** $$x^{\uparrow}(t)=\sup_{0\le s\le t}x(s),\qquad t\ge0.$$
--   2. **The set $E$ (§7, pp. 81–82).** $E$ is the set of $x\in D([0,\infty),\mathbb R)$ that are unbounded above on $[0,\infty)$ and satisfy $x(0)\ge0$.
--   3. **First passage time (§7, p. 82).** For $x\in E$, $$x^{-1}(t)=\inf\{s\ge0: x(s)>t\},\qquad t\ge0.$$
--
--   The first passage time $x^{-1}(t)$ is the first time the path exceeds level $t$. It is the right-continuous inverse of $x^{\uparrow}$, and the map $x\mapsto x^{-1}$ converts limit theorems for cumulative processes into limit theorems for their first passage (counting) processes.
--
--   **Formalization Note** $x^{\uparrow}(t)$ is a real `sSup` of $x([0,t])$; it is the paper's value whenever $x$ is bounded on $[0,t]$, which holds for $x\in D$. The first passage time is a real `sInf`; the set is nonempty exactly because $x\in E$ is unbounded above, so every theorem applying it carries the hypothesis $x\in E$ (an empty set would give the junk value $0$). Values at negative arguments ($t<0$) are irrelevant: every statement is on $[0,\infty)$. The inequality is strict ($x(s)>t$), as on the page, which makes $x^{-1}$ right-continuous.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §6, p. 80 (x↑); §7, pp. 81–82 (E and x⁻¹)

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD
import Definitions.Def_WhittFLT_Reflection_Supremum

namespace WhittFLT.FirstPassage

open Set Filter Topology

/-- §7, p. 82: `x ∈ E` — `x ∈ D([0, ∞), ℝ)`, unbounded above, `x(0) ≥ 0`. -/
def InE (x : ℝ → ℝ) : Prop :=
  WhittFLT.Composition.IsCadlagOn (Ici 0) x ∧ ¬ BddAbove (x '' Ici 0) ∧ 0 ≤ x 0

/-- §7, p. 82: the first passage time `x⁻¹(t) = inf{s ≥ 0 : x(s) > t}`. -/
noncomputable def firstPassage (x : ℝ → ℝ) (t : ℝ) : ℝ := sInf {s | 0 ≤ s ∧ t < x s}

end WhittFLT.FirstPassage


