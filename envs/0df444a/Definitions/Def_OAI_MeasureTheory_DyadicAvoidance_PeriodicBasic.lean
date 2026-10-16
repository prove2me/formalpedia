-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
-- name    : OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T02:57:54.756767+00:00
-- url     : https://prove2.me/theorems/5c91ee47-1049-42f7-a1ea-74aa20b02ffd
-- title:
--   One-periodic subsets of $\mathbb{R}$ and their density over one period
-- statement:
--   This file introduces two basic notions for subsets of the real line that are invariant under translation by $1$.
--
--   1. **One-periodic sets.** A set $H \subseteq \mathbb{R}$ is *one-periodic* if
--   $$
--   x + 1 \in H \iff x \in H \qquad \text{for every } x \in \mathbb{R}.
--   $$
--   Equivalently $H + 1 = H$, so $H$ is invariant under translation by every integer.
--
--   2. **Density over a period.** For an arbitrary set $H \subseteq \mathbb{R}$, its *period density* is
--   $$
--   \operatorname{dens}(H) = \lambda\big(H \cap [0,1]\big) \in [0,\infty],
--   $$
--   where $\lambda$ denotes Lebesgue measure on $\mathbb{R}$ and $[0,1]$ is the closed unit interval. For a one-periodic set this is the mass of $H$ in one fundamental period.
--
--   These two notions describe the intermediate object of the dyadic avoidance construction: one builds open one-periodic sets $H$ of small period density that meet every affine copy $\{x + t\,2^{-n} : n \ge 1\}$ with $x \in \mathbb{R}$ and $t \in [1,2]$. A compact subset of $[0,1]$ of measure close to $1$ that avoids every nondegenerate affine copy of the sequence $(2^{-n})_{n \ge 1}$ is then obtained by deleting from $[0,1]$ an open set assembled from dilated and reflected copies of such periodic sets.
--
--   **Formalization Note** The density is `MeasureTheory.volume (H ∩ Set.Icc 0 1)`, a value in the extended nonnegative reals `ENNReal`; since `volume` is an outer measure, it is defined for every set $H$, measurable or not.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicBasic.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicBasic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance

namespace OAI

noncomputable section

namespace Problem310

def OnePeriodic (H : Set ℝ) : Prop :=
  ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H

def periodDensity (H : Set ℝ) : ENNReal :=
  MeasureTheory.volume (H ∩ Set.Icc (0 : ℝ) 1)

end Problem310

end

end OAI


