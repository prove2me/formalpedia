-- Prove2me | Definitions.Def_Avram2004_Shared_Standing
-- name    : Avram2004_Shared_Standing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:18:02.801075+00:00
-- url     : https://prove2.me/theorems/ac2ebb90-97b7-4573-bfa5-5acc8d5a27e7
-- title:
--   Standing assumption: unbounded variation, or bounded variation and Λ(dx) ≪ dx
-- statement:
--   Let $X$ be a real-valued process indexed by $t\ge0$ with càdlàg paths, and write $\Delta X_t=X_t-X_{t-}$ for its jump at time $t$.
--
--   1. $X$ has **bounded variation** if almost every path has finite total variation on every compact interval $[0,t]$.
--   2. $X$ satisfies **(AC)**, the absolute continuity of its Lévy measure $\Lambda$ with respect to Lebesgue measure, $\Lambda(dx)\ll dx$, if for every Borel set $A\subseteq\mathbb R$ of Lebesgue measure zero, almost surely no nonzero jump $\Delta X_t$ with $t\in(0,1]$ lies in $A$.
--   3. The **standing assumption** of the paper is: $X$ has unbounded variation, or $X$ has bounded variation and satisfies (AC). Equivalently,
--   $$\text{bounded variation}\ \Longrightarrow\ \text{(AC)}.$$
--
--   The paper restricts itself to this class throughout ("We restrict ourselves to the Lévy processes which have unbounded variation or have bounded variation and a Lévy measure which is absolutely continuous with respect to the Lebesgue measure"). Under it the scale functions are continuously differentiable on $(0,\infty)$, which is what gives meaning to the derivative $W_v^{(p)\prime}(k)$ in Theorem 1.
--
--   **Formalization Note** For a Lévy process the paths are either almost surely of bounded variation on compacts or almost surely not, so "unbounded variation or (bounded variation and (AC))" is the implication above. The Lévy measure is not constructed: $\Lambda(A\setminus\{0\})$ is the expected number of jumps in $(0,1]$ landing in $A$, and this number is Poisson distributed, so $\Lambda(A\setminus\{0\})=0$ exactly when almost surely there is no such jump.
--
--   **Shared definition.** This is the group's single copy of this definition, reviewed once for every chunk that uses it: `01-reflected-exit` (Theorem 1: Eq. (2) p. 216, Remark 4 p. 218, Proposition 1 p. 219, Theorem 1 and its proof pp. 220–224, Remark 6 p. 225); `02-russian` (Theorem 2: Remarks 3–4 and Lemma 1 p. 218, the Russian problem (27)–(28) pp. 227–228, Corollary 1 p. 228, Lemma 2 and Theorem 2 p. 229, proof of Theorem 2 pp. 230–231); `03-canadized-russian` (Theorem 3: Corollary 1 p. 228, Lemma 2 (i) p. 229, the Canadized problem (32) and Lemma 3 pp. 231–233, Theorem 3 p. 233, Lemma 4 p. 234, proof of Theorem 3 pp. 234–235).
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 216, Section 2, condition (AC) and the sentence before it

import Mathlib

open MeasureTheory
open scoped NNReal

namespace Avram2004.Shared

/-- Almost every path of `X` has bounded variation on every compact interval `[0, t]`. -/
def BoundedVar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0, eVariationOn (fun r => X r ω) (Set.Icc 0 t) ≠ ⊤

/-- Condition (AC): the Lévy measure `Λ` is absolutely continuous with respect to Lebesgue measure.
It is stated through the jumps of `X`: for every Lebesgue-null Borel set `A`, almost surely no
nonzero jump `ΔX_t = X_t - X_{t-}` with `t ∈ (0, 1]` lands in `A`. (`Λ(A \ {0})` is the expected number
of such jumps, and that number is Poisson distributed, so `Λ(A \ {0}) = 0` iff almost surely there is
none.) -/
def LevyAC {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ A : Set ℝ, MeasurableSet A → volume A = 0 →
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ≥0) 1,
      X t ω - Function.leftLim (fun r => X r ω) t ∉ A \ {0}

/-- The standing assumption of the paper (§2, p. 216): `X` has unbounded variation, or `X` has
bounded variation and satisfies (AC). Since the paths of a Lévy process are either almost surely of
bounded variation or almost surely not, this is the implication "bounded variation → (AC)". -/
def Standing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  BoundedVar P X → LevyAC P X

end Avram2004.Shared


