-- Prove2me | Definitions.Def_ARGFContract_Hardness_Supplement_RealNetUtility
-- name    : ARGFContract_Hardness_Supplement_RealNetUtility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:02:24.527198+00:00
-- url     : https://prove2.me/theorems/1703adc0-a8fd-4288-a17f-c4b239f2c802
-- title:
--   Real net utility $\mu(S)=f(S)-\sum_{i\in S}c_i$ and its attained maximum
-- statement:
--   Let $E=\{1,\dots,N\}$ be a finite set of agents with real costs $c_i$ and let $f:2^E\to\mathbb R$ be a value oracle. The **net utility** of a committee $S\subseteq E$ is
--
--   $$\mu(S)=f(S)-\sum_{i\in S}c_i ,$$
--
--   and the µ-Max value is $\max_{S\subseteq E}\mu(S)$, the maximum over the whole finite power set including $\varnothing$; it is attained. A committee $S$ is **optimal** ($S\in S_{OPT}$) when $\mu(T)\le\mu(S)$ for every $T\subseteq E$.
--
--   These are equations (2.1)–(2.2) on real data, used by every algorithmic result of the supplement.
--
--   **Formalization Note** Agents are `Fin N`. The published base definition `ARGFContract_Hardness_NetUtility` is the same formula on rational data; this module is its real analogue, so that the companion theorems are not restricted to rational instances.
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, STOC 2027 submission #348 (October 2026), equations (2.1)–(2.2), p. 6

import Mathlib

open Finset

namespace ARGFContract.Hardness.Supplement

/-- Equation (2.1), p. 6, on real data: `µ(S) = f(S) − ∑_{i∈S} c_i`. -/
def netUtilityReal {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  f S - ∑ i ∈ S, c i

/-- Equation (2.2), p. 6, on real data: the maximum of `µ` over the whole finite powerset
of `E = Fin n`, including `∅`. The powerset is finite and nonempty, so the maximum is
attained; there is no default value. -/
noncomputable def maxNetUtilityReal {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) : ℝ :=
  (univ : Finset (Finset (Fin n))).sup' univ_nonempty (netUtilityReal f c)

/-- `S` is an optimal committee `S_OPT ∈ argmax_{S ⊆ E} µ(S)`, equation (2.2). -/
def IsOptimalSet {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) : Prop :=
  ∀ T : Finset (Fin n), netUtilityReal f c T ≤ netUtilityReal f c S

end ARGFContract.Hardness.Supplement


