-- Prove2me | Definitions.Def_LevyExtrema_SBA_StickBreaking
-- name    : LevyExtrema_SBA_StickBreaking
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:57.127711+00:00
-- url     : https://prove2.me/theorems/d5eafafc-94f5-4b8d-987f-d72625399257
-- title:
--   Uniform stick-breaking on $[0,T]$: $L_0=T$, $\ell_n=V_nL_{n-1}$, $L_n=L_{n-1}-\ell_n$
-- statement:
--   Fix a horizon $T\ge0$ and a sequence $(V_n)_{n\ge1}$ of random variables. The **stick-breaking process** on $[0,T]$ is
--
--   $$L_0=T,\qquad \ell_n=V_nL_{n-1},\qquad L_n=L_{n-1}-\ell_n\quad(n\ge1),$$
--
--   so that $L_n=T\prod_{k=1}^n(1-V_k)$ is the length left after $n$ sticks have been broken off and $\ell_n$ is the length of the $n$-th stick. The sticks are **uniform** when $(V_n)$ is an i.i.d. sequence of $\mathrm U(0,1)$ random variables: each $V_n$ is measurable with law the Lebesgue measure on $[0,1]$, and the sequence is mutually independent. The module also defines $Y_{L_k}$, a path $Y$ evaluated at the random time $L_k$.
--
--   **Formalization Note** The sequence is indexed from $0$: Lean's `V k` is the paper's $V_{k+1}$, `stickRem T V k` is $L_k$, and `stickLen T V k` is $\ell_{k+1}$. A random time $L_k$ is passed to a path through `Real.toNNReal` (time is $\mathbb R_{\ge0}$; $L_k\in[0,T]$ almost surely).
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, §1.1, p. 2 (after (1.1))

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LevyExtrema.SBA

/-- **Remaining stick length L_k of the stick-breaking process.**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, §1.1, p. 2: "L_0 = T,
ℓ_n = V_n L_{n−1} and L_n = L_{n−1} − ℓ_n for n ∈ N".

`stickRem T V 0 = T`, `stickRem T V (k+1) = (1 − V k) · stickRem T V k`.

**Formalization Note.** `V` is indexed from 0: Lean's `V k` is the paper's `V_{k+1}`, and
`stickRem T V k` is the paper's `L_k`. -/
noncomputable def stickRem (T : ℝ≥0) {Ω : Type*} (V : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => (T : ℝ)
  | k + 1, ω => (1 - V k ω) * stickRem T V k ω

/-- **Stick length ℓ_{k+1} = V_{k+1} L_k** (p. 2). Lean's `stickLen T V k` is the paper's
`ℓ_{k+1}`, so `stickLen T V k + stickRem T V (k+1) = stickRem T V k`. -/
noncomputable def stickLen (T : ℝ≥0) {Ω : Type*} (V : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  V k ω * stickRem T V k ω

/-- **A path evaluated at the random time L_k**: `atStick T Y V k ω = Y_{L_k}(ω)`.
The random time enters through `Real.toNNReal` (time is `ℝ≥0`; `L_k ∈ [0, T]` almost surely). -/
noncomputable def atStick (T : ℝ≥0) {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ) (k : ℕ)
    (ω : Ω) : ℝ :=
  Y (Real.toNNReal (stickRem T V k ω)) ω

/-- **Uniform stick-breaking weights**: `(V_n)` is a U(0, 1)-iid sequence (p. 2: "(V_n)_{n∈N} is a
U(0, 1)-iid sequence"). Each `V k` is measurable with law the Lebesgue measure on `[0, 1]`, and the
family is mutually independent. -/
def IsUniformSticks {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V : ℕ → Ω → ℝ) : Prop :=
  (∀ k, Measurable (V k)) ∧ iIndepFun V P ∧
    ∀ k, P.map (V k) = volume.restrict (Set.Icc (0 : ℝ) 1)

end LevyExtrema.SBA


