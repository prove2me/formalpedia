-- Prove2me | Definitions.Def_RecursiveStopping_IsClosedSupermartingale
-- name    : RecursiveStopping_IsClosedSupermartingale
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:20.614529+00:00
-- url     : https://prove2.me/theorems/d865dffe-ebb1-4313-b4b3-94185b831591
-- title:
--   Supermartingale on $[0,\infty]$ with terminal value $0$
-- statement:
--   A real process $(Y_t)_{t\ge0}$ is a **supermartingale for $t\in[0,\infty]$** when the process $(Y_t)_{t\in[0,\infty]}$ with $Y_\infty:=0$ is an $(\mathcal F_t)_{t\in[0,\infty]}$-supermartingale under $\mathsf P$ (with $\mathcal F_\infty=\bigvee_t\mathcal F_t$): it is adapted, integrable, and
--
--   $$
--   \mathsf E[Y_u\,|\,\mathcal F_t]\le Y_t\quad\mathsf P\text{-a.s.},\qquad 0\le t\le u\le\infty .
--   $$
--
--   The terminal value $0$ is the paper's convention at $t=\infty$ for discounted value processes $e^{-rt}v(X_t)$.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, Theorem 3.1, p.10; (18), p.11; convention at τ = ∞, p.6

import Mathlib
import Definitions.Def_RecursiveStopping_extendTop

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping

/-- A real process `(Y_t)_{t ≥ 0}` is a **supermartingale for `t ∈ [0, ∞]`** (Colaneri &
De Angelis, arXiv:1905.02650v4, Theorem 3.1, p.10; Lemma 3.3 (18), p.11) when the process
indexed by `[0, ∞]` with `Y_∞ := 0` is a supermartingale with respect to `(F_t)_{t ∈ [0, ∞]}`
(`extendTop 𝔽`, with `F_∞ = ⋁_t F_t`) under `P` (Mathlib's `Supermartingale`: adapted,
integrable, `E[Y_u | F_t] ≤ Y_t` a.s. for `t ≤ u ≤ ∞`).

**Formalization Note** The terminal value `0` is the paper's convention at `t = ∞` (p.6): for
the discounted value process `e^{−rt}v(X_t)` the value at `∞` is `e^{−r·∞}·lim sup v(X_t) = 0`. -/
def IsClosedSupermartingale {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (𝔽 : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  Supermartingale (fun t ω => if t = ⊤ then 0 else Y t.toNNReal ω) (extendTop 𝔽) P

end RecursiveStopping


