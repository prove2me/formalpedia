-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_IMcx
-- name    : BauerleRiederMDP_LQ_Supplement_TradeExec_IMcx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:38:26.917255+00:00
-- url     : https://prove2.me/theorems/ea6a221a-b320-4be2-8aa2-618b17efd89a
-- title:
--   The set $IM_cx$
-- statement:
--   **The set $IM_cx$** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.4, p.295, PDF 305): `IM_cx := {v ∈ IB_b | v(t, x) ≤ C(x), v(t, 0) = 0, v is convex in x, v is continuous and increasing in t, x}`, with the bounding function $b(t, x) = C(x)$ (Proposition 9.4.1).
--
--   **Formalization Note.** Functions on $E = [0, T] \times  \mathbb N _0$ are functions on $\mathbb R  \times  \mathbb N $ constrained on $E$. $v \in  IB_b$ is $|v(t, x)| \le  c C(x)$ on $E$ (with the convention $0/0 = 0$ at $x = 0$, where $C(0) = 0$ and $v(t, 0) = 0$); measurability in $t$ follows from continuity. Convexity in $x \in  \mathbb N _0$ is $v(t, x + 1) - v(t, x) \ge  v(t, x) - v(t, x - 1)$, $x \ge  1$; continuity is in $t$ ($\mathbb N _0$ is discrete).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.4, p.295, PDF 305

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec

namespace BauerleRiederMDP.LQ.Supplement

/-- **The set `IM_cx`** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), §9.4, p.295, PDF 305): `IM_cx := {v ∈ IB_b | v(t, x) ≤ C(x), v(t, 0) = 0, v is convex in x,
v is continuous and increasing in t, x}`, with the bounding function `b(t, x) = C(x)`
(Proposition 9.4.1).

**Formalization Note.** Functions on `E = [0, T] × ℕ_0` are functions on `ℝ × ℕ` constrained on `E`.
`v ∈ IB_b` is `|v(t, x)| ≤ c C(x)` on `E` (with the convention `0/0 = 0` at `x = 0`, where `C(0) = 0`
and `v(t, 0) = 0`); measurability in `t` follows from continuity. Convexity in `x ∈ ℕ_0` is
`v(t, x + 1) − v(t, x) ≥ v(t, x) − v(t, x − 1)`, `x ≥ 1`; continuity is in `t` (`ℕ_0` is discrete). -/
def TradeExec.IMcx (P : TradeExec) : Set (ℝ × ℕ → ℝ) :=
  {v | (∃ c : ℝ, ∀ t ∈ Set.Icc 0 P.T, ∀ x, |v (t, x)| ≤ c * P.C x) ∧
    (∀ t ∈ Set.Icc 0 P.T, ∀ x, v (t, x) ≤ P.C x) ∧
    (∀ t ∈ Set.Icc 0 P.T, v (t, 0) = 0) ∧
    (∀ t ∈ Set.Icc 0 P.T, ∀ x : ℕ, 1 ≤ x → v (t, x) - v (t, x - 1) ≤ v (t, x + 1) - v (t, x)) ∧
    (∀ x, ContinuousOn (fun t => v (t, x)) (Set.Icc 0 P.T)) ∧
    (∀ x, MonotoneOn (fun t => v (t, x)) (Set.Icc 0 P.T)) ∧
    (∀ t ∈ Set.Icc 0 P.T, Monotone fun x => v (t, x))}

end BauerleRiederMDP.LQ.Supplement


