-- Prove2me | Definitions.Def_AnytimeAdaVR_blockSeq
-- name    : AnytimeAdaVR_blockSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:27.100502+00:00
-- url     : https://prove2.me/theorems/a9a913ac-23ab-4b14-90c1-989727367086
-- title:
--   Iterates and estimates of one S or M block
-- statement:
--   A block of kind S or M starts at a point $x$ with scale $a$ and length $b$, and uses fresh samples $\xi_1,\dots,\xi_b$. Set $x_1=x$, $v_1=g(x_1;\xi_1)$, and for $t=2,\dots,b$
--   $$
--   \text{S: } v_t=\Big(1-\frac1t\Big)v_{t-1}+\frac1t g(x_t;\xi_t),\qquad \text{M: } v_t=g(x_t;\xi_t)+\Big(1-\frac1t\Big)\big(v_{t-1}-g(x_{t-1};\xi_t)\big).
--   $$
--   After each estimate the block takes the step $x_{t+1}=x_t-\eta N(v_t)$, with $\eta$ fixed for the block and $N(v)=v/\|v\|$ for $v\ne0$, $N(0)=0$ (eq. (3), p.4). In M, both points $x_t$ and $x_{t-1}$ of the pair are evaluated with the same sample $\xi_t$.
--
--   The definition returns, after $s$ steps, the triple $(x_{s+1},x_s,v_s)$.
--
--   **Formalization Note** $N$ is the published normalization `GarberOLO.Alg3.unitDir`. The samples are a sequence $\xi(0),\xi(1),\dots$ with step $t$ using $\xi(t-1)$; only the first $b$ are read during a block.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §5.1, eqs. (10)–(11), p.7; Algorithm 2, lines 3–19, p.8

import Mathlib
import Definitions.Def_AnytimeAdaVR_SMKind
import Definitions.Def_GarberOLO_Alg3_unitDir
import Definitions.Def_AnytimeAdaVR_stepSize

namespace AnytimeAdaVR

/-- **The iterates and estimates of one S or M block.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §5.1, p.7, eqs. (10)–(11), and
Algorithm 2, lines 3–19, p.8: "At the beginning of a block, set x_1 = x and v_1 = g(x_1; ξ_1) with
one fresh sample. For t = 2, …, b, use S: v_t = (1 − 1/t)v_{t−1} + g(x_t; ξ_t)/t,
M: v_t = g(x_t; ξ_t) + (1 − 1/t)(v_{t−1} − g(x_{t−1}; ξ_t)). After computing v_t, take the normalized
step x_{t+1} = x_t − ηN(v_t)", with `η` from (11) fixed for the block.

`blockSeq k g x a b ξ s` is the triple `(x_{s+1}, x_s, v_s)` after `s` steps of a block of kind `k`
started at `x` with scale `a` and length `b`; at `s = 0` it is `(x_1, x_1, 0)` with `x_1 = x`.
Step `t` uses the sample `ξ (t − 1)`; in M both points of the pair `x_t, x_{t−1}` use that same
sample.

**Formalization Note.** The normalization `N` of (3), p.4 (`N(v) = v/‖v‖` for `v ≠ 0`, `N(0) = 0`)
is the published `GarberOLO.Alg3.unitDir`, the same map. The block's samples are a sequence `ξ : ℕ → Ξ` (only `ξ 0, …, ξ (b−1)` are
read for `s ≤ b`). The recursion is defined for every `s`; only `s ≤ b` is a step of the block. -/
noncomputable def blockSeq {d : ℕ} {Ξ : Type*} (k : SMKind)
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (a : ℝ) (b : ℕ) (ξ : ℕ → Ξ) :
    ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)
  | 0 => (x, x, 0)
  | s + 1 =>
      let st := blockSeq k g x a b ξ s
      let xt := st.1
      let xprev := st.2.1
      let vprev := st.2.2
      let t : ℝ := (s : ℝ) + 1
      let vt : EuclideanSpace ℝ (Fin d) :=
        if s = 0 then g xt (ξ s)
        else
          match k with
          | .S => (1 - 1 / t) • vprev + (1 / t) • g xt (ξ s)
          | .M => g xt (ξ s) + (1 - 1 / t) • (vprev - g xprev (ξ s))
      (xt - stepSize k a b • GarberOLO.Alg3.unitDir vt, xt, vt)

end AnytimeAdaVR


