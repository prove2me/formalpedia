-- Prove2me | Definitions.Def_WaitTimePricing_Existence_Algorithm1
-- name    : WaitTimePricing_Existence_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:45.936743+00:00
-- url     : https://prove2.me/theorems/a5d6d0bc-b3ff-4f2a-81c7-d77517a28d53
-- title:
--   Algorithm 1 — shooting construction $V^g_N, K^g_N$, the value $g_N$ (23), and the limits $\bar g$ (24), $V^{\bar g}$
-- statement:
--   This file encodes the backward explicit-Euler scheme (Algorithm 1) that constructs a piecewise-linear approximate solution of the optimality equations, and the limits built from it.
--
--   **Algorithm 1.** Fix $g\ge 0$ and $N\ge 1$; set $\epsilon_N=\bar w/N$ and $x_i=i\,\epsilon_N$, so $x_0=0$ and $x_N=\bar w$. Initialize
--   $$V^g_N(w)=-(w-\bar w)\,g\quad(w\ge\bar w),\qquad K^g_N(w)=0\quad(w>\bar w).$$
--   For $i=1,\dots,N$, with $V^g_N$ already fixed on $[x_{N-i+1},\infty)$, compute
--   $$K^g_N(x_{N-i+1})=\lambda\max\Big\{\max_{p\in[0,\Gamma(x_{N-i+1})]}\mathbf v(p)-\alpha c(x_{N-i+1})+V^g_N(x_{N-i+1}+\mathtt t(p))-V^g_N(x_{N-i+1}),\ 0\Big\},$$
--   set $K^g_N(w)=K^g_N(x_{N-i+1})$ for $w\in(x_{N-i},x_{N-i+1})$, and
--   $$V^g_N(w)=V^g_N(x_{N-i+1})+\big(-g+K^g_N(x_{N-i+1})\big)(w-x_{N-i+1}),\qquad w\in[x_{N-i},x_{N-i+1}).$$
--   Finally $K^g_N(0)=\lambda\max\{\max_{p\in[0,\Gamma(0)]}\mathbf v(p)+V^g_N(\mathtt t(p))-V^g_N(0),\,0\}$.
--
--   **Shooting value and limits.** The shooting value (23) is
--   $$g_N=\min\{g\ge 0 : g\ge K^g_N(0)\},$$
--   the least $g$ for which the slope of $V^g_N$ at $0$ is non-positive. Then (24) $\bar g=\lim_{j\to\infty}g_{2^j}$, and $V^{\bar g}(w)=\lim_{j\to\infty}V^{\bar g}_{2^j}(w)$ (Proposition 6).
--
--   **Formalization Note** The loop is a recursion on the number of passes: pass $i$ reads only values on $[x_{N-i+1},\infty)$, which are final. The initialization (16) is extended from $[\bar w,\bar w+C]$ to all $w\ge\bar w$ and (17) from $(\bar w,\bar w+C]$ to $(\bar w,\infty)$; only values on $[0,\bar w+C]$ enter the loop, so the construction is unchanged. Values for $w<0$ are never used. Only $N\ge1$ is meaningful. The "min" in (23) is a real infimum (its attainment is a result of the paper, not built in). $\bar g$ and $V^{\bar g}$ are limits that take a default value when the limit does not exist; the mission's statements assert the convergence alongside every use.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 14 Algorithm 1 (16)–(22); p. 16 (23), (24); p. 17 Proposition 6

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting

/-!
# Wait-time based pricing: Algorithm 1, the shooting value `g_N` and the limits `ḡ`, `V^ḡ`

Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times,
SSRN 3709573 (version of October 12, 2020), p. 14 (Algorithm 1, (16)–(22)), p. 16 ((23), (24)),
p. 17 (Proposition 6, definition of `V^ḡ`).
-/

namespace WaitTimePricing.Existence

noncomputable section

open Set Filter

/-- The grid of Algorithm 1, (18), p. 14: `ε_N = w̄ / N`, `x_0 = 0`, `x_{i+1} = x_i + ε_N`,
i.e. `x_i = i · w̄ / N`. Only `N ≥ 1` is meaningful. -/
def grid (M : Model) (N i : ℕ) : ℝ :=
  (i : ℝ) * (wbar M / N)

/-- The slope adjustment of (19) and (22), p. 14, at a point `x` for a current function `V`:
`λ max{max_{p∈[0,Γ(x)]} v(p) − αc(x) + V(x + t(p)) − V(x), 0}`. -/
def slopeAdj (M : Model) (obj : Objective) (V : ℝ → ℝ) (x : ℝ) : ℝ :=
  M.lam * max (innerMax M obj V x) 0

/-- The function `V^g_N` after the first `k` passes of the loop of Algorithm 1, p. 14.

* `k = 0`: the initialization (16), `V(w) = −(w − w̄) g`.
* pass `i = k + 1`: with `κ = K^g_N(x_{N−i+1})` computed by (19) from the current function
  (which is final on `[x_{N−i+1}, ∞)`), set (21)
  `V(w) = V(x_{N−i+1}) + (−g + κ)(w − x_{N−i+1})` for `w ∈ [x_{N−i}, x_{N−i+1})`, and leave
  `V` unchanged elsewhere.

Values on `[x_{N−k}, ∞)` are those of Algorithm 1; values below `x_{N−k}` are provisional. -/
def VStep (M : Model) (obj : Objective) (g : ℝ) (N : ℕ) : ℕ → ℝ → ℝ
  | 0 => fun w => -(w - wbar M) * g
  | k + 1 => fun w =>
      if grid M N (N - (k + 1)) ≤ w ∧ w < grid M N (N - k) then
        VStep M obj g N k (grid M N (N - k)) +
          (-g + slopeAdj M obj (VStep M obj g N k) (grid M N (N - k))) * (w - grid M N (N - k))
      else VStep M obj g N k w

/-- The function `K^g_N` after the first `k` passes of the loop of Algorithm 1, p. 14:
`0` initially ((17)), and pass `i = k + 1` sets `K = K^g_N(x_{N−i+1})` (computed by (19)) on
`(x_{N−i}, x_{N−i+1}]` ((19) at the right end point, (20) on the open interval). -/
def KStep (M : Model) (obj : Objective) (g : ℝ) (N : ℕ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun w =>
      if grid M N (N - (k + 1)) < w ∧ w ≤ grid M N (N - k) then
        slopeAdj M obj (VStep M obj g N k) (grid M N (N - k))
      else KStep M obj g N k w

/-- The output `V^g_N` of Algorithm 1, p. 14, for a value `g ≥ 0` and a number of grid cells
`N ≥ 1`: (16) on `[w̄, ∞)` and (21) on `[0, w̄)`.

**Formalization Note.** The paper sets (16), `V^g_N(w) = −(w − w̄) g`, on `[w̄, w̄ + C]` only;
here it holds for every `w ≥ w̄` (the loop never touches `w ≥ w̄ = x_N`). Only values on
`[0, w̄ + C]` enter (19)–(22), so the construction is unchanged, and (14) can be stated on all of
`(w̄, ∞)`. Values for `w < 0` are unconstrained and never used (they are `−(w − w̄) g`). -/
def VgN (M : Model) (obj : Objective) (g : ℝ) (N : ℕ) : ℝ → ℝ :=
  VStep M obj g N N

/-- The slope adjustment `K^g_N` of Algorithm 1, p. 14: (17) `K = 0` on `(w̄, ∞)`; (19)–(20)
`K(w) = K^g_N(x_{N−i+1})` on `(x_{N−i}, x_{N−i+1}]`, `i = 1, …, N`; and (22)
`K^g_N(0) = λ max{max_{p∈[0,Γ(0)]} v(p) + V^g_N(t(p)) − V^g_N(0), 0}`.

**Formalization Note.** (17) is extended from `(w̄, w̄ + C]` to `(w̄, ∞)`; values for `w < 0` are
`0` and never used. In (22) the term `α c(0)` of `slopeAdj` vanishes since `c(0) = 0`. -/
def KgN (M : Model) (obj : Objective) (g : ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  if w = 0 then slopeAdj M obj (VgN M obj g N) 0 else KStep M obj g N N w

/-- The shooting value (23), p. 16: `g_N := min {g | g ≥ K^g_N(0)}`.

**Formalization Note.** Algorithm 1 takes `g ≥ 0`, so the set is `{g | 0 ≤ g ∧ K^g_N(0) ≤ g}`, and
the "min" is encoded as the real `sInf`. Attainment of the minimum is not built in (the paper
establishes it in the proof of Lemma 7, p. 39). -/
def gN (M : Model) (obj : Objective) (N : ℕ) : ℝ :=
  sInf {g : ℝ | 0 ≤ g ∧ KgN M obj g N 0 ≤ g}

/-- The limit (24), p. 16: `ḡ := lim_{j→∞} g_{2^j}`.

**Formalization Note.** Encoded with `limUnder`, which is a junk value when the limit does not
exist; Proposition 5 asserts the convergence, and every statement about `ḡ` is accompanied by
that convergence. -/
def gbar (M : Model) (obj : Objective) : ℝ :=
  limUnder atTop (fun j : ℕ => gN M obj (2 ^ j))

/-- The limit function of Proposition 6, p. 17: `V^ḡ(w) := lim_{j→∞} V^ḡ_{2^j}(w)`.

**Formalization Note.** Encoded pointwise with `limUnder`, a junk value when the limit does not
exist; Proposition 6 asserts the convergence on `[0, w̄ + C]`. For `w ≥ w̄` every `V^ḡ_{2^j}(w)`
equals `−(w − w̄) ḡ`, so the limit exists there too. Values for `w < 0` are never used. -/
def Vbar (M : Model) (obj : Objective) (w : ℝ) : ℝ :=
  limUnder atTop (fun j : ℕ => VgN M obj (gbar M obj) (2 ^ j) w)

end

end WaitTimePricing.Existence


