-- Prove2me | Definitions.Def_ApproxOLO_FullInfo_Model
-- name    : ApproxOLO_FullInfo_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:59.170954+00:00
-- url     : https://prove2.me/theorems/3bbaa5ab-562a-4727-aadf-3f1231f5d327
-- title:
--   §2–§4.1, pp. 4–14 — the OLO instance, α-approximation oracle, α-regret (1), extended oracle (2), the Lemma 5 ellipsoid procedure, Problem (5), Algorithms 2 and 3
-- statement:
--   The objects of Garber's online linear optimization with an approximation oracle.
--
--   1. **Instance** (§2.1, p. 4). Sets $\mathcal K,\mathcal F\subset\mathbb R^d_+$ (the non-negative orthant), both compact, $\mathcal K$ nonempty, with constants $R,F,C>0$ such that $\|x\|\le R$ for $x\in\mathcal K$, $\|f\|\le F$ for $f\in\mathcal F$, and $0\le x\cdot f\le C$ for $x\in\mathcal K$, $f\in\mathcal F$. Throughout, $\|\cdot\|$ is the Euclidean norm.
--
--   2. **Approximation oracle** (p. 4). A map $\mathcal O_{\mathcal K}$ with parameter $\alpha>0$ such that for every $c\in\mathbb R^d_+$, $\mathcal O_{\mathcal K}(c)\in\mathcal K$ and
--   $$\mathcal O_{\mathcal K}(c)\cdot c\le\alpha\min_{x\in\mathcal K}x\cdot c\ \ (\alpha\ge1),\qquad \mathcal O_{\mathcal K}(c)\cdot c\ge\alpha\max_{x\in\mathcal K}x\cdot c\ \ (\alpha<1).$$
--   $\alpha\ge1$ is the loss-minimization case and $\alpha<1$ the payoff-maximization case.
--
--   3. **$\alpha$-regret** (Eq. (1), p. 4) of plays with per-round losses/payoffs $\ell_t$ ($=x_t\cdot f_t$) against $f_1,\dots,f_T$:
--   $$\frac1T\sum_{t=1}^T\ell_t-\alpha\min_{x\in\mathcal K}\frac1T\sum_{t=1}^Tx\cdot f_t\ \ (\alpha\ge1),\qquad \alpha\max_{x\in\mathcal K}\frac1T\sum_{t=1}^Tx\cdot f_t-\frac1T\sum_{t=1}^T\ell_t\ \ (\alpha<1).$$
--
--   4. **Extended oracle** (Eq. (2), Lemma 1, p. 6). With $c^+$ ($c^-$) the non-negative (negative) coordinates of $c$ and $\bar v=v/\|v\|$ for $v\ne0$, $\bar 0=0$:
--   $$\hat{\mathcal O}_{\mathcal K}(c)=(v,s)=\begin{cases}(\mathcal O_{\mathcal K}(c^+)-\alpha R\,\bar c^-,\ \mathcal O_{\mathcal K}(c^+)) & \alpha\ge1,\\ (\mathcal O_{\mathcal K}(-c^-)-R\,\bar c^+,\ \mathcal O_{\mathcal K}(-c^-)) & \alpha<1.\end{cases}$$
--   $\mathrm{CH}(\alpha\mathcal K)$ is the convex hull of $\alpha\mathcal K=\{\alpha x: x\in\mathcal K\}$.
--
--   5. **The ellipsoid procedure of Lemma 5** (p. 9) for a point $x$ and tolerance $\varepsilon$, on the feasibility problem (4): find $w$ with $(x-z)\cdot w\ge\varepsilon$ for all $z\in\alpha\mathcal K$ and $\|w\|\le1$. Starting from the unit ball (center $w_0=0$, matrix $I$), at the current center $w$ it queries $(v,s)=\hat{\mathcal O}_{\mathcal K}(-w)$; if $(x-v)\cdot w<\varepsilon$ it cuts with $v-x$ (keeping $\{h:(v-x)\cdot h\le(v-x)\cdot w\}$); otherwise, if $\|w\|>1$, it cuts with $w$ (keeping $\{h: w\cdot h\le w\cdot w\}$); otherwise it declares (4) feasible. Cuts are standard central cuts. The oracle outputs $(v_k,s_k)$ of iterations $k=0,1,\dots$ are recorded.
--
--   6. **Problem (5)** (p. 10): $(a_1,\dots,a_N)$ is optimal if it minimizes $\tfrac12\|\sum_i a_iv_i-x\|^2$ over the probability simplex.
--
--   7. **Algorithm 2** (p. 12): from $\tilde y=y/\max\{1,\|y\|/(\alpha R)\}$, repeatedly run the procedure of item 5 on $(\tilde y,\varepsilon)$ for $N$ iterations, $N$ a positive integer with $N\ge c\,d^2\ln\frac{(\alpha+1)R+\|\tilde y\|}{\varepsilon}$; on a separating $w$ set $\tilde y\leftarrow\tilde y-\varepsilon w$; otherwise return $\tilde y$, the $N$ oracle outputs and an optimal solution of (5).
--
--   8. **Algorithm 3** (p. 14): $s_1\in\mathcal K$, $\tilde y_1=\alpha s_1$; in round $t$ play $s_t$, receive $f_t\in\mathcal F$, set $y_{t+1}=\tilde y_t\mp\eta f_t$ ($-$ if $\alpha\ge1$, $+$ if $\alpha<1$), call Algorithm 2 on $(y_{t+1},\varepsilon)$, and sample $s_{t+1}=s_i$ with probability $a_i$. The expected loss/payoff of round $t\ge2$ is $\sum_ia_i\,s_i\cdot f_t$ with the output of the call of round $t-1$; round 1 plays $s_1$.
--
--   These are the objects the regret bound (Theorem 1) and its lemmas are about.
--
--   **Formalization Note** Vectors are `Fin d → ℝ` and every norm is `euclNorm x = √(x·x)` (Mathlib's `‖·‖` on this type is the sup norm). The oracle guarantee is written "for every $x\in\mathcal K$", equivalent to the min/max form because the extremum over the compact nonempty $\mathcal K$ is attained; in (1) the min/max are `sInf`/`sSup` over the image of $\mathcal K$, attained under the same hypotheses. The paper fixes no particular ellipsoid method ("[10, 5]"); the mission fixes the start $B(0,1)$ and the central-cut update of the reused `LinearOptimization_EllipsoidMethod` module, which keeps $\{h: a\cdot h\ge a\cdot w\}$, so the cuts use $a=x-v$ and $a=-w$. A zero cut ($v=x$) leaves the center in place (Lean's $(\sqrt0)^{-1}=0$). Algorithms are run predicates: a run of Algorithm 2 records the loop count, the point at each loop, the iteration budget of each call and the decomposition returned; a run of Algorithm 3 requires the calls of rounds $1,\dots,T-1$ only (the call of round $T$ produces $s_{T+1}$, never played). Rounds are $1,\dots,T$.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, pp. 4–14: §2.1 (setting, oracle, Eq. (1)), §2.2 notation (p. 5), Lemma 1 Eq. (2) (p. 6), Lemma 5 Problems (4)–(5) (pp. 9–10), Algorithm 2 (p. 12), Algorithm 3 (p. 14)

import Mathlib
import Definitions.Def_LinearOptimization_EllipsoidMethod

namespace ApproxOLO.FullInfo

open Matrix

/-- Points of `ℝ^d`, as coordinate functions (Garber, arXiv:1709.03093v1, §2.1, p. 4). -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- The standard Euclidean norm `‖x‖ = √(x · x)` (p. 4: "throughout this work we let ‖·‖ denote
the standard Euclidean norm"). Mathlib's `‖·‖` on `Fin d → ℝ` is the sup norm and is never used. -/
noncomputable def euclNorm {d : ℕ} (x : Vec d) : ℝ := Real.sqrt (x ⬝ᵥ x)

/-- `x ∈ ℝ^d_+`, the non-negative orthant (p. 4). -/
def IsNonneg {d : ℕ} (x : Vec d) : Prop := ∀ i, 0 ≤ x i

/-- The setting of §2.1 (p. 4): `K, F ⊂ ℝ^d_+` compact, `K` nonempty, `max_{x∈K} ‖x‖ ≤ R`,
`max_{f∈F} ‖f‖ ≤ F` (here `Fb`), and `C ≥ x · f ≥ 0` for `x ∈ K`, `f ∈ F`, with `R, F, C > 0`. -/
def IsInstance {d : ℕ} (K Fs : Set (Vec d)) (R Fb C : ℝ) : Prop :=
  IsCompact K ∧ K.Nonempty ∧ IsCompact Fs ∧ (∀ x ∈ K, IsNonneg x) ∧ (∀ f ∈ Fs, IsNonneg f) ∧
    0 < R ∧ 0 < Fb ∧ 0 < C ∧ (∀ x ∈ K, euclNorm x ≤ R) ∧ (∀ f ∈ Fs, euclNorm f ≤ Fb) ∧
    ∀ x ∈ K, ∀ f ∈ Fs, 0 ≤ x ⬝ᵥ f ∧ x ⬝ᵥ f ≤ C

/-- The approximated linear optimization oracle `O_K : ℝ^d_+ → K` with parameter `α > 0` (p. 4):
for every `c ∈ ℝ^d_+`, `O_K(c) ∈ K`, and `O_K(c) · c ≤ α min_{x∈K} x · c` if `α ≥ 1`,
`O_K(c) · c ≥ α max_{x∈K} x · c` if `α < 1` (both written for every `x ∈ K`, which is equivalent
since the extremum over the compact nonempty `K` is attained). Values outside `ℝ^d_+` are
unconstrained. -/
def IsApproxOracle {d : ℕ} (K : Set (Vec d)) (alpha : ℝ) (O : Vec d → Vec d) : Prop :=
  ∀ c, IsNonneg c → O c ∈ K ∧
    (1 ≤ alpha → ∀ x ∈ K, O c ⬝ᵥ c ≤ alpha * (x ⬝ᵥ c)) ∧
    (alpha < 1 → ∀ x ∈ K, alpha * (x ⬝ᵥ c) ≤ O c ⬝ᵥ c)

/-- `c⁺`: equal to `c` on its non-negative coordinates and zero elsewhere (Lemma 1, p. 6). -/
def posCoord {d : ℕ} (c : Vec d) : Vec d := fun i => max (c i) 0

/-- `c⁻`: equal to `c` on its negative coordinates and zero elsewhere (Lemma 1, p. 6). -/
def negCoord {d : ℕ} (c : Vec d) : Vec d := fun i => min (c i) 0

/-- `v̄ = v/‖v‖` if `‖v‖ > 0`, and `0` if `‖v‖ = 0` (Lemma 1, p. 6). -/
noncomputable def unitDir {d : ℕ} (v : Vec d) : Vec d :=
  if 0 < euclNorm v then (euclNorm v)⁻¹ • v else 0

/-- The extended approximation oracle (2) of Lemma 1 (p. 6), `Ô_K(c) = (v, s)`:
`(O_K(c⁺) − αR c̄⁻, O_K(c⁺))` if `α ≥ 1`, and `(O_K(−c⁻) − R c̄⁺, O_K(−c⁻))` if `α < 1`. -/
noncomputable def extOracle {d : ℕ} (O : Vec d → Vec d) (alpha R : ℝ) (c : Vec d) :
    Vec d × Vec d :=
  if 1 ≤ alpha then (O (posCoord c) - (alpha * R) • unitDir (negCoord c), O (posCoord c))
  else (O (-negCoord c) - R • unitDir (posCoord c), O (-negCoord c))

/-- `CH(αK)`, the convex hull of `αK = {αx | x ∈ K}` (§2.2, p. 5). -/
def scaledHull {d : ℕ} (K : Set (Vec d)) (alpha : ℝ) : Set (Vec d) :=
  convexHull ℝ ((fun x => alpha • x) '' K)

/-- The `α`-regret (1) (p. 4) of a sequence of plays with per-round losses/payoffs
`ell t` (`= x_t · f_t`) against the vectors `f_1, …, f_T` (`fs`):
`(1/T) Σ_t ell t − α min_{x∈K} (1/T) Σ_t x · f_t` if `α ≥ 1`, and
`α max_{x∈K} (1/T) Σ_t x · f_t − (1/T) Σ_t ell t` if `α < 1`. Rounds are `1, …, T`.
The `sInf`/`sSup` are over the image of `K`; on a compact nonempty `K` they are the attained
minimum/maximum. -/
noncomputable def regretOf {d : ℕ} (K : Set (Vec d)) (alpha : ℝ) (T : ℕ) (fs : ℕ → Vec d)
    (ell : ℕ → ℝ) : ℝ :=
  if 1 ≤ alpha then
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, ell t
      - alpha * sInf ((fun x => (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t) '' K)
  else
    alpha * sSup ((fun x => (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t) '' K)
      - (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, ell t

/-- One iteration of the Ellipsoid method of Lemma 5 (p. 9) on Problem (4) for the point `x`.
The state is the ellipsoid `E(w, D) = {h | (h − w)ᵀ D⁻¹ (h − w) ≤ 1}`; `w` is the current iterate.
Step 1: `(v, s) ← Ô_K(−w)`; if `(x − v) · w < ε`, cut with `v − x` (keep `{h | (v − x) · h ≤ (v − x) · w}`).
Step 2: else if `‖w‖ > 1`, cut with `w` (keep `{h | w · h ≤ w · w}`).
Step 3: otherwise the iterate is feasible and the state is left unchanged.
Cuts use the standard central-cut update of `LinearOptimization` (Bertsimas–Tsitsiklis Thm 8.1),
which keeps `{h | a · h ≥ a · w}`; so `a = x − v` in step 1 and `a = −w` in step 2. -/
noncomputable def ellStep {d : ℕ} (O : Vec d → Vec d) (alpha R : ℝ) (x : Vec d) (eps : ℝ)
    (st : Vec d × Matrix (Fin d) (Fin d) ℝ) : Vec d × Matrix (Fin d) (Fin d) ℝ :=
  let w := st.1
  let D := st.2
  let v := (extOracle O alpha R (-w)).1
  if (x - v) ⬝ᵥ w < eps then
    (LinearOptimization.ellipsoidUpdateCenter w D (x - v),
      LinearOptimization.ellipsoidUpdateMatrix D (x - v))
  else if 1 < euclNorm w then
    (LinearOptimization.ellipsoidUpdateCenter w D (-w),
      LinearOptimization.ellipsoidUpdateMatrix D (-w))
  else st

/-- The state of the Lemma 5 Ellipsoid method at the start of iteration `k` (0-based), started
from the unit ball `E₀ = B(0, 1)` (center `0`, matrix `I`). -/
noncomputable def ellIter {d : ℕ} (O : Vec d → Vec d) (alpha R : ℝ) (x : Vec d) (eps : ℝ)
    (k : ℕ) : Vec d × Matrix (Fin d) (Fin d) ℝ :=
  (ellStep O alpha R x eps)^[k] (0, 1)

/-- The extended-oracle output `(v_k, s_k) = Ô_K(−w_k)` queried in iteration `k` (0-based). -/
noncomputable def ellOut {d : ℕ} (O : Vec d → Vec d) (alpha R : ℝ) (x : Vec d) (eps : ℝ)
    (k : ℕ) : Vec d × Vec d :=
  extOracle O alpha R (-(ellIter O alpha R x eps k).1)

/-- Step 3's test at iteration `k`: `‖w_k‖ ≤ 1` and `(x − v_k) · w_k ≥ ε`, i.e. the method
declares Problem (4) feasible at iteration `k`. -/
def ellFeasibleAt {d : ℕ} (O : Vec d → Vec d) (alpha R : ℝ) (x : Vec d) (eps : ℝ) (k : ℕ) :
    Prop :=
  euclNorm (ellIter O alpha R x eps k).1 ≤ 1 ∧
    eps ≤ (x - (ellOut O alpha R x eps k).1) ⬝ᵥ (ellIter O alpha R x eps k).1

/-- `a` is an optimal solution of Problem (5) (p. 10): `a` lies in the simplex and minimizes
`½‖Σ_i a_i v_i − x‖²` over the simplex. -/
def IsSimplexOpt {d N : ℕ} (v : Fin N → Vec d) (x : Vec d) (a : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1 ∧
    ∀ b : Fin N → ℝ, (∀ i, 0 ≤ b i) → ∑ i, b i = 1 →
      euclNorm (∑ i, a i • v i - x) ^ 2 / 2 ≤ euclNorm (∑ i, b i • v i - x) ^ 2 / 2

/-- What Algorithm 2 (p. 12) returns: the point `ỹ`, the decomposition size `N`, the oracle
outputs `{(v_i, s_i)}`, the distribution `(a_1, …, a_N)`, and the number `loops` of times the
`for` loop was entered. -/
structure Alg2Out (d : ℕ) where
  yt : Vec d
  N : ℕ
  pts : Fin N → Vec d × Vec d
  a : Fin N → ℝ
  loops : ℕ

/-- `out` is the result of a complete run of Algorithm 2 (p. 12) on input `(y, ε)`, where the
Separation-or-Decomposition procedure of Lemma 5 is run, at the `i`-th entry of the loop
(0-based) with current point `ys i`, for `Ns i` iterations, `Ns i` a positive integer with
`Ns i ≥ c d² ln(((α+1)R + ‖ys i‖)/ε)`:
line 2 sets `ys 0 = y / max{1, ‖y‖/(αR)}`; at every loop but the last the procedure declares
feasibility at its first feasible iteration `j < Ns i`, returning `w = w_j`, and line 6 sets
`ys (i+1) = ys i − ε w`; at the last loop it completes `Ns` iterations without declaring
feasibility, and lines 8–9 return `ỹ = ys (loops − 1)`, the `N` oracle outputs gathered, and
an optimal solution `a` of Problem (5). -/
def IsAlg2Run {d : ℕ} (c : ℝ) (O : Vec d → Vec d) (alpha R : ℝ) (y : Vec d) (eps : ℝ)
    (out : Alg2Out d) : Prop :=
  ∃ ys : ℕ → Vec d, ∃ Ns : ℕ → ℕ,
    1 ≤ out.loops ∧
    ys 0 = (max 1 (euclNorm y / (alpha * R)))⁻¹ • y ∧
    (∀ i < out.loops, 1 ≤ Ns i ∧
      c * (d : ℝ) ^ 2 * Real.log (((alpha + 1) * R + euclNorm (ys i)) / eps) ≤ (Ns i : ℝ)) ∧
    (∀ i, i + 1 < out.loops → ∃ j < Ns i,
      ellFeasibleAt O alpha R (ys i) eps j ∧
      (∀ j' < j, ¬ ellFeasibleAt O alpha R (ys i) eps j') ∧
      ys (i + 1) = ys i - eps • (ellIter O alpha R (ys i) eps j).1) ∧
    (∀ j < Ns (out.loops - 1), ¬ ellFeasibleAt O alpha R (ys (out.loops - 1)) eps j) ∧
    out.yt = ys (out.loops - 1) ∧ out.N = Ns (out.loops - 1) ∧
    (∀ i : Fin out.N, out.pts i = ellOut O alpha R (ys (out.loops - 1)) eps i) ∧
    IsSimplexOpt (fun i => (out.pts i).1) out.yt out.a

/-- The iterate `ỹ_t` of Algorithm 3 (p. 14): `ỹ_1 = α s_1` (line 3), and for `t ≥ 2` the point
returned by the Algorithm 2 call of round `t − 1`, stored as `outs t`. -/
def alg3Iterate {d : ℕ} (alpha : ℝ) (s1 : Vec d) (outs : ℕ → Alg2Out d) (t : ℕ) : Vec d :=
  if t ≤ 1 then alpha • s1 else (outs t).yt

/-- A run of Algorithm 3 (p. 14) on the vectors `f_t = fs t`: `s_1 ∈ K` (line 2), and for every
round `t` whose call determines a played point (`1 ≤ t < T`), `outs (t+1)` is a complete run of
Algorithm 2 on `(y_{t+1}, ε)` with `y_{t+1} = ỹ_t − η f_t` if `α ≥ 1` and `ỹ_t + η f_t` if `α < 1`
(lines 7–8). The call of round `T` only produces `s_{T+1}`, which is never played. -/
def IsAlg3Run {d : ℕ} (c : ℝ) (K : Set (Vec d)) (O : Vec d → Vec d) (alpha R eta eps : ℝ)
    (T : ℕ) (fs : ℕ → Vec d) (s1 : Vec d) (outs : ℕ → Alg2Out d) : Prop :=
  s1 ∈ K ∧ ∀ t, 1 ≤ t → t < T →
    IsAlg2Run c O alpha R
      (if 1 ≤ alpha then alg3Iterate alpha s1 outs t - eta • fs t
        else alg3Iterate alpha s1 outs t + eta • fs t)
      eps (outs (t + 1))

/-- The expected loss/payoff `E[s_t · f_t]` of round `t` of Algorithm 3: `s_1 · f_1` in round 1,
and for `t ≥ 2`, `Σ_i a_i (s_i · f_t)` with the distribution and points of the call of round
`t − 1` (line 9 samples `s_t = s_i` with probability `a_i`). -/
noncomputable def alg3ExpLoss {d : ℕ} (s1 : Vec d) (outs : ℕ → Alg2Out d) (fs : ℕ → Vec d)
    (t : ℕ) : ℝ :=
  if t ≤ 1 then s1 ⬝ᵥ fs t
  else ∑ i : Fin (outs t).N, (outs t).a i * (((outs t).pts i).2 ⬝ᵥ fs t)

end ApproxOLO.FullInfo


