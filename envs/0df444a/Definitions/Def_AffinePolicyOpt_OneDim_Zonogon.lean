-- Prove2me | Definitions.Def_AffinePolicyOpt_OneDim_Zonogon
-- name    : AffinePolicyOpt_OneDim_Zonogon
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:48:33.17172+00:00
-- url     : https://prove2.me/theorems/df3dbc99-226e-476c-88d5-e87283ccd76b
-- title:
--   §4, pp. 8–20 — zonogon projection π (23), hypercube, generator order (32), clamp law, r-side (21), z-hull (22), points ṽ_i (29), System (37)
-- statement:
--   This file fixes the planar objects used in the induction step of the proof of Theorem 3.1 (§4, in the simplified notation of §4.1.1).
--
--   1. **Zonogon projection.** For generators $a=(a_1,\dots,a_k)$, $b=(b_1,\dots,b_k)$ and offsets $a_0,b_0$, the affine map $\pi(w)=(\theta_1(w),\theta_2(w))=\big(a_0+\sum_i a_iw_i,\ b_0+\sum_i b_iw_i\big)$ of (23). The zonogon is $\Theta=\pi(\mathcal H_k)$, with $\mathcal H_k=[0,1]^k$ the unit hypercube.
--   2. **Prefix vertices.** $e_{\le n}\in\{0,1\}^k$ is the hypercube vertex with ones in the first $n$ coordinates; under Assumptions 2–3, $v_n=\pi(e_{\le n})$.
--   3. **Generator order (32).** $b_i\ge 0$ for all $i$ and $a_1/b_1>a_2/b_2>\dots>a_k/b_k$, written cross-multiplied: $a_jb_i<a_ib_j$ for $i<j$.
--   4. **Clamp law.** $u^*(\theta)=\max\big(L,\min(U,\,y^*-\theta)\big)$, the optimal control law of (8) (with the thresholds $y^*-U$, $y^*-L$).
--   5. **Right side (Definition 4.1).** For $X\subseteq\mathbb R^2$, $\operatorname{r-side}(X)$ is the set of extreme points of $\operatorname{conv}(X)+\{(-t,0):t\ge0\}$: the vertices of $\operatorname{conv}(X)$ met counter-clockwise from $y^-$ (the rightmost lowest point) to $y^+$ (the rightmost highest point).
--   6. **Zonogon hull (Definition 4.2).** For a chain $y_0,\dots,y_m$, $\operatorname{z-hull}=\{y_0+\sum_{i=1}^m w_i(y_i-y_{i-1}):0\le w_i\le1\}$.
--   7. **Points (29).** $\tilde v_i=\big(\theta_1[v_i]+c\,u^*(\theta_2[v_i]),\ \theta_2[v_i]+u^*(\theta_2[v_i])\big)$, $i=0,\dots,k$.
--   8. **Partial sums.** $\sum_{i=p+1}^{q}x_i$ of a vector, and the matched index set $\{0,\dots,s\}\cup\{t\}\cup\{r,\dots,k\}$ of Algorithm 1.
--   9. **System (37).** Unknowns $q_0,q_1,\dots,q_k,K_U,K_L$:
--   $$q_0+\dots+q_i=u^*(v_i)\ \ (i\text{ matched}),\qquad a_i+c\,q_i=K_U(b_i+q_i)\ \ (s<i\le\min(t,r)),\qquad a_i+c\,q_i=K_L(b_i+q_i)\ \ (\max(t,s)<i\le r).$$
--
--   These objects are what Lemmas 4.1–4.9 and Corollary 4.1 are stated about.
--
--   **Formalization Note** Generator indices are stored 0-based (Lean index $g$ is the paper's $g+1$); vertex indices $0,\dots,k$ are natural numbers. The right side is encoded through the leftward ray $\operatorname{cone}([-1;0])$; the page's "equivalent definition" with $\operatorname{cone}([0;-1])$ is a misprint (it yields the upper chain). The alignment rows of (37), printed as $(a_i+c q_i)/(b_i+q_i)=K$, are cross-multiplied, so no division by a possibly zero denominator occurs. The clamp is the corrected form of (8): with an interval of minimizers the printed thresholds $\underline y-U$, $\overline y-L$ make the middle piece infeasible.
-- source:
--   Bertsimas, Iancu & Parrilo, Optimality of Affine Policies in Multi-stage Robust Optimization, arXiv:0904.3986v1, pp. 4–14, (8), Definitions 4.1–4.2 (21)–(22), (23), (29), (31)–(32), Algorithm 1 and System (37)

import Mathlib

namespace AffinePolicyOpt.OneDim

open scoped Pointwise

/-- The affine projection `π` of (23) / Lemma 7.2:
`π(w) = (a_0 + Σ_i a_i w_i, b_0 + Σ_i b_i w_i) = (θ_1(w), θ_2(w))`. -/
def zon {k : ℕ} (a0 b0 : ℝ) (a b : Fin k → ℝ) (w : Fin k → ℝ) : ℝ × ℝ :=
  (a0 + ∑ i, a i * w i, b0 + ∑ i, b i * w i)

/-- The unit hypercube `ℋ_k = [0, 1]^k`. -/
def cube (k : ℕ) : Set (Fin k → ℝ) :=
  {w | ∀ i, w i ∈ Set.Icc (0 : ℝ) 1}

/-- The hypercube vertex `[1, …, 1, 0, …, 0]` with ones in the first `n` coordinates
(Assumption 3: the vertex projecting to `v_n`). -/
def prefixVertex (k n : ℕ) : Fin k → ℝ :=
  fun i => if (i : ℕ) < n then 1 else 0

/-- The ordering (32) of the generators, ratios cross-multiplied:
`b_i ≥ 0` for all `i`, and `a_i / b_i > a_j / b_j` whenever `i < j`. -/
def GenOrdered {k : ℕ} (a b : Fin k → ℝ) : Prop :=
  (∀ i, 0 ≤ b i) ∧ ∀ i j, i < j → a j * b i < a i * b j

/-- The clamped control law `u*(θ) = max(L, min(U, y* − θ))` (the corrected form of (8)). -/
def clampLaw (L U ystar : ℝ) (θ : ℝ) : ℝ :=
  max L (min U (ystar - θ))

/-- The leftward ray `cone([−1; 0]) = {(−t, 0) : t ≥ 0}`. -/
def leftRay : Set (ℝ × ℝ) :=
  {p | p.1 ≤ 0 ∧ p.2 = 0}

/-- The right side of a set `X ⊆ ℝ²` (Definition 4.1): the extreme points of
`conv(X) + cone([−1; 0])`, i.e. the vertices of `conv(X)` from `y⁻` counter-clockwise to `y⁺`. -/
def rside (X : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  Set.extremePoints ℝ (convexHull ℝ X + leftRay)

/-- The zonogon hull (22) of a chain `y_0, …, y_m`:
`{y_0 + Σ_{i=1}^m w_i (y_i − y_{i−1}) : 0 ≤ w_i ≤ 1}`. -/
def zhullChain {m : ℕ} (y : Fin (m + 1) → ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ w ∈ cube m, p = y 0 + ∑ i : Fin m, w i • (y i.succ - y i.castSucc)}

/-- The points `ṽ_i` of (29): with `v_i = π([1,…,1,0,…,0])` (ones in the first `i`
coordinates) and `u* = clampLaw L U y*`,
`ṽ_i = (θ_1[v_i] + c u*(θ_2[v_i]), θ_2[v_i] + u*(θ_2[v_i]))`. -/
def vtilde {k : ℕ} (a0 b0 : ℝ) (a b : Fin k → ℝ) (c L U ystar : ℝ) (i : ℕ) : ℝ × ℝ :=
  let θ := zon a0 b0 a b (prefixVertex k i)
  (θ.1 + c * clampLaw L U ystar θ.2, θ.2 + clampLaw L U ystar θ.2)

/-- The sum `x_{p+1} + ⋯ + x_q` of a 1-based vector stored 0-based: the entries with Lean index
`g` such that `p ≤ g < q`. -/
def psum {n : ℕ} (x : Fin n → ℝ) (p q : ℕ) : ℝ :=
  ∑ g ∈ Finset.univ.filter (fun g : Fin n => p ≤ (g : ℕ) ∧ (g : ℕ) < q), x g

/-- The matched vertex indices of Algorithm 1, line 6: `{0, …, s} ∪ {t} ∪ {r, …, k}`. -/
def matchedIdx (k s r t : ℕ) : Set ℕ :=
  {i | i ≤ s} ∪ {t} ∪ {i | r ≤ i ∧ i ≤ k}

/-- System (37) of Algorithm 1 (line 7), for the unknowns `q_0, q = (q_1, …, q_k)` (stored
0-based), `K_U`, `K_L`, with the alignment rows cross-multiplied:
* matching: `q_0 + ⋯ + q_i = u*(v_i)` for every matched index `i`;
* alignment below `t`: `a_i + c q_i = K_U (b_i + q_i)` for `i ∈ {s+1, …, min(t, r)}`;
* alignment above `t`: `a_i + c q_i = K_L (b_i + q_i)` for `i ∈ {max(t, s)+1, …, r}`. -/
def System37 {k : ℕ} (a0 b0 : ℝ) (a b : Fin k → ℝ) (c L U ystar : ℝ) (s r t : ℕ)
    (q0 : ℝ) (q : Fin k → ℝ) (KU KL : ℝ) : Prop :=
  (∀ i ∈ matchedIdx k s r t,
      q0 + psum q 0 i = clampLaw L U ystar (zon a0 b0 a b (prefixVertex k i)).2) ∧
  (∀ g : Fin k, s ≤ (g : ℕ) → (g : ℕ) < min t r → a g + c * q g = KU * (b g + q g)) ∧
  (∀ g : Fin k, max t s ≤ (g : ℕ) → (g : ℕ) < r → a g + c * q g = KL * (b g + q g))

end AffinePolicyOpt.OneDim


