-- Prove2me | Definitions.Def_BSUMConv_BSUM_Setting
-- name    : BSUMConv_BSUM_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:52.351479+00:00
-- url     : https://prove2.me/theorems/0ffe62b4-a40a-43e3-8a1a-c15846dff2e2
-- title:
--   §II, §IV, §V, Figs. 2–3, Assumption 2, pp. 4, 8–9, 15 — feasible set, extension of f, coordinatewise stationarity, Assumption 2 (B1)–(B4), BSUM and MISUM runs
-- statement:
--   This file fixes the objects of Sections IV and V of Razaviyayn, Hong and Luo for the block-structured problem
--
--   $$\min_{x}\ f(x)\quad \text{s.t.}\quad x\in\mathcal X=\mathcal X_1\times\cdots\times\mathcal X_n,\qquad (12)$$
--
--   where each $\mathcal X_i\subseteq\mathbb R^{m_i}$ is a closed convex set and $f$ is a continuous real function on $\mathcal X$. A point is written $x=(x_1,\dots,x_n)$ with $x_i\in\mathbb R^{m_i}$. The directional derivative $f'(x;d)=\liminf_{\lambda\downarrow0}\,(f(x+\lambda d)-f(x))/\lambda$, stationarity and regularity are those of the referenced setting of Tseng (2001).
--
--   1. **Feasible set.** $\mathcal X$ is the product of the block sets $\mathcal X_i$.
--   2. **Extension of $f$.** Following the paper's convention $\operatorname{dom} f=\mathcal X$ (p. 5), $f$ is extended to the whole space by $+\infty$ off $\mathcal X$. Stationarity of $z$ for (12) ($f'(z;d)\ge0$ for every $d$ with $z+d\in\mathcal X$, p. 4) and regularity of $f$ at $z$ are taken for this extension, so only feasible directions matter.
--   3. **Coordinatewise stationarity.** $z\in\mathcal X$ and $f'(z;d)\ge0$ for every $d=(0,\dots,d_k,\dots,0)$ with $z_k+d_k\in\mathcal X_k$, for every block $k$. This is the property the proofs of Theorems 2(a) and 3 establish and call "coordinatewise minimum".
--   4. **Assumption 2** (p. 9) on the approximation functions $u_i(x_i,y)$, $x_i\in\mathbb R^{m_i}$, $y\in\mathbb R^m$:
--      - (B1) $u_i(y_i,y)=f(y)$ for all $y\in\mathcal X$ and all $i$;
--      - (B2) $u_i(x_i,y)\ge f(y_1,\dots,y_{i-1},x_i,y_{i+1},\dots,y_n)$ for all $x_i\in\mathcal X_i$, $y\in\mathcal X$ and all $i$;
--      - (B3) $u_i'(x_i,y;d_i)\big|_{x_i=y_i}=f'(y;d)$ for all $y\in\mathcal X$ and $d=(0,\dots,d_i,\dots,0)$ with $y_i+d_i\in\mathcal X_i$, the left side being the directional derivative in the variable $x_i$ only;
--      - (B4) $u_i(x_i,y)$ is continuous in $(x_i,y)$ on $\mathcal X_i\times\mathcal X$.
--   5. **Quasi-convexity in $x_i$:** for each $i$ and $y\in\mathcal X$, $x_i\mapsto u_i(x_i,y)$ is quasi-convex on $\mathcal X_i$.
--   6. **Unique block minimiser** for block $i$: for every $y\in\mathcal X$, $\min_{x_i\in\mathcal X_i}u_i(x_i,y)$ has exactly one minimiser.
--   7. **BSUM run** (Fig. 2, subproblem (13)): a sequence $x^0,x^1,\dots$ with $x^0\in\mathcal X$ and a block schedule; at each step the scheduled block $i$ is replaced by an arbitrary minimiser of $u_i(\cdot,x^r)$ over $\mathcal X_i$ and the other blocks are kept. The cyclic rule is that of the referenced setting.
--   8. **MISUM run** (Fig. 3): $x^0\in\mathcal X$; at each step every block subproblem attains its minimum, a block $k$ attaining $\min_i\min_{x_i\in\mathcal X_i}u_i(x_i,x^r)$ is chosen, its block is replaced by an arbitrary minimiser of $u_k(\cdot,x^r)$ over $\mathcal X_k$, and the other blocks are kept.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The paper's $n$ blocks are $N$ blocks indexed by $\{0,\dots,N-1\}$, and the paper's $m_i$ is `n i`. The block space carries the sup norm of the product (irrelevant for every statement here except through convergence, which is norm-independent). The extension of $f$ is `fext f X` with value $+\infty$ off $\mathcal X$. Existence of block minimisers is not assumed: a run only says that each new block is a minimiser.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, pp. 4, 8–9, 15, §II, (12), (13), Fig. 2, Assumption 2 (B1)–(B4), Theorem 2(a) hypotheses, Fig. 3

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

namespace BSUMConv.BSUM

open TsengBCD.Stationary

/-- The feasible set `X = X₁ × ⋯ × X_n` of problem (12), p. 8, as a subset of the block space
`X n = ℝ^{m₁} × ⋯ × ℝ^{m_n}` (paper block `k ∈ {1, …, n}` is the Lean index `k - 1 : Fin N`). -/
def Xset {N : ℕ} {n : Fin N → ℕ} (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))) :
    Set (X n) :=
  Set.pi Set.univ Xs

open Classical in
/-- The objective `f`, defined on `X` ("without loss of generality, we can assume that
`dom f = X`", p. 5), as an extended-real function on the whole block space: `f(x)` on `X`
and `+∞` off `X`. -/
noncomputable def fext {V : Type*} (f : V → ℝ) (S : Set V) : V → EReal :=
  fun x => if x ∈ S then (f x : EReal) else ⊤

/-- Coordinatewise stationarity at `z` for problem (12): `z ∈ X` and
`f′(z; (0, …, d_k, …, 0)) ≥ 0` for every block `k` and every `d_k` with `z_k + d_k ∈ X_k`.
This is what the proofs of Theorems 2(a) and 3 (pp. 12, 16) establish; the paper calls it
"coordinatewise minimum" ("in other words, z is the coordinatewise minimum of f(·)", p. 12). -/
def IsCoordStationary {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))) (f : X n → ℝ) (z : X n) : Prop :=
  z ∈ Xset Xs ∧ ∀ (k : Fin N) (dk : EuclideanSpace ℝ (Fin (n k))),
    z k + dk ∈ Xs k → 0 ≤ dirDeriv (fext f (Xset Xs)) z (Pi.single k dk)

/-- Assumption 2, p. 9, on the block approximation functions `u_i(x_i, y)`:
(B1) `u_i(y_i, y) = f(y)` for `y ∈ X`;
(B2) `u_i(x_i, y) ≥ f(y₁, …, y_{i−1}, x_i, y_{i+1}, …, y_n)` for `x_i ∈ X_i`, `y ∈ X`;
(B3) `u′_i(x_i, y; d_i)|_{x_i = y_i} = f′(y; (0, …, d_i, …, 0))` whenever `y_i + d_i ∈ X_i`,
the left side being the directional derivative in the variable `x_i` only;
(B4) `u_i(x_i, y)` is continuous in `(x_i, y)` (on `X_i × X`). -/
structure Assumption2 {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i)))) (f : X n → ℝ)
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) : Prop where
  B1 : ∀ y ∈ Xset Xs, ∀ i, u i (y i) y = f y
  B2 : ∀ i, ∀ xi ∈ Xs i, ∀ y ∈ Xset Xs, f (Function.update y i xi) ≤ u i xi y
  B3 : ∀ y ∈ Xset Xs, ∀ (i : Fin N) (di : EuclideanSpace ℝ (Fin (n i))), y i + di ∈ Xs i →
    dirDeriv (fun xi => (u i xi y : EReal)) (y i) di =
      dirDeriv (fext f (Xset Xs)) y (Pi.single i di)
  B4 : ∀ i, ContinuousOn (fun p : EuclideanSpace ℝ (Fin (n i)) × X n => u i p.1 p.2)
    (Xs i ×ˢ Xset Xs)

/-- "`u_i(x_i, y)` is quasi-convex in `x_i`" (Theorem 2(a), p. 10): for every `i` and every
`y ∈ X`, the function `x_i ↦ u_i(x_i, y)` is quasi-convex on `X_i`. -/
def BlockQuasiconvex {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) : Prop :=
  ∀ i, ∀ y ∈ Xset Xs, QuasiconvexOn ℝ (Xs i) (fun xi => u i xi y)

/-- "The subproblem (13) has a unique solution for any point `x^{r−1} ∈ X`" for block `i`:
for every `y ∈ X`, `min_{x_i ∈ X_i} u_i(x_i, y)` has exactly one minimiser. -/
def UniqueBlockMin {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) (i : Fin N) : Prop :=
  ∀ y ∈ Xset Xs, ∃! xi, xi ∈ Xs i ∧ ∀ w ∈ Xs i, u i xi y ≤ u i w y

/-- A run of the BSUM algorithm (Fig. 2, subproblem (13), p. 9) with block schedule `s`:
`s r` is the block updated on the step from `x^r` to `x^{r+1}`; `x⁰ ∈ X`; the new block
`x^{r+1}_{s r}` is an (arbitrary) minimiser of `u_{s r}(·, x^r)` over `X_{s r}`; the other
blocks are unchanged. The cyclic rule of Fig. 2 is `IsCyclic s`. -/
def IsBSUMRun {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) (s : ℕ → Fin N)
    (x : ℕ → X n) : Prop :=
  x 0 ∈ Xset Xs ∧ ∀ r, x (r + 1) (s r) ∈ Xs (s r) ∧
    (∀ w ∈ Xs (s r), u (s r) (x (r + 1) (s r)) (x r) ≤ u (s r) w (x r)) ∧
    ∀ k, k ≠ s r → x (r + 1) k = x r k

/-- A run of the MISUM algorithm (Fig. 3, p. 15): `x⁰ ∈ X`; at each step every block
subproblem has a minimum, a block `k` attaining `min_i min_{x_i ∈ X_i} u_i(x_i, x^r)` is
chosen, `x^{r+1}_k` is an (arbitrary) minimiser of `u_k(·, x^r)` over `X_k` (so its value is
at most `u_i(w, x^r)` for every block `i` and every `w ∈ X_i`), and the other blocks are
unchanged. -/
def IsMISUMRun {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) (x : ℕ → X n) : Prop :=
  x 0 ∈ Xset Xs ∧ ∀ r,
    (∀ i, ∃ xi ∈ Xs i, ∀ w ∈ Xs i, u i xi (x r) ≤ u i w (x r)) ∧
    ∃ k : Fin N, x (r + 1) k ∈ Xs k ∧
    (∀ i, ∀ w ∈ Xs i, u k (x (r + 1) k) (x r) ≤ u i w (x r)) ∧
    ∀ i, i ≠ k → x (r + 1) i = x r i

end BSUMConv.BSUM


