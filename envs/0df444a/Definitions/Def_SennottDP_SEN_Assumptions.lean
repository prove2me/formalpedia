-- Prove2me | Definitions.Def_SennottDP_SEN_Assumptions
-- name    : SennottDP_SEN_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T10:17:27.605981+00:00
-- url     : https://prove2.me/theorems/9ab33dac-2fb3-4c25-bba3-06080c5efd06
-- title:
--   The (SEN), (H) and (H*) assumptions; limit functions, limit points and the average cost optimality inequality
-- statement:
--   Let $z \in S$ be a distinguished state. The **relative value function** is $h_\alpha(i) = V_\alpha(i) - V_\alpha(z)$.
--
--   The **(SEN) assumptions** (with witnesses $M$ and $L$) are:
--
--   1. (SEN1) $(1-\alpha)V_\alpha(z)$ is bounded for $\alpha \in (0,1)$;
--   2. (SEN2) there is a nonnegative finite function $M$ with $h_\alpha(i) \le M(i)$ for $i \in S$, $\alpha \in (0,1)$;
--   3. (SEN3) there is a nonnegative finite constant $L$ with $-L \le h_\alpha(i)$ for $i \in S$, $\alpha \in (0,1)$.
--
--   A real function $h$ on $S$ is a **limit function** if $V_\alpha(z) < \infty$ for $\alpha\in(0,1)$ and, for some sequence $\alpha_n \to 1^-$ and a subsequence $\beta_n$, $\lim_n h_{\beta_n}(i) = h(i)$ for all $i$ (7.8). Given stationary policies $f_\alpha$ realizing the discount optimality equation
--   $$V_\alpha(i) = \min_{a \in A_i}\Big\{ C(i,a) + \alpha \sum_j P_{ij}(a) V_\alpha(j) \Big\},$$
--   a stationary policy $f$ is a **limit point** (of $f_{\alpha_n}$ for some $\alpha_n \to 1^-$) if along a subsequence $\beta_n$, for each $i$, $f_{\beta_n}(i) = f(i)$ for all large $n$. A limit function $h$ is **associated** with $f$ if one sequence $\beta_n \to 1^-$ makes both $h_{\beta_n} \to h$ and $f_{\beta_n} \to f$.
--
--   The right side of the **average cost optimality inequality** (7.9) is $\min_{a} \{ C(i,a) + \sum_j P_{ij}(a) h(j)\}$; a stationary policy realizes it if $e(i)$ attains this minimum for every $i$.
--
--   The **(H) assumptions** (witnesses $M$, $L$ now a function) are (H1) = (SEN1), (H2) = (SEN2), and
--
--   1. (H3) there is a nonnegative finite function $L$ with $-L(i) \le h_\alpha(i)$ for $i \in S$, $\alpha \in (0,1)$;
--   2. (H4) $\sum_j P_{ij}(a) L(j) < \infty$ for $i \in S$, $a \in A_i$;
--   3. (H5) for every limit function $h$, stationary policy $e$ and initial state: $-\infty < E_e[h(X_n)]$ for $n \ge 2$, and $\liminf_n E_e[h(X_n)]/n \ge 0$.
--
--   The **(H\*) assumptions** replace (H5) by (H\*5): for every stationary $e$ and initial state, $E_e[L(X_n)] < \infty$ for $n \ge 2$ and $\lim_n E_e[L(X_n)]/n = 0$.
--
--   **Formalization Note** $h_\alpha$ is computed in `EReal` as $V_\alpha(i) - V_\alpha(z)$ with both values in $[0,\infty]$; it is $+\infty$ exactly when $V_\alpha(i) = \infty > V_\alpha(z)$, so (SEN2) forces every $V_\alpha(i)$ to be finite and cannot hold through a junk real value. (SEN1) is `∃ B : ℝ≥0, (1-α) V_α(z) ≤ B`, which forces $V_\alpha(z) < \infty$. The family $f_\alpha$ is a function `ℝ → StationaryPolicy`, constrained only on $(0,1)$ by the theorems that use it. Sequences $\alpha_n \to 1^-$ are real sequences in $(0,1)$ converging to $1$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 132, (SEN1)–(SEN3); p. 134, Definition 7.2.2; p. 135, (7.9); pp. 157–158, (H1)–(H5); p. 158, (H*5) in Proposition 7.7.1; p. 63, (4.9)

import Mathlib
import Definitions.Def_SennottDP_SEN_Criteria

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.SEN

variable {S : Type} [Countable S] {Act : Type}

/-- The one-step quantity `C(i,a) + α ∑_j P_{ij}(a) V_α(j)` of the discount optimality equation
(4.9), p. 63, in `[0, ∞]`. -/
noncomputable def doeQ (M : SennottDP.Discounted.MDC S Act) (α : ℝ) (i : S) (a : Act) : ℝ≥0∞ :=
  (M.C i a : ℝ≥0∞) + ENNReal.ofReal α * ∑' j, M.P i a j * discValue M α j

/-- Sennott (1999), (4.9), p. 63, and Definition 7.2.2(ii), p. 134: the stationary policy `f`
realizes the discount optimality equation for the discount factor `α`, i.e. for every state `i`
the action `f(i)` attains `min_{a ∈ A_i} { C(i,a) + α ∑_j P_{ij}(a) V_α(j) }`. -/
def RealizesDOE (M : SennottDP.Discounted.MDC S Act) (α : ℝ) (f : StationaryPolicy M) : Prop :=
  ∀ i, doeQ M α i (f.1 i) = (M.A i).inf' (M.A_nonempty i) (doeQ M α i)

/-- Sennott (1999), p. 132: the relative value function `h_α(i) = V_α(i) − V_α(z)` for the
distinguished state `z`, as an extended real. When `V_α(z) < ∞` (which (SEN1) implies) this is
the book's difference, with value `+∞` exactly when `V_α(i) = ∞`. -/
noncomputable def hRel (M : SennottDP.Discounted.MDC S Act) (z : S) (α : ℝ) (i : S) : EReal :=
  (discValue M α i : EReal) - (discValue M α z : EReal)

/-- Sennott (1999), (SEN1), p. 132: the quantity `(1 − α) V_α(z)` is bounded for
`α ∈ (0,1)`: there is a finite constant `B` with `(1 − α) V_α(z) ≤ B` for all `α ∈ (0,1)`. -/
def SEN1 (M : SennottDP.Discounted.MDC S Act) (z : S) : Prop :=
  ∃ B : ℝ≥0, ∀ α ∈ Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - α) * discValue M α z ≤ (B : ℝ≥0∞)

/-- Sennott (1999), (SEN2), p. 132, with its witness: `Mf` is a nonnegative (finite) function
with `h_α(i) ≤ Mf(i)` for `i ∈ S` and `α ∈ (0,1)`. -/
def SEN2 (M : SennottDP.Discounted.MDC S Act) (z : S) (Mf : S → ℝ) : Prop :=
  (∀ i, 0 ≤ Mf i) ∧ ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ i, hRel M z α i ≤ (Mf i : EReal)

/-- Sennott (1999), (SEN3), p. 132, with its witness: `L` is a nonnegative (finite) constant with
`−L ≤ h_α(i)` for `i ∈ S` and `α ∈ (0,1)`. -/
def SEN3 (M : SennottDP.Discounted.MDC S Act) (z : S) (L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ i, ((-L : ℝ) : EReal) ≤ hRel M z α i

/-- Sennott (1999), p. 132: the (SEN) assumptions for the distinguished state `z`, with the
function `Mf` of (SEN2) and the constant `L` of (SEN3). "The (SEN) assumptions hold" means that
such `Mf` and `L` exist. -/
def SENAssumptions (M : SennottDP.Discounted.MDC S Act) (z : S) (Mf : S → ℝ) (L : ℝ) : Prop :=
  SEN1 M z ∧ SEN2 M z Mf ∧ SEN3 M z L

/-- Sennott (1999), Definition 7.2.2(i), p. 134: `h : S → ℝ` is a limit function (for the
distinguished state `z`): `V_α(z) < ∞` for `α ∈ (0,1)`, and there are a sequence `α_n → 1⁻` in
`(0,1)` and a subsequence `β_n = α_{φ(n)}` with `lim_n h_{β_n}(i) = h(i)` for every `i ∈ S`
(7.8). -/
def IsLimitFunction (M : SennottDP.Discounted.MDC S Act) (z : S) (h : S → ℝ) : Prop :=
  (∀ α ∈ Set.Ioo (0 : ℝ) 1, discValue M α z ≠ ⊤) ∧
    ∃ (αs : ℕ → ℝ) (φ : ℕ → ℕ), (∀ n, αs n ∈ Set.Ioo (0 : ℝ) 1) ∧
      Tendsto αs atTop (𝓝 1) ∧ StrictMono φ ∧
      ∀ i, Tendsto (fun n => hRel M z (αs (φ n)) i) atTop (𝓝 (h i : EReal))

/-- Sennott (1999), Definition 7.2.2(ii), p. 134 (= Definition B.1): given a family `fam α` of
stationary policies (in the theorems, `fam α = f_α` realizes the discount optimality equation),
the stationary policy `f` is a limit point (of `f_{α_n}`): there are a sequence `α_n → 1⁻` in
`(0,1)` and a subsequence `β_n = α_{φ(n)}` such that for each state `i`, `f_{β_n}(i) = f(i)` for
all sufficiently large `n` (dependent on `i`). -/
def IsLimitPoint (M : SennottDP.Discounted.MDC S Act) (fam : ℝ → StationaryPolicy M) (f : StationaryPolicy M) :
    Prop :=
  ∃ (αs : ℕ → ℝ) (φ : ℕ → ℕ), (∀ n, αs n ∈ Set.Ioo (0 : ℝ) 1) ∧
    Tendsto αs atTop (𝓝 1) ∧ StrictMono φ ∧
    ∀ i, ∀ᶠ n in atTop, (fam (αs (φ n))).1 i = f.1 i

/-- Sennott (1999), Definition 7.2.2(iii), p. 134: the limit function `h` is associated with the
limit point `f` (of the family `fam`): `V_α(z) < ∞` for `α ∈ (0,1)`, and there is one sequence
`β_n → 1⁻` in `(0,1)` along which both `lim_n h_{β_n}(i) = h(i)` and `lim_n f_{β_n} = f`
(`f_{β_n}(i) = f(i)` for all large `n`, for each `i`). -/
def IsAssociated (M : SennottDP.Discounted.MDC S Act) (z : S) (fam : ℝ → StationaryPolicy M) (f : StationaryPolicy M)
    (h : S → ℝ) : Prop :=
  (∀ α ∈ Set.Ioo (0 : ℝ) 1, discValue M α z ≠ ⊤) ∧
    ∃ βs : ℕ → ℝ, (∀ n, βs n ∈ Set.Ioo (0 : ℝ) 1) ∧ Tendsto βs atTop (𝓝 1) ∧
      (∀ i, Tendsto (fun n => hRel M z (βs n) i) atTop (𝓝 (h i : EReal))) ∧
      ∀ i, ∀ᶠ n in atTop, (fam (βs n)).1 i = f.1 i

/-- The right side of the average cost optimality inequality (7.9), p. 135:
`min_{a ∈ A_i} { C(i,a) + ∑_j P_{ij}(a) h(j) }`, as an extended real (the sum is `wsum`). -/
noncomputable def acoiMin (M : SennottDP.Discounted.MDC S Act) (h : S → ℝ) (i : S) : EReal :=
  (M.A i).inf' (M.A_nonempty i) (fun a => ((M.C i a : ℝ) : EReal) + wsum (M.P i a) h)

/-- A stationary policy `e` realizes the minimum in (7.9), p. 135: for every `i`, the action
`e(i)` attains `min_a { C(i,a) + ∑_j P_{ij}(a) h(j) }`. -/
def RealizesACOI (M : SennottDP.Discounted.MDC S Act) (h : S → ℝ) (e : StationaryPolicy M) : Prop :=
  ∀ i, ((M.C i (e.1 i) : ℝ) : EReal) + wsum (M.P i (e.1 i)) h = acoiMin M h i

/-- Sennott (1999), (H3), p. 158, with its witness: `Lf` is a nonnegative (finite) function with
`−Lf(i) ≤ h_α(i)` for `i ∈ S` and `α ∈ (0,1)`. -/
def H3 (M : SennottDP.Discounted.MDC S Act) (z : S) (Lf : S → ℝ) : Prop :=
  (∀ i, 0 ≤ Lf i) ∧ ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ i, ((-Lf i : ℝ) : EReal) ≤ hRel M z α i

/-- Sennott (1999), (H4), p. 158: `∑_j P_{ij}(a) Lf(j) < ∞` for `i ∈ S` and `a ∈ A_i`. -/
def H4 (M : SennottDP.Discounted.MDC S Act) (Lf : S → ℝ) : Prop :=
  ∀ i, ∀ a ∈ M.A i, ∑' j, M.P i a j * ENNReal.ofReal (Lf j) ≠ ⊤

/-- Sennott (1999), (H5), p. 158: for every limit function `h` (for `z`), every stationary policy
`e` and every initial state `i`: (i) `−∞ < E_e[h(X_n) | X_0 = i]` for `n ≥ 2`, and
(ii) `liminf_{n→∞} E_e[h(X_n) | X_0 = i]/n ≥ 0`. -/
def H5 (M : SennottDP.Discounted.MDC S Act) (z : S) : Prop :=
  ∀ h : S → ℝ, IsLimitFunction M z h → ∀ e : StationaryPolicy M, ∀ i : S,
    (∀ n : ℕ, 2 ≤ n → ⊥ < expReal M e.toPolicy i n h) ∧
      0 ≤ liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M e.toPolicy i n h) atTop

/-- Sennott (1999), (H*5), p. 158: for every stationary policy `e` and every initial state `i`:
(i) `E_e[Lf(X_n) | X_0 = i] < ∞` for `n ≥ 2`, and (ii) `lim_{n→∞} E_e[Lf(X_n) | X_0 = i]/n = 0`. -/
def HStar5 (M : SennottDP.Discounted.MDC S Act) (Lf : S → ℝ) : Prop :=
  ∀ e : StationaryPolicy M, ∀ i : S,
    (∀ n : ℕ, 2 ≤ n → SennottDP.Discounted.expState M e.toPolicy i n (fun j => ENNReal.ofReal (Lf j)) ≠ ⊤) ∧
      Tendsto (fun n : ℕ => SennottDP.Discounted.expState M e.toPolicy i n (fun j => ENNReal.ofReal (Lf j)) /
        (n : ℝ≥0∞)) atTop (𝓝 0)

/-- Sennott (1999), pp. 157–158: the (H) assumptions for the distinguished state `z`, with the
function `Mf` of (H2) = (SEN2) and the function `Lf` of (H3): (H1) = (SEN1), (H2) = (SEN2),
(H3), (H4), (H5). -/
def HAssumptions (M : SennottDP.Discounted.MDC S Act) (z : S) (Mf Lf : S → ℝ) : Prop :=
  SEN1 M z ∧ SEN2 M z Mf ∧ H3 M z Lf ∧ H4 M Lf ∧ H5 M z

/-- Sennott (1999), Proposition 7.7.1, p. 158: the (H*) assumptions, i.e. (H) with (H5) replaced
by (H*5). -/
def HStarAssumptions (M : SennottDP.Discounted.MDC S Act) (z : S) (Mf Lf : S → ℝ) : Prop :=
  SEN1 M z ∧ SEN2 M z Mf ∧ H3 M z Lf ∧ H4 M Lf ∧ HStar5 M Lf

end SennottDP.SEN


