-- Prove2me | Definitions.Def_SethiChengSS_Infinite_Model
-- name    : SethiChengSS_Infinite_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:58.641591+00:00
-- url     : https://prove2.me/theorems/6b66f477-e587-4959-bd0d-d30d455f6362
-- title:
--   §2, §3, §6, pp. 932–937 — the infinite-horizon Markov-modulated inventory model: data, assumptions, policies, costs (6.1)/(6.3), values, DP (6.2)/(6.5), w_n (6.6), (s, S) rule
-- statement:
--   This file sets up the nonstationary discounted infinite-horizon inventory model of Sethi and Cheng (1997), §2 and §6.
--
--   **Data.** Demand states form the finite set $I = \{1,\dots,L\}$ and follow a Markov chain with transition matrix $P = (p_{ij})$. In period $k = 0, 1, 2, \dots$ the demand $\xi_k \ge 0$ has the conditional density $\varphi_{i,k}$ when the state is $i_k = i$. Ordering $u \ge 0$ units in period $k$ in state $i$ costs
--   $$c_k(i,u) = K^i_k\,\delta(u) + c^i_k\,u, \qquad \delta(z) = \begin{cases} 1, & z > 0,\\ 0, & z \le 0,\end{cases} \tag{2.1}$$
--   and holding a surplus (inventory or backlog) $x$ costs $f_k(i,x)$.
--
--   **Standing assumptions** (§2): $P$ is stochastic; every $\varphi_{i,k}$ is a probability density vanishing on $(-\infty,0)$ with $\int_0^\infty z\,\varphi_{i,k}(z)\,dz \le M$, one $M$ for all $k$ and $i$; $K^i_k \ge 0$, $c^i_k \ge 0$; each $f_k(i,\cdot)$ is convex and nonnegative with $f_k(i,0) = 0$ and
--   $$f_k(i,x) \le C(1+|x|) \tag{2.2}$$
--   for one constant $C > 0$. The optional assumptions (4.1) $K^i_n \ge \sum_j p_{ij}K^j_{n+1} \ge 0$ and (4.2) $c^i_n x + F_{n+1}(f_{n+1})(i,x) \to +\infty$ as $x \to \infty$ are stated for every period $n$.
--
--   **Policies and costs.** An admissible decision is a history-dependent order rule: the order $u_{n+t} \ge 0$ may depend on the states $i_n,\dots,i_{n+t}$ and on the past demands $\xi_n,\dots,\xi_{n+t-1}$, measurably in the demands. The surplus evolves by $x_{k+1} = x_k + u_k - \xi_k$ (2.4). For a discount factor $\alpha$, the truncated objective (6.3) and the infinite-horizon objective (6.1) are
--   $$J_{n,k}(i,x;U) = \sum_{l=n}^{n+k-1} \alpha^{l-n}\,E\big[c_l(i_l,u_l) + f_l(i_l,x_l)\big], \qquad J_n(i,x;U) = \sum_{l=n}^{\infty} \alpha^{l-n}\,E\big[c_l(i_l,u_l) + f_l(i_l,x_l)\big],$$
--   with $i_n = i$, $x_n = x$. Their infima over admissible $U$ are the truncated value $v_{n,k}$ (6.4) and the value function $v_n$; $\lim_k v_{n,k}$ is also recorded. The cost $w_n(i,x) = J_n(i,x;\mathbf 0)$ of never ordering is (6.6).
--
--   **Operators.** $F_{n+1}(b)(i,y) = \sum_j p_{ij}\int_0^\infty b(j,y-z)\,\varphi_{i,n}(z)\,dz$ (3.1). The dynamic programming equations are (6.2) $v_n(i,x) = f_n(i,x) + \inf_{u\ge0}\{c_n(i,u) + \alpha F_{n+1}(v_{n+1})(i,x+u)\}$, their truncated form (6.5) with $v_{n,0} = 0$, and the order-nothing equation (6.7) $w_n = f_n + \alpha F_{n+1}(w_{n+1})$. The classes $B_0 \supset B_1 \supset C_1$ (p. 933) are nonnegative pointwise limits of continuous functions, those of linear growth, and those also uniformly continuous in $x$.
--
--   **Order rules.** The $(s,S)$ rule is $\hat u(x) = (S-x)\,\delta(s-x)$ with extended-real $s$, $S$ (Remark 4.4: $s = -\infty$ means never order), and the feedback policy (3.3) of a Markov rule $\hat u_n(i,x)$ applies it along the surplus path it generates.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** States are `Fin L` (zero-based). Expectations are sums over state paths $(i_n,\dots,i_{n+k})$ of Lebesgue integrals over the demand vector against the weight $\prod_t p_{i_t i_{t+1}}\varphi_{i_t,t}(\xi_t)$ in $[0,\infty]$: this builds in the conditional independence of $\xi_k$ and $i_{k+1}$ given $i_k$ that (3.1) uses. $J_n$ (6.1) is the supremum over $k$ of $J_{n,k}$, which equals the series because every term is nonnegative. The density and mean conditions are stated with lower Lebesgue integrals, so they are never junk. $F_{n+1}$ uses the Bochner integral, which is $0$ for non-integrable integrands; the statements that make it genuine are the $C_1$ conclusions of the mission. The DP infima are real infima over $u \ge 0$; they are bounded below by $0$ whenever the functions involved are nonnegative. This model is restated from the companion finite-horizon mission (drafts cannot import drafts).
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, pp. 932–933 (§2, (2.1)–(2.5), (3.1), (3.3), classes B_0, B_1, C_1), p. 933 ((4.1), (4.2)), p. 935 (Remark 4.4), pp. 936–937 ((6.1)–(6.7))

import Mathlib
import Definitions.Def_BertsekasKConvex

namespace SethiChengSS.Infinite

open MeasureTheory Filter Topology
open scoped ENNReal

/-- The data of the Markov-modulated inventory model of Sethi and Cheng (1997), §2, p. 932, for the
infinite horizon of §6 (every period `k ∈ ℕ`). Demand states are `Fin L` (the paper's
`I = {1, …, L}`, shifted to start at `0`).
* `P i j` is the transition probability `p_ij` of the demand-state Markov chain;
* `φ k i` is the conditional density `φ_{i,k}` of the demand `ξ_k` of period `k` when `i_k = i`;
* `K k i`, `c k i` are the fixed and variable ordering costs `K^i_k`, `c^i_k` of (2.1);
* `f k i` is the surplus cost `f_k(i, ·)`;
* `C` is the constant of (2.2) and `M` the bound on the conditional mean demand. -/
structure Model (L : ℕ) where
  P : Fin L → Fin L → ℝ
  φ : ℕ → Fin L → ℝ → ℝ
  K : ℕ → Fin L → ℝ
  c : ℕ → Fin L → ℝ
  f : ℕ → Fin L → ℝ → ℝ
  C : ℝ
  M : ℝ

variable {L : ℕ}

/-- The standing assumptions of §2 (p. 932): `P` is a stochastic matrix; each `φ k i` is a
probability density of a nonnegative demand with mean at most `M` (the same `M` for every `k`, `i`);
`K^i_k ≥ 0`, `c^i_k ≥ 0` (2.1); every `f_k(i, ·)` is convex, nonnegative, vanishes at `0`, and
satisfies `f_k(i, x) ≤ C(1 + |x|)` with one constant `C > 0` (2.2). -/
def Standing (D : Model L) : Prop :=
  (∀ i j, 0 ≤ D.P i j) ∧ (∀ i, ∑ j, D.P i j = 1) ∧
  (∀ k i, Measurable (D.φ k i)) ∧ (∀ k i z, 0 ≤ D.φ k i z) ∧
  (∀ k i z, z < 0 → D.φ k i z = 0) ∧
  (∀ k i, ∫⁻ z, ENNReal.ofReal (D.φ k i z) = 1) ∧
  (∀ k i, ∫⁻ z, ENNReal.ofReal (z * D.φ k i z) ≤ ENNReal.ofReal D.M) ∧
  (∀ k i, 0 ≤ D.K k i) ∧ (∀ k i, 0 ≤ D.c k i) ∧
  (∀ k i, ConvexOn ℝ Set.univ (D.f k i)) ∧ (∀ k i x, 0 ≤ D.f k i x) ∧ (∀ k i, D.f k i 0 = 0) ∧
  0 < D.C ∧ (∀ k i x, D.f k i x ≤ D.C * (1 + |x|))

/-- `δ(z) = 0` for `z ≤ 0` and `1` for `z > 0` (p. 932). -/
noncomputable def delta (z : ℝ) : ℝ := if 0 < z then 1 else 0

/-- The ordering cost (2.1): `c_k(i, u) = K^i_k δ(u) + c^i_k u`. -/
noncomputable def orderCost (D : Model L) (k : ℕ) (i : Fin L) (u : ℝ) : ℝ :=
  D.K k i * delta u + D.c k i * u

/-- The operator `F_{n+1}` of (3.1), p. 933: for `b : I × ℝ → ℝ`,
`F_{n+1}(b)(i, y) = Σ_j p_ij ∫_0^∞ b(j, y − z) φ_{i,n}(z) dz`.
`Fnext D n b` is the paper's `F_{n+1}(b)`: it uses the demand density `φ_{i,n}` of period `n`. -/
noncomputable def Fnext (D : Model L) (n : ℕ) (b : Fin L → ℝ → ℝ) (i : Fin L) (y : ℝ) : ℝ :=
  ∑ j, D.P i j * ∫ z in Set.Ioi (0 : ℝ), b j (y - z) * D.φ n i z

/-- Assumption (4.1), p. 933, for every period `n`:
`K^i_n ≥ K̄^i_{n+1} ≡ Σ_j p_ij K^j_{n+1} ≥ 0`. -/
def Cond41 (D : Model L) : Prop :=
  ∀ n i, (∑ j, D.P i j * D.K (n + 1) j) ≤ D.K n i ∧ 0 ≤ ∑ j, D.P i j * D.K (n + 1) j

/-- Assumption (4.2), p. 933, for every period `n`:
`c^i_n x + F_{n+1}(f_{n+1})(i, x) → +∞` as `x → ∞`. -/
def Cond42 (D : Model L) : Prop :=
  ∀ n i, Tendsto (fun x => D.c n i * x + Fnext D n (D.f (n + 1)) i x) atTop atTop

/-- A history-dependent (nonanticipative) ordering policy started at some period `n` (§2):
`U t σ ξ` is the order quantity `u_{n+t}` as a function of the demand states
`σ = (i_n, …, i_{n+t})` and of the past demands `ξ = (ξ_n, …, ξ_{n+t−1})`. -/
def Policy (L : ℕ) : Type := (t : ℕ) → (Fin (t + 1) → Fin L) → (Fin t → ℝ) → ℝ

/-- Admissible decisions: nonnegative order quantities, measurable in the past demands for each
history of demand states. -/
def Admissible (U : Policy L) : Prop :=
  (∀ t σ ξ, 0 ≤ U t σ ξ) ∧ ∀ t σ, Measurable (U t σ)

/-- The surplus path (2.4) under policy `U` from `x_n = x`: `surplus U x t σ ξ` is `x_{n+t}`,
given the states `σ = (i_n, …, i_{n+t})` and demands `ξ = (ξ_n, …, ξ_{n+t−1})`;
`x_{k+1} = x_k + u_k − ξ_k`. -/
def surplus (U : Policy L) (x : ℝ) : (t : ℕ) → (Fin (t + 1) → Fin L) → (Fin t → ℝ) → ℝ
  | 0, _, _ => x
  | t + 1, σ, ξ =>
      surplus U x t (Fin.init σ) (Fin.init ξ) + U t (Fin.init σ) (Fin.init ξ) - ξ (Fin.last t)

/-- The states `(i_n, …, i_{n+t})` of a path `σ = (i_n, …, i_{n+k})`, for `t < k`. -/
def stHist {k : ℕ} (σ : Fin (k + 1) → Fin L) (t : Fin k) : Fin (t.val + 1) → Fin L :=
  fun j => σ (Fin.castLE (Nat.succ_le_succ t.isLt.le) j)

/-- The demands `(ξ_n, …, ξ_{n+t−1})` of a demand vector `ξ = (ξ_n, …, ξ_{n+k−1})`, for `t < k`. -/
def dmHist {k : ℕ} (ξ : Fin k → ℝ) (t : Fin k) : Fin t.val → ℝ :=
  fun j => ξ (Fin.castLE t.isLt.le j)

/-- The joint density weight of the states `σ = (i_n, …, i_{n+k})` and demands
`ξ = (ξ_n, …, ξ_{n+k−1})` given `i_n = σ 0`: `Π_{t<k} p_{i_{n+t} i_{n+t+1}} φ_{i_{n+t}, n+t}(ξ_{n+t})`
(conditional independence of `ξ_k` and `i_{k+1}` given `i_k`, the reading of §2 and (3.1)). -/
noncomputable def pathWeight (D : Model L) (n : ℕ) {k : ℕ} (σ : Fin (k + 1) → Fin L)
    (ξ : Fin k → ℝ) : ℝ :=
  ∏ t : Fin k, D.P (σ t.castSucc) (σ t.succ) * D.φ (n + t) (σ t.castSucc) (ξ t)

/-- The discounted cost `Σ_{l=n}^{n+k−1} α^{l−n} [c_l(i_l, u_l) + f_l(i_l, x_l)]` of the first `k`
periods along the path `(σ, ξ)` under policy `U` from `x_n = x`. -/
noncomputable def truncCost (D : Model L) (α : ℝ) (n : ℕ) (U : Policy L) (x : ℝ) {k : ℕ}
    (σ : Fin (k + 1) → Fin L) (ξ : Fin k → ℝ) : ℝ :=
  ∑ t : Fin k, α ^ (t : ℕ) *
    (orderCost D (n + t) (σ t.castSucc) (U t (stHist σ t) (dmHist ξ t)) +
      D.f (n + t) (σ t.castSucc) (surplus U x t (stHist σ t) (dmHist ξ t)))

/-- The truncated objective (6.3), p. 936:
`J_{n,k}(i, x; U) = Σ_{l=n}^{n+k−1} E[c_l(i_l, u_l) + f_l(i_l, x_l)] α^{l−n}` with `i_n = i`,
`x_n = x`, as an expectation in `[0, ∞]` over the state paths and the demand densities. -/
noncomputable def Jtrunc (D : Model L) (α : ℝ) (n k : ℕ) (i : Fin L) (x : ℝ) (U : Policy L) :
    ℝ≥0∞ :=
  ∑ σ : Fin (k + 1) → Fin L,
    if σ 0 = i then
      ∫⁻ ξ : Fin k → ℝ, ENNReal.ofReal (pathWeight D n σ ξ) *
        ENNReal.ofReal (truncCost D α n U x σ ξ) ∂(Measure.pi fun _ => volume)
    else 0

/-- The infinite-horizon objective (6.1), p. 936:
`J_n(i, x; U) = Σ_{k=n}^∞ α^{k−n} E[c_k(i_k, u_k) + f_k(i_k, x_k)]`, encoded as the supremum of
its `k`-period truncations (the costs are nonnegative). -/
noncomputable def Jinf (D : Model L) (α : ℝ) (n : ℕ) (i : Fin L) (x : ℝ) (U : Policy L) : ℝ≥0∞ :=
  ⨆ k : ℕ, Jtrunc D α n k i x U

/-- The value function (6.4) of the `k`-period truncated problem:
`v_{n,k}(i, x) = inf_{U ∈ 𝒰} J_{n,k}(i, x; U)`. -/
noncomputable def vTrunc (D : Model L) (α : ℝ) (n k : ℕ) (i : Fin L) (x : ℝ) : ℝ≥0∞ :=
  ⨅ (U : Policy L) (_ : Admissible U), Jtrunc D α n k i x U

/-- The value function of the infinite-horizon problem (p. 937):
`v_n(i, x) = inf_{U ∈ 𝒰} J_n(i, x; U)`. -/
noncomputable def value (D : Model L) (α : ℝ) (n : ℕ) (i : Fin L) (x : ℝ) : ℝ≥0∞ :=
  ⨅ (U : Policy L) (_ : Admissible U), Jinf D α n i x U

/-- The limit `lim_{k→∞} v_{n,k}` of the truncated value functions ((6.9), p. 937); the truncated
values increase in `k` by (6.8), so the limit is their supremum. -/
noncomputable def vLim (D : Model L) (α : ℝ) (n : ℕ) (i : Fin L) (x : ℝ) : ℝ≥0∞ :=
  ⨆ k : ℕ, vTrunc D α n k i x

/-- The dynamic programming equations (6.5), p. 937, of the truncated problems, by recursion on
the number `k` of remaining periods: `v_{n,0} = 0` and
`v_{n,k+1}(i, x) = f_n(i, x) + inf_{u≥0} {c_n(i, u) + α F_{n+1}(v_{n+1,k})(i, x + u)}`. -/
noncomputable def dpTrunc (D : Model L) (α : ℝ) : ℕ → ℕ → Fin L → ℝ → ℝ
  | _, 0 => fun _ _ => 0
  | n, k + 1 => fun i x =>
      D.f n i x + ⨅ u : {u : ℝ // 0 ≤ u},
        (orderCost D n i u + α * Fnext D n (dpTrunc D α (n + 1) k) i (x + u))

/-- The policy `0 = {0, 0, …}` of ordering nothing ever (p. 937). -/
def zeroPolicy : Policy L := fun _ _ _ => 0

/-- The cost (6.6) of ordering nothing ever: `w_n(i, x) = J_n(i, x; 0)`. -/
noncomputable def w (D : Model L) (α : ℝ) (n : ℕ) (i : Fin L) (x : ℝ) : ℝ≥0∞ :=
  Jinf D α n i x zeroPolicy

/-- A sequence `v_n` of real functions solves the dynamic programming equations (6.2), p. 936:
`v_n(i, x) = f_n(i, x) + inf_{u≥0} {c_n(i, u) + α F_{n+1}(v_{n+1})(i, x + u)}`, `n = 0, 1, 2, …`. -/
def BellmanInf (D : Model L) (α : ℝ) (v : ℕ → Fin L → ℝ → ℝ) : Prop :=
  ∀ n i x, v n i x = D.f n i x + ⨅ u : {u : ℝ // 0 ≤ u},
    (orderCost D n i u + α * Fnext D n (v (n + 1)) i (x + u))

/-- The rule `û_n(i, x) ≥ 0` attains the infimum in the dynamic programming equations (6.2)
written with the functions `v`: for every `n`, `i`, `x`,
`c_n(i, û_n(i, x)) + α F_{n+1}(v_{n+1})(i, x + û_n(i, x)) = inf_{u≥0} {c_n(i, u) + α F_{n+1}(v_{n+1})(i, x + u)}`. -/
def AttainsInf (D : Model L) (α : ℝ) (v : ℕ → Fin L → ℝ → ℝ) (û : ℕ → Fin L → ℝ → ℝ) : Prop :=
  ∀ n i x, 0 ≤ û n i x ∧
    orderCost D n i (û n i x) + α * Fnext D n (v (n + 1)) i (x + û n i x) =
      ⨅ u : {u : ℝ // 0 ≤ u}, (orderCost D n i u + α * Fnext D n (v (n + 1)) i (x + u))

/-- A sequence `w_n` of real functions solves (6.7), p. 937:
`w_n(i, x) = f_n(i, x) + α F_{n+1}(w_{n+1})(i, x)`. -/
def BellmanW (D : Model L) (α : ℝ) (v : ℕ → Fin L → ℝ → ℝ) : Prop :=
  ∀ n i x, v n i x = D.f n i x + α * Fnext D n (v (n + 1)) i x

/-- The class `B_0` (p. 933): nonnegative functions on `I × ℝ` that are pointwise limits of
sequences of nonnegative functions continuous in `x` (continuous functions on `I × ℝ`, `I` discrete),
which includes the continuous ones. -/
def InB0 (b : Fin L → ℝ → ℝ) : Prop :=
  (∀ i x, 0 ≤ b i x) ∧
    ∃ g : ℕ → Fin L → ℝ → ℝ, (∀ m i, Continuous (g m i)) ∧ (∀ m i x, 0 ≤ g m i x) ∧
      ∀ i x, Tendsto (fun m => g m i x) atTop (𝓝 (b i x))

/-- The class `B_1` (p. 933): functions of `B_0` of linear growth,
`0 ≤ b(i, x) ≤ C_b(1 + |x|)` for some `C_b > 0`. -/
def InB1 (b : Fin L → ℝ → ℝ) : Prop :=
  InB0 b ∧ ∃ Cb : ℝ, 0 < Cb ∧ ∀ i x, b i x ≤ Cb * (1 + |x|)

/-- The class `C_1` (p. 933): functions of `B_1` uniformly continuous in `x`. -/
def InC1 (b : Fin L → ℝ → ℝ) : Prop :=
  InB1 b ∧ ∀ i, UniformContinuous (b i)

/-- A sequence `b_n` lies in `C_1` with one growth constant for all periods:
every `b_n ∈ C_1` and `b_n(i, x) ≤ C'(1 + |x|)` for one `C'` and every `n`, `i`, `x`. This is the
reading of "in class `C_1`" for the sequence `w_n` (p. 937). -/
def SeqInC1 (b : ℕ → Fin L → ℝ → ℝ) : Prop :=
  (∀ n, InC1 (b n)) ∧ ∃ C' : ℝ, ∀ n i x, b n i x ≤ C' * (1 + |x|)

/-- The `(s, S)` order rule `(S − x) δ(s − x)` (Theorem 6.2) with extended-real `s`, `S`
(Remark 4.4, p. 935): order up to `S` when `x < s`, otherwise order nothing. With `s = −∞` it never
orders. -/
noncomputable def orderSS (s S : EReal) (x : ℝ) : ℝ :=
  if (x : EReal) < s then S.toReal - x else 0

/-- The surplus `x̂_{n+t}` generated by the Markov rule `û` from `x̂_n = x` along the states
`(i_n, …, i_{n+t})` and demands `(ξ_n, …, ξ_{n+t−1})` ((3.3), p. 933):
`x̂_{k+1} = x̂_k + û_k(i_k, x̂_k) − ξ_k`. -/
def fbSurplus (û : ℕ → Fin L → ℝ → ℝ) (n : ℕ) (x : ℝ) :
    (t : ℕ) → (Fin (t + 1) → Fin L) → (Fin t → ℝ) → ℝ
  | 0, _, _ => x
  | t + 1, σ, ξ =>
      fbSurplus û n x t (Fin.init σ) (Fin.init ξ) +
        û (n + t) (Fin.init σ (Fin.last t)) (fbSurplus û n x t (Fin.init σ) (Fin.init ξ)) -
          ξ (Fin.last t)

/-- The feedback policy (3.3) of the Markov rule `û`, started at period `n` from `x_n = x`:
`u_{n+t} = û_{n+t}(i_{n+t}, x̂_{n+t})`. -/
def feedback (û : ℕ → Fin L → ℝ → ℝ) (n : ℕ) (x : ℝ) : Policy L :=
  fun t σ ξ => û (n + t) (σ (Fin.last t)) (fbSurplus û n x t σ ξ)

end SethiChengSS.Infinite


