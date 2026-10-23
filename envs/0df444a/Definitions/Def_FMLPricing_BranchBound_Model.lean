-- Prove2me | Definitions.Def_FMLPricing_BranchBound_Model
-- name    : FMLPricing_BranchBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:00.979228+00:00
-- url     : https://prove2.me/theorems/ef00e98e-5042-4b3a-a435-88e035e60cf9
-- title:
--   §2, §3.2–§3.6 — finite-mixture logit revenue, no-purchase reparameterization cnstr-rev(x), boxes R(x, r), LP(x, r), χ and Algorithm 1 BNB(ε)
-- statement:
--   This file sets up the finite-mixture logit (FML) pricing model of van de Geer and den Boer and the branch-and-bound algorithm $\mathrm{BNB}(\varepsilon)$ that approximately maximizes its revenue.
--
--   **Instance.** There are $m \ge 1$ customer segments $c \in M = \{1,\dots,m\}$ with shares $w_c > 0$, $\sum_c w_c = 1$, and $n \ge 1$ products $j \in N = \{1,\dots,n\}$ with valuations $a_{cj} \in \mathbb R$ and price sensitivities $b_j > 0$. At prices $p \in \mathbb R^n$ a segment-$c$ customer buys product $i$, or nothing, with probabilities
--   $$
--   q_{ci}(p) = \frac{e^{a_{ci} - b_i p_i}}{1 + \sum_{j \in N} e^{a_{cj} - b_j p_j}}, \qquad q_{c0}(p) = \frac{1}{1 + \sum_{j \in N} e^{a_{cj} - b_j p_j}},
--   $$
--   and the expected revenue per customer is $\Pi(p) = \sum_{c} w_c \sum_j p_j q_{cj}(p)$ (2).
--
--   **Reparameterization.** The price box is $[\underline p, \bar p]$ with $\underline p_j = b_j^{-1}$ and $\bar p_j = b_j^{-1} + \max_{c} \sup_{p \in \mathbb R^n} \sum_i p_i q_{ci}(p)$. The no-purchase vector is $q_0(p) = (q_{10}(p), \dots, q_{m0}(p))$ and the attainable set is $X = \{q_0(p) : p \in [\underline p, \bar p]\}$ (3). With $s_{cj} = e^{a_{cj}}$, $k_j^\top x = b_j^{-1} \sum_c w_c s_{cj} x_c$, $\underline z_j = e^{-\bar p_j b_j}$ and $\bar z_j = e^{-\underline p_j b_j}$, the problem $\texttt{cnstr-rev}(x)$ maximizes $-\sum_j z_j \log(z_j)\, k_j^\top x$ over $z \in [\underline z, \bar z]$ subject to $1 + \sum_j s_{cj} z_j = 1/x_c$ for all $c$; its optimal value is $\pi(x)$. The substitution is $z_j = e^{-p_j b_j}$, with inverse $p_j = -b_j^{-1} \log z_j$. Also $\mu_c(x) = (1 - x_c)/x_c$.
--
--   **Boxes and bounds.** For $x \in \mathbb R^m$ and $r \in \mathbb R$: $\underline x_c(x, r) = (x_c - r) \vee q_{c0}(\underline p)$, $\bar x_c(x, r) = (x_c + r) \wedge q_{c0}(\bar p)$ and $R(x, r) = [\underline x(x, r), \bar x(x, r)]$. The derivative-free bound $\pi^\xi(x, r)$ is the supremum of $-\sum_{c,j} \xi_{cj} \log(\xi_{cj}/\bar x_c(x, r))\, s_{cj} w_c b_j^{-1}$ over $\xi \in \mathbb R^{m \times n}$ with $\underline z_j \underline x_c(x,r) \le \xi_{cj} \le \bar z_j \bar x_c(x,r)$ and $1 - \bar x_c(x,r) \le \sum_j s_{cj} \xi_{cj} \le 1 - \underline x_c(x,r)$.
--
--   **The linear program $\mathrm{LP}(x, r)$** minimizes $\gamma$ over $(\gamma, z, \delta^+, \delta^-) \in \mathbb R \times \mathbb R^n \times \mathbb R^m_+ \times \mathbb R^m_+$ subject to (13) $\sum_j s_{cj} z_j + \delta^+_c - \delta^-_c = \mu_c(x)$, (14) $\gamma \ge \delta^+_c + \delta^-_c$, (15)–(16) $\mu_c(\bar x_c(x,r)) \le \mu_c(x) - \delta^+_c + \delta^-_c \le \mu_c(\underline x_c(x,r))$, and (17) $\underline z_j \le z_j \le \bar z_j$. A solution is a feasible point with least $\gamma$. The map $\chi$ is $\chi(x, \delta^+, \delta^-)_c = x_c / (1 + x_c(\delta^-_c - \delta^+_c))$.
--
--   **Algorithm 1, $\mathrm{BNB}(\varepsilon)$.** The state is $(\underline\pi, \bar\pi, r, \mathcal X_1, x^\star)$ with $\bar\pi \in [-\infty, \infty]$. It starts at $\underline\pi = \Pi(\underline p)$, $\bar\pi = \infty$, $r = r_0 = \tfrac12 \max_c (q_{c0}(\bar p) - q_{c0}(\underline p))$, $\mathcal X_1 = \{q_0(\underline p) + r_0 \mathbf 1\}$ and $x^\star = q_0(\underline p)$. While $(1 - \varepsilon)\bar\pi > \underline\pi$, one pass sets $\bar\pi = -\infty$, $\mathcal X_2 = \emptyset$ and visits the centers $x \in \mathcal X_1$ in a given order. For each $x$ with $R(x, r) \cap X \neq \emptyset$ it takes a solution of $\mathrm{LP}(x, r)$, forms $x^\delta = \chi(x, \delta^+, \delta^-)$ and $r^\delta = r + \|x - x^\delta\|_\infty$, and then, in this order: if $\pi(x^\delta) \ge \underline\pi$ it sets $\underline\pi = \pi(x^\delta)$ and $x^\star = x^\delta$; if $U(x^\delta, r^\delta) \ge \underline\pi$ it adds $x$ to $\mathcal X_2$; and if $U(x^\delta, r^\delta) \ge \bar\pi$ it sets $\bar\pi = U(x^\delta, r^\delta)$. It then halves $r$ and replaces $\mathcal X_1$ by $\{x + \omega r : x \in \mathcal X_2, \omega \in \{-1, 1\}^m\}$, using the halved $r$. Here $U$ is the bounding rule, which the paper takes to be $\pi^u$ (12).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The instance is a structure `FML m n` with the standing assumptions in `Standing`. The page says $w_c \in (0,1)$; `Standing` asks $w_c > 0$ and $\sum_c w_c = 1$, which the model needs. $\pi$, $\bar p$ and $\pi^\xi$ are real suprema (`sSup`). They are meaningful where the underlying set is nonempty and bounded above: $\pi$ on $X$; $\bar p$ always, since $\sum_i p_i q_{ci}(p) \le \sum_i e^{a_{ci} - 1}/b_i$; $\pi^\xi$ when $R(x,r) \cap X \neq \emptyset$. The outer $\max_c$ is `⨆ c`, attained because $M$ is finite and nonempty. Algorithm 1 is defined, not assumed: the line-8 loop is a left fold over a list `enum 𝒳₁`, the line-9 solution comes from a selection `sol`, the bounding rule `U` replaces $\pi^u$, and `bnbRun k` is the state after $k$ passes. The page never initialises $x^\star$; here it starts at $q_0(\underline p)$, where $\pi(q_0(\underline p)) = \Pi(\underline p)$ is the initial $\underline\pi$. **Constraints (15)–(16)** are printed as $\delta^+_c \le \mu_c(x) - \mu_c(\bar x_c(x,r))$ and $\delta^-_c \le \mu_c(\underline x_c(x,r)) - \mu_c(x)$. This file uses the two-sided form that the proof of Proposition 7 (p. 43) derives from them. The printed form is infeasible whenever $x_c > q_{c0}(\bar p)$ or $x_c < q_{c0}(\underline p)$, even when $R(x, r)$ meets $X$, and Algorithm 1 creates such a center at its first pass on some instances (e.g. $m = 2$, $n = 1$, $a = (-3, 3)$, $b = 1$). Whenever $\underline x(x,r) \le x \le \bar x(x,r)$, every feasible point of the printed LP is feasible here.
-- source:
--   van de Geer & den Boer, Price Optimization Under the Finite-Mixture Logit Model, SSRN 3235432 (version of August 26, 2021), pp. 6–7, 10–18, §2 (q_ci, q_c0, (2)), Proposition 1 (p̲, p̄), (3), cnstr-rev(x), μ, R(x, r) p. 14, π^ξ p. 15, LP(x, r) (13)–(17) p. 16, χ p. 17, Algorithm 1 p. 18

import Mathlib

/-!
van de Geer & den Boer, *Price Optimization Under the Finite-Mixture Logit Model*,
SSRN 3235432 (version of August 26, 2021).

The finite-mixture logit (FML) pricing model of §2 (pp. 6–7), the no-purchase
reparameterization of §3.2 (pp. 10–12), the boxes `R(x, r)` and the derivative-free bound
`π^ξ` of §3.4 (pp. 14–15), the linear program `LP(x, r)` and the map `χ` of §3.5
(pp. 16–17), and Algorithm 1 `BNB(ε)` of §3.6 (p. 18), with its bounding rule `π^u` left
as a parameter `U`.

Constraints (15)–(16) of `LP(x, r)` are encoded in the two-sided form
`μ_c(x̄_c) ≤ μ_c(x) − δ⁺_c + δ⁻_c ≤ μ_c(x̲_c)` that the proof of Proposition 7 (p. 43)
derives from them; the printed one-sided form `δ⁺_c ≤ μ_c(x) − μ_c(x̄_c)`,
`δ⁻_c ≤ μ_c(x̲_c) − μ_c(x)` with `δ± ≥ 0` is infeasible whenever `x_c > q_c0(p̄)` or
`x_c < q_c0(p̲)`, which Algorithm 1 produces at its first iteration on some instances.
-/

open Classical

namespace FMLPricing.BranchBound

/-- An FML instance (§2, pp. 6–7): `m` segments with shares `w c`, `n` products,
valuations `a c j` and price sensitivities `b j`. -/
structure FML (m n : ℕ) where
  w : Fin m → ℝ
  a : Fin m → Fin n → ℝ
  b : Fin n → ℝ

/-- Standing assumptions of §2: `m, n ≥ 1`, `w_c > 0` with `∑ w_c = 1`, `b_j > 0`. -/
structure Standing {m n : ℕ} (I : FML m n) : Prop where
  m_pos : 0 < m
  n_pos : 0 < n
  w_pos : ∀ c, 0 < I.w c
  w_sum : ∑ c, I.w c = 1
  b_pos : ∀ j, 0 < I.b j

variable {m n : ℕ} (I : FML m n)

/-- `1 + ∑_{j} exp(a_cj − b_j p_j)`, the logit denominator of segment `c`. -/
noncomputable def denom (c : Fin m) (p : Fin n → ℝ) : ℝ :=
  1 + ∑ j, Real.exp (I.a c j - I.b j * p j)

/-- `q_ci(p)`, the probability that a segment-`c` customer buys product `i` (p. 7). -/
noncomputable def q (c : Fin m) (i : Fin n) (p : Fin n → ℝ) : ℝ :=
  Real.exp (I.a c i - I.b i * p i) / denom I c p

/-- `q_0(p) = (q_10(p), …, q_m0(p))`, the no-purchase probabilities (pp. 7, 10). -/
noncomputable def q0 (p : Fin n → ℝ) : Fin m → ℝ :=
  fun c => 1 / denom I c p

/-- `Π(p) = ∑_c w_c ∑_j p_j q_cj(p)`, the expected revenue (2), p. 7. -/
noncomputable def Pi (p : Fin n → ℝ) : ℝ :=
  ∑ c, I.w c * ∑ j, p j * q I c j p

/-- `max_{p ∈ ℝⁿ} ∑_i p_i q_ci(p)`, the best single-segment revenue (Proposition 1, p. 10). -/
noncomputable def segMax (c : Fin m) : ℝ :=
  sSup (Set.range fun p : Fin n → ℝ => ∑ i, p i * q I c i p)

/-- `p̲_j = b_j⁻¹` (Proposition 1, p. 10). -/
noncomputable def pLo : Fin n → ℝ := fun j => (I.b j)⁻¹

/-- `p̄_j = b_j⁻¹ + max_{c} max_{p} ∑_i p_i q_ci(p)` (Proposition 1, p. 10). -/
noncomputable def pHi : Fin n → ℝ := fun j => (I.b j)⁻¹ + ⨆ c : Fin m, segMax I c

/-- The price box `[p̲, p̄]`. -/
def priceBox : Set (Fin n → ℝ) := Set.Icc (pLo I) (pHi I)

/-- `X = {q_0(p) : p ∈ [p̲, p̄]}` (3), p. 10. -/
def Xset : Set (Fin m → ℝ) := q0 I '' priceBox I

/-- `s_cj = e^{a_cj}` (p. 11). -/
noncomputable def s (c : Fin m) (j : Fin n) : ℝ := Real.exp (I.a c j)

/-- `k_jᵀ x = b_j⁻¹ ∑_c w_c s_cj x_c` (p. 11). -/
noncomputable def kx (j : Fin n) (x : Fin m → ℝ) : ℝ :=
  (I.b j)⁻¹ * ∑ c, I.w c * s I c j * x c

/-- `z̲_j = e^{−p̄_j b_j}` (p. 11). -/
noncomputable def zLo : Fin n → ℝ := fun j => Real.exp (-(pHi I j) * I.b j)

/-- `z̄_j = e^{−p̲_j b_j}` (p. 11). -/
noncomputable def zHi : Fin n → ℝ := fun j => Real.exp (-(pLo I j) * I.b j)

/-- The change of variables `z_j = e^{−p_j b_j}` (p. 11). -/
noncomputable def zOf (p : Fin n → ℝ) : Fin n → ℝ := fun j => Real.exp (-(p j) * I.b j)

/-- The inverse change of variables `p_j = −b_j⁻¹ log z_j` (Proposition 2, p. 12). -/
noncomputable def priceOf (z : Fin n → ℝ) : Fin n → ℝ := fun j => -(I.b j)⁻¹ * Real.log (z j)

/-- Feasible set of `cnstr-rev(x)` (p. 12): `z ∈ [z̲, z̄]` with
`1 + ∑_j s_cj z_j = 1 / x_c` for every `c`. -/
def cnstrFeasible (x : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {z | z ∈ Set.Icc (zLo I) (zHi I) ∧ ∀ c, 1 + ∑ j, s I c j * z j = 1 / x c}

/-- Objective of `cnstr-rev(x)` (p. 12): `−∑_j z_j log(z_j) k_jᵀ x`. -/
noncomputable def cnstrObj (x : Fin m → ℝ) (z : Fin n → ℝ) : ℝ :=
  -∑ j, z j * Real.log (z j) * kx I j x

/-- `π(x)`, the optimal value of `cnstr-rev(x)` (p. 12). Meaningful for `x ∈ X`, where the
feasible set is nonempty and compact. -/
noncomputable def piX (x : Fin m → ℝ) : ℝ :=
  sSup (cnstrObj I x '' cnstrFeasible I x)

/-- `z` is a maximizer of `cnstr-rev(x)`. -/
def IsCnstrMax (x : Fin m → ℝ) (z : Fin n → ℝ) : Prop :=
  z ∈ cnstrFeasible I x ∧ ∀ z' ∈ cnstrFeasible I x, cnstrObj I x z' ≤ cnstrObj I x z

/-- `μ(x) = ((1 − x_1)/x_1, …, (1 − x_m)/x_m)` (p. 13). -/
noncomputable def mu (x : Fin m → ℝ) : Fin m → ℝ := fun c => (1 - x c) / x c

/-- `x̲_c(x, r) = (x_c − r) ∨ q_c0(p̲)` (p. 14). -/
noncomputable def xLo (x : Fin m → ℝ) (r : ℝ) : Fin m → ℝ :=
  fun c => max (x c - r) (q0 I (pLo I) c)

/-- `x̄_c(x, r) = (x_c + r) ∧ q_c0(p̄)` (p. 14). -/
noncomputable def xHi (x : Fin m → ℝ) (r : ℝ) : Fin m → ℝ :=
  fun c => min (x c + r) (q0 I (pHi I) c)

/-- `R(x, r) = [x̲(x, r), x̄(x, r)]` (p. 14). -/
def Rbox (x : Fin m → ℝ) (r : ℝ) : Set (Fin m → ℝ) := Set.Icc (xLo I x r) (xHi I x r)

/-- Feasible set of the derivative-free bound `π^ξ(x, r)` (p. 15). -/
def xiFeasible (x : Fin m → ℝ) (r : ℝ) : Set (Fin m → Fin n → ℝ) :=
  {ξ | (∀ c j, zLo I j * xLo I x r c ≤ ξ c j ∧ ξ c j ≤ zHi I j * xHi I x r c) ∧
       ∀ c, 1 - xHi I x r c ≤ ∑ j, s I c j * ξ c j ∧ ∑ j, s I c j * ξ c j ≤ 1 - xLo I x r c}

/-- Objective of `π^ξ(x, r)` (p. 15):
`−∑_{c,j} ξ_cj log(ξ_cj / x̄_c(x, r)) s_cj w_c b_j⁻¹`. -/
noncomputable def xiObj (x : Fin m → ℝ) (r : ℝ) (ξ : Fin m → Fin n → ℝ) : ℝ :=
  -∑ c, ∑ j, ξ c j * Real.log (ξ c j / xHi I x r c) * s I c j * I.w c * (I.b j)⁻¹

/-- `π^ξ(x, r)`, the derivative-free upper bound (p. 15). -/
noncomputable def piXi (x : Fin m → ℝ) (r : ℝ) : ℝ :=
  sSup (xiObj I x r '' xiFeasible I x r)

/-- Decision variables `(γ, z, δ⁺, δ⁻)` of `LP(x, r)` (p. 16). -/
structure LPVars (m n : ℕ) where
  γ : ℝ
  z : Fin n → ℝ
  δp : Fin m → ℝ
  δm : Fin m → ℝ

/-- Feasibility in `LP(x, r)` (p. 16): (13), (14), (15)–(16) in the two-sided form
`μ_c(x̄_c(x, r)) ≤ μ_c(x) − δ⁺_c + δ⁻_c ≤ μ_c(x̲_c(x, r))`, (17), and `δ⁺, δ⁻ ≥ 0`. -/
def LPFeasibleAt (x : Fin m → ℝ) (r : ℝ) (v : LPVars m n) : Prop :=
  (∀ c, ∑ j, s I c j * v.z j + v.δp c - v.δm c = mu x c) ∧
  (∀ c, v.δp c + v.δm c ≤ v.γ) ∧
  (∀ c, v.δp c - v.δm c ≤ mu x c - mu (xHi I x r) c) ∧
  (∀ c, v.δm c - v.δp c ≤ mu (xLo I x r) c - mu x c) ∧
  (∀ j, zLo I j ≤ v.z j ∧ v.z j ≤ zHi I j) ∧
  (∀ c, 0 ≤ v.δp c ∧ 0 ≤ v.δm c)

/-- `LP(x, r)` is feasible. -/
def LPFeasible (x : Fin m → ℝ) (r : ℝ) : Prop := ∃ v, LPFeasibleAt I x r v

/-- `v` is a solution (a minimizer of `γ`) of `LP(x, r)`. -/
def IsLPSolution (x : Fin m → ℝ) (r : ℝ) (v : LPVars m n) : Prop :=
  LPFeasibleAt I x r v ∧ ∀ v', LPFeasibleAt I x r v' → v.γ ≤ v'.γ

/-- `χ(x, δ⁺, δ⁻)_c = x_c / (1 + x_c (δ⁻_c − δ⁺_c))` (p. 17). -/
noncomputable def chi (x δp δm : Fin m → ℝ) : Fin m → ℝ :=
  fun c => x c / (1 + x c * (δm c - δp c))

/-- State of `BNB(ε)`: lower bound `π̲`, upper bound `π̄ ∈ [−∞, ∞]`, radius `r`, the
centers `𝒳₁`, and the incumbent `x⋆`. -/
structure BNBState (m : ℕ) where
  lo : ℝ
  hi : EReal
  r : ℝ
  X1 : Finset (Fin m → ℝ)
  xs : Fin m → ℝ

/-- Accumulator of the `for` loop on line 8: `π̲`, `π̄`, `𝒳₂`, `x⋆`. -/
structure LoopAcc (m : ℕ) where
  lo : ℝ
  hi : EReal
  X2 : Finset (Fin m → ℝ)
  xs : Fin m → ℝ

/-- `r₀ = ½ max_c (q_c0(p̄) − q_c0(p̲))` (line 3). -/
noncomputable def r0 : ℝ := (1 / 2) * ⨆ c : Fin m, (q0 I (pHi I) c - q0 I (pLo I) c)

/-- Lines 1–4 of Algorithm 1: `π̲ = Π(p̲)`, `π̄ = ∞`, `r = r₀`, `𝒳₁ = {q_0(p̲) + r₀}`;
the incumbent `x⋆` (never initialised on the page) starts at `q_0(p̲)`. -/
noncomputable def bnbInit : BNBState m where
  lo := Pi I (pLo I)
  hi := ⊤
  r := r0 I
  X1 := {q0 I (pLo I) + fun _ => r0 I}
  xs := q0 I (pLo I)

/-- One pass of the body of the `for` loop on lines 8–14 at center `x` and radius `r`,
with bounding rule `U` (in place of `π^u`) and LP solution selection `sol` (line 9). -/
noncomputable def bnbVisit (U : (Fin m → ℝ) → ℝ → ℝ) (sol : (Fin m → ℝ) → ℝ → LPVars m n)
    (r : ℝ) (A : LoopAcc m) (x : Fin m → ℝ) : LoopAcc m :=
  if (Rbox I x r ∩ Xset I).Nonempty then
    let xδ := chi x (sol x r).δp (sol x r).δm
    let rδ := r + ‖x - xδ‖
    let lo₁ := if piX I xδ ≥ A.lo then piX I xδ else A.lo
    let xs₁ := if piX I xδ ≥ A.lo then xδ else A.xs
    let X2₁ := if U xδ rδ ≥ lo₁ then insert x A.X2 else A.X2
    let hi₁ := if ((U xδ rδ : ℝ) : EReal) ≥ A.hi then ((U xδ rδ : ℝ) : EReal) else A.hi
    ⟨lo₁, hi₁, X2₁, xs₁⟩
  else A

/-- The children `x + ω r` for `ω ∈ {−1, 1}^m` (lines 18–19). -/
noncomputable def children (r : ℝ) (x : Fin m → ℝ) : Finset (Fin m → ℝ) :=
  Finset.univ.image fun σ : Fin m → Bool => x + r • fun c => if σ c then (1 : ℝ) else -1

/-- Lines 6–19 of Algorithm 1: reset `π̄ = −∞` and `𝒳₂ = ∅`, visit the centers of `𝒳₁` in
the order `enum S.X1`, halve `r`, and branch every center of `𝒳₂` with the halved radius. -/
noncomputable def bnbBody (U : (Fin m → ℝ) → ℝ → ℝ) (sol : (Fin m → ℝ) → ℝ → LPVars m n)
    (enum : Finset (Fin m → ℝ) → List (Fin m → ℝ)) (S : BNBState m) : BNBState m :=
  let A := (enum S.X1).foldl (bnbVisit I U sol S.r) ⟨S.lo, ⊥, ∅, S.xs⟩
  let r' := S.r / 2
  ⟨A.lo, A.hi, r', A.X2.biUnion (children r'), A.xs⟩

/-- The test of the `while` loop, line 5: `(1 − ε) π̄ > π̲` in `[−∞, ∞]`. -/
def bnbCond (ε : ℝ) (S : BNBState m) : Prop :=
  ((1 - ε : ℝ) : EReal) * S.hi > (S.lo : EReal)

/-- The state of `BNB(ε)` after `k` passes through the loop body. -/
noncomputable def bnbRun (U : (Fin m → ℝ) → ℝ → ℝ) (sol : (Fin m → ℝ) → ℝ → LPVars m n)
    (enum : Finset (Fin m → ℝ) → List (Fin m → ℝ)) (k : ℕ) : BNBState m :=
  (bnbBody I U sol enum)^[k] (bnbInit I)

end FMLPricing.BranchBound


