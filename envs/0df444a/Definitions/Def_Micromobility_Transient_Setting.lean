-- Prove2me | Definitions.Def_Micromobility_Transient_Setting
-- name    : Micromobility_Transient_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:38.423996+00:00
-- url     : https://prove2.me/theorems/4472daf2-854d-4eaf-95c8-8e05347133a0
-- title:
--   §2–§4 and App. F — the compact mean-field rebalancing model: Â, X̆, (F.1)–(F.6), N̂ (3.4), V̂, the transient-horizon policy (4.1)–(4.3)
-- statement:
--   This file fixes the compact mean-field model of shared-micromobility rebalancing of Akturk, Candogan and Gupta, together with the objects that Theorem 4.2 and its supporting results are about.
--
--   **Primitives (§2, pp. 8–12).** There are $\hat e$ station types $e = 1, \dots, \hat e$, with $n_e$ stations of type $e$ and $n = \sum_e n_e$ stations in total. A customer leaving a type-$e'$ station returns the unit at a type-$e$ station with probability
--   $$p_{e',e} = \frac{n_e w_{e',e}}{\sum_{e_2} w_{e',e_2} n_{e_2}},$$
--   for nonnegative weights $w_{e',e}$. Demand at a type-$e$ station has law $D^e$ on $\mathbb N_0$. A returned unit is still charged with probability $q$. Costs are discounted by $\gamma$. The extended types are $0$ (the warehouse), $1, \dots, \hat e$ (charged units of each type) and $\hat e + 1, \dots, 2\hat e$ (the depleted stock of each type); moving one unit from extended type $e_1$ to $e_2$ costs $c_{e_1,e_2}$. The holding cost is $c_h$ and the shortage cost $c_p$. Rebalancing keeps between $L^e$ and $U^e$ charged units at each type-$e$ station and between $L^{r,e}$ and $U^{r,e}$ (scaled) depleted units of type $e$.
--
--   **Standing assumptions.** $0 \le \gamma < 1$, $0 \le q \le 1$, $n_e \ge 1$, $w \ge 0$ with $\sum_{e_2} w_{e',e_2} n_{e_2} > 0$, $L^e \le U^e$, $0 \le L^{r,e} \le U^{r,e}$, each $D^e$ has finite mean and variance, $c_{e_1,e_2} \ge c_{e_1,e_1}/2 + c_{e_2,e_2}/2$ for all $e_1, e_2$, $c_{0,0} = 0$, $c_{\hat e + e, \hat e + e} = 0$, and $c_{e_1,e_2} \ge 0$.
--
--   **Actions (p. 15).** An action $\hat a \in \hat A$ consists of fractions $\hat a_{e,d} \ge 0$, zero unless $L^e \le d \le U^e$, with $\sum_{d=L^e}^{U^e} \hat a_{e,d} = n_e/n$, and a scaled depleted stock $\hat a_{e,r} \in [L^{r,e}, U^{r,e}]$.
--
--   **Transitions ((3.2), (F.1)–(F.5)).** Returned charged units at type $e$ arrive as $\hat R^e \sim \mathrm{Pois}(\lambda_e(\hat a))$ with
--   $$\lambda_e(\hat a) = q\,\frac{n}{n_e}\sum_{e'} p_{e',e}\sum_{b=L^{e'}}^{U^{e'}} \hat a_{e',b}\,\mathbb E[\min(b, D^{e'})],$$
--   independent of $D^e$. The next state $\breve x' = \breve x'(\hat a)$ depends on the action only:
--   $$\breve x'_{e,d} = \sum_{b=L^e}^{U^e} \hat a_{e,b}\,\mathbb P[b - \min(b, D^e) + \hat R^e = d] \ (d \le U^e), \qquad \breve x'_{e,d} = 0 \ (d > U^e),$$
--   $\breve x'_{e,r} = \hat a_{e,r} + (1-q)\sum_{e'} p_{e',e}\sum_b \hat a_{e',b}\mathbb E[\min(b, D^{e'})]$, and $\breve x'_{e,s}$, $\breve x'_{e,u}$ aggregate the mass above $U^e$ with weights $d$ and $d - U^e$.
--
--   **States (p. A-22).** The compact state space $\breve X$ is the set of $\breve x = (\breve x_{e,d}, \breve x_{e,r}, \breve x_{e,s}, \breve x_{e,u})$ with $\breve x_{e,d} = 0$ for $d > U^e$, $\sum_{d=0}^{U^e - 1} \breve x_{e,d} \le n_e/n$, and $\breve x_{e,r}, \breve x_{e,s}, \breve x_{e,u}$ in the intervals of p. A-22, whose upper ends are the values these coordinates take when every station of every type holds $U^e$ units (with the Poisson variable $\hat R^{e,u}$ of rate $q\frac{n}{n_e}\sum_{e'} p_{e',e}\frac{n_{e'}}{n}\mathbb E[\min(U^{e'}, D^{e'})]$). An action $\hat a$ is read as a state (p. A-31) with $\breve x_{e,d} = \hat a_{e,d}$, $\breve x_{e,r} = \hat a_{e,r}$ and $\breve x_{e,s} = \breve x_{e,u} = 0$.
--
--   **Costs ((F.6), (3.4)).** The rebalancing cost is
--   $$\hat c_2(\breve x, \hat a) = n\sum_e \frac{c_{e,e}}{2}\breve x_{e,u} + n\sum_e\frac{c_{e,e}}{2}\sum_{b=0}^{U^e-1}\Big|\sum_{d=0}^{b}(\breve x_{e,d} - \hat a_{e,d})\Big| + n\,\Phi(\breve x, \hat a),$$
--   where $\Phi$ is the optimal value of the min-cost-flow problem: minimize $\sum_{e_1}\sum_{e_2 \ne e_1}(c_{e_1,e_2} - c_{e_1,e_1}/2 - c_{e_2,e_2}/2)\,y^{e_1,e_2}$ over $y \ge 0$ subject to $\breve x_{e,s} + \sum_{b=1}^{U^e} b(\breve x_{e,b} - \hat a_{e,b}) = \sum_{e_1}(y^{e,e_1} - y^{e_1,e})$ and $\breve x_{e,r} - \hat a_{e,r} = \sum_{e_1}(y^{\hat e+e,e_1} - y^{e_1,\hat e+e})$ for every type $e$. The newsvendor cost is
--   $$\hat N(\hat a) = n c_h\sum_e\sum_{b} b\,\hat a_{e,b} + n c_h\sum_e \hat a_{e,r} + n c_p\sum_e\sum_b \hat a_{e,b}\,\mathbb E[(D^e - b)^+].$$
--
--   **Values and the policy.** For an initial state $\breve x$ and actions $a_0, a_1, \dots$, the trajectory is $\breve x^0 = \breve x$, $\breve x^{k+1} = \breve x'(a_k)$, and the discounted cost is $J(\breve x, a) = \sum_{k \ge 0}\gamma^k(\hat c_2(\breve x^k, a_k) + \hat N(a_k))$. The value function is
--   $$\hat V(\breve x) = \inf_{\{a_k\} \subset \hat A} J(\breve x, a),$$
--   the infimum over action sequences in $\hat A$. For a transient horizon $T$ and $\tilde a = (\tilde a^0, \dots, \tilde a^T) \in \hat A^{T+1}$, the objective of (4.1) is
--   $$\sum_{k=0}^{T-1}\gamma^k\big(\hat c_2(\breve x^k, \tilde a^k) + \hat N(\tilde a^k)\big) + \gamma^T \hat c_2(\breve x^T, \tilde a^T) + \frac{\gamma^T}{1-\gamma}\big(\gamma\hat c_2(\breve x^{T+1}, \tilde a^T) + \hat N(\tilde a^T)\big),$$
--   and the policy $\tilde\pi$ of (4.2)–(4.3) plays $\tilde a^k$ in period $k < T$ and $\tilde a^T$ in every period $k \ge T$. Theorem 4.2's constant is
--   $$C = 2\sum_{e=1}^{\hat e}\Big(n_e\max(c_{0,e}, c_{e,0})(U^e - L^e) + n\max(c_{0,\hat e+e}, c_{\hat e+e,0})(U^{r,e} - L^{r,e})\Big).$$
--
--   **Optimality notions.** An action $\hat a$ is optimal at $\breve x$ if $\hat a \in \hat A$ minimizes $\hat c_2(\breve x, \cdot) + \hat N(\cdot) + \gamma\hat V(\breve x'(\cdot))$ over $\hat A$ (the minimization in the Bellman equation (3.6)); a policy is optimal if it takes an optimal action at every state of $\breve X$. A fixed point (Definition H.1) is a state $\breve x^f \in \breve X$ with an optimal action $\hat a^f$ such that $\breve x'(\hat a^f) = \breve x^f$. The triangle inequality of Lemma H.7 is $\hat c_2(\breve x, \hat a) \le \hat c_2(\breve x, \hat z) + \hat c_2(\hat z, \hat a)$ for $\breve x \in \breve X$ and $\hat a, \hat z \in \hat A$.
--
--   These are the objects of the paper's §3.4–§4 and Appendices F and H; every result of the mission is stated about them.
--
--   **Formalization Note.** The model is built on two general definitions of this mission: the flow value $\Phi$ is the transshipment LP `transshipValue` (nodes `Fin (2ê+1)`, balance nodes the charged types and depleted stocks, the warehouse free), and $J$, $\hat V$ and the trajectory are those of the deterministic dynamic program `DetDP` with admissible actions $\hat A$, transition (F.1)–(F.5) and stage cost $\hat c_2 + \hat N$. Types are `Fin ê` (0-based: the paper's type $e$ is index $e-1$); extended types are `Fin (2ê+1)` with `chg e` $= e$ and `dep e` $= \hat e + e$ in the paper's numbering. Level vectors are functions $\mathbb N \to \mathbb R$. $\mathbb P[b - \min(b, D^e) + \hat R^e = d]$ is the convolution $\sum_k \mathbb P(D^e = k)\,\mathrm{Pois}(\lambda)(d - (b-k)^+)$, which is the paper's quantity under the independence of $D^e$ and $\hat R^e$. $\hat V$ is the infimum over the subtype of $\hat A$-valued sequences (p. 18 and Proposition F.3), not the Bellman fixed point of (3.6); (3.6) is a separate result. The flow value is an infimum over feasible $y \ge 0$; the feasible set is nonempty (route every imbalance through the warehouse) and the objective is bounded below by $0$, so it is not a junk value. $\breve X$ is formalized exactly as printed: it does not require $\breve x_{e,d} \ge 0$. The upper end of $\breve x_{e,r}$'s interval uses the action bound $U^{r,e}$ (printed "$U^e_r$"). The disclosed additions to the paper's hypotheses are $\gamma \ge 0$ and $c_{e_1,e_2} \ge 0$. Everything is time-homogeneous and stated at $t = 0$.
-- source:
--   Akturk, Candogan, Gupta, Managing Resources for Shared Micromobility: Approximate Optimality in Large-Scale Systems, SSRN 4155841 (version of 2024-05-22), pp. 9–18, 25, A-22–A-25, A-28, A-31, (3.2)–(3.6), (4.1)–(4.3), (F.1)–(F.6), Definition H.1

import Mathlib
import Definitions.Def_Micromobility_Transient_TransshipLP
import Definitions.Def_Micromobility_Transient_DetDP

namespace Micromobility.Transient

open Finset

/-! # The compact mean-field rebalancing model (Akturk, Candogan, Gupta, SSRN 4155841)

The paper's types `e = 1, …, ê` are `Fin ê` (0-based: the paper's type `e` is index `e - 1`).
The extended types `0, 1, …, 2ê` of p. 11–12 are `Fin (2 * ê + 1)`: `0` is the warehouse,
`chg e` is the charged type `e`, `dep e` is the depleted stock `ê + e`. -/

/-- The extended index of the charged type `e` (the paper's `e ∈ {1, …, ê}`). -/
def chg {ê : ℕ} (e : Fin ê) : Fin (2 * ê + 1) := ⟨e.val + 1, by omega⟩

/-- The extended index of the depleted stock of type `e` (the paper's `ê + e`). -/
def dep {ê : ℕ} (e : Fin ê) : Fin (2 * ê + 1) := ⟨ê + e.val + 1, by omega⟩

/-- The primitives of the model (pp. 8–12). -/
structure Model (ê : ℕ) where
  /-- `n_e`, the number of stations of type `e`. -/
  nst : Fin ê → ℕ
  /-- the destination weights `w_{e',e}`. -/
  w : Fin ê → Fin ê → ℝ
  /-- the law of the demand `D^e` at a type-`e` station. -/
  D : Fin ê → PMF ℕ
  /-- the action bounds `L^e ≤ U^e` on charged units per station. -/
  L : Fin ê → ℕ
  U : Fin ê → ℕ
  /-- the action bounds `L^{r,e} ≤ U^{r,e}` on (scaled) depleted units. -/
  Lr : Fin ê → ℝ
  Ur : Fin ê → ℝ
  /-- `q`, the probability that a returned unit is still charged. -/
  q : ℝ
  /-- `γ`, the discount factor. -/
  γ : ℝ
  /-- the holding cost `c_h` and the shortage (penalty) cost `c_p`. -/
  ch : ℝ
  cp : ℝ
  /-- the unit rebalancing costs `c_{e1,e2}` between extended types. -/
  c : Fin (2 * ê + 1) → Fin (2 * ê + 1) → ℝ

/-- An action `â ∈ Â` (p. 15): `d e b` is `â_{e,b}`, `r e` is `â_{e,r}`. -/
structure Action (ê : ℕ) where
  d : Fin ê → ℕ → ℝ
  r : Fin ê → ℝ

/-- A compact state `x̆ ∈ X̆` (p. A-22): `d e b = x̆_{e,b}`, `r e = x̆_{e,r}`, `s e = x̆_{e,s}`,
`u e = x̆_{e,u}`. -/
structure State (ê : ℕ) where
  d : Fin ê → ℕ → ℝ
  r : Fin ê → ℝ
  s : Fin ê → ℝ
  u : Fin ê → ℝ

/-- An action read as a state (p. A-31): `u = s = 0`, `r = â_r`, `d = â_d`. -/
def toState {ê : ℕ} (a : Action ê) : State ê where
  d := a.d
  r := a.r
  s := fun _ => 0
  u := fun _ => 0

/-- The policy (4.2)–(4.3) as an action sequence: `ã^k` for `k < T`, then `ã^T` forever. -/
def policySeq {ê : ℕ} (T : ℕ) (ã : Fin (T + 1) → Action ê) : ℕ → Action ê :=
  fun k => ã ⟨min k T, Nat.lt_succ_of_le (min_le_right k T)⟩

namespace Model

variable {ê : ℕ} (M : Model ê)

/-- `n = Σ_e n_e`, the total number of stations. -/
noncomputable def n : ℝ := ∑ e, (M.nst e : ℝ)

/-- `p_{e',e} = n_e w_{e',e} / Σ_{e2} w_{e',e2} n_{e2}` (p. 9). -/
noncomputable def p (e' e : Fin ê) : ℝ :=
  (M.nst e : ℝ) * M.w e' e / ∑ e2, M.w e' e2 * (M.nst e2 : ℝ)

/-- The standing assumptions of §2 (pp. 8–12), plus the disclosed additions `0 ≤ γ` and
`c_{e1,e2} ≥ 0`. -/
structure Standing : Prop where
  gamma_nonneg : 0 ≤ M.γ
  gamma_lt_one : M.γ < 1
  q_nonneg : 0 ≤ M.q
  q_le_one : M.q ≤ 1
  nst_pos : ∀ e, 1 ≤ M.nst e
  w_nonneg : ∀ e' e, 0 ≤ M.w e' e
  w_sum_pos : ∀ e', 0 < ∑ e2, M.w e' e2 * (M.nst e2 : ℝ)
  L_le_U : ∀ e, M.L e ≤ M.U e
  Lr_nonneg : ∀ e, 0 ≤ M.Lr e
  Lr_le_Ur : ∀ e, M.Lr e ≤ M.Ur e
  /-- finite mean and finite variance of `D^e` -/
  D_second_moment : ∀ e, Summable (fun k : ℕ => (M.D e k).toReal * (k : ℝ) ^ 2)
  /-- the cost assumption of p. 12 -/
  c_triangle : ∀ e1 e2, M.c e1 e1 / 2 + M.c e2 e2 / 2 ≤ M.c e1 e2
  c_warehouse : M.c 0 0 = 0
  c_dep_diag : ∀ e, M.c (dep e) (dep e) = 0
  /-- disclosed addition (paper.md slip 9) -/
  c_nonneg : ∀ e1 e2, 0 ≤ M.c e1 e2

/-- `𝔼[min(b, D^e)]`. -/
noncomputable def EminD (e : Fin ê) (b : ℕ) : ℝ :=
  ∑' k : ℕ, (M.D e k).toReal * ((min b k : ℕ) : ℝ)

/-- `𝔼[(D^e - b)^+]`. -/
noncomputable def EposD (e : Fin ê) (b : ℕ) : ℝ :=
  ∑' k : ℕ, (M.D e k).toReal * max ((k : ℝ) - (b : ℝ)) 0

/-- The Poisson probability `ℙ[Pois(λ) = j] = e^{-λ} λ^j / j!`. -/
noncomputable def poisPMF (lam : ℝ) (j : ℕ) : ℝ := Real.exp (-lam) * lam ^ j / (j.factorial : ℝ)

/-- `ℙ[b - min(b, D^e) + R = d]` for `R ~ Pois(λ)` independent of `D^e`
(the convolution of the two laws; `b - k` is truncated, i.e. `b - min(b, k)`). -/
noncomputable def transProb (e : Fin ê) (lam : ℝ) (b d : ℕ) : ℝ :=
  ∑' k : ℕ, (M.D e k).toReal *
    (if b - k ≤ d then poisPMF lam (d - (b - k)) else 0)

/-- The Poisson rate of `R̂^e` under action `â` (3.2):
`q (n/n_e) Σ_{e'} p_{e',e} Σ_{b=L^{e'}}^{U^{e'}} â_{e',b} 𝔼[min(b, D^{e'})]`. -/
noncomputable def lam (a : Action ê) (e : Fin ê) : ℝ :=
  M.q * (M.n / (M.nst e : ℝ)) *
    ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), a.d e' b * M.EminD e' b

/-- The Poisson rate of `R̂^{e,u}` (p. A-22):
`q (n/n_e) Σ_{e'} p_{e',e} (n_{e'}/n) 𝔼[min(U^{e'}, D^{e'})]`. -/
noncomputable def lamU (e : Fin ê) : ℝ :=
  M.q * (M.n / (M.nst e : ℝ)) *
    ∑ e', M.p e' e * ((M.nst e' : ℝ) / M.n) * M.EminD e' (M.U e')

/-- Membership in the action set `Â` (p. 15). -/
structure InA (a : Action ê) : Prop where
  nonneg : ∀ e d, 0 ≤ a.d e d
  support : ∀ e d, (d < M.L e ∨ M.U e < d) → a.d e d = 0
  mass : ∀ e, ∑ d ∈ Icc (M.L e) (M.U e), a.d e d = (M.nst e : ℝ) / M.n
  r_ge : ∀ e, M.Lr e ≤ a.r e
  r_le : ∀ e, a.r e ≤ M.Ur e

/-- Membership in the compact state space `X̆` (p. A-22), exactly as printed. -/
structure InX (x : State ê) : Prop where
  d_zero : ∀ e d, M.U e < d → x.d e d = 0
  d_sum : ∀ e, ∑ d ∈ range (M.U e), x.d e d ≤ (M.nst e : ℝ) / M.n
  r_nonneg : ∀ e, 0 ≤ x.r e
  r_le : ∀ e, x.r e ≤ M.Ur e + (1 - M.q) *
    ∑ e', M.p e' e * ((M.nst e' : ℝ) / M.n) * M.EminD e' (M.U e')
  s_nonneg : ∀ e, 0 ≤ x.s e
  s_le : ∀ e, x.s e ≤ ∑' d : ℕ,
    (if M.U e < d then (d : ℝ) * ((M.nst e : ℝ) / M.n) * M.transProb e (M.lamU e) (M.U e) d
      else 0)
  u_nonneg : ∀ e, 0 ≤ x.u e
  u_le : ∀ e, x.u e ≤ ∑' d : ℕ,
    (if M.U e < d then ((d : ℝ) - (M.U e : ℝ)) * ((M.nst e : ℝ) / M.n) *
      M.transProb e (M.lamU e) (M.U e) d else 0)

/-- `Σ_{b=L^e}^{U^e} â_{e,b} ℙ[b - min(b, D^e) + R̂^e = d]`, the mass at level `d` after the
period (the common inner sum of (F.1), (F.4), (F.5)). -/
noncomputable def mixProb (a : Action ê) (e : Fin ê) (d : ℕ) : ℝ :=
  ∑ b ∈ Icc (M.L e) (M.U e), a.d e b * M.transProb e (M.lam a e) b d

/-- The transition (F.1)–(F.5): the next state depends on the action only. -/
noncomputable def next (a : Action ê) : State ê where
  d := fun e d => if d ≤ M.U e then M.mixProb a e d else 0
  r := fun e => a.r e + (1 - M.q) *
    ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), a.d e' b * M.EminD e' b
  s := fun e => ∑' d : ℕ, (if M.U e < d then (d : ℝ) * M.mixProb a e d else 0)
  u := fun e => ∑' d : ℕ,
    (if M.U e < d then ((d : ℝ) - (M.U e : ℝ)) * M.mixProb a e d else 0)

/-- The balance nodes of the flow component of (F.6): the charged types `chg e` (left summand)
and the depleted stocks `dep e` (right summand). The warehouse `0` is not a balance node. -/
def extNode : Fin ê ⊕ Fin ê → Fin (2 * ê + 1) := Sum.elim chg dep

/-- The required net outflows of the flow component of (F.6), p. A-25:
`x̆_{e,s} + Σ_{b=1}^{U^e} b (x̆_{e,b} - â_{e,b})` at the charged type `e`, and `x̆_{e,r} - â_{e,r}` at the
depleted stock `ê + e`. -/
noncomputable def flowSupply (x : State ê) (a : Action ê) : Fin ê ⊕ Fin ê → ℝ :=
  Sum.elim (fun e => x.s e + ∑ b ∈ Icc 1 (M.U e), (b : ℝ) * (x.d e b - a.d e b))
    (fun e => x.r e - a.r e)

/-- The arc costs of the flow component of (F.6): `c_{e1,e2} - c_{e1,e1}/2 - c_{e2,e2}/2`. -/
noncomputable def flowCoeff (e1 e2 : Fin (2 * ê + 1)) : ℝ :=
  M.c e1 e2 - M.c e1 e1 / 2 - M.c e2 e2 / 2

/-- The feasible flows of (F.6), p. A-25: `y ≥ 0`, one balance constraint per charged type and one
per depleted stock (`Σ_{e1} (y^{i,e1} - y^{e1,i})` = the required net outflow); none at the
warehouse. -/
def FlowFeasible (x : State ê) (a : Action ê) (y : Fin (2 * ê + 1) → Fin (2 * ê + 1) → ℝ) :
    Prop :=
  TransshipFeasible extNode (M.flowSupply x a) y

/-- The objective of the flow component of (F.6):
`Σ_{e1} Σ_{e2 ≠ e1} (c_{e1,e2} - c_{e1,e1}/2 - c_{e2,e2}/2) y^{e1,e2}`. -/
noncomputable def flowCost (y : Fin (2 * ê + 1) → Fin (2 * ê + 1) → ℝ) : ℝ :=
  transshipCost M.flowCoeff y

/-- The optimal value of the flow LP of (F.6): the transshipment LP on the extended types with arc
costs `flowCoeff`, balance nodes `extNode` and net outflows `flowSupply x̆ â`. -/
noncomputable def flowValue (x : State ê) (a : Action ê) : ℝ :=
  transshipValue M.flowCoeff extNode (M.flowSupply x a)

/-- The rebalancing cost `ĉ₂(x̆, â)` (F.6), pp. A-24–A-25. -/
noncomputable def c2 (x : State ê) (a : Action ê) : ℝ :=
  M.n * ∑ e, M.c (chg e) (chg e) / 2 * x.u e +
  M.n * ∑ e, M.c (chg e) (chg e) / 2 *
    ∑ b ∈ range (M.U e), |∑ d ∈ range (b + 1), (x.d e d - a.d e d)| +
  M.n * M.flowValue x a

/-- The newsvendor cost `N̂(â)` (3.4), p. 18. -/
noncomputable def Nhat (a : Action ê) : ℝ :=
  M.n * M.ch * ∑ e, ∑ b ∈ Icc (M.L e) (M.U e), (b : ℝ) * a.d e b +
  M.n * M.ch * ∑ e, a.r e +
  M.n * M.cp * ∑ e, ∑ b ∈ Icc (M.L e) (M.U e), a.d e b * M.EposD e b

/-- The compact mean-field model as a discounted deterministic dynamic program on `X̆`-states:
admissible actions `Â`, transition (F.1)–(F.5) (which depends on the action only), stage cost
`ĉ₂(x̆, â) + N̂(â)`, discount `γ`. -/
noncomputable def dp : DetDP (State ê) (Action ê) where
  admissible := M.InA
  step := fun _ a => M.next a
  cost := fun x a => M.c2 x a + M.Nhat a
  γ := M.γ

/-- The state trajectory of an action sequence: `x_0 = x̆`, `x_{k+1}` is (F.1)–(F.5) of `a_k`. -/
noncomputable def traj (x : State ê) (a : ℕ → Action ê) : ℕ → State ê := M.dp.traj x a

/-- The discounted cost `Σ_k γ^k (ĉ₂(x_k, a_k) + N̂(a_k))` of an action sequence from `x̆`. -/
noncomputable def J (x : State ê) (a : ℕ → Action ê) : ℝ := M.dp.J x a

/-- The value function `V̂(x̆)` (p. 18, Proposition F.3): the infimum of `J x̆` over the action
sequences that stay in `Â`. -/
noncomputable def Vhat (x : State ê) : ℝ := M.dp.V x

/-- The objective of the program (4.1) at `x̆` with transient horizon `T`, evaluated at
`ã = (ã^0, …, ã^T)`, where `x̆^k` is the trajectory of `ã` (`x̆^0 = x̆`, `x̆^{k+1}` = (F.1)–(F.5)
of `ã^k`, `k ≤ T`). -/
noncomputable def obj41 (x : State ê) (T : ℕ) (ã : Fin (T + 1) → Action ê) : ℝ :=
  ∑ k ∈ range T, M.γ ^ k *
      (M.c2 (M.traj x (policySeq T ã) k) (policySeq T ã k) + M.Nhat (policySeq T ã k)) +
  M.γ ^ T * M.c2 (M.traj x (policySeq T ã) T) (ã (Fin.last T)) +
  M.γ ^ T / (1 - M.γ) *
    (M.γ * M.c2 (M.traj x (policySeq T ã) (T + 1)) (ã (Fin.last T)) + M.Nhat (ã (Fin.last T)))

/-- Theorem 4.2's constant
`C = 2 Σ_e ( n_e max(c_{0,e}, c_{e,0})(U^e - L^e) + n max(c_{0,ê+e}, c_{ê+e,0})(U^{r,e} - L^{r,e}) )`. -/
noncomputable def Cconst : ℝ :=
  2 * ∑ e, ((M.nst e : ℝ) * max (M.c 0 (chg e)) (M.c (chg e) 0) * ((M.U e : ℝ) - (M.L e : ℝ)) +
    M.n * max (M.c 0 (dep e)) (M.c (dep e) 0) * (M.Ur e - M.Lr e))

/-- `â` attains the minimum of the Bellman right-hand side (3.6) at `x̆`:
`â ∈ Â` and `ĉ₂(x̆, â) + N̂(â) + γ V̂(x̆')` is minimal over `Â`, `x̆'` being (F.1)–(F.5) of the action. -/
def IsOptimalAction (x : State ê) (a : Action ê) : Prop :=
  M.InA a ∧ ∀ a', M.InA a' →
    M.c2 x a + M.Nhat a + M.γ * M.Vhat (M.next a) ≤ M.c2 x a' + M.Nhat a' + M.γ * M.Vhat (M.next a')

/-- A stationary policy that takes an optimal action at every state of `X̆`. -/
def IsOptimalPolicy (π : State ê → Action ê) : Prop :=
  ∀ y, M.InX y → M.IsOptimalAction y (π y)

/-- Definition H.1 (p. A-28): `x̆^f ∈ X̆` is a fixed point with fixed point action `â^f` if `â^f`
is optimal at `x̆^f` and taking `â^f` leads back to `x̆^f`. -/
def IsFixedPoint (xf : State ê) (af : Action ê) : Prop :=
  M.InX xf ∧ M.IsOptimalAction xf af ∧ M.next af = xf

/-- The triangle inequality of `ĉ₂` in the sense of Lemma H.7 (p. A-32), with the second
`ĉ₂(ẑ, ·)` read through the action-as-state convention of p. A-31. -/
def TriangleIneq : Prop :=
  ∀ x, M.InX x → ∀ a z, M.InA a → M.InA z → M.c2 x a ≤ M.c2 x z + M.c2 (toState z) a

end Model

end Micromobility.Transient


