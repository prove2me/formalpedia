-- Prove2me | Definitions.Def_MDPFinance_JumpMarkets_TradeExecution
-- name    : MDPFinance_JumpMarkets_TradeExecution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:23:19.424827+00:00
-- url     : https://prove2.me/theorems/ca106b71-e289-4df9-9fd0-b3ef9386ae5a
-- title:
--   Trade execution in illiquid markets: the dark-pool model, its operator and IM_cx
-- statement:
--   The data of §9.4. An agent holds $x_0 \in \mathbb{N}$ shares and must sell them within
--   $[0,T]$, but can only sell in blocks at the jump times of a Poisson process of intensity $\lambda$
--   — a **dark pool**, where there is no order book and liquidity arrives at random. Selling $a$ shares
--   costs $C(a)$, where $C : \mathbb{N}_0 \to \mathbb{R}_+$ is strictly increasing and strictly convex
--   with $C(0) = 0$; strict convexity is in its discrete form
--
--   $$ C(x) - C(x-1) < C(x+1) - C(x), \quad x \in \mathbb{N}. \tag{9.19} $$
--
--   $C$ is the market depth function, so small blocks are cheaper; but everything unsold at $T$ is
--   dumped on a traditional market at once, costing $C(X_T)$, which is the tension the problem is
--   about. The state process is $X_t = x_0 - \int_0^t \pi_s dN_s$ and the problem is to **minimise**
--
--   $$ V_\pi(t,x) := \mathbb{E}^\pi_{tx}\Big[\int_t^T C(\pi_s)dN_s + C(X_T)\Big], \qquad
--   V(t,x) := \inf_\pi V_\pi(t,x) $$
--
--   over admissible controls, those with $\pi_t \le X_t$ for all $t$.
--
--   The embedded discrete-time model has state space $E = [0,T] \times \mathbb{N}_0$, action space
--   $A := \{\alpha : [0,T] \to \mathbb{N}_0 \text{ measurable}\}$ **(9.20)** with
--   $D(x) := \{\alpha \in A \mid \alpha_t \le x\}$, and one-stage cost
--
--   $$ c(t,x,\alpha) := \int_0^{T-t}\lambda e^{-\lambda s}C(\alpha_s)ds + e^{-\lambda(T-t)}C(x). \tag{9.21} $$
--
--   The flow is **uncontrolled** here — $\phi^\alpha_t(x) = x$, the inventory does not move between
--   jumps — which makes this model simpler than §9.3's. The dynamic programming operator is
--
--   $$ (\mathcal{T}v)(t,x) = \int_0^{T-t}\lambda e^{-\lambda s}\min_{u \in \{0,\dots,x\}}\big(C(u) +
--   v(t+s, x-u)\big)ds + e^{-\lambda(T-t)}C(x), $$
--
--   with $f^*(t,x) = \operatorname{argmin}_{u \in \{0,\dots,x\}}(C(u) + v(t,x-u))$ **(9.22)**, the
--   **smallest** minimizer — the book's own choice, and what makes Theorem 9.4.2's unit-Lipschitz bound
--   meaningful. Finally
--
--   $$ IM_{cx} := \{v \in IB_b \mid v(t,x) \le C(x),\ v(t,0) = 0,\ v \text{ convex in } x,\
--   v \text{ continuous and increasing in } t, x\}. $$
--
--   **Convex, not concave.** This is a minimisation with a convex cost and a convex value function,
--   the opposite curvature from §9.3's terminal wealth problem; $IM_{cx}$ and $IM_{cv}$ are different
--   sets and neither theorem may use the other's. The clauses $v(t,x) \le C(x)$ and $v(t,0) = 0$ are
--   the two properties "which can immediately be seen" (p. 295) and are part of the set's definition.
--
--   Unlike §9.3 this section needs no `IsLUB` device: the inner optimisation is a minimum over the
--   **finite** set $\{0,\dots,x\}$, which is a genuine function.
--
--   **Moderation note.** The draft had no value function for §9.4 at all: Theorem 9.4.2 could only speak about *some* fixed point of `𝒯`. Now the embedded model's value `V(t,x) = inf_π V_π(t,x)` is defined from the one-stage costs (`J_n`, `J_{∞π}`, `V`, in `[0,∞]`) over admissible measurable Markov policies (`Offer` carries the product σ-algebra). The cost, operator, smallest minimizer `f^*`, `IM_cx` and the bounding-function predicate are as drafted.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §9.4, pp. 293-296 (PDF 303-306)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MDPFinance.JumpMarkets

/-- The **trade execution problem** of §9.4 (p. 293): trading epochs at the jumps of a Poisson
process of intensity `λ`, horizon `T`, and the cost `C(a)` of selling `a` shares, `C : ℕ_0 → ℝ_+`
strictly increasing, strictly convex in the discrete sense **(9.19)**, `C(0) = 0`. -/
structure TradeExecution where
  lam : ℝ
  lam_pos : 0 < lam
  T : ℝ
  T_pos : 0 < T
  C : ℕ → ℝ
  C_zero : C 0 = 0
  C_nonneg : ∀ a, 0 ≤ C a
  C_strictMono : StrictMono C
  C_convex : ∀ x : ℕ, C (x + 1) - C x < C (x + 2) - C (x + 1)

/-- The state space `E = [0,T] × ℕ_0` (p. 294). -/
def TradeExecution.E (M : TradeExecution) : Set (ℝ × ℕ) := Set.Icc 0 M.T ×ˢ Set.univ

/-- `A := {α : [0,T] → ℕ_0 measurable}` **(9.20)**, with the product σ-algebra. -/
structure Offer where
  val : ℝ → ℕ
  meas : Measurable val

instance : MeasurableSpace Offer := MeasurableSpace.comap Offer.val MeasurableSpace.pi

/-- `α ∈ D(x)`: the offer never exceeds the inventory (p. 294). -/
def Offer.Admissible (a : Offer) (x : ℕ) : Prop := ∀ t, a.val t ≤ x

/-- The one-stage cost **(9.21)** `c(t,x,α) := ∫_0^{T-t} λe^{-λs} C(α_s) ds + e^{-λ(T-t)} C(x)`. -/
noncomputable def TradeExecution.c (M : TradeExecution) (a : Offer) (p : ℝ × ℕ) : ℝ :=
  (∫ s in Set.Ioo (0 : ℝ) (M.T - p.1), M.lam * Real.exp (-M.lam * s) * M.C (a.val s))
    + Real.exp (-M.lam * (M.T - p.1)) * M.C p.2

/-- A Markov policy `(f_n)` of the embedded model: measurable `f_n : E → A` with
`f_n(t,x) ∈ D(x)`. -/
def TradeExecution.IsPolicy (f : ℕ → ℝ × ℕ → Offer) : Prop :=
  ∀ n, Measurable (f n) ∧ ∀ p, (f n p).Admissible p.2

/-- `J_{n(f_k)}(t,x)`: the expected cost of the first `n` trading epochs (in `[0,∞]`); the next
epoch is `Exp(λ)`-distributed, the inventory moves to `x - α_s`, and beyond `T` nothing more
accrues (cemetery state). -/
noncomputable def TradeExecution.Jn (M : TradeExecution) :
    ℕ → (ℕ → ℝ × ℕ → Offer) → ℝ × ℕ → ℝ≥0∞
  | 0, _, _ => 0
  | (n + 1), f, p =>
      ENNReal.ofReal (M.c (f 0 p) p) +
        ∫⁻ s in Set.Ioo (0 : ℝ) (M.T - p.1), ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
          M.Jn n (fun k => f (k + 1)) (p.1 + s, p.2 - (f 0 p).val s)

/-- `V_π(t,x) = J_{∞π}(t,x) = Σ_k 𝔼^π_{tx}[c(T_k, X_{T_k}, f_k(T_k, X_{T_k}))]` (p. 294). -/
noncomputable def TradeExecution.Jinfpi (M : TradeExecution) (f : ℕ → ℝ × ℕ → Offer)
    (p : ℝ × ℕ) : ℝ≥0∞ :=
  ⨆ n, M.Jn n f p

/-- `V(t,x) := inf_π V_π(t,x)` over admissible Markov policies (p. 294; the value of the
discrete-time model, which by Theorem 8.3.2 is the value of the trade execution problem). -/
noncomputable def TradeExecution.Jinf (M : TradeExecution) (p : ℝ × ℕ) : ℝ≥0∞ :=
  ⨅ f : ℕ → ℝ × ℕ → Offer, ⨅ (_ : TradeExecution.IsPolicy f), M.Jinfpi f p

/-- The dynamic programming operator (p. 295):
`(𝒯v)(t,x) = ∫_0^{T-t} λe^{-λs} min_{u ∈ {0,…,x}} (C(u) + v(t+s, x-u)) ds + e^{-λ(T-t)} C(x)`. -/
noncomputable def TradeExecution.T_op (M : TradeExecution) (v : ℝ × ℕ → ℝ) (p : ℝ × ℕ) : ℝ :=
  (∫ s in Set.Ioo (0 : ℝ) (M.T - p.1),
      M.lam * Real.exp (-M.lam * s) *
        (Finset.range (p.2 + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
          (fun u => M.C u + v (p.1 + s, p.2 - u)))
    + Real.exp (-M.lam * (M.T - p.1)) * M.C p.2

/-- `f^*(t,x) = argmin_{u ∈ {0,…,x}} (C(u) + v(t, x-u))` **(9.22)**, the smallest minimizer. -/
noncomputable def TradeExecution.fstar (M : TradeExecution) (v : ℝ × ℕ → ℝ) (p : ℝ × ℕ) : ℕ :=
  sInf {u : ℕ | u ≤ p.2 ∧ ∀ u' ≤ p.2, M.C u + v (p.1, p.2 - u) ≤ M.C u' + v (p.1, p.2 - u')}

/-- `IM_cx := {v ∈ IB_b | v(t,x) ≤ C(x), v(t,0) = 0, v convex in x, v continuous and increasing
in t and x}` (p. 295), `b(t,x) = C(x)`. -/
def TradeExecution.IMcx (M : TradeExecution) (v : ℝ × ℕ → ℝ) : Prop :=
  (∃ Cst : ℝ, ∀ p ∈ M.E, |v p| ≤ Cst * M.C p.2) ∧
  (∀ p ∈ M.E, v p ≤ M.C p.2) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) M.T, v (t, 0) = 0) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ x : ℕ,
    v (t, x + 1) - v (t, x) ≤ v (t, x + 2) - v (t, x + 1)) ∧
  (∀ x : ℕ, ContinuousOn (fun t => v (t, x)) (Set.Icc 0 M.T)) ∧
  (∀ x : ℕ, MonotoneOn (fun t => v (t, x)) (Set.Icc (0 : ℝ) M.T)) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) M.T, Monotone (fun x : ℕ => v (t, x)))

/-- `b(t,x) := C(x)` is a bounding function with module `α_b` (Proposition 9.4.1): `|c| ≤ C(x)`
and `∫ b dQ(·|t,x,α) = ∫_0^{T-t} λe^{-λs} C(x - α_s) ds ≤ α_b C(x)` on `D`. -/
def TradeExecution.IsBoundingFunction (M : TradeExecution) (alpha : ℝ) : Prop :=
  (∀ p ∈ M.E, ∀ a : Offer, a.Admissible p.2 → |M.c a p| ≤ M.C p.2) ∧
  ∀ p ∈ M.E, ∀ a : Offer, a.Admissible p.2 →
    (∫ s in Set.Ioo (0 : ℝ) (M.T - p.1),
        M.lam * Real.exp (-M.lam * s) * M.C (p.2 - a.val s)) ≤ alpha * M.C p.2

end MDPFinance.JumpMarkets


