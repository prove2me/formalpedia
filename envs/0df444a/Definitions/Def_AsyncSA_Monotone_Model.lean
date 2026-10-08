-- Prove2me | Definitions.Def_AsyncSA_Monotone_Model
-- name    : AsyncSA_Monotone_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:25.902737+00:00
-- url     : https://prove2.me/theorems/cb60d663-83ab-4287-8747-d83f68f9a9f3
-- title:
--   The asynchronous stochastic approximation algorithm of §2: updates (1)–(3), Assumptions 1–4, and the bracketing sequences (16)–(17)
-- statement:
--   This file fixes the objects of Tsitsiklis's analysis of asynchronous stochastic approximation for a monotone mapping.
--
--   **The algorithm.** Let $F:\mathbb R^n\to\mathbb R^n$ with components $F_1,\dots,F_n$. A vector $x(t)\in\mathbb R^n$ is updated at discrete times $t=0,1,2,\dots$ by
--   $$
--   x_i(t+1)=x_i(t)+\alpha_i(t)\bigl(F_i(x^i(t))-x_i(t)+w_i(t)\bigr),\qquad x^i(t)=\bigl(x_1(\tau^i_1(t)),\dots,x_n(\tau^i_n(t))\bigr),
--   $$
--   where $\alpha_i(t)\in[0,1]$ is a stepsize, $w_i(t)$ is a noise term, and $0\le\tau^i_j(t)\le t$ are possibly outdated time indices. All of $x(t),\alpha_i(t),w_i(t),\tau^i_j(t)$ are random variables on a probability space $(\Omega,\mathcal F,P)$, and $\{\mathcal F(t)\}$ is an increasing sequence of sub-σ-fields of $\mathcal F$.
--
--   **Generalized conditional expectations.** For a sub-σ-field $\mathcal G$, "$E[f\mid\mathcal G]=0$" means $\int_S f\,dP=0$ for every $S\in\mathcal G$ on which $f$ is integrable, and "$E[f^2\mid\mathcal G]\le g$" means $\int_S f^2\,dP\le\int_S g^+\,dP$ (in $[0,\infty]$) for every $S\in\mathcal G$.
--
--   **Assumptions.** Write $M(t)=\max_{\tau\le t}\max_j|x_j(\tau)|$ and let $e$ be the vector of ones.
--
--   1. *Assumption 1*: for all $i,j$, $\tau^i_j(t)\to\infty$ as $t\to\infty$, with probability 1.
--   2. *Assumption 2*: $x(0)$ is $\mathcal F(0)$-measurable; $w_i(t)$ is $\mathcal F(t+1)$-measurable; $\alpha_i(t)$ and $\tau^i_j(t)$ are $\mathcal F(t)$-measurable; $E[w_i(t)\mid\mathcal F(t)]=0$; and there are deterministic constants $A,B$ with $E[w_i^2(t)\mid\mathcal F(t)]\le A+B\,M(t)^2$ for all $i,t$.
--   3. *Assumption 3*: for every $i$, $\sum_{t=0}^\infty\alpha_i(t)=\infty$ w.p.1, and there is a deterministic $C$ with $\sum_{t=0}^\infty\alpha_i^2(t)\le C$ w.p.1.
--   4. *Assumption 4* (for a given $x^*$): $F$ is monotone ($x\le y\Rightarrow F(x)\le F(y)$, componentwise), continuous, $x^*$ is its unique fixed point, and for every $x\in\mathbb R^n$ and every $r>0$
--   $$
--   F(x)-re\le F(x-re)\le F(x+re)\le F(x)+re .
--   $$
--
--   The file also records that $x(t)$ is $\mathcal F(t)$-measurable ("adapted"), and defines
--
--   - $W(t;t_0)$ of (20): $W(t_0;t_0)=0$, $W(t+1;t_0)=(1-\alpha(t))W(t;t_0)+\alpha(t)w(t)$ for $t\ge t_0$, for scalar sequences $\alpha,w$;
--   - the sequences of (16)–(17): $U^0=x^*+re$, $L^0=x^*-re$, $U^{k+1}=(U^k+F(U^k))/2$, $L^{k+1}=(L^k+F(L^k))/2$.
--
--   These objects are the vocabulary of Theorem 2 and of Lemmas 1, 4–7.
--
--   **Formalization Note** Components are indexed by `Fin n` (0-based; the paper uses $1,\dots,n$). The update is stated in the paper's unified form, valid for every $t$, with $\alpha_i(t)=0$ when $x_i$ is not updated; the update sets $T^i$ are therefore not represented (they are infinite as a consequence of Assumption 3(a) and $\alpha_i\le1$). The paper also sets $\tau^i_j(t)=t$ off $T^i$; here $\tau^i_j(t)$ is left free there, which is more general because it does not influence $x(t+1)$ when $\alpha_i(t)=0$. $\alpha_i(t)\in[0,1]$ and $\tau^i_j(t)\le t$ hold on every sample path. The conditional expectations are the generalized ones above, not Mathlib's `condExp` (which is $0$ for non-integrable functions and would make Assumption 2(d) vacuous); `ENNReal.ofReal` clips a negative right-hand side of 2(e) to $0$, which only matters where the paper's inequality is unsatisfiable anyway. Infinite series are expressed by partial sums (divergence to $+\infty$; every partial sum $\le C$), never by `tsum`. The constants $A,B$ (`cA`, `cB`) and $C$ are chosen before the almost-sure quantifier, as the paper's "deterministic" requires. $r e$ is `r • 1`; vector inequalities are the componentwise (Pi) order. $W(t;t_0)$ is $0$ for $t\le t_0$. Assumptions 5 and 6 and the weighted norm (6) are not used by this mission and are omitted.
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), pp. 187–189, §2 (eqs. (1)–(3), (7), Assumptions 1–4); p. 193, §5, (16)–(17); p. 194, (20)

import Mathlib

namespace AsyncSA.Monotone

open MeasureTheory Filter Topology

/-- `E[f | m] = 0` in the generalized sense of conditional expectation, without assuming `f`
integrable: `∫_S f dP = 0` for every `m`-measurable set `S` on which `f` is integrable. -/
def CondMeanZero {Ω : Type*} [m0 : MeasurableSpace Ω] (m : MeasurableSpace Ω)
    (P : @Measure Ω m0) (f : Ω → ℝ) : Prop :=
  ∀ S, MeasurableSet[m] S → ∫⁻ ω in S, ‖f ω‖ₑ ∂P < ⊤ → ∫ ω in S, f ω ∂P = 0

/-- `E[f² | m] ≤ g`: `∫_S f² dP ≤ ∫_S g dP` (as `[0, ∞]`-valued integrals) for every
`m`-measurable set `S`. -/
def CondSqLe {Ω : Type*} [m0 : MeasurableSpace Ω] (m : MeasurableSpace Ω)
    (P : @Measure Ω m0) (f g : Ω → ℝ) : Prop :=
  ∀ S, MeasurableSet[m] S →
    ∫⁻ ω in S, ENNReal.ofReal (f ω ^ 2) ∂P ≤ ∫⁻ ω in S, ENNReal.ofReal (g ω) ∂P

/-- §2: the asynchronous stochastic approximation algorithm, in the unified form of (1)–(3)
(`α i t = 0` off `T^i`). `τ i j t ω` is `τ^i_j(t)`. -/
structure Algorithm (n : ℕ) (Ω : Type*) where
  F : (Fin n → ℝ) → Fin n → ℝ
  x : ℕ → Ω → Fin n → ℝ
  α : Fin n → ℕ → Ω → ℝ
  w : Fin n → ℕ → Ω → ℝ
  τ : Fin n → Fin n → ℕ → Ω → ℕ
  α_mem : ∀ i t ω, α i t ω ∈ Set.Icc (0 : ℝ) 1
  τ_le : ∀ i j t ω, τ i j t ω ≤ t
  update : ∀ i t ω, x (t + 1) ω i =
    x t ω i + α i t ω * (F (fun j => x (τ i j t ω) ω j) i - x t ω i + w i t ω)

namespace Algorithm

variable {n : ℕ} {Ω : Type*} (A : Algorithm n Ω)

/-- `x^i(t)` of (3): the vector of possibly outdated components used by the update of `x_i`. -/
def xi (i : Fin n) (t : ℕ) (ω : Ω) : Fin n → ℝ := fun j => A.x (A.τ i j t ω) ω j

/-- `M(t) = max_{τ ≤ t} ‖x(τ)‖_∞`, the quantity in Assumption 2(e). -/
noncomputable def runMax (t : ℕ) (ω : Ω) : ℝ :=
  ⨆ s : Fin (t + 1), ⨆ j : Fin n, |A.x s ω j|

variable [m0 : MeasurableSpace Ω]

/-- Assumption 1: `τ^i_j(t) → ∞` with probability 1, for every `i, j`. -/
def Assumption1 (P : Measure Ω) : Prop :=
  ∀ i j, ∀ᵐ ω ∂P, Tendsto (fun t => A.τ i j t ω) atTop atTop

/-- Assumption 2: measurability with respect to the filtration, conditional mean zero noise and
the conditional variance bound `E[w_i(t)² | ℱ(t)] ≤ A + B max_j max_{τ ≤ t} |x_j(τ)|²` with
deterministic constants `A = cA`, `B = cB`. -/
structure Assumption2 (P : Measure Ω) (𝓕 : Filtration ℕ m0) : Prop where
  x0_meas : ∀ j, Measurable[𝓕 0] fun ω => A.x 0 ω j
  w_meas : ∀ i t, Measurable[𝓕 (t + 1)] (A.w i t)
  α_meas : ∀ i t, Measurable[𝓕 t] (A.α i t)
  τ_meas : ∀ i j t, Measurable[𝓕 t] (A.τ i j t)
  mean_zero : ∀ i t, CondMeanZero (𝓕 t) P (A.w i t)
  var_bound : ∃ cA cB : ℝ, ∀ i t,
    CondSqLe (𝓕 t) P (A.w i t) fun ω => cA + cB * A.runMax t ω ^ 2

/-- `x(t)` is `ℱ(t)`-measurable for every `t` (used implicitly by the paper). -/
def Adapted (𝓕 : Filtration ℕ m0) : Prop :=
  ∀ t j, Measurable[𝓕 t] fun ω => A.x t ω j

/-- Assumption 3: `Σ_t α_i(t) = ∞` w.p.1 (partial sums tend to `+∞`), and a deterministic `C`
with `Σ_t α_i(t)² ≤ C` w.p.1 (every partial sum is at most `C`). -/
structure Assumption3 (P : Measure Ω) : Prop where
  sum_inf : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun T => ∑ t ∈ Finset.range T, A.α i t ω) atTop atTop
  sum_sq : ∃ C : ℝ, ∀ i, ∀ᵐ ω ∂P, ∀ T, ∑ t ∈ Finset.range T, A.α i t ω ^ 2 ≤ C

end Algorithm

variable {n : ℕ}

/-- Assumption 4, with `xstar` the unique fixed point of 4(c). Vector inequalities are
componentwise; `r • 1` is `r e`. -/
structure Assumption4 (F : (Fin n → ℝ) → Fin n → ℝ) (xstar : Fin n → ℝ) : Prop where
  mono : Monotone F
  cont : Continuous F
  fixed : F xstar = xstar
  unique : ∀ y, F y = y → y = xstar
  shift : ∀ x : Fin n → ℝ, ∀ r : ℝ, 0 < r →
    F x - r • (1 : Fin n → ℝ) ≤ F (x - r • (1 : Fin n → ℝ)) ∧
    F (x - r • (1 : Fin n → ℝ)) ≤ F (x + r • (1 : Fin n → ℝ)) ∧
    F (x + r • (1 : Fin n → ℝ)) ≤ F x + r • (1 : Fin n → ℝ)

/-- `W(t; t0)` of (20): `W(t0; t0) = 0` and `W(t+1; t0) = (1 − α(t)) W(t; t0) + α(t) w(t)` for
`t ≥ t0` (and `0` for `t ≤ t0`). For `t0 = 0` this is the `W_i(t)` of §5 with `W_i(0) = 0`. -/
noncomputable def tailW (α w : ℕ → ℝ) (t0 : ℕ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => if t0 ≤ t then (1 - α t) * tailW α w t0 t + α t * w t else 0

/-- (16): `U^0 = x* + r e`, `U^{k+1} = (U^k + F(U^k)) / 2`. -/
noncomputable def Useq (F : (Fin n → ℝ) → Fin n → ℝ) (xstar : Fin n → ℝ) (r : ℝ) : ℕ → Fin n → ℝ
  | 0 => xstar + r • (1 : Fin n → ℝ)
  | k + 1 => (1 / 2 : ℝ) • (Useq F xstar r k + F (Useq F xstar r k))

/-- (17): `L^0 = x* − r e`, `L^{k+1} = (L^k + F(L^k)) / 2`. -/
noncomputable def Lseq (F : (Fin n → ℝ) → Fin n → ℝ) (xstar : Fin n → ℝ) (r : ℝ) : ℕ → Fin n → ℝ
  | 0 => xstar - r • (1 : Fin n → ℝ)
  | k + 1 => (1 / 2 : ℝ) • (Lseq F xstar r k + F (Lseq F xstar r k))

end AsyncSA.Monotone


