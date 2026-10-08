-- Prove2me | Definitions.Def_KellyReversibility_Reversibility_MarkovProcess
-- name    : KellyReversibility_Reversibility_MarkovProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:21:27.001642+00:00
-- url     : https://prove2.me/theorems/a4137953-83d4-48e3-83ce-7b082859c7de
-- title:
--   Finite-state Markov processes: generator, $P(t)=e^{tQ}$, equilibrium, reversibility and the constructions of Chapter 1
-- statement:
--   Let $\mathcal S$ be a finite state space and $q(j,k)\ge 0$, $j\ne k$, the transition rates of a continuous-time Markov process $X(t)$, $t\in\mathbb R$; Kelly's convention is $q(j,j)=0$ (p. 3). Write $q(j)=\sum_{k}q(j,k)$.
--
--   1. The **generator** is $Q(j,k)=q(j,k)$ for $j\ne k$ and $Q(j,j)=-\sum_{k\ne j}q(j,k)$; the **transition matrices** are $P(t)=e^{tQ}$.
--   2. The rates are **irreducible** if every state can be reached from every other state through transitions of positive rate.
--   3. An **equilibrium distribution** (p. 3) is a collection of positive numbers $\pi(j)$ summing to unity that satisfy the equilibrium equations
--   $$\pi(j)\sum_{k}q(j,k)=\sum_k\pi(k)q(k,j),\qquad j\in\mathcal S. \tag{1.3}$$
--   4. The stationary process with rates $q$ and equilibrium distribution $\pi$ has finite-dimensional distributions $\pi(j_1)\prod_r P(t_{r+1}-t_r)(j_r,j_{r+1})$ for $t_1\le\dots\le t_n$; it is **reversible** if these are invariant under $t_r\mapsto\tau-t_r$ (p. 5), and **dynamically reversible** with respect to a conjugation $j\mapsto j^+$ (p. 31) if $X(t)$ is statistically indistinguishable from $[X(\tau-t)]^+$:
--   $$P\bigl(X(t_r)=j_r,\ r=1,\dots,n\bigr)=P\bigl(X(\tau-t_r)=j_r^+,\ r=1,\dots,n\bigr).$$
--   5. The **graph $G$** of the process (p. 8) has vertex set $\mathcal S$ and an edge between distinct $j,k$ whenever $q(j,k)>0$ or $q(k,j)>0$.
--   6. For $\mathcal A\subseteq\mathcal S$ and $c>0$, the **altered rates** of Lemma 1.9 replace $q(j,k)$ by $cq(j,k)$ for $j\in\mathcal A$, $k\notin\mathcal A$, and the **altered distribution** is $B\pi(j)$ on $\mathcal A$ and $Bc\pi(j)$ off $\mathcal A$, where $B^{-1}=\sum_{j\in\mathcal A}\pi(j)+c\sum_{j\notin\mathcal A}\pi(j)$.
--   7. For an initial distribution $u(0)$, $u(t)=u(0)P(t)$ is the solution of the forward equations (1.16), and $H(t)=\sum_j\pi(j)\,h\bigl(u_j(t)/\pi(j)\bigr)$ (p. 18).
--
--   **Formalization Note** The state space is finite, a restriction of Kelly's countable state space; on a finite space the process cannot explode and its law is determined by $\pi$ and $e^{tQ}$ (Mathlib's `NormedSpace.exp`). The generator is $\operatorname{of}(q)-\operatorname{diag}(q(j))$, whose diagonal is $-\sum_{k\ne j}q(j,k)$ whatever $q(j,j)$ is. The equilibrium equations reuse `FullBalance` of the published file `KellyStochasticNetworks_Balance` (an unconditional sum, which is the finite sum here). Reversibility is the distributional definition, not detailed balance.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 1–3, Eq. (1.3); p. 5; p. 8 (graph G); p. 25 (Lemma 1.9); p. 18, Eq. (1.16); p. 31 (dynamic reversibility)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw

namespace KellyReversibility.Reversibility

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The generator matrix `Q` of a Markov process on a finite state space with transition
rates `q`: `Q(j, k) = q(j, k)` for `j ≠ k` and `Q(j, j) = -∑_{k ≠ j} q(j, k)`. -/
def generator (q : S → S → ℝ) : Matrix S S ℝ :=
  Matrix.of q - Matrix.diagonal (fun j => ∑ k, q j k)

/-- The transition matrix `P(t) = exp(t Q)`, `P(t)(j, k) = P(X(s + t) = k | X(s) = j)`. -/
noncomputable def transition (q : S → S → ℝ) (t : ℝ) : Matrix S S ℝ :=
  NormedSpace.exp (t • generator q)

/-- The rates `q` are **irreducible**: every state can be reached from every other state
through a chain of transitions with positive rates (Kelly, p. 1). -/
def RatesIrreducible {T : Type*} (q : T → T → ℝ) : Prop :=
  ∀ j k : T, Relation.ReflTransGen (fun a b => 0 < q a b) j k

/-- `π` is an **equilibrium distribution** for the rates `q` (Kelly, p. 3): positive numbers
summing to one that satisfy the equilibrium equations (1.3),
`π(j) ∑_k q(j, k) = ∑_k π(k) q(k, j)`. -/
def IsEquilibrium {T : Type*} [Fintype T] (π : T → ℝ) (q : T → T → ℝ) : Prop :=
  (∀ j, 0 < π j) ∧ ∑ j, π j = 1 ∧ KellyStochasticNetworks.FullBalance π q

/-- The stationary Markov process (time set `ℝ`) with transition rates `q` and equilibrium
distribution `π` is **reversible** (Kelly, p. 5). -/
def ProcessReversible (q : S → S → ℝ) (π : S → ℝ) : Prop :=
  IsReversibleLaw (transition q) π

/-- The stationary Markov process with rates `q` and equilibrium distribution `π` is
**dynamically reversible** with respect to the conjugation `j ↦ conj j` (Kelly, p. 31):
`X(t)` is statistically indistinguishable from `[X(τ - t)]⁺`, i.e.
`P(X(t_r) = j_r ∀ r) = P(X(τ - t_r) = (j_r)⁺ ∀ r)`. -/
def DynamicallyReversible (q : S → S → ℝ) (π : S → ℝ) (conj : S → S) : Prop :=
  ∀ (n : ℕ) (t : Fin (n + 1) → ℝ) (j : Fin (n + 1) → S) (τ : ℝ),
    fdd (transition q) π t j = fdd (transition q) π (fun r => τ - t r) (conj ∘ j)

/-- The graph `G` associated with a Markov process (Kelly, p. 8): vertices are the states,
and distinct `j, k` are joined by an edge if `q(j, k) > 0` or `q(k, j) > 0`. -/
def rateGraph (q : S → S → ℝ) : SimpleGraph S where
  Adj j k := j ≠ k ∧ (0 < q j k ∨ 0 < q k j)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The rates of Lemma 1.9: `q(j, k)` is changed to `c q(j, k)` for `j ∈ A`, `k ∉ A`. -/
def alteredRates (q : S → S → ℝ) (A : Finset S) (c : ℝ) : S → S → ℝ :=
  fun j k => if j ∈ A ∧ k ∉ A then c * q j k else q j k

/-- The distribution of Lemma 1.9: `B π(j)` for `j ∈ A` and `B c π(j)` for `j ∉ A`, with
`B⁻¹ = ∑_{j ∈ A} π(j) + c ∑_{j ∉ A} π(j)`. -/
noncomputable def alteredEquilibrium (π : S → ℝ) (A : Finset S) (c : ℝ) : S → ℝ :=
  fun j => (∑ i ∈ A, π i + c * ∑ i ∈ Aᶜ, π i)⁻¹ * (if j ∈ A then π j else c * π j)

/-- The distribution at time `t` of the process started with distribution `u₀` at time `0`:
`u(t) = u₀ P(t)`, the solution of the forward equations (1.16) with `u(0) = u₀`. -/
noncomputable def distAt (q : S → S → ℝ) (u₀ : S → ℝ) (t : ℝ) : S → ℝ :=
  Matrix.vecMul u₀ (transition q t)

/-- The function `H(t) = ∑_j π(j) h(u_j(t) / π(j))` of §1.4 (Kelly, p. 18). -/
noncomputable def entropyH (q : S → S → ℝ) (π : S → ℝ) (h : ℝ → ℝ) (u₀ : S → ℝ)
    (t : ℝ) : ℝ :=
  ∑ j, π j * h (distAt q u₀ t j / π j)

end KellyReversibility.Reversibility


