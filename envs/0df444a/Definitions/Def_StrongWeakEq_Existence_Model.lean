-- Prove2me | Definitions.Def_StrongWeakEq_Existence_Model
-- name    : StrongWeakEq_Existence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:37:48.477696+00:00
-- url     : https://prove2.me/theorems/d2090160-18c1-4d42-8988-25f47e566232
-- title:
--   §2, pp. 4–6, (2.1)–(2.4), (2.7), (2.8), (3.1), (3.7) — generator rows, controls, standing assumptions, payoff F, concatenation, Γ, weak and strong equilibria
-- statement:
--   A continuous-time Markov chain $X$ on the finite state space $S=\{1,\dots,N\}$ is controlled through its generator $Q\in\mathbb R^{N\times N}$, whose $i$-th row is written $Q_i$.
--
--   1. **Generator rows** (2.1). $E_i=\{q\in\mathbb R^N : q_j\ge 0 \text{ for } j\ne i,\ q_i=-\sum_{j\ne i}q_j\}$ is the set of possible $i$-th rows of a generator. An admissible set $D_i\subseteq E_i$ is given for each $i$.
--   2. **Controls.** $\mathcal Q=\{Q\in\mathbb R^{N\times N}: Q_i\in D_i\ \forall i\in S\}$.
--   3. **Standing assumptions of §2.** A payoff rate $f(t,i,q)$ (with $t\ge 0$ the time difference to the payment, $i$ the current state, $q$ the current row) satisfies
--      (2.2) $t\mapsto f(t,i,q)$ is continuous on $[0,\infty)$ for every $i$ and $q\in D_i$; and
--      (2.3) for every $c>0$,
--   $$\int_0^\infty \Big(\sup_{i\in S,\ q\in D_i,\ \|q\|\le c}|f(t,i,q)|\Big)\,dt<\infty .$$
--   4. **Expected payoff** (2.4) and the **shifted payoff** (3.1):
--   $$F(i,Q)=\mathbb E_{i,Q}\Big[\int_0^\infty f(t,X_t,Q_{X_t})\,dt\Big],\qquad F_\varepsilon(i,Q)=\mathbb E_{i,Q}\Big[\int_0^\infty f(t+\varepsilon,X_t,Q_{X_t})\,dt\Big],$$
--      with $F(Q)=(F(1,Q),\dots,F(N,Q))$.
--   5. **Concatenation** (p. 5). For $\varepsilon>0$, $Q\otimes_\varepsilon Q'$ lets $Q$ govern $X$ on $[0,\varepsilon]$ and $Q'$ on $(\varepsilon,\infty)$; $F(i,Q\otimes_\varepsilon Q')$ is the payoff (2.4) under it, where the row in force at time $t$ is $Q_{X_t}$ for $t\le\varepsilon$ and $Q'_{X_t}$ afterwards.
--   6. **The first-order gain** (3.7): $\Gamma^{Q^*}(q)=f(0,i,q)+q\cdot F(Q^*)$ for a candidate $i$-th row $q$.
--   7. **Weak equilibrium** (Definition 2.1): $Q^*\in\mathcal Q$ with
--   $$\liminf_{\varepsilon\downarrow 0}\frac{F(i,Q^*)-F(i,Q\otimes_\varepsilon Q^*)}{\varepsilon}\ge 0\qquad\forall Q\in\mathcal Q,\ i\in S. \tag{2.7}$$
--   8. **Strong equilibrium** (Definition 2.2): $Q^*\in\mathcal Q$ such that for every $i\in S$ and $Q\in\mathcal Q$ there is $\varepsilon>0$ with $F(i,Q^*)\ge F(i,Q\otimes_{\varepsilon'}Q^*)$ for all $0<\varepsilon'\le\varepsilon$ (2.8).
--
--   These are the objects of every statement in the mission. Because $t$ in $f(t,i,q)$ is a time difference, an optimal $Q$ for one initial state need not stay optimal later, and the equilibrium notions replace optimality.
--
--   **Formalization Note** State $k$ of the paper is the index $k-1$ of `Fin N`. The expectation $\mathbb E_{i,Q}$ over the chain is written out through its one-dimensional marginals: under a generator $Q$ the law of $X_t$ given $X_0=i$ is the $i$-th row of the matrix exponential $e^{tQ}$, so $\mathbb E_{i,Q}[\int_0^\infty \varphi(t,X_t)\,dt]=\int_0^\infty\sum_j (e^{tQ})_{ij}\varphi(t,j)\,dt$ by Fubini; no Markov process is constructed. Under $Q\otimes_\varepsilon Q'$ the transition matrix from $0$ to $t$ is $e^{tQ}$ for $t\le\varepsilon$ and $e^{\varepsilon Q}e^{(t-\varepsilon)Q'}$ for $t>\varepsilon$. The integrals are Bochner integrals over $(0,\infty)$. The norm in (2.3) is the sup norm of $\mathbb R^N$ (the paper uses the Euclidean norm; the two conditions are equivalent because (2.3) quantifies over every $c>0$), and the integrability of the supremum is stated as the existence of an integrable majorant $g$ of $|f(t,i,q)|$ on $[0,\infty)$. The liminf in (2.7) is encoded without a real-valued liminf: for every $\eta>0$, the quotient is eventually $\ge-\eta$ as $\varepsilon\downarrow 0$, which is exactly $\liminf\ge 0$ in the extended reals. $\Gamma$ takes the state $i$ explicitly because $f(0,i,\cdot)$ depends on it; the paper writes $\Gamma^{Q^*}(Q_i)$. Membership $Q^*\in\mathcal Q$ is part of both equilibrium notions.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, pp. 4–6, (2.1)–(2.4), Definitions 2.1–2.2 (2.7)–(2.8), (3.1), (3.7)

import Mathlib

namespace StrongWeakEq.Existence

open MeasureTheory Filter Topology

/-- (2.1), p. 4: the set `Eᵢ` of possible `i`-th rows of a generator,
`q_j ≥ 0` for `j ≠ i` and `qᵢ = −∑_{j≠i} q_j`. -/
def GenRow {N : ℕ} (i : Fin N) : Set (Fin N → ℝ) :=
  {q | (∀ j, j ≠ i → 0 ≤ q j) ∧ q i = -∑ j ∈ Finset.univ.erase i, q j}

/-- p. 4: the control space `𝒬 = {Q ∈ ℝ^{N×N} : Qᵢ ∈ Dᵢ ∀ i}`. -/
def Controls {N : ℕ} (D : Fin N → Set (Fin N → ℝ)) : Set (Matrix (Fin N) (Fin N) ℝ) :=
  {Q | ∀ i, Q i ∈ D i}

/-- The standing assumptions of §2 (p. 4): `Dᵢ ⊆ Eᵢ` (2.1); (2.2) `t ↦ f(t,i,q)` is continuous on
`[0,∞)` for `q ∈ Dᵢ`; (2.3) for every `c > 0`, `t ↦ sup_{i, q ∈ Dᵢ, ‖q‖ ≤ c} |f(t,i,q)|` has an
integrable majorant on `[0,∞)`. -/
structure Standing {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) : Prop where
  rows : ∀ i, D i ⊆ GenRow i
  cont : ∀ i, ∀ q ∈ D i, ContinuousOn (fun t => f t i q) (Set.Ici 0)
  integ : ∀ c : ℝ, 0 < c → ∃ g : ℝ → ℝ, IntegrableOn g (Set.Ici 0) ∧
    ∀ t, 0 ≤ t → ∀ i, ∀ q ∈ D i, ‖q‖ ≤ c → |f t i q| ≤ g t

/-- (2.4), p. 4: `F(i,Q) = E_{i,Q}[∫₀^∞ f(t, X_t, Q_{X_t}) dt] = ∫₀^∞ ∑ⱼ (e^{tQ})ᵢⱼ f(t, j, Qⱼ) dt`. -/
noncomputable def payoff {N : ℕ} (f : ℝ → Fin N → (Fin N → ℝ) → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), ∑ j, NormedSpace.exp (t • Q) i j * f t j (Q j)

/-- (3.1), p. 6: `F_ε(i,Q) = E_i[∫₀^∞ f(t+ε, X_t, Q_{X_t}) dt]`. -/
noncomputable def shiftedPayoff {N : ℕ} (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (ε : ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), ∑ j, NormedSpace.exp (t • Q) i j * f (t + ε) j (Q j)

/-- p. 5: the transition matrix from time `0` to time `t` under `Q ⊗_ε Q'` (`Q` on `[0,ε]`, `Q'` on
`(ε,∞)`). -/
noncomputable def concatTrans {N : ℕ} (ε : ℝ) (Q Q' : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  if t ≤ ε then NormedSpace.exp (t • Q)
  else NormedSpace.exp (ε • Q) * NormedSpace.exp ((t - ε) • Q')

/-- p. 5: `F(i, Q ⊗_ε Q')`, the expected payoff (2.4) under the concatenated generator. -/
noncomputable def concatPayoff {N : ℕ} (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (ε : ℝ)
    (Q Q' : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), ∑ j, concatTrans ε Q Q' t i j * f t j (if t ≤ ε then Q j else Q' j)

/-- (3.7), p. 6: `Γ^{Q*}(q) = f(0,i,q) + q · F(Q*)` for a candidate `i`-th row `q`. -/
noncomputable def Gamma {N : ℕ} (f : ℝ → Fin N → (Fin N → ℝ) → ℝ)
    (Qs : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) (q : Fin N → ℝ) : ℝ :=
  f 0 i q + q ⬝ᵥ (fun j => payoff f Qs j)

/-- Definition 2.1, p. 5: `Q*` is a weak equilibrium, (2.7):
`liminf_{ε↓0} (F(i,Q*) − F(i, Q ⊗_ε Q*))/ε ≥ 0` for all `Q ∈ 𝒬`, `i ∈ S`. -/
def IsWeakEquilibrium {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (Qs : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  Qs ∈ Controls D ∧ ∀ Q ∈ Controls D, ∀ i, ∀ η : ℝ, 0 < η →
    ∀ᶠ ε in 𝓝[>] (0:ℝ), -η ≤ (payoff f Qs i - concatPayoff f ε Q Qs i) / ε

/-- Definition 2.2, p. 5: `Q*` is a strong equilibrium, (2.8): for all `i`, `Q` there is `ε > 0` with
`F(i,Q*) ≥ F(i, Q ⊗_{ε'} Q*)` for all `0 < ε' ≤ ε`. -/
def IsStrongEquilibrium {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (Qs : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  Qs ∈ Controls D ∧ ∀ Q ∈ Controls D, ∀ i, ∃ ε : ℝ, 0 < ε ∧
    ∀ ε' ∈ Set.Ioc (0:ℝ) ε, concatPayoff f ε' Q Qs i ≤ payoff f Qs i

end StrongWeakEq.Existence


