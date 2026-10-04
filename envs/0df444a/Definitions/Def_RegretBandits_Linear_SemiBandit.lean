-- Prove2me | Definitions.Def_RegretBandits_Linear_SemiBandit
-- name    : RegretBandits_Linear_SemiBandit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:51:19.328773+00:00
-- url     : https://prove2.me/theorems/a84d9773-c4aa-416c-b34e-1827f61e701e
-- title:
--   Combinatorial arm sets and the semi-bandit loss estimate (5.5)
-- statement:
--   In **online combinatorial optimization** (Section 5.4), the set of arms is a nonempty set $\mathcal C\subseteq\{0,1\}^d$ such that
--   $$\|v\|_1=\sum_{i=1}^d v(i)=m\qquad\text{for all }v\in\mathcal C,$$
--   for some integer $m$. Losses are vectors $\ell_t\in[0,1]^d$, and playing $v\in\mathcal C$ costs $\ell_t^\top v$. Under **semi-bandit feedback** the player who plays $v_t$ observes only $(\ell_t(1)v_t(1),\dots,\ell_t(d)v_t(d))$.
--
--   OSMD runs on $\mathcal K=\mathrm{Conv}(\mathcal C)$ and plays a random arm $v_t\in\mathcal C$ with $\mathbb E[v_t\mid x_t]=x_t$. Its loss estimate is
--   $$\tilde\ell_t(i)=\frac{\ell_t(i)\,v_t(i)}{x_t(i)},\qquad i=1,\dots,d. \tag{5.5}$$
--   It uses only the observed coordinates, and it is unbiased: $\mathbb E[\tilde\ell_t(i)\mid x_t]=\ell_t(i)$.
--
--   This setting contains the $d$-armed adversarial bandit ($\mathcal C=\{e_1,\dots,e_d\}$, $m=1$), as well as $m$-sets and paths.
--
--   **Formalization Note** $\mathcal C$ is a `Set (Fin d → ℝ)` of $0/1$ vectors. The estimate is evaluated only at points $x_t$ of the open orthant $(0,+\infty)^d$, where $x_t(i)>0$, so Lean's convention $x/0=0$ never applies.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 77, Section 5.4, Eq. (5.5)

import Mathlib

namespace RegretBandits.Linear

/-- The online combinatorial optimization setting (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 77):
the set of arms `C ⊆ {0, 1}^d` is nonempty and every `v ∈ C` has `‖v‖₁ = m`. -/
def IsCombinatorialSet {d : ℕ} (C : Set (Fin d → ℝ)) (m : ℕ) : Prop :=
  C.Nonempty ∧ ∀ v ∈ C, (∀ i, v i = 0 ∨ v i = 1) ∧ ∑ i, v i = (m : ℝ)

/-- The semi-bandit loss estimate (5.5) (p. 77): `ℓ̃_t(i) = ℓ_t(i) v_t(i) / x_t(i)`, computed from
the observed coordinates `ℓ_t(i) v_t(i)`, the played arm `v_t` and the OSMD point `x_t`. It is used
only at points `x_t` of the open orthant `(0, +∞)^d`, where `x_t(i) > 0`. -/
noncomputable def semiBanditEstimate {d : ℕ} (ℓ v x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ℓ i * v i / x i

end RegretBandits.Linear


