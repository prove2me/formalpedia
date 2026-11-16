-- Prove2me | Definitions.Def_OptHedgeGames_Supplement_Block
-- name    : OptHedgeGames_Supplement_Block
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:20:20.620246+00:00
-- url     : https://prove2.me/theorems/bfa5491d-838a-4f61-818a-bd5197058b98
-- title:
--   The single oscillating block — actions $V$, strategy $p_z$ (46), utilities (47), $g_{\mu,\delta}$ (48) and the recurrence (49)
-- statement:
--   For complex numbers $w=w_1+iw_2$ and $z=z_1+iz_2$ write $\mathrm{Re}(\overline wz)=w_1z_1+w_2z_2$.
--
--   A **single oscillating block** has $n\ge9$ actions: eight **active** actions named by
--   $$
--   V=\{1,-1,i,-i,1+i,-1-i,1-i,-1+i\},
--   $$
--   and $n-8$ distinct **neutral** actions $b_1,\dots,b_{n-8}$. Each action $\tau$ has the complex coordinate $w(\tau)$: its name if it is active, $0$ if it is neutral. The coefficient $c$ is $c(\pm1)=\pm1$, $c(\pm i)=\pm i$, and $0$ on the diagonal and neutral actions.
--
--   1. The strategy with score $z\in\mathbb C$ is
--   $$
--   p_z(\tau)=\frac{\exp(\mathrm{Re}(\overline{w(\tau)}z))}{Z(z)},\qquad Z(z)=\sum_\tau\exp(\mathrm{Re}(\overline{w(\tau)}z)),
--   $$
--   the sum running over all $n$ actions (each neutral action contributes $1$).
--   2. For a payoff coefficient $\mu\in\mathbb C$ and a shift $\delta\in\mathbb C$, both players use the utility table
--   $$
--   U(v,w)=\mathrm{Re}\big(\overline v\,\mu\,c(w)\,e^{-\mathrm{Re}(\overline w\delta)}\big),
--   $$
--   where $v$ is the coordinate of the player's own action and $w$ that of the opponent's.
--   3. The expected complex utility coefficient is $g_{\mu,\delta}(z)=\sum_wp_z(w)\,\mu\,c(w)\,e^{-\mathrm{Re}(\overline w\delta)}$.
--   4. The score and memory follow the recurrence
--   $$
--   z_{t+1}=z_t+\eta[2g_{\mu,\delta}(z_t)-\varrho_t],\qquad \varrho_{t+1}=g_{\mu,\delta}(z_t),\qquad (z_0,\varrho_0)=(0,0),
--   $$
--   whose one-step map on $\mathbb C^2$ is $\Phi_{\mu,\delta}$.
--
--   These are the objects of Theorem 6.2; by Lemma 6.1 of the paper the recurrence is the Optimistic Hedge run of the two-player game with utilities $U$.
--
--   **Formalization Note** The actions are `Fin 8 ⊕ Fin (n - 8)`, which has $n$ elements for $n\ge8$; `vtx` lists $V$ in the order above and `cCoef` is $c$ in the same order. The overbars are complex conjugates; `pair w z` is $\mathrm{Re}(\overline wz)$. The trajectory of the recurrence is `blockTraj`, the $t$-fold iterate of `blockStep` from $(0,0)$.
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), §6.1, Step 1, (46)–(49), pp.25–26

import Mathlib

namespace OptHedgeGames

namespace Supplement

/-- The real pairing `Re(w̄ z) = w₁z₁ + w₂z₂` of complex numbers `w = w₁ + iw₂`, `z = z₁ + iz₂`
(Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), §6.1, after (46), p.25).

**Formalization Note** The bar is a complex conjugate; `pair w z = (conj w * z).re`. -/
def pair (w z : ℂ) : ℝ := w.re * z.re + w.im * z.im

/-- The eight **active actions** `V = {1, −1, i, −i, 1+i, −1−i, 1−i, −1+i}`, listed in the paper's
order (manuscript sha256 383e3793…, §6.1, Step 1, p.25). -/
def vtx : Fin 8 → ℂ :=
  ![1, -1, Complex.I, -Complex.I, 1 + Complex.I, -1 - Complex.I, 1 - Complex.I, -1 + Complex.I]

/-- The **linear coefficient** `c`: `c(1) = 1, c(−1) = −1, c(i) = i, c(−i) = −i` and `c = 0` on the
four diagonal actions (manuscript sha256 383e3793…, §6.1, Step 1, p.25; Figure 5, p.26). It is
indexed like `vtx`. -/
def cCoef : Fin 8 → ℂ :=
  ![1, -1, Complex.I, -Complex.I, 0, 0, 0, 0]

/-- The **actions of one oscillating block** with `n` actions: the eight active actions (`Sum.inl k`,
named `vtx k`) and the `n − 8` distinct neutral actions `b₁, …, b_{n−8}` (`Sum.inr j`)
(manuscript sha256 383e3793…, §6.1, Step 1, p.25).

**Formalization Note** For `n ≥ 9` (the hypothesis of Theorem 6.2) this type has exactly `n`
elements; `n − 8` is natural-number subtraction. -/
abbrev BlockAction (n : ℕ) : Type := Fin 8 ⊕ Fin (n - 8)

/-- The complex **coordinate** `w(τ)` of an action: its name if it is active, `0` if it is neutral
(manuscript sha256 383e3793…, p.25). -/
def BlockAction.coord {n : ℕ} : BlockAction n → ℂ
  | Sum.inl k => vtx k
  | Sum.inr _ => 0

/-- The payoff coefficient `c(w(τ))` of an action: `cCoef` on active actions, `0` on neutral ones
(manuscript sha256 383e3793…, p.25). -/
def BlockAction.c {n : ℕ} : BlockAction n → ℂ
  | Sum.inl k => cCoef k
  | Sum.inr _ => 0

/-- The **normalizer (46)** `Z(z) = Σ_τ exp(Re(w(τ)̄ z))`, a sum over all `n` actions, each neutral
action contributing `exp 0 = 1` (manuscript sha256 383e3793…, (46), p.25). -/
noncomputable def blockZ (n : ℕ) (z : ℂ) : ℝ :=
  ∑ τ : BlockAction n, Real.exp (pair τ.coord z)

/-- The **common strategy (46)** with score `z`, `p_z(τ) = exp(Re(w(τ)̄ z))/Z(z)`
(manuscript sha256 383e3793…, (46), p.25). -/
noncomputable def blockProb (n : ℕ) (z : ℂ) (τ : BlockAction n) : ℝ :=
  Real.exp (pair τ.coord z) / blockZ n z

/-- The **utility table (47)** of an oscillating block with payoff coefficient `µ` and shift `δ`:
`U(v, w) = Re(v̄ µ c(w) e^{−Re(w̄δ)})`, where `v` is the coordinate of the player's own action `τ` and
`w` that of the opponent's action `σ`; both players use it (manuscript sha256 383e3793…, (47),
p.25). The losses are `−U`. -/
noncomputable def blockU {n : ℕ} (μ δ : ℂ) (τ σ : BlockAction n) : ℝ :=
  ((starRingEnd ℂ) τ.coord * μ * σ.c * (Real.exp (-pair σ.coord δ) : ℂ)).re

/-- The **expected complex utility coefficient (48)**,
`g_{µ,δ}(z) = Σ_w p_z(w) µ c(w) e^{−Re(w̄δ)}`, the sum running over all `n` actions
(manuscript sha256 383e3793…, (48), p.25). -/
noncomputable def blockG (n : ℕ) (μ δ : ℂ) (z : ℂ) : ℂ :=
  ∑ σ : BlockAction n, (blockProb n z σ : ℂ) * μ * σ.c * (Real.exp (-pair σ.coord δ) : ℂ)

/-- The **one-step map `Φ_{µ,δ}` of the recurrence (49)** on states `(z, ϱ) ∈ ℂ²`:
`(z, ϱ) ↦ (z + η[2g_{µ,δ}(z) − ϱ], g_{µ,δ}(z))`
(manuscript sha256 383e3793…, (49), p.26). -/
noncomputable def blockStep (n : ℕ) (η : ℝ) (μ δ : ℂ) (s : ℂ × ℂ) : ℂ × ℂ :=
  (s.1 + (η : ℂ) * (2 * blockG n μ δ s.1 - s.2), blockG n μ δ s.1)

/-- The **trajectory of (49) from `(z₀, ϱ₀) = (0, 0)`**: `blockTraj n η μ δ t = (z_t, ϱ_t)`
(manuscript sha256 383e3793…, (49), p.26). -/
noncomputable def blockTraj (n : ℕ) (η : ℝ) (μ δ : ℂ) (t : ℕ) : ℂ × ℂ :=
  (blockStep n η μ δ)^[t] (0, 0)

end Supplement

end OptHedgeGames


