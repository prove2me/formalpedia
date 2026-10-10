-- Prove2me | Definitions.Def_NondomArb_Superhedge_General
-- name    : NondomArb_Superhedge_General
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:22:24.623659+00:00
-- url     : https://prove2.me/theorems/30a2afa7-c70f-4000-8d2d-662626b0e4d2
-- title:
--   §2: general filtered market — predictable strategies, wealth H • S_T, NA(𝒫), the cone 𝒞, π(f); local martingales (Appendix)
-- statement:
--   This is the general setting of §2 of Bouchard–Nutz, together with the discrete-time martingale notions of the Appendix.
--
--   Let $(\Omega,\mathcal F)$ be a measurable space with a filtration $(\mathcal F_t)_{t=0,\dots,T}$, let $\mathcal P$ be a nonempty family of probability measures on $\mathcal F$, and let $S=(S_0,\dots,S_T)$ be $\mathcal F$-measurable $\mathbb R^d$-valued random variables (not necessarily adapted).
--
--   1. A *trading strategy* $H=(H_1,\dots,H_T)$ is predictable: $H_u$ is $\mathcal F_{u-1}$-measurable. Its terminal wealth from zero initial capital is
--   $$H\bullet S_T=\sum_{u=1}^T H_u\,\Delta S_u,\qquad \Delta S_u=S_u-S_{u-1}.$$
--   2. **NA($\mathcal P$)**: $H\bullet S_T\ge 0$ $\mathcal P$-q.s. implies $H\bullet S_T=0$ $\mathcal P$-q.s.
--   3. **The cone** $\mathcal C=\{H\bullet S_T: H \text{ predictable}\}-\mathcal L^0_+$; a random variable $W$ belongs to $\mathcal C$ if $W=H\bullet S_T-K$ $\mathcal P$-q.s. for some predictable $H$ and some nonnegative random variable $K$.
--   4. **The superhedging price** of a random variable $f$:
--   $$\pi(f)=\inf\{x\in\mathbb R:\ \exists H,\ x+H\bullet S_T\ge f\ \ \mathcal P\text{-q.s.}\}\in[-\infty,\infty],\qquad \inf\emptyset=+\infty .$$
--   5. **Martingales** (Appendix): for a probability $Q$, an adapted $\mathbb R^d$-valued process $X$ is a $Q$-martingale on $\{0,\dots,T\}$ if each $X_t$ is $Q$-integrable and $E_Q[X_{t+1}\mid\mathcal F_t]=X_t$ $Q$-a.s.; it is a *local* $Q$-martingale if there are stopping times $\tau_n\uparrow\infty$ $Q$-a.s. such that every stopped process $X^{\tau_n}=(X_{t\wedge\tau_n})_t$ is a $Q$-martingale.
--
--   This setting is the one in which the paper proves closedness of $\mathcal C$ (Theorem 2.2) and existence of optimal superhedging strategies (Theorem 2.3); the martingale notions are those of Lemma A.2.
--
--   **Formalization Note** Lean's `H u` is the paper's $H_{u+1}$ and must be $\mathcal F_u$-measurable, $u=0,\dots,T-1$. Membership in $\mathcal C$ is read up to $\mathcal P$-polar sets, as the paper uses it in the proof of Theorem 2.3. The price is an infimum in `EReal`. Stopping times are $\mathbb N$-valued with $\{\tau\le t\}\in\mathcal F_t$; martingale conditions are stated componentwise with Mathlib's conditional expectation.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, pp. 9–10, §2 (setting, Theorem 2.2, Theorem 2.3), (1.2); p. 35, Appendix

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic

namespace NondomArb.Superhedge.General

open MeasureTheory

/-! §2 (pp. 9–10): a general measurable space `(Ω, F)` with filtration `(F_t)_{t = 0,…,T}`, a
nonempty set `𝒫` of probability measures, an `ℝ^d`-valued, not necessarily adapted process
`S = (S_0, …, S_T)`, predictable strategies, no options (`e = 0`).

Index convention: `H u` (for `u = 0, …, T − 1`) is the paper's `H_{u+1}`, the position held over
`(u, u+1]`; it must be `F_u`-measurable (predictability). -/

/-- The trading strategy `H` is *predictable*: the paper's `H_{u+1}` (Lean's `H u`) is
`F_u`-measurable for `u = 0, …, T − 1`. -/
def IsPredictable {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m) (T : ℕ) {d : ℕ}
    (H : ℕ → Ω → (Fin d → ℝ)) : Prop :=
  ∀ u < T, Measurable[ℱ u] (H u)

/-- **(1.2)** The terminal wealth `H • S_T = Σ_{u=1}^T H_u ΔS_u` (Lean index `u = 0, …, T−1`). -/
def wealth {Ω : Type*} (T : ℕ) {d : ℕ} (S H : ℕ → Ω → (Fin d → ℝ)) (ω : Ω) : ℝ :=
  ∑ u ∈ Finset.range T, H u ω ⬝ᵥ (S (u + 1) ω - S u ω)

/-- **NA(𝒫)** (Definition 1.1 with `e = 0`, as restated on p. 10): for every predictable `H`,
`H • S_T ≥ 0` `𝒫`-q.s. implies `H • S_T = 0` `𝒫`-q.s. -/
def NA {Ω : Type*} {m : MeasurableSpace Ω} (Pset : Set (Measure Ω)) (ℱ : Filtration ℕ m) (T : ℕ)
    {d : ℕ} (S : ℕ → Ω → (Fin d → ℝ)) : Prop :=
  ∀ H : ℕ → Ω → (Fin d → ℝ), IsPredictable ℱ T H →
    QS Pset (fun ω => 0 ≤ wealth T S H ω) → QS Pset (fun ω => wealth T S H ω = 0)

/-- Membership in the cone `𝒞 = {H • S_T : H ∈ ℋ} − L⁰₊` of Theorem 2.2, read up to `𝒫`-polar
sets: there are a predictable `H` and a nonnegative random variable `K` with
`W = H • S_T − K` `𝒫`-q.s. -/
def InCone {Ω : Type*} {m : MeasurableSpace Ω} (Pset : Set (Measure Ω)) (ℱ : Filtration ℕ m) (T : ℕ)
    {d : ℕ} (S : ℕ → Ω → (Fin d → ℝ)) (W : Ω → ℝ) : Prop :=
  ∃ H : ℕ → Ω → (Fin d → ℝ), IsPredictable ℱ T H ∧
    ∃ K : Ω → ℝ, Measurable K ∧ (∀ ω, 0 ≤ K ω) ∧ QS Pset (fun ω => W ω = wealth T S H ω - K ω)

/-- The superhedging price of Theorem 2.3,
`π(f) = inf{x ∈ ℝ : ∃ H ∈ ℋ, x + H • S_T ≥ f 𝒫-q.s.}`, an infimum in `[−∞, ∞]` with
`inf ∅ = +∞`. -/
noncomputable def price {Ω : Type*} {m : MeasurableSpace Ω} (Pset : Set (Measure Ω))
    (ℱ : Filtration ℕ m) (T : ℕ) {d : ℕ} (S : ℕ → Ω → (Fin d → ℝ)) (f : Ω → ℝ) : EReal :=
  sInf {x : EReal | ∃ x' : ℝ, x = (x' : EReal) ∧ ∃ H : ℕ → Ω → (Fin d → ℝ), IsPredictable ℱ T H ∧
    QS Pset (fun ω => f ω ≤ x' + wealth T S H ω)}

/-- Appendix (p. 35). An `ℝ^d`-valued process `X` is a *`Q`-martingale* on `{0, …, T}` in the
filtration `(F_t)`: each component of `X_t` is `F_t`-measurable and `Q`-integrable for `t ≤ T`, and
`E_Q[X_{t+1} | F_t] = X_t` `Q`-a.s. for `t < T`. -/
def IsMartingaleOn {Ω : Type*} {m : MeasurableSpace Ω} (Q : Measure Ω) (ℱ : Filtration ℕ m)
    (T : ℕ) {d : ℕ} (X : ℕ → Ω → (Fin d → ℝ)) : Prop :=
  (∀ t ≤ T, ∀ i : Fin d, Measurable[ℱ t] (fun ω => X t ω i) ∧ Integrable (fun ω => X t ω i) Q) ∧
  ∀ t < T, ∀ i : Fin d, Q[fun ω => X (t + 1) ω i | ℱ t] =ᵐ[Q] fun ω => X t ω i

/-- A (finite-valued) stopping time of the filtration `(F_t)`: `{τ ≤ t} ∈ F_t` for all `t`. -/
def IsStoppingTimeN {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m) (τ : Ω → ℕ) : Prop :=
  ∀ t : ℕ, MeasurableSet[ℱ t] {ω | τ ω ≤ t}

/-- Appendix (p. 35). `X` is a *local `Q`-martingale* on `{0, …, T}`: there are stopping times
`τ_n`, nondecreasing in `n` with `τ_n ↑ ∞` `Q`-a.s., such that every stopped process
`X^{τ_n} = (X_{t ∧ τ_n})_t` is a `Q`-martingale. -/
def IsLocalMartingaleOn {Ω : Type*} {m : MeasurableSpace Ω} (Q : Measure Ω) (ℱ : Filtration ℕ m)
    (T : ℕ) {d : ℕ} (X : ℕ → Ω → (Fin d → ℝ)) : Prop :=
  ∃ τ : ℕ → Ω → ℕ, (∀ n, IsStoppingTimeN ℱ (τ n)) ∧ (∀ ω, Monotone (fun n => τ n ω)) ∧
    (∀ᵐ ω ∂Q, Filter.Tendsto (fun n => τ n ω) Filter.atTop Filter.atTop) ∧
    ∀ n, IsMartingaleOn Q ℱ T (fun t ω => X (min t (τ n ω)) ω)

end NondomArb.Superhedge.General


