-- Prove2me | Definitions.Def_BilateralRegret_regret
-- name    : BilateralRegret_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:19.309216+00:00
-- url     : https://prove2.me/theorems/bcb1f24c-b81a-4af6-a135-4447393b4ea7
-- title:
--   Valuation laws with bounded density, the i.i.d. sample space $(\mu_S\otimes\mu_B)^{\otimes T}\otimes\mu_L^{\otimes T}$, and the regret $R_T$ of a price process
-- statement:
--   **Bounded density.** A law $\mu$ on $\mathbb R$ has density bounded by $M$ if $\mu(A)\le M\,\mathrm{Leb}(A)$ for every Borel set $A$. For a law on $[0,1]$ this says exactly that $\mu$ has a Lebesgue density with values in $[0,M]$; it forces $M\ge1$.
--
--   **Sample space.** For a horizon $T$, a scenario is $\omega=((S_t,B_t)_{t\le T},(U_t)_{t\le T})$: seller and buyer valuations and the player's uniform draws. In the stochastic i.i.d. setting with independent valuations, the law of $\omega$ is
--
--   $$
--   \mathbb P_T=(\mu_S\otimes\mu_B)^{\otimes T}\otimes\mu_L^{\otimes T},
--   $$
--
--   so the pairs $(S_t,B_t)$ are i.i.d. with $S_t$ independent of $B_t$, and $U_1,\dots,U_T$ are i.i.d. uniform on $[0,1]$ and independent of the valuations (an oblivious adversary).
--
--   **Regret.** For a price process $P$ (the price $P_t(\omega)$ posted in round $t$),
--
--   $$
--   R_T=\sup_{p\in[0,1]}\mathbb E\Big[\sum_{t=1}^T\mathrm{GFT}(p,S_t,B_t)-\sum_{t=1}^T\mathrm{GFT}(P_t,S_t,B_t)\Big].
--   $$
--
--   This is the benchmark of the paper: the best fixed price in hindsight, in expectation.
--
--   **Formalization Note** Rounds $t=1,\dots,T$ are indices $t-1$ of `Fin T`. The supremum is the real supremum over the subtype $[0,1]$; the expectations lie in $[-T,T]$ when the valuations are almost surely in $[0,1]$, so it is the true supremum. The paper writes $\max$ (a maximizer exists by Lemma 2). The density bound is stated for one law at a time.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, §2, p.6 (regret R_T, (iid), (iv), (bd)); Definition 2 and Definition 4, p.23; App. C.2.3, p.24; Theorem 3, p.12 (densities bounded by M)

import Mathlib
import Definitions.Def_BilateralRegret_GFT

namespace BilateralRegret

open MeasureTheory

/-- **Density bounded by `M`** for a law `μ` on `ℝ`: `μ(A) ≤ M · Leb(A)` for every Borel set `A`.
For a law on `[0,1]` this says exactly that `μ` has a Lebesgue density with values in `[0, M]`.

Cesa-Bianchi et al., arXiv:2109.12974v1, Theorem 3, p.12 ("have densities bounded by some
constant `M`"); cf. (bd), p.6 and App. C.2.3, p.24.

**Formalization Note.** The bound is stated for one valuation law at a time (the seller's and
the buyer's separately), not for the joint law of `(S, B)`; see the theorems' `Differences from
the source`. -/
def DensityBoundedBy (M : ℝ) (μ : Measure ℝ) : Prop :=
  ∀ A : Set ℝ, MeasurableSet A → μ A ≤ ENNReal.ofReal M * volume A

/-- The sample space of the bilateral trade game at horizon `T` (Definition 2, p.23, truncated
to `T` rounds): the seller/buyer valuations `(S_t, B_t)` and the player's uniform
randomization `U_t`, for rounds `t = 1, …, T`.

**Formalization Note.** Round `t ∈ {1, …, T}` is the index `t − 1 : Fin T`. -/
abbrev Scenario (T : ℕ) := (Fin T → ℝ × ℝ) × (Fin T → ℝ)

/-- **The stochastic (iid) scenario with independent valuations (iv)** at horizon `T`
(App. C.2.3, p.24, and Definition 2, p.23):
`P_T = (μ_S ⊗ μ_B)^{⊗T} ⊗ (μ_L)^{⊗T}`. The pairs `(S_t, B_t)` are i.i.d. with law `μ_S ⊗ μ_B`
(so `S_t` and `B_t` are independent), and the player's randomization `U_1, …, U_T` is i.i.d.
uniform on `[0,1]` and independent of the valuations (the oblivious adversary of p.23). -/
noncomputable def scenario (μS μB : Measure ℝ) (T : ℕ) : Measure (Scenario T) :=
  (Measure.pi fun _ : Fin T => μS.prod μB).prod (Measure.pi fun _ : Fin T => unif)

/-- The seller's valuation `S_t` in round `t`. -/
def sellerVal {T : ℕ} (ω : Scenario T) (t : Fin T) : ℝ := (ω.1 t).1

/-- The buyer's valuation `B_t` in round `t`. -/
def buyerVal {T : ℕ} (ω : Scenario T) (t : Fin T) : ℝ := (ω.1 t).2

/-- The player's uniform draw `U_t` in round `t`. -/
def unifDraw {T : ℕ} (ω : Scenario T) (t : Fin T) : ℝ := ω.2 t

/-- **Regret** of a price process `P` (the price `P_t(ω)` posted in round `t`) over `T` rounds,
with valuation laws `μ_S`, `μ_B`:
`R_T = sup_{p ∈ [0,1]} 𝔼[ Σ_{t=1}^T GFT(p, S_t, B_t) − Σ_{t=1}^T GFT(P_t, S_t, B_t) ]`.

Cesa-Bianchi et al., arXiv:2109.12974v1, §2, p.6 (`R_T(α)`), and Definition 4, p.23
(`R^ℙ_T(α) := sup_{x ∈ 𝒳} 𝔼_ℙ[…]`, with `𝒳 = [0,1]`).

**Formalization Note.** The supremum is the real `⨆` over the subtype `[0,1]`, which is nonempty;
each expectation lies in `[−T, T]` when the valuations are a.s. in `[0,1]` (and a Bochner
integral of a non-integrable function is `0`), so the family is bounded and `⨆` is the true
supremum. The paper writes `max`; the supremum does not presuppose a maximizer (Lemma 2
supplies one). -/
noncomputable def regret (T : ℕ) (μS μB : Measure ℝ) (P : Scenario T → Fin T → ℝ) : ℝ :=
  ⨆ p : Set.Icc (0 : ℝ) 1,
    ∫ ω, (∑ t, GFT p (sellerVal ω t) (buyerVal ω t)
          - ∑ t, GFT (P ω t) (sellerVal ω t) (buyerVal ω t)) ∂(scenario μS μB T)

end BilateralRegret


