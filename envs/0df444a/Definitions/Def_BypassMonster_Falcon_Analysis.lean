-- Prove2me | Definitions.Def_BypassMonster_Falcon_Analysis
-- name    : BypassMonster_Falcon_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:31.76866+00:00
-- url     : https://prove2.me/theorems/6a06b5ca-5498-40d0-9c50-9b208a2a5ee9
-- title:
--   App. A.1–A.6 — implicit rewards ℛ, ℛ̂, implicit regrets Reg, Reĝ, V(p,π), 𝒱, the randomized policy Qₘ, the event Γ₂ and the martingale differences Mₜ
-- statement:
--   The quantities of the paper's analysis (App. A.1–A.6) for the run of FALCON+ defined in `BypassMonster.Falcon.Model`. Throughout, $m$ is an epoch, $\omega$ an outcome of the canonical space, $\pi:\mathcal X\to\mathcal A$ a deterministic policy (an element of the universal policy space $\Psi=\mathcal A^{\mathcal X}$), and $p_m(\cdot\mid x)$ the action selection kernel of epoch $m$ (step 6 of Algorithm 2 with $x_t$ replaced by $x$).
--
--   1. Implicit rewards and regrets: $\mathcal R(\pi)=\mathbb E_{x\sim\mathcal D_{\mathcal X}}[f^*(x,\pi(x))]$, $\mathrm{Reg}(\pi)=\mathcal R(\pi_{f^*})-\mathcal R(\pi)$; $\hat{\mathcal R}_m(\pi)=\mathbb E_{x}[\hat f_m(x,\pi(x))]$ and $\widehat{\mathrm{Reg}}_m(\pi)=\hat{\mathcal R}_m(\pi_{\hat f_m})-\hat{\mathcal R}_m(\pi)$, where $\pi_{\hat f_m}(x)=\hat a_m(x)$ is the greedy action.
--   2. The decisional divergence $V(p,\pi)=\mathbb E_x\big[1/p(\pi(x)\mid x)\big]$ and, for $m\ge2$, $\mathcal V_m(\pi)=\max_{1\le n\le m-1}V(p_n,\pi)$.
--   3. The equivalent randomized policy $Q_m(\pi)=\prod_{x\in\mathcal X}p_m(\pi(x)\mid x)$ on $\Psi$.
--   4. The error of $\hat f_m$ under the kernel $p_{m-1}$ that generated its training data,
--   $$\mathrm{err}_m=\mathbb E_{x\sim\mathcal D_{\mathcal X},\,a\sim p_{m-1}(\cdot\mid x)}\big[(\hat f_m(x,a)-f^*(x,a))^2\big],$$
--   and the event $\Gamma_2=\{\forall m\ge2:\ \mathrm{err}_m\le K/(4\gamma_m^2)\}$.
--   5. The martingale differences $M_t=r_t(\pi_{f^*}(x_t))-r_t(a_t)-\sum_{\pi\in\Psi}Q_{m(t)}(\pi)\mathrm{Reg}(\pi)$.
--
--   These are the objects the milestones (Lemmas A.2–A.10) are stated in; the goal theorem does not use them.
--
--   **Formalization Note** The paper indexes $\hat{\mathcal R}_t$, $\widehat{\mathrm{Reg}}_t$ and $\mathcal V_t$ by a round $t$; they depend on $t$ only through its epoch $m(t)$ and are indexed here by the epoch. $\mathcal V_m$ is set to $0$ for $m\le1$, where the paper never uses it. The paper's expression $\mathbb E_{x_t,a_t}[(\hat f_m(x_t,a_t)-f^*(x_t,a_t))^2\mid\Upsilon_{t-1}]$ in $\Gamma_2$ is encoded as $\mathrm{err}_m$, which is how the proof of Lemma A.2 (p. 1923) rewrites it (a fresh $(x,a)$ with $a\sim p_{m-1}(\cdot\mid x)$, $\hat f_m$ frozen); the printed $\Gamma_2$ says "$t$ in epoch $m$" where the first display of Lemma A.2 and the proof of Lemma A.7 use $t$ in epoch $m-1$. The σ-algebra $\Upsilon_{t-1}$ is replaced by the coordinate filtration $\sigma(\omega_0,\dots,\omega_{t-1})$ of the canonical space, which contains it.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), App. A.1 p. 1922; Lemma A.2 (Γ₂) pp. 1922–1923; proof of Lemma A.3 (Qₘ) p. 1923; proof of Lemma A.10 (Mₜ) p. 1927

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model

/-!
The analysis quantities of App. A.1–A.6 (pp. 1922–1927) for a run of FALCON+ on the canonical
space. Every quantity the paper indexes by a round `t` ("for any round `t` in epoch `m`") depends
on `t` only through its epoch `m(t)`, and is indexed here by the epoch `m`. The paper's
σ-algebra `Υ_t = σ((x_1,r_1,a_1), …, (x_t,r_t,a_t))` is replaced by the coordinate filtration
`σ(ω 0, …, ω t)` of the canonical space (`MeasureTheory.Filtration.piLE t`), which contains it.
-/

namespace BypassMonster.Falcon

open MeasureTheory ProbabilityTheory

variable {X : Type*} {K : ℕ}

/-- The expected reward of a policy `π : X → 𝒜`, `ℛ(π) = E_{x∼D_X}[f*(x, π(x))]` (App. A.1). -/
noncomputable def R [MeasurableSpace X] (DX : Measure X) (ν : Kernel X (Fin K → ℝ))
    (π : X → Fin K) : ℝ :=
  ∫ x, fstar ν x (π x) ∂DX

/-- The implicit regret `Reg(π) = ℛ(π_{f*}) − ℛ(π)` (App. A.1), with `πstar = π_{f*}`. -/
noncomputable def Reg [MeasurableSpace X] (DX : Measure X) (ν : Kernel X (Fin K → ℝ))
    (πstar : X → Fin K) (π : X → Fin K) : ℝ :=
  R DX ν πstar - R DX ν π

namespace Params

/-- The predicted expected reward `ℛ̂_t(π) = E_{x∼D_X}[f̂_m(x, π(x))]` for rounds `t` of epoch `m`
(App. A.1). -/
noncomputable def Rhat [NeZero K] [MeasurableSpace X] (A : Params X K) (DX : Measure X) (m : ℕ)
    (ω : Omega X K) (π : X → Fin K) : ℝ :=
  ∫ x, A.fhat m ω x (π x) ∂DX

/-- The greedy policy `π_{f̂_m}(x) = â_m(x) = amax (f̂_m(x, ·))` of epoch `m`. -/
noncomputable def greedy [NeZero K] (A : Params X K) (m : ℕ) (ω : Omega X K) (x : X) : Fin K :=
  A.amax (A.fhat m ω x)

/-- The predicted implicit regret `Reĝ_t(π) = ℛ̂_t(π_{f̂_m}) − ℛ̂_t(π)` for rounds `t` of epoch `m`
(App. A.1). -/
noncomputable def RegHat [NeZero K] [MeasurableSpace X] (A : Params X K) (DX : Measure X)
    (m : ℕ) (ω : Omega X K) (π : X → Fin K) : ℝ :=
  A.Rhat DX m ω (A.greedy m ω) - A.Rhat DX m ω π

end Params

/-- `V(p, π) = E_{x∼D_X}[1 / p(π(x) | x)]` for a kernel `p` and a policy `π` (App. A.1). -/
noncomputable def V [MeasurableSpace X] (DX : Measure X) (p : X → Fin K → ℝ)
    (π : X → Fin K) : ℝ :=
  ∫ x, 1 / p x (π x) ∂DX

namespace Params

/-- `𝒱_t(π) = max_{1 ≤ n ≤ m(t) − 1} V(p_n, π)` for rounds `t` of epoch `m ≥ 2` (App. A.1); set to
`0` for `m ≤ 1`, where the maximum is over an empty range and the paper never uses it. -/
noncomputable def calV [NeZero K] [MeasurableSpace X] (A : Params X K) (DX : Measure X) (m : ℕ)
    (ω : Omega X K) (π : X → Fin K) : ℝ :=
  if h : 2 ≤ m then
    (Finset.Icc 1 (m - 1)).sup' (by simp; omega) (fun n => V DX (A.pm n ω) π)
  else 0

/-- The equivalent randomized policy `Q_m = ∏_{x ∈ X} p_m(· | x)` on the universal policy space
`Ψ = 𝒜^X` (proof of Lemma A.3, p. 1923): `Q_m(π) = ∏_x p_m(π(x) | x)`. -/
noncomputable def Qm [Fintype X] [NeZero K] (A : Params X K) (m : ℕ) (ω : Omega X K)
    (π : X → Fin K) : ℝ :=
  ∏ x, A.pm m ω x (π x)

/-- The error of the predictor `f̂_m` under the kernel `p_{m−1}` that generated its training data
(epoch `m − 1`): `E_{x∼D_X, a∼p_{m−1}(·|x)}[(f̂_m(x,a) − f*(x,a))² | p_{m−1}]`, the quantity
the proof of Lemma A.2 (p. 1923) writes for `E_{x_t,a_t}[(f̂_m(x_t,a_t) − f*(x_t,a_t))² | Υ_{t−1}]`,
`t` in epoch `m − 1`. Used for `m ≥ 2`. -/
noncomputable def errSq [NeZero K] [MeasurableSpace X] (A : Params X K) (DX : Measure X)
    (ν : Kernel X (Fin K → ℝ)) (m : ℕ) (ω : Omega X K) : ℝ :=
  popSqErr DX ν (A.pm (m - 1) ω) (A.fhat m ω)

/-- The event `Γ_2` (Lemma A.2, p. 1923): for every epoch `m ≥ 2`, the error of `f̂_m` under the
kernel of its training epoch `m − 1` is at most `K / (4 γ_m²)`. -/
def Gamma2 [NeZero K] [MeasurableSpace X] (A : Params X K) (DX : Measure X)
    (ν : Kernel X (Fin K → ℝ)) : Set (Omega X K) :=
  {ω | ∀ m : ℕ, 2 ≤ m → A.errSq DX ν m ω ≤ (K : ℝ) / (4 * A.gamma m ^ 2)}

/-- The martingale difference of the proof of Lemma A.10 (p. 1927):
`M_t = r_t(π_{f*}(x_t)) − r_t(a_t) − ∑_{π ∈ Ψ} Q_{m(t)}(π) Reg(π)`. -/
noncomputable def Mt [Fintype X] [DecidableEq X] [NeZero K] [MeasurableSpace X] (A : Params X K)
    (DX : Measure X) (ν : Kernel X (Fin K → ℝ)) (πstar : X → Fin K) (t : ℕ)
    (ω : Omega X K) : ℝ :=
  ((ω t).1.2 (πstar (ω t).1.1) - (ω t).1.2 (A.action t ω))
    - ∑ π : X → Fin K, A.Qm (epochOf A.τ t) ω π * Reg DX ν πstar π

end Params

end BypassMonster.Falcon


