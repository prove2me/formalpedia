-- Prove2me | Definitions.Def_ReusablePricing_DPCB_Events
-- name    : ReusablePricing_DPCB_Events
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:53.600991+00:00
-- url     : https://prove2.me/theorems/ad0feaab-93ae-41ed-9733-49b14c61ea7c
-- title:
--   EC.4 Step 1, ec8–ec13 — batches 𝒯_k^b, δ_k^b of (EC.17), the events 𝒜_k^b of (EC.16) and 𝒢(ϵ, m, δ), η_e and η_δ
-- statement:
--   This file defines the objects of the proof of Theorem 3 (Section EC.4) that its milestones refer to.
--
--   1. The batch $\mathcal{T}_k^b = \{ t \in [1,T] : \beta_k(t) = b \}$.
--   2. $\underline{n} = \min_k \underline{n}_k$ and the threshold of (EC.17):
--   $$
--   \delta^b_k = \begin{cases} \dfrac{\underline{n}-1}{\underline{n}} \cdot \dfrac{\min_k \epsilon_k - 1}{4K} & \text{if } \min\{t : t \in \mathcal{T}_k^b\} \le n_K + \ell_K + 1, \\[2mm] \dfrac{\underline{n}-1}{\underline{n}} \cdot \dfrac{\epsilon_k - 1}{4} & \text{otherwise.} \end{cases}
--   $$
--   3. The event $\mathcal{A}^b_k$ of (EC.16): for every $t \in \mathcal{T}_k^b$, $\bigl|\sum_{s \in \mathcal{T}_k^b,\, s \le t} \Delta^s_k\bigr| < \delta^b_k$.
--   4. The high-probability event $\mathcal{G}(\epsilon, m, \delta) = \bigcap_k \bigcap_{b=1}^{B_k} \mathcal{A}^b_k$.
--   5. $(\eta^t_e)_k = \mathbf{1}\{\lambda^{t,D}_k > 0\}$ and $(\eta^t_\delta)_k = \frac{1}{m_k}\sum_{s \in \mathcal{T}_k^{\beta_k(t)-1}} \Delta^s_k$.
--
--   On $\mathcal{G}$ the control's rates can be written explicitly, and the proof of Theorem 3 splits the loss into its value on $\mathcal{G}$ and the probability of the complement.
--
--   **Formalization Note** (EC.17) writes $\underline{n}$, which Section 6 never defines; it is read as $\min_k \underline{n}_k$, the analogue of Section 4's $\underline{n}$. $n_K + \ell_K$ is written $\max_k (n_k+\ell_k)$, equal to it under the ordering (i) of p. 17. The printed (EC.16) sums $\Delta^s_k$ over the periods $(b-1)m_k+1, \dots, t \le bm_k$; this coincides with the batch $\mathcal{T}_k^b$ when every $\lambda^{t,D}_k$ is positive, and the proof of Lemma EC.3 uses the batch sums, so the event is stated over the batch. The minimum over $k$ uses $K \ge 1$.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), p. ec8 (EC.4 Step 1, (EC.16), 𝒢(ϵ, m, δ)), p. ec9 ((EC.17)), pp. ec12–ec13 (η_e, η_δ)

import Mathlib
import Definitions.Def_ReusablePricing_DPCB_Control

open Finset

namespace ReusablePricing.DPCB

namespace General

variable (P : General)

/-- Batch `𝒯_k^b = {t ∈ [1, T] : β_k(t) = b}`. -/
def batch (β : Fin P.K → ℕ → ℕ) (k : Fin P.K) (b : ℕ) : Finset ℕ :=
  (Icc 1 P.T).filter (fun t => β k t = b)

/-- `max_k (n_k + ℓ_k)`, which is `n_K + ℓ_K` under the ordering (i) of p. 17. -/
def maxNL : ℕ := Finset.univ.sup (fun k : Fin P.K => P.n k + P.ℓ k)

/-- `n̲ = min_k n̲_k` (for `K ≥ 1`), as a real number. -/
noncomputable def nlMin (nl : Fin P.K → ℕ) : ℝ := ((⨅ k, nl k : ℕ) : ℝ)

/-- `δ^b_k` of (EC.17), ec9: `((n̲ - 1)/n̲)·(min_k ϵ_k - 1)/(4K)` if the first period of `𝒯_k^b`
is at most `n_K + ℓ_K + 1`, and `((n̲ - 1)/n̲)·(ϵ_k - 1)/4` otherwise. -/
noncomputable def delta (nl : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
    (k : Fin P.K) (b : ℕ) : ℝ :=
  if ((P.batch β k b).filter (fun t => t ≤ P.maxNL + 1)).Nonempty then
    (P.nlMin nl - 1) / P.nlMin nl * ((P.epsMin ε - 1) / (4 * (P.K : ℝ)))
  else
    (P.nlMin nl - 1) / P.nlMin nl * ((ε k - 1) / 4)

/-- The event `𝒜^b_k` of (EC.16), read over the batch `𝒯_k^b`: every partial sum of the errors
`Δ^s_k` over the periods of the batch up to `t` is less than `δ^b_k` in absolute value. -/
def inA (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
    (δ : Fin P.K → ℕ → ℝ) (k : Fin P.K) (b : ℕ) (ω : P.Path) : Prop :=
  ∀ t ∈ P.batch β k b,
    |∑ s ∈ (P.batch β k b).filter (fun s => s ≤ t), P.err nl m ε β s ω k| < δ k b

/-- The event `𝒢(ϵ, m, δ) = ⋂_k ⋂_{b=1}^{B_k} 𝒜^b_k` (ec8). -/
def inG (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ) (B : Fin P.K → ℕ)
    (δ : Fin P.K → ℕ → ℝ) (ω : P.Path) : Prop :=
  ∀ k, ∀ b ∈ Icc 1 (B k), P.inA nl m ε β δ k b ω

/-- `(η^t_e)_k = 1{λ^{t,D}_k > 0}` (ec12). -/
noncomputable def etaE (t : ℕ) (k : Fin P.K) : ℝ := if 0 < P.lamD t k then 1 else 0

/-- `(η^t_δ)_k = (∑_{s ∈ 𝒯_k^{β_k(t) - 1}} Δ^s_k) / m_k` (ec12). -/
noncomputable def etaDelta (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
    (t : ℕ) (ω : P.Path) (k : Fin P.K) : ℝ :=
  P.prevErr nl m ε β t ω k / (m k : ℝ)

end General

end ReusablePricing.DPCB


