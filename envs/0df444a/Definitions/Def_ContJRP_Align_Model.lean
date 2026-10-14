-- Prove2me | Definitions.Def_ContJRP_Align_Model
-- name    : ContJRP_Align_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:23.521044+00:00
-- url     : https://prove2.me/theorems/b51b2825-291b-4c9a-9225-142a9fb42bc5
-- title:
--   §1.1, pp. 1–3 — EOQ cost C, multiples M_{t,Δ}, joint orders N(·,Δ), density, J of (1), F, and 1/M_N
-- statement:
--   This file sets up the continuous-time joint replenishment model.
--
--   1. **EOQ cost.** For ordering cost $K$ and holding cost $H$, ordering every $T>0$ time units costs per unit time
--   $$C(T)=\frac{K}{T}+HT .$$
--   Commodity $i$ has $C_i(T)=K_i/T+H_iT$.
--
--   2. **Multiples.** For $t>0$ and $\Delta\ge0$, $\mathcal M_{t,\Delta}=\{0,t,2t,\dots,\lfloor\Delta/t\rfloor\,t\}$ is the set of integer multiples of $t$ in $[0,\Delta]$, including $0$.
--
--   3. **Joint orders.** For a finite family of intervals $(T_i)_{i\in s}$, $N(T,\Delta)=\big|\bigcup_{i\in s}\mathcal M_{T_i,\Delta}\big|$ is the number of joint orders in $[0,\Delta]$, and the **ordering density** is $\lim_{\Delta\to\infty}N(T,\Delta)/\Delta$.
--
--   4. **Costs.** With joint ordering cost $K_0$, the long-run joint ordering cost of a policy $T=(T_1,\dots,T_n)$ is
--   $$J(T)=K_0\cdot\lim_{\Delta\to\infty}\frac{N(T,\Delta)}{\Delta}\qquad(1)$$
--   and its long-run average cost is $F(T)=J(T)+\sum_{i\in[n]}C_i(T_i)$.
--
--   5. **Least common multiple.** For a set $\mathcal N$ of indices, $M_{\mathcal N}$ is the least positive common integer multiple of $\{T_i\}_{i\in\mathcal N}$, with $M_{\mathcal N}=\infty$ (so $1/M_{\mathcal N}=0$) when there is none.
--
--   These are the objects in which the objective of the joint replenishment problem and Lemma 1.2's closed form for its density are written.
--
--   **Formalization Note** The index set of $N(\cdot,\Delta)$ is an arbitrary finite set, so the same definition serves policies (index $[n]$) and sets of representatives (index a set of segments). The density is a `limUnder`, which returns an unspecified value when the limit does not exist; Lemma 1.2 (a separate item) proves the limit exists whenever all intervals are positive. `invLcm` is $1/M_{\mathcal N}$, defined as the reciprocal of the infimum of the positive common multiples, and $0$ when there is none.
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, pp. 1–3, §1.1, (1), and the definition of M_N on p. 3

import Mathlib

namespace ContJRP.Align

open Classical

/-- EOQ cost `C(T) = K / T + H * T` of ordering every `T` time units (Segev, §1.1, p. 2). -/
noncomputable def eoqCost (K H T : ℝ) : ℝ := K / T + H * T

/-- `M_{t,Δ} = {0, t, 2t, …, ⌊Δ/t⌋ t}`, the integer multiples of `t` within `[0, Δ]` (p. 2). -/
noncomputable def multiplesUpTo (t Δ : ℝ) : Finset ℝ :=
  (Finset.range (⌊Δ / t⌋₊ + 1)).image (fun k : ℕ => (k : ℝ) * t)

/-- `N(·, Δ) = |⋃_{i ∈ s} M_{T_i,Δ}|`, the number of joint orders in `[0, Δ]` placed by the
intervals `(T_i)_{i ∈ s}` (p. 2). For a policy, `s = Finset.univ`. -/
noncomputable def numOrders {ι : Type*} (s : Finset ι) (T : ι → ℝ) (Δ : ℝ) : ℕ :=
  (s.biUnion fun i => multiplesUpTo (T i) Δ).card

/-- The ordering density `lim_{Δ→∞} N(·, Δ)/Δ`, as a `limUnder` (junk value if the limit fails
to exist; Lemma 1.2 shows it exists for positive intervals). -/
noncomputable def orderDensity {ι : Type*} (s : Finset ι) (T : ι → ℝ) : ℝ :=
  Filter.limUnder Filter.atTop (fun Δ : ℝ => (numOrders s T Δ : ℝ) / Δ)

/-- The long-run joint ordering cost `J(T) = K₀ · lim_{Δ→∞} N(T, Δ)/Δ`, equation (1). -/
noncomputable def jointCost {n : ℕ} (K0 : ℝ) (T : Fin n → ℝ) : ℝ :=
  K0 * orderDensity Finset.univ T

/-- The long-run average cost `F(T) = J(T) + Σ_i C_i(T_i)` (p. 2). -/
noncomputable def totalCost {n : ℕ} (K0 : ℝ) (K H : Fin n → ℝ) (T : Fin n → ℝ) : ℝ :=
  jointCost K0 T + ∑ i, eoqCost (K i) (H i) (T i)

/-- The positive common integer multiples of `(T_i)_{i ∈ s}`. -/
def commonMultiples {ι : Type*} (s : Finset ι) (T : ι → ℝ) : Set ℝ :=
  {t | 0 < t ∧ ∀ i ∈ s, ∃ k : ℕ, t = k * T i}

/-- `1 / M_s`, where `M_s` is the least common multiple of `(T_i)_{i ∈ s}`, with the convention
`M_s = ∞` (so `1 / M_s = 0`) when there is no common multiple (p. 3). -/
noncomputable def invLcm {ι : Type*} (s : Finset ι) (T : ι → ℝ) : ℝ :=
  if (commonMultiples s T).Nonempty then (sInf (commonMultiples s T))⁻¹ else 0

end ContJRP.Align


