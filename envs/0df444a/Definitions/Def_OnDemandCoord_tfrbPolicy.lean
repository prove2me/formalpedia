-- Prove2me | Definitions.Def_OnDemandCoord_tfrbPolicy
-- name    : OnDemandCoord_tfrbPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:20:24.641441+00:00
-- url     : https://prove2.me/theorems/dcb17133-bf7b-423e-af62-8a7da21fc851
-- title:
--   The Target Fill Rate-Based (TFRB) policy, Algorithm 1
-- statement:
--   **Algorithm 1 (TFRB policy)**, p. 16. Fix staffing levels $Q$, a workforce level $S$ used in the simulation, target fill rates $\beta$, and a number $T\ge2$ of simulated periods. Let $\nu$ be the law of $\hat X=(X-Q)^+$.
--
--   1. **Priority allocation** (Step 1b, Scenarios 1–2). For a priority list $\sigma$ (firm $\sigma(1)$ first), vacancies $\hat x$ and workforce $S$, the firm at position $j$ gets $$a_{\sigma(j)}=\min\Big\{\hat x_{\sigma(j)},\ \Big(S-\sum_{l<j}\hat x_{\sigma(l)}\Big)^+\Big\}.$$
--   2. **Simulation** (Step 1). Draw $\hat X(1),\dots,\hat X(T)$ i.i.d. with law $\nu$. In period 1 allocate arbitrarily (a feasible allocation $a_1(\hat X(1))$). In period $t\ge2$ compute the debts $d_i(t)=(t-1)\beta_i\mathbb E[\hat X_i]-\sum_{s<t}A_i(s)$, list the firms in nonincreasing order of debt (list $L(t)$), and allocate $\hat X(t)$ by priority in that order.
--   3. **Draw** (Step 2). $\mu_T(\sigma)=\frac1{T-1}\sum_{t=2}^{T}\mathbb P(L(t)=\sigma)$ is the law of a list drawn uniformly from $L(2),\dots,L(T)$.
--   4. **Allocate** (Step 3). The TFRB policy $\kappa_T$ maps $(\hat x,S')$ to the law of the priority allocation of $(\hat x,S')$ in an order $\sigma\sim\mu_T$.
--
--   The policy is announced before demand is realized: $\mu_T$ is computed once, from $\nu$ at the announced $Q$, and does not change when a firm later deviates.
--
--   **Formalization Note** The "arbitrary" first allocation and the tie-breaking among firms with equal debts are left open by the paper. They are the *run data*: a measurable first allocation $a_1$, feasible for $(\hat x,S)$ whenever $\hat x\ge0$, and a measurable choice `pick` of a list ordering every debt vector nonincreasingly. Every theorem quantifies over all run data. Periods are indexed from 0 in Lean ($t$ in Lean is the paper's $t+1$). The simulation runs on the product space $(\mathbb R^n)^T$ with the product measure $\nu^{\otimes T}$.
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), Algorithm 1, p. 16; §A.4.1 pp. A3–A5 (PDF 35–37)

import Mathlib
import Definitions.Def_OnDemandCoord_Model

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **The priority allocation**, Algorithm 1, Step 1b, Scenarios 1–2, p. 16. For a priority list
`σ` (with `σ 0` served first), vacancies `x` and workforce `s`,
`a_{σ j} = min {x_{σ j}, (s − ∑_{l < j} x_{σ l})⁺}`: each firm in turn is filled until the workforce
is depleted or the list ends.

**Formalization Note.** For `x ≥ 0` the formula is Scenarios 1 and 2: with `i'` the first position
where the partial sum exceeds `s`, firms before `i'` get their vacancies, firm `[i']` the remainder,
later firms `0`. Positions are `Fin n`, so `[i]` of the paper is `σ (i - 1)`. -/
noncomputable def priorityAlloc {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (s : ℝ) :
    Fin n → ℝ :=
  fun i => min (x i) (max (s - ∑ l ∈ Finset.univ.filter (fun l => l < σ⁻¹ i), x (σ l)) 0)

theorem measurable_priorityAlloc {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Measurable (fun z : (Fin n → ℝ) × ℝ => priorityAlloc σ z.1 z.2) := by
  unfold priorityAlloc
  fun_prop

/-- **The run data of the simulation in Algorithm 1**, for the workforce `s`: what the paper leaves
open. `a₁` is the first allocation (Step 1a, "allocate the workforce arbitrarily"), and `pick` is a
tie-break, a choice of priority list from the debts (Step 1b, "firms with larger gaps in the past
have higher priorities").

**Formalization Note.** Both are quantified over wherever the policy is used, so no choice is made
for the paper. `a₁` is feasible for `(x, s)` by (1). `pick d` lists the firms in nonincreasing
order of the debt `d`, with `σ 0` served first; on ties it is arbitrary. The measurability fields
make the laws of the priority lists well defined. -/
structure RunData (n : ℕ) (s : ℝ) where
  /-- The allocation of the first simulated period. -/
  a₁ : (Fin n → ℝ) → Fin n → ℝ
  measurable_a₁ : Measurable a₁
  feasible_a₁ : ∀ x, 0 ≤ x → IsFeasibleAlloc x s (a₁ x)
  /-- The priority list as a function of the debts. -/
  pick : (Fin n → ℝ) → Equiv.Perm (Fin n)
  measurableSet_pick : ∀ σ, MeasurableSet (pick ⁻¹' {σ})
  antitone_pick : ∀ d, Antitone (d ∘ pick d)

namespace RunData

variable {n : ℕ} {s : ℝ} (run : RunData n s) (β m : Fin n → ℝ) (ξ : ℕ → Fin n → ℝ)

/-- **Cumulative allocations of the simulation**, Algorithm 1, Step 1. `cumAlloc t` is
`∑_{r ≤ t} A(r)` of the paper, the total allocated in the first `t` simulated periods, for samples
`ξ 0, ξ 1, …` (the paper's `X̂(1), X̂(2), …`). Period `1` of the paper uses `a₁`. Each later period is
the priority allocation of its sample, in the order chosen from the current debts
`t β_i m_i − ∑_{r ≤ t} A_i(r)`, where `m_i = E[X̂_i]`. -/
noncomputable def cumAlloc : ℕ → Fin n → ℝ
  | 0 => 0
  | 1 => run.a₁ (ξ 0)
  | t + 2 => cumAlloc (t + 1) +
      priorityAlloc (run.pick fun i => ((t + 1 : ℕ) : ℝ) * (β i * m i) - cumAlloc (t + 1) i)
        (ξ (t + 1)) s

/-- **The priority list** of the simulated period with Lean index `t`, i.e. the paper's `L(t + 1)`
(`t ≥ 1`): firms ordered by the debts
`d_i(t + 1) = t β_i E[X̂_i] − ∑_{r ≤ t} A_i(r)` of Algorithm 1, Step 1b, and (A.4.1), p. A4. -/
noncomputable def priorityList (t : ℕ) : Equiv.Perm (Fin n) :=
  run.pick fun i => (t : ℝ) * (β i * m i) - run.cumAlloc β m ξ t i

end RunData

/-- A finite sample `ξ(1), …, ξ(T)` as a sequence. The recursion of `RunData.cumAlloc` reads only
coordinates `< T`, so the default value is never used by a list `L(t)` with `t ≤ T`. -/
noncomputable def extendSample {n T : ℕ} (ξ : Fin T → Fin n → ℝ) : ℕ → Fin n → ℝ :=
  fun t => if h : t < T then ξ ⟨t, h⟩ else 0

/-- The law `ν^{⊗T}` of `T` i.i.d. simulated samples with law `ν` (Algorithm 1, Step 1). -/
noncomputable def sampleLaw {n : ℕ} (ν : Measure (Fin n → ℝ)) (T : ℕ) :
    Measure (Fin T → Fin n → ℝ) :=
  Measure.pi fun _ => ν

/-- **The law of the drawn list**, Algorithm 1, Step 2: `μ_T(σ)` is the probability that a list drawn
uniformly from `L(2), …, L(T)` equals `σ`, i.e.
`μ_T(σ) = (T − 1)⁻¹ ∑_{t = 2}^{T} ν^{⊗T}(L(t) = σ)`. Lean's index `t ∈ [1, T)` is the paper's `t + 1`. -/
noncomputable def RunData.listWeight {n : ℕ} {s : ℝ} (run : RunData n s) (β m : Fin n → ℝ)
    (ν : Measure (Fin n → ℝ)) (T : ℕ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ((T : ℝ) - 1)⁻¹ * ∑ t ∈ Finset.Ico 1 T,
    (sampleLaw ν T).real {ξ | run.priorityList β m (extendSample ξ) t = σ}

/-- **The TFRB kernel**, Algorithm 1, Steps 2–3, p. 16: `κ_T (x̂, r)` is the law of the priority
allocation of `(x̂, r)` in an order `σ ∼ μ_T`. It is a fixed function of `(x̂, r)`: `μ_T` is computed
once from `ν`, `β`, `m`, `s`, and does not move with the argument. -/
noncomputable def RunData.tfrbKernel {n : ℕ} {s : ℝ} (run : RunData n s) (β m : Fin n → ℝ)
    (ν : Measure (Fin n → ℝ)) (T : ℕ) : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ) where
  toFun z := ∑ σ, ENNReal.ofReal (run.listWeight β m ν T σ) •
    Measure.dirac (priorityAlloc σ z.1 z.2)
  measurable' := by
    refine Finset.measurable_sum _ fun σ _ => ?_
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ((Measure.measurable_coe ht).comp
      (Measure.measurable_dirac.comp (measurable_priorityAlloc σ))).const_mul _

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)

/-- **The TFRB policy `A*(·)`**, Algorithm 1, p. 16, for the staffing level `Q`, the workforce level
`s` of the simulation, the target fill rates `β`, the run data and the number `T` of simulated
periods. The simulation uses `ν`, the law of `X̂ = (X − Q)⁺`, and `E[X̂_i]`, both at `Q`.

**Formalization Note.** Algorithm 1 takes `T` "a large number". `T` is a parameter here, and it is
used with `T ≥ 2` (one list at least). When a firm deviates from `Q`, the policy does not change:
`Q` here is the announced level, and the deviating firm only changes the point at which the kernel
is evaluated (p. 10, the policy is announced; p. 15, "has to be announced before the demand
realization"). -/
noncomputable def tfrb (Q : Fin n → ℝ) (s : ℝ) (β : Fin n → ℝ) (run : RunData n s) (T : ℕ) :
    Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ) :=
  run.tfrbKernel β (M.mean Q) (P.map (M.vacVec Q)) T

end Model

end OnDemandCoord


