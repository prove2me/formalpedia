-- Prove2me | Definitions.Def_DegenNRM_policyRun
-- name    : DegenNRM_policyRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:36:38.671213+00:00
-- url     : https://prove2.me/theorems/50d87c41-48b4-4f56-913f-212ef23c7e19
-- title:
--   Algorithm 1 with the estimator of Algorithm 2: capacities, value $V^\pi(I)$ and regret (3)
-- statement:
--   Fix initial capacities $C$, a horizon $T$ and a **selection** $\sigma$ of optimal solutions of (13): for every period $t\in[T]$ and every remaining capacity $c\ge0$, $\sigma(t,c)$ is an optimal solution of (13) with $s=T-t+1$ periods left.
--
--   Algorithm 1 with the estimator of Algorithm 2 starts with $c_1=C$. In period $t$ it observes the type $j_t$ and the reward $\tilde r_t$, computes $\hat M$ of Algorithm 2 from $\kappa_1$ of (15), $s=T-t+1$ and $\hat q^*=\sigma(t,c_t)$, and serves the query ($x_t=1$) iff $\tilde r_t\ge\hat M$ and $c_t\ge a_{j_t}$ componentwise; then $c_{t+1}=c_t-a_{j_t}x_t$. Its value is $V^\pi(I)=\sum_{t=1}^T\tilde r_tx_t$ and its regret is
--   $$\mathrm{Regret}(\pi)=\mathbb E_{I\sim F}[V^{\mathrm{off}}(I)]-\mathbb E_{I\sim F}[V^\pi(I)].$$
--
--   **Formalization Note** The capacities and decisions are defined by recursion on the period from the sample path; only $\sigma$ is free. Both integrands are measurable for every $\sigma$ (the capacities take countably many values), and the goal theorem also asserts their integrability.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Algorithm 1, p.12; Algorithm 2, p.15; (3), p.6

import Mathlib
import Definitions.Def_DegenNRM_arrivalLaw
import Definitions.Def_DegenNRM_offlineValue
import Definitions.Def_DegenNRM_IsQuantOpt
import Definitions.Def_DegenNRM_kappa1
import Definitions.Def_DegenNRM_algorithm2

open MeasureTheory

namespace DegenNRM

/-- **A selection of optimal solutions of (13)** for a horizon `T` (Jiang, Ma & Zhang,
arXiv:2210.07996v5, Algorithm 2, line 2, p.15: "Obtain {q̂*_{j,t}} by solving the optimization
problem (13)").

`σ t c` is the solution the algorithm uses in period `t ∈ [T]` at remaining capacity `c ≥ 0`; it
must be an optimal solution of (13) with `s = T - t + 1` periods left.

**Formalization Note.** Problem (13) may have several optimal solutions; the paper does not
say which one is used, so the theorems of this mission hold for every selection `σ`. -/
def IsFluidSelection {m n : ℕ} (inst : Instance m n) (T : ℕ)
    (σ : ℕ → (Fin m → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T → ∀ c : Fin m → ℝ, 0 ≤ c →
    IsFluidOpt inst c ((T - t + 1 : ℕ) : ℝ) (σ t c)

/-- **The decision of Algorithm 1 with the estimator of Algorithm 2** in period `t` at remaining
capacity `c`, for an arrival of type `j` with reward `r` (arXiv:2210.07996v5, Algorithm 1,
lines 4–6, p.12, and Algorithm 2, p.15): serve iff `r ≥ M̂_{c, a_j}` and `c ≥ a_j`
componentwise, where `M̂` is computed by Algorithm 2 from `κ₁` of (15), `s = T - t + 1` and the
type-`j` entry of `σ t c`. -/
def accepts {m n : ℕ} (inst : Instance m n) (T : ℕ) (σ : ℕ → (Fin m → ℝ) → (Fin n → ℝ))
    (t : ℕ) (c : Fin m → ℝ) (j : Fin n) (r : ℝ) : Prop :=
  estimator inst (kappa1 inst) ((T - t + 1 : ℕ) : ℝ) j (σ t c j) ≤ r ∧ ∀ i, inst.a j i ≤ c i

open Classical in
/-- **The remaining capacities `c_t` of Algorithm 1** (arXiv:2210.07996v5, Algorithm 1, p.12):
`capacity … ω k` is the capacity vector at the beginning of period `k + 1`. It starts at
`c_1 = C`; in period `t` (coordinate `t - 1` of `ω`), if the query is served then
`c_{t+1} = c_t - a_{j_t}`, otherwise `c_{t+1} = c_t`. -/
noncomputable def capacity {m n T : ℕ} (inst : Instance m n) (C : Fin m → ℝ)
    (σ : ℕ → (Fin m → ℝ) → (Fin n → ℝ)) (ω : Fin T → Fin n × ℝ) : ℕ → (Fin m → ℝ)
  | 0 => C
  | k + 1 =>
    if h : k < T then
      if accepts inst T σ (k + 1) (capacity inst C σ ω k) (ω ⟨k, h⟩).1 (ω ⟨k, h⟩).2 then
        capacity inst C σ ω k - inst.a (ω ⟨k, h⟩).1
      else capacity inst C σ ω k
    else capacity inst C σ ω k

open Classical in
/-- **The total collected value `V^π(I) = Σ_t r̃_t x_t`** of Algorithm 1 with the estimator of
Algorithm 2 (arXiv:2210.07996v5, §2, p.6, and Algorithm 1, p.12), where `x_t = 1` iff the
policy serves the query of period `t`. -/
noncomputable def policyValue {m n T : ℕ} (inst : Instance m n) (C : Fin m → ℝ)
    (σ : ℕ → (Fin m → ℝ) → (Fin n → ℝ)) (ω : Fin T → Fin n × ℝ) : ℝ :=
  ∑ k : Fin T,
    if accepts inst T σ ((k : ℕ) + 1) (capacity inst C σ ω k) (ω k).1 (ω k).2 then (ω k).2
    else 0

/-- **The regret (3) of Algorithm 1 with the estimator of Algorithm 2**
(arXiv:2210.07996v5, (3), p.6): `Regret(π) = E_{I∼F}[V^off(I)] - E_{I∼F}[V^π(I)]`, both
expectations over the law of the sample path of `T` periods.

**Formalization Note.** The policy is deterministic given the selection `σ`, so the only
randomness is the sample path. Both integrands are measurable for every `σ` (the capacities
take countably many values) and bounded on the support; the goal theorem asserts their
integrability as well, so the Bochner integrals are the expectations. -/
noncomputable def regret {m n : ℕ} (inst : Instance m n) (C : Fin m → ℝ) (T : ℕ)
    (σ : ℕ → (Fin m → ℝ) → (Fin n → ℝ)) : ℝ :=
  (∫ ω, offlineValue inst C ω ∂(pathLaw inst T)) - ∫ ω, policyValue inst C σ ω ∂(pathLaw inst T)

end DegenNRM


