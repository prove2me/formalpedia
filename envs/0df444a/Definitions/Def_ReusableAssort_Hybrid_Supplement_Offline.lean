-- Prove2me | Definitions.Def_ReusableAssort_Hybrid_Supplement_Offline
-- name    : ReusableAssort_Hybrid_Supplement_Offline
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:17:36.298359+00:00
-- url     : https://prove2.me/theorems/ed72c722-fb9d-458b-b04c-15f6fb552102
-- title:
--   Optimum offline benchmark, §EC.2 item 1, p. ec3
-- statement:
--   The optimum offline benchmark (§EC.2, item 1). The offline algorithm knows in advance the realized types $z_1, \dots, z_T$, the rental duration $d_{t,i} \sim g^{z_t}_i$ that product $i$ would have if rented at time $t$, and the consumer's choice $f_t(S)$ for every possible assortment $S$.
--
--   1. **Choice laws.** A joint law of the choice function $f_t$ for a consumer of type $z$ at time $t$ is *valid* if it is a probability distribution whose marginal at each $S \in \mathcal S$ is the choice model: $\Pr[f_t(S) = i] = \phi^z(S, i)$.
--   2. **Offline feasibility.** A sequence $A_1, \dots, A_T$ with $A_t \in \mathcal S$ is feasible on a realization if every product offered at time $t$ has a unit on hand: fewer than $c_i$ units of $i$ rented before $t$ are still out (a unit rented at $\tau$ with duration $d$ is out at $\tau, \dots, \tau + d - 1$).
--   3. **Benchmark.** With independent types across times, durations independent across products conditional on each type, and a choice function drawn independently of those durations from the specified joint law,
--   $$\mathrm{OPT}_{\mathrm{off}} = \mathbb E\Bigl[\max_{A \text{ feasible}} \sum_{t=1}^T r^{z_t}_{f_t(A_t)}\Bigr],$$
--   where a time with no rental contributes $0$.
--
--   **Formalization Note** The paper does not fix the joint law of choices across assortments; the benchmark is a function of the chosen valid law. The maximum is over a finite set that contains the sequence offering the empty assortment at every time (under the model assumptions).
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. ec3 (PDF 29), §EC.2 item 1

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Model

namespace ReusableAssort.Hybrid.Supplement

variable {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]

/-- A realization seen by the optimum offline (§EC.2, item 1, p. ec3): for each step `k`
(time `k + 1`), the type `z_{k+1}`, the rental duration `d_{k+1,i} ∈ {0, …, T}` that product
`i` would draw if rented at that time, and the consumer's choice `f(S) ∈ S ∪ {none}` for every
possible assortment `S`. -/
abbrev OfflineReal (n T : ℕ) (Z : Type) :=
  (Fin T → Z) × (Fin T → Fin n → Fin (T + 1)) × (Fin T → Finset (Fin n) → Option (Fin n))

/-- A joint law `law t z` of the consumer's choices across all assortments, for a consumer of
type `z` arriving at time `t`: a probability distribution on choice functions whose marginal
at every feasible `S` is the choice model, `Pr[f(S) = i] = ϕ^z(S, i)`. -/
def ValidChoiceLaw (I : Instance n T Z)
    (law : ℕ → Z → (Finset (Fin n) → Option (Fin n)) → ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ z,
    (∀ f, 0 ≤ law t z f) ∧ (∑ f, law t z f = 1) ∧
    ∀ S ∈ I.feas, ∀ i, ∑ f ∈ Finset.univ.filter (fun f => f S = some i), law t z f = I.phi z S i

/-- Probability of an offline realization: independent types `z_t ∼ F_t` across times;
conditional on each type, independent durations `d_{t,i} ∼ g^{z_t}_i` across products
and a choice function drawn independently of those durations from `law t z_t`. -/
noncomputable def offlineProb (I : Instance n T Z)
    (law : ℕ → Z → (Finset (Fin n) → Option (Fin n)) → ℝ) (ω : OfflineReal n T Z) : ℝ :=
  ∏ k : Fin T, (I.F (k.1 + 1) (ω.1 k) * (∏ i, I.g (ω.1 k) i (ω.2.1 k i : ℕ))
    * law (k.1 + 1) (ω.1 k) (ω.2.2 k))

/-- Product `i` is rented at step `k` when the offline offers `A k`. -/
abbrev offlineRented (ω : OfflineReal n T Z) (A : Fin T → Finset (Fin n)) (k : Fin T)
    (i : Fin n) : Prop :=
  ω.2.2 k (A k) = some i ∧ i ∈ A k

/-- An offline assortment sequence is feasible on the realization `ω` if every `A k ∈ 𝒮` and
every offered product has a unit on hand: fewer than `c_i` units of `i` rented at earlier steps
`j < k` are still out (a unit rented at step `j` with duration `d` is out at steps
`j, …, j + d − 1`). -/
def OfflineFeasible (I : Instance n T Z) (ω : OfflineReal n T Z)
    (A : Fin T → Finset (Fin n)) : Prop :=
  ∀ k, A k ∈ I.feas ∧ ∀ i ∈ A k,
    (Finset.univ.filter (fun j : Fin T =>
      j < k ∧ offlineRented ω A j i ∧ k.1 < j.1 + (ω.2.1 j i : ℕ))).card < I.c i

/-- Revenue of the offline assortment sequence `A` on the realization `ω`. -/
noncomputable def offlineRev (I : Instance n T Z) (ω : OfflineReal n T Z)
    (A : Fin T → Finset (Fin n)) : ℝ :=
  ∑ k, ∑ i, if offlineRented ω A k i then I.r (ω.1 k) i else 0

/-- The optimum offline revenue on `ω`: the maximum over feasible assortment sequences (a finite,
and under `Instance.Assumptions` nonempty, set: `A ≡ ∅` is feasible). -/
noncomputable def offlineMax (I : Instance n T Z) (ω : OfflineReal n T Z) : ℝ :=
  ⨆ A : {A : Fin T → Finset (Fin n) // OfflineFeasible I ω A}, offlineRev I ω A.1

/-- The optimum offline benchmark (§EC.2, item 1, p. ec3): the expected revenue of the offline
algorithm that knows the types, the rental durations and the choices for every assortment. -/
noncomputable def optOffline (I : Instance n T Z)
    (law : ℕ → Z → (Finset (Fin n) → Option (Fin n)) → ℝ) : ℝ :=
  ∑ ω : OfflineReal n T Z, offlineProb I law ω * offlineMax I ω

end ReusableAssort.Hybrid.Supplement


