-- Prove2me | Definitions.Def_SampQueryLB_WarmSLC_Measurement
-- name    : SampQueryLB_WarmSLC_Measurement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:14:12.00619+00:00
-- url     : https://prove2.me/theorems/f2e5a71c-726f-43ee-b4b7-b4bc386049bc
-- title:
--   §3 — adaptive linear measurement processes of a hidden Gaussian vector, with labels, and the shared and independent models $P^{sh}$, $P^{ind}$
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space and $\Xi\sim N(0,I_E)$, sampled once; a seed $\omega$ lives in a measurable space $O$ with law $\mu_O$, independent of $\Xi$. A $q$-round **adaptive linear measurement process** with batch sizes $m_1,\dots,m_q$ (Definition 3.1) is given by Borel maps $B_k$ choosing the batch of measurement vectors $(a_{k,1},\dots,a_{k,m_k})=B_k(\omega,Z_1,\dots,Z_{k-1})\in E^{m_k}$, and the measurements are $Z_k=(\langle\Xi,a_{k,1}\rangle,\dots,\langle\Xi,a_{k,m_k}\rangle)$. As in §3.3, each round also carries a Borel label $\ell_k=L_k(\omega,Z_1,\dots,Z_{k-1})\in\{\mathrm{local},\mathrm{far}\}$.
--
--   In the **shared model** every batch measures the same $\Xi$; in the **independent model** local batches measure $\Xi^{\mathrm{local}}$ and far batches an independent copy $\Xi^{\mathrm{far}}$, both $N(0,I_E)$ and independent of $\omega$. $P^{sh}$ and $P^{ind}$ are the laws of the full transcript $(\omega,Z_1,\dots,Z_q)$ in the two models. For a seed value $\omega$ and any record $z=(z_1,\dots,z_q)$, $L(\omega,z)$ and $F(\omega,z)$ are the spans of the local and of the far measurement vectors evaluated along $z$.
--
--   **Formalization Note.** A record is `z : (k : Fin q) → Fin (m k) → ℝ`. The maps take the seed and the whole record but may not depend on the entries of rounds $\ge k$ (non-anticipation), which is the paper's dependence on $(\omega,Z_1,\dots,Z_{k-1})$. `record ω ξl ξf` is the unique record consistent with measuring local batches against `ξl` and far ones against `ξf`, obtained by $q$ iterations of one round of measurements from $0$. Labels are Booleans (`true` = local). A terminal batch (Remark 3.2) is one more round. Return maps, the algorithm's transcript and its output are Borel functions of the full transcript, so the theorems quantify over all measurable functions of it.
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), pp. 15–19, §3.1 (Definition 3.1, oracle simulation, Remark 3.2), §3.3

import Mathlib

/-!
# Adaptive linear measurement processes and the shared / independent models (§3)

Zhou, Suzuki, arXiv:2611.05813 (held version dated November 3, 2026), pp. 15–19
(Definition 3.1, oracle simulation, Remark 3.2, §3.3).

Conventions.
* `E` is a finite-dimensional real inner product space, the hidden vector is `Ξ ∼ N(0, I_E)`
  (`stdGaussian E`), and the seed lives in a measurable space `O` (standard Borel in the
  theorems) with a law `μO`, independent of `Ξ`.
* There are `q` rounds with batch sizes `m k`; a measurement record is
  `z : (k : Fin q) → Fin (m k) → ℝ` (`Rec q m`), so `z k` is the batch `Z_k`. A terminal batch
  (Remark 3.2) is simply one more round.
* The batch map of round `k` and its label (`true` = local, `false` = far) take the seed and the
  whole record, and are required not to depend on the entries of rounds `≥ k` (non-anticipation);
  this is the paper's `B_k(ω, Z_1, …, Z_{k−1})`, `L_k(ω, Z_1, …, Z_{k−1})`.
* `record ω ξl ξf` is the full record when local batches measure `ξl` and far batches `ξf`: the
  unique fixed point of one round of measurements, reached after `q` iterations from `0`.
* `shLaw` is the law `P^sh` of the full transcript `(ω, Z_1, …, Z_q)` when both groups measure
  the same `Ξ`; `indLaw` is `P^ind`, when they measure independent copies `Ξ^local`, `Ξ^far`.
* The return maps of an oracle simulation and the algorithm's transcript and output are Borel
  functions of the full transcript; the theorems quantify over every measurable function of it.
-/

namespace SampQueryLB.WarmSLC

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable section

/-- Measurement records of a `q`-round process with batch sizes `m`. -/
abbrev Rec (q : ℕ) (m : Fin q → ℕ) := (k : Fin q) → Fin (m k) → ℝ

/-- A `q`-round adaptive linear measurement process with labels (Definition 3.1, §3.3). -/
structure MeasProcess (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] (O : Type*) [MeasurableSpace O] (q : ℕ) (m : Fin q → ℕ) where
  /-- The measurement vectors `(a_{k,1}, …, a_{k,m_k}) = B_k(ω, Z_1, …, Z_{k−1})`. -/
  batch : (k : Fin q) → O × Rec q m → Fin (m k) → E
  /-- The label `L_k(ω, Z_1, …, Z_{k−1})`: `true` for local, `false` for far. -/
  label : (k : Fin q) → O × Rec q m → Bool
  batch_measurable : ∀ k, Measurable (batch k)
  label_measurable : ∀ k, Measurable (label k)
  batch_nonanticipating : ∀ k ω (z z' : Rec q m), (∀ j, j < k → z j = z' j) →
    batch k (ω, z) = batch k (ω, z')
  label_nonanticipating : ∀ k ω (z z' : Rec q m), (∀ j, j < k → z j = z' j) →
    label k (ω, z) = label k (ω, z')

namespace MeasProcess

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {O : Type*} [MeasurableSpace O] {q : ℕ} {m : Fin q → ℕ}

/-- One round of measurements of the whole record: round `k` is measured against `ξl` if it is
labelled local and against `ξf` otherwise. -/
def step (P : MeasProcess E O q m) (ω : O) (ξl ξf : E) (z : Rec q m) : Rec q m :=
  fun k b => if P.label k (ω, z) then ⟪ξl, P.batch k (ω, z) b⟫ else ⟪ξf, P.batch k (ω, z) b⟫

/-- The full record `(Z_1, …, Z_q)` with local batches measured against `ξl` and far batches
against `ξf` (the fixed point of `step`, reached after `q` iterations by non-anticipation). -/
def record (P : MeasProcess E O q m) (ω : O) (ξl ξf : E) : Rec q m :=
  (P.step ω ξl ξf)^[q] 0

/-- `P^sh`: the law of `(ω, Z_1, …, Z_q)` when both groups measure the same `Ξ ∼ N(0, I_E)`. -/
def shLaw [FiniteDimensional ℝ E] [BorelSpace E] (P : MeasProcess E O q m) (μO : Measure O) :
    Measure (O × Rec q m) :=
  (μO.prod (stdGaussian E)).map (fun p => (p.1, P.record p.1 p.2 p.2))

/-- `P^ind`: the law of `(ω, Z_1, …, Z_q)` when local batches measure `Ξ^local` and far batches an
independent copy `Ξ^far`. -/
def indLaw [FiniteDimensional ℝ E] [BorelSpace E] (P : MeasProcess E O q m) (μO : Measure O) :
    Measure (O × Rec q m) :=
  (μO.prod ((stdGaussian E).prod (stdGaussian E))).map
    (fun p => (p.1, P.record p.1 p.2.1 p.2.2))

/-- `L(ω, z)`: the span of the local measurement vectors evaluated along `z`. -/
def localSpan (P : MeasProcess E O q m) (ω : O) (z : Rec q m) : Submodule ℝ E :=
  Submodule.span ℝ {a | ∃ k b, P.label k (ω, z) = true ∧ P.batch k (ω, z) b = a}

/-- `F(ω, z)`: the span of the far measurement vectors evaluated along `z`. -/
def farSpan (P : MeasProcess E O q m) (ω : O) (z : Rec q m) : Submodule ℝ E :=
  Submodule.span ℝ {a | ∃ k b, P.label k (ω, z) = false ∧ P.batch k (ω, z) b = a}

end MeasProcess

end

end SampQueryLB.WarmSLC


