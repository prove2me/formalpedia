-- Prove2me | Definitions.Def_SkutellaCQP_MaxSNP_Supplement_PreemptAlgorithm
-- name    : SkutellaCQP_MaxSNP_Supplement_PreemptAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:47:30.630705+00:00
-- url     : https://prove2.me/theorems/aff25a4f-4f1c-4e7f-8dd6-9db86fceda24
-- title:
--   §4 — full real-time comparators and the encoded derandomization pipeline
-- statement:
--   An input consists of at least one machine, finitely many jobs, positive rational processing times, nonnegative rational release dates and nonnegative rational weights. Its binary code lists the entire data tables. A measurable preemptive comparator records the job run by each machine at each real time. Run sets are measurable, respect releases and nonnegative time, are bounded above per job, never process one job simultaneously on two machines, and satisfy
--   $$\sum_i\frac{|\{t:\text{machine }i\text{ processes }j\text{ at }t\}|}{p_{ij}}=1.$$
--   Completion is the supremum of the run times and the objective is the weighted sum of completions. Under these conditions the run measures are finite, and the supremum sets are nonempty and bounded; no integral-time optimum is assumed.
--
--   A finite output contains rational fractional slot assignments, a rational relaxation value, supported slots, and rational start times of the published nonpreemptive reconstruction. The derandomization fixes jobs by index and minimizes conditional expectations of the explicit quadratic upper bound obtained from the slot-start inequality on p. 20. Thus it uses a pessimistic estimator rather than presupposing efficient exact integration of a random maximum.
--
--   The pipeline requires a feasible published CQP′ₚ solution, additive error $2^{-q(|I|)-1}$ against every feasible relaxation value, the conditional choices, and equality of the encoded starts with the reconstructed starts. Theorem 4.5 must supply both the polynomial $q$ and an actual polynomial-time machine; they are not assumptions of this definition.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), DOI 10.1145/375827.375840, pp. 2–3, 9, 20–23; proof of Lemma 3.5, Theorem 4.5

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Supplement_Encoding
import Definitions.Def_SkutellaCQP_Preempt_Setting

namespace SkutellaCQP.MaxSNP.Supplement

open Finset MeasureTheory

/-- Computational input: all finite rational data; integer input is a special case.
Analytic schedule comparators below still have arbitrary real times. -/
structure ReleaseInput where
  m : ℕ
  n : ℕ
  machines_pos : 0 < m
  p : Fin m → Fin n → ℚ
  r : Fin m → Fin n → ℚ
  w : Fin n → ℚ
  p_pos : ∀ i j, 0 < p i j
  r_nonneg : ∀ i j, 0 ≤ r i j
  w_nonneg : ∀ j, 0 ≤ w j

/-- Binary input encoding, with the tables in lexicographic order. -/
def ReleaseInput.code (I : ReleaseInput) : List Bool :=
  natCode I.m ++ natCode I.n ++
  listCode ratCode ((List.finRange I.m).flatMap fun i => (List.finRange I.n).map (I.p i)) ++
  listCode ratCode ((List.finRange I.m).flatMap fun i => (List.finRange I.n).map (I.r i)) ++
  listCode ratCode ((List.finRange I.n).map I.w)

def ReleaseInput.pr (I : ReleaseInput) (i : Fin I.m) (j : Fin I.n) : ℝ := I.p i j

def ReleaseInput.rr (I : ReleaseInput) (i : Fin I.m) (j : Fin I.n) : ℝ := I.r i j

def ReleaseInput.wr (I : ReleaseInput) (j : Fin I.n) : ℝ := I.w j

/-- A full measurable preemptive schedule, allowing migration and arbitrary real times.
The finite-list schedule model remains the representation of algorithmic output. -/
structure MeasurablePreemptive {m n : ℕ} (p r : Fin m → Fin n → ℝ) where
  run : ℝ → Fin m → Option (Fin n)
  measurable : ∀ i j, MeasurableSet {t | run t i = some j}
  released : ∀ t i j, run t i = some j → 0 ≤ t ∧ r i j ≤ t
  job_exclusive : ∀ t i h j, run t i = some j → run t h = some j → i = h
  bounded : ∀ j, ∃ T : ℝ, ∀ t i, run t i = some j → t ≤ T
  total : ∀ j, ∑ i, (volume {t | run t i = some j}).toReal / p i j = 1

/-- Full-measurable-schedule completion time. On the feasible positive-processing domain the
set is nonempty, bounded above, and bounded below by 0. No integer-time optimum is assumed. -/
noncomputable def MeasurablePreemptive.completion {m n : ℕ} {p r : Fin m → Fin n → ℝ}
    (P : MeasurablePreemptive p r) (j : Fin n) : ℝ :=
  sSup {t | ∃ i, P.run t i = some j}

noncomputable def MeasurablePreemptive.value {m n : ℕ} {p r : Fin m → Fin n → ℝ}
    (P : MeasurablePreemptive p r) (w : Fin n → ℝ) : ℝ :=
  ∑ j, w j * P.completion j

/-- A finite rational CQP solution plus a slot assignment. Shape and support are separately
checked, so no default `getD` value can create an unencoded schedule. -/
structure DeroundOutput where
  a : List ℚ
  Z : ℚ
  machine : List ℕ
  slot : List ℕ
  start : List ℚ

/-- Output encoding. -/
def DeroundOutput.code (o : DeroundOutput) : List Bool :=
  listCode ratCode o.a ++ ratCode o.Z ++ listCode natCode o.machine ++ listCode natCode o.slot ++ listCode ratCode o.start

/-- Required shape of a finite output. -/
def DeroundOutput.Shape (I : ReleaseInput) (o : DeroundOutput) : Prop :=
  o.a.length = I.m * I.n * I.n ∧ o.machine.length = I.n ∧ o.slot.length = I.n ∧ o.start.length = I.n ∧
  (∀ j : Fin I.n, o.machine[j.val]?.getD 0 < I.m) ∧
  (∀ j : Fin I.n, o.slot[j.val]?.getD 0 < I.n)

/-- Lexicographic table of a fractional slot assignment. -/
def DeroundOutput.frac (I : ReleaseInput) (o : DeroundOutput)
    (i : Fin I.m) (k j : Fin I.n) : ℝ :=
  (o.a[(i.val * I.n + k.val) * I.n + j.val]?.getD 0 : ℚ)

/-- The encoded slot assignment. Out-of-shape indices are mapped into range solely to keep
this total; every algorithm assertion requires `Shape`. -/
def DeroundOutput.slots (I : ReleaseInput) (o : DeroundOutput) (j : Fin I.n) : Fin I.m × Fin I.n :=
  (⟨o.machine[j.val]?.getD 0 % I.m, Nat.mod_lt _ I.machines_pos⟩,
   ⟨o.slot[j.val]?.getD 0 % I.n, Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt)⟩)

/-- Pointwise upper bound on the reconstructed value from the proof on p. 20:
replace a slot's starting time by its release plus all earlier-slot processing on that
machine. This quadratic pessimistic estimator has efficiently computable conditional
expectations; it avoids requiring exact evaluation of a maximum of random workloads. -/
noncomputable def pessimisticValue (I : ReleaseInput)
    (τ : Fin I.n → Fin I.m × Fin I.n) : ℝ :=
  ∑ j, I.wr j * (SkutellaCQP.RelDates.rho I.rr (τ j).1 (τ j).2 + I.pr (τ j).1 j +
    (∑ k ∈ univ.filter (fun k => k ≠ j ∧ (τ k).1 = (τ j).1 ∧ (τ k).2 < (τ j).2),
      I.pr (τ j).1 k) +
    (∑ k ∈ univ.filter (fun k => τ k = τ j ∧ SkutellaCQP.NoRel.prec I.pr I.wr (τ j).1 k j),
      I.pr (τ j).1 k))

/-- Conditional expectation after fixing the first `t` jobs, for independent slot rounding.
The expectation is of the explicit pessimistic estimator from p. 20, not a performance assumption. -/
noncomputable def conditionalValue (I : ReleaseInput) (a : Fin I.m → Fin I.n → Fin I.n → ℝ)
    (τ : Fin I.n → Fin I.m × Fin I.n) (t : ℕ) : ℝ :=
  ∑ σ ∈ univ.filter (fun σ : Fin I.n → Fin I.m × Fin I.n =>
    ∀ j : Fin I.n, j.val < t → σ j = τ j),
    (∏ j ∈ univ.filter (fun j : Fin I.n => t ≤ j.val), a (σ j).1 (σ j).2 j) *
      pessimisticValue I σ

/-- The method of conditional probabilities: choose a supported slot minimizing the
next conditional expectation, processing jobs by index. -/
def ConditionalGreedy (I : ReleaseInput) (a : Fin I.m → Fin I.n → Fin I.n → ℝ)
    (τ : Fin I.n → Fin I.m × Fin I.n) : Prop :=
  ∀ j : Fin I.n, 0 < a (τ j).1 (τ j).2 j ∧
    ∀ x : Fin I.m × Fin I.n, 0 < a x.1 x.2 j →
      conditionalValue I a τ (j.val + 1) ≤
        conditionalValue I a (Function.update τ j x) (j.val + 1)

/-- The pipeline must actually find a near-optimal feasible CQP solution and perform
conditional-expectation rounding. The accuracy polynomial is existentially supplied by
Theorem 4.5, and is not inferred from an integral preemptive optimum. -/
def PreemptPipeline (q : Polynomial ℕ) (A : ReleaseInput → DeroundOutput) : Prop :=
  ∀ I, let o := A I
    o.Shape I ∧
    SkutellaCQP.Preempt.CQPpFeasible I.pr I.wr I.rr (o.frac I) (o.Z : ℝ) ∧
    (∀ a Y, SkutellaCQP.Preempt.CQPpFeasible I.pr I.wr I.rr a Y →
      (o.Z : ℝ) ≤ Y + 1 / (2 : ℝ) ^ (q.eval I.code.length + 1)) ∧
    ConditionalGreedy I (o.frac I) (o.slots I) ∧
    (∀ j : Fin I.n, ((o.start[j.val]?.getD 0 : ℚ) : ℝ) =
      SkutellaCQP.RelDates.Cslot I.pr I.wr I.rr (o.slots I) j - I.pr ((o.slots I j).1) j)

end SkutellaCQP.MaxSNP.Supplement


