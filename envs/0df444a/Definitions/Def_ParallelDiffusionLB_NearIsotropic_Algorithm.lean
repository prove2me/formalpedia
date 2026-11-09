-- Prove2me | Definitions.Def_ParallelDiffusionLB_NearIsotropic_Algorithm
-- name    : ParallelDiffusionLB_NearIsotropic_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:12.425236+00:00
-- url     : https://prove2.me/theorems/a229684c-c93c-4ce6-851c-7c87e00b436e
-- title:
--   Measurable adaptive parallel algorithms and their output laws
-- statement:
--   An algorithm has a seed $\omega$ in an arbitrary measurable probability space, $R\ge0$ adaptive rounds, and $P$ query slots in each round. Round $r$ chooses its entire batch as a measurable function of the seed and the answers from rounds strictly before $r$. Its output is a measurable function of the seed and all $R$ answer batches. Query and response spaces are abstract; diffusion sampling instantiates them by $\mathbb R^d\times(0,\infty)$ and $\mathbb R^d$.
--
--   The recursive interaction computes the answer transcript and output for a sequence of round oracles. For a fixed oracle $o$ and independent seed law $\nu$, the output law is
--   $$Q_o^A=\operatorname{Law}_{\omega\sim\nu}(A^o(\omega)).$$
--   Exactly $P$ slots represent at most $P$ queries by padding unused slots with legal queries whose answers are ignored. There is no computational restriction and no restriction on how query locations or noise levels vary within a batch. The structural measurability lemmas ensure that measurable oracles give genuine measurable output maps.
--
--   This interface is shared by the main lower bound and generic progressive simulation.
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, §2.2, p. 6; Lemma A.13, p. 27

import Mathlib

open MeasureTheory
noncomputable section
universe u v w z

namespace ParallelDiffusionLB.NearIsotropic

/-- The answers to the preceding `r` batches, each with `P` slots. -/
abbrev History (Ans : Type v) (P r : ℕ) := Fin r → Fin P → Ans

/-- General finite-round adaptive parallel algorithm (§2.2).
Exactly P slots encode at most P queries by repetition; all randomness is in the seed.
No constraint is imposed on computation or on the measurable batch maps. -/
structure ParallelAlgorithm (Q : Type u) (Ans : Type v) (Out : Type w)
    (Ω : Type z) [MeasurableSpace Q] [MeasurableSpace Ans]
    [MeasurableSpace Out] [MeasurableSpace Ω] (P R : ℕ) where
  batch : (r : Fin R) → Ω × History Ans P r.val → Fin P → Q
  batch_measurable : ∀ r, Measurable (batch r)
  output : Ω × History Ans P R → Out
  output_measurable : Measurable output

namespace ParallelAlgorithm
variable {Q : Type u} {Ans : Type v} {Out : Type w} {Ω : Type z}
  [MeasurableSpace Q] [MeasurableSpace Ans] [MeasurableSpace Out] [MeasurableSpace Ω]
  {P R : ℕ}

/-- Execute a prefix with the same seed, allowing a distinct oracle in each round. -/
def run (A : ParallelAlgorithm Q Ans Out Ω P R) (o : Fin R → Q → Ans) (ω : Ω) :
    (r : ℕ) → r ≤ R → History Ans P r
  | 0, _ => Fin.elim0
  | r+1, h =>
    let past := A.run o ω r (by omega)
    Fin.lastCases (fun p => o ⟨r, by omega⟩ (A.batch ⟨r, by omega⟩ (ω,past) p)) past

/-- Actual or progressive answer transcript. Queries are reconstructed from this and the seed. -/
def transcript (A : ParallelAlgorithm Q Ans Out Ω P R) (o : Fin R → Q → Ans)
    (ω : Ω) : History Ans P R := A.run o ω R le_rfl

def result (A : ParallelAlgorithm Q Ans Out Ω P R) (o : Fin R → Q → Ans) (ω : Ω) : Out :=
  A.output (ω, A.transcript o ω)

/-- Structural measurability, derived from the batch maps and measurable oracles. -/
theorem run_measurable (A : ParallelAlgorithm Q Ans Out Ω P R)
    (o : Fin R → Q → Ans) (ho : ∀ r, Measurable (o r)) :
    ∀ r (h : r ≤ R), Measurable (fun ω => A.run o ω r h) := by
  intro r
  induction r with
  | zero => intro h; exact measurable_pi_lambda _ (fun i => Fin.elim0 i)
  | succ r ih =>
    intro h
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · apply measurable_pi_lambda
      intro p
      simpa only [run, Fin.lastCases_last, Function.comp_def, id_eq] using (ho ⟨r, by omega⟩).comp ((measurable_pi_apply p).comp
        ((A.batch_measurable ⟨r, by omega⟩).comp (measurable_id.prodMk (ih (by omega)))))
    · simpa only [run, Fin.lastCases_castSucc, Function.comp_def] using (measurable_pi_apply j).comp (ih (by omega))

theorem result_measurable (A : ParallelAlgorithm Q Ans Out Ω P R)
    (o : Fin R → Q → Ans) (ho : ∀ r, Measurable (o r)) : Measurable (A.result o) :=
  A.output_measurable.comp (measurable_id.prodMk (A.run_measurable o ho R le_rfl))

/-- Output law for a fixed oracle, averaging only over the independent seed. -/
def outputLaw (A : ParallelAlgorithm Q Ans Out Ω P R) (ν : Measure Ω) (o : Q → Ans) :
    Measure Out := ν.map (A.result (fun _ => o))

end ParallelAlgorithm
end ParallelDiffusionLB.NearIsotropic


