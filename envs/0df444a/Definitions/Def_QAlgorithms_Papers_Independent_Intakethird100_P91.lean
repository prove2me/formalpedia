-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P91
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P91
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:19:08.283041+00:00
-- url     : https://prove2.me/theorems/cde140ce-f7ea-43b5-b060-3c6692e7d7b1
-- title:
--   Definitions for Monotonicity of $p$-norms of multiple operators via unitary swivels
-- statement:
--   The objects the formalized statements of *Monotonicity of $p$-norms of multiple operators via unitary swivels* (arXiv:1610.01262) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsSwivelTuple`: The full-space unitary swivels of Theorem 1, PDF p.3. Each V_i commutes with its own C_i; there is no commutation requirement between distinct C_i. Both unitary identities are explicit, including on the kernel of C_i.
--   - `swivelValues`: The set of objective values in Eq.(5), PDF p.3, including the outer real power r. Its greatest element, asserted in swivelMonotonicity, is the printed maximum. No empty/unbounded real-supremum convention is used.
--   - `boundarySup`: The computed endpoint supremum M_k in Lemma 4, Eq.(26), PDF p.4. Theorem hypotheses make this real range nonempty and bounded above. Outside those hypotheses, an unbounded range has Mathlib's default sSup=0.
-- source:
--   Monotonicity of $p$-norms of multiple operators via unitary swivels, arXiv:1610.01262v1, https://arxiv.org/abs/1610.01262v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P29

/-!
Wilde, arXiv:1610.01262v1, PDF pp.3--5. Finite complex matrices implement
footnote 2 on p.4. Only pinned accepted-library interfaces are imported.
Lemma 5 and Remark 6 are exact reuses recorded in items.json; the singular
trace-exponential preview on p.2 is deferred in HARD.md and GAPS.json.
Compilation is pending the batch handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakethird100.P91

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Dependency50.P21
  (extendedLog upperLogIntegral betaDensity betaZero interpolationExponent)
open QAlgorithms.Papers.Independent.Bridge50.P29
  (positiveComplexPower orderedProduct)

/-- The full-space unitary swivels of Theorem 1, PDF p.3. Each V_i commutes
with its own C_i; there is no commutation requirement between distinct C_i.
Both unitary identities are explicit, including on the kernel of C_i. -/
def IsSwivelTuple {d L : ℕ} (C V : Fin L → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ i, (V i)ᴴ * V i = 1 ∧ V i * (V i)ᴴ = 1 ∧ C i * V i = V i * C i

/-- The set of objective values in Eq.(5), PDF p.3, including the outer
real power r. Its greatest element, asserted in swivelMonotonicity, is the
printed maximum. No empty/unbounded real-supremum convention is used. -/
def swivelValues {d L : ℕ} (C : Fin L → Matrix (Fin d) (Fin d) ℂ) (r : ℝ) : Set ℝ :=
  {x | ∃ V : Fin L → Matrix (Fin d) (Fin d) ℂ,
    IsSwivelTuple C V ∧
    x = (schattenNorm (ENNReal.ofReal r)
      (orderedProduct (fun i => positiveComplexPower (C i) (1 / (r : ℂ)) * V i))) ^ r}

/-- The computed endpoint supremum M_k in Lemma 4, Eq.(26), PDF p.4.
Theorem hypotheses make this real range nonempty and bounded above.
Outside those hypotheses, an unbounded range has Mathlib's default sSup=0. -/
def boundarySup {d : ℕ} (G : ℂ → Matrix (Fin d) (Fin d) ℂ)
    (p : ℝ≥0∞) (k : ℝ) : ℝ :=
  sSup (Set.range (fun t : ℝ => schattenNorm p (G ((k : ℂ) + (t : ℂ) * Complex.I))))

example {d L : ℕ} (C : Fin L → Matrix (Fin d) (Fin d) ℂ) :
    IsSwivelTuple C (fun _ => 1) := by
  intro i
  simp

example {d L : ℕ} (C : Fin L → Matrix (Fin d) (Fin d) ℂ) (r : ℝ) :
    (swivelValues C r).Nonempty := by
  refine ⟨_, (fun _ => 1), ?_, rfl⟩
  intro i
  simp

example {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (p : ℝ≥0∞) (k : ℝ) :
    boundarySup (fun _ => A) p k = schattenNorm p A := by
  simp [boundarySup]

end QAlgorithms.Papers.Independent.Intakethird100.P91


