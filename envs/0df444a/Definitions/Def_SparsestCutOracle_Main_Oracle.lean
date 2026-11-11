-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Oracle
-- name    : SparsestCutOracle_Main_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:45:12.342021+00:00
-- url     : https://prove2.me/theorems/e5ae892a-7186-4c2a-a673-2e31b3ecb742
-- title:
--   Exact and approximate oracle contracts and feedback evaluation
-- statement:
--   An exact response is algebraically valid and has a bounded amount of added capacity. For an approximate Gram matrix $\widetilde X$, validity is tested against $\widetilde X$, while the relaxed feedback guarantee is tested against the exact matrix $X$:
--
--   $$Z\mathbin\bullet X\ge-\alpha/10.$$
--
--   The approximation program sees the exponent matrix only through charged matrix-vector calls. The oracle receives only the approximate coordinates and the graph data. A separate ordinary charged program must multiply the stored feedback matrix by any new vector in $\widetilde O(m+n)$ work; it is given neither a feedback oracle nor a precomputed product. These separate interfaces preserve Lemma 10's information restriction and running-time clause.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 18–20, 25–26, 57–60, Theorem 6 and Lemma 10

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_MMW

namespace SparsestCutOracle.Main

noncomputable def OracleOutcome {n cP : ℕ} (G : Graph n) (π : Fin n → ℝ)
    (X : Mat n) (α β κ Cq Cadd Cwidth : ℝ) (out : State) : Prop :=
  (outInt out 0 = 0 ∧ BalancedSparse G π α κ β Cq (procCut n out)) ∨
  ∃ r : Response n cP, EncodedResponse out r ∧ ValidResponse G.toWGraph π X α β Cadd r ∧
    Width π (Cwidth * (α / totalWeight π) * Real.log n ^ 2) (feedback π α r)

/-- Approximate vectors are retained at positive output addresses; certificate data stay negative. -/
noncomputable def approximateDimension (s : State) : ℕ := (s.base.integerMemory 0).toNat

noncomputable def approximateGram (n : ℕ) (s : State) : Mat n :=
  fun i j => ∑ k ∈ Finset.range (approximateDimension s),
    s.base.core.mem (1 + i.val * approximateDimension s + k) *
      s.base.core.mem (1 + j.val * approximateDimension s + k)

/-- An ordinary machine gets the stored certificate (negative cells), n,m, and a new vector u.
It receives neither a precomputed matrix-vector product nor an oracle for the feedback matrix. -/
noncomputable def feedbackInput {n : ℕ} (m : ℕ) (certificate : State) (u : Fin n → ℝ) : State :=
  let s := init [(n : ℤ), (m : ℤ)] ((List.finRange n).map u)
  { s with base := { s.base with
    integerMemory := fun z => if z < 0 then certificate.base.integerMemory z else s.base.integerMemory z
    core := { s.base.core with
      mem := fun z => if z < 0 then certificate.base.core.mem z else s.base.core.mem z } } }

def FeedbackEvaluator {n : ℕ} (M : Program) (m : ℕ) (certificate : State) (Z : Mat n)
    (C : ℝ) (c : ℕ) : Prop :=
  ∀ (u : Fin n → ℝ) (ω : Tape),
    ∃ t : ℕ, (run M (feedbackInput m certificate u) ω t).base.halted = true ∧
      ((run M (feedbackInput m certificate u) ω t).base.work : ℝ) ≤
        C * ((m : ℝ) + n) * (1 + Real.log n) ^ c ∧
      ∀ i : Fin n,
        (run M (feedbackInput m certificate u) ω t).base.core.mem (-1 - (i.val : ℤ)) =
          ∑ j, Z i j * u j

noncomputable def ApproximateOutcome {n cP : ℕ} (G : Graph n) (π : Fin n → ℝ)
    (X Xtilde : Mat n) (α β κ Cq Cadd Cwidth : ℝ)
    (M : Program) (Cmul : ℝ) (cmul : ℕ) (out : State) : Prop :=
  (outInt out 0 = 0 ∧ BalancedSparse G π α κ β Cq (procCut n out)) ∨
  ∃ r : Response n cP, EncodedResponse out r ∧
    ValidResponse G.toWGraph π Xtilde α β Cadd r ∧
    Width π (Cwidth * (α / totalWeight π) * Real.log n ^ 2) (feedback π α r) ∧
    -α / 10 ≤ dot (feedback π α r) X ∧
    FeedbackEvaluator M G.length out (feedback π α r) Cmul cmul

/-- A Gram representation supplied as actual input coordinates, with no exact iterate supplied. -/
def coordsGram {n r : ℕ} (v : Fin n → Fin r → ℝ) : Mat n :=
  fun i j => ∑ k, v i k * v j k

noncomputable def approximateOracleInput {n r : ℕ} (G : Graph n) (π : Fin n → ℝ)
    (v : Fin n → Fin r → ℝ) (κ α β : ℝ) : State :=
  init (graphInts G ++ [(r : ℤ)])
    (graphReals G π ([κ, α, β] ++
      ((List.finRange n).flatMap fun i => (List.finRange r).map (v i))))

/-- A charged matrix-vector sketch, with fixed accuracy cγ/log n. -/
def SketchGuarantee (S : Procedure) (a : ℕ) (pL : ℕ) (KL cγ C Cr : ℝ) (c : ℕ) : Prop :=
  ∀ (n : ℕ) (π : Fin n → ℝ) (A : Mat n) (L : ℝ) (tA : ℕ),
    2 ≤ n → (∀ i, 0 < π i) → A.IsSymm → 0 ≤ L → Width (fun _ => 1) L A →
    L ≤ KL * (1 + Real.log n) ^ pL → 1 ≤ tA →
    let γ := cγ / Real.log n
    let input := gramInput π L γ
    let V : MatvecContext := ⟨n, A, tA⟩
    (∀ O : FairService, ∀ ω : Tape, ProcHalts S O V input ω ∧
      let out := procFinal S O V input ω
      (out.machine.base.work : ℝ) ≤ C * ((tA : ℝ) + n) * (1 + Real.log n) ^ c ∧
      (vectorDimension out.machine : ℝ) ≤ Cr * γ⁻¹ ^ 2 * Real.log n ∧
      dot (D π) (vectorGram n out.machine) = totalWeight π) ∧
    ∀ O : FairService, ProcHighProbability n a S O V input
      (fun out => GramAccuracy π (exponentialGram π A) (vectorGram n out.machine) γ)

end SparsestCutOracle.Main


