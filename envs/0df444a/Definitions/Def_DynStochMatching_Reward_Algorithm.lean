-- Prove2me | Definitions.Def_DynStochMatching_Reward_Algorithm
-- name    : DynStochMatching_Reward_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T20:41:55.064997+00:00
-- url     : https://prove2.me/theorems/ee5b253b-8a2f-4538-bd62-d8322ba67433
-- title:
--   Complete reward policy and uniform complexity specifications
-- statement:
--   The algorithm solves RB once and selects the exact B.2 flow using the graph’s canonical bipartition when available, or the finite-lifetime side in the asymmetric case. A canonical partition is specified by least binary code; its implementation is required to be polynomial, rather than committing to enumeration as an implementation. Offline output includes flow, compatibility order and decomposition weights. An online decision uses two independent exact uniform samples and the current finite realization. Fixed finite register programs and uniform natural constants must compute these outputs in polynomial scalar work, with one polynomial-size offline LP and no online LP. The policy itself is the chronological execution already defined, and all reward comparisons refer to the optimum over observable policies.
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, Theorem 2, Lemma 9 and Algorithm 2, printed 21–22, 40–45 / PDF 22–23, 41–46

import Definitions.Def_DynStochMatching_Reward_Compatibility
import Definitions.Def_DynStochMatching_Reward_RealMachine

open scoped Classical

namespace DynStochMatching.Reward

/-- The least binary-coded bipartition. This specifies a canonical output, not an exponential
implementation; the machine clause asks for a polynomial implementation of this same output. -/
noncomputable def canonicalPartition {n : ℕ} (D : Instance n) : Option (Fin n → Bool) :=
  ((List.range (2 ^ n)).find? (fun k => IsBipartition D (fun i => k.testBit i.val))).map
    (fun k i => k.testBit i.val)

noncomputable def finiteSide {n : ℕ} (D : Instance n) : Fin n → Bool :=
  fun i => match D.lifetime i with | .exponential _ _ => true | .immediate => false

noncomputable def sourceDomain {n : ℕ} (D : Instance n) : Prop :=
  IsOrdinary D ∨ ∃ side, IsAsymmetric D side

noncomputable def chosenFlow {n : ℕ} (O : LinearOracle) (D : Instance n) : Flow n :=
  let x := solveRB O D
  if IsOrdinary D then
    match canonicalPartition D with
    | none => quarterFlow D x
    | some side => bipartiteFlow D x (orientSide D x side)
  else bipartiteFlow D x (finiteSide D)

noncomputable def algorithmPolicy {n : ℕ} (O : LinearOracle) (D : Instance n) : MatchingPolicy :=
  compatibilityPolicy D (chosenFlow O D)

noncomputable def instanceInput {n : ℕ} (D : Instance n) : List ℝ :=
  (List.finRange n).map D.arrivalRate ++
  (List.finRange n).map (fun i => match D.lifetime i with | .immediate => (1 : ℝ) | _ => 0) ++
  (List.finRange n).map (fun i => finiteDeathRate (D.lifetime i)) ++
  (List.finRange n).flatMap (fun i => (List.finRange n).map (D.reward i))

noncomputable def flowOutput {n : ℕ} (x : Flow n) : List ℝ :=
  (List.finRange n).flatMap (fun i => (List.finRange n).map (x.edge i)) ++
  (List.finRange n).map x.abandon ++ (List.finRange n).map x.unused

noncomputable def setupOutput {n : ℕ} (D : Instance n) (x : Flow n) : List ℝ :=
  flowOutput x ++
  (List.finRange n).flatMap (fun i => (List.range n).map (fun l =>
    match (support x i)[l]? with | some j => ((j.val + 1 : ℕ) : ℝ) | none => 0)) ++
  (List.finRange n).flatMap (fun i => (List.range n).map (decomposition D x i))

noncomputable def labelCode (n : ℕ) : VertexLabel → ℝ
  | .passive => 0
  | .active l => (l + 1 : ℕ)
  | .isolated => (n + 1 : ℕ)

abbrev AvailableAgent (n : ℕ) := Fin n × VertexLabel

noncomputable def validAvailable {n : ℕ} (x : Flow n) (a : AvailableAgent n) : Prop :=
  match a.2 with | .active l => l < (support x a.1).length | _ => True

noncomputable def onlinePartner {n : ℕ} (D : Instance n) (x : Flow n)
    (available : List (AvailableAgent n)) (j : Fin n) (label : VertexLabel) : Option ℕ :=
  if label ≠ .passive then none
  else (((available.zipIdx).filter (fun (a, _) => match a.2 with
    | .active l => j ∈ compatibility x a.1 l | _ => False)).mergeSort
      (fun (a, k) (b, h) => if D.reward a.1 j = D.reward b.1 j then
        if a.1 = b.1 then
          if labelCode n a.2 = labelCode n b.2 then k ≤ h
          else labelCode n a.2 < labelCode n b.2
        else a.1.val < b.1.val
      else D.reward a.1 j > D.reward b.1 j)).head? |>.map Prod.snd

noncomputable def onlineInput {n : ℕ} (D : Instance n) (x : Flow n)
    (available : List (AvailableAgent n)) (j : Fin n) (u v : ℝ) : List ℝ :=
  instanceInput D ++ setupOutput D x ++ [(j.val : ℝ), u, v] ++
    available.flatMap (fun a => [(a.1.val : ℝ), labelCode n a.2])

noncomputable def onlineOutput {n : ℕ} (D : Instance n) (x : Flow n)
    (available : List (AvailableAgent n)) (j : Fin n) (u v : ℝ) : List ℝ :=
  let label := labelVertex D x j u v
  [labelCode n label, match onlinePartner D x available j label with
    | none => 0 | some k => (k + 1 : ℕ)]

/-- Uniform polynomial scalar work and one polynomial-size LP for the offline construction. -/
noncomputable def polynomialFlowConstruction : Prop :=
  ∃ code : List Instruction, ∃ C d : ℕ, 0 < C ∧
    ∀ (n : ℕ) (D : Instance n) (O : LinearOracle), sourceDomain D →
      computesWithin O code [n] (instanceInput D) (flowOutput (chosenFlow O D))
        (C * (n + 1) ^ d) 1 (C * (n + 1) ^ d)

/-- The operational complexity clause covers offline construction and each online decision.
The two independent uniform samples are exact sampling primitives supplied to that decision. -/
noncomputable def polynomialPolicyImplementation : Prop :=
  ∃ offline online : List Instruction, ∃ C d : ℕ, 0 < C ∧
    ∀ (n : ℕ) (D : Instance n) (O : LinearOracle), sourceDomain D →
      computesWithin O offline [n] (instanceInput D) (setupOutput D (chosenFlow O D))
        (C * (n + 1) ^ d) 1 (C * (n + 1) ^ d) ∧
      ∀ (available : List (AvailableAgent n)) (j : Fin n) (u v : ℝ),
        (∀ a ∈ available, validAvailable (chosenFlow O D) a) →
        0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 →
        computesWithin O online [n, available.length]
          (onlineInput D (chosenFlow O D) available j u v)
          (onlineOutput D (chosenFlow O D) available j u v)
          (C * (n + available.length + 1) ^ d) 0 0

noncomputable def flowGuarantees {n : ℕ} (D : Instance n) (x : Flow n) : Prop :=
  (flowReward D x : EReal) ≥ (1 / 4 : ℝ) * optimalReward D ∧
  ((∃ side, IsBipartition D side) →
    (flowReward D x : EReal) ≥ (1 / 2 : ℝ) * optimalReward D) ∧
  ((∃ side, IsAsymmetric D side) → (flowReward D x : EReal) ≥ optimalReward D)

end DynStochMatching.Reward


