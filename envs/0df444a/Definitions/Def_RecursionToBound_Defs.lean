-- Prove2me | Definitions.Def_RecursionToBound_Defs
-- name    : RecursionToBound_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:43:31.215786+00:00
-- url     : https://prove2.me/theorems/12be43a1-1d4f-407c-8380-1a7fe8a5aa49
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Count_Defs
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_SparsificationLemma_StepSparsifyDefs
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_PairsToBound_Defs
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace RecursionToBound
open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
def epsOf (r : ℕ × ℕ) : ℚ := min ((r.1 : ℚ) / (r.2 : ℚ)) 1
def widthOr3F (ψ : Fml) : ℕ := max 3 (StepSparsify.widthOf ψ)
def thresholds (k : ℕ) (r : ℕ × ℕ) : ℕ → ℕ := Cal.thetaC (Cal.alphaC k (epsOf r))
def occBound (k : ℕ) (r : ℕ × ℕ) : ℕ := 2 * (∑ j ∈ range k, thresholds k r j) + 2
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
def countOutput (k : ℕ) (pad : U) (i : Idx) (n : ℕ) (x : CNode) : ℕ :=
  bif (out x).isEmpty then 2 ^ n else countD S k pad i n (StepSparsify.DeltaOf n (out x)) (out x)
def countAll (k : ℕ) (r : ℕ × ℕ) (i : Idx) (d : U × Fml) (pad : U) : ℕ :=
  bif hasNil d.2 then 0 else _root_.StepSparsify.walkSG (thresholds k r) k pad (countOutput S k pad i d.1.length) (rootC (d.1, noTaut d.2))
def needAt (k : ℕ) (i : Idx) (n Δ : ℕ) : ℕ :=
  needNet S i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) (BbD k n) + Nat.size (nPrMax (S.K i) n Δ) + Nat.size (8 * (10 * n + 1) * (sbMax Δ + 1) * (Nat.size (Δ * n) + 2) + 8)
def needAtC (b : U) (k : ℕ) (i : Idx) (n Δ : ℕ) : Option ℕ :=
  (needNetC S b i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) (BbD k n)).map fun v =>
    v + Nat.size (nPrMax (S.K i) n Δ) + Nat.size (8 * (10 * n + 1) * (sbMax Δ + 1) * (Nat.size (Δ * n) + 2) + 8)
def deltas (k : ℕ) (r : ℕ × ℕ) (n : ℕ) : List ℕ := (List.range (min (occBound k r) (n + 1) - 1)).map (· + 2)
def needOutputs (k : ℕ) (r : ℕ × ℕ) (i : Idx) (n : ℕ) : ℕ := ((deltas k r n).map (needAt S k i n)).foldr max 0
def needOutputsC (b : U) (k : ℕ) (r : ℕ × ℕ) (i : Idx) (n : ℕ) : Option ℕ :=
  (deltas k r n).foldr (fun Δ o => o.bind fun v => (needAtC S b k i n Δ).map (max v)) (some 0)
end
def needWalk (k : ℕ) (r : ℕ × ℕ) (n : ℕ) : ℕ :=
  (⌈epsOf r * n⌉₊ + 2) + Nat.size (stackLenCU k (32 * Cal.alphaC k (epsOf r)) n (inLen k n))
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
def planAt (n₁ k n : ℕ) (i : Idx) (r : ℕ × ℕ) : Option ℕ :=
  if n₁ ≤ n then (needOutputsC S (List.replicate n ()) k r i n).bind fun v => if v + needWalk k r n ≤ n then some (v + needWalk k r n) else none
  else none
def widthU (x : List Bool) : ℕ := widthOr3F (fmlOf x).2
def numU (pick : U → U × Idx) (num : U × U → ℕ × ℕ) (x : List Bool) : ℕ × ℕ :=
  num ((pick (root17 (nU x))).1, List.replicate (S.K (idxU pick x)) ())
def plan (n₁ : ℕ) (pick : U → U × Idx) (num : U × U → ℕ × ℕ) (x : List Bool) : Option ℕ :=
  planAt S n₁ (kcU (widthU x) (nU x)) (nU x) (idxU pick x) (numU S pick num x)
def expo (n₁ : ℕ) (pick : U → U × Idx) (num : U × U → ℕ × ℕ) (x : List Bool) : ℕ := (plan S n₁ pick num x).getD (nU x)
def count (n₁ : ℕ) (pick : U → U × Idx) (num : U × U → ℕ × ℕ) (p : List Bool × U) : List Bool :=
  outW (fmlOf p.1, bif (plan S n₁ pick num p.1).isNone then bruteU p
    else countAll S (kcU (widthU p.1) (nU p.1)) (numU S pick num p.1) (idxU pick p.1) (fmlOf p.1) p.2)
end
def ThmVariablesAWithNumberBetween : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ (M : TM2ComputableAux Bool Bool) (C' : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ThmVariablesAFor S Q M C'
def ThmVariablesAForEveryMachine : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ n₀ : ℕ, ∀ n₁ : ℕ, n₀ ≤ n₁ → (∃ (M : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Computes M (count S n₁ Q.pick num) (expo S n₁ Q.pick num) q) ∧
      ∀ (M : TM2ComputableAux Bool Bool) (q : ℕ), Computes M (count S n₁ Q.pick num) (expo S n₁ Q.pick num) q → ∃ C' : ℕ, ThmVariablesAFor S Q M C'
def WalkTreeIsSparsify : Prop :=
  ∀ (k n D : ℕ) (r : ℕ × ℕ) (ψ : Sparsify.PFml), 3 ≤ k → 0 < r.1 → 0 < r.2 → IsKCNF k n ψ → Cal.depthC (Cal.alphaC k (epsOf r)) k n ≤ D →
    (Sparsify.leaves (stepC (thresholds k r) k) D (rootC (List.replicate n (), noTaut ψ))).map out = Cal.sparsify k n (epsOf r) ψ
def OutputsAreFew : Prop :=
  ∀ (k n : ℕ) (r : ℕ × ℕ) (e : ℝ) (ψ : Sparsify.PFml), 3 ≤ k → 0 < e → e ≤ 1 → e ≤ (r.1 : ℝ) / r.2 → (r.1 : ℝ) / r.2 ≤ 2 * e → IsKCNF k n ψ →
    e ≤ ((epsOf r : ℚ) : ℝ) ∧ ((epsOf r : ℚ) : ℝ) ≤ 2 * e ∧ ((epsOf r : ℚ) : ℝ) ≤ 1 ∧
    ((Cal.sparsify k n (epsOf r) ψ).length : ℝ) ≤ (2 : ℝ) ^ (((epsOf r : ℚ) : ℝ) * n) ∧ (2 : ℝ) ^ (((epsOf r : ℚ) : ℝ) * n) ≤ (2 : ℝ) ^ (2 * e * n)
def OutputsAreWithinTheSetting : Prop :=
  ∀ C₀ : ℕ, 1 ≤ C₀ → ∃ n₁ : ℕ, ∀ (k n Δ : ℕ) (r : ℕ × ℕ) (e : ℝ), n₁ ≤ n → 3 ≤ k → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n → 1 / MainTheoremForms.lg n ^ C₀ ≤ e → e ≤ 1 → e ≤ (r.1 : ℝ) / r.2 → (r.1 : ℝ) / r.2 ≤ 2 * e →
    2 ≤ Δ → Δ ≤ occBound k r →
      MainTheoremForms.lg Δ ≤ 3 * k * MainTheoremForms.lg (8 * k / e) + 2 ∧ (Δ : ℝ) ≤ MainTheoremForms.lg n ^ (4 * k * C₀) ∧
      (3 * k * MainTheoremForms.lg (8 * k / e) + 2 ≤ 3 * k * (3 + (C₀ + 1 / 4) * MainTheoremForms.lg (MainTheoremForms.lg n)) + 2 ∧ 3 * (k : ℝ) * (3 + (C₀ + 1 / 4) * MainTheoremForms.lg (MainTheoremForms.lg n)) + 2 ≤ 4 * k * C₀ * MainTheoremForms.lg (MainTheoremForms.lg n)) ∧
      Δ ≤ n + 1 ∧ 29 * LD Δ + 19 ≤ n
def OwnDeltaIsBounded : Prop :=
  ∀ (k n : ℕ) (r : ℕ × ℕ) (ψ : Sparsify.PFml), 3 ≤ k → 0 < r.1 → 0 < r.2 → IsKCNF k n ψ → ∀ Φ ∈ Cal.sparsify k n (epsOf r) ψ, StepSparsify.DeltaOf n Φ ≤ occBound k r
def OccBoundIsThePrinted : Prop :=
  ∀ (k : ℕ) (r : ℕ × ℕ), 3 ≤ k → 0 < r.1 → 0 < r.2 → (occBound k r : ℝ) ≤ 2 * (8 * (k : ℝ) / ((epsOf r : ℚ) : ℝ)) ^ (3 * k) + 2
def BoundsGrowWithDelta : Prop :=
  ∀ k K n Δ Δ' : ℕ, Δ ≤ Δ' → UbD k K n Δ ≤ UbD k K n Δ' ∧ PbD K n Δ ≤ PbD K n Δ' ∧ nPrMax K n Δ ≤ nPrMax K n Δ' ∧ sbMax Δ ≤ sbMax Δ'
def OneOutputCost : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly →
    ∃ A n₁ : ℕ, ∀ k n l Δ : ℕ, n₁ ≤ n → IsLevel S Q n l → 3 ≤ k → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n → 2 ≤ Δ → (Δ : ℝ) ≤ MainTheoremForms.lg n ^ (4 * k * C₀) →
      (needAt S k (Q.idx l) n Δ : ℝ) ≤ A * e l * k * n * MainTheoremForms.lg Δ
def WalkCost : Prop :=
  ∃ c : ℕ, ∀ (k n : ℕ) (r : ℕ × ℕ), 3 ≤ k → 2 ≤ n → 0 < r.1 → 0 < r.2 →
    (needWalk k r n : ℝ) ≤ ((epsOf r : ℚ) : ℝ) * n + c * k * (MainTheoremForms.lg n + MainTheoremForms.lg (8 * k / ((epsOf r : ℚ) : ℝ)))
def ExponentIsWithinTheBound : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ A n₁ : ℕ, ∀ k n l : ℕ, n₁ ≤ n → IsLevel S Q n l → 3 ≤ k → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n →
      ((needOutputs S k (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) (Q.idx l) n + needWalk k (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) n : ℕ) : ℝ) ≤ A * expVariablesA k n (e l)
def PlanFailsOnlyAboveN : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (n₁ k n : ℕ) (i : Idx) (r : ℕ × ℕ),
    (∀ v, planAt S n₁ k n i r = some v → n₁ ≤ n ∧ v = needOutputs S k r i n + needWalk k r n ∧ v ≤ n) ∧
    (planAt S n₁ k n i r = none → n₁ ≤ n → n < needOutputs S k r i n + needWalk k r n)
def CutOffIsIdle : Prop := ∀ k n : ℕ, 1 ≤ n → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n → kcU k n = k
def WidthOnTheCode : Prop :=
  (∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → widthU (SatM.enc k φ) = PairsToBound.widthOr3 φ) ∧
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (num : U × U → ℕ × ℕ) (k n l : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → IsLevel S Q n l →
    numU S Q.pick num (SatM.enc k φ) = num (List.replicate l (), List.replicate (S.K (Q.idx l)) ()) ∧ idxU Q.pick (SatM.enc k φ) = Q.idx l
def CountIsRight : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ n₀ : ℕ, ∀ n₁ : ℕ, n₀ ≤ n₁ → ∀ (k n : ℕ) (φ : CNF n), S.K (Q.idx 0) ^ 17 ≤ n → 3 ≤ k → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n → SatK.IsKCNF k φ →
      ∀ pad : U, 2 ^ expo S n₁ Q.pick num (SatM.enc k φ) ≤ pad.length → count S n₁ Q.pick num (SatM.enc k φ, pad) = SatK.binary n (SatK.numSat φ)
def CountIsPolynomialTime : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (n₁ : ℕ) (pick : U → U × Idx) (num : U × U → ℕ × ℕ), PolyT pick → PolyT num →
    PolyT (count S n₁ pick num) ∧ PolyT (expo S n₁ pick num)
end RecursionToBound


