-- Prove2me | Definitions.Def_OAIQ087A013
-- name    : OAIQ087A013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:22:55.332998+00:00
-- url     : https://prove2.me/theorems/e286b06c-8200-40f8-86fb-e9fb461afe7c
-- title:
--   Definitions bundle OAIQ087A013 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 3 definitions and 6 theorems. The definitions and types are `OAI.OptimalMaxCut.GaussianBellman.corrAverage`, `OAI.OptimalMaxCut.GaussianBellman.gradient`, `OAI.OptimalMaxCut.GaussianBellman.slopeSection`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`MaxCut_Encoding_BitCube`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Encoding/BitCube.lean), [`MaxCut_Encoding_BitPairWeightQ`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Encoding/BitPairWeightQ.lean), [`MaxCut_Estimates_Anchor`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Anchor.lean).
--
--   **Imports.** It imports the published bundle `Def_OptimalMaxCut`; the bundles `OAIQ087A000`, `OAIQ087A005` and `OAIQ087A006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ087A019`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OptimalMaxCut
import Definitions.Def_OAIQ087A000
import Definitions.Def_OAIQ087A005
import Definitions.Def_OAIQ087A006

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitCube
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.GaussianBellman
open scoped BigOperators
open Set Finset

noncomputable def corrAverage (t : ℝ) : (n : ℕ) → (BitCube n → BitCube n → ℝ) → ℝ
  | 0, F => F default default
  | n + 1, F => corrAverage t n (fun x y =>
      ∑ a : Bool, ∑ b : Bool, bitPairWeight t a b * F (Fin.cons a x) (Fin.cons b y))

noncomputable def slopeSection {n : ℕ} (f : BitCube (n + 1) → ℝ) (x : BitCube n) : ℝ :=
  (f (Fin.cons false x) - f (Fin.cons true x)) / 2

 theorem corrAverage_mono {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (n : ℕ)
    {F G : BitCube n → BitCube n → ℝ} (h : ∀ x y, F x y ≤ G x y) :
    corrAverage t n F ≤ corrAverage t n G := by
  induction n with
  | zero => exact h _ _
  | succ n ih =>
    apply ih
    intro x y
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    exact mul_le_mul_of_nonneg_left (h _ _) (bitPairWeight_nonneg ht a b)

 theorem corrAverage_add (t : ℝ) (n : ℕ) (F G : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => F x y + G x y) = corrAverage t n F + corrAverage t n G := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [corrAverage, mul_add, Finset.sum_add_distrib, ih]

 theorem expect_zero_cube (f : BitCube 0 → ℝ) : (𝔼 x, f x) = f default := by
  have hf : f = fun _ => f default := funext (fun x => congrArg f (Subsingleton.elim x default))
  rw [hf, Fintype.expect_const]

noncomputable def gradient {n : ℕ} (f : BitCube n → ℝ) (i : Fin n) (x : BitCube n) : ℝ :=
  (f x - f (Function.update x i (!x i))) / 2

end OptimalMaxCut.GaussianBellman

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitPairWeightQ
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

 theorem bitPairWeightQ_cast (t : ℚ) (a b : Bool) : (bitPairWeightQ t a b : ℝ) = bitPairWeight t a b := by
  cases a <;> cases b <;> simp [bitPairWeightQ, bitPairWeight, sign]

end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Anchor
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut
open scoped BigOperators
open CounterMachine
attribute [local instance] Classical.propDecidable

@[simp] theorem nameBits_length_exact (n : ℕ) :
    (MaxCutGames.BinaryEncoding.nameBits n).length = 2*n.size+1 := by
  exact MaxCutGames.BinaryEncoding.nameBits_length n

@[simp] theorem ScaledGraph.bits_length_exact (G : ScaledGraph) :
    G.bits.length = (2*G.graph.vertices.size+1)+(2*G.scale.size+1)+G.graph.vertices^2 := by
  simp only [ScaledGraph.bits,List.length_append,nameBits_length_exact,Graph.table_length]

end OptimalMaxCut

end

end OAI
end


