-- Prove2me | Definitions.Def_OAIQ053K050
-- name    : OAIQ053K050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:09:50.175637+00:00
-- url     : https://prove2.me/theorems/f2505718-9780-42c9-a7e0-bebf0e7a8373
-- title:
--   Definitions bundle OAIQ053K050 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 18 definitions and 24 theorems. The definitions and types are `OAI.MetricKMedian.Gaussian.ListOperation.coefficientsProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.downProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.liftProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.pivotProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.reduceProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.residualProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.upProgram`, `OAI.MetricKMedian.InputParser.parseBound`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.encode`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput.encode`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.countProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.dimProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.ed`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.eqd`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.featuresProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.largeProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.lawProgram`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.rawProgram`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_SequentialParserProgram`, `KMedian_Compression_CompressionBinaryProgram`, `KMedian_Compression_CompressionBounds`, `KMedian_Compression_CompressionListStep`, `KMedian_Compression_GaussianListCompiler`, `KMedian_Compression_GaussianListMachine`, `KMedian_Process_RoundingCoordinateHeight`, `KMedian_Process_RoundingRunHeight`, `KMedian_Programs_RationalFeatureProgram`, `KMedian_Rounding_SignedGridInvariant`, `KMedian_Rounding_SignedListOperations`, `KMedian_Sparse_SparseAlgorithm`, `KMedian_Sparse_SparseIterationHeight`, `KMedian_Sparse_SparseSignedPartial`, `KMedian_Sparse_SparseWeightedPartial`.
--
--   **Imports.** It imports the bundles `OAIQ053K044`, `OAIQ053K045` and `OAIQ053K046` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K056`, `OAIQ053K057`, `OAIQ053K058`, `OAIQ053K060` and `OAIQ053K061`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K044
import Definitions.Def_OAIQ053K045
import Definitions.Def_OAIQ053K046

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_SequentialParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
section Generic
variable {α : Type} [Coding α] [Inhabited α] (read : List Bool → α × List Bool)
variable (P : PolyProgram enc enc read) (hrest : ∀ xs, (read xs).2.length≤xs.length)
noncomputable def parseBound : Polynomial ℕ := X+X*(2*P.sizeBound+1)
end Generic
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListCompiler
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function

noncomputable def pivotProgram : PolyProgram er Nat.bits pivot :=
  (ratNonzero.listFindIdx 0).congr _ (fun _ => rfl)

noncomputable def coefficientsProgram : PolyProgram ef er (fun x : ℕ × Row => coefficients x.2 x.1) := by
  let p := fst Nat.bits er
  let row := snd Nat.bits er
  let inp := row.fanout p
  let denom := inp.comp (listGetD Ratio.encode 0)
  let rem := inp.comp (listEraseIdx Ratio.encode 0)
  let divide : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.2/x.1) :=
    ((exchange Ratio.encode Ratio.encode).comp ratDiv).congr _ (fun _ => rfl)
  exact ((denom.fanout rem).comp (divide.listMapWith 0 0)).congr _ (fun _ => rfl)

noncomputable def reduceProgram : PolyProgram (encodePair (encodePair er Nat.bits) er) er
    (fun x : (Row × ℕ) × Row => reduce x.1.1 x.1.2 x.2) := by
  let ec := encodePair er Nat.bits
  let cp := fst ec er
  let c := cp.comp (fst er Nat.bits)
  let p := cp.comp (snd er Nat.bits)
  let row := snd ec er
  let inp := row.fanout p
  let rem := inp.comp (listEraseIdx Ratio.encode 0)
  let val := inp.comp (listGetD Ratio.encode 0)
  let zp := (rem.fanout c).comp (listZip Ratio.encode Ratio.encode 0 0)
  let term : PolyProgram (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)) Ratio.encode
      (fun x : ℚ × (ℚ × ℚ) => x.2.1-x.2.2*x.1) := by
    let pair := snd Ratio.encode (encodePair Ratio.encode Ratio.encode)
    let a := pair.comp (fst Ratio.encode Ratio.encode)
    let b := pair.comp (snd Ratio.encode Ratio.encode)
    let d := fst Ratio.encode (encodePair Ratio.encode Ratio.encode)
    exact ((a.fanout ((b.fanout d).comp ratMul)).comp ratSub).congr _ (fun _ => rfl)
  exact ((val.fanout zp).comp (term.listMapWith (0,0) 0)).congr _ (fun _ => rfl)

noncomputable def residualProgram : PolyProgram (encodePair ef ers) ers
    (fun x : (ℕ × Row) × Rows => residual x.1.2 x.1.1 x.2) := by
  let frame := fst ef ers
  let p := frame.comp (fst Nat.bits er)
  let c := frame.comp coefficientsProgram
  let rows := snd ef ers
  let start := (c.fanout p).fanout rows
  exact (start.comp (reduceProgram.listMapWith [] [])).congr _ (fun _ => rfl)

noncomputable def liftProgram : PolyProgram (encodePair ef er) er
    (fun x : (ℕ × Row) × Row => lift x.1.2 x.1.1 x.2) := by
  let frame := fst ef er
  let p := frame.comp (fst Nat.bits er)
  let c := frame.comp coefficientsProgram
  let z := snd ef er
  let terms := (c.fanout z).comp (listZipWith Ratio.encode Ratio.encode 0 0 ratMul)
  let value := (terms.comp ratSum).comp ratNeg
  exact (((z.fanout p).fanout value).comp (listInsertAt Ratio.encode 0)).congr _ (fun _ => rfl)

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListMachine
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function

noncomputable def downProgram : PolyProgram ed (encodeLoop eState er) down := by
  let dat := fst edata efs
  let slots := dat.comp (fst eslots ers)
  let rows := dat.comp (snd eslots ers)
  let frames := snd edata efs
  let row := rows.comp (listHead er [])
  let p := row.comp pivotProgram
  let frame := p.fanout row
  let tl := rows.comp (listTail er [])
  let recRows := (frame.fanout tl).comp residualProgram
  let recSlots := slots.comp (listTail eu ())
  let recFrames := (frame.fanout frames).comp (listCons ef)
  let recurse := (((recSlots.fanout recRows).fanout recFrames).comp (injectLeft eUp ed)).comp (injectRight eState er)
  let skip := (((slots.fanout tl).fanout frames).comp (injectLeft eUp ed)).comp (injectRight eState er)
  let test := (p.fanout (row.comp (listLength Ratio.encode 0))).comp natLT
  let pivotCase := ite test skip recurse
  let zeroCase := (((constant ed er []).fanout frames).comp (injectRight eUp ed)).comp (injectRight eState er)
  let noCols := ite (slots.comp (listIsEmpty eu)) pivotCase zeroCase
  let baseCase := (((slots.comp basisProgram).fanout frames).comp (injectRight eUp ed)).comp (injectRight eState er)
  exact (ite (rows.comp (listIsEmpty er)) noCols baseCase).congr _ (fun x => by
    simp only [down,Function.comp_def,decide_eq_true_eq])

noncomputable def upProgram : PolyProgram eUp (encodeLoop eState er) up := by
  let z := fst er efs
  let frames := snd er efs
  let frame := frames.comp (listHead ef (0,[]))
  let new := (frame.fanout z).comp liftProgram
  let tl := frames.comp (listTail ef (0,[]))
  let recur := ((new.fanout tl).comp (injectRight eUp ed)).comp (injectRight eState er)
  let done := z.comp (injectLeft eState er)
  exact (ite (frames.comp (listIsEmpty ef)) recur done).congr _ (fun _ => rfl)

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_CompressionListStep
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset
abbrev ed := encodePair es (encodePair el em)

abbrev Input.encode (I : Input) := ed I.raw

noncomputable def rawProgram : PolyProgram Input.encode ed Input.raw :=
  (identity ed).recode Input.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def lawProgram : PolyProgram Input.encode el Input.lawData :=
  ((rawProgram.comp (snd es (encodePair el em))).comp (fst el em)).congr _ (fun _ => rfl)
noncomputable def featuresProgram : PolyProgram Input.encode em Input.features :=
  ((rawProgram.comp (snd es (encodePair el em))).comp (snd el em)).congr _ (fun _ => rfl)
noncomputable def dimProgram : PolyProgram Input.encode es (fun I => List.replicate I.d ()) :=
  (rawProgram.comp (fst es (encodePair el em))).congr _ (fun _ => rfl)

noncomputable def largeProgram : PolyProgram Input.encode encodeBool (fun I => decide I.large) := by
  let nums := lawProgram.comp (snd Signed.encode er)
  let nonz := (((identity Signed.encode).fanout (constant Signed.encode Signed.encode 0)).comp intEQ).comp boolNot
  let size := (nums.comp (nonz.listFilter 0)).comp (listLength Signed.encode 0)
  let dim := ((dimProgram.comp (listLength Gaussian.ListOperation.eu ())).fanout (constant Input.encode Nat.bits 1)).comp natAdd
  exact ((dim.fanout size).comp natLT).congr _ (fun I => by
    simp only [Function.comp_apply,Input.large,Input.lawData,List.length_replicate]
    congr 1
    congr 1
    change ((List.ofFn I.μ.numerator).filter (fun z => !decide (z=0))).length=I.μ.support.card
    have he : (List.ofFn I.μ.numerator).filter (fun z => !decide (z=0))=
        List.ofFn (fun j : Fin I.μ.support.card => I.μ.numerator ((I.μ.support.orderIsoOfFin rfl) j).val) := by
      simp only [← decide_not]
      rw [List.ofFn_eq_map,List.filter_map]
      exact EncodingLists.map_filter_enum _ (fun i => I.μ.numerator i≠0)
    rw [he,List.length_ofFn])

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_CompressionBounds
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.IntegerLaw.trim_denominator _root_.OAI.MetricKMedian.IntegerLaw.trim_numerator _root_.OAI.MetricKMedian.IntegerLaw.trim_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset Polynomial

theorem input_bounds (I : Input) :
    I.n≤I.encode.length ∧ I.d≤I.encode.length ∧
    I.μ.denominator≤(2:ℤ)^I.encode.length ∧ ∀ i j, |I.v i j|≤(2:ℤ)^I.encode.length := by
  let L := I.encode.length
  have hl : L=2*I.d+1+2*(ListPivot.el I.lawData).length+1+(em I.features).length := by
    simp only [L,Input.raw,encodePair_length,Gaussian.ListOperation.slots_size]
    omega
  have hn := EncodedList.length_le Signed.encode (List.ofFn I.μ.numerator)
  simp only [List.length_ofFn] at hn
  have hlaw : (ListPivot.el I.lawData).length=2*(Signed.encode I.μ.denominator).length+1+(er (List.ofFn I.μ.numerator)).length := by
    simp only [Input.lawData,ListPivot.el,encodePair_length]
  refine ⟨by change I.n≤L; change I.n≤(er (List.ofFn I.μ.numerator)).length at hn; omega,by change I.d≤L; omega,?_,?_⟩
  · have hlen : (Signed.encode I.μ.denominator).length≤L := by omega
    exact (le_abs_self _).trans ((Signed.height_length _).trans (pow_le_pow_right₀ (by norm_num) hlen))
  · intro i j
    have hrow : List.ofFn (I.v i)∈I.features := List.mem_ofFn.mpr ⟨i,rfl⟩
    have hcol : I.v i j∈List.ofFn (I.v i) := List.mem_ofFn.mpr ⟨j,rfl⟩
    have h1 := EncodedList.member_length Signed.encode (List.ofFn (I.v i)) _ hcol
    have h2 := EncodedList.member_length er I.features _ hrow
    change (Signed.encode (I.v i j)).length≤(er (List.ofFn (I.v i))).length at h1
    change (er (List.ofFn (I.v i))).length≤(em I.features).length at h2
    exact (Signed.height_length _).trans (pow_le_pow_right₀ (by norm_num) (by omega))

theorem Input.encode_length (I : Input) : I.encode.length =
    2*I.d+1+(2*(2*(Signed.encode I.μ.denominator).length+1+
      (er (List.ofFn I.μ.numerator)).length)+1+(em I.features).length) := by
  simp only [Input.encode,Input.raw,Input.lawData,ed,el,ListPivot.el,encodePair_length,
    Gaussian.ListOperation.slots_size]

theorem state_size (I : Input) (t : ℕ) (ht : t≤I.n) :
    (Input.encode (Input.step^[t] I)).length≤ statePolynomial.eval I.encode.length := by
  let L := I.encode.length
  let ν := (lawStep I.v)^[t] I.μ
  obtain ⟨hn,hd,hμ,hv⟩ := input_bounds I
  have hν : ν.denominator≤(2:ℤ)^(height L) := by
    apply (iterate_denominator I.μ I.v L hv hμ t).trans
    apply pow_le_pow_right₀ (by norm_num)
    dsimp only [height]
    gcongr
    exact ht.trans hn
  have hden : (Signed.encode ν.denominator).length≤height L+4 :=
    Signed.length_height (by rwa [abs_of_pos ν.denominator_pos])
  have hnum : (er (List.ofFn ν.numerator)).length ≤ L*(2*(height L+4)+1) := by
    apply (EncodedList.length_bound Signed.encode (List.ofFn ν.numerator) (height L+4) ?_).trans
    · simpa only [List.length_ofFn] using Nat.mul_le_mul_right (2*(height L+4)+1) hn
    · intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      apply Signed.length_height
      rw [abs_of_nonneg (ν.numerator_nonneg i)]
      exact (ν.numerator_le i).trans hν
  have hfeat : (em I.features).length≤L := by
    simp only [L,Input.raw,encodePair_length]
    omega
  rw [input_iterate,Input.encode_length,statePolynomial_eval]
  exact size_arithmetic L I.d (Signed.encode ν.denominator).length
    (er (List.ofFn ν.numerator)).length (em I.features).length (height L) hd hden hnum hfeat

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RationalFeatureProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function
abbrev eqd := encodePair es (encodePair el eqm)

abbrev RationalInput.encode (I : RationalInput) := eqd I.raw

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_CompressionBinaryProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Polynomial

noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.n :=
  ((lawProgram.comp (snd Signed.encode er)).comp (listLength Signed.encode 0)).congr _
    (fun I => by simp only [Function.comp_apply,Input.lawData,List.length_ofFn])

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseAlgorithm
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem compressAuto_denominator {d : ℕ} (μ : SparseIntegerLaw α)
    (v : α → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i : Fin μ.length, ∀ j, |(v μ.states[i.val] j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i : Fin μ.length, ∀ j, ((v μ.states[i.val] j).den:ℤ) ≤ (2:ℤ)^L) :
    (μ.compressAuto v).law.denominator ≤ μ.law.denominator *
      (2:ℤ)^(((2*(d+1)*(d+1+L*(μ.length+1)))*(μ.length+1))*μ.length) :=
  (μ.law.compressAuto_spec (fun i => v μ.states[i.val]) L hnum hden).1

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseWeightedPartial
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedPartial
open Finset RationalWeightedStep
variable {n : ℕ}

 theorem run_length (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (t : ℕ) : (run β hβ p t).length ≤ n+n*n+1 := by
  cases t with
  | zero => change 1 ≤ _; omega
  | succ t => exact ((run β hβ p t).branch (probability β)
      (probability_unit β hβ) (endpoint β)).compressAuto_correct features |>.1

 theorem run_invariants (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (t : ℕ) :
    ∀ a : Fin (run β hβ p t).length,
      let q := (run β hβ p t).states[a.val]
      (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧
      (∑ i, β i*point q i)=∑ i, β i*point p i ∧
      (fractional q).card ≤ max (n-t) 1 := by
  induction t with
  | zero =>
    intro a
    have he : (run β hβ p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    dsimp only
    rw [he]
    refine ⟨hp,rfl,?_⟩
    have hh := card_le_card (filter_subset (fun i : Fin n => 0 < point p i ∧ point p i < 1) univ)
    simp only [card_univ,Fintype.card_fin] at hh
    exact hh.trans (le_max_left _ _)
  | succ t ih =>
    apply (run β hβ p t).step_property features (probability β)
      (probability_unit β hβ) (endpoint β)
      (fun q => (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧
        (∑ i, β i*point q i)=∑ i, β i*point p i ∧
        (fractional q).card ≤ max (n-(t+1)) 1)
    intro a b
    obtain ⟨ha0,ha1,ha2⟩ := ih a
    refine ⟨endpoint_feasible β hβ _ ha0 b,(endpoint_weighted β hβ _ b).trans ha1,?_⟩
    by_cases h : 1 < (fractional (run β hβ p t).states[a.val]).card
    · have hh := endpoint_smaller β hβ _ h b
      omega
    · simp only [endpoint,dite_eq_right h]
      omega

end MetricKMedian.SparseWeightedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPartial
open Finset RationalSignedStep
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

 theorem run_length (β : Fin n → ℚ) 
    (p : Vector ℚ n) (t : ℕ) : (run β p t).length ≤ n+n*n+1 := by
  cases t with
  | zero => change 1 ≤ _; omega
  | succ t => exact ((run β p t).branch (probability β)
      (probability_unit β) (endpoint β)).compressAuto_correct features |>.1

end MetricKMedian.SparseSignedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedGridInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.SparseWeightedPartial
open RationalWeightedStep RationalGrid
variable {n : ℕ}

theorem run_grid (β : Fin n → ℚ) (hβ : ∀ i, 0<β i) (p : Vector ℚ n)
    (D : ℤ) (hb : ∀ i, At D (β i)) (hp : ∀ i, At D (β i*point p i)) (t : ℕ) :
    ∀ a : Fin (run β hβ p t).length, ∀ i, At D (β i*point (run β hβ p t).states[a.val] i) := by
  induction t with
  | zero =>
    intro a
    have he : (run β hβ p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    rw [he]
    exact hp
  | succ t ih =>
    apply (run β hβ p t).step_property features (probability β) (probability_unit β hβ)
      (endpoint β) (fun q => ∀ i, At D (β i*point q i))
    intro a b
    exact endpoint_grid β hβ D hb _ (ih a) b
end MetricKMedian.SparseWeightedPartial

namespace MetricKMedian.SparseSignedPartial
open RationalSignedStep RationalGrid
open RationalWeightedStep (point)
variable {n : ℕ}

theorem run_grid (β : Fin n → ℚ) (p : Vector ℚ n)
    (D : ℤ) (hb : ∀ i, At D (β i)) (hp : ∀ i, At D (β i*point p i)) (t : ℕ) :
    ∀ a : Fin (run β p t).length, ∀ i, At D (β i*point (run β p t).states[a.val] i) := by
  induction t with
  | zero =>
    intro a
    have he : (run β p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    rw [he]
    exact hp
  | succ t ih =>
    apply (run β p t).step_property SparseWeightedPartial.features (probability β) (probability_unit β)
      (endpoint β) (fun q => ∀ i, At D (β i*point q i))
    intro a b
    exact endpoint_grid β D hb _ (ih a) b

theorem run_zero_weight (β : Fin n → ℚ) (p : Vector ℚ n) (t : ℕ) :
    ∀ a : Fin (run β p t).length, ∀ i, β i=0 → point (run β p t).states[a.val] i=point p i := by
  induction t with
  | zero =>
    intro a
    have he : (run β p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    rw [he]
    exact fun _ _ => rfl
  | succ t ih =>
    apply (run β p t).step_property SparseWeightedPartial.features (probability β) (probability_unit β)
      (endpoint β) (fun q => ∀ i, β i=0 → point q i=point p i)
    intro a b i hi
    exact (endpoint_zero_weight β _ b i hi).trans (ih a i hi)
end MetricKMedian.SparseSignedPartial
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingCoordinateHeight
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MetricKMedian.RoundingHeight
open RationalGrid RationalWeightedStep Binary
variable {n : ℕ}

theorem weighted_run (β : Fin n → ℚ) (hβ : ∀ i, 0<β i) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) (a : Fin (SparseWeightedPartial.run β hβ p t).length)
    (i : Fin n) : HasHeight (point (SparseWeightedPartial.run β hβ p t).states[a.val] i) (2*n*L+L) := by
  apply coordinate_height β p _ L hb hp
  · exact SparseWeightedPartial.run_grid β hβ p _ (initial_grid β p).1 (initial_grid β p).2 t a
  · intro j hj; exact False.elim ((hβ j).ne' hj)
  · exact (SparseWeightedPartial.run_invariants β hβ p hu t a).1

theorem signed_run (β : Fin n → ℚ) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) (a : Fin (SparseSignedPartial.run β p t).length)
    (i : Fin n) : HasHeight (point (SparseSignedPartial.run β p t).states[a.val] i) (2*n*L+L) := by
  apply coordinate_height β p _ L hb hp
  · exact SparseSignedPartial.run_grid β p _ (initial_grid β p).1 (initial_grid β p).2 t a
  · exact SparseSignedPartial.run_zero_weight β p t a
  · exact (SparseSignedPartial.run_invariants β p hu t a).1

end MetricKMedian.RoundingHeight
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseIterationHeight
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MetricKMedian.SparseIntegerLaw
open Binary
variable {α : Type} {d : ℕ}

theorem step_denominator_height (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ)
    (p : α → ℚ) (hp : ∀ a, 0≤p a ∧ p a≤1) (next : α → Fin 2 → α)
    (N P F : ℕ) (hN : μ.length≤N)
    (hP : ∀ i : Fin μ.length, HasHeight (p μ.states[i.val]) P)
    (hF : ∀ i : Fin μ.length, ∀ b j, HasHeight (v (next μ.states[i.val] b) j) F) :
    (μ.step v p hp next).law.denominator≤μ.law.denominator*(2:ℤ)^(stepHeight N d P F) := by
  have hf : ∀ i : Fin (μ.branch p hp next).length, ∀ j,
      HasHeight (v (μ.branch p hp next).states[i.val] j) F := by
    intro i j
    change HasHeight (v ((Vector.ofFn _)[i.val]) j) F
    simp only [Vector.getElem_ofFn]
    exact hF _ _ j
  have hc := (μ.branch p hp next).compressAuto_denominator v F
    (fun i j => (hf i j).1) (fun i j => (hf i j).2)
  have hb : (μ.branch p hp next).law.denominator≤μ.law.denominator*(2:ℤ)^(P*μ.length) :=
    IntegerBranching.branch_denominator μ.law (fun i => p μ.states[i.val]) (fun i => hp μ.states[i.val]) P (fun i => (hP i).2)
  apply hc.trans
  calc
    _ ≤ (μ.law.denominator*(2:ℤ)^(P*μ.length)) *
        (2:ℤ)^(((2*(d+1)*(d+1+F*((μ.branch p hp next).length+1)))*((μ.branch p hp next).length+1))*(μ.branch p hp next).length) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = μ.law.denominator*(2:ℤ)^(stepHeight μ.length d P F) := by
      simp only [branch,stepHeight,← mul_assoc,Nat.mul_comm 2 μ.length]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ μ.law.denominator_pos.le
      apply pow_le_pow_right₀ (by norm_num)
      unfold stepHeight
      gcongr

end MetricKMedian.SparseIntegerLaw
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingRunHeight
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RoundingHeight
open RationalWeightedStep Binary
variable {n : ℕ}

theorem weighted_endpoint (β : Fin n → ℚ) (hβ : ∀ i, 0<β i) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) (a : Fin (SparseWeightedPartial.run β hβ p t).length)
    (b : Fin 2) (i : Fin n) :
    HasHeight (point (endpoint β (SparseWeightedPartial.run β hβ p t).states[a.val] b) i) (2*n*L+L) := by
  apply coordinate_height β p _ L hb hp
  · exact endpoint_grid β hβ _ (initial_grid β p).1 _
      (SparseWeightedPartial.run_grid β hβ p _ (initial_grid β p).1 (initial_grid β p).2 t a) b
  · intro j hj; exact False.elim ((hβ j).ne' hj)
  · exact endpoint_feasible β hβ _ (SparseWeightedPartial.run_invariants β hβ p hu t a).1 b

theorem signed_endpoint (β : Fin n → ℚ) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) (a : Fin (SparseSignedPartial.run β p t).length)
    (b : Fin 2) (i : Fin n) :
    HasHeight (point (RationalSignedStep.endpoint β (SparseSignedPartial.run β p t).states[a.val] b) i) (2*n*L+L) := by
  apply coordinate_height β p _ L hb hp
  · exact RationalSignedStep.endpoint_grid β _ (initial_grid β p).1 _
      (SparseSignedPartial.run_grid β p _ (initial_grid β p).1 (initial_grid β p).2 t a) b
  · intro j hj
    exact (RationalSignedStep.endpoint_zero_weight β _ b j hj).trans
      (SparseSignedPartial.run_zero_weight β p t a j hj)
  · exact RationalSignedStep.endpoint_feasible β _ (SparseSignedPartial.run_invariants β p hu t a).1 b

theorem weighted_denominator (β : Fin n → ℚ) (hβ : ∀ i, 0<β i) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) :
    (SparseWeightedPartial.run β hβ p t).law.denominator≤(2:ℤ)^(stepHeight n L*t) := by
  induction t with
  | zero => simp only [SparseWeightedPartial.run,SparseIntegerLaw.dirac,mul_zero,pow_zero,le_refl]
  | succ t ih =>
    apply (SparseIntegerLaw.step_denominator_height _ _ _ _ _ (n+n*n+1)
      (3*(2*n*L+L+2*L+1)+1) (2*(2*n*L+L)) (SparseWeightedPartial.run_length β hβ p t)
      (fun a => probability_height β _ _ L hb (weighted_run β hβ p L t hb hp hu a))
      (fun a b i => SparseWeightedPartial.features_height _ _ (weighted_endpoint β hβ p L t hb hp hu a b) i)).trans
    calc
      _ ≤ (2:ℤ)^(stepHeight n L*t)*(2:ℤ)^(stepHeight n L) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ = _ := by rw [← pow_add,Nat.mul_succ]

theorem signed_denominator (β : Fin n → ℚ) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) :
    (SparseSignedPartial.run β p t).law.denominator≤(2:ℤ)^(stepHeight n L*t) := by
  induction t with
  | zero => simp only [SparseSignedPartial.run,SparseIntegerLaw.dirac,mul_zero,pow_zero,le_refl]
  | succ t ih =>
    apply (SparseIntegerLaw.step_denominator_height _ _ _ _ _ (n+n*n+1)
      (3*(2*n*L+L+2*L+1)+1) (2*(2*n*L+L)) (SparseSignedPartial.run_length β p t)
      (fun a => RationalSignedStep.probability_height β _ _ L hb (signed_run β p L t hb hp hu a))
      (fun a b i => SparseWeightedPartial.features_height _ _ (signed_endpoint β p L t hb hp hu a b) i)).trans
    calc
      _ ≤ (2:ℤ)^(stepHeight n L*t)*(2:ℤ)^(stepHeight n L) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ = _ := by rw [← pow_add,Nat.mul_succ]

end MetricKMedian.RoundingHeight
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly RationalWeightedStep Finset

attribute [fun_prop] square_poly

theorem square_list {n : ℕ} (p : Vector ℚ n) :
    square p.toList=List.ofFn (fun z : Fin (n*n) => ((finProdFinEquiv.symm z).1.val,(finProdFinEquiv.symm z).2.val)) := by
  simp only [square,indices,Vector.length_toList,range_finRange,List.flatMap_def,List.map_map,Function.comp_def]
  rw [← List.ofFn_eq_map]
  conv => lhs; arg 1; arg 1; intro i; rw [← List.ofFn_eq_map]
  exact ofFn_product _

namespace Signed

theorem valid_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (z : Fin (n*n)) :
    valid (List.ofFn β) p.toList ((finProdFinEquiv.symm z).1.val,(finProdFinEquiv.symm z).2.val)=
      decide (z∈RationalSignedStep.pairs β p) := by
  simp only [valid,frac,get_point,Gaussian.ListOperation.get_ofFn,← Bool.decide_and]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,RationalSignedStep.pairs,mem_filter,mem_univ,true_and,RationalWeightedStep.fractional,Fin.val_ne_iff]
  tauto

theorem active_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) :
    active (List.ofFn β) p.toList=decide (RationalSignedStep.Active β p) := by
  unfold active index
  rw [square_list]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,List.findIdx_lt_length,List.mem_ofFn]
  constructor
  · rintro ⟨a,⟨z,rfl⟩,hz⟩
    exact ⟨z,by simpa only [valid_list,decide_eq_true_eq] using hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨_,⟨z,rfl⟩,by simpa only [valid_list,decide_eq_true_eq] using hz⟩

theorem index_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (h : RationalSignedStep.Active β p) :
    index (List.ofFn β) p.toList=((RationalSignedStep.pairs β p).min' h).val := by
  unfold index
  rw [square_list]
  let z := (RationalSignedStep.pairs β p).min' h
  apply (List.findIdx_eq (by simpa only [List.length_ofFn] using z.isLt)).mpr
  constructor
  · simp only [List.getElem_ofFn,valid_list,decide_eq_true_eq]
    exact min'_mem _ h
  · intro j hj
    simp only [List.getElem_ofFn,valid_list,decide_eq_false_iff_not]
    intro hm
    exact (not_le_of_gt hj) ((RationalSignedStep.pairs β p).min'_le _ hm)

theorem pair_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (h : RationalSignedStep.Active β p) :
    pair (List.ofFn β) p.toList=((RationalSignedStep.pair β p h).val.1.val,(RationalSignedStep.pair β p h).val.2.val) := by
  simp only [pair,index_list β p h,square_list,Gaussian.ListOperation.get_ofFn,RationalSignedStep.pair]

theorem probability_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) :
    probability (List.ofFn β) p.toList=RationalSignedStep.probability β p := by
  unfold probability RationalSignedStep.probability
  rw [active_list]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · simp only [ratio,pair_list β p h,Gaussian.ListOperation.get_ofFn,up_list,down_list]
  · rfl

theorem endpoint_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2) :
    endpoint (List.ofFn β) p.toList (decide (b≠0))=(RationalSignedStep.endpoint β p b).toList := by
  unfold endpoint RationalSignedStep.endpoint
  rw [active_list]
  simp only [decide_eq_true_eq]
  by_cases h : RationalSignedStep.Active β p
  · simp only [ite_eq_left h,dite_eq_left h,ratio,pair_list β p h,Gaussian.ListOperation.get_ofFn,up_list,down_list]
    by_cases hb : b=0 <;> simp [hb,move_list]
  · simp only [ite_eq_right h,dite_eq_right h]

end Signed
end MetricKMedian.RoundingList
end

end OAI
end


