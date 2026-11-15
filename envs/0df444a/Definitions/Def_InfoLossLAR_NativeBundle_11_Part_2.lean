-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_11_Part_2
-- name    : InfoLossLAR_NativeBundle_11_Part_2
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T19:26:42.500063+00:00
-- url     : https://prove2.me/theorems/43bec570-3953-4643-9d51-0a9696819d0f
-- title:
--   Public seed draws and primary weighted-score data
-- statement:
--   This package defines finite probability-array and public-index draws, safe palettes, reference and activation draws, public anchor and seed draws, concrete core proposals and their stored budget expressions, and root averages, singleton and leg groups, selected primary coefficients, centered and weighted primary scores.
--
--   These are stored finite data and their constructor and interpretation APIs. They keep the actual binary or rational computation distinct from its ideal real semantics; later theorems establish approximation and platform running-time guarantees. The smaller compilation unit preserves entire original source modules and introduces no assumed transport or lattice-reduction result.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0. Original source units Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentPublicIndexProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentProbabilityArrayDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentSafePaletteIndex, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentReferenceDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentActivationDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentUniformDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentAnchorIndexDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentPublicSeedDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentSafeDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentCoreProposal, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentCoreProposalWork, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentReferenceCacheWork, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentProposalSamplerPolynomial, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootReferenceResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootAverage, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryLegMassResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryFirstCoefficient, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootDensityResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootSingleton, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootSingletonResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryUnselectedLeg, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryUnselectedLegResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryLegGroup, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinarySeedRootAverage, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPositiveAverage, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPrimarySelectedCoefficient, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPrimaryFamily, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPositivePrimary, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPrimaryCenteredScore, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootWeightedScore, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPrimaryFixedMass. Exact syntax-oracle source spans, body hashes and closed scope wrappers recorded in compact_heavy_split/manifest.json. Source SHA256 1b1198f83a6d51a8941023a48ba86485e6d2aadc9980a4a170fe118b33506512. Compiler-only optimization: one local scope marks Polynomial addition and multiplication instances irreducible while generating native equation lemmas. Every original definition and proof source body is unchanged; all11528 public types and recursive standard-axiom audits pass. New sourceSHA256 c4ec3ee9735f601ee4675be2bcea03ef6d6550629fa77d10d28b9751a7cfa341.

import Definitions.Def_InfoLossLAR_NativeBundle_11_Part_1

section
attribute [local irreducible] Polynomial.instAdd Polynomial.instMul

section




















/-! The public primary/ordinary role address is selected by an actual counter
comparison and, on the ordinary branch, a counter subtraction. -/
namespace CurrentAFT.CurrentPublicIndexProgram
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram CurrentProposalDimensions
set_option maxHeartbeats 500000
attribute [local irreducible] CurrentProposalDimensions.current

def decode (security : ℕ) (index : Fin (current security).controls) :
    CountedValue (PublicOutputExperiment.PublicIndex security) :=
  let below := lessCounter index.val (current security).legs
  if h : below.value then
    have hi : index.val < Parameters.legCount security := by
      have hh := (lessCounter_value _ _).mp h
      rwa [(current_values security).2.1] at hh
    ⟨.inl ⟨index.val, hi⟩, below.work + 2⟩
  else
    let offset := subtractCounter index.val (current security).legs
    have hi : offset.count < BackgroundRates.ordinaryPool security := by
      have hh : ¬index.val < (current security).legs := by simpa only [← lessCounter_value] using h
      have hb : index.val < Parameters.legCount security + BackgroundRates.ordinaryPool security := by
        simpa only [(current_values security).2.2.2.2.2] using index.isLt
      rw [subtractCounter_value, (current_values security).2.1]
      rw [(current_values security).2.1] at hh
      omega
    ⟨.inr ⟨offset.count, hi⟩, below.work + offset.work + 3⟩



def workBound (security : ℕ) : ℕ := 5 * (current security).controls + 5



end CurrentAFT.CurrentPublicIndexProgram

end

section






















/-! Literal ticket sampling from a stored certified rational probability array. -/

namespace CurrentAFT.CurrentProbabilityArrayDraw

open AFT AFT.RationalNumerics AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 400000

structure ProbabilityArray (count : ℕ) where
  data : Vector RationalBits count
  nonneg : ∀ index, 0 ≤ (data.get index).decode
  mass : ∑ index, (data.get index).decode = 1

def draw (count : ℕ) (table : ProbabilityArray (count + 1)) (bits : ℕ)
    (word : Fin (bits + (count + 1) + 1) → Fin 2) : CountedValue (Fin (count + 1)) :=
  let guard := addCounter bits (count + 1)
  have heq : guard.count + 1 = bits + (count + 1) + 1 := by rw [addCounter_value]
  let selected := binaryRationalDraw table.data (guard.count + 1) (fun index => word (index.cast heq))
  have hi : selected.value < count + 1 := by
    dsimp only [selected]
    rw [binaryRationalDraw_cast _ _ _ heq, binaryRationalDraw_value table.data table.nonneg table.mass]
    exact Fin.isLt _
  ⟨⟨selected.value, hi⟩, guard.work + selected.work + 3⟩



def workBound (count height bits : ℕ) : ℕ :=
  (2 * bits + 1) + binaryRationalDrawWork count height (bits + count + 1) + 3



/-- Cardinal-sized wrapper, with positivity used only to exclude an empty table. -/
def positiveDraw : (count : ℕ) → (hpositive : 0 < count) → (table : ProbabilityArray count) → (bits : ℕ) →
    (Fin (bits + count + 1) → Fin 2) → CountedValue (Fin count)
  | 0, hpositive, _, _, _ => False.elim (by omega)
  | count + 1, _, table, bits, word => draw count table bits word



noncomputable section
open scoped Classical

def law {count : ℕ} (table : ProbabilityArray count) : FiniteDist (Fin count) where
  weight index := (table.data.get index).decode
  nonneg index := by exact_mod_cast table.nonneg index
  sum_one := by exact_mod_cast table.mass








end
end CurrentAFT.CurrentProbabilityArrayDraw

end

section






















/-! Native interval coordinates for the actual safe body alphabet. -/
namespace CurrentAFT.CurrentSafePaletteIndex

open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 500000

abbrev count (security : ℕ) := Parameters.modulus security - 2 * Parameters.safeMargin security

theorem count_positive (security : ℕ) : 0 < count security := by
  have h := ProposalPrimary.safe_clearance security
  change 0 < Parameters.modulus security - 2 * Parameters.safeMargin security
  omega

def equiv (security : ℕ) : Fin (count security) ≃ ActualControls.SafePalette security where
  toFun index := ⟨⟨Parameters.safeMargin security + index.val, by
      have h := index.isLt
      have hc := ProposalPrimary.safe_clearance security
      dsimp only [count] at h
      omega⟩, by
    unfold InwardAnchor.SafeColor
    change (Parameters.safeMargin security : ℤ) ≤ ((Parameters.safeMargin security + index.val : ℕ) : ℤ) ∧
      ((Parameters.safeMargin security + index.val : ℕ) : ℤ) < (Parameters.modulus security : ℤ) - Parameters.safeMargin security
    have h := index.isLt
    have hc := ProposalPrimary.safe_clearance security
    dsimp only [count] at h
    constructor <;> omega⟩
  invFun color := ⟨color.val.val - Parameters.safeMargin security, by
    have h := color.property
    unfold InwardAnchor.SafeColor at h
    have hc := ProposalPrimary.safe_clearance security
    dsimp only [count]
    omega⟩
  left_inv index := by apply Fin.ext; dsimp; omega
  right_inv color := by
    apply Subtype.ext
    apply Fin.ext
    have h := color.property.1
    dsimp only
    omega

@[simp] theorem equiv_value (security : ℕ) (index : Fin (count security)) :
    ((equiv security index).val).val = Parameters.safeMargin security + index.val := rfl







noncomputable section
open scoped Classical

instance safeNonempty (security : ℕ) : Nonempty (Fin (count security)) :=
  ⟨⟨0, count_positive security⟩⟩

def uniformLaw (security : ℕ) : FiniteDist (ActualControls.SafePalette security) :=
  (FiniteDist.uniform (Fin (count security))).map (equiv security)





end
end CurrentAFT.CurrentSafePaletteIndex

end

section






























/-! Certified primary/body sampling arrays prepared from the same executed
reference cache used by the weight evaluator. The center array is explicitly
restricted to native interval coordinates, so ticket rounding always returns a
safe control, even for tapes assigned to the first bucket. -/
namespace CurrentAFT.CurrentReferenceDraw

open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentProbabilityArrayDraw
open scoped BigOperators
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current
noncomputable local instance safeFintype (security : ℕ) : Fintype (ActualControls.SafePalette security) := by
  classical
  exact Subtype.fintype _

structure Counts where
  colors : ℕ
  margin : ℕ
  safe : ℕ
  work : ℕ

def counts (security : ℕ) : Counts :=
  let colors := PublicParameterProgram.modulus security
  let window := BinaryActivationProgram.cutoff security
  let square := addCounter window.count 1
  let margin := multiplyCounter 3 square.count
  let double := doubleCounter margin.count
  let safe := subtractCounter colors.count double.count
  ⟨colors.count, margin.count, safe.count,
    colors.work + window.work + square.work + margin.work + double.work + safe.work + 6⟩

theorem counts_values (security : ℕ) :
    (counts security).colors = Parameters.modulus security ∧
    (counts security).margin = Parameters.safeMargin security ∧
    (counts security).safe = CurrentSafePaletteIndex.count security := by
  have hm : (multiplyCounter 3 (addCounter (BinaryActivationProgram.cutoff security).count 1).count).count =
      Parameters.safeMargin security := by
    rw [BinaryBodyProgram.margin_value]
    rfl
  exact ⟨PublicParameterProgram.modulus_value security, hm, by
    simp only [counts, subtractCounter_value, doubleCounter_value, hm,
      PublicParameterProgram.modulus_value]⟩

theorem colors_positive (security : ℕ) : 0 < (PublicParameterProgram.modulus security).count := by
  rw [PublicParameterProgram.modulus_value]
  exact (Parameters.modulus_spec security).2.pos

theorem safe_positive (security : ℕ) : 0 < (counts security).safe := by
  rw [(counts_values security).2.2]
  exact CurrentSafePaletteIndex.count_positive security

def primaryEquiv (security : ℕ) : Fin (PublicParameterProgram.modulus security).count ≃ FirstHistogram.Palette security :=
  finCongr (PublicParameterProgram.modulus_value security)

def bodyEquiv (security : ℕ) : Fin (counts security).safe ≃ ActualControls.SafePalette security :=
  (finCongr (counts_values security).2.2).trans (CurrentSafePaletteIndex.equiv security)

@[simp] theorem bodyEquiv_value (security : ℕ) (index : Fin (counts security).safe) :
    (bodyEquiv security index).val.val = (counts security).margin + index.val := by
  rw [(counts_values security).2.1]
  rfl

def centerData (security : ℕ) (input : BinaryReferenceTables.Result security) :
    CountedValue (Vector RationalBits (counts security).safe) :=
  storeData (counts security).safe (fun index =>
    let added := addCounter (counts security).margin index.val
    have hi : added.count < (PublicParameterProgram.modulus security).count := by
      rw [addCounter_value, ← bodyEquiv_value, PublicParameterProgram.modulus_value]
      exact (bodyEquiv security index).val.isLt
    let entry := readVector zero input.center ⟨added.count, hi⟩
    ⟨entry.value, added.work + entry.work + 2⟩)

theorem centerData_get (security : ℕ) (input : BinaryReferenceTables.Result security)
    (index : Fin (counts security).safe) :
    (centerData security input).value.get index = input.center.get
      ((primaryEquiv security).symm (bodyEquiv security index).val) := by
  simp only [centerData, storeData_get, readVector_value]
  congr 1
  apply Fin.ext
  change (addCounter (counts security).margin index.val).count = (bodyEquiv security index).val.val
  rw [addCounter_value, bodyEquiv_value]

def centerDataWork (security : ℕ) : ℕ :=
  (counts security).safe * (2 * (counts security).margin +
    3 * (PublicParameterProgram.modulus security).count + 8) + 2



structure Cache (security bits : ℕ) where
  primary : ProbabilityArray (PublicParameterProgram.modulus security).count
  body : ProbabilityArray (counts security).safe
  activation : RationalBits
  primary_value : ∀ index, (primary.data.get index).decode = RationalProposalProgram.primary security bits index.val
  body_value : ∀ index, (body.data.get index).decode = RationalProposalProgram.center security bits (bodyEquiv security index).val.val
  activation_value : activation.decode = LocalPairProgram.activationApprox security bits

 theorem body_mass (security bits : ℕ) :
    (∑ color : ActualControls.SafePalette security, RationalProposalProgram.center security bits color.val.val) = 1 := by
  have h := (RationalProposalProgram.approximateBodyReference security bits).sum_one
  change (∑ color : ActualControls.SafePalette security,
    (RationalProposalProgram.center security bits color.val.val : ℝ)) = 1 at h
  exact_mod_cast h

/-- Only the safe restriction is generated here; the already generated q by q
reference cache is reused without regenerating any Gaussian or anchor table. -/
def prepare (security bits : ℕ) (input : BinaryReferenceTables.Result security)
    (hinput : input = BinaryReferenceTables.current security bits) : CountedValue (Cache security bits) :=
  let center := centerData security input
  have hp (index) : (input.primary.get index).decode = RationalProposalProgram.primary security bits index.val := by
    rw [hinput]
    exact BinaryReferenceTables.primary_value security bits index
  have hb (index) : (center.value.get index).decode = RationalProposalProgram.center security bits (bodyEquiv security index).val.val := by
    rw [centerData_get, hinput, BinaryReferenceTables.center_value]
    rfl
  have hpn (index) : 0 ≤ (input.primary.get index).decode := by
    rw [hp]
    have h := (RationalProposalProgram.approximatePrimaryLaw security bits).nonneg (primaryEquiv security index)
    change (0 : ℝ) ≤ (RationalProposalProgram.primary security bits index.val : ℝ) at h
    exact_mod_cast h
  have hpm : (∑ index, (input.primary.get index).decode) = 1 := by
    simp_rw [hp]
    exact (Equiv.sum_comp (primaryEquiv security)
      (fun color => RationalProposalProgram.primary security bits color.val)).trans
      (RationalProposalProgram.primary_mass security bits)
  have hbn (index) : 0 ≤ (center.value.get index).decode := by
    rw [hb]
    exact RationalProposalProgram.center_nonneg security bits (bodyEquiv security index).val
  have hbm : (∑ index, (center.value.get index).decode) = 1 := by
    simp_rw [hb]
    exact (Equiv.sum_comp (bodyEquiv security)
      (fun color => RationalProposalProgram.center security bits color.val.val)).trans (body_mass security bits)
  ⟨⟨⟨input.primary, hpn, hpm⟩, ⟨center.value, hbn, hbm⟩, input.activation, hp, hb, by
      rw [hinput]; exact BinaryReferenceTables.activation_value security bits⟩,
    (counts security).work + center.work + 3⟩

@[simp] theorem prepare_primary (security bits : ℕ) (input : BinaryReferenceTables.Result security)
    (hinput : input = BinaryReferenceTables.current security bits) :
    (prepare security bits input hinput).value.primary.data = input.primary := rfl

@[simp] theorem prepare_body (security bits : ℕ) (input : BinaryReferenceTables.Result security)
    (hinput : input = BinaryReferenceTables.current security bits) :
    (prepare security bits input hinput).value.body.data = (centerData security input).value := rfl


def primaryDraw (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (word : Fin (drawBits + (PublicParameterProgram.modulus security).count + 1) → Fin 2) :
    CountedValue (FirstHistogram.Palette security) :=
  let selected := positiveDraw _ (colors_positive security) cache.primary drawBits word
  ⟨primaryEquiv security selected.value, (PublicParameterProgram.modulus security).work + selected.work + 1⟩

def bodyDraw (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (word : Fin (drawBits + (counts security).safe + 1) → Fin 2) :
    CountedValue (ActualControls.SafePalette security) :=
  let selected := positiveDraw _ (safe_positive security) cache.body drawBits word
  let added := addCounter (counts security).margin selected.value.val
  have he : added.count = (bodyEquiv security selected.value).val.val := by
    rw [addCounter_value, bodyEquiv_value]
  ⟨⟨⟨added.count, by rw [he]; exact (bodyEquiv security selected.value).val.isLt⟩, by
      simpa only [he] using (bodyEquiv security selected.value).property⟩,
    (counts security).work + selected.work + added.work + 2⟩









noncomputable section
open scoped Classical






def primaryDrawLaw (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    FiniteDist (FirstHistogram.Palette security) :=
  (FiniteDist.uniform (Fin (drawBits + (PublicParameterProgram.modulus security).count + 1) → Fin 2)).map
    (fun word => (primaryDraw security tableBits drawBits cache word).value)

def bodyDrawLaw (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    FiniteDist (ActualControls.SafePalette security) :=
  (FiniteDist.uniform (Fin (drawBits + (counts security).safe + 1) → Fin 2)).map
    (fun word => (bodyDraw security tableBits drawBits cache word).value)





end
end CurrentAFT.CurrentReferenceDraw

end

section


























/-! The auxiliary public activation bit is sampled from the executed cached
Gaussian zero mass; its two rational entries are an exact probability vector. -/
namespace CurrentAFT.CurrentActivationDraw
open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentProbabilityArrayDraw CurrentReferenceDraw
open scoped BigOperators
set_option maxHeartbeats 500000

def table (security tableBits : ℕ) (cache : Cache security tableBits) : CountedValue (ProbabilityArray 2) :=
  let negative := negate cache.activation
  let difference := add one negative.data
  let data := Vector.ofFn (fun index : Fin 2 => if index = 0 then difference.data else cache.activation)
  have hb : 0 ≤ cache.activation.decode ∧ cache.activation.decode ≤ 1 := by
    rw [cache.activation_value]
    have h := LocalPairProgram.activationApprox_bounds security tableBits
    constructor
    · exact_mod_cast h.1
    · apply (Rat.cast_le (K := ℝ)).mp
      exact h.2.trans (by norm_num)
  have he (index : Fin 2) : (data.get index).decode =
      if index = 0 then 1 - cache.activation.decode else cache.activation.decode := by
    simp only [data, Vector.get_ofFn]
    split_ifs <;> simp only [difference, negative, RationalBits.add_value, one_value, negate_value, sub_eq_add_neg]
  ⟨⟨data, by intro index; rw [he]; split_ifs <;> linarith, by
      simp [he, Fin.sum_univ_two]⟩,
    negative.work + difference.work + 4⟩

def draw (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (word : Fin (drawBits + 2 + 1) → Fin 2) : CountedValue Bool :=
  let probabilities := table security tableBits cache
  let selected := positiveDraw 2 (by decide) probabilities.value drawBits word
  ⟨finTwoEquiv selected.value, probabilities.work + selected.work + 2⟩








def workBound (height bits : ℕ) : ℕ :=
  2 * primitiveWorkBound height + CurrentProbabilityArrayDraw.workBound 2 (height + 1) bits + 6



noncomputable section
open scoped Classical

def approximateLaw (security tableBits : ℕ) : FiniteDist Bool where
  weight flag := if flag then (LocalPairProgram.activationApprox security tableBits : ℝ)
    else 1 - LocalPairProgram.activationApprox security tableBits
  nonneg flag := by
    have h := LocalPairProgram.activationApprox_bounds security tableBits
    cases flag <;> simp only [Bool.false_eq_true, if_false, if_true] <;> linarith
  sum_one := by simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]; ring



def drawLaw (security tableBits drawBits : ℕ) (cache : Cache security tableBits) : FiniteDist Bool :=
  (FiniteDist.uniform (Fin (drawBits + 2 + 1) → Fin 2)).map
    (fun word => (draw security tableBits drawBits cache word).value)







end
end CurrentAFT.CurrentActivationDraw

end

section




















/-! Exact target law and ticket error for the executed interval-index sampler. -/
namespace CurrentAFT.CurrentUniformDraw
open AFT AFT.BinaryArithmetic
open scoped BigOperators Classical
noncomputable section

def law (count : ℕ) (hpositive : 0 < count) (bits : ℕ) : FiniteDist (Fin count) :=
  (FiniteDist.uniform (Fin (bits + count + 1) → Fin 2)).map
    (fun word => (binaryUniformDraw count hpositive bits word).value)



end
end CurrentAFT.CurrentUniformDraw

end

section






















/-! Public anchor indices from the executed current width counter. -/
namespace CurrentAFT.CurrentAnchorIndexDraw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 400000

def width (security : ℕ) : UnaryCounterResult :=
  let base := addCounter security 2
  let result := powerCounter base.count 48
  ⟨result.count, base.work + result.work + 2⟩

theorem width_value (security : ℕ) : (width security).count = Parameters.anchorWidth security := by
  simp only [width, powerCounter_value, addCounter_value, Parameters.anchorWidth, Parameters.scale, Parameters.base, ← pow_mul]

theorem width_positive (security : ℕ) : 0 < (width security).count := by
  rw [width_value]
  exact InwardAnchor.anchorWidth_pos security

abbrev Tape (security bits : ℕ) := Fin (bits + (width security).count + 1) → Fin 2

def indexEquiv (security : ℕ) : Fin (width security).count ≃ InwardAnchor.Index security :=
  finCongr (width_value security)

def draw (security bits : ℕ) (word : Tape security bits) : CountedValue (InwardAnchor.Index security) :=
  let result := binaryUniformDraw (width security).count (width_positive security) bits word
  ⟨indexEquiv security result.value, (width security).work + result.work + 1⟩

def workBound (security bits : ℕ) : ℕ :=
  (width security).work + binaryUniformDrawWork (width security).count bits + 1



noncomputable section
open scoped Classical
local instance anchorNonempty (security : ℕ) : Nonempty (InwardAnchor.Index security) :=
  ⟨⟨0, InwardAnchor.anchorWidth_pos security⟩⟩

def law (security bits : ℕ) : FiniteDist (InwardAnchor.Index security) :=
  (FiniteDist.uniform (Tape security bits)).map (fun word => (draw security bits word).value)



end
end CurrentAFT.CurrentAnchorIndexDraw

end

section




























/-! Executed current public leg seeds. The protected first/second sources are
absent: activation, fair coin, anchor index and two blur edges are sampled
independently from the actual public reference data. -/
namespace CurrentAFT.CurrentPublicSeedDraw
open AFT AFT.GaussianSource AFT.RationalNumerics AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentReferenceDraw
open scoped BigOperators
set_option maxHeartbeats 800000
attribute [local irreducible] Parameters.anchorWidth Parameters.base

abbrev EdgeTape (security bits : ℕ) := Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) bits) → Fin 2
abbrev Tape (security bits : ℕ) := (Fin (bits + 2 + 1) → Fin 2) ×
  (Bool × (CurrentAnchorIndexDraw.Tape security bits × (EdgeTape security bits × EdgeTape security bits)))

def draw (security tableBits drawBits : ℕ) (cache : Cache security tableBits) (word : Tape security drawBits) :
    CountedValue (ActualPublicLegCharge.PublicSeed security) :=
  let activation := CurrentActivationDraw.draw security tableBits drawBits cache word.1
  let anchor := CurrentAnchorIndexDraw.draw security drawBits word.2.2.1
  let first := CurrentEdgeDrawProgram.draw security drawBits word.2.2.2.1
  let second := CurrentEdgeDrawProgram.draw security drawBits word.2.2.2.2
  ⟨⟨activation.value, word.2.1, anchor.value, (first.value, second.value)⟩,
    activation.work + anchor.work + first.work + second.work + 5⟩


def workBound (security height bits : ℕ) : ℕ :=
  CurrentActivationDraw.workBound height bits + CurrentAnchorIndexDraw.workBound security bits +
    2 * CurrentEdgeDrawProgram.workBound security bits + 5



noncomputable section
open scoped Classical
local instance anchorNonempty (security : ℕ) : Nonempty (InwardAnchor.Index security) :=
  ⟨⟨0, InwardAnchor.anchorWidth_pos security⟩⟩

def edgeLaw (security bits : ℕ) : FiniteDist (Window (DiffuseProfiles.edgeCutoff security)) :=
  (FiniteDist.uniform (EdgeTape security bits)).map (fun word => (CurrentEdgeDrawProgram.draw security bits word).value)

def tapeLaw (security bits : ℕ) : FiniteDist (Tape security bits) :=
  (FiniteDist.uniform (Fin (bits + 2 + 1) → Fin 2)).prod ((FiniteDist.uniform Bool).prod
    ((FiniteDist.uniform (CurrentAnchorIndexDraw.Tape security bits)).prod
      ((FiniteDist.uniform (EdgeTape security bits)).prod (FiniteDist.uniform (EdgeTape security bits)))))

def productLaw (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    FiniteDist (ActualPublicLegCharge.SeedProduct security) :=
  (CurrentActivationDraw.drawLaw security tableBits drawBits cache).prod ((FiniteDist.uniform Bool).prod
    ((CurrentAnchorIndexDraw.law security drawBits).prod ((edgeLaw security drawBits).prod (edgeLaw security drawBits))))

def law (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    FiniteDist (ActualPublicLegCharge.PublicSeed security) :=
  (tapeLaw security drawBits).map (fun word => (draw security tableBits drawBits cache word).value)







end
end CurrentAFT.CurrentPublicSeedDraw

end

section


























/-! Finite-bit public safe-baseline draws, with executed native interval offsets. -/
namespace CurrentAFT.CurrentSafeDraw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram CurrentReferenceDraw
open scoped BigOperators
set_option maxHeartbeats 500000

abbrev Tape (security bits : ℕ) := Fin (bits + (counts security).safe + 1) → Fin 2

def draw (security bits : ℕ) (word : Tape security bits) : CountedValue (FirstHistogram.Palette security) :=
  let selected := binaryUniformDraw (counts security).safe (safe_positive security) bits word
  let added := addCounter (counts security).margin selected.value.val
  have hi : added.count < Parameters.modulus security := by
    rw [addCounter_value, ← bodyEquiv_value]
    exact (bodyEquiv security selected.value).val.isLt
  ⟨⟨added.count, hi⟩, (counts security).work + selected.work + added.work + 2⟩





def workBound (security bits : ℕ) : ℕ :=
  (counts security).work + binaryUniformDrawWork (counts security).safe bits + 2 * (counts security).margin + 3



noncomputable section
open scoped Classical

def law (security bits : ℕ) : FiniteDist (FirstHistogram.Palette security) :=
  (FiniteDist.uniform (Tape security bits)).map (fun word => (draw security bits word).value)





end
end CurrentAFT.CurrentSafeDraw

end

section




































/-! Literal public proposal buffers. Controls, leg seeds and queue baselines
are materialized sequentially, as are both directions of the two public
permutations. The extra chart-input vector is gathered by charged array reads.
Every input tape is public and independent of the hidden Gaussian source. -/
namespace CurrentAFT.CurrentCoreProposal
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open ActualPublicCharge CurrentReferenceDraw CurrentProposalDimensions
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize
  CurrentPublicSeedDraw.draw CurrentSafeDraw.draw CurrentReferenceDraw.primaryDraw CurrentReferenceDraw.bodyDraw

abbrev ControlTape (security bits : ℕ) :=
  (Fin (bits + (PublicParameterProgram.modulus security).count + 1) → Fin 2) ×
    (Fin (bits + (CurrentReferenceDraw.counts security).safe + 1) → Fin 2)
abbrev LegTape (security bits : ℕ) := CurrentPublicSeedDraw.Tape security bits × CurrentSafeDraw.Tape security bits
abbrev Tapes (security bits : ℕ) :=
  ((((PublicOutputExperiment.PublicIndex security → ControlTape security bits) ×
      (Fin (Parameters.legCount security) → LegTape security bits)) ×
    (Fin (Parameters.modulus security) → CurrentSafeDraw.Tape security bits)) ×
      (Fin ((current security).body * bits) → Fin 2)) ×
      (Fin ((current security).dimension * bits) → Fin 2)

def controlDraw (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : ControlTape security bits) :
    CountedValue (SafeControlGroups.SafeGroup security) :=
  let primary := CurrentReferenceDraw.primaryDraw security tableBits bits cache word.1
  let body := CurrentReferenceDraw.bodyDraw security tableBits bits cache word.2
  ⟨(primary.value, body.value), primary.work + body.work + 2⟩

def legDraw (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : LegTape security bits) :
    CountedValue (LegCore security) :=
  let seed := CurrentPublicSeedDraw.draw security tableBits bits cache word.1
  let baseline := CurrentSafeDraw.draw security bits word.2
  ⟨(seed.value, baseline.value), seed.work + baseline.work + 2⟩

abbrev Controls (security : ℕ) := Vector (SafeControlGroups.SafeGroup security) (current security).controls
abbrev Legs (security : ℕ) := Vector (LegCore security) (current security).legs
abbrev Baselines (security : ℕ) := Vector (FirstHistogram.Palette security) (current security).colors

def decode (security : ℕ) (controls : Controls security) (legs : Legs security) (baselines : Baselines security)
    (body : CurrentPermutationDraw.CachedPermutation (current security).body)
    (endpoints : CurrentPermutationDraw.CachedPermutation (current security).dimension) : Core security where
  controls index := controls.get ((controlsEquiv security).symm index)
  legs index := legs.get ((legEquiv security).symm index)
  queueBaselines index := baselines.get ((queueEquiv security).symm index)
  bodyPermutation := (CurrentProposalDimensions.bodyEquiv security).permCongr body.toEquiv
  endpointPermutation := (endpointEquiv security).permCongr endpoints.toEquiv

def defaultControl (security : ℕ) : SafeControlGroups.SafeGroup security :=
  (⟨0, (Parameters.modulus_spec security).2.pos⟩,
    CurrentSafePaletteIndex.equiv security ⟨0, CurrentSafePaletteIndex.count_positive security⟩)

def defaultLeg (security : ℕ) : LegCore security :=
  ((CurrentChartsDraw.defaultInput security).2, (defaultControl security).1)

def gatherInputs (security : ℕ) (controls : Controls security) (legs : Legs security) :
    CountedValue (CurrentChartsDraw.InputVector security) :=
  let data := storeData (current security).legs (fun index =>
    let address := (controlsEquiv security).symm (.inl (legEquiv security index))
    let control := readVector (defaultControl security) controls address
    let leg := readVector (defaultLeg security) legs index
    ⟨(control.value.1, leg.value.1), control.work + leg.work + 2⟩)
  ⟨data.value.cast (current_values security).2.1, (current security).work + data.work + 2⟩

theorem gatherInputs_value (security : ℕ) (controls : Controls security) (legs : Legs security)
    (index : Fin (Parameters.legCount security)) :
    (gatherInputs security controls legs).value.get index =
      ((controls.get ((controlsEquiv security).symm (.inl index))).1,
        (legs.get ((legEquiv security).symm index)).1) := by
  simp only [gatherInputs, Vector.get_cast, storeData_get, readVector_value]
  rfl

structure MaterializedCore (security : ℕ) where
  controls : Controls security
  legs : Legs security
  baselines : Baselines security
  body : CurrentPermutationDraw.CachedPermutation (current security).body
  endpoints : CurrentPermutationDraw.CachedPermutation (current security).dimension
  inputs : CurrentChartsDraw.InputVector security
  inputs_correct : ∀ index, inputs.get index =
    ((controls.get ((controlsEquiv security).symm (.inl index))).1,
      (legs.get ((legEquiv security).symm index)).1)

def MaterializedCore.core {security : ℕ} (data : MaterializedCore security) : Core security :=
  decode security data.controls data.legs data.baselines data.body data.endpoints

def MaterializedCore.cached {security : ℕ} (data : MaterializedCore security) : CurrentPublicCompletion.CachedCore security :=
  ⟨data.core, data.inputs, by
    apply Vector.ext
    intro index hindex
    change data.inputs.get ⟨index, hindex⟩ = _
    rw [data.inputs_correct]
    simp only [CurrentChartsDraw.inputsOfCore, Vector.getElem_ofFn, MaterializedCore.core, decode]⟩

def draw (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : Tapes security bits) :
    CountedValue (MaterializedCore security) :=
  let controls := storeData (current security).controls (fun index =>
    let address := CurrentPublicIndexProgram.decode security index
    let result := controlDraw security tableBits bits cache (word.1.1.1.1 address.value)
    ⟨result.value, address.work + result.work + 2⟩)
  let legs := storeData (current security).legs (fun index =>
    legDraw security tableBits bits cache (word.1.1.1.2 (legEquiv security index)))
  let baselines := storeData (current security).colors (fun index =>
    CurrentSafeDraw.draw security bits (word.1.1.2 (queueEquiv security index)))
  let body := CurrentPermutationDraw.draw (current security).body bits (Vector.ofFn word.1.2)
  let endpoints := CurrentPermutationDraw.draw (current security).dimension bits (Vector.ofFn word.2)
  let inputs := gatherInputs security controls.value legs.value
  ⟨⟨controls.value, legs.value, baselines.value, body.value, endpoints.value, inputs.value,
      gatherInputs_value security controls.value legs.value⟩,
    (current security).work + controls.work + legs.work + baselines.work + body.work + endpoints.work + inputs.work +
      (current security).body * bits + (current security).dimension * bits + 9⟩











end CurrentAFT.CurrentCoreProposal

end

section


























/-! Bit-work bounds for all materialized public-core buffers and both
permutation directions. References to a stored control/leg use readVector. -/
namespace CurrentAFT.CurrentCoreProposalWork
open AFT AFT.BinaryArithmetic AFT.RationalNumerics AFT.RationalRejectionProgram
open CurrentReferenceDraw CurrentProposalDimensions CurrentCoreProposal
set_option maxHeartbeats 1000000
attribute [local irreducible] CurrentProposalDimensions.current CurrentReferenceDraw.counts
  PublicParameterProgram.modulus CurrentPublicSeedDraw.draw CurrentSafeDraw.draw
  CurrentReferenceDraw.primaryDraw CurrentReferenceDraw.bodyDraw


def controlWork (security height bits : ℕ) : ℕ :=
  (PublicParameterProgram.modulus security).work +
    CurrentProbabilityArrayDraw.workBound (PublicParameterProgram.modulus security).count height bits + 1 +
    (CurrentReferenceDraw.counts security).work +
    CurrentProbabilityArrayDraw.workBound (CurrentReferenceDraw.counts security).safe height bits +
      2 * (CurrentReferenceDraw.counts security).margin + 3 + 2

def legWork (security height bits : ℕ) : ℕ :=
  CurrentPublicSeedDraw.workBound security height bits + CurrentSafeDraw.workBound security bits + 2





def gatherWork (security : ℕ) : ℕ := (current security).work +
  (current security).legs * (3 * (current security).controls + 3 * (current security).legs + 10) + 4



def workBound (security height bits : ℕ) : ℕ :=
  (current security).work +
    ((current security).controls * (CurrentPublicIndexProgram.workBound security + controlWork security height bits + 4) + 2) +
    ((current security).legs * (legWork security height bits + 2) + 2) +
    ((current security).colors * (CurrentSafeDraw.workBound security bits + 2) + 2) +
    CurrentPermutationDraw.workBound (current security).body bits +
    CurrentPermutationDraw.workBound (current security).dimension bits + gatherWork security +
    (current security).body * bits + (current security).dimension * bits + 9



end CurrentAFT.CurrentCoreProposalWork

end

section


























/-! Polynomial preparation of the same reference cache for proposal sampling. -/
namespace CurrentAFT.CurrentReferenceCacheWork
open AFT AFT.BinaryArithmetic AFT.RationalNumerics CurrentReferenceDraw
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
attribute [local irreducible] PublicParameterProgram.modulus BinaryActivationProgram.cutoff
  CurrentReferenceDraw.counts BinaryReferenceTables.current
  addCounter multiplyCounter doubleCounter subtractCounter

noncomputable def countsWorkPolynomial : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial + BinaryActivationProgram.cutoffWorkPolynomial +
    (2 * (Polynomial.X + 2)^2 + 1) + (3 * (2 * ((Polynomial.X + 2)^2 + 1) + 3) + 1) +
    (9 * (Polynomial.X + 2)^2 + 1) +
    (2 * CurrentProposalResources.primeSizePolynomial + 2) + 6

 theorem counts_work (security : ℕ) : (counts security).work ≤ countsWorkPolynomial.eval security := by
  let colors := PublicParameterProgram.modulus security
  let window := BinaryActivationProgram.cutoff security
  let square := addCounter window.count 1
  let margin := multiplyCounter 3 square.count
  let double := doubleCounter margin.count
  have hc := PublicParameterProgram.modulus_work security
  have hw := BinaryActivationProgram.cutoff_work security
  have hq : colors.count ≤ 131072 * (security + 2)^64 := by
    rw [show colors.count = Parameters.modulus security from PublicParameterProgram.modulus_value security]
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hwindow : window.count ≤ (security + 2)^2 := by
    have hv : window.count = (security + 2)^2 - 1 := BinaryActivationProgram.cutoff_value security
    exact hv ▸ Nat.sub_le _ _
  have hs : square.count ≤ (security + 2)^2 + 1 := by
    rw [show square.count = window.count + 1 from addCounter_value _ _]
    exact Nat.add_le_add_right hwindow 1
  have hm : margin.count = 3 * (security + 2)^2 := BinaryBodyProgram.margin_value security
  have hsub := subtractCounter_work_left colors.count double.count
  change colors.work ≤ _ at hc
  change window.work ≤ _ at hw
  unfold CurrentReferenceDraw.counts
  change colors.work + window.work + square.work + margin.work + double.work +
    (subtractCounter colors.count double.count).work + 6 ≤ _
  have hsw : square.work = 2 * window.count + 1 := addCounter_work _ _
  have hmw : margin.work = 3 * (2 * square.count + 3) + 1 := multiplyCounter_work _ _
  have hdw : double.work = 3 * margin.count + 1 := doubleCounter_work _
  have hmwbound : margin.work ≤ 3 * (2 * ((security + 2)^2 + 1) + 3) + 1 := by
    rw [hmw]
    gcongr
  rw [hm] at hdw
  simp only [countsWorkPolynomial, CurrentProposalResources.primeSizePolynomial,
    PublicParameterProgram.workPolynomial_eval, BinaryActivationProgram.cutoffWorkPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

 theorem native_bounds (security : ℕ) :
    (PublicParameterProgram.modulus security).count ≤ CurrentProposalResources.countPolynomial.eval security ∧
    (counts security).safe ≤ CurrentProposalResources.countPolynomial.eval security ∧
    (counts security).margin ≤ CurrentProposalResources.countPolynomial.eval security := by
  have hq := (BinaryProposalMetadata.counts_bounds security).1
  rw [(BinaryProposalMetadata.counts_value security).1] at hq
  have hb : 1 ≤ security + 2 := by omega
  have hbase : (security + 2)^2 ≤ (security + 2)^160 := Nat.pow_le_pow_right hb (by decide)
  rcases counts_values security with ⟨_, hm, hs⟩
  simp only [CurrentProposalResources.countPolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat,
    BinaryProposalMetadata.sizePolynomial_eval]
  constructor
  · rw [PublicParameterProgram.modulus_value]
    omega
  constructor
  · rw [hs]
    unfold CurrentSafePaletteIndex.count
    exact (Nat.sub_le _ _).trans (by omega)
  · rw [hm, Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]
    unfold BinaryProposalMetadata.sizeBound
    omega

 

 

end
end CurrentAFT.CurrentReferenceCacheWork

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentReferenceCacheWork.countsWorkPolynomial
  pure ()

end

section






























/-! Closed polynomial envelopes for the executed proposal primitives. -/
namespace CurrentAFT.CurrentProposalSamplerPolynomial
open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalNumerics
open CurrentProposalResources
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus
  CurrentProposalDimensions.current CurrentReferenceDraw.counts addCounter powerCounter

noncomputable def ticketPolynomial (count height bits : Polynomial ℕ) : Polynomial ℕ :=
  (2 * bits + 1) + binaryRationalDrawPolynomial count height (bits + count + 1) + 3

 

 

noncomputable def widthWorkPolynomial : Polynomial ℕ :=
  2 * Polynomial.X + 1 + 49 * (6 * (Polynomial.X + 3)^50 + 4) + 2

 theorem width_work (security : ℕ) : (CurrentAnchorIndexDraw.width security).work ≤ widthWorkPolynomial.eval security := by
  have h := powerCounter_work (security + 2) 48
  simp only [CurrentAnchorIndexDraw.width, addCounter_value, addCounter_work,
    widthWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X, powerCounterWork] at h ⊢
  norm_num only at h ⊢
  simpa only [Nat.add_assoc, show security + 2 + 1 = security + 3 by omega] using Nat.add_le_add_left (Nat.add_le_add_right h 2) (2*security+1)

 theorem width_count (security : ℕ) : (CurrentAnchorIndexDraw.width security).count ≤ countPolynomial.eval security := by
  rw [CurrentAnchorIndexDraw.width_value]
  have hb : 1 ≤ security + 2 := by omega
  have hp := Nat.pow_le_pow_right hb (by decide : 48 ≤ 160)
  simp only [countPolynomial, BinaryProposalMetadata.sizePolynomial, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
    Parameters.anchorWidth, Parameters.scale, Parameters.base, ← pow_mul]
  norm_num only
  omega

noncomputable def edgeCutoffWorkPolynomial : Polynomial ℕ :=
  2 * Polynomial.X + 1 + 3 * (6 * (Polynomial.X + 3)^4 + 4) + (2 * (Polynomial.X + 2)^2 + 1) +
    500 * ((Polynomial.X + 2)^2 + 4)^2 + 4

 theorem edgeCutoffWorkPolynomial_eval (security : ℕ) :
    edgeCutoffWorkPolynomial.eval security = CurrentEdgeDrawProgram.cutoffWork security := by
  simp only [edgeCutoffWorkPolynomial, CurrentEdgeDrawProgram.cutoffWork, powerCounterWork,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  norm_num only
  simp only [show security + 2 + 1 = security + 3 by omega]

noncomputable def edgeWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  let cutoff := (Polynomial.X + 2)^2
  edgeCutoffWorkPolynomial + CurrentGaussianBits.workPolynomial (bits + 1) +
    binaryRationalDrawPolynomial (2 * cutoff + 1) (500000000 * (cutoff + (bits + 1) + 2)^6)
      (bits + (2 * cutoff + 1) + 2) + 6 * cutoff + 7 + 2

 

end
end CurrentAFT.CurrentProposalSamplerPolynomial

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentProposalSamplerPolynomial.ticketPolynomial
  pure ()

end

section

































/-! Closed current-parameter polynomial resources for the actual binary root
reference atom. The body sites and touched Gaussian words are both executed. -/
namespace CurrentAFT.BinaryRootReferenceResources
open AFT GaussianSource RationalNumerics BinaryArithmetic RationalRejectionProgram
open CurrentProposalResources BinaryRootSignedMass
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus


def bodyPolynomial : Polynomial ℕ := primeSizePolynomial*(Polynomial.X+2)^96

def cutoffPolynomial : Polynomial ℕ := (Polynomial.X+2)^2

def rootBitsPolynomial : Polynomial ℕ := 2*cutoffPolynomial+2


def bodyWorkPolynomial : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+2*Polynomial.X+1+97*(6*(Polynomial.X+3)^98+4)+
    primeSizePolynomial*(2*(Polynomial.X+2)^96+3)+5

 

 

 

 

 

 


def pointWorkPolynomial (count : ℕ) : Polynomial ℕ :=
  let R := rootBitsPolynomial
  let Q := primeSizePolynomial
  Polynomial.C count*(Polynomial.C (6*count)+
    (60*(R+Q+1)^2+50*(Q+1)^2+48*(R+Q+Q)+50)+11)+3

 


def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinarySparseCycleAveragePolynomial.heightPolynomial 1 bodyPolynomial cutoffPolynomial precision 0


def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  bodyWorkPolynomial+CurrentProposalSamplerPolynomial.edgeCutoffWorkPolynomial+PublicParameterProgram.workPolynomial+
    50*(primeSizePolynomial+1)^2+
    BinarySparseCycleAveragePolynomial.workPolynomial 1 bodyPolynomial cutoffPolynomial precision 0 (pointWorkPolynomial 1)+11

 

end
end CurrentAFT.BinaryRootReferenceResources

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootReferenceResources.bodyPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootReferenceResources.bodyWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootReferenceResources.cutoffPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootReferenceResources.pointWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootReferenceResources.rootBitsPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootReferenceResources.workPolynomial
  pure ()

end

section





























/-! # Actual reference-root averaging of an arbitrary joint finite mass -/
namespace CurrentAFT.BinaryRootAverage
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryRootSignedMass.referenceEntry
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def term (security bits : ℕ) (kernel : IntegerBits → RationalResult) (root : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter root.val
  let probability := BinaryRootSignedMass.referenceEntry security bits root.val
  let column := kernel ⟨false,code.digits⟩
  let result := RationalBits.multiply probability.data column.data
  ⟨result.data,code.work+probability.work+column.work+result.work+4⟩

def current (security bits : ℕ) (kernel : IntegerBits → RationalResult) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := sumFin modulus.count (term security bits kernel)
  ⟨result.data,modulus.work+result.work+2⟩



noncomputable section
def termHeightPolynomial (precision leafBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootReferenceResources.heightPolynomial precision+leafBits
def termWorkPolynomial (precision leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryRootReferenceResources.workPolynomial precision+leafWork+
    primitiveWorkPolynomial (termHeightPolynomial precision leafBits)+4
def heightPolynomial (precision leafBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(termHeightPolynomial precision leafBits+1)
def workPolynomial (precision leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryFirstInverseProgram.colorsPolynomial*
    (termWorkPolynomial precision leafBits leafWork+
      primitiveWorkPolynomial ((BinaryFirstInverseProgram.colorsPolynomial+1)*(termHeightPolynomial precision leafBits+1))+2)+4





end
end CurrentAFT.BinaryRootAverage

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootAverage.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootAverage.termHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootAverage.termWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootAverage.workPolynomial
  pure ()

end

section





























/-! # Polynomial resources for the complete centered leg mass -/
namespace CurrentAFT.BinaryLegMass
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

def meanHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootAverage.heightPolynomial precision (atRootHeightPolynomial precision BinaryFirstInverseProgram.colorsPolynomial)
def meanWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootAverage.workPolynomial precision (atRootHeightPolynomial precision BinaryFirstInverseProgram.colorsPolynomial)
    (atRootWorkPolynomial precision BinaryFirstInverseProgram.colorsPolynomial)



def differenceOperandPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  atRootHeightPolynomial precision rootBits+meanHeightPolynomial precision
def differenceHeightPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  differenceOperandPolynomial precision rootBits+1
def differenceWorkPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  atRootWorkPolynomial precision rootBits+meanWorkPolynomial precision+
    2*primitiveWorkPolynomial (differenceOperandPolynomial precision rootBits)+5



end
end CurrentAFT.BinaryLegMass

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryLegMass.differenceHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryLegMass.differenceOperandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryLegMass.differenceWorkPolynomial
  pure ()

end

section


























/-! # First-degree table dispatch with charged natural-index reads -/
namespace CurrentAFT.BinaryFirstCoefficient
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def current (order : ℕ) (primary body : ℕ → RationalResult) : CoefficientProgram order :=
  fun arity colors centers =>
    let primaryShape := BinaryFirstFamily.primaryGuard arity.val.1.val arity.val.2.val
    let bodyShape := BinaryFirstFamily.primaryGuard arity.val.2.val arity.val.1.val
    if hp : primaryShape.value=true then
      let input := readVector 0 colors ⟨0,by have := (BinaryFirstFamily.primaryGuard_value _ _).mp hp; omega⟩
      let result := primary input.value
      ⟨result.data,primaryShape.work+bodyShape.work+input.work+result.work+5⟩
    else if hb : bodyShape.value=true then
      let center := readVector 0 centers ⟨0,by have := (BinaryFirstFamily.primaryGuard_value _ _).mp hb; omega⟩
      let result := body center.value
      ⟨result.data,primaryShape.work+bodyShape.work+center.work+result.work+5⟩
    else ⟨zero,primaryShape.work+bodyShape.work+3⟩





end CurrentAFT.BinaryFirstCoefficient

end

section
























/-! # The actual singleton mass lifts have polynomial bit height and work -/
namespace CurrentAFT.BinaryRootProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open UniformBodyProfiles (BodyRole)
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current BinaryPaletteLookup.current
  BinaryShiftedSafeProfile.current PublicParameterProgram.modulus BinaryActivationProgram.cutoff
  BinaryRootConvolution.current BinaryMassLiftInput.current
noncomputable section

def deviationOperandPolynomial (precision queueBits rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  shiftedHeightPolynomial precision queueBits rootBits inputBits+meanHeightPolynomial precision queueBits inputBits
def deviationHeightPolynomial (precision queueBits rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  deviationOperandPolynomial precision queueBits rootBits inputBits+1
def deviationWorkPolynomial (precision queueBits rootBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  shiftedWorkPolynomial precision queueBits rootBits inputBits+meanWorkPolynomial precision queueBits inputBits+
    2*primitiveWorkPolynomial (deviationOperandPolynomial precision queueBits rootBits inputBits)+5



def meanDeviationOperandPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  meanHeightPolynomial precision queueBits inputBits+BinaryFirstInverseProgram.colorsPolynomial
def meanDeviationHeightPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*meanDeviationOperandPolynomial precision queueBits inputBits+1
def meanDeviationWorkPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+60*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    meanWorkPolynomial precision queueBits inputBits+
    3*primitiveWorkPolynomial (meanDeviationOperandPolynomial precision queueBits inputBits)+7



def densityInputHeightPolynomial (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  deviationHeightPolynomial precision queueBits rootBits BinaryFirstInverseProgram.colorsPolynomial
def densityInputWorkPolynomial (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    deviationWorkPolynomial precision queueBits rootBits BinaryFirstInverseProgram.colorsPolynomial+2
def meanDensityInputHeightPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  meanDeviationHeightPolynomial precision queueBits BinaryFirstInverseProgram.colorsPolynomial
def meanDensityInputWorkPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    meanDeviationWorkPolynomial precision queueBits BinaryFirstInverseProgram.colorsPolynomial+2





def firstDensityHeightPolynomial (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (densityInputHeightPolynomial precision queueBits rootBits)
def firstDensityWorkPolynomial (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.workPolynomial precision (densityInputHeightPolynomial precision queueBits rootBits)
    (densityInputWorkPolynomial precision queueBits rootBits)
def meanDensityHeightPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (meanDensityInputHeightPolynomial precision queueBits)
def meanDensityWorkPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.workPolynomial precision (meanDensityInputHeightPolynomial precision queueBits)
    (meanDensityInputWorkPolynomial precision queueBits)





end
end CurrentAFT.BinaryRootProfile

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.densityInputWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.deviationHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.deviationOperandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.deviationWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.meanDensityInputWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.meanDeviationHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.meanDeviationOperandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootProfile.meanDeviationWorkPolynomial
  pure ()

end

section
































/-! # The actual pure-primary singleton and its finite reciprocal are executed -/
namespace CurrentAFT.BinaryRootSingleton
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
open UniformBodyProfiles (BodyRole)
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def zeroProfile (_color : ℕ) : RationalResult := ⟨zero,1⟩

def first (security bits order : ℕ) (role : BodyRole) (queue root : IntegerBits) : CoefficientProgram order :=
  BinaryFirstCoefficient.current order
    (BinaryProfileLookup.current security (BinaryRootProfile.firstDensity security bits role queue root)) zeroProfile

def meanFirst (security bits order : ℕ) (role : BodyRole) (queue : IntegerBits) : CoefficientProgram order :=
  BinaryFirstCoefficient.current order
    (BinaryProfileLookup.current security (BinaryRootProfile.meanDensity security bits role queue)) zeroProfile

def positive (security bits order : ℕ) (role : BodyRole) (queue : IntegerBits) : CoefficientProgram order :=
  fun arity colors centers =>
    let unit := BinaryFamilyPower.unit order arity colors centers
    let first := meanFirst security bits order role queue arity colors centers
    let result := RationalBits.add unit.value first.value
    ⟨result.data,unit.work+first.work+result.work+2⟩

def inverse (security bits order : ℕ) (programs : List (Entry order)) (role : BodyRole) (queue : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyReciprocal.current order programs (positive security bits order role queue)

def current (security bits order : ℕ) (programs : List (Entry order)) (role : BodyRole)
    (queue root : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (first security bits order role queue root)
    (inverse security bits order programs role queue)

def normalized (security order : ℕ) (table : RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.pullback order (fun color => color%BinaryProfileLookup.colors security)
    (fun color => color%BinaryProfileLookup.colors security) table







noncomputable section
open scoped Classical





end
end CurrentAFT.BinaryRootSingleton

end

section
























/-! # Polynomial resources for the pure-primary singleton reciprocal -/
namespace CurrentAFT.BinaryRootSingleton
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
open UniformBodyProfiles (BodyRole)
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryProfileLookup.current BinaryRootProfile.firstDensity BinaryRootProfile.meanDensity
noncomputable section

def firstHeightPolynomial (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileLookup.heightPolynomial (BinaryRootProfile.firstDensityHeightPolynomial precision queueBits rootBits)
def firstWorkPolynomial (order : ℕ) (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (30*order+51)+BinaryProfileLookup.workPolynomial
    (BinaryRootProfile.firstDensityHeightPolynomial precision queueBits rootBits)
    (BinaryRootProfile.firstDensityWorkPolynomial precision queueBits rootBits)
def meanFirstHeightPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileLookup.heightPolynomial (BinaryRootProfile.meanDensityHeightPolynomial precision queueBits)
def meanFirstWorkPolynomial (order : ℕ) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (30*order+51)+BinaryProfileLookup.workPolynomial
    (BinaryRootProfile.meanDensityHeightPolynomial precision queueBits)
    (BinaryRootProfile.meanDensityWorkPolynomial precision queueBits)





def positiveHeightPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  meanFirstHeightPolynomial precision queueBits+1
def positiveWorkPolynomial (order : ℕ) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (12*order+8)+meanFirstWorkPolynomial order precision queueBits+
    primitiveWorkPolynomial (meanFirstHeightPolynomial precision queueBits)



def inverseHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyReciprocal.heightPolynomial order programs (positiveHeightPolynomial precision queueBits)
def inverseWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyReciprocal.workPolynomial order programs (positiveHeightPolynomial precision queueBits)
    (positiveWorkPolynomial order precision queueBits)



def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs
    (firstHeightPolynomial precision queueBits rootBits+inverseHeightPolynomial order programs precision queueBits)
def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs
    (firstHeightPolynomial precision queueBits rootBits+inverseHeightPolynomial order programs precision queueBits)
    (firstWorkPolynomial order precision queueBits rootBits+inverseWorkPolynomial order programs precision queueBits)



end
end CurrentAFT.BinaryRootSingleton

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootSingleton.firstWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootSingleton.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootSingleton.meanFirstWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootSingleton.positiveHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootSingleton.positiveWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootSingleton.workPolynomial
  pure ()

end

section
































namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.BinaryFamilyArithmetic
end CurrentAFT.BinaryFamilyArithmetic
namespace CurrentAFT.BinaryFamilyArithmetic.multiply
end CurrentAFT.BinaryFamilyArithmetic.multiply
namespace CurrentAFT.BinaryFamilyProduct
end CurrentAFT.BinaryFamilyProduct
namespace CurrentAFT.BinaryFamilyProduct.run
end CurrentAFT.BinaryFamilyProduct.run
namespace CurrentAFT.BinaryFamilyValidSemantics
end CurrentAFT.BinaryFamilyValidSemantics
namespace CurrentAFT.BinaryRootSingleton
end CurrentAFT.BinaryRootSingleton







/-! # The complete executed unselected leg, including its actual denominator -/
namespace CurrentAFT.BinaryUnselectedLeg
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev Descriptor := BinaryLegSelectedCoefficient.Entry

def higher (security bits order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (root : IntegerBits) : CoefficientProgram order :=
  BinaryLegFamily.higher security bits order fallback entries (BinaryLegMass.difference security bits root)

def positive (security bits order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 8) : CoefficientProgram order :=
  BinaryLegFamily.positive security bits order fallback entries (BinaryLegMass.mean security bits)

def inverse (security bits order : ℕ) (programs : List (Entry order)) (fallback : Descriptor)
    (entries : Vector Descriptor 8) : CoefficientProgram order :=
  BinaryFamilyReciprocal.current order programs (positive security bits order fallback entries)

def numerator (security bits order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (root : IntegerBits) : CoefficientProgram order := fun arity colors centers =>
  let first := BinaryRootSingleton.first security bits order .attachment BinaryProfileLookup.zeroRoot root arity colors centers
  let higher := higher security bits order fallback entries root arity colors centers
  let result := RationalBits.add first.value higher.value
  ⟨result.data,first.work+higher.work+result.work+2⟩

def current (security bits order : ℕ) (programs : List (Entry order)) (fallback : Descriptor)
    (entries : Vector Descriptor 8) (root : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (numerator security bits order fallback entries root)
    (inverse security bits order programs fallback entries)

noncomputable section
open scoped Classical











end
end CurrentAFT.BinaryUnselectedLeg

end

section





























/-! # The complete unselected leg has derived polynomial binary resources -/
namespace CurrentAFT.BinaryUnselectedLeg
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

def higherHeightPolynomial (entries : Vector Descriptor 8) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryLegFamily.sumHeightPolynomial entries precision (BinaryLegMass.differenceHeightPolynomial precision rootBits)
def higherWorkPolynomial (order : ℕ) (entries : Vector Descriptor 8) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryLegFamily.sumWorkPolynomial order 2 entries precision (BinaryLegMass.differenceHeightPolynomial precision rootBits)
    (BinaryLegMass.differenceWorkPolynomial precision rootBits)
def positiveHeightPolynomial (entries : Vector Descriptor 8) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryLegFamily.positiveHeightPolynomial entries precision (BinaryLegMass.meanHeightPolynomial precision)
def positiveWorkPolynomial (order : ℕ) (entries : Vector Descriptor 8) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryLegFamily.positiveWorkPolynomial order entries precision (BinaryLegMass.meanHeightPolynomial precision)
    (BinaryLegMass.meanWorkPolynomial precision)





def inverseHeightPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 8)
    (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyReciprocal.heightPolynomial order programs (positiveHeightPolynomial entries precision)
def inverseWorkPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 8)
    (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyReciprocal.workPolynomial order programs (positiveHeightPolynomial entries precision)
    (positiveWorkPolynomial order entries precision)



def numeratorOperandPolynomial (entries : Vector Descriptor 8) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootSingleton.firstHeightPolynomial precision 0 rootBits+higherHeightPolynomial entries precision rootBits
def numeratorHeightPolynomial (entries : Vector Descriptor 8) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  numeratorOperandPolynomial entries precision rootBits+1
def numeratorWorkPolynomial (order : ℕ) (entries : Vector Descriptor 8) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootSingleton.firstWorkPolynomial order precision 0 rootBits+higherWorkPolynomial order entries precision rootBits+
    primitiveWorkPolynomial (numeratorOperandPolynomial entries precision rootBits)+2



def heightPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 8)
    (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyProductClosure.heightPolynomial order programs (numeratorHeightPolynomial entries precision rootBits)
    (inverseHeightPolynomial order programs entries precision)
def workPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 8)
    (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyProductClosure.workPolynomial order programs (numeratorHeightPolynomial entries precision rootBits)
    (inverseHeightPolynomial order programs entries precision) (numeratorWorkPolynomial order entries precision rootBits)
    (inverseWorkPolynomial order programs entries precision)



end
end CurrentAFT.BinaryUnselectedLeg

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryUnselectedLeg.numeratorHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryUnselectedLeg.numeratorOperandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryUnselectedLeg.numeratorWorkPolynomial
  pure ()

end

section



























/-! # The full unselected leg channel on the stored three-slot source buffer -/
namespace CurrentAFT.BinaryLegGroup
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security
abbrev Descriptor := BinaryUnselectedLeg.Descriptor

def current (security bits order : ℕ) (programs : List (Entry order)) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (source : Vector (Fin (colors security)) 3) : CoefficientProgram order := fun arity colors centers =>
  let root := readVector (BinaryFirstFamily.first security) source 0
  let code := canonicalCounter root.value.val
  let result := BinaryUnselectedLeg.current security bits order programs fallback entries ⟨false,code.digits⟩ arity colors centers
  ⟨result.value,root.work+code.work+result.work+3⟩

noncomputable section
open scoped Classical



def heightPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 8) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryUnselectedLeg.heightPolynomial order programs entries precision BinaryFirstInverseProgram.colorsPolynomial
def workPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 8) (precision : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryUnselectedLeg.workPolynomial order programs entries precision BinaryFirstInverseProgram.colorsPolynomial+15



end
end CurrentAFT.BinaryLegGroup

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryLegGroup.workPolynomial
  pure ()

end

section


























/-! The original local seed average applied to an executed root-valued leaf.
The root is the difference of the two true sampled edge indices. -/
namespace CurrentAFT.BinarySeedRootAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff

def term (edgeCutoff scalarCutoff : ℕ) (kernel : IntegerBits → RationalResult)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) : RationalResult :=
  let root := BinaryBodyProgram.shift edgeCutoff scalarCutoff false left right scalar
  let result := kernel ⟨root.negative,root.digits⟩
  ⟨result.data,root.work+result.work+2⟩

def evaluate (security edgeCutoff scalarCutoff bits : ℕ) (kernel : IntegerBits → RationalResult) : RationalResult :=
  BinarySeedAverage.evaluate security edgeCutoff scalarCutoff bits (term edgeCutoff scalarCutoff kernel)

def current (security bits : ℕ) (kernel : IntegerBits → RationalResult) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let result := evaluate security parameters.cutoff window.count bits kernel
  ⟨result.data,parameters.work+window.work+result.work+3⟩





noncomputable section
noncomputable def rootBitsPolynomial : Polynomial ℕ := 4*(Polynomial.X+2)^2+2
noncomputable def termWorkPolynomial (leafWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBodyProgram.shiftWorkPolynomial ((Polynomial.X+2)^2)+leafWork+2
noncomputable def heightPolynomial (precision leafBits : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*(Polynomial.X+2)^2+1
  let gaussian := 500000000*((Polynomial.X+2)^2+precision+2)^6
  count*(gaussian+count*(count*(2*gaussian+leafBits+1)+1)+1)
noncomputable def workPolynomial (precision leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial+BinaryActivationProgram.cutoffWorkPolynomial+
    BinarySeedAverage.workPolynomial ((Polynomial.X+2)^2) ((Polynomial.X+2)^2) precision leafBits (termWorkPolynomial leafWork)+3



end
end CurrentAFT.BinarySeedRootAverage

end

section





























/-! The positive four-endpoint reference averages its two independent roots
inside the single actual scalar average. -/
namespace CurrentAFT.BinaryPositiveAverage
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits : ℕ) (word : Vector (Fin (colors security)) 4) : RationalResult :=
  BinaryScalarAverage.current security bits (fun scalar =>
    BinarySeedRootAverage.current security bits (fun compensator =>
      BinarySeedRootAverage.current security bits (fun attachment =>
        BinaryPositiveReference.fixedMass security bits compensator attachment scalar word)))



noncomputable section
noncomputable def inputBits : Polynomial ℕ := BinarySeedRootAverage.rootBitsPolynomial+BinaryCoefficientScalarAverage.scalarBitsPolynomial
noncomputable def innerHeight (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinarySeedRootAverage.heightPolynomial precision (BinaryPositiveReference.heightPolynomial precision inputBits)
noncomputable def innerWork (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinarySeedRootAverage.workPolynomial precision (BinaryPositiveReference.heightPolynomial precision inputBits)
    (BinaryPositiveReference.workPolynomial precision inputBits)
noncomputable def outerHeight (precision : Polynomial ℕ) : Polynomial ℕ := BinarySeedRootAverage.heightPolynomial precision (innerHeight precision)
noncomputable def outerWork (precision : Polynomial ℕ) : Polynomial ℕ := BinarySeedRootAverage.workPolynomial precision (innerHeight precision) (innerWork precision)
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryCoefficientScalarAverage.heightPolynomial precision (outerHeight precision)
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryCoefficientScalarAverage.workPolynomial precision (outerHeight precision) (outerWork precision)



end
end CurrentAFT.BinaryPositiveAverage

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPositiveAverage.inputBits
  pure ()

end

section





























/-! # A stored four-endpoint subset inserted in its actual coefficient fiber -/
namespace CurrentAFT.BinaryPrimarySelectedCoefficient
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  GradedControlAlgebra RationalRejectionProgram BinaryFamilyProduct
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure Entry where
  selected : Finset (Fin 4)
  slots : Vector (Fin 4) selected.card
  program : BinaryStoredSymmetrization.Program selected.card

def finite (security bits order : ℕ) (entry : Entry)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult) :
    BinaryFiniteCoefficient.FiniteProgram security order := fun arity colors centers =>
  let result := BinaryCoefficientFiber.current security arity.val.1.val arity.val.2.val entry.selected.card 0 colors centers
    (fun inputs _ => BinaryCoefficientExtraction.current security bits entry.slots entry.program inputs mass)
  ⟨result.data,result.work+4⟩

def current (security bits order : ℕ) (entry : Entry)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult) : CoefficientProgram order :=
  BinaryFiniteCoefficient.lift security order (finite security bits order entry mass)

noncomputable section
open scoped Classical





def heightPolynomial (entry : Entry) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientExtraction.heightPolynomial 4 entry.program precision inputBits
def finiteWorkPolynomial (order : ℕ) (entry : Entry) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (6*order+8*entry.selected.card+34)+BinaryCoefficientExtraction.workPolynomial 4 entry.program precision inputBits inputWork
def workPolynomial (order : ℕ) (entry : Entry) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFiniteCoefficient.workPolynomial order (finiteWorkPolynomial order entry precision inputBits inputWork)





def Valid (entry : Entry) : Prop :=
  (∀ index, entry.slots.get index=((Finset.orderIsoOfFin entry.selected rfl) index).val) ∧
    entry.program.meaning RationalBits.decode=BinaryStoredSymmetrization.meanSyntax entry.selected.card





end
end CurrentAFT.BinaryPrimarySelectedCoefficient

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimarySelectedCoefficient.finiteWorkPolynomial
  pure ()

end

section





























/-! # All sixteen stored subsets of the actual four-endpoint joint mass -/
namespace CurrentAFT.BinaryPrimaryFamily
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  GradedControlAlgebra RationalRejectionProgram BinaryFamilyProduct
open BinaryPrimarySelectedCoefficient
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def guarded (security bits order lower : ℕ) (entry : Entry)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult) : CoefficientProgram order :=
  fun arity colors centers =>
    let shape := lessCounter (lower-1) entry.selected.card
    if shape.value then
      let result := BinaryPrimarySelectedCoefficient.current security bits order entry mass arity colors centers
      ⟨result.value,shape.work+result.work+2⟩
    else ⟨zero,shape.work+2⟩

def sum (security bits order lower : ℕ) (fallback : Entry) (entries : Vector Entry 16)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult) : CoefficientProgram order :=
  BinarySubsetCoefficientSum.current order fallback entries (fun entry => guarded security bits order lower entry mass)



def positive (security bits order : ℕ) (fallback : Entry) (entries : Vector Entry 16)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 4 → RationalResult) : CoefficientProgram order :=
  fun arity colors centers =>
    let unit := BinaryFamilyPower.unit order arity colors centers
    let terms := sum security bits order 1 fallback entries mass arity colors centers
    let result := RationalBits.add unit.value terms.value
    ⟨result.data,unit.work+terms.work+result.work+2⟩

noncomputable section
open scoped Classical







noncomputable def leafHeight (entries : Vector Entry 16) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  ∑ index : Fin 16, BinaryPrimarySelectedCoefficient.heightPolynomial (entries.get index) precision inputBits
noncomputable def leafWork (order lower : ℕ) (entries : Vector Entry 16) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (3*lower+4)+∑ index : Fin 16,
    BinaryPrimarySelectedCoefficient.workPolynomial order (entries.get index) precision inputBits inputWork
noncomputable def heightPolynomial (entries : Vector Entry 16) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinarySubsetCoefficientSum.heightPolynomial 16 (leafHeight entries precision inputBits)
noncomputable def workPolynomial (order lower : ℕ) (entries : Vector Entry 16) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinarySubsetCoefficientSum.workPolynomial 16 (leafHeight entries precision inputBits) (leafWork order lower entries precision inputBits inputWork)



noncomputable def positiveHeightPolynomial (entries : Vector Entry 16) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  heightPolynomial entries precision inputBits+1
noncomputable def positiveWorkPolynomial (order : ℕ) (entries : Vector Entry 16) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (12*order+10)+workPolynomial order 1 entries precision inputBits inputWork+
    primitiveWorkPolynomial (heightPolynomial entries precision inputBits)



end
end CurrentAFT.BinaryPrimaryFamily

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryFamily.leafHeight
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryFamily.leafWork
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryFamily.positiveHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryFamily.positiveWorkPolynomial
  pure ()

end

section




























namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.BinaryFamilyArithmetic
end CurrentAFT.BinaryFamilyArithmetic
namespace CurrentAFT.BinaryFamilyArithmetic.multiply
end CurrentAFT.BinaryFamilyArithmetic.multiply
namespace CurrentAFT.BinaryFamilyProduct
end CurrentAFT.BinaryFamilyProduct
namespace CurrentAFT.BinaryFamilyProduct.run
end CurrentAFT.BinaryFamilyProduct.run
namespace CurrentAFT.BinaryFamilyValidSemantics
end CurrentAFT.BinaryFamilyValidSemantics





/-! The computed independent positive reference and its actual finite reciprocal. -/
namespace CurrentAFT.BinaryPositivePrimary
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
  GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
open BinaryPrimarySelectedCoefficient
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def positive (security bits order : ℕ) (fallback : BinaryPrimarySelectedCoefficient.Entry)
    (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) : CoefficientProgram order :=
  BinaryPrimaryFamily.positive security bits order fallback entries (BinaryPositiveAverage.current security bits)

def inverse (security bits order : ℕ) (programs : List (FixedFamilyPrograms.Entry order))
    (fallback : BinaryPrimarySelectedCoefficient.Entry) (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) : CoefficientProgram order :=
  BinaryFamilyReciprocal.current order programs (positive security bits order fallback entries)

noncomputable section
open scoped Classical





noncomputable def positiveHeight (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryFamily.positiveHeightPolynomial entries precision (BinaryPositiveAverage.heightPolynomial precision)
noncomputable def positiveWork (order : ℕ) (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryFamily.positiveWorkPolynomial order entries precision
    (BinaryPositiveAverage.heightPolynomial precision) (BinaryPositiveAverage.workPolynomial precision)



noncomputable def heightPolynomial (order : ℕ) (programs : List (FixedFamilyPrograms.Entry order))
    (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyReciprocal.heightPolynomial order programs (positiveHeight entries precision)
noncomputable def workPolynomial (order : ℕ) (programs : List (FixedFamilyPrograms.Entry order))
    (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyReciprocal.workPolynomial order programs (positiveHeight entries precision) (positiveWork order entries precision)



end
end CurrentAFT.BinaryPositivePrimary

end

section






























/-! # Actual centered primary point scores, materialized from the common reference -/
namespace CurrentAFT.BinaryPrimaryCenteredScore
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current PublicParameterProgram.modulus
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def point {count : ℕ} (atom : RationalBits) (source output : Fin count) : RationalResult :=
  let delta := BinaryMassLiftColumn.point source output
  let result := difference delta.data atom
  ⟨result.data,delta.work+result.work+2⟩



def current (security bits : ℕ) (source : Fin (colors security)) : ArrayResult (colors security) :=
  let modulus := PublicParameterProgram.modulus security
  let references := BinaryReferenceTables.current security bits
  let atom := readVector zero references.primary source
  let result := buildArray modulus.count (point atom.value source)
  ⟨result.data,modulus.work+references.work+atom.work+result.work+4⟩



def pointWork (count bits : ℕ) := 12*count+7+2*primitiveWorkBound (bits+1)+4



noncomputable section
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryReferenceTables.heightPolynomial precision+2
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryReferenceTables.currentWorkPolynomial precision+
    3*BinaryFirstInverseProgram.colorsPolynomial+3+
    BinaryFirstInverseProgram.colorsPolynomial*(12*BinaryFirstInverseProgram.colorsPolynomial+7+
      2*primitiveWorkPolynomial (BinaryReferenceTables.heightPolynomial precision+1)+6)+2+4



end
end CurrentAFT.BinaryPrimaryCenteredScore

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryCenteredScore.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryCenteredScore.workPolynomial
  pure ()

end

section






























/-! # The genuine weighted paired-score numerator, without division by a center atom -/
namespace CurrentAFT.BinaryRootWeightedScore
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current

def cached {count : ℕ} (primary centerLaw score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (rate : RationalBits) (input center : Fin count) : RationalResult :=
  let profile := sumFin count (BinaryPairedScore.term primary score anchor center)
  let first := readVector zero score input
  let body := readVector zero centerLaw center
  let leading := RationalBits.multiply body.value first.value
  let correction := RationalBits.multiply rate profile.data
  let result := difference leading.data correction.data
  ⟨result.data,profile.work+first.work+body.work+leading.work+correction.work+result.work+5⟩



def current (security bits : ℕ) (score : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (input center : Fin (PublicParameterProgram.modulus security).count) : RationalResult :=
  let refs := BinaryReferenceTables.current security bits
  let result := cached refs.primary refs.center score refs.anchor refs.activation input center
  ⟨result.data,refs.work+result.work+2⟩







noncomputable section
noncomputable def operandPolynomial (precision scoreBits : Polynomial ℕ) : Polynomial ℕ := BinaryReferenceTables.heightPolynomial precision+scoreBits
noncomputable def heightPolynomial (precision scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCurrentPaired.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial (operandPolynomial precision scoreBits)
noncomputable def workPolynomial (precision scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+
    BinaryCurrentPaired.evaluationWorkPolynomial BinaryFirstInverseProgram.colorsPolynomial (operandPolynomial precision scoreBits)+2



end
end CurrentAFT.BinaryRootWeightedScore

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootWeightedScore.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootWeightedScore.operandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootWeightedScore.workPolynomial
  pure ()

end

section





























/-! Actual four-endpoint centered primary mass before scalar/root averaging. -/
namespace CurrentAFT.BinaryPrimaryFixedMass
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
  BinaryFourPointPair.current BinaryRootControlRest.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def term (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (score : Vector RationalBits (colors security))
    (word : Vector (Fin (colors security)) 4) (primary center : Fin (colors security)) : RationalResult :=
  let references := BinaryReferenceTables.current security bits
  let p := readVector zero references.primary primary
  let b := BinaryRootWeightedScore.current security bits score primary center
  let pair := BinaryFourPointPair.current security bits primary scalar word
  let rest := BinaryRootControlRest.current security compensator attachment scalar center word
  let first := RationalBits.multiply p.value b.data
  let second := RationalBits.multiply first.data pair.data
  let final := RationalBits.multiply second.data rest.data
  ⟨final.data,references.work+p.work+b.work+pair.work+rest.work+first.work+second.work+final.work+8⟩



def fixedMass (security bits : ℕ) (compensator attachment scalar : IntegerBits)
    (score : Vector RationalBits (colors security))
    (word : Vector (Fin (colors security)) 4) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := sumFin modulus.count (fun primary => sumFin modulus.count (term security bits compensator attachment scalar score word primary))
  ⟨result.data,modulus.work+result.work+2⟩






noncomputable section
noncomputable def termHeightPolynomial (precision inputBits scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.heightPolynomial precision+BinaryRootWeightedScore.heightPolynomial precision scoreBits+BinaryFourPointPair.heightPolynomial precision inputBits+
    BinaryRootControlRest.heightPolynomial inputBits
noncomputable def termWorkPolynomial (precision inputBits scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+3*BinaryFirstInverseProgram.colorsPolynomial+11+
    BinaryRootWeightedScore.workPolynomial precision scoreBits+
    BinaryFourPointPair.workPolynomial precision inputBits+BinaryRootControlRest.workPolynomial inputBits+
    3*primitiveWorkPolynomial (termHeightPolynomial precision inputBits scoreBits)



noncomputable def innerHeightPolynomial (precision inputBits scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(termHeightPolynomial precision inputBits scoreBits+1)
noncomputable def innerWorkPolynomial (precision inputBits scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  Q*(termWorkPolynomial precision inputBits scoreBits+primitiveWorkPolynomial ((Q+1)*(termHeightPolynomial precision inputBits scoreBits+1))+2)+2
noncomputable def heightPolynomial (precision inputBits scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(innerHeightPolynomial precision inputBits scoreBits+1)
noncomputable def workPolynomial (precision inputBits scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  PublicParameterProgram.workPolynomial+Q*(innerWorkPolynomial precision inputBits scoreBits+
    primitiveWorkPolynomial ((Q+1)*(innerHeightPolynomial precision inputBits scoreBits+1))+2)+4



end
end CurrentAFT.BinaryPrimaryFixedMass

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryFixedMass.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryFixedMass.innerHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryFixedMass.innerWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryFixedMass.termHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryFixedMass.termWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryFixedMass.workPolynomial
  pure ()

end

end


