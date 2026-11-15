-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_10_Part_2_Stage_3
-- name    : InfoLossLAR_NativeBundle_10_Part_2_Stage_3
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T19:07:18.256059+00:00
-- url     : https://prove2.me/theorems/164f5673-7d37-4096-a168-3f05aa13f0de
-- title:
--   Paired tensors and physical weight coordinates
-- statement:
--   This package defines two-pool averages, paired scores and their tensor representations, physical-weight coordinates, and numerical weight-evaluation interfaces. It keeps the finite binary data distinct from their ideal real-valued semantics.
-- source:
--   Unchanged scope-closed source modules from local proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0, regrouped into a smaller semantic compilation unit after two terminal platform timeouts. All original source-body hashes are preserved; all 11528 public native/runtime types and recursive standard-axiom audits pass. Source SHA256 dc18db29bce3452434e1915bbc6347d23555bf1a1b3c3f010977d6f6830bfd9b. Compiler-only optimization: one local scope marks Polynomial addition and multiplication instances irreducible while generating native equation lemmas. Every original definition and proof source body is unchanged; all11528 public types and recursive standard-axiom audits pass. New sourceSHA256 a527ff0c00652f7960c6afc0931b58bf36dd2780f6004dad2e5fa9e6e6b64e04.

import Definitions.Def_InfoLossLAR_NativeBundle_10_Part_2_Stage_2

section
attribute [local irreducible] Polynomial.instAdd Polynomial.instMul

section




















/-! # Binary averaging over actual distinct choices in two pools -/
namespace CurrentAFT.BinaryTwoPoolAverage
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def current (primaryPool bodyPool r s : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (kernel : Vector (Fin primaryPool) r → Vector (Fin bodyPool) s → RationalResult) : RationalResult :=
  let numerator := BinaryDistinctTuples.sum primaryPool r hp (fun primary =>
    BinaryDistinctTuples.sum bodyPool s hb (kernel primary))
  let primaryMass := BinaryDistinctTuples.normalizer primaryPool r hp
  let bodyMass := BinaryDistinctTuples.normalizer bodyPool s hb
  let denominator := RationalBits.multiply primaryMass.data bodyMass.data
  let result := quotient numerator.data denominator.data
  ⟨result.data, numerator.work+primaryMass.work+bodyMass.work+denominator.work+result.work+5⟩

def normalizerHeight (pool count : ℕ) : ℕ := BinaryTupleSum.height pool count 0
def normalizerWork (pool count : ℕ) : ℕ := BinaryTupleSum.work pool count 0 (BinaryDistinctTuples.work pool count+3)
def numeratorHeight (primaryPool bodyPool r s leafHeight : ℕ) : ℕ :=
  BinaryTupleSum.height primaryPool r (BinaryTupleSum.height bodyPool s leafHeight)
def numeratorWork (primaryPool bodyPool r s leafHeight leafWork : ℕ) : ℕ :=
  BinaryTupleSum.work primaryPool r (BinaryTupleSum.height bodyPool s leafHeight)
    (BinaryDistinctTuples.work primaryPool r+
      BinaryTupleSum.work bodyPool s leafHeight (BinaryDistinctTuples.work bodyPool s+leafWork+2)+2)
def height (primaryPool bodyPool r s leafHeight : ℕ) : ℕ :=
  numeratorHeight primaryPool bodyPool r s leafHeight+normalizerHeight primaryPool r+normalizerHeight bodyPool s
def work (primaryPool bodyPool r s leafHeight leafWork : ℕ) : ℕ :=
  numeratorWork primaryPool bodyPool r s leafHeight leafWork+normalizerWork primaryPool r+normalizerWork bodyPool s+
    primitiveWorkBound (normalizerHeight primaryPool r+normalizerHeight bodyPool s)+
    2*primitiveWorkBound (height primaryPool bodyPool r s leafHeight)+7

noncomputable section
open scoped Classical





end
end CurrentAFT.BinaryTwoPoolAverage

end

section


















/-! # Binary evaluation of a paired score from stored reference tables

Every reference and score lookup is a sequential array read. The returned
rational is formed by binary arithmetic, with explicit height and work
bounds. Reference-table construction is accounted for separately.
-/
namespace CurrentAFT.BinaryPairedScore
open AFT AFT.RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000

def term {count : ℕ} (primary score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (center color : Fin count) : RationalResult :=
  let p := readVector zero primary color
  let f := readVector zero score color
  let a := matrixEntry anchor color center
  let product := multiply p.value f.value
  let result := multiply product.data a.value
  ⟨result.data, p.work + f.work + a.work + product.work + result.work + 2⟩



def current {count : ℕ} (primary centerLaw score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (rate : RationalBits)
    (input center : Fin count) : RationalResult :=
  let profile := sumFin count (term primary score anchor center)
  let first := readVector zero score input
  let body := readVector zero centerLaw center
  let reciprocal := inverse body.value
  let activated := multiply rate profile.data
  let correction := multiply activated.data reciprocal.data
  let negative := negate correction.data
  let result := add first.value negative.data
  ⟨result.data, profile.work + first.work + body.work + reciprocal.work + activated.work +
    correction.work + negative.work + result.work + 6⟩



def height (count bits : ℕ) : ℕ := (count + 1) * (3 * bits + 1) + 3 * bits + 3
def work (count bits : ℕ) : ℕ :=
  count * (13 * count + 18 + 3 * primitiveWorkBound (height count bits)) +
    6 * count + 14 + 5 * primitiveWorkBound (height count bits)









end CurrentAFT.BinaryPairedScore

end

section




























/-! # The current paired evaluator with its reference cache generated

Only the score vector is an input.  Every reference table is produced by
`BinaryReferenceTables.current`, including its full production cost.
-/
namespace CurrentAFT.BinaryCurrentPaired
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def scoreAt {count : ℕ} (score : Vector RationalBits count) (output : ℕ) : ℚ :=
  if h : output < count then (score.get ⟨output, h⟩).decode else 0







noncomputable section


noncomputable def heightPolynomial (count bound : Polynomial ℕ) : Polynomial ℕ :=
  (count+1)*(3*bound+1)+3*bound+3
noncomputable def evaluationWorkPolynomial (count bound : Polynomial ℕ) : Polynomial ℕ :=
  count*(13*count+18+3*primitiveWorkPolynomial (heightPolynomial count bound))+
    6*count+14+5*primitiveWorkPolynomial (heightPolynomial count bound)







end
end CurrentAFT.BinaryCurrentPaired

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCurrentPaired.evaluationWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCurrentPaired.heightPolynomial
  pure ()

end

section



























/-! # All primary slots of a joint kernel evaluated on stored binary data

The recursive score profile is materialized before each paired operation.
Groups and tuple tails are read by sequential array scans.
-/
namespace CurrentAFT.BinaryPairedTensor
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def dropFirst {Value : Type*} {count : ℕ} (fallback : Value) (word : Vector Value (count+1)) : CountedValue (Vector Value count) :=
  let computed := Vector.ofFn (fun index : Fin count => readVector fallback word index.succ)
  ⟨computed.map (fun result => result.value), (∑ index, (computed.get index).work)+2*count+2⟩



def dropWork (count : ℕ) : ℕ := count*(3*(count+1)+5)+2



def lift {colors : ℕ} (primary center : Vector RationalBits colors)
    (anchor : Vector (Vector RationalBits colors) colors) (rate : RationalBits)
    (profile : Fin colors → ℚ) (group : Fin colors × Fin colors) : ℚ :=
  profile group.1-rate.decode*(∑ color, (primary.get color).decode*profile color*((anchor.get color).get group.2).decode)/
    (center.get group.2).decode

def value {colors : ℕ} (primary center : Vector RationalBits colors)
    (anchor : Vector (Vector RationalBits colors) colors) (rate : RationalBits) :
    (count : ℕ) → ((Fin count → Fin colors) → ℚ) → (Fin count → Fin colors × Fin colors) → ℚ
  | 0, kernel, _ => kernel Fin.elim0
  | count+1, kernel, groups => lift primary center anchor rate
      (fun color => value primary center anchor rate count (fun rest => kernel (Fin.cons color rest))
        (fun index => groups index.succ)) (groups 0)

def current {colors : ℕ} (primary center : Vector RationalBits colors)
    (anchor : Vector (Vector RationalBits colors) colors) (rate : RationalBits) (fallback : Fin colors × Fin colors) :
    (count : ℕ) → (Vector (Fin colors) count → RationalResult) → Vector (Fin colors × Fin colors) count → RationalResult
  | 0, kernel, _ => kernel (Vector.ofFn Fin.elim0)
  | count+1, kernel, groups =>
      let head := readVector fallback groups 0
      let tail := dropFirst fallback groups
      let profile := buildArray colors (fun color => current primary center anchor rate fallback count
        (fun rest =>
          let word := BinaryTupleSum.prepend color rest
          let result := kernel word.value
          ⟨result.data, word.work+result.work+1⟩) tail.value)
      let result := BinaryPairedScore.current primary center profile.data anchor rate head.value.1 head.value.2
      ⟨result.data, head.work+tail.work+profile.work+result.work+4⟩



def height (colors referenceHeight : ℕ) : (count leafHeight : ℕ) → ℕ
  | 0, leafHeight => leafHeight
  | count+1, leafHeight => BinaryPairedScore.height colors (referenceHeight+height colors referenceHeight count leafHeight)

def work (colors referenceHeight : ℕ) : (count leafHeight leafWork : ℕ) → ℕ
  | 0, _, leafWork => leafWork
  | count+1, leafHeight, leafWork =>
      (3*(count+1)+3)+dropWork count+
      (colors*(work colors referenceHeight count leafHeight (BinaryTupleSum.prependWork count+leafWork+1)+2)+2)+
      BinaryPairedScore.work colors (referenceHeight+height colors referenceHeight count leafHeight)+4



noncomputable def heightPolynomial (colors referenceHeight : Polynomial ℕ) : (count : ℕ) → Polynomial ℕ → Polynomial ℕ
  | 0, leafHeight => leafHeight
  | count+1, leafHeight => BinaryCurrentPaired.heightPolynomial colors
      (referenceHeight+heightPolynomial colors referenceHeight count leafHeight)

noncomputable def workPolynomial (colors referenceHeight : Polynomial ℕ) : (count : ℕ) → Polynomial ℕ → Polynomial ℕ → Polynomial ℕ
  | 0, _, leafWork => leafWork
  | count+1, leafHeight, leafWork =>
      Polynomial.C (3*(count+1)+3)+Polynomial.C (dropWork count)+
      (colors*(workPolynomial colors referenceHeight count leafHeight
        (Polynomial.C (BinaryTupleSum.prependWork count)+leafWork+1)+2)+2)+
      BinaryCurrentPaired.evaluationWorkPolynomial colors
        (referenceHeight+heightPolynomial colors referenceHeight count leafHeight)+4





end CurrentAFT.BinaryPairedTensor

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPairedTensor.heightPolynomial
  let _ ← Lean.Meta.getUnfoldEqnFor? `CurrentAFT.BinaryPairedTensor.heightPolynomial true
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPairedTensor.workPolynomial
  let _ ← Lean.Meta.getUnfoldEqnFor? `CurrentAFT.BinaryPairedTensor.workPolynomial true
  pure ()

end

section



/-! # Fixed rectangular coordinates for the current joint weight tables

Primary digits precede body digits.  These coordinates retain every joint
entry; positivity and runtime are supplied by separate program modules.
-/
namespace CurrentAFT.WeightCoordinates
set_option maxHeartbeats 600000

/-- The first coordinate is the most significant digit. -/
def tupleCode (base : ℕ) : (count : ℕ) → (Fin count → ℕ) → ℕ
  | 0, _ => 0
  | count+1, word => base*tupleCode base count (fun index => word index.castSucc)+word (Fin.last count)

def jointCode (base r s : ℕ) (primary : Fin r → ℕ) (body : Fin s → ℕ) : ℕ :=
  base^s*tupleCode base r primary+tupleCode base s body

def arityCode (order r s : ℕ) : ℕ := r*(order+1)+s

theorem tupleCode_lt (base count : ℕ) (_hb : 0 < base) (word : Fin count → ℕ)
    (hw : ∀ index, word index < base) : tupleCode base count word < base^count := by
  induction count with
  | zero => simp only [tupleCode, pow_zero]; omega
  | succ count ih =>
    have ht := ih (fun index => word index.castSucc) (fun index => hw index.castSucc)
    have hl := hw (Fin.last count)
    simp only [tupleCode, pow_succ]
    nlinarith

theorem jointCode_lt (base r s : ℕ) (hb : 0 < base) (primary : Fin r → ℕ) (body : Fin s → ℕ)
    (hp : ∀ index, primary index < base) (hq : ∀ index, body index < base) :
    jointCode base r s primary body < base^(r+s) := by
  have hp' := tupleCode_lt base r hb primary hp
  have hq' := tupleCode_lt base s hb body hq
  have hpower : 0 < base^s := pow_pos hb s
  unfold jointCode
  rw [pow_add]
  nlinarith

theorem jointCode_lt_capacity (base order r s : ℕ) (hb : 0 < base) (hdegree : r+s ≤ order)
    (primary : Fin r → ℕ) (body : Fin s → ℕ)
    (hp : ∀ index, primary index < base) (hq : ∀ index, body index < base) :
    jointCode base r s primary body < base^order :=
  (jointCode_lt base r s hb primary body hp hq).trans_le
    (Nat.pow_le_pow_right hb hdegree)

theorem arityCode_lt (order r s : ℕ) (hr : r ≤ order) (hs : s ≤ order) :
    arityCode order r s < (order+1)^2 := by
  unfold arityCode
  nlinarith

def wordIndex (base order r s : ℕ) (hb : 0 < base) (hdegree : r+s ≤ order)
    (primary : Fin r → Fin base) (body : Fin s → Fin base) : Fin (base^order) :=
  ⟨jointCode base r s (fun index => (primary index).val) (fun index => (body index).val),
    jointCode_lt_capacity base order r s hb hdegree _ _ (fun index => (primary index).isLt) (fun index => (body index).isLt)⟩

def arityIndex (order : ℕ) (r s : Fin (order+1)) : Fin ((order+1)^2) :=
  ⟨arityCode order r.val s.val, arityCode_lt order r.val s.val (Nat.le_of_lt_succ r.isLt) (Nat.le_of_lt_succ s.isLt)⟩

theorem arityCode_injective (order : ℕ) : Function.Injective
    (fun pair : Fin (order+1) × Fin (order+1) => arityIndex order pair.1 pair.2) := by
  rintro ⟨r, s⟩ ⟨r', s'⟩ he
  have h := congrArg Fin.val he
  change r.val*(order+1)+s.val = r'.val*(order+1)+s'.val at h
  have hmod : s.val = s'.val := by
    have hh := congrArg (fun number => number % (order+1)) h
    simpa only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt s'.isLt] using hh
  have hquot : r.val = r'.val := by nlinarith
  exact Prod.ext (Fin.ext hquot) (Fin.ext hmod)

end CurrentAFT.WeightCoordinates

end

section
























/-! # Executed indices and sequential joint-table reads for the weight -/
namespace CurrentAFT.BinaryWeightCoordinates
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] multiplyCounter addCounter powerCounter

 opaque checkedPower (base exponent : ℕ) :
    {result : UnaryCounterResult // result.count = base^exponent ∧ result.work ≤ powerCounterWork base exponent} :=
  ⟨powerCounter base exponent, powerCounter_value base exponent, powerCounter_work base exponent⟩

def leading {count : ℕ} (word : Vector ℕ (count+1)) : CountedValue (Vector ℕ count) :=
  let computed := Vector.ofFn (fun index : Fin count => readVector 0 word index.castSucc)
  ⟨computed.map (fun result => result.value), (∑ index, (computed.get index).work)+2*count+2⟩

theorem leading_get {count : ℕ} (word : Vector ℕ (count+1)) (index : Fin count) :
    (leading word).value.get index = word.get index.castSucc := by simp [leading, readVector_value]

def leadingWork (count : ℕ) : ℕ := count*(3*(count+1)+5)+2



def encode (base : ℕ) : (count : ℕ) → Vector ℕ count → UnaryCounterResult
  | 0, _ => ⟨0, 1⟩
  | count+1, word =>
      let digits := leading word
      let previous := encode base count digits.value
      let last := readVector 0 word (Fin.last count)
      let scaled := multiplyCounter base previous.count
      let result := addCounter scaled.count last.value
      ⟨result.count, digits.work+previous.work+last.work+scaled.work+result.work+5⟩

theorem encode_value (base count : ℕ) (word : Vector ℕ count) :
    (encode base count word).count = WeightCoordinates.tupleCode base count word.get := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [encode, addCounter_value, multiplyCounter_value, readVector_value, ih, WeightCoordinates.tupleCode]
    congr 2
    apply congrArg (WeightCoordinates.tupleCode base count)
    funext index
    exact leading_get word index

def encodeWork (base capacity : ℕ) : ℕ → ℕ
  | 0 => 1
  | count+1 => leadingWork count+encodeWork base capacity count+(3*(count+1)+3)+
      (base*(2*capacity+3)+1)+(2*(base*capacity)+1)+5



def joint (base r s : ℕ) (primary : Vector ℕ r) (body : Vector ℕ s) : UnaryCounterResult :=
  let first := encode base r primary
  let second := encode base s body
  let power := (checkedPower base s).val
  let scaled := multiplyCounter power.count first.count
  let result := addCounter scaled.count second.count
  ⟨result.count, first.work+second.work+power.work+scaled.work+result.work+5⟩

theorem joint_value (base r s : ℕ) (primary : Vector ℕ r) (body : Vector ℕ s) :
    (joint base r s primary body).count = WeightCoordinates.jointCode base r s primary.get body.get := by
  simp only [joint, addCounter_value, multiplyCounter_value, encode_value, (checkedPower base s).property.1,
    WeightCoordinates.jointCode]

def jointWork (base order r s : ℕ) : ℕ :=
  let capacity := base^order
  encodeWork base capacity r+encodeWork base capacity s+powerCounterWork base s+
    (capacity*(2*capacity+3)+1)+(2*(capacity*capacity)+1)+5



def arity (order r s : ℕ) : UnaryCounterResult :=
  let size := addCounter order 1
  let row := multiplyCounter r size.count
  let result := addCounter row.count s
  ⟨result.count, size.work+row.work+result.work+3⟩

theorem arity_value (order r s : ℕ) : (arity order r s).count = WeightCoordinates.arityCode order r s := by
  simp only [arity, addCounter_value, multiplyCounter_value, WeightCoordinates.arityCode]

def arityWork (order : ℕ) : ℕ :=
  (2*order+1)+(order*(2*(order+1)+3)+1)+(2*(order*(order+1))+1)+3



abbrev Table (base order : ℕ) := Vector (Vector RationalBits (base^order)) ((order+1)^2)

def read (base order r s : ℕ) (hb : 0 < base) (hdegree : r+s ≤ order)
    (table : Table base order) (primary : Vector (Fin base) r) (body : Vector (Fin base) s) : RationalResult :=
  let first := primary.map Fin.val
  let second := body.map Fin.val
  let wordCode := joint base r s first second
  let blockCode := arity order r s
  let row := readVector (Vector.replicate (base^order) zero) table
    ⟨blockCode.count, by
      rw [arity_value]
      exact WeightCoordinates.arityCode_lt order r s (by omega) (by omega)⟩
  let value := readVector zero row.value
    ⟨wordCode.count, by
      rw [joint_value]
      exact WeightCoordinates.jointCode_lt_capacity base order r s hb hdegree _ _
        (fun index => by
          change (primary.map Fin.val).get index < base
          simpa only [Vector.get_map] using (primary.get index).isLt)
        (fun index => by
          change (body.map Fin.val).get index < base
          simpa only [Vector.get_map] using (body.get index).isLt)⟩
  ⟨value.value, r+s+2+wordCode.work+blockCode.work+row.work+value.work+base^order+4⟩





def readWork (base order r s : ℕ) : ℕ := r+s+2+jointWork base order r s+arityWork order+
  (3*((order+1)^2)+3)+(3*(base^order)+3)+base^order+4





noncomputable def encodeWorkPolynomial (base capacity : Polynomial ℕ) : ℕ → Polynomial ℕ
  | 0 => 1
  | count+1 => Polynomial.C (leadingWork count)+encodeWorkPolynomial base capacity count+Polynomial.C (3*(count+1)+3)+
      (base*(2*capacity+3)+1)+(2*(base*capacity)+1)+5

noncomputable def jointWorkPolynomial (base : Polynomial ℕ) (order r s : ℕ) : Polynomial ℕ :=
  let capacity := base^order
  encodeWorkPolynomial base capacity r+encodeWorkPolynomial base capacity s+
    Polynomial.C (s+1)*(6*(base+1)^(s+2)+4)+
    (capacity*(2*capacity+3)+1)+(2*(capacity*capacity)+1)+5

noncomputable def readWorkPolynomial (base : Polynomial ℕ) (order r s : ℕ) : Polynomial ℕ :=
  Polynomial.C (r+s+2)+jointWorkPolynomial base order r s+Polynomial.C (arityWork order)+
    Polynomial.C (3*((order+1)^2)+3)+(3*(base^order)+3)+base^order+4







end CurrentAFT.BinaryWeightCoordinates

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightCoordinates.encodeWorkPolynomial
  let _ ← Lean.Meta.getUnfoldEqnFor? `CurrentAFT.BinaryWeightCoordinates.encodeWorkPolynomial true
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightCoordinates.jointWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightCoordinates.readWorkPolynomial
  pure ()

end

section





















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.TensorSupApproximation
end CurrentAFT.TensorSupApproximation




/-! # The actual and computed paired operators on arbitrary real scores -/
namespace CurrentAFT.PairedScoreApproximation
open AFT ActualControls ProposalPrimary ControlCoordinates RationalProposalProgram
  RationalPairedLiftProgram DiffuseProfiles
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def pairedLinear (primary : FiniteDist Primary) (body : FiniteDist Body)
    (anchor : Primary → FiniteDist Body) (rate : ℝ) :
    (Primary → ℝ) →ₗ[ℝ] ((Primary × Body) → ℝ) where
  toFun := ControlCoordinates.pairedLift primary body anchor rate
  map_add' first second := by
    funext point
    simp only [ControlCoordinates.pairedLift, ControlCoordinates.anchorProfile, Pi.add_apply, mul_add,
      add_mul, Finset.sum_add_distrib, add_div]
    ring
  map_smul' scalar score := by
    funext point
    simp only [ControlCoordinates.pairedLift, ControlCoordinates.anchorProfile, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have he : (∑ color, primary.weight color * (scalar * score color) * (anchor color).weight point.2) =
        scalar * ∑ color, primary.weight color * score color * (anchor color).weight point.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro color _
      ring
    rw [he]
    ring



def actual (security : ℕ) := pairedLinear (primaryLaw security) (bodyReference security)
  (anchorReference security) (activation security)
def approximate (security bits : ℕ) := pairedLinear (approximatePrimaryLaw security bits)
  (approximateBodyReference security bits) (approximateAnchorReference security bits)
    (LocalPairProgram.activationApprox security bits)









end
end CurrentAFT.PairedScoreApproximation

end

section






















/-! # Uniform numerical error for the actual public weight

The entire joint coefficient table is evaluated with the computed paired
reference. Distinct choices are averaged before summing all arities. No
factorization of a joint kernel or independence of endpoints is used.
-/
namespace CurrentAFT.NumericalWeightEvaluation
open AFT ActualControls ProposalPrimary ControlCoordinates GradedControlAlgebra
  CalibrationPointCoordinates PairedScoreApproximation TensorSupApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance weightFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def factor (security : ℕ) : ℝ := 1 + 2 * Parameters.modulus security
def localError (security bits : ℕ) : ℝ := RationalPairedLiftProgram.errorConstant security / (2 : ℝ)^bits












def evaluate (security bits order primaryPool bodyPool : ℕ)
    (table : PointTable (ActualControls.Palette security) (SafePalette security) order)
    (groups : Fin primaryPool → SafeControlGroups.SafeGroup security)
    (centers : Fin bodyPool → SafePalette security) : ℝ :=
  table ⟨zeroArity order, Fin.elim0, Fin.elim0⟩ +
    ∑ arity : PositiveArity order,
      twoPoolUStatistic primaryPool bodyPool
        (fun selected selectedCenters => TensorChannel.apply arity.val.1.val
          (fun _ => approximate security bits)
          (fun colors => table ⟨positiveArity order arity, colors, selectedCenters⟩) selected)
        groups centers



end
end CurrentAFT.NumericalWeightEvaluation

end

end


