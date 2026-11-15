-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_11_Part_4
-- name    : InfoLossLAR_NativeBundle_11_Part_4
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T19:32:08.765036+00:00
-- url     : https://prove2.me/theorems/172c733e-c837-4cc2-baac-c921a022bb3b
-- title:
--   Full-response metadata serialization and rectangle programs
-- statement:
--   This package defines root-metadata serialization, finite binary sums and bounded root-tag data, the full-response program and stored resource expressions, natural-coordinate and rectangle iteration, materialization and decoding, rectangle entries, point-family products, and the coefficient identities required to interpret complete response data.
--
--   These are stored finite data and their constructor and interpretation APIs. They keep the actual binary or rational computation distinct from its ideal real semantics; later theorems establish approximation and platform running-time guarantees. The smaller compilation unit preserves entire original source modules and introduces no assumed transport or lattice-reduction result.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0. Original source units Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootMetadataSerializer, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryListSum, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CountedBoundedRootTags, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryFullResponseProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootMetadataResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryFullResponseResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryNaturalCoordinates, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRectangleIteration, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRectangleMaterialization, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRectangleResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRectangleAddress, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryCounterTupleDecode, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRectangleDecode, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRectangleDecodeResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentBinaryRectangleDecode, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRectangleEntry, Definitions.Def_InfoLossLAR_Native_CurrentAFT_PointFamilyProducts, Definitions.Def_InfoLossLAR_Native_CurrentAFT_EmptyRootCoefficientIdentity, Definitions.Def_InfoLossLAR_Native_CurrentAFT_FullResponseWeightedIdentity, Definitions.Def_InfoLossLAR_Native_CurrentAFT_FullResponseDefectIdentity. Exact syntax-oracle source spans, body hashes and closed scope wrappers recorded in compact_heavy_split/manifest.json. Source SHA256 8d73ec9f25c0e7b45464ab8822a5281eec8ca447b42653cf307e3c10c6595057. Compiler-only optimization: one local scope marks Polynomial addition and multiplication instances irreducible while generating native equation lemmas. Every original definition and proof source body is unchanged; all11528 public types and recursive standard-axiom audits pass. New sourceSHA256 2f9b5b3c5cc2534d83b2f9c1ebfd5749638dc4c6a29dc5a7ab9266fb8b1c4fdd.

import Definitions.Def_InfoLossLAR_NativeBundle_11_Part_3

section
attribute [local irreducible] Polynomial.instAdd Polynomial.instMul

section

































/-! Bounded serialization of selected controls and sorted root tags.
The executed filter visits only the supplied tags; candidate root lookup
visits two slots per selected or retained group. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT BinaryArithmetic RationalRejectionProgram RationalRootGroupProgram
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

abbrev population (legs ordinary queues : ℕ) := legs+(legs+ordinary)+queues

def primaryMissing {legs ordinary queues r : ℕ} (primary : Vector (Fin legs) r)
    (block : Fin (population legs ordinary queues)) : CountedValue Bool :=
  BinaryProposalGuard.allFin r (fun index =>
    let found := readVector (⟨0,by have := (primary.get index).isLt;omega⟩ : Fin legs) primary index
    let companion := addCounter legs found.value.val
    let legEqual := equalCounter block.val found.value.val
    let companionEqual := equalCounter block.val companion.count
    ⟨!(legEqual.value || companionEqual.value),found.work+companion.work+legEqual.work+companionEqual.work+4⟩)

def ordinaryMissing {legs ordinary queues s : ℕ} (body : Vector (Fin ordinary) s)
    (block : Fin (population legs ordinary queues)) : CountedValue Bool :=
  BinaryProposalGuard.allFin s (fun index =>
    let found := readVector (⟨0,by have := (body.get index).isLt;omega⟩ : Fin ordinary) body index
    let twice := addCounter legs legs
    let position := addCounter twice.count found.value.val
    let same := equalCounter block.val position.count
    ⟨!same.value,found.work+twice.work+position.work+same.work+4⟩)

def isKept {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (block : Fin (population legs ordinary queues)) : CountedValue Bool :=
  let first := primaryMissing primary block
  let second := ordinaryMissing body block
  ⟨first.value && second.value,first.work+second.work+2⟩

theorem primaryMissing_value {legs ordinary queues r : ℕ} (primary : Vector (Fin legs) r)
    (block : Fin (population legs ordinary queues)) :
    (primaryMissing primary block).value=true ↔
      ∀ index,block.val≠(primary.get index).val ∧ block.val≠legs+(primary.get index).val := by
  simp only [primaryMissing,BinaryProposalGuard.allFin_value,readVector_value,addCounter_value,
    Bool.not_eq_true',Bool.eq_false_iff,ne_eq,Bool.or_eq_true,equalCounter_value,not_or]

theorem ordinaryMissing_value {legs ordinary queues s : ℕ} (body : Vector (Fin ordinary) s)
    (block : Fin (population legs ordinary queues)) :
    (ordinaryMissing body block).value=true ↔ ∀ index,block.val≠legs+legs+(body.get index).val := by
  simp only [ordinaryMissing,BinaryProposalGuard.allFin_value,readVector_value,addCounter_value,
    Bool.not_eq_true',Bool.eq_false_iff,ne_eq,equalCounter_value]

theorem isKept_value {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (block : Fin (population legs ordinary queues)) :
    (isKept primary body block).value=true ↔
      (∀ index,block.val≠(primary.get index).val ∧ block.val≠legs+(primary.get index).val) ∧
        ∀ index,block.val≠legs+legs+(body.get index).val := by
  simp only [isKept,Bool.and_eq_true,primaryMissing_value,ordinaryMissing_value]

def filter {α : Type*} (test : α → CountedValue Bool) : List α → CountedValue (List α)
  | [] => ⟨[],1⟩
  | head::tail =>
    let checked := test head
    let rest := filter test tail
    ⟨if checked.value then head::rest.value else rest.value,checked.work+rest.work+3⟩

theorem filter_value {α : Type*} (test : α → CountedValue Bool) (items : List α) :
    (filter test items).value=items.filter (fun item => (test item).value) := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [filter,List.filter_cons,ih]



def kept {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) : CountedValue (List (Fin (population legs ordinary queues))) :=
  let computed := filter (isKept primary body) tagged.toList
  ⟨computed.value,computed.work+tags+1⟩

theorem kept_value {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) :
    (kept primary body tagged).value=tagged.toList.filter (fun block => (isKept primary body block).value) := by
  exact filter_value _ _



def groupCount {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) := (r+s)+(kept primary body tagged).value.length

theorem groupCount_pos {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) (index : Fin tags) : 0<groupCount primary body tagged := by
  by_cases hrs : r+s=0
  · have hr : r=0 := by omega
    have hs : s=0 := by omega
    have hall : ∀ block : Fin (population legs ordinary queues),(isKept primary body block).value=true := by
      intro block
      apply (isKept_value primary body block).mpr
      constructor
      · intro i;have := i.isLt;omega
      · intro i;have := i.isLt;omega
    have hk : (kept primary body tagged).value=tagged.toList := by
      rw [kept_value]
      exact List.filter_eq_self.mpr (fun block _ => hall block)
    simp only [groupCount,hk,Vector.length_toList]
    have := index.isLt
    omega
  · unfold groupCount
    omega

def candidate {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (slot : Fin 2) : CountedValue (Option ℕ) :=
  let first := lessCounter group.val r
  let second := lessCounter group.val (r+s)
  let zero := equalCounter slot.val 0
  if hp : first.value=true then
    let index : Fin r := ⟨group.val,(lessCounter_value _ _).mp hp⟩
    let found := readVector (⟨0,by have := (primary.get index).isLt;omega⟩ : Fin legs) primary index
    let companion := addCounter legs found.value.val
    ⟨some (if zero.value then companion.count else found.value.val),first.work+second.work+zero.work+found.work+companion.work+5⟩
  else if hb : second.value=true then
    let position := differenceCounter group.val r
    let index : Fin s := ⟨position.count,by
      rw [differenceCounter_value]
      have ht := (lessCounter_value _ _).mp hb
      have hf : ¬group.val<r := fun h => hp ((lessCounter_value _ _).mpr h)
      omega⟩
    let found := readVector (⟨0,by have := (body.get index).isLt;omega⟩ : Fin ordinary) body index
    let twice := addCounter legs legs
    let value := addCounter twice.count found.value.val
    ⟨if zero.value then some value.count else none,
      first.work+second.work+zero.work+position.work+found.work+twice.work+value.work+7⟩
  else
    let position := differenceCounter group.val (r+s)
    let found := readList retained position.count
    ⟨if zero.value then found.data.map Fin.val else none,first.work+second.work+zero.work+position.work+found.work+5⟩

def role {legs ordinary queues r s : ℕ} (_primary : Vector (Fin legs) r) (_body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length)) : CountedValue LocalRole :=
  let first := lessCounter group.val r
  let second := lessCounter group.val (r+s)
  if first.value then ⟨.primary,first.work+second.work+2⟩ else
  if second.value then ⟨.ordinary,first.work+second.work+3⟩ else
    let position := differenceCounter group.val (r+s)
    let found := readList retained position.count
    let value := (found.data.map Fin.val).getD 0
    let leg := lessCounter value legs
    let centers := addCounter legs ordinary
    let boundary := addCounter legs centers.count
    let center := lessCounter value boundary.count
    ⟨if leg.value then .leg else if center.value then .center else .queue,
      first.work+second.work+position.work+found.work+leg.work+centers.work+boundary.work+center.work+9⟩

def find {α : Type*} (test : α → CountedValue Bool) : List α → CountedValue (Option α)
  | [] => ⟨none,1⟩
  | head::tail =>
    let checked := test head
    if checked.value then ⟨some head,checked.work+2⟩ else
      let rest := find test tail
      ⟨rest.value,checked.work+rest.work+3⟩





def splitIndex {groups : ℕ} (index : Fin (groups*2)) : CountedValue (Fin groups × Fin 2) :=
  let division := divideCounter index.val 2
  ⟨(⟨division.quotient,by
      rw [(divideCounter_value index.val 2 (by omega)).1]
      exact Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using index.isLt)⟩,
    ⟨division.remainder,by rw [(divideCounter_value index.val 2 (by omega)).2];omega⟩),division.work+2⟩



def matchesBlock {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (block : Fin (population legs ordinary queues))
    (index : Fin (((r+s)+retained.length)*2)) : CountedValue Bool :=
  let pair := splitIndex index
  let value := candidate primary body retained pair.value.1 pair.value.2
  match value.value with
  | none => ⟨false,pair.work+value.work+2⟩
  | some number =>
    let checked := equalCounter number block.val
    ⟨checked.value,pair.work+value.work+checked.work+2⟩

def position {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (block : Fin (population legs ordinary queues)) :
    CountedValue (Option (Fin (((r+s)+retained.length)*2))) :=
  let count := (r+s)+retained.length
  let result := find (matchesBlock primary body retained block) (List.ofFn (id : Fin (count*2) → Fin (count*2)))
  ⟨result.value,result.work+count*2+2⟩

def tagSlot {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) (index : Fin tags) :
    CountedValue (Fin (groupCount primary body tagged) × Fin 2) :=
  let block := readVector (⟨0,by have := (tagged.get index).isLt;omega⟩ : Fin (population legs ordinary queues)) tagged index
  let found := position primary body (kept primary body tagged).value block.value
  let zero : Fin ((groupCount primary body tagged)*2) := ⟨0,by have := groupCount_pos primary body tagged index;omega⟩
  let pair := splitIndex (found.value.getD zero)
  ⟨pair.value,(kept primary body tagged).work+block.work+found.work+pair.work+3⟩

structure Result (r s tags : ℕ) where
  kept : ℕ
  data : BinaryPackedRootMetadata.Data r s kept tags
  work : ℕ

def current {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) : Result r s tags :=
  let retained := kept primary body tagged
  let roles := storeData ((r+s)+retained.value.length) (role primary body retained.value)
  let positions := storeData tags (tagSlot primary body tagged)
  ⟨retained.value.length,⟨roles.value,positions.value⟩,retained.work+roles.work+positions.work+4⟩

























end CurrentAFT.BinaryRootMetadataSerializer

end

section


















/-! # Executed rational sums over stored finite metadata lists -/
namespace CurrentAFT.BinaryListSum
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
variable {Index : Type*}

def current (kernel : Index → RationalResult) : List Index → RationalResult
  | [] => ⟨zero,1⟩
  | index::tail =>
    let remaining := current kernel tail
    let next := kernel index
    let result := RationalBits.add next.data remaining.data
    ⟨result.data,remaining.work+next.work+result.work+2⟩



def height (count bits : ℕ) := count*(bits+1)
def work (count bits budget : ℕ) := count*(budget+primitiveWorkBound ((count+1)*(bits+1))+2)+2







noncomputable def heightPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ := count*(bits+1)
noncomputable def workPolynomial (count bits budget : Polynomial ℕ) : Polynomial ℕ :=
  count*(budget+primitiveWorkPolynomial ((count+1)*(bits+1))+2)+2




end CurrentAFT.BinaryListSum

end

section




























/-! # Stored, strictly ordered bounded root tags, with no powerset enumeration -/
namespace CurrentAFT.CountedBoundedRootTags
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure Tag (population order : ℕ) where
  values : List (Fin population)
  increasing : values.Pairwise (·<·)
  bounded : values.length ≤ order

def Tag.vector {population order : ℕ} (tag : Tag population order) : Vector (Fin population) tag.values.length := Vector.ofFn tag.values.get
def Tag.set {population order : ℕ} (tag : Tag population order) : Finset (Fin population) := tag.values.toFinset





def Tag.read {population order : ℕ} (tag : Tag population order) (index : Fin tag.values.length) : CountedValue (Fin population) :=
  let result := readList tag.values index.val
  ⟨result.data.get (by rw [readList_value,List.getElem?_eq_getElem index.isLt]; rfl),result.work+1⟩



def Tag.store {population order : ℕ} (tag : Tag population order) : CountedValue (Vector (Fin population) tag.values.length) :=
  storeData tag.values.length tag.read





def source (population : ℕ) : CountedValue (List (Fin population)) :=
  let values := storeData population (fun index => (⟨index,1⟩ : CountedValue (Fin population)))
  ⟨values.value.toList,values.work+population+1⟩

theorem source_value (population : ℕ) : (source population).value=List.finRange population := by
  simp only [source,storeData,Vector.map_ofFn,Vector.toList_ofFn]
  rfl



def entry (population order : ℕ) (size : Fin (order+1)) : CountedValue (List (Tag population order)) :=
  let base := source population
  let computed := countedSubsequences size.val base.value
  let values := computed.value.attach.map (fun (word : {word : List (Fin population) // word∈computed.value}) =>
    let member : word.val∈(List.finRange population).sublistsLen size.val := by
      have hw : word.val∈(countedSubsequences size.val (source population).value).value := word.property
      simpa only [countedSubsequences_value,source_value] using hw
    let properties := List.mem_sublistsLen.mp member
    (⟨word.val,(List.sortedLT_finRange population).pairwise.sublist properties.1,by rw [properties.2]; have := size.isLt; omega⟩ : Tag population order))
  ⟨values,base.work+computed.work+computed.value.length*(size.val+3)^2+2⟩



def current (population order : ℕ) : CountedValue (List (Tag population order)) :=
  let entries := (List.range (order+1)).attach.map (fun size => entry population order ⟨size.val,List.mem_range.mp size.property⟩)
  let values := entries.flatMap (fun result => result.value)
  ⟨values,(entries.map (fun result => result.work)).sum+3*values.length+4*population+3*(order+1)+5⟩







def entryWorkBound (population order : ℕ) :=
  (10*(order+1)+(order+3)^2+9)*(population+1)^(order+2)
def workBound (population order : ℕ) :=
  (order+1)*entryWorkBound population order+3*((order+1)*(population+1)^order)+4*population+3*(order+1)+5





def guarded {population order : ℕ} (kernel : Tag population order → RationalResult) (tag : Tag population order) : RationalResult :=
  let test := lessCounter 1 tag.values.length
  let result := kernel tag
  ⟨if test.value then result.data else zero,test.work+result.work+2⟩



def sum (population order : ℕ) (kernel : Tag population order → RationalResult) : RationalResult :=
  let tags := current population order
  let result := BinaryListSum.current (guarded kernel) tags.value
  ⟨result.data,tags.work+result.work+2⟩

def lengthBound (population order : ℕ) := (order+1)*(population+1)^order
def sumWork (population order bits budget : ℕ) :=
  workBound population order+BinaryListSum.work (lengthBound population order) bits (budget+3*order+7)+2








noncomputable def countPolynomial (order : ℕ) (population : Polynomial ℕ) : Polynomial ℕ := Polynomial.C (order+1)*(population+1)^order
noncomputable def generationWorkPolynomial (order : ℕ) (population : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (order+1)*(Polynomial.C (10*(order+1)+(order+3)^2+9)*(population+1)^(order+2))+
    3*countPolynomial order population+4*population+Polynomial.C (3*(order+1)+5)
noncomputable def heightPolynomial (order : ℕ) (population bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryListSum.heightPolynomial (countPolynomial order population) bits
noncomputable def workPolynomial (order : ℕ) (population bits budget : Polynomial ℕ) : Polynomial ℕ :=
  generationWorkPolynomial order population+
    BinaryListSum.workPolynomial (countPolynomial order population) bits (budget+Polynomial.C (3*order+7))+2






noncomputable section
open scoped Classical






end
end CurrentAFT.CountedBoundedRootTags

end

section







































/-! # The actual full-response algorithm from finite stored metadata

Each root set is generated once as an increasing bounded sublist. Every
control selection is averaged with its actual without-replacement mass.
The common queue is averaged only after multiplying by its background.
-/
namespace CurrentAFT.BinaryFullResponseProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct BinaryFullResponseData
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

abbrev Data (order : ℕ) := BinaryFullResponseData.Data order
abbrev Color (security : ℕ) := BinaryWeightedPointKernel.Color security
abbrev PrimaryPool (security : ℕ) := BinaryControlChoiceAverage.PrimaryPool security
abbrev BodyPool (security : ℕ) := BinaryControlChoiceAverage.BodyPool security
abbrev Tag (security order : ℕ) := CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order

def tagged (security bits order : ℕ) (data : Data order) (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (primary : Vector (PrimaryPool security) source.val.1.val) (body : Vector (BodyPool security) source.val.2.val)
    (tag : Tag security order) : CoefficientProgram order := fun output inputs centers =>
  let counts := BinaryFullResponseCounts.current security
  let stored := tag.store
  let native : Vector (Fin (BinaryRootMetadataSerializer.population counts.leg counts.ordinary counts.queue)) tag.values.length :=
    Eq.mpr (congrArg (fun count => Vector (Fin count) tag.values.length) (BinaryFullResponseCounts.body_decomposition security)) stored.value
  let metadata := BinaryRootMetadataSerializer.current primary body native
  let result := BinaryPackedRootUniform.current security bits order data.groups data.points queue source metadata.data sourcePrimary sourceBody output inputs centers
  ⟨result.value,counts.work+stored.work+metadata.work+result.work+4⟩

def emptyTag (security order : ℕ) : Tag security order := ⟨[],by simp,Nat.zero_le _⟩

def tagSum (security bits order : ℕ) (data : Data order) (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (primary : Vector (PrimaryPool security) source.val.1.val) (body : Vector (BodyPool security) source.val.2.val) :
    CoefficientProgram order := fun output inputs centers =>
  let counts := BinaryFullResponseCounts.current security
  let result := CountedBoundedRootTags.sum counts.body order (fun tag =>
    let value := tagged security bits order data queue source sourcePrimary sourceBody primary body tag output inputs centers
    ⟨value.value,value.work+1⟩)
  ⟨result.data,counts.work+result.work+2⟩

def selected (security bits order : ℕ) (data : Data order) (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (primary : Vector (PrimaryPool security) source.val.1.val) (body : Vector (BodyPool security) source.val.2.val) : CoefficientProgram order :=
  BinaryCoefficientOperations.add order
    (tagged security bits order data queue source sourcePrimary sourceBody primary body (emptyTag security order))
    (tagSum security bits order data queue source sourcePrimary sourceBody primary body)

def choiceAverage (security bits order : ℕ) (data : Data order) (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val) :
    CoefficientProgram order := fun output inputs centers =>
  let result := BinaryControlChoiceAverage.current security order source (fun primary body =>
    let value := selected security bits order data queue source sourcePrimary sourceBody primary body output inputs centers
    ⟨value.value,value.work+1⟩)
  ⟨result.data,result.work+1⟩

def fixedQueue (security bits order : ℕ) (data : Data order) (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order data.groups.programs
    (BinaryBackgroundPopulation.current security bits order data.groups.programs queue)
    (choiceAverage security bits order data queue source sourcePrimary sourceBody)

def response (security bits order : ℕ) (data : Data order) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val) : CoefficientProgram order :=
  BinaryCoefficientScalarAverage.current security bits order (fun queue => fixedQueue security bits order data queue source sourcePrimary sourceBody)

def current (security bits order : ℕ) (data : Data order) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val) :
    CoefficientProgram order := fun output inputs centers =>
  let value := response security bits order data source sourcePrimary sourceBody output inputs centers
  let basis := BinaryFullResponseData.basis security bits order data source sourcePrimary sourceBody output inputs centers
  let result := difference value.value basis.value
  ⟨result.data,value.work+basis.work+result.work+3⟩

end CurrentAFT.BinaryFullResponseProgram

end

section





























/-! Actual operation counts for the bounded metadata serializer. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def missingWork (size count : ℕ) := count*(3*count+20*size+34)+1





def keptWork (size r s tags : ℕ) := tags*(missingWork size r+missingWork size s+5)+tags+2



def localWork (size r s retained : ℕ) := 100*(size+r+s+retained+1)







def splitWork (groups : ℕ) := 500*(2*groups+4)^2+2



def matchWork (size r s retained : ℕ) := splitWork (r+s+retained)+localWork size r s retained+6*size+4



def positionWork (size r s retained : ℕ) :=
  ((r+s+retained)*2)*(matchWork size r s retained+3)+1+(r+s+retained)*2+2



def tagWork (size r s tags : ℕ) := keptWork size r s tags+3*tags+3+positionWork size r s tags+splitWork (r+s+tags)+3



def workBound (size r s tags : ℕ) := keptWork size r s tags+(r+s+tags)*(localWork size r s tags+2)+2+
  tags*(tagWork size r s tags+2)+2+4





noncomputable def workPolynomial (order : ℕ) : Polynomial ℕ :=
  let size := BinaryProposalMetadata.sizePolynomial
  let degree := Polynomial.C order
  let missing := degree*(3*degree+20*size+34)+1
  let retained := degree*(missing+missing+5)+degree+2
  let localCost := 100*(size+degree+degree+degree+1)
  let split := 500*(2*(degree+degree+degree)+4)^2+2
  let matchCost := split+localCost+6*size+4
  let position := ((degree+degree+degree)*2)*(matchCost+3)+1+(degree+degree+degree)*2+2
  let tag := retained+3*degree+3+position+split+3
  retained+(degree+degree+degree)*(localCost+2)+2+degree*(tag+2)+2+4







end CurrentAFT.BinaryRootMetadataSerializer

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootMetadataSerializer.workPolynomial
  pure ()

end

section































/-! # Complete polynomial resources of the actual full-response algorithm -/
namespace CurrentAFT.BinaryFullResponseResources
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct BinaryFullResponseProgram
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryFullResponseCounts.current
  BinaryPackedRootUniform.current BinaryBackgroundPopulation.current

def taggedHeight (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryPackedRootUniform.heightPolynomial order order data.groups data.points precision queueBits
def taggedWork (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryFullResponseCounts.workPolynomial+Polynomial.C (order*(2*order+4)+2)+BinaryRootMetadataSerializer.workPolynomial order+
    BinaryPackedRootUniform.workPolynomial order order data.groups data.points precision queueBits+4
def tagSumHeight (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  CountedBoundedRootTags.heightPolynomial order BinaryProposalMetadata.sizePolynomial (taggedHeight order data precision queueBits)
def tagSumWork (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryFullResponseCounts.workPolynomial+CountedBoundedRootTags.workPolynomial order BinaryProposalMetadata.sizePolynomial
    (taggedHeight order data precision queueBits) (taggedWork order data precision queueBits+1)+2
def selectedHeight (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryCoefficientOperations.addHeight (taggedHeight order data precision queueBits) (tagSumHeight order data precision queueBits)
def selectedWork (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryCoefficientOperations.addWork (taggedHeight order data precision queueBits) (tagSumHeight order data precision queueBits)
    (taggedWork order data precision queueBits) (tagSumWork order data precision queueBits)
def choiceHeight (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryControlChoiceAverage.heightPolynomial order (selectedHeight order data precision queueBits)
def choiceWork (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryControlChoiceAverage.workPolynomial order (selectedHeight order data precision queueBits) (selectedWork order data precision queueBits+1)+1
def fixedQueueHeight (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryFamilyArithmetic.heightPolynomial order data.groups.programs
    (BinaryBackgroundPopulation.heightPolynomial order data.groups.programs precision queueBits+choiceHeight order data precision queueBits)
def fixedQueueWork (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) :=
  BinaryFamilyArithmetic.workPolynomial order data.groups.programs
    (BinaryBackgroundPopulation.heightPolynomial order data.groups.programs precision queueBits+choiceHeight order data precision queueBits)
    (BinaryBackgroundPopulation.workPolynomial order data.groups.programs precision queueBits+choiceWork order data precision queueBits)
def responseHeight (order : ℕ) (data : Data order) (precision : Polynomial ℕ) :=
  BinaryCoefficientScalarAverage.heightPolynomial precision
    (fixedQueueHeight order data precision BinaryCoefficientScalarAverage.scalarBitsPolynomial)
def responseWork (order : ℕ) (data : Data order) (precision : Polynomial ℕ) :=
  BinaryCoefficientScalarAverage.workPolynomial precision
    (fixedQueueHeight order data precision BinaryCoefficientScalarAverage.scalarBitsPolynomial)
    (fixedQueueWork order data precision BinaryCoefficientScalarAverage.scalarBitsPolynomial)
def heightPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) :=
  responseHeight order data precision+BinaryFullResponseData.basisHeightPolynomial order data precision+1
def workPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) :=
  responseWork order data precision+BinaryFullResponseData.basisWorkPolynomial order data precision+
    2*primitiveWorkPolynomial (responseHeight order data precision+BinaryFullResponseData.basisHeightPolynomial order data precision)+5















end
end CurrentAFT.BinaryFullResponseResources

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFullResponseResources.choiceWork
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFullResponseResources.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFullResponseResources.tagSumWork
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFullResponseResources.taggedWork
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFullResponseResources.workPolynomial
  pure ()

end

section




















/-! Stored finite palette words are copied to natural-query buffers by actual reads. -/
namespace CurrentAFT.BinaryNaturalCoordinates
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

def current {base count : ℕ} (hb : 0<base) (word : Vector (Fin base) count) : CountedValue (Vector ℕ count) :=
  storeData count (fun index =>
    let read := readVector ⟨0,hb⟩ word index
    ⟨read.value.val,read.work+1⟩)







end CurrentAFT.BinaryNaturalCoordinates

end

section

























/-! # Materialized calibration output in the joint weight array layout

Both counter arithmetic for flattening and sequential array copying are
executed. The shared matrix iteration keeps its common-denominator height
bound, and every retained coordinate has the exact original rational value.
-/
namespace CurrentAFT.BinaryRectangleIteration
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] multiplyCounter addCounter

def position (rows columns : ℕ) (row : Fin rows) (column : Fin columns) : UnaryCounterResult :=
  let multiplied := multiplyCounter columns row.val
  let added := addCounter multiplied.count column.val
  ⟨added.count, multiplied.work + added.work + 2⟩

theorem position_value (rows columns : ℕ) (row : Fin rows) (column : Fin columns) :
    (position rows columns row column).count = (finProdFinEquiv (row, column)).val := by
  simp only [position, addCounter_value, multiplyCounter_value]
  change columns * row.val + column.val = column.val + columns * row.val
  omega

def entry (rows columns : ℕ) (vector : Vector RationalBits (rows*columns))
    (row : Fin rows) (column : Fin columns) : CountedValue RationalBits :=
  let index := position rows columns row column
  let stored := readVector zero vector ⟨index.count, by rw [position_value]; exact (finProdFinEquiv (row, column)).isLt⟩
  ⟨stored.value, index.work + stored.work + 1⟩

def reshape (rows columns : ℕ) (vector : Vector RationalBits (rows*columns)) :
    CountedValue (Vector (Vector RationalBits columns) rows) :=
  storeData rows (fun row => storeData columns (entry rows columns vector row))





def entryWork (rows columns : ℕ) : ℕ :=
  columns*(2*rows+3)+2*(columns*rows)+3*(rows*columns)+8

def reshapeWork (rows columns : ℕ) : ℕ := rows*(columns*(entryWork rows columns+2)+4)+2





def run (rows columns : ℕ) (matrix : Vector (Vector RationalBits (rows*columns)) (rows*columns))
    (rhs : Vector RationalBits (rows*columns)) (steps : ℕ) :
    CountedValue (Vector (Vector RationalBits columns) rows) :=
  let iterated := iteration matrix rhs steps
  let result := reshape rows columns iterated.data
  ⟨result.value, iterated.work + result.work + 1⟩





noncomputable def reshapePolynomial (rows columns : Polynomial ℕ) : Polynomial ℕ :=
  rows*(columns*(columns*(2*rows+3)+2*(columns*rows)+3*(rows*columns)+10)+4)+2



noncomputable def workPolynomial (rows columns bits steps : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCalibrationIteration.workPolynomial (rows*columns) bits steps + reshapePolynomial rows columns + 1





noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] CurrentRectangleIndex.colors Parameters.base

variable {Source Target : Type*} [Fintype Source] [Fintype Target]





end
end CurrentAFT.BinaryRectangleIteration

end

section





























/-! Actual counters and full rectangular matrix/rhs buffers before calibration
iteration. The caller supplies the executed numerical entry program; all table
visits and copies, including zero-padded rows, are performed here. -/
namespace CurrentAFT.BinaryRectangleMaterialization
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryArithmetic.RationalBits GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus

abbrev Size (security order : ℕ) := ((order+1)^2)*(CurrentRectangleIndex.colors security)^order

structure Dimensions where
  rows : ℕ
  columns : ℕ
  size : ℕ
  work : ℕ


def dimensions (security order : ℕ) : Dimensions :=
  let modulus := PublicParameterProgram.modulus security
  let successor := addCounter order 1
  let rows := powerCounter successor.count 2
  let columns := powerCounter modulus.count order
  let size := multiplyCounter rows.count columns.count
  ⟨rows.count,columns.count,size.count,modulus.work+successor.work+rows.work+columns.work+size.work+5⟩

 theorem dimensions_values (security order : ℕ) :
    (dimensions security order).rows = (order+1)^2 ∧
    (dimensions security order).columns = (CurrentRectangleIndex.colors security)^order ∧
    (dimensions security order).size = Size security order := by
  simp only [dimensions, powerCounter_value, addCounter_value, multiplyCounter_value,
    CurrentRectangleIndex.colors, Size, and_self]


def rhsEntry (index : ℕ) : CountedValue RationalBits :=
  let hit := equalCounter index 0
  ⟨if hit.value then one else zero, hit.work+2⟩

 

structure Result (security order : ℕ) where
  matrix : Vector (Vector RationalBits (Size security order)) (Size security order)
  rhs : Vector RationalBits (Size security order)
  work : ℕ


def current (security order : ℕ)
    (entry : Fin (Size security order) → Fin (Size security order) → CountedValue RationalBits) : Result security order :=
  let dims := dimensions security order
  let matrix := storeData dims.size (fun output => storeData dims.size (fun input =>
    entry (output.cast (dimensions_values security order).2.2) (input.cast (dimensions_values security order).2.2)))
  let rhs := storeData dims.size (fun output => rhsEntry output.val)
  ⟨(matrix.value.map (fun row => row.cast (dimensions_values security order).2.2)).cast (dimensions_values security order).2.2,
    rhs.value.cast (dimensions_values security order).2.2,
    dims.work+matrix.work+rhs.work+dims.size+3⟩

 

 


def run (security order steps : ℕ)
    (entry : Fin (Size security order) → Fin (Size security order) → CountedValue RationalBits) :
    CountedValue (BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :=
  let table := current security order entry
  let result := BinaryRectangleIteration.run ((order+1)^2) ((CurrentRectangleIndex.colors security)^order) table.matrix table.rhs steps
  ⟨result.value,table.work+result.work+1⟩

noncomputable section
open scoped Classical
local instance finDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base


def scalarPoint (security order : ℕ) : CurrentRectangleIndex.Point security order :=
  ⟨zeroArity order,(Fin.elim0,Fin.elim0)⟩

 

 

 

 

end
end CurrentAFT.BinaryRectangleMaterialization

end

section

























/-! Polynomial resources for producing the complete rectangular matrix,
its exact scalar right-hand side, and the stored calibration iterate. -/
namespace CurrentAFT.BinaryRectangleResources
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryArithmetic.RationalBits BinaryRectangleMaterialization
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus


def dimensionsWork (security order : ℕ) : ℕ :=
  let q := CurrentRectangleIndex.colors security
  PublicParameterProgram.workBound security + (2*order+1) + powerCounterWork (order+1) 2 +
    powerCounterWork q order + ((order+1)^2*(2*q^order+3)+1) + 5

 


def currentWork (security order entryWork : ℕ) : ℕ :=
  let size := Size security order
  dimensionsWork security order + (size*(size*(entryWork+2)+4)+2) + (size*(3*size+6)+2) + size+3

 

noncomputable section
open scoped BigOperators


def columnsPolynomial (order : ℕ) : Polynomial ℕ := CurrentProposalResources.primeSizePolynomial^order

def sizePolynomial (order : ℕ) : Polynomial ℕ := Polynomial.C ((order+1)^2)*columnsPolynomial order

 

 

 


def dimensionsPolynomial (order : ℕ) : Polynomial ℕ :=
  let q := CurrentProposalResources.primeSizePolynomial
  PublicParameterProgram.workPolynomial + Polynomial.C (2*order+1+powerCounterWork (order+1) 2) +
    Polynomial.C (order+1)*(6*(q+1)^(order+2)+4) + Polynomial.C ((order+1)^2)*(2*q^order+3)+6

 


def currentPolynomial (order : ℕ) (entryWork : Polynomial ℕ) : Polynomial ℕ :=
  let size := sizePolynomial order
  dimensionsPolynomial order + (size*(size*(entryWork+2)+4)+2) + (size*(3*size+6)+2)+size+3

 


def runPolynomial (order : ℕ) (entryHeight entryWork steps : Polynomial ℕ) : Polynomial ℕ :=
  currentPolynomial order entryWork +
    BinaryRectangleIteration.workPolynomial (Polynomial.C ((order+1)^2)) (columnsPolynomial order) entryHeight steps + 1

 

end
end CurrentAFT.BinaryRectangleResources

end

section



























/-! Executed flattening inverse for the actual rectangular calibration arrays. -/
namespace CurrentAFT.BinaryRectangleAddress
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryRectangleMaterialization
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] dimensions

def current (security order : ℕ) (index : Fin (Size security order)) :
    CountedValue (CurrentRectangleIndex.Rectangle security order) :=
  let dims := dimensions security order
  let division := divideCounter index.val dims.columns
  let row : Fin ((order+1)^2) := ⟨division.quotient, by
    have hp : 0<dims.columns := by rw [(dimensions_values security order).2.1]; exact pow_pos (CurrentRectangleIndex.colors_pos security) _
    rw [(divideCounter_value index.val dims.columns hp).1]
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    rw [(dimensions_values security order).2.1]
    exact index.isLt⟩
  let column : Fin ((CurrentRectangleIndex.colors security)^order) := ⟨division.remainder,by
    have hp : 0<dims.columns := by rw [(dimensions_values security order).2.1]; exact pow_pos (CurrentRectangleIndex.colors_pos security) _
    rw [(divideCounter_value index.val dims.columns hp).2,← (dimensions_values security order).2.1]
    exact Nat.mod_lt _ hp⟩
  ⟨(row,column),dims.work+division.work+3⟩



noncomputable section
noncomputable def workPolynomial (order : ℕ) : Polynomial ℕ :=
  BinaryRectangleResources.dimensionsPolynomial order+
    500*(BinaryRectangleResources.sizePolynomial order+BinaryRectangleResources.columnsPolynomial order+2)^2+3



end
end CurrentAFT.BinaryRectangleAddress

end

section























/-! Fixed-degree radix decoding with actual binary long division and buffer reads. -/
namespace CurrentAFT.BinaryCounterTupleDecode
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def append {Value : Type*} {count : ℕ} (leading : Vector Value count) (last : Value) : CountedValue (Vector Value (count+1)) :=
  let entries := Vector.ofFn (fun index : Fin (count+1) =>
    Fin.lastCases (motive := fun _ => CountedValue Value) ⟨last,1⟩ (fun index => readVector last leading index) index)
  ⟨entries.map (fun entry => entry.value),(∑ index, (entries.get index).work)+2*(count+1)+2⟩





def current (base : ℕ) (hb : 0<base) : (count : ℕ) → ℕ → CountedValue (Vector (Fin base) count)
  | 0,_ => ⟨#v[],1⟩
  | count+1,code =>
    let divided := divideCounter code base
    let previous := current base hb count divided.quotient
    let last : Fin base := ⟨divided.remainder, by rw [(divideCounter_value code base hb).2]; exact Nat.mod_lt _ hb⟩
    let result := append previous.value last
    ⟨result.value,divided.work+previous.work+result.work+3⟩



def workBound (base capacity limit count : ℕ) : ℕ :=
  (count+1)*(500*(capacity+base+2)^2+(limit+1)*(3*limit+5)+5)



end CurrentAFT.BinaryCounterTupleDecode

end

section
























/-! Polynomially bounded rectangular addresses are decoded using executed
counter division, radix buffers, and safe-body comparisons. -/
namespace CurrentAFT.BinaryRectangleDecode
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram GradedControlAlgebra
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure Data (base order margin : ℕ) where
  arity : TruncatedArity order
  primary : Vector (Fin base) arity.val.1.val
  body : Vector (Fin base) arity.val.2.val
  safe : ∀ index, margin≤(body.get index).val ∧ (body.get index).val+margin<base

def Data.point {base order margin : ℕ} (data : Data base order margin) :
    RectanglePointIndex.Point base order (fun color => margin≤color.val ∧ color.val+margin<base) :=
  ⟨data.arity,data.primary.get,fun index => ⟨data.body.get index,data.safe index⟩⟩

def safe (base margin color : ℕ) : CountedValue Bool :=
  let lower := lessCounter color margin
  let shifted := addCounter color margin
  let upper := lessCounter shifted.count base
  ⟨!lower.value && upper.value,lower.work+shifted.work+upper.work+3⟩

theorem safe_value (base margin color : ℕ) : (safe base margin color).value=true ↔ margin≤color ∧ color+margin<base := by
  simp only [safe,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,lessCounter_value,addCounter_value]
  constructor
  · rintro ⟨hl,hu⟩
    refine ⟨?_,hu⟩
    by_contra h
    exact hl ((lessCounter_value color margin).mpr (by omega))
  · rintro ⟨hl,hu⟩
    exact ⟨fun h => by have hh := (lessCounter_value color margin).mp h; omega,hu⟩



def safeWord (base margin count : ℕ) (hb : 0<base) (word : Vector (Fin base) count) : CountedValue Bool :=
  BinaryProposalGuard.allFin count (fun index =>
    let color := readVector ⟨0,hb⟩ word index
    let check := safe base margin color.value.val
    ⟨check.value,color.work+check.work+1⟩)

theorem safeWord_value (base margin count : ℕ) (hb : 0<base) (word : Vector (Fin base) count) :
    (safeWord base margin count hb word).value=true ↔ ∀ index, margin≤(word.get index).val ∧ (word.get index).val+margin<base := by
  simp only [safeWord,BinaryProposalGuard.allFin_value,safe_value,readVector_value]



def current (base order margin : ℕ) (hb : 0<base) (row : Fin ((order+1)^2)) (column : Fin (base^order)) :
    CountedValue (Option (Data base order margin)) :=
  let shape := divideCounter row.val (order+1)
  let r : Fin (order+1) := ⟨shape.quotient, by
    rw [(divideCounter_value row.val (order+1) (by omega)).1]
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    simpa only [pow_two] using row.isLt⟩
  let s : Fin (order+1) := ⟨shape.remainder, by
    rw [(divideCounter_value row.val (order+1) (by omega)).2]
    exact Nat.mod_lt _ (by omega)⟩
  let degree := addCounter r.val s.val
  let valid := lessCounter degree.count (order+1)
  if hv : valid.value=true then
    let arity : TruncatedArity order := ⟨(r,s),by
      have h := (lessCounter_value _ _).mp hv
      change (addCounter r.val s.val).count<order+1 at h
      rw [addCounter_value] at h
      change r.val+s.val≤order
      omega⟩
    let capacity := powerCounter base degree.count
    let within := lessCounter column.val capacity.count
    if hw : within.value=true then
      let split := powerCounter base s.val
      let divided := divideCounter column.val split.count
      let primary := BinaryCounterTupleDecode.current base hb r.val divided.quotient
      let body := BinaryCounterTupleDecode.current base hb s.val divided.remainder
      let safe := safeWord base margin s.val hb body.value
      if hs : safe.value=true then
        ⟨some ⟨arity,primary.value,body.value,(safeWord_value base margin s.val hb body.value).mp hs⟩,
          shape.work+degree.work+valid.work+capacity.work+within.work+split.work+divided.work+primary.work+body.work+safe.work+12⟩
      else ⟨none,shape.work+degree.work+valid.work+capacity.work+within.work+split.work+divided.work+primary.work+body.work+safe.work+12⟩
    else ⟨none,shape.work+degree.work+valid.work+capacity.work+within.work+7⟩
  else ⟨none,shape.work+degree.work+valid.work+4⟩

end CurrentAFT.BinaryRectangleDecode

end

section




















/-! Resource bounds for executed rectangular address decoding. Every long
division, power counter, radix buffer and safe-body scan is included. -/
namespace CurrentAFT.BinaryRectangleDecodeResources
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram GradedControlAlgebra
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def headerWork (order : ℕ) : ℕ :=
  500*((order+1)^2+(order+1)+2)^2+(2*order+1)+(3*(order+1)+2)

def safeWork (base order margin : ℕ) : ℕ :=
  order*(3*order+8*base+3*margin+14)+1

def divisionWork (base order : ℕ) : ℕ := 500*(2*base^order+2)^2


def workBound (base order margin : ℕ) : ℕ :=
  headerWork order+2*powerCounterWork base order+(3*base^order+2)+divisionWork base order+
    2*BinaryCounterTupleDecode.workBound base (base^order) order order+safeWork base order margin+12

 

 

noncomputable section


def workPolynomial (order : ℕ) (base margin : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (headerWork order)+2*Polynomial.C (order+1)*(6*(base+1)^(order+2)+4)+
    (3*base^order+2)+500*(2*base^order+2)^2+
    2*Polynomial.C (order+1)*(500*(base^order+base+2)^2+Polynomial.C ((order+1)*(3*order+5))+5)+
    Polynomial.C order*(Polynomial.C (3*order)+8*base+3*margin+14)+1+12

 

 

 

end
end CurrentAFT.BinaryRectangleDecodeResources

end

section


























namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.BinaryRectangleDecode
end CurrentAFT.BinaryRectangleDecode
namespace CurrentAFT.BinaryRectangleDecode.Data
end CurrentAFT.BinaryRectangleDecode.Data
namespace CurrentAFT.BinaryRectangleDecode.Data.point
end CurrentAFT.BinaryRectangleDecode.Data.point




/-! Actual current-parameter rectangular decoding. The checked prime and safe
margin are computed by the proposal counters; returned arrays are precisely
the native palette words used by the coefficient programs. -/
namespace CurrentAFT.CurrentBinaryRectangleDecode
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram GradedControlAlgebra
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus

abbrev Data (security order : ℕ) :=
  BinaryRectangleDecode.Data (CurrentReferenceDraw.counts security).colors order (CurrentReferenceDraw.counts security).margin

 theorem colors_eq (security : ℕ) : (CurrentReferenceDraw.counts security).colors=CurrentRectangleIndex.colors security := rfl

 theorem colors_positive (security : ℕ) : 0<(CurrentReferenceDraw.counts security).colors :=
  CurrentReferenceDraw.colors_positive security

 theorem margin_eq (security : ℕ) : (CurrentReferenceDraw.counts security).margin=3*(security+2)^2 :=
  BinaryBodyProgram.margin_value security

 theorem safe_iff (security : ℕ) (color : Fin (CurrentRectangleIndex.colors security)) :
    (CurrentReferenceDraw.counts security).margin≤color.val ∧
        color.val+(CurrentReferenceDraw.counts security).margin<(CurrentReferenceDraw.counts security).colors ↔
      CurrentRectangleIndex.safe security color := by
  rw [margin_eq,colors_eq]
  unfold CurrentRectangleIndex.safe
  omega


def safeEquiv (security : ℕ) :
    {color : Fin (CurrentReferenceDraw.counts security).colors //
      (CurrentReferenceDraw.counts security).margin≤color.val ∧ color.val+(CurrentReferenceDraw.counts security).margin<(CurrentReferenceDraw.counts security).colors} ≃
    {color : Fin (CurrentRectangleIndex.colors security) // CurrentRectangleIndex.safe security color} where
  toFun color := ⟨color.val,(safe_iff security color.val).mp color.property⟩
  invFun color := ⟨color.val,(safe_iff security color.val).mpr color.property⟩
  left_inv _ := rfl
  right_inv _ := rfl


def nativePointEquiv (security order : ℕ) :
    RectanglePointIndex.Point (CurrentReferenceDraw.counts security).colors order
      (fun color => (CurrentReferenceDraw.counts security).margin≤color.val ∧ color.val+(CurrentReferenceDraw.counts security).margin<(CurrentReferenceDraw.counts security).colors) ≃
    RectanglePointIndex.Point (CurrentRectangleIndex.colors security) order (CurrentRectangleIndex.safe security) :=
  Equiv.sigmaCongrRight (fun arity : TruncatedArity order =>
    Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight (fun _ : Fin arity.val.2.val => safeEquiv security)))


def pointEquiv (security order : ℕ) :
    RectanglePointIndex.Point (CurrentReferenceDraw.counts security).colors order
      (fun color => (CurrentReferenceDraw.counts security).margin≤color.val ∧ color.val+(CurrentReferenceDraw.counts security).margin<(CurrentReferenceDraw.counts security).colors) ≃
    CurrentRectangleIndex.Point security order :=
  (nativePointEquiv security order).trans (CurrentRectangleIndex.pointEquiv security order)


def semanticPoint (security order : ℕ) (data : Data security order) : CurrentRectangleIndex.Point security order :=
  pointEquiv security order data.point


 

 

 


def current (security order : ℕ) (row : Fin ((order+1)^2)) (column : Fin ((CurrentReferenceDraw.counts security).colors^order)) :
    CountedValue (Option (Data security order)) :=
  let counts := CurrentReferenceDraw.counts security
  let result := BinaryRectangleDecode.current counts.colors order counts.margin (colors_positive security) row column
  ⟨result.value,counts.work+result.work+1⟩

 

 

 

noncomputable section


def workPolynomial (order : ℕ) : Polynomial ℕ :=
  CurrentReferenceCacheWork.countsWorkPolynomial+
    BinaryRectangleDecodeResources.workPolynomial order CurrentProposalResources.primeSizePolynomial (3*(Polynomial.X+2)^2)+1

 

end
end CurrentAFT.CurrentBinaryRectangleDecode

end

section



























/-! Actual flat-address decoding and zero padding around a finite response entry. -/
namespace CurrentAFT.BinaryRectangleEntry
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryRectangleMaterialization CurrentBinaryRectangleDecode
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def decodeFlat (security order : ℕ) (index : Fin (Size security order)) : CountedValue (Option (Data security order)) :=
  let address := BinaryRectangleAddress.current security order index
  let decoded := CurrentBinaryRectangleDecode.current security order address.value.1 address.value.2
  ⟨decoded.value,address.work+decoded.work+2⟩

def current (security order : ℕ) (entry : Data security order → Data security order → CountedValue RationalBits)
    (output input : Fin (Size security order)) : CountedValue RationalBits :=
  let out := decodeFlat security order output
  let source := decodeFlat security order input
  match out.value,source.value with
  | some outData,some sourceData =>
    let result := entry outData sourceData
    ⟨result.value,out.work+source.work+result.work+4⟩
  | _,_ => ⟨zero,out.work+source.work+3⟩





noncomputable section
noncomputable def decodeWorkPolynomial (order : ℕ) : Polynomial ℕ :=
  BinaryRectangleAddress.workPolynomial order+CurrentBinaryRectangleDecode.workPolynomial order+2
noncomputable def workPolynomial (order : ℕ) (entryWork : Polynomial ℕ) : Polynomial ℕ :=
  2*decodeWorkPolynomial order+entryWork+4



attribute [local irreducible] decodeFlat



end
end CurrentAFT.BinaryRectangleEntry

end

section















/-! Exact canonical-family products of centered point atoms. These are
identities of coefficient data, prior to any physical polynomial evaluation. -/
namespace CurrentAFT.PointFamilyProducts
open AFT ControlCoordinates ControlProduct CanonicalReconstruction GradedControlAlgebra BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def append {Color : Type*} {first second : ℕ} (left : Fin first → Color) (right : Fin second → Color) :
    Fin (first+second) → Color := fun index => Sum.elim left right (finSumFinEquiv.symm index)





def arity (order r s : ℕ) (h : r+s ≤ order) : TruncatedArity order :=
  ⟨(⟨r, by omega⟩, ⟨s, by omega⟩),h⟩

def pointFamily (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) {r s : ℕ} (h : r+s ≤ order) (colors : Fin r → Primary) (centers : Fin s → Body) :
    KernelFamily primary body order :=
  Pi.single (arity order r s h) (pointKernel primary body hp hb colors centers)























end
end CurrentAFT.PointFamilyProducts

end

section

















/-! The empty root component reconstructs the original canonical kernel
as coefficient data. No injectivity of physical evaluation is used. -/
namespace CurrentAFT.EmptyRootCoefficientIdentity
open AFT ControlCoordinates ControlProduct CanonicalReconstruction GradedControlAlgebra BackgroundFamilies
  LocalCoefficientFamily ProposalPrimary ActualControls CompleteRaising CompleteRaisingEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  primaryLaw bodyReference











end
end CurrentAFT.EmptyRootCoefficientIdentity

end

section






















/-! The one-queue, bounded-tag formula is exactly the full current response
on a weighted point column, including its independent leading component. -/
namespace CurrentAFT.FullResponseWeightedIdentity
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary ControlCoordinates ControlProduct CanonicalReconstruction
  UniformTaggedOutput ActualRootFamily FullResponsePointFormula ActualBackground
  RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  primaryLaw bodyReference

def sourceKernel (security order : ℕ) (source : Index security order) :=
  WeightedPointKernelProgram.actualKernel security source.2.1 source.2.2

def selected (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (source : Index security order) (chosen : Selection security source.1.val.1.val source.1.val.2.val)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) : Family security order :=
  ActualRootResponse.response order horder queue chosen ∅ layout (sourceKernel security order source)+
    ∑ tagged ∈ RationalFullResponseProgram.tags security order,
      ActualRootResponse.response order horder queue chosen tagged layout (sourceKernel security order source)

def choiceAverage (security order : ℕ) (horder : 1 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) : Family security order :=
  ∑ choice : Choice security source.1.val.1.val source.1.val.2.val,
    (choiceLaw security _ _ (primary_room security order hroom source.1)
      (body_room security order hroom source.1)).weight choice •
        selected security order horder queue source (selection security _ _ choice) layout

def fixedQueue (security order : ℕ) (horder : 2 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) : Family security order :=
  fixedQueueBackground security order horder queue * choiceAverage security order (by omega) hroom queue source layout

def response (security order : ℕ) (horder : 2 ≤ order) (hroom : 2*order ≤ security)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) : Family security order :=
  ∑ scalar : FirstHistogram.Scalar security, (DiffuseProfiles.scalarLaw security).weight scalar •
    fixedQueue security order horder hroom scalar.val source layout









end
end CurrentAFT.FullResponseWeightedIdentity

end

section






















/-! The numerical response minus its weighted point column is the defect,
with no additional identity matrix or redundant-coordinate correction. -/
namespace CurrentAFT.FullResponseWeightedIdentity
open AFT ActualBlockFock GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary FullResponsePointFormula RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
local instance defectFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension primaryLaw bodyReference



end
end CurrentAFT.FullResponseWeightedIdentity

end

end


