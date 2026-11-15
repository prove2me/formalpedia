-- Prove2me | Definitions.Def_InfoLossLAR_NativeSparsePrefix_07
-- name    : InfoLossLAR_NativeSparsePrefix_07
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T13:31:56.564132+00:00
-- url     : https://prove2.me/theorems/4298de33-7446-4b46-81d7-86aca2b195ff
-- title:
--   Joint tensor channels, public pools, and affine data
-- statement:
--   This package defines tensor and joint physical channels, centered coefficient maps, Fock coordinate data, tagged and mixed-tail interfaces, public pool numbering and source embedding, role slots, root-response data, and integral affine pairs.
--
--   These interfaces retain public records, protected source coordinates, channel evaluation, and affine outputs as distinct objects. They expose mathematical data and the supporting constructor APIs; the subsequent response, approximation, and transport bounds are stated as separate theorems. Recorded native operation charges are not by themselves platform machine-time certificates.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; Lean source modules AFT/TensorChannel.lean, AFT/ChannelCentering.lean, AFT/MixtureTail.lean, AFT/TaggedBlockTail.lean, AFT/LocalCoefficientLinear.lean, AFT/JointFock.lean, AFT/TensorChannelFormula.lean, AFT/JointPhysicalChannel.lean, AFT/PackedFock.lean, AFT/PackedFockEvaluation.lean, AFT/JointPhysicalFock.lean, AFT/PublicChartGaussian.lean, AFT/ResponseEnergy.lean, AFT/SignedFirstCoefficient.lean, AFT/SingletonFock.lean, AFT/ActualJointFock.lean, AFT/BlockCoefficientNorms.lean, AFT/RestrictedBlockMean.lean, AFT/ActualTaggedTail.lean, AFT/ActualInputMixedTail.lean, AFT/ActualFiniteControlTail.lean, AFT/FiniteSetNumbering.lean, AFT/PublicPools.lean, AFT/PublicSourceEmbedding.lean, AFT/ActualPublicSources.lean, AFT/RoleSourceSlots.lean, AFT/ActualPublicTaggedPlacement.lean, AFT/JointSignedChannel.lean, AFT/ActualRootResponse.lean, AFT/Affine.lean. Source bodies and declaration spans are recorded in native_sparse_prefix/manifest.json; SHA256 96e9a81b05bacc88cf26fca36b92550664491cc67b227f39ccdfe8457a590e8f. Repackaging of identical data declarations, with 4163 public types matched to native source and 7722 origin declarations recursively audited for standard logical axioms only.

import Definitions.Def_InfoLossLAR_NativeSparsePrefix_06

section







/-! # Tensor Hilbert operator bounds for arbitrary joint finite kernels -/

namespace AFT.TensorChannel

open scoped BigOperators Classical
noncomputable section

variable {Input Output : Type*} [Fintype Input] [Fintype Output]

/-- Apply finite local linear channels to all coordinates of one arbitrary
joint kernel. No product decomposition of that kernel is used. -/
def apply : (count : ℕ) →
    (Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) →
    ((Fin count → Input) → ℝ) → (Fin count → Output) → ℝ
  | 0, _, kernel, _ => kernel Fin.elim0
  | count + 1, channel, kernel, output =>
      channel 0 (fun first => apply count (fun index => channel index.succ)
        (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) (output 0)

omit [Fintype Input] [Fintype Output] in
@[simp] theorem apply_cons (count : ℕ)
    (channel : Fin (count + 1) → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin (count + 1) → Input) → ℝ) (first : Output) (rest : Fin count → Output) :
    apply (count + 1) channel kernel (Fin.cons first rest) =
      channel 0 (fun input => apply count (fun index => channel index.succ)
        (fun tail => kernel (Fin.cons input tail)) rest) first := by
  simp only [apply, Fin.cons_zero, Fin.cons_succ]

 theorem expectation_mono {Sample : Type*} [Fintype Sample]
    (law : FiniteDist Sample) {first second : Sample → ℝ} (h : ∀ point, first point ≤ second point) :
    law.expectation first ≤ law.expectation second :=
  Finset.sum_le_sum fun point _ => mul_le_mul_of_nonneg_left (h point) (law.nonneg point)

/-- The Hilbert norm of the complete tensor channel is the product of its
local bounds. This applies to every joint kernel, including nonseparable
kernels with arbitrary dependencies among the distinguished coordinates. -/
theorem energy_le (count : ℕ) (input : Fin count → FiniteDist Input)
    (output : Fin count → FiniteDist Output)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (bound : Fin count → ℝ)
    (hchannel : ∀ index kernel, (output index).l2Sq (channel index kernel) ≤
      bound index ^ 2 * (input index).l2Sq kernel)
    (kernel : (Fin count → Input) → ℝ) :
    (FiniteDist.independent output).l2Sq (apply count channel kernel) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.independent input).l2Sq kernel := by
  induction count with
  | zero =>
    have hconstant : kernel = fun _ => kernel Fin.elim0 := by
      funext word
      congr 1
      funext index
      exact Fin.elim0 index
    rw [hconstant]
    simp only [apply, FiniteDist.l2Sq, FiniteDist.expectation_const, Fin.prod_univ_zero, one_mul]
    exact le_rfl
  | succ count ih =>
    let tailInput := FiniteDist.independent (fun index : Fin count => input index.succ)
    let tailOutput := FiniteDist.independent (fun index : Fin count => output index.succ)
    let tailValue := fun first rest => apply count (fun index => channel index.succ)
      (fun tail => kernel (Fin.cons first tail)) rest
    have htail (first : Input) : tailOutput.l2Sq (tailValue first) ≤
        (∏ index : Fin count, bound index.succ ^ 2) * tailInput.l2Sq (fun rest => kernel (Fin.cons first rest)) :=
      ih (fun index => input index.succ) (fun index => output index.succ)
        (fun index => channel index.succ) (fun index => bound index.succ)
        (fun index => hchannel index.succ) _
    have hsplit : (FiniteDist.independent output).l2Sq (apply (count + 1) channel kernel) =
        tailOutput.expectation (fun rest => (output 0).l2Sq (channel 0 (fun first => tailValue first rest))) := by
      unfold FiniteDist.l2Sq
      rw [FiniteConcentration.expectation_cons]
      simp only [apply_cons]
      exact FiniteDist.expectation_comm _ _ _
    rw [hsplit]
    calc
      _ ≤ tailOutput.expectation (fun rest => bound 0 ^ 2 * (input 0).l2Sq (fun first => tailValue first rest)) :=
        expectation_mono tailOutput (fun rest => hchannel 0 _)
      _ = bound 0 ^ 2 * (input 0).expectation (fun first => tailOutput.l2Sq (tailValue first)) := by
        rw [FiniteDist.expectation_const_mul]
        congr 1
        exact FiniteDist.expectation_comm _ _ _
      _ ≤ bound 0 ^ 2 * (input 0).expectation (fun first =>
          (∏ index : Fin count, bound index.succ ^ 2) * tailInput.l2Sq (fun rest => kernel (Fin.cons first rest))) :=
        mul_le_mul_of_nonneg_left (expectation_mono (input 0) htail) (sq_nonneg _)
      _ = _ := by
        rw [FiniteDist.expectation_const_mul, Fin.prod_univ_succ]
        rw [mul_assoc]
        congr 2
        unfold FiniteDist.l2Sq
        exact (FiniteConcentration.expectation_cons count input (fun word => kernel word ^ 2)).symm








end
end AFT.TensorChannel

end

section





/-! # Exact canonical projection before finite local Hilbert channels -/

namespace AFT.TensorChannel

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Input Output : Type*} [Fintype Input] [Fintype Output]

omit [Fintype Output] in
/-- Orthogonal centering with respect to the actual input law. -/
def center (law : FiniteDist Input) : (Input → ℝ) →ₗ[ℝ] (Input → ℝ) where
  toFun kernel := fun point => kernel point - law.expectation kernel
  map_add' first second := by
    funext point
    change first point + second point - law.expectation (fun x => first x + second x) = _
    rw [FiniteDist.expectation_add]
    simp only [Pi.add_apply]
    ring
  map_smul' scalar kernel := by
    funext point
    change scalar * kernel point - law.expectation (fun x => scalar * kernel x) = _
    rw [FiniteDist.expectation_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype Output] in
@[simp] theorem center_apply (law : FiniteDist Input) (kernel : Input → ℝ) (point : Input) :
    center law kernel point = kernel point - law.expectation kernel := rfl



omit [Fintype Output] in
/-- Exact variance identity gives contraction, including laws with zeros. -/
theorem center_energy (law : FiniteDist Input) (kernel : Input → ℝ) :
    law.l2Sq (center law kernel) = law.l2Sq kernel - law.expectation kernel ^ 2 := by
  let mean := law.expectation kernel
  have hpoint (point : Input) : law.weight point * (kernel point - mean) ^ 2 =
      law.weight point * kernel point ^ 2 - 2 * mean * (law.weight point * kernel point) +
        law.weight point * mean ^ 2 := by ring
  change (∑ point, law.weight point * (kernel point - mean) ^ 2) = _
  simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, law.sum_one, one_mul]
  change law.l2Sq kernel - 2 * mean * mean + mean ^ 2 = law.l2Sq kernel - mean ^ 2
  ring

omit [Fintype Output] in
theorem center_energy_le (law : FiniteDist Input) (kernel : Input → ℝ) :
    law.l2Sq (center law kernel) ≤ law.l2Sq kernel := by
  rw [center_energy]
  exact sub_le_self _ (sq_nonneg _)



omit [Fintype Input] [Fintype Output] in
theorem apply_add (count : ℕ) (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (first second : (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel (first + second) output = apply count channel first output + apply count channel second output := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change channel 0 (fun input => apply count (fun index => channel index.succ)
      ((fun rest => first (Fin.cons input rest)) + (fun rest => second (Fin.cons input rest)))
      (fun index => output index.succ)) (output 0) = _
    simp only [ih]
    change channel 0 ((fun input => apply count (fun index => channel index.succ)
      (fun rest => first (Fin.cons input rest)) (fun index => output index.succ)) +
      (fun input => apply count (fun index => channel index.succ)
        (fun rest => second (Fin.cons input rest)) (fun index => output index.succ))) (output 0) = _
    rw [map_add]
    rfl

omit [Fintype Input] [Fintype Output] in
theorem apply_smul (count : ℕ) (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (scalar : ℝ) (kernel : (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel (scalar • kernel) output = scalar * apply count channel kernel output := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change channel 0 (fun input => apply count (fun index => channel index.succ)
      (scalar • (fun rest => kernel (Fin.cons input rest))) (fun index => output index.succ)) (output 0) = _
    simp only [ih]
    change channel 0 (scalar • (fun input => apply count (fun index => channel index.succ)
      (fun rest => kernel (Fin.cons input rest)) (fun index => output index.succ))) (output 0) = _
    rw [map_smul]
    rfl

omit [Fintype Input] [Fintype Output] in
/-- The full tensor operation is itself a literal linear map. -/
def applyLinear (count : ℕ) (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) :
    ((Fin count → Input) → ℝ) →ₗ[ℝ] ((Fin count → Output) → ℝ) where
  toFun := apply count channel
  map_add' first second := funext (apply_add count channel first second)
  map_smul' scalar kernel := funext (apply_smul count channel scalar kernel)







end
end AFT.TensorChannel

end

section









namespace AFT
end AFT
namespace AFT.BlockProducts
end AFT.BlockProducts



/-! # Complete signed tails commute with the actual conditioning mixture -/

namespace AFT.HistogramNormalization

open scoped BigOperators Classical

variable {Slot Color Source : Type*} [Fintype Slot] [Fintype Color] [Fintype Source]

omit [Fintype Slot] [Fintype Color] in
theorem expectation_square_le (source : FiniteDist Source) (value : Source → ℝ) :
    source.expectation value ^ 2 ≤ source.l2Sq value := by
  have h := CanonicalMoments.expectation_mul_sq_le source value (fun _ => 1)
  simpa only [mul_one, one_pow, FiniteDist.l2Sq, FiniteDist.expectation, FiniteDist.sum_one] using h















end AFT.HistogramNormalization

end

section








namespace AFT
end AFT
namespace AFT.Fock
end AFT.Fock
namespace AFT.Fock.response
end AFT.Fock.response
namespace AFT.Fock.tensorResponse
end AFT.Fock.tensorResponse
namespace AFT.TaggedFock
end AFT.TaggedFock



/-! # The complete signed tail of actual marked blocks and their complement -/

namespace AFT.BlockProducts

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

variable {Index Color TaggedSlot : Type*} [Fintype Index] [Fintype Color] [Fintype TaggedSlot]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

local instance _root_.AFT.BlockProducts.instDecidableEqSum_aFT {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance _root_.AFT.BlockProducts.instDecidableEqSigma_aFT : DecidableEq (Sigma Slots) := Classical.decEq _

/-- Actual signed mass: one arbitrary joint tagged output and every remaining
independent physical block. Dependence within the tagged outputs is retained. -/
def taggedBlockMass (tagged : (TaggedSlot → Color) → ℝ)
    (law : (index : Index) → FiniteDist (Slots index → Color))
    (word : (TaggedSlot ⊕ Sigma Slots) → Color) : ℝ :=
  tagged (word ∘ Sum.inl) * blockMass Slots law (word ∘ Sum.inr)



/-- The finite marked-coefficient budget computed from the actual signed mass. -/
def taggedCoefficientEnergy (reference : FiniteDist Color) (tagged : (TaggedSlot → Color) → ℝ)
    (population : ℕ) (radius : ℝ) : ℝ :=
  (Fintype.card TaggedSlot + 1 : ℕ) * ∑ degree ∈ Finset.range (Fintype.card TaggedSlot + 1),
    (degree.factorial : ℝ) * 2 ^ degree * BlockFock.tensorEnergy
      (TensorFock.normalizedTensor population radius
        (LocalTensors.degreeTensor (fun _ : TaggedSlot => reference) tagged) degree)



/-- The three explicit local coefficient conditions of the independent-block
estimate, at its doubled radius. -/
def CubicBlockConditions (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color))
    (population capacity : ℕ) (radius : ℝ) : Prop :=
  (SelectionBound.nonlinearSupport
      (fun index word => (Real.sqrt 2) ^ 2 * normalizedQuadratic Slots reference law
        (radius / Real.sqrt population) index word)
      (fun index word => (Real.sqrt 2) ^ 3 * normalizedCubic Slots reference law
        (radius / Real.sqrt population) index word)).card ≤ capacity ∧
  (∑ index, ∑ color, (Real.sqrt 2 * normalizedLinear Slots reference law
      (radius / Real.sqrt population) index color) ^ 2) ≤ 1 / 8 ∧
  (∑ index, (128 * SelectionBound.localPairNorm
      (fun index word => (Real.sqrt 2) ^ 2 * normalizedQuadratic Slots reference law
        (radius / Real.sqrt population) index word) index +
        128 * Real.sqrt capacity * SelectionBound.localTripleNorm
          (fun index word => (Real.sqrt 2) ^ 3 * normalizedCubic Slots reference law
            (radius / Real.sqrt population) index word) index)) ≤ 1 / 2



end

end AFT.BlockProducts

end

section










/-! # The actual finite Fock coefficients form one linear Hilbert channel -/

namespace AFT.LocalTensors

open scoped BigOperators Classical
noncomputable section
local instance localCoefficientLinearFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- Actual finite tensor symmetrization is a linear operation. -/
def symmetrizeLinear : BlockFock.Tensor Slot Color →ₗ[ℝ] BlockFock.Tensor Slot Color where
  toFun := BlockFock.symmetrize
  map_add' first second := by
    funext word
    simp only [BlockFock.symmetrize, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' scalar tensor := by
    funext word
    simp only [BlockFock.symmetrize, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro permutation _
    ring

/-- Every actual selected homogeneous piece is linear in the signed mass. -/
def degreePieceLinear (reference : Slot → FiniteDist Color) (degree : ℕ) (selected : Finset Slot) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] BlockFock.Tensor (Fin degree) Color where
  toFun mass := degreePiece reference mass degree selected
  map_add' first second := by
    funext word
    by_cases h : Fintype.card selected = degree
    · simp only [degreePiece, dif_pos h, localTensor_formula, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    · simp only [degreePiece, dif_neg h, Pi.add_apply, add_zero]
  map_smul' scalar mass := by
    funext word
    by_cases h : Fintype.card selected = degree
    · simp only [degreePiece, dif_pos h, localTensor_formula, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro input _
      ring
    · simp only [degreePiece, dif_neg h, Pi.smul_apply, smul_eq_mul, mul_zero]

/-- All degree coefficients are the literal linear response of the signed
physical mass. This map includes the actual finite symmetrization. -/
def degreeTensorLinear (reference : Slot → FiniteDist Color) (degree : ℕ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] BlockFock.Tensor (Fin degree) Color :=
  symmetrizeLinear.comp (∑ selected : Finset Slot, degreePieceLinear reference degree selected)

@[simp] theorem degreeTensorLinear_apply (reference : Slot → FiniteDist Color) (degree : ℕ)
    (mass : (Slot → Color) → ℝ) : degreeTensorLinear reference degree mass = degreeTensor reference mass degree := by
  simp only [degreeTensorLinear, LinearMap.comp_apply, LinearMap.sum_apply, symmetrizeLinear,
    LinearMap.coe_mk, AddHom.coe_mk, degreePieceLinear]
  unfold degreeTensor
  congr 1
  funext word
  exact Finset.sum_apply word Finset.univ (fun selected => degreePiece reference mass degree selected)

/-- Every degree and every color-word basis vector of the actual finite
marked Fock space, without choosing a basis of the centered subspace. -/
abbrev FockCoordinate (Slot Color : Type*) [Fintype Slot] :=
  Sigma (fun degree : Fin (Fintype.card Slot + 1) => Fin degree.val → Color)

/-- A single explicit linear channel whose counting norm is exactly the
marked coefficient budget. Scalar local-response estimates can therefore
be tensored directly on arbitrary joint input kernels. -/
def finiteFockChannel (reference : FiniteDist Color) (population : ℕ) (radius : ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] (FockCoordinate Slot Color → ℝ) where
  toFun mass coordinate :=
    Real.sqrt ((Fintype.card Slot + 1 : ℕ) * (coordinate.1.val.factorial : ℝ) * 2 ^ coordinate.1.val) *
      (radius / Real.sqrt population) ^ coordinate.1.val *
        degreeTensor (fun _ : Slot => reference) mass coordinate.1.val coordinate.2
  map_add' first second := by
    funext coordinate
    rw [← degreeTensorLinear_apply, map_add]
    simp only [Pi.add_apply, mul_add, degreeTensorLinear_apply]
  map_smul' scalar mass := by
    funext coordinate
    rw [← degreeTensorLinear_apply, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, degreeTensorLinear_apply]
    ring



end
end AFT.LocalTensors

end

section








namespace AFT
end AFT
namespace AFT.Fock
end AFT.Fock
namespace AFT.Fock.response
end AFT.Fock.response
namespace AFT.Fock.tensorResponse
end AFT.Fock.tensorResponse
namespace AFT.TaggedFock
end AFT.TaggedFock



/-! # Multiplying finite coefficient spaces without decomposing the input kernel -/

namespace AFT.JointFock

open MeasureTheory TensorFock NonlinearFock
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance jointFockSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Choice : Index → Type*) [∀ index, Fintype (Choice index)]
variable (Slots : (index : Index) → Choice index → Type*) [∀ index choice, Fintype (Slots index choice)]

/-- Local degree/word coordinates are exactly a choice of all local degrees
and one word on their disjoint union. This reindexing does not separate the
joint coefficient array into rank-one terms. -/
def coordinateEquiv :
    ((index : Index) → Sigma (fun choice : Choice index => Slots index choice → Color)) ≃
      Sigma (fun choice : (index : Index) → Choice index => (Sigma (fun index => Slots index (choice index))) → Color) where
  toFun point := ⟨(fun index => (point index).1), fun slot => (point slot.1).2 slot.2⟩
  invFun point := fun index => ⟨point.1 index, fun slot => point.2 ⟨index, slot⟩⟩
  left_inv point := by funext index; rfl
  right_inv point := by rcases point with ⟨choice, word⟩; rfl

/-- The homogeneous tensor for one vector of local degrees is just a slice
of the original arbitrary joint array. -/
def degreeTensor
    (coefficient : ((index : Index) → Sigma (fun choice : Choice index => Slots index choice → Color)) → ℝ)
    (choice : (index : Index) → Choice index) :
    BlockFock.Tensor (Sigma (fun index => Slots index (choice index))) Color :=
  fun word => coefficient (fun index => ⟨choice index, fun slot => word ⟨index, slot⟩⟩)



/-- Evaluate the actual arbitrary joint array by multiplying the local
monomials at one shared Gaussian color vector. -/
def evaluation
    (coefficient : ((index : Index) → Sigma (fun choice : Choice index => Slots index choice → Color)) → ℝ)
    (value : Color → ℂ) : ℂ :=
  ∑ point, (coefficient point : ℂ) * ∏ index, wordMonomial (point index).2 value





end
end AFT.JointFock

end

section





/-! # The tensor operator is the literal finite signed joint response -/

namespace AFT.TensorChannel
open scoped BigOperators Classical
noncomputable section
variable {Input Output : Type*} [Fintype Input]

/-- A local linear response is the sum of its responses to the actual input
coordinate vectors. This does not impose any separability on joint inputs. -/
theorem channel_sum_single (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : Input → ℝ) (output : Output) :
    channel kernel output = ∑ point, kernel point * channel (Pi.single point 1) output := by
  have heq : kernel = ∑ point, kernel point • (Pi.single point (1 : ℝ) : Input → ℝ) := by
    funext point
    simp [Pi.single_apply]
  conv_lhs => rw [heq, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The actual finite tensor response is a single signed sum over the full
joint input word, rather than a rank-one representation of the kernel. -/
theorem apply_formula (count : ℕ)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel kernel output =
      ∑ point, kernel point * ∏ index, channel index (Pi.single (point index) 1) (output index) := by
  induction count with
  | zero =>
    simp only [apply, Fin.prod_univ_zero, mul_one, Fintype.sum_unique]
    congr 1
  | succ count ih =>
    rw [show apply (count + 1) channel kernel output = channel 0
      (fun first => apply count (fun index => channel index.succ)
        (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) (output 0) from rfl]
    rw [channel_sum_single]
    simp only [ih, Finset.sum_mul]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (count + 1) => Input)), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro rest _
    change (kernel (Fin.cons first rest) * ∏ x, channel x.succ (Pi.single (rest x) 1) (output x.succ)) *
      channel 0 (Pi.single first 1) (output 0) = _
    simp only [Fin.prod_univ_succ, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
    ring

/-- The exact finite formula is independent of the chosen decidable equality
on its finite coordinate set. -/
theorem apply_formula_instance (count : ℕ) [decision : DecidableEq (Fin count)]
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel kernel output =
      ∑ point, kernel point * ∏ index, channel index (Pi.single (point index) 1) (output index) := by
  have hd : decision = instDecidableEqFin count := Subsingleton.elim _ _
  cases hd
  exact apply_formula count channel kernel output



end
end AFT.TensorChannel

end

section












/-! # Exact joint signed mass and its physical generating polynomial -/

namespace AFT.JointPhysicalChannel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Input Color : Type*} [Fintype Index] [Fintype Input] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]
local instance jointPhysicalChannelSigmaDecEq : DecidableEq (Sigma Slots) := Classical.decEq _

/-- The literal signed output of arbitrary local finite channels fed by one
joint input kernel. The joint kernel is retained inside the single input sum. -/
def mass (channel : (index : Index) → (Input → ℝ) →ₗ[ℝ] ((Slots index → Color) → ℝ))
    (kernel : (Index → Input) → ℝ) (output : Sigma Slots → Color) : ℝ :=
  ∑ input, kernel input * ∏ index, channel index (Pi.single (input index) 1) (fun slot => output ⟨index, slot⟩)







end
end AFT.JointPhysicalChannel

end

section












/-! # One common finite Fock alphabet for heterogeneous local output blocks -/
namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
local instance packedFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

abbrev PackedCoordinate (maximum : ℕ) (Color : Type*) :=
  Sigma (fun degree : Fin (maximum + 1) => Fin degree.val → Color)

/-- All local degrees are embedded into one common alphabet; unused higher
degrees are the actual zero coefficients, not an assumed truncation. -/
def packedFockChannel (reference : FiniteDist Color) (maximum population : ℕ) (radius : ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] (PackedCoordinate maximum Color → ℝ) where
  toFun mass coordinate := Real.sqrt (coordinate.1.val.factorial : ℝ) *
    (Real.sqrt 2 * (radius / Real.sqrt population)) ^ coordinate.1.val *
      degreeTensor (fun _ : Slot => reference) mass coordinate.1.val coordinate.2
  map_add' first second := by
    funext coordinate
    rw [← degreeTensorLinear_apply, map_add]
    simp only [Pi.add_apply, mul_add, degreeTensorLinear_apply]
  map_smul' scalar mass := by
    funext coordinate
    rw [← degreeTensorLinear_apply, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, degreeTensorLinear_apply]
    ring





end
end AFT.LocalTensors

end

section










/-! # Decoding the finite coefficient channel gives the actual polynomial -/
namespace AFT.LocalTensors
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
local instance packedFockEvaluationFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- A factorial decoder of norm at most one. It converts the coefficient
Hilbert channel into its actual polynomial at the common Gaussian vector. -/
def fockDecoder (maximum : ℕ) (coordinate : PackedCoordinate maximum Color) : ℝ :=
  1 / Real.sqrt (coordinate.1.val.factorial : ℝ)









end
end AFT.LocalTensors

end

section












/-! # Arbitrary joint physical responses through their exact finite Fock channels -/
namespace AFT.JointPhysicalChannel
open MeasureTheory LocalTensors TensorFock
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Input Color : Type*} [Fintype Index] [Fintype Input] [Fintype Color]
local instance jointPhysicalFockSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _
local instance jointPhysicalFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- A factorial decoder only contracts the complete joint coefficient array. -/
def decodedCoefficient (maximum : ℕ) (coefficient : (Index → PackedCoordinate maximum Color) → ℝ)
    (point : Index → PackedCoordinate maximum Color) : ℝ :=
  coefficient point * ∏ index, fockDecoder maximum (point index)





variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

/-- The actual packed response array, still containing the full joint input
kernel inside one finite sum. -/
def coefficient (reference : FiniteDist Color) (maximum population : ℕ) (radius : ℝ)
    (channel : (index : Index) → (Input → ℝ) →ₗ[ℝ] ((Slots index → Color) → ℝ))
    (kernel : (Index → Input) → ℝ) (point : Index → PackedCoordinate maximum Color) : ℝ :=
  ∑ input, kernel input * ∏ index,
    packedFockChannel reference maximum population radius
      (channel index (Pi.single (input index) 1)) (point index)







end
end AFT.JointPhysicalChannel

end

section







namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration


/-! # The complete positive chart and public-anchor conditional output -/

namespace AFT.V7Calibration

open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance publicGaussianFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

abbrev PublicOffsets (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter))
    (sample : bodySample cutoffScale parameter × Bool) :=
  {offset : ℤ // offset ∈ anchorInterval (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter)}





abbrev PublicChartFamily (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter)) :=
  (sample : bodySample cutoffScale parameter × Bool) → PublicOffsets cutoffScale parameter mark sample →
    FiniteDist (Chart (ZMod (Parameters.modulus parameter)))









end
end AFT.V7Calibration

end

section








namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap


/-! # Weighted Hilbert energy of the literal four-term primary response -/

namespace AFT

open scoped BigOperators Classical
noncomputable section

variable {Color : Type*} [Fintype Color]

theorem profileSquareNorm_four_le (reference first second third fourth : Color → ℝ)
    (hr : ∀ color, 0 ≤ reference color) :
    profileSquareNorm reference (first + second + third - fourth) ≤
      4 * (profileSquareNorm reference first + profileSquareNorm reference second +
        profileSquareNorm reference third + profileSquareNorm reference fourth) := by
  simp only [profileSquareNorm, Pi.add_apply, Pi.sub_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro color _
  have hpoint : (first color + second color + third color - fourth color) ^ 2 ≤
      4 * (first color ^ 2 + second color ^ 2 + third color ^ 2 + fourth color ^ 2) := by
    nlinarith only [sq_nonneg (first color - second color), sq_nonneg (third color + fourth color),
      sq_nonneg (first color + second color - (third color - fourth color))]
  exact (div_le_div_of_nonneg_right hpoint (hr color)).trans_eq (by ring)

theorem profileSquareNorm_reference_comparison (primary reference profile : Color → ℝ)
    (comparison : ℝ) (hp : ∀ color, 0 < primary color) (hr : ∀ color, 0 < reference color)
    (hcompare : ∀ color, primary color ≤ comparison * reference color) :
    profileSquareNorm reference profile ≤ comparison * profileSquareNorm primary profile := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  apply (div_le_iff₀ (hr color)).mpr
  have hh := mul_le_mul_of_nonneg_right (hcompare color)
    (div_nonneg (sq_nonneg (profile color)) (hp color).le)
  have heq : primary color * (profile color ^ 2 / primary color) = profile color ^ 2 := by
    field_simp [ne_of_gt (hp color)]
  rw [heq] at hh
  nlinarith only [hh]

/-- The diagonal, sign response, full public anchor, and root compensator
are estimated in the actual output reference norm. -/
theorem four_channel_response_energy (primary reference sign response : Color → ℝ)
    (firstAnchor secondAnchor : Color → Color → ℝ) (activation diagonal majorant l1 anchorCost : ℝ)
    (hp : ∀ color, 0 < primary color) (hpmass : ∑ color, primary color = 1)
    (hr : ∀ color, 0 < reference color)
    (hdiag : ∀ color, primary color ≤ diagonal * reference color)
    (hsign : ∀ color, |sign color| ≤ 1)
    (hmajorant : 0 ≤ majorant) (hv : ∀ color, |response color| ≤ majorant * reference color)
    (hl1 : (∑ color, |response color|) ≤ l1)
    (hfirst0 : ∀ color output, 0 ≤ firstAnchor color output)
    (hsecond0 : ∀ color output, 0 ≤ secondAnchor color output)
    (hfirstMass : ∀ color, ∑ output, firstAnchor color output = 1)
    (hsecondMass : ∀ color, ∑ output, secondAnchor color output = 1)
    (hfirst : ∀ output, applyAnchor firstAnchor primary output ≤ anchorCost * reference output)
    (hsecond : ∀ output, applyAnchor secondAnchor primary output ≤ anchorCost * reference output)
    (profile : Color → ℝ) :
    profileSquareNorm reference
      (activation • profile + (signFunctional sign profile) • response +
        activation • applyAnchor firstAnchor profile - activation • applyAnchor secondAnchor profile) ≤
      4 * (activation ^ 2 * diagonal + majorant * l1 + 2 * activation ^ 2 * anchorCost) *
        profileSquareNorm primary profile := by
  have hn := profileSquareNorm_nonneg primary profile (fun color => (hp color).le)
  have hd := mul_le_mul_of_nonneg_left
    (profileSquareNorm_reference_comparison primary reference profile diagonal hp hr hdiag) (sq_nonneg activation)
  have h1 := mul_le_mul_of_nonneg_left
    (applyAnchor_profileSquareNorm_le primary reference firstAnchor profile anchorCost hp hr
      hfirst0 hfirstMass hfirst) (sq_nonneg activation)
  have h2 := mul_le_mul_of_nonneg_left
    (applyAnchor_profileSquareNorm_le primary reference secondAnchor profile anchorCost hp hr
      hsecond0 hsecondMass hsecond) (sq_nonneg activation)
  have hvnorm := (signProfile_square_bound reference response majorant hr hv).trans
    (mul_le_mul_of_nonneg_left hl1 hmajorant)
  have hsnorm := mul_le_mul (signFunctional_sq_le primary sign profile hp hpmass hsign)
    hvnorm (profileSquareNorm_nonneg reference response (fun color => (hr color).le)) hn
  have hfour := profileSquareNorm_four_le reference (activation • profile)
    ((signFunctional sign profile) • response) (activation • applyAnchor firstAnchor profile)
    (activation • applyAnchor secondAnchor profile) (fun color => (hr color).le)
  simp only [profileSquareNorm_smul] at hfour
  nlinarith only [hd, h1, h2, hsnorm, hfour]

end
end AFT

end

section






namespace AFT
end AFT
namespace AFT.LocalTensors
end AFT.LocalTensors


/-! # The exact first Fock coefficient of an arbitrary signed finite mass -/

namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
local instance signedFirstCoefficientFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- The full signed one-point color count, before subtracting its total mass. -/
def signedColorCount (mass : (Slot → Color) → ℝ) (color : Color) : ℝ :=
  ∑ input, mass input * ∑ slot, if input slot = color then (1 : ℝ) else 0

/-- The actual first symmetric coefficient is the sum of the whitened
one-site responses, preserving cancellation between all physical outputs. -/
theorem signed_degreeTensor_one_formula (reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (color : Color) :
    degreeTensor (fun _ : Slot => reference) mass 1 (fun _ => color) =
      ∑ input, mass input * ∑ slot, atomCoefficient reference (input slot) color := by
  have hpiece (selected : Finset Slot) :
      degreePiece (fun _ => reference) mass 1 selected (fun _ => color) =
        if selected.card = 1 then localTensor (fun _ => reference) mass selected (fun _ => color) else 0 := by
    by_cases h : selected.card = 1
    · have hh : Fintype.card selected = 1 := by simpa using h
      simp only [degreePiece, dif_pos hh, if_pos h, Function.comp_def]
    · have hh : Fintype.card selected ≠ 1 := by simpa using h
      simp only [degreePiece, dif_neg hh, if_neg h]
  have hsym : degreeTensor (fun _ : Slot => reference) mass 1 (fun _ => color) =
      ∑ selected : Finset Slot, degreePiece (fun _ => reference) mass 1 selected (fun _ => color) := by
    unfold degreeTensor BlockFock.symmetrize
    simp only [Function.comp_def]
    rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  rw [hsym]
  simp_rw [hpiece]
  rw [← Finset.sum_filter]
  have hsets : Finset.univ.filter (fun selected : Finset Slot => selected.card = 1) =
      Finset.univ.powersetCard 1 := by ext selected; simp
  rw [hsets, Finset.powersetCard_one, Finset.sum_map]
  simp_rw [localTensor_formula]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot _
  congr 1
  change (∏ selected : ({slot} : Finset Slot), atomCoefficient reference (input selected) color) = _
  exact (Finset.prod_coe_sort ({slot} : Finset Slot)
    (fun index => atomCoefficient reference (input index) color)).trans (Finset.prod_singleton _ _)

/-- For zero total signed mass the exact first coefficient is the whitened
signed count profile, with no loss from bounding the output slots separately. -/
theorem degreeTensor_one_zero_mass (reference : FiniteDist Color)
    (href : ∀ color, 0 < reference.weight color)
    (mass : (Slot → Color) → ℝ) (hmass : ∑ input, mass input = 0) (color : Color) :
    degreeTensor (fun _ : Slot => reference) mass 1 (fun _ => color) =
      signedColorCount mass color / Real.sqrt (reference.weight color) := by
  rw [signed_degreeTensor_one_formula]
  have hs : Real.sqrt (reference.weight color) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (href color))
  have hsq := Real.sq_sqrt (reference.nonneg color)
  have hatom (input : Color) : atomCoefficient reference input color =
      (if input = color then (1 : ℝ) else 0) / Real.sqrt (reference.weight color) -
        Real.sqrt (reference.weight color) := by
    unfold atomCoefficient Hoeffding.centeredAtom
    split_ifs <;> field_simp [hs, (href color).ne'] <;> nlinarith [hsq]
  simp_rw [hatom]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_sub]
  rw [← Finset.sum_mul, hmass, zero_mul, sub_zero]
  unfold signedColorCount
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro input _
  rw [← Finset.sum_div]
  ring

/-- The first-degree Fock energy equals the actual signed count-profile
energy exactly. This applies to every finite output block and signed mass. -/
theorem degreeTensor_one_energy_zero_mass (reference : FiniteDist Color)
    (href : ∀ color, 0 < reference.weight color)
    (mass : (Slot → Color) → ℝ) (hmass : ∑ input, mass input = 0) :
    BlockFock.tensorEnergy (degreeTensor (fun _ : Slot => reference) mass 1) =
      profileSquareNorm reference.weight (signedColorCount mass) := by
  unfold BlockFock.tensorEnergy profileSquareNorm
  have he := (Equiv.funUnique (Fin 1) Color).symm.sum_comp
    (fun word => degreeTensor (fun _ : Slot => reference) mass 1 word ^ 2)
  rw [← he]
  apply Finset.sum_congr rfl
  intro color _
  change degreeTensor (fun _ : Slot => reference) mass 1 (fun _ => color) ^ 2 = _
  rw [degreeTensor_one_zero_mass reference href mass hmass, div_pow,
    Real.sq_sqrt (reference.nonneg color)]

end
end AFT.LocalTensors

end

section












/-! # Complete Fock energy of a genuine canonical singleton response -/

namespace AFT.LocalTensors

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance singletonFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]







end
end AFT.LocalTensors

end

section



































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.HistogramNormalization
end AFT.HistogramNormalization
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.PhysicalBlockTensors.fourOutputCount
end AFT.PhysicalBlockTensors.fourOutputCount
namespace AFT.PhysicalBlockTensors.tripleOutputCount
end AFT.PhysicalBlockTensors.tripleOutputCount
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBlockBodyLaw
end AFT.V7Calibration.actualBlockBodyLaw
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualRootValue
end AFT.V7Calibration.actualRootValue
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.fixedChartTriple
end AFT.V7Calibration.fixedChartTriple
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.fixedRootAnchor
end AFT.V7Calibration.fixedRootAnchor
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerAnchorProfile
end AFT.V7Calibration.integerAnchorProfile
namespace AFT.V7Calibration.integerAnchorShiftProfile
end AFT.V7Calibration.integerAnchorShiftProfile
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.marginalRootAnchor
end AFT.V7Calibration.marginalRootAnchor
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.publicAnchorFiniteProfile
end AFT.V7Calibration.publicAnchorFiniteProfile
namespace AFT.V7Calibration.publicChartEndpointMean
end AFT.V7Calibration.publicChartEndpointMean
namespace AFT.V7Calibration.publicChartRaw
end AFT.V7Calibration.publicChartRaw
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedChartTriple
end AFT.V7Calibration.signedChartTriple
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.V7Calibration.signedSliceAtSource
end AFT.V7Calibration.signedSliceAtSource
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap




/-! # All actual primary and body channels on arbitrary joint canonical input -/
namespace AFT.V7Calibration
open Filter GaussianSource LocalTensors JointPhysicalChannel
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualJointFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualJointFockSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- A primary score changes its two endpoints, attached body and compensator;
a body score changes its single physical body output. -/
def actualRoleSlots : Bool → Type
  | true => Fin 4
  | false => Fin 1

instance actualRoleSlotsFintype (role : Bool) : Fintype (actualRoleSlots role) := by
  cases role <;> dsimp [actualRoleSlots] <;> infer_instance

def actualRoleInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (role : Bool) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  if role then actualPrimaryLaw cutoffScale parameter beta else actualBodyLaw cutoffScale parameter beta









end
end AFT.V7Calibration

end

section








/-! # Norms of normalized physical block coefficients -/

namespace AFT.BlockProducts

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.BlockProducts.instDecidableEqFin_aFT (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]











end

end AFT.BlockProducts

end

section











namespace AFT
end AFT
namespace AFT.BlockProducts
end AFT.BlockProducts
namespace AFT.BlockProducts.splitSlotsEquiv
end AFT.BlockProducts.splitSlotsEquiv
namespace AFT.V7Calibration
end AFT.V7Calibration



/-! # Exact removed-block means and their dimension-free bounds -/

namespace AFT.BlockProducts

open scoped BigOperators Classical
noncomputable section

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

/-- The literal degree-one block tensor in Euclidean color coordinates. -/
def linearVector (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ) (index : Index) :
    EuclideanSpace ℝ Color := WithLp.toLp 2 (normalizedLinear Slots reference law scale index)

omit [Fintype Index] in
@[simp] theorem linearVector_apply (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ) (index : Index) (color : Color) :
    (linearVector Slots reference law scale index).ofLp color = normalizedLinear Slots reference law scale index color := rfl








end
end AFT.BlockProducts

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts
open scoped BigOperators Classical Topology
noncomputable section
local instance restrictedBlockMeanFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance restrictedBlockMeanSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _







end
end AFT.V7Calibration

end

section































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BlockProducts
end AFT.BlockProducts
namespace AFT.FiniteConcentration
end AFT.FiniteConcentration
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.condition
end AFT.FiniteDist.condition
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.normalizedRoot
end AFT.GaussianSource.normalizedRoot
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.rootMomentConstant
end AFT.GaussianSource.rootMomentConstant
namespace AFT.GaussianSource.rootPrefixDensity
end AFT.GaussianSource.rootPrefixDensity
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.GaussianSource.v7RootKernelSq
end AFT.GaussianSource.v7RootKernelSq
namespace AFT.GaussianSource.v7RootThetaBound
end AFT.GaussianSource.v7RootThetaBound
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBlockBodyLaw
end AFT.V7Calibration.actualBlockBodyLaw
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualFockScale
end AFT.V7Calibration.actualFockScale
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualRootValue
end AFT.V7Calibration.actualRootValue
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile


/-! # Complete physical marked-block tails with arbitrary joint signed output -/

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
local instance actualTaggedTailFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualTaggedTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualTaggedTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

abbrev actualMarkedSlots (parameter : ℕ) (selected : Finset (blockIndex parameter)) :=
  Sigma (fun index : {i : blockIndex parameter // i ∈ selected} => blockSlots parameter index)









end
end AFT.V7Calibration

end

section










namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration



/-! # The complete mixed tail of actual arbitrary joint primary/body input -/
namespace AFT.V7Calibration
open Filter GaussianSource LocalTensors JointPhysicalChannel HistogramNormalization BlockProducts
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualInputMixedTailFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualInputMixedTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualInputMixedTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Physical slot placement together with the actual source coordinates used
by its primary, attached, compensator and singleton channels. -/
structure ActualTaggedPlacement (parameter count : ℕ) (role : Fin count → Bool)
    (selected : Finset (blockIndex parameter)) where
  attached : Fin count → blockIndex parameter
  compensator : Fin count → blockIndex parameter
  body : Fin count → blockIndex parameter
  slots : Sigma (fun index => actualRoleSlots (role index)) ≃ actualMarkedSlots parameter selected











end
end AFT.V7Calibration

end

section

















namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.HistogramNormalization
end AFT.HistogramNormalization
namespace AFT.HistogramNormalization.densityTail
end AFT.HistogramNormalization.densityTail
namespace AFT.JointPhysicalChannel
end AFT.JointPhysicalChannel
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualRolePoolCapacity
end AFT.V7Calibration.actualRolePoolCapacity
namespace AFT.V7Calibration.actualRoleRateFactor
end AFT.V7Calibration.actualRoleRateFactor



/-! # Complete tails of actual finite signed control representations -/
namespace AFT.V7Calibration
open Filter GaussianSource BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualFiniteControlTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualFiniteControlTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

/-- A literal finite canonical joint input and its physical placement. -/
structure ActualCanonicalControl (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) where
  count : ℕ
  role : Fin count → Bool
  selected : Finset (blockIndex parameter)
  placement : ActualTaggedPlacement parameter count role selected
  kernel : (Fin count → Fin (Parameters.modulus parameter)) → ℝ
  canonical : Hoeffding.Canonical
    (fun index => actualRoleInput cutoffScale parameter beta (role index)) Finset.univ kernel













end
end AFT.V7Calibration

end

section





/-! # Sorting a finite public set using an explicitly given coordinate code -/
namespace AFT

 def finiteSetNumbering {State : Type*} {size : ℕ} (index : State≃Fin size) (set : Finset State) :
    Fin set.card≃set :=
  letI : LinearOrder State := LinearOrder.lift' index index.injective
  (set.orderIsoOfFin rfl).toEquiv

 def finiteSetMatching {State : Type*} {size : ℕ} (index : State≃Fin size)
    (first second : Finset State) (hcard : first.card ≤ second.card) : first↪second :=
  (finiteSetNumbering index first).symm.toEmbedding.trans
    ((Fin.castLEEmb hcard).trans (finiteSetNumbering index second).toEmbedding)

end AFT

end

section













/-! # Actual disjoint public control and reserve pools -/

namespace AFT.PublicPools

open scoped BigOperators Classical

noncomputable section

variable {Position : Type*} [Fintype Position] [DecidableEq Position]

def controls (legs queue : Finset Position) := legs \ queue

def available (legs queue : Finset Position) := (legs ∪ queue)ᶜ

omit [Fintype Position] in
theorem controls_card_le (legs queue : Finset Position) : (controls legs queue).card ≤ legs.card :=
  Finset.card_le_card Finset.sdiff_subset

theorem available_card_lower (legs queue : Finset Position) :
    Fintype.card Position - legs.card - queue.card ≤ (available legs queue).card := by
  rw [available, Finset.card_compl]
  have hh := Finset.card_union_le legs queue
  omega



def matchingPositions (legs queue : Finset Position)
    (pairing : controls legs queue ↪ available legs queue) : Finset Position :=
  Finset.univ.map ⟨fun control => (pairing control).val,
    fun _ _ h => pairing.injective (Subtype.ext h)⟩

@[simp] theorem matchingPositions_card (legs queue : Finset Position)
    (pairing : controls legs queue ↪ available legs queue) :
    (matchingPositions legs queue pairing).card = (controls legs queue).card := by
  simp only [matchingPositions, Finset.card_map, Finset.card_univ, Fintype.card_coe]



def reserve (legs queue : Finset Position)
    (pairing : controls legs queue ↪ available legs queue) : Finset Position :=
  available legs queue \ matchingPositions legs queue pairing





end
end AFT.PublicPools

namespace AFT.GaussianSource

open scoped BigOperators Classical
open V7Calibration PublicPools FiniteDist

noncomputable section

/-- The actual V7 sizes leave more than half of all bodies after removing
all attachments, queue positions, and one compensator for each leg. -/
theorem actual_pool_budget (parameter : ℕ) :
    2 * (2 * Parameters.legs parameter + Parameters.modulus parameter) ≤ Parameters.bodies parameter := by
  have hsecurity : 1 ≤ Parameters.security parameter := (by decide : 1 ≤ 2).trans (Parameters.security_ge_two parameter)
  have hleg : Parameters.legs parameter ≤ Parameters.modulus parameter :=
    (pow_le_pow_right₀ hsecurity (by omega : 30 ≤ 40)).trans (Parameters.modulus_bounds parameter).1
  have hmean : 8 ≤ Parameters.meanDensity parameter := by
    have hh := Nat.pow_le_pow_left (Parameters.security_ge_two parameter) 20
    dsimp [Parameters.meanDensity]
    omega
  have hdim : 8 * Parameters.modulus parameter ≤ Parameters.dimension parameter := by
    simpa only [Parameters.dimension, Nat.mul_comm] using Nat.mul_le_mul_left (Parameters.modulus parameter) hmean
  have hpop := Parameters.population_identity parameter
  omega

def actualLegBodies (parameter : ℕ) : Finset (blockIndex parameter) :=
  (Finset.univ : Finset (Fin (Parameters.legs parameter))).map ⟨Sum.inl, Sum.inl_injective⟩

@[simp] theorem actualLegBodies_card (parameter : ℕ) :
    (actualLegBodies parameter).card = Parameters.legs parameter := by
  simp only [actualLegBodies, Finset.card_map, Finset.card_univ, Fintype.card_fin]

def actualControlMatching (parameter : ℕ) (placement : Equiv.Perm (blockIndex parameter)) :
    controls (actualLegBodies parameter) (permutationMask (actualQueueSelection parameter) placement) ↪
      available (actualLegBodies parameter) (permutationMask (actualQueueSelection parameter) placement) :=
  finiteSetMatching (blockIndexNumbering parameter) _ _ (by
    have hc := controls_card_le (actualLegBodies parameter)
      (permutationMask (actualQueueSelection parameter) placement)
    have ha := available_card_lower (actualLegBodies parameter)
      (permutationMask (actualQueueSelection parameter) placement)
    simp only [actualLegBodies_card, permutationMask_card, actualQueueSelection_card, blockIndex_card] at hc ha
    have hh := actual_pool_budget parameter
    omega)

def actualReservedBodies (parameter : ℕ) (placement : Equiv.Perm (blockIndex parameter)) :
    Finset (blockIndex parameter) :=
  reserve _ _ (actualControlMatching parameter placement)



end
end AFT.GaussianSource

end

section











/-! # Distinct physical sources from the real public matching and reserve -/
namespace AFT.PublicPools
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Position Primary Body : Type*} [Fintype Position] [DecidableEq Position]

/-- Attached sources, their injectively matched compensators, and reserved
body sources are three genuinely disjoint populations. -/
def sourceFunction (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) :
    (Primary ⊕ Primary) ⊕ Body → Position
  | .inl (.inl index) => (primary index).val
  | .inl (.inr index) => (pairing (primary index)).val
  | .inr index => (body index).val

theorem sourceFunction_injective (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) :
    Function.Injective (sourceFunction legs queue pairing primary body) := by
  have hp (i : Primary) : (primary i).val∈legs := (Finset.mem_sdiff.mp (primary i).property).1
  have hc (i : Primary) : (pairing (primary i)).val∉legs := by
    have hh := Finset.mem_compl.mp (pairing (primary i)).property
    exact fun hi => hh (Finset.mem_union_left queue hi)
  have hb (i : Body) : (body i).val∉legs := by
    have hh := Finset.mem_compl.mp (Finset.mem_sdiff.mp (body i).property).1
    exact fun hi => hh (Finset.mem_union_left queue hi)
  have hm (i : Primary) : (pairing (primary i)).val∈matchingPositions legs queue pairing :=
    Finset.mem_map.mpr ⟨primary i,Finset.mem_univ _,rfl⟩
  have hbm (i : Body) : (body i).val∉matchingPositions legs queue pairing :=
    (Finset.mem_sdiff.mp (body i).property).2
  rintro (⟨i|i⟩|i) (⟨j|j⟩|j) he <;> dsimp only [sourceFunction] at he
  · exact congrArg (Sum.inl ∘ Sum.inl) (primary.injective (Subtype.ext he))
  · exact False.elim (hc j (he ▸ hp i))
  · exact False.elim (hb j (he ▸ hp i))
  · exact False.elim (hc i (he.symm ▸ hp j))
  · exact congrArg (Sum.inl ∘ Sum.inr) (primary.injective (pairing.injective (Subtype.ext he)))
  · exact False.elim (hbm j (he ▸ hm i))
  · exact False.elim (hb i (he.symm ▸ hp j))
  · exact False.elim (hbm i (he.symm ▸ hm j))
  · exact congrArg Sum.inr (body.injective (Subtype.ext he))

def sourceEmbedding (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) :
    (Primary ⊕ Primary) ⊕ Body ↪ Position :=
  ⟨sourceFunction legs queue pairing primary body,sourceFunction_injective legs queue pairing primary body⟩



variable [Fintype Primary] [Fintype Body]

def sourceSelection (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) : Finset Position :=
  Finset.univ.map (sourceEmbedding legs queue pairing primary body)

def sourceEquiv (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) :
    ((Primary ⊕ Primary) ⊕ Body) ≃ sourceSelection legs queue pairing primary body :=
  Equiv.ofBijective (fun source => ⟨sourceEmbedding legs queue pairing primary body source,
    Finset.mem_map.mpr ⟨source,Finset.mem_univ _,rfl⟩⟩) ⟨
      fun a b h => (sourceEmbedding legs queue pairing primary body).injective (congrArg Subtype.val h),by
      rintro ⟨position,hposition⟩
      obtain ⟨source,_,hs⟩ := Finset.mem_map.mp hposition
      exact ⟨source,Subtype.ext hs⟩⟩

@[simp] theorem sourceEquiv_val (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing)
    (source : (Primary ⊕ Primary) ⊕ Body) :
    (sourceEquiv legs queue pairing primary body source).val=sourceEmbedding legs queue pairing primary body source := rfl

end
end AFT.PublicPools

end

section













/-! # Actual public choices have disjoint, queue-free physical root sources -/
namespace AFT.V7Calibration
open GaussianSource PublicPools FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

abbrev actualControlPool (n : ℕ) (placement : Equiv.Perm (blockIndex n)) :=
  controls (actualLegBodies n) (permutationMask (actualQueueSelection n) placement)

abbrev ActualPublicPrimaryChoice (n : ℕ) (placement : Equiv.Perm (blockIndex n)) (Primary : Type*) :=
  Primary ↪ actualControlPool n placement

abbrev ActualPublicBodyChoice (n : ℕ) (placement : Equiv.Perm (blockIndex n)) (Body : Type*) :=
  Body ↪ actualReservedBodies n placement

def actualPublicSourceEmbedding (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body) :
    (Primary ⊕ Primary) ⊕ Body ↪ blockIndex n :=
  sourceEmbedding _ _ (actualControlMatching n placement) primary body

def actualPublicSelected (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body) : Finset (blockIndex n) :=
  sourceSelection _ _ (actualControlMatching n placement) primary body

def actualPublicSourceEquiv (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body) :
    ((Primary ⊕ Primary) ⊕ Body) ≃ actualPublicSelected n placement primary body :=
  sourceEquiv _ _ (actualControlMatching n placement) primary body

@[simp] theorem actualPublicSourceEquiv_val (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (source : (Primary ⊕ Primary) ⊕ Body) :
    (actualPublicSourceEquiv n placement primary body source).val=actualPublicSourceEmbedding n placement primary body source := rfl



theorem mem_actualLegBodies_iff (n : ℕ) (index : blockIndex n) :
    index∈actualLegBodies n ↔ ∃ leg,index=Sum.inl leg := by
  simp only [actualLegBodies,Finset.mem_map,Finset.mem_univ,true_and,Function.Embedding.coeFn_mk]
  exact exists_congr fun _ => eq_comm

omit [Fintype Primary] [Fintype Body] in
theorem actualPublicSource_attached (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (index : Primary) : ∃ leg,actualPublicSourceEmbedding n placement primary body (.inl (.inl index))=Sum.inl leg := by
  apply (mem_actualLegBodies_iff n _).mp
  exact (Finset.mem_sdiff.mp (primary index).property).1

omit [Fintype Primary] [Fintype Body] in
theorem actualPublicSource_compensator (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (index : Primary) : ∃ free,actualPublicSourceEmbedding n placement primary body (.inl (.inr index))=Sum.inr free := by
  have hn : actualPublicSourceEmbedding n placement primary body (.inl (.inr index))∉actualLegBodies n := by
    exact fun h => (Finset.mem_compl.mp (actualControlMatching n placement (primary index)).property)
      (Finset.mem_union_left _ h)
  cases he : actualPublicSourceEmbedding n placement primary body (.inl (.inr index)) with
  | inl leg => exact False.elim (hn ((mem_actualLegBodies_iff n _).mpr ⟨leg,he⟩))
  | inr free => exact ⟨free,rfl⟩

omit [Fintype Primary] [Fintype Body] in
theorem actualPublicSource_body (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (index : Body) : ∃ free,actualPublicSourceEmbedding n placement primary body (.inr index)=Sum.inr free := by
  have hn : actualPublicSourceEmbedding n placement primary body (.inr index)∉actualLegBodies n := by
    exact fun h => (Finset.mem_compl.mp (Finset.mem_sdiff.mp (body index).property).1)
      (Finset.mem_union_left _ h)
  cases he : actualPublicSourceEmbedding n placement primary body (.inr index) with
  | inl leg => exact False.elim (hn ((mem_actualLegBodies_iff n _).mpr ⟨leg,he⟩))
  | inr free => exact ⟨free,rfl⟩


@[simp] theorem actualPublicSelected_card (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body) :
    (actualPublicSelected n placement primary body).card=2*Fintype.card Primary+Fintype.card Body := by
  simp only [actualPublicSelected,sourceSelection,Finset.card_map,Finset.card_univ,Fintype.card_sum]
  omega











end
end AFT.V7Calibration

end

section










/-! # Exact physical output coordinates of primary and body roles -/
namespace AFT.V7Calibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev PrimaryRoles {count : ℕ} (role : Fin count → Bool) := {i : Fin count // role i=true}
abbrev BodyRoles {count : ℕ} (role : Fin count → Bool) := {i : Fin count // ¬role i=true}
abbrev RoleSources {count : ℕ} (role : Fin count → Bool) := (PrimaryRoles role ⊕ PrimaryRoles role) ⊕ BodyRoles role

def roleSourceSlots {count : ℕ} (role : Fin count → Bool) : RoleSources role → Type
  | .inl (.inl _) => Fin 3
  | .inl (.inr _) => Fin 1
  | .inr _ => Fin 1

instance roleSourceSlotsFintype {count : ℕ} (role : Fin count → Bool) (source : RoleSources role) :
    Fintype (roleSourceSlots role source) := by rcases source with ⟨_|_⟩|_ <;> dsimp [roleSourceSlots] <;> infer_instance

def rolePartition {count : ℕ} (role : Fin count → Bool) : (PrimaryRoles role ⊕ BodyRoles role) ≃ Fin count :=
  Equiv.sumCompl (fun index => role index=true)

def primaryRoleSlotEquiv {count : ℕ} (role : Fin count → Bool) (index : PrimaryRoles role) :
    actualRoleSlots (role (rolePartition role (.inl index))) ≃ Fin 4 :=
  Equiv.cast (by change actualRoleSlots (role index.val)=Fin 4; rw [index.property]; rfl)

def bodyRoleSlotEquiv {count : ℕ} (role : Fin count → Bool) (index : BodyRoles role) :
    actualRoleSlots (role (rolePartition role (.inr index))) ≃ Fin 1 :=
  Equiv.cast (by
    change actualRoleSlots (role index.val)=Fin 1
    have hh : role index.val=false := by simpa using index.property
    rw [hh]
    rfl)

/-- Four primary outputs are the attached triple followed by its compensator. -/
def primaryOutputSplit (Primary : Type*) : (Primary × Fin 4) ≃ (Primary × Fin 3) ⊕ (Primary × Fin 1) :=
  (Equiv.prodCongr (Equiv.refl Primary) (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4).symm).trans
    (Equiv.prodSumDistrib Primary (Fin 3) (Fin 1))

def roleOutputPartition {count : ℕ} (role : Fin count → Bool) :
    (Sigma (fun index => actualRoleSlots (role index))) ≃
      (PrimaryRoles role × Fin 4) ⊕ (BodyRoles role × Fin 1) :=
  ((Equiv.sigmaCongrLeft (β:=fun index => actualRoleSlots (role index)) (rolePartition role)).symm.trans
    (Equiv.sumSigmaDistrib (fun index => actualRoleSlots (role (rolePartition role index))))).trans
      (Equiv.sumCongr (Equiv.sigmaEquivProdOfEquiv (primaryRoleSlotEquiv role))
        (Equiv.sigmaEquivProdOfEquiv (bodyRoleSlotEquiv role)))

def sourceOutputPartition {count : ℕ} (role : Fin count → Bool) :
    Sigma (roleSourceSlots role) ≃
      ((PrimaryRoles role × Fin 3) ⊕ (PrimaryRoles role × Fin 1)) ⊕ (BodyRoles role × Fin 1) :=
  (Equiv.sumSigmaDistrib (roleSourceSlots role)).trans
    (Equiv.sumCongr ((Equiv.sumSigmaDistrib (fun index => roleSourceSlots role (.inl index))).trans
      (Equiv.sumCongr (Equiv.sigmaEquivProd _ _) (Equiv.sigmaEquivProd _ _)))
      (Equiv.sigmaEquivProd _ _))

def roleOutputSourceEquiv {count : ℕ} (role : Fin count → Bool) :
    (Sigma (fun index => actualRoleSlots (role index))) ≃ Sigma (roleSourceSlots role) :=
  ((roleOutputPartition role).trans (Equiv.sumCongr (primaryOutputSplit (PrimaryRoles role))
    (Equiv.refl _))).trans (sourceOutputPartition role).symm


@[simp] theorem roleOutputSourceEquiv_symm_attached {count : ℕ} (role : Fin count → Bool)
    (index : PrimaryRoles role) (slot : Fin 3) :
    (roleOutputSourceEquiv role).symm ⟨.inl (.inl index),slot⟩=
      ⟨index.val,(primaryRoleSlotEquiv role index).symm (Fin.castAdd 1 slot)⟩ := by rfl

@[simp] theorem roleOutputSourceEquiv_symm_compensator {count : ℕ} (role : Fin count → Bool)
    (index : PrimaryRoles role) (slot : Fin 1) :
    (roleOutputSourceEquiv role).symm ⟨.inl (.inr index),slot⟩=
      ⟨index.val,(primaryRoleSlotEquiv role index).symm (Fin.natAdd 3 slot)⟩ := by rfl

@[simp] theorem roleOutputSourceEquiv_symm_body {count : ℕ} (role : Fin count → Bool)
    (index : BodyRoles role) (slot : Fin 1) :
    (roleOutputSourceEquiv role).symm ⟨.inr index,slot⟩=
      ⟨index.val,(bodyRoleSlotEquiv role index).symm slot⟩ := by rfl

end
end AFT.V7Calibration

end

section













/-! # Concrete tagged placements from the actual public pools -/
namespace AFT.V7Calibration
open GaussianSource PublicPools FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {count : ℕ} (n : ℕ) (placement : Equiv.Perm (blockIndex n)) (role : Fin count → Bool)
    (primary : ActualPublicPrimaryChoice n placement (PrimaryRoles role))
    (body : ActualPublicBodyChoice n placement (BodyRoles role))

def actualPublicSourceSlotEquiv (source : RoleSources role) :
    roleSourceSlots role source ≃ blockSlots n (actualPublicSourceEmbedding n placement primary body source) :=
  Equiv.cast (by
    rcases source with ⟨index|index⟩|index
    · obtain ⟨leg,hleg⟩ := actualPublicSource_attached n placement primary body index
      rw [hleg]
      rfl
    · obtain ⟨free,hfree⟩ := actualPublicSource_compensator n placement primary body index
      rw [hfree]
      rfl
    · obtain ⟨free,hfree⟩ := actualPublicSource_body n placement primary body index
      rw [hfree]
      rfl)

def actualPublicSlotsEquiv : Sigma (fun index => actualRoleSlots (role index)) ≃
    actualMarkedSlots n (actualPublicSelected n placement primary body) :=
  ((roleOutputSourceEquiv role).trans (Equiv.sigmaCongrRight
    (actualPublicSourceSlotEquiv n placement role primary body))).trans
    (Equiv.sigmaCongrLeft (β:=fun source : actualPublicSelected n placement primary body => blockSlots n source.val)
      (actualPublicSourceEquiv n placement primary body))

def actualPublicAttached (index : Fin count) : blockIndex n :=
  if h : role index=true then (primary ⟨index,h⟩).val else
    Sum.inl ⟨0,by have hh := Parameters.security_ge_two n; unfold Parameters.legs; positivity⟩

def actualPublicCompensator (index : Fin count) : blockIndex n :=
  if h : role index=true then (actualControlMatching n placement (primary ⟨index,h⟩)).val else
    Sum.inl ⟨0,by have hh := Parameters.security_ge_two n; unfold Parameters.legs; positivity⟩

def actualPublicBody (index : Fin count) : blockIndex n :=
  if h : ¬role index=true then (body ⟨index,h⟩).val else
    Sum.inl ⟨0,by have hh := Parameters.security_ge_two n; unfold Parameters.legs; positivity⟩



@[simp] theorem actualPublicAttached_source (index : PrimaryRoles role) :
    actualPublicAttached n placement role primary index.val=
      actualPublicSourceEmbedding n placement primary body (.inl (.inl index)) := by
  simp only [actualPublicAttached,dif_pos index.property]
  rfl

@[simp] theorem actualPublicCompensator_source (index : PrimaryRoles role) :
    actualPublicCompensator n placement role primary index.val=
      actualPublicSourceEmbedding n placement primary body (.inl (.inr index)) := by
  simp only [actualPublicCompensator,dif_pos index.property]
  rfl

@[simp] theorem actualPublicBody_source (index : BodyRoles role) :
    actualPublicBody n placement role body index.val=
      actualPublicSourceEmbedding n placement primary body (.inr index) := by
  simp only [actualPublicBody,dif_pos index.property]
  rfl




/-- The slot equivalence preserves the actual physical source index, rather
than merely its cardinality. -/
@[simp] theorem actualPublicSlotsEquiv_source
    (coordinate : Sigma (fun index => actualRoleSlots (role index))) :
    (actualPublicSlotsEquiv n placement role primary body coordinate).1.val=
      actualPublicSourceEmbedding n placement primary body ((roleOutputSourceEquiv role coordinate).1) := rfl





end
end AFT.V7Calibration

end

section




namespace AFT
end AFT


/-! # Joint source/input extension of actual signed finite channels -/

namespace AFT
open scoped BigOperators Classical
noncomputable section

/-- Averaging a family of signed profiles is contractive in every fixed
weighted profile Hilbert space. Source probabilities remain inside the sum. -/
theorem profileSquareNorm_average_le {Source Output : Type*} [Fintype Source] [Fintype Output]
    (source : FiniteDist Source) (reference : Output → ℝ) (href : ∀ output, 0 ≤ reference output)
    (profile : Source → Output → ℝ) :
    profileSquareNorm reference (fun output => ∑ point, source.weight point * profile point output) ≤
      ∑ point, source.weight point * profileSquareNorm reference (profile point) := by
  calc
    _ ≤ ∑ output, (∑ point, source.weight point * profile point output ^ 2) / reference output := by
      apply Finset.sum_le_sum
      intro output _
      apply div_le_div_of_nonneg_right _ (href output)
      have hh : (∑ point, source.weight point * profile point output) ^ 2 ≤
          (∑ point, source.weight point) * (∑ point, source.weight point * profile point output ^ 2) := by
        apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
        · intro point _; exact source.nonneg point
        · intro point _; exact mul_nonneg (source.nonneg point) (sq_nonneg _)
        · intro point _; ring
      simpa only [source.sum_one, one_mul] using hh
    _ = _ := by
      simp only [Finset.sum_div, profileSquareNorm, Finset.mul_sum, mul_div_assoc]
      exact Finset.sum_comm

/-- Turning a density into its actual signed mass preserves its Hilbert
square exactly, including zero-probability input atoms. -/
theorem profileSquareNorm_weight_mul {Input : Type*} [Fintype Input]
    (input : FiniteDist Input) (density : Input → ℝ) :
    profileSquareNorm input.weight (fun color => input.weight color * density color) = input.l2Sq density := by
  apply Finset.sum_congr rfl
  intro color _
  change (input.weight color * density color) ^ 2 / input.weight color = input.weight color * density color ^ 2
  by_cases hz : input.weight color = 0
  · simp only [hz, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), div_zero]
  · field_simp

end
end AFT

end

section
























namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.HistogramNormalization
end AFT.HistogramNormalization
namespace AFT.HistogramNormalization.densityTail
end AFT.HistogramNormalization.densityTail
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.centeredRootBodyProfile
end AFT.V7Calibration.centeredRootBodyProfile
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile




/-! # The actual finite root-response operator and exact source expansion -/

namespace AFT.Hoeffding
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Source : Type*} [Fintype Index] [Fintype Source]



variable [DecidableEq Index]



end
end AFT.Hoeffding

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The literal centered histogram generating polynomial of an arbitrary
signed physical output mass, retaining all homogeneous degrees. -/
def centeredGeneratingLinear (reference : Color → ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun mass := ∑ word, mass word • ∏ slot, centeredFactor reference (word slot)
  map_add' first second := by
    simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' scalar mass := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.smul_sum,smul_smul]

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualRootResponseFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualRootResponseSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualRootResponseSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _



























end
end AFT.V7Calibration

end

section




/-!
# Affine evaluation and the exact AFT preservation interface

The linear part is an actual linear equivalence, so legality is represented
by invertibility, not by an arbitrary proposition named `legal`.
For the paper take `R = ZMod q` and `V = Fin d → ZMod q`.
This file does not construct the calibrated Gaussian sampler of Section 9.
-/

namespace AFT

open scoped Classical

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- The reduced affine data returned by a legal AFT sampler. The paper permits
returning residues rather than integer lifts (immediately after Definition 5.1). -/
structure AffinePair where
  linear : V ≃ₗ[R] V
  offset : V

namespace AffinePair

variable {R V}

/-- The deterministic evaluator, exactly `Q x + b`. -/
def eval (pair : AffinePair R V) (input : V) : V :=
  pair.linear input + pair.offset

/-- Every legal affine evaluator is a bijection. -/
def equiv (pair : AffinePair R V) : V ≃ V where
  toFun := pair.eval
  invFun output := pair.linear.symm (output - pair.offset)
  left_inv input := by simp [eval]
  right_inv output := by simp [eval]

@[simp] theorem equiv_apply (pair : AffinePair R V) (input : V) :
    pair.equiv input = pair.eval input := rfl



/-- The always-legal fallback in Appendix A. -/
def fallback : AffinePair R V := ⟨LinearEquiv.refl R V, 0⟩

@[simp] theorem fallback_eval (input : V) :
    (fallback : AffinePair R V).eval input = input := by simp [eval, fallback]

/-- Left multiplication acts on each column of a public matrix. -/
def columnsEquiv (pair : AffinePair R V) (Column : Type*) :
    (Column → V) ≃ (Column → V) :=
  Equiv.piCongrRight (fun _ => pair.linear.toEquiv)

@[simp] theorem columnsEquiv_apply (pair : AffinePair R V) (Column : Type*)
    (matrix : Column → V) (column : Column) :
    pair.columnsEquiv Column matrix column = pair.linear (matrix column) := rfl



end AffinePair

section Probability

variable {R V} [Fintype V]
variable {Sample Column : Type*} [Fintype Sample] [Fintype Column]







end Probability
end AFT

end


