-- Prove2me | Definitions.Def_OAIQ259US000
-- name    : OAIQ259US000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:07:20.391086+00:00
-- url     : https://prove2.me/theorems/59f08c24-48aa-41a5-b5ff-0b180a29fa86
-- title:
--   Definitions bundle OAIQ259US000 of the split of OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 167 declarations of OpenAI's Lean: 81 definitions, 3 inductive types or structures, 1 instance and 82 theorems. The definitions and types are `OAI.Saxl.Balance.BandsValid`, `OAI.Saxl.Balance.FixedComponentSums`, `OAI.Saxl.Balance.FourInterlacing`, `OAI.Saxl.Balance.OutputBands`, `OAI.Saxl.Balance.OutputBands.Allows`, `OAI.Saxl.Balance.OutputBands.alphabet`, `OAI.Saxl.Balance.OutputBands.label`, `OAI.Saxl.Balance.OutputBands.letterLabel`, `OAI.Saxl.Balance.Packing`, `OAI.Saxl.Balance.Packing.congr`, `OAI.Saxl.Balance.Piece`, `OAI.Saxl.Balance.Piece.join`, `OAI.Saxl.Balance.bigColumns`, `OAI.Saxl.Balance.componentWords`, `OAI.Saxl.Balance.cyclicSquareMap`, `OAI.Saxl.Balance.fixedSumSpace`, `OAI.Saxl.Balance.joinedFiberHom`, `OAI.Saxl.Balance.joinedLabels`, `OAI.Saxl.Balance.outerWordMap`, `OAI.Saxl.Balance.output`, `OAI.Saxl.Columns.Cells`, `OAI.Saxl.Columns.col`, `OAI.Saxl.Columns.columnTableau`, `OAI.Saxl.Columns.enumerate`, `OAI.Saxl.Columns.row`, `OAI.Saxl.Columns.toYoung`, `OAI.Saxl.SupportLE`, `OAI.Saxl.coindEval`, `OAI.Saxl.coindLift`, `OAI.Saxl.coindOuter`, `OAI.Saxl.coindTrans`, `OAI.Saxl.columnMove`, `OAI.Saxl.coordinateProjection`, `OAI.Saxl.cyclicProductMap`, `OAI.Saxl.externalTensor`, `OAI.Saxl.externalWordMap`, `OAI.Saxl.fiberGroup`, `OAI.Saxl.functionTensor`, `OAI.Saxl.intertwiningLiftSubrep`, `OAI.Saxl.intertwiningRangeEquiv` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `Saxl_BandFactorization`, `Saxl_BandOrbit`, `Saxl_Basic`, `Saxl_ColumnContraction`, `Saxl_CoordinateSector`, `Saxl_CyclicSector`, `Saxl_CyclicTensor`, `Saxl_Model`, `Saxl_PieriRestriction`, `Saxl_Polytabloid`, `Saxl_PositionSplit`, `Saxl_PositionTensor`, `Saxl_SpechtDuality`, `Saxl_SpechtSubmodule`, `Saxl_StaircaseTensor`, `Saxl_SupportSeparation`, `Saxl_TableauTransport`, `UniversalSquare_Balance_BalanceBlocks`, `UniversalSquare_Balance_BalanceColumns`, `UniversalSquare_Balance_BalanceGluing`, `UniversalSquare_Balance_BalancePacking`, `UniversalSquare_Balance_BalanceProduct`, `UniversalSquare_Balance_BalanceProjection`, `UniversalSquare_Balance_PackingSupport`, `UniversalSquare_Balance_WordPacking`, `UniversalSquare_Band_OutputBands`, `UniversalSquare_Band_TwoStrip`, `UniversalSquare_Capacity_NumericBands`, `UniversalSquare_Contraction_PairForms`, `UniversalSquare_Contraction_SquareDetection`, `UniversalSquare_Contraction_SymmetricPairs`, `UniversalSquare_Specht_CyclicRestriction`, `UniversalSquare_Specht_DualPolytabloid`, `UniversalSquare_Support_AttachmentTransfer`, `UniversalSquare_Support_CoindProduct`, `UniversalSquare_Support_Neighboring`, `UniversalSquare_Support_ProductInduction`, `UniversalSquare_Support_SupportTransport`, `UniversalSquare_Support_WordRelabel`.
--
--   **Imports.** It imports the published bundle `Def_UniversalTensorSquares`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ259US006` and `OAIQ259US007`; the statements `OAI.Saxl.Columns.two_path_cyclic_support_placed`, `OAI_Saxl_dominated_support`, `OAI.Saxl.dominated_support_uts` and `OAI.UniversalTensorSquare.packingPlan_pos`.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_UniversalTensorSquares

section
-- module Solutions.OAIQ259_US.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV

namespace Saxl

/- Coefficients of position tensors on an alphabet of size `d`. -/


def staircase (m : ℕ) : YoungDiagram where
  cells := ((Finset.range m) ×ˢ (Finset.range m)).filter (fun x => x.1 + x.2 < m)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hy ⊢
    exact ⟨⟨lt_of_le_of_lt hxy.1 hy.1.1, lt_of_le_of_lt hxy.2 hy.1.2⟩,
      lt_of_le_of_lt (Nat.add_le_add hxy.1 hxy.2) hy.2⟩


end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/


@[simp] theorem mem_staircase {m i j : ℕ} :
    (i, j) ∈ staircase m ↔ i + j < m := by
  change (i, j) ∈ ((Finset.range m) ×ˢ (Finset.range m)).filter
    (fun x => x.1 + x.2 < m) ↔ _
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

@[simp] theorem staircase_card_zero : (staircase 0).card = 0 := by
  simp [staircase, YoungDiagram.card]

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_Polytabloid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- A finite set is the unique maximizer of its strictly signed separator.
Used below for the Ferrers equality case in the Specht submodule theorem. -/
def signC {n : ℕ} : Equiv.Perm (Fin n) →* ℂ :=
  ((Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)).comp Equiv.Perm.sign

@[simp] lemma signC_def {n : ℕ} (g : Equiv.Perm (Fin n)) :
    signC g = (((Equiv.Perm.sign g) : ℤ) : ℂ) := rfl

@[simp] lemma signC_inv {n : ℕ} (g : Equiv.Perm (Fin n)) : signC g⁻¹ = signC g := by
  simp [signC_def, Equiv.Perm.sign_inv]

@[simp] lemma signC_mul_self {n : ℕ} (g : Equiv.Perm (Fin n)) : signC g * signC g = 1 := by
  calc signC g * signC g = signC (g⁻¹ * g) := by rw [map_mul, signC_inv]
       _ = 1 := by rw [inv_mul_cancel, map_one]

lemma wordRep_single {n d : ℕ} (g : Equiv.Perm (Fin n)) (a : Fin n → Fin d) :
    wordRep n d g (Pi.single a 1) = Pi.single (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) (1 : ℂ) := by
  classical
  ext b
  change (Pi.single a (1 : ℂ) : WordSpace n d) (b ∘ g) = _
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    have hh := congrFun h (g⁻¹ i)
    simpa using hh
  · intro h
    funext i
    have hh := congrFun h (g i)
    simpa using hh

/- Actual column antisymmetrizer on the word-coordinate module. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SpechtSubmodule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV

namespace Saxl

lemma mem_cyclic {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) : v ∈ cyclic ρ v := by
  change v ∈ Submodule.span ℂ _
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

lemma cyclic_le {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (P : Subrepresentation ρ) :
    cyclic ρ v ≤ P ↔ v ∈ P := by
  constructor
  · intro h
    exact h (mem_cyclic ρ v)
  · intro hv
    change Submodule.span ℂ _ ≤ P.toSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact P.apply_mem_toSubmodule g hv

/- The actual row-tabloid permutation module, embedded in the word space. -/

@[simp] lemma wordRep_star {n d : ℕ} (g : Equiv.Perm (Fin n)) (x : WordSpace n d) :
    star (wordRep n d g x) = wordRep n d g (star x) := rfl

def wordPerm (n d : ℕ) (g : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n → Fin d) where
  toFun a := a ∘ g
  invFun a := a ∘ (g⁻¹ : Equiv.Perm (Fin n))
  left_inv a := by ext i; simp
  right_inv a := by ext i; simp

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SpechtDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The ordinary bilinear coordinate pairing restricted to any invariant word subspace. -/
def wordMap {n d e : ℕ} (L : Fin d → Fin e → ℂ) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n e) where
  toLinearMap :=
    { toFun := fun x b => ∑ a, x a * ∏ i, L (a i) (b i)
      map_add' := by
        intro x y
        ext b
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext b
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
          RingHom.id_apply] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext b
    change (∑ a, x (a ∘ g) * ∏ i, L (a i) (b i)) =
      ∑ a, x a * ∏ i, L (a i) (b (g i))
    apply Eq.trans ?_ (Equiv.sum_comp (wordPerm n d g)
      (fun a => x a * ∏ i, L (a i) (b (g i))))
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [wordPerm]
    congr 1
    exact (Equiv.prod_comp g (fun i => L (a i) (b i))).symm

@[simp] lemma wordMap_single {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (a : Fin n → Fin d) (b : Fin n → Fin e) :
    wordMap L (Pi.single a 1) b = ∏ i, L (a i) (b i) := by
  classical
  simp [wordMap, Pi.single_apply]

/- A nonzero contraction with a real cyclic vector gives an actual nonzero
intertwiner into its cyclic representation. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_TableauTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A change of tableau enumeration only applies a position permutation. -/
def tableauMove {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) : Equiv.Perm (Fin n) :=
  s.trans t.symm

@[simp] lemma tableauMove_apply {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) (i : Fin n) :
    t (tableauMove s t i) = s i := by simp [tableauMove]

@[simp] lemma tableauMove_inv_apply {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) (i : Fin n) :
    s ((tableauMove s t)⁻¹ i) = t i := by simp [tableauMove, Equiv.Perm.inv_def]

def columnMove {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    columnGroup s ≃ columnGroup t where
  toFun h := ⟨tableauMove s t * h.val * (tableauMove s t)⁻¹, by
    intro i
    simp only [Equiv.Perm.mul_apply, tableauMove_apply]
    rw [h.property, tableauMove_inv_apply]⟩
  invFun h := ⟨(tableauMove s t)⁻¹ * h.val * tableauMove s t, by
    intro i
    simp only [Equiv.Perm.mul_apply, tableauMove_inv_apply]
    rw [h.property, tableauMove_apply]⟩
  left_inv h := by apply Subtype.ext; simp [mul_assoc]
  right_inv h := by apply Subtype.ext; simp [mul_assoc]

lemma rowWord_move {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    rowWord t = rowWord s ∘ ((tableauMove s t)⁻¹ : Equiv.Perm (Fin n)) := by
  funext i
  apply Fin.ext
  exact congrArg (fun c : μ.cells => c.val.1) (tableauMove_inv_apply s t i).symm

lemma polytabloid_move {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    polytabloid t = wordRep n (μ.colLen 0) (tableauMove s t) (polytabloid s) := by
  classical
  let := Fintype.ofFinite (columnGroup s)
  let := Fintype.ofFinite (columnGroup t)
  unfold polytabloid
  rw [map_sum]
  refine (Fintype.sum_equiv (columnMove s t).symm _ _ ?_)
  intro h
  let g := tableauMove s t
  change signC (h : Equiv.Perm (Fin n)) • wordRep n (μ.colLen 0) h.val (Pi.single (rowWord t) 1) =
    wordRep n (μ.colLen 0) g
      (signC ((columnMove s t).symm h).val •
        wordRep n (μ.colLen 0) ((columnMove s t).symm h).val (Pi.single (rowWord s) 1))
  have hs : signC ((columnMove s t).symm h).val = signC h.val := by
    change signC (g⁻¹ * h.val * g) = signC h.val
    rw [map_mul, map_mul, signC_inv]
    calc signC g * signC h.val * signC g = signC h.val * (signC g * signC g) := by ring
         _ = signC h.val := by rw [signC_mul_self, mul_one]
  rw [map_smul, hs]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul]
  change wordRep n (μ.colLen 0) h.val (Pi.single (rowWord t) 1) =
    wordRep n (μ.colLen 0) (g * (g⁻¹ * h.val * g)) (Pi.single (rowWord s) 1)
  have he : g * (g⁻¹ * h.val * g) = h.val * g := by group
  have hv : wordRep n (μ.colLen 0) g (Pi.single (rowWord s) 1) = Pi.single (rowWord t) 1 := by
    rw [wordRep_single, rowWord_move s t]
  rw [he, map_mul, Module.End.mul_apply, hv]

lemma polytabloid_mem_all {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    polytabloid t ∈ spechtSub s := by
  rw [polytabloid_move s t]
  exact (spechtSub s).apply_mem_toSubmodule _ (mem_cyclic _ _)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_StaircaseTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
def splitLeft {n d e : ℕ} (w : Fin n → Fin (d*e)) : Fin n → Fin d :=
  fun i => (finProdFinEquiv.symm (w i)).1

def splitRight {n d e : ℕ} (w : Fin n → Fin (d*e)) : Fin n → Fin e :=
  fun i => (finProdFinEquiv.symm (w i)).2

def mergeWords {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) : Fin n → Fin (d*e) :=
  fun i => finProdFinEquiv (a i, b i)

@[simp] lemma splitLeft_merge {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    splitLeft (mergeWords a b) = a := by ext i; simp [splitLeft, mergeWords]
@[simp] lemma splitRight_merge {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    splitRight (mergeWords a b) = b := by ext i; simp [splitRight, mergeWords]
@[simp] lemma merge_split {n d e : ℕ} (w : Fin n → Fin (d*e)) :
    mergeWords (splitLeft w) (splitRight w) = w := by
  funext i
  exact finProdFinEquiv.apply_symm_apply (w i)

def wordUncurry (n d e : ℕ) :
    ((Fin n → Fin e) → WordSpace n d) ≃ₗ[ℂ] WordSpace n (d*e) where
  toFun f w := f (splitRight w) (splitLeft w)
  invFun z b a := z (mergeWords a b)
  left_inv f := by ext b a; simp
  right_inv z := by ext w; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- Tensor regrouping by positions. -/
def wordTensor (n d e : ℕ) :
    WordSpace n d ⊗[ℂ] WordSpace n e ≃ₗ[ℂ] WordSpace n (d*e) :=
  TensorProduct.piScalarRight ℂ ℂ (WordSpace n d) (Fin n → Fin e) ≪≫ₗ wordUncurry n d e

@[simp] lemma wordTensor_tmul {n d e : ℕ} (x : WordSpace n d) (y : WordSpace n e)
    (w : Fin n → Fin (d*e)) :
    wordTensor n d e (x ⊗ₜ[ℂ] y) w = x (splitLeft w) * y (splitRight w) := by
  change y (splitRight w) • x (splitLeft w) = _
  exact mul_comm _ _

lemma wordTensor_equivariant {n d e : ℕ} (g : Equiv.Perm (Fin n))
    (z : WordSpace n d ⊗[ℂ] WordSpace n e) :
    wordTensor n d e (((wordRep n d).tprod (wordRep n e)) g z) =
      wordRep n (d*e) g (wordTensor n d e z) := by
  induction z using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    ext w
    change wordTensor n d e (wordRep n d g x ⊗ₜ[ℂ] wordRep n e g y) w = _
    change wordTensor n d e (wordRep n d g x ⊗ₜ[ℂ] wordRep n e g y) w =
      wordTensor n d e (x ⊗ₜ[ℂ] y) (w ∘ g)
    simp only [wordTensor_tmul]
    rfl

def wordTensorIntertwiner (n d e : ℕ) :
    Representation.IntertwiningMap ((wordRep n d).tprod (wordRep n e)) (wordRep n (d*e)) where
  toLinearMap := (wordTensor n d e).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    exact wordTensor_equivariant g z

end Saxl

namespace Saxl

/- Transposition is an honest permutation of the self-conjugate staircase. -/
def staircaseSwap (m : ℕ) : (staircase m).cells ≃ (staircase m).cells where
  toFun x := ⟨(x.val.2, x.val.1), by
    have h : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩
  invFun x := ⟨(x.val.2, x.val.1), by
    have h : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev stairTableau (m : ℕ) : Tableau (staircase m).card (staircase m) :=
  canonicalTableau (staircase m) rfl

def stairRowTableau (m : ℕ) : Tableau (staircase m).card (staircase m) :=
  (stairTableau m).trans (staircaseSwap m)

def staircaseWord (m : ℕ) : WordSpace (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0) :=
  wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairTableau m))

def staircaseCyclic (m : ℕ) : Subrepresentation
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)) :=
  cyclic (wordRep _ _) (staircaseWord m)

def spechtInclusion {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.IntertwiningMap (spechtRep t) (wordRep n (μ.colLen 0)) where
  toLinearMap := (spechtSub t).toSubmodule.subtype
  isIntertwining' _ := rfl

def staircaseTensorMap (m : ℕ) :
    Representation.IntertwiningMap ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m)))
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)) :=
  (wordTensorIntertwiner _ _ _).comp
    ((spechtInclusion (stairTableau m)).tensor (spechtInclusion (stairTableau m)))

lemma staircaseTensorMap_injective (m : ℕ) : Function.Injective (staircaseTensorMap m) := by
  apply (wordTensor _ _ _).injective.comp
  exact TensorProduct.map_injective_of_flat_flat _ _
    (spechtSub (stairTableau m)).toSubmodule.subtype_injective
    (spechtSub (stairTableau m)).toSubmodule.subtype_injective

lemma staircaseCyclic_le_tensorRange (m : ℕ) :
    staircaseCyclic m ≤ (staircaseTensorMap m).range := by
  apply (cyclic_le _ _ _).mpr
  refine ⟨(⟨polytabloid (stairRowTableau m), polytabloid_mem_all _ _⟩ : Specht (stairTableau m)) ⊗ₜ[ℂ]
    (⟨polytabloid (stairTableau m), mem_cyclic _ _⟩ : Specht (stairTableau m)), ?_⟩
  rfl

attribute [irreducible] staircaseTensorMap

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CoordinateSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/
def coordinateProjection {n d : ℕ} (P : (Fin n → Fin d) → Prop) :
    Module.End ℂ (WordSpace n d) := by
  classical
  exact {
    toFun := fun x a => if P a then x a else 0
    map_add' := by intros; funext a; by_cases h : P a <;> simp [h]
    map_smul' := by intros; funext a; by_cases h : P a <;> simp [h] }

@[simp] lemma coordinateProjection_apply {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (x : WordSpace n d) (a : Fin n → Fin d) [Decidable (P a)] :
    coordinateProjection P x a = if P a then x a else 0 := by
  classical
  by_cases h : P a <;> simp [coordinateProjection, h]

def sectorGroup {n : ℕ} (D : Fin n → Prop) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ i, D (g i) ↔ D i}
  one_mem' _ := Iff.rfl
  mul_mem' hg hh i := (hg _).trans (hh i)
  inv_mem' := by
    intro g hg i
    simpa using (hg (g⁻¹ i)).symm

/- The genuine unnormalized signed block alternation. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PositionSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl
/- The genuine product position permutation under a disjoint-set enumeration. -/
def sumPerm {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) : Equiv.Perm (Fin n) :=
  e.symm.permCongr (Equiv.sumCongr g h)

@[simp] lemma sumPerm_left {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) (i : Fin a) :
    sumPerm e g h (e.symm (Sum.inl i)) = e.symm (Sum.inl (g i)) := by
  simp [sumPerm, Equiv.permCongr_apply]

@[simp] lemma sumPerm_right {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) (i : Fin b) :
    sumPerm e g h (e.symm (Sum.inr i)) = e.symm (Sum.inr (h i)) := by
  simp [sumPerm, Equiv.permCongr_apply]

def leftWord {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) (w : Fin n → Fin d) : Fin a → Fin d :=
  fun i => w (e.symm (Sum.inl i))

def rightWord {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) (w : Fin n → Fin d) : Fin b → Fin d :=
  fun i => w (e.symm (Sum.inr i))

def positionProduct {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : WordSpace a d) (y : WordSpace b d) : WordSpace n d :=
  fun w => x (leftWord e w) * y (rightWord e w)



def fiberGroup {n : ℕ} {α : Type uAlpha} (f : Fin n → α) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ i, f (g i) = f i}
  one_mem' _ := rfl
  mul_mem' hg hh i := (hg _).trans (hh i)
  inv_mem' := by
    intro g hg i
    simpa using (hg (g⁻¹ i)).symm

def leftPositions {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Fin a ≃ {i : Fin n // (e i).isLeft = true} where
  toFun i := ⟨e.symm (Sum.inl i), by simp⟩
  invFun i := (e i.val).getLeft i.property
  left_inv i := by simp
  right_inv i := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Sum.inl_getLeft _ _

def rightPositions {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Fin b ≃ {i : Fin n // ¬(e i).isLeft = true} where
  toFun i := ⟨e.symm (Sum.inr i), by simp⟩
  invFun i := (e i.val).getRight (by
    have hi := i.property
    cases h : e i.val <;> simp_all)
  left_inv i := by simp
  right_inv i := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Sum.inr_getRight _ _

def leftRestriction {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) : Equiv.Perm (Fin a) :=
  (leftPositions e).symm.permCongr ((g : Equiv.Perm (Fin n)).subtypePerm g.property)

def rightRestriction {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) : Equiv.Perm (Fin b) :=
  (rightPositions e).symm.permCongr ((g : Equiv.Perm (Fin n)).subtypePerm (fun i => not_congr (g.property i)))

lemma leftRestriction_apply {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) (i : Fin a) :
    e.symm (Sum.inl (leftRestriction e g i)) = g.val (e.symm (Sum.inl i)) := by
  apply e.injective
  simp only [Equiv.apply_symm_apply]
  exact Sum.inl_getLeft _ _

lemma rightRestriction_apply {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) (i : Fin b) :
    e.symm (Sum.inr (rightRestriction e g i)) = g.val (e.symm (Sum.inr i)) := by
  apply e.injective
  simp only [Equiv.apply_symm_apply]
  exact Sum.inr_getRight _ _

lemma sumPerm_restrictions {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) :
    sumPerm e (leftRestriction e g) (rightRestriction e g) = g.val := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j => simpa using leftRestriction_apply e g j
  | inr j => simpa using rightRestriction_apply e g j


@[simp] lemma staircase_colLen (m j : ℕ) : (staircase m).colLen j = m-j := by
  have hh : ∀ i, i < (staircase m).colLen j ↔ i < m-j := by
    intro i
    rw [← YoungDiagram.mem_iff_lt_colLen, mem_staircase]
    omega
  have h₁ := hh ((staircase m).colLen j)
  have h₂ := hh (m-j)
  omega

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

def letterLift {n d e : ℕ} (f : Fin d → Fin e) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n e) :=
  wordMap (fun a b => if f a = b then 1 else 0)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_ColumnContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/
@[reducible] def Cells : List ℕ → Type
  | [] => Empty
  | r :: rs => Fin r ⊕ Cells rs

def row : {rs : List ℕ} → Cells rs → ℕ
  | _ :: _, .inl i => i.val
  | _ :: _, .inr c => row c

def col : {rs : List ℕ} → Cells rs → ℕ
  | _ :: _, .inl _ => 0
  | _ :: _, .inr c => col c + 1

def enumerate : (rs : List ℕ) → Fin rs.sum ≃ Cells rs
  | [] => (Equiv.equivOfIsEmpty (Fin 0) Empty)
  | r :: rs => finSumFinEquiv.symm.trans ((Equiv.refl (Fin r)).sumCongr (enumerate rs))

@[simp] lemma enumerate_left (r : ℕ) (rs : List ℕ) (i : Fin r) :
    enumerate (r :: rs) (Fin.castAdd rs.sum i) = Sum.inl i := by
  exact congrArg ((Equiv.refl (Fin r)).sumCongr (enumerate rs))
    (finSumFinEquiv_symm_apply_castAdd i)

@[simp] lemma enumerate_right (r : ℕ) (rs : List ℕ) (i : Fin rs.sum) :
    enumerate (r :: rs) (Fin.natAdd r i) = Sum.inr (enumerate rs i) := by
  exact congrArg ((Equiv.refl (Fin r)).sumCongr (enumerate rs))
    (finSumFinEquiv_symm_apply_natAdd i)

lemma coords_injective (rs : List ℕ) :
    Function.Injective (fun c : Cells rs => (row c, col c)) := by
  induction rs with
  | nil => exact Function.injective_of_subsingleton _
  | cons r rs ih =>
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Fin.ext (congrArg Prod.fst h))
      | inr b => have := congrArg Prod.snd h; simp [col] at this
    | inr a =>
      cases b with
      | inl b => have := congrArg Prod.snd h; simp [col] at this
      | inr b =>
        apply congrArg Sum.inr
        apply ih
        dsimp only [row, col] at h
        have hr := congrArg Prod.fst h
        have hc := congrArg Prod.snd h
        exact Prod.ext hr (Nat.add_right_cancel hc)

lemma coords_range (rs : List ℕ) (i j : ℕ) :
    (∃ c : Cells rs, row c = i ∧ col c = j) ↔ ∃ h : j < rs.length, i < rs[j] := by
  induction rs generalizing j with
  | nil => simp [Cells]
  | cons r rs ih =>
    cases j with
    | zero =>
      constructor
      · rintro ⟨c, hr, hc⟩
        cases c with
        | inl a => exact ⟨by simp, by simpa [row] using hr ▸ a.isLt⟩
        | inr a => simp [col] at hc
      · rintro ⟨h, hi⟩
        exact ⟨Sum.inl ⟨i, hi⟩, rfl, rfl⟩
    | succ j =>
      constructor
      · rintro ⟨c, hr, hc⟩
        cases c with
        | inl a => simp [col] at hc
        | inr a =>
          have hj : col a = j := Nat.add_right_cancel hc
          obtain ⟨hj, hi⟩ := (ih j).mp ⟨a, hr, hj⟩
          exact ⟨Nat.succ_lt_succ hj, hi⟩
      · rintro ⟨h, hi⟩
        obtain ⟨a, ha, hc⟩ := (ih j).mpr ⟨Nat.lt_of_succ_lt_succ h, hi⟩
        exact ⟨Sum.inr a, ha, congrArg (· + 1) hc⟩

/- The matrix product indexed by the actual consecutive position order. -/
def toYoung (μ : YoungDiagram) : Cells μ.transpose.rowLens ≃ μ.cells := by
  let f : Cells μ.transpose.rowLens → μ.cells := fun c =>
    ⟨(row c, col c), by
      obtain ⟨hj, hi⟩ := (coords_range μ.transpose.rowLens (row c) (col c)).mp ⟨c, rfl, rfl⟩
      simpa only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen,
        YoungDiagram.get_rowLens, YoungDiagram.rowLen_transpose] using hi⟩
  exact Equiv.ofBijective f ⟨fun _ _ h => coords_injective _ (congrArg Subtype.val h), by
    intro c
    have hmem : c.val.1 < μ.colLen c.val.2 := YoungDiagram.mem_iff_lt_colLen.mp c.property
    have hj : c.val.2 < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp
      (μ.up_left_mem (Nat.zero_le _) le_rfl c.property)
    have hj' : c.val.2 < μ.transpose.rowLens.length := by simpa using hj
    obtain ⟨a, ha, hb⟩ := (coords_range μ.transpose.rowLens c.val.1 c.val.2).mpr
      ⟨hj', by simpa using hmem⟩
    exact ⟨a, Subtype.ext (Prod.ext ha hb)⟩⟩

@[simp] lemma toYoung_val (μ : YoungDiagram) (c : Cells μ.transpose.rowLens) :
    (toYoung μ c).val = (row c, col c) := rfl


def columnTableau (μ : YoungDiagram) : Tableau μ.transpose.rowLens.sum μ :=
  (enumerate μ.transpose.rowLens).trans (toYoung μ)

@[simp] lemma columnTableau_val (μ : YoungDiagram) (i : Fin μ.transpose.rowLens.sum) :
    (columnTableau μ i).val = (row (enumerate μ.transpose.rowLens i),
      col (enumerate μ.transpose.rowLens i)) := rfl

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

/- Explicit finite-group induction on a linear map. -/

open scoped MonoidAlgebra

theorem intertwining_lift_surjective {G : Type uG} {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (hF : Function.Surjective F)
    (f : Representation.IntertwiningMap τ σ) :
    ∃ h : Representation.IntertwiningMap τ ρ, F.comp h = f := by
  let EF := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
  let EH := Representation.IntertwiningMap.equivLinearMapAsModule τ ρ
  let Ef := Representation.IntertwiningMap.equivLinearMapAsModule τ σ
  obtain ⟨h, hh⟩ := IsSemisimpleModule.lifting_property (EF F) hF (Ef f)
  refine ⟨EH.symm h, ?_⟩
  ext z
  exact LinearMap.congr_fun hh z

end Saxl

namespace Saxl

lemma intertwiner_cyclic_mem {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (v : X) (x : X) (hx : x ∈ cyclic ρ v) :
    F x ∈ cyclic σ (F v) := by
  change x ∈ Submodule.span ℂ _ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    change F (ρ g v) ∈ _
    have hF : F (ρ g v) = σ g (F v) := LinearMap.congr_fun (F.isIntertwining' g) v
    rw [hF]
    exact (cyclic σ (F v)).apply_mem_toSubmodule g (mem_cyclic _ _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SupportSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uR uX uY uG uV

namespace Saxl
open scoped MonoidAlgebra

/- In a semisimple module, support containment is equivalent to separation
by homomorphisms (multiplicities are immaterial for the band step). -/
theorem hom_separates_of_simple_support {R : Type uR} {X : Type uX} {Y : Type uY} [Ring R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [IsSemisimpleModule R X]
    (h : ∀ S : Submodule R X, IsSimpleModule R S →
      ∃ f : S →ₗ[R] Y, f ≠ 0) (x : X) (hx : x ≠ 0) :
    ∃ f : X →ₗ[R] Y, f x ≠ 0 := by
  classical
  let K : Submodule R X := ⨅ f : X →ₗ[R] Y, LinearMap.ker f
  have hK : K = ⊥ := by
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le K with hk | ⟨S, hS, hs⟩
    · exact hk
    obtain ⟨f, hf⟩ := h S hs
    obtain ⟨F, hF⟩ := IsSemisimpleModule.extension_property S.subtype S.subtype_injective f
    exfalso
    apply hf
    ext s
    have hm : s.val ∈ K := hS s.property
    have he : F s.val = 0 := ((Submodule.mem_iInf _).mp hm F)
    change f s = 0
    exact (LinearMap.congr_fun hF s).symm.trans he
  by_contra hf
  push Not at hf
  apply hx
  have hm : x ∈ K := (Submodule.mem_iInf _).mpr (fun f => hf f)
  simpa only [hK, Submodule.mem_bot] using hm

end Saxl

namespace Saxl
open scoped MonoidAlgebra

/- The invariant-subspace and group-algebra subtype constructions agree. -/
def subrepModuleEquiv {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    S.toRepresentation.asModule ≃ₗ[ℂ[G]] S.asSubmodule where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change (⟨(a • x).val, _⟩ : S.asSubmodule) = a • ⟨x.val, x.property⟩
    apply Subtype.ext
    change (a • x).val = ρ.asModuleEquiv (a • ρ.asModuleEquiv.symm x.val)
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp only [zero_smul, map_zero]; rfl
    | add a b ha hb =>
      simp only [add_smul, map_add]
      change (a • x).val + (b • x).val = _
      rw [ha, hb]
    | single g c =>
      rw [Representation.single_smul, Representation.single_smul]
      rfl

lemma subrep_irreducible_of_simple {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Submodule ℂ[G] ρ.asModule)
    [IsSimpleModule ℂ[G] S] :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' S).toRepresentation := by
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  let e : (Subrepresentation.ofSubmodule' S).toRepresentation.asModule ≃ₗ[ℂ[G]] S :=
    subrepModuleEquiv (Subrepresentation.ofSubmodule' S)
  exact IsSimpleModule.congr e

end Saxl

namespace Saxl

def subrepInclusion {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    Representation.IntertwiningMap S.toRepresentation ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

/- All constituents needed from a d-letter permutation module are detected
by a module containing each Specht type of height at most d. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PositionTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Concatenation of words on independent position blocks. -/
def joinPositions {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : Fin a → Fin d) (y : Fin b → Fin d) : Fin n → Fin d :=
  fun i => Sum.elim x y (e i)

@[simp] lemma leftWord_join {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : Fin a → Fin d) (y : Fin b → Fin d) : leftWord e (joinPositions e x y) = x := by
  funext i
  simp [leftWord, joinPositions]

@[simp] lemma rightWord_join {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : Fin a → Fin d) (y : Fin b → Fin d) : rightWord e (joinPositions e x y) = y := by
  funext i
  simp [rightWord, joinPositions]

@[simp] lemma joinPositions_parts {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w : Fin n → Fin d) : joinPositions e (leftWord e w) (rightWord e w) = w := by
  funext i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j <;> simp [joinPositions,leftWord,rightWord]

def positionUncurry {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    ((Fin b → Fin d) → WordSpace a d) ≃ₗ[ℂ] WordSpace n d where
  toFun f w := f (rightWord e w) (leftWord e w)
  invFun z y x := z (joinPositions e x y)
  left_inv f := by ext y x; simp
  right_inv z := by ext w; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def positionTensor {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    WordSpace a d ⊗[ℂ] WordSpace b d ≃ₗ[ℂ] WordSpace n d :=
  TensorProduct.piScalarRight ℂ ℂ (WordSpace a d) (Fin b → Fin d) ≪≫ₗ positionUncurry e

@[simp] lemma positionTensor_tmul {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : WordSpace a d) (y : WordSpace b d) :
    positionTensor e (x ⊗ₜ[ℂ] y) = positionProduct e x y := by
  funext w
  change y (rightWord e w) * x (leftWord e w) = _
  exact mul_comm _ _

lemma positionProduct_equivariant {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b))
    (x : WordSpace a d) (y : WordSpace b d) :
    wordRep n d (sumPerm e g h) (positionProduct e x y) =
      positionProduct e (wordRep a d g x) (wordRep b d h y) := by
  funext w
  change x (leftWord e (w ∘ sumPerm e g h)) * y (rightWord e (w ∘ sumPerm e g h)) = _
  have hl : leftWord e (w ∘ sumPerm e g h) = leftWord e w ∘ g := by
    funext i
    simp [leftWord]
  have hr : rightWord e (w ∘ sumPerm e g h) = rightWord e w ∘ h := by
    funext i
    simp [rightWord]
  rw [hl,hr]
  rfl

lemma product_mem_cyclic {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (u : WordSpace b d)
    (x : WordSpace a d) (y : WordSpace b d)
    (hx : x ∈ cyclic (wordRep a d) v) (hy : y ∈ cyclic (wordRep b d) u) :
    positionProduct e x y ∈ cyclic (wordRep n d) (positionProduct e v u) := by
  let S := cyclic (wordRep n d) (positionProduct e v u)
  change x ∈ Submodule.span ℂ _ at hx
  change y ∈ Submodule.span ℂ _ at hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h,rfl⟩ := hy
      rw [← positionProduct_equivariant]
      exact S.apply_mem_toSubmodule (sumPerm e g h) (mem_cyclic _ _)
    | zero =>
      have hz : positionProduct e (wordRep a d g v) 0 = 0 := by ext; simp [positionProduct]
      rw [hz]
      exact S.toSubmodule.zero_mem
    | add y z hy hz ihy ihz =>
      have he : positionProduct e (wordRep a d g v) (y+z) =
          positionProduct e (wordRep a d g v) y + positionProduct e (wordRep a d g v) z := by
        ext; simp [positionProduct,mul_add]
      rw [he]
      exact S.toSubmodule.add_mem ihy ihz
    | smul c y hy ih =>
      have he : positionProduct e (wordRep a d g v) (c • y) =
          c • positionProduct e (wordRep a d g v) y := by ext; simp [positionProduct,mul_left_comm]
      rw [he]
      exact S.toSubmodule.smul_mem c ih
  | zero =>
    have hz : positionProduct e 0 y = 0 := by ext; simp [positionProduct]
    rw [hz]
    exact S.toSubmodule.zero_mem
  | add x z hx hz ihx ihz =>
    have he : positionProduct e (x+z) y = positionProduct e x y + positionProduct e z y := by
      ext; simp [positionProduct,add_mul]
    rw [he]
    exact S.toSubmodule.add_mem ihx ihz
  | smul c x hx ih =>
    have he : positionProduct e (c • x) y = c • positionProduct e x y := by
      ext; simp [positionProduct,mul_assoc]
    rw [he]
    exact S.toSubmodule.smul_mem c ih

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

@[simp] lemma sumPerm_mul {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g g' : Equiv.Perm (Fin a)) (h h' : Equiv.Perm (Fin b)) :
    sumPerm e (g*g') (h*h') = sumPerm e g h * sumPerm e g' h' := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j <;> simp only [sumPerm_left, sumPerm_right, Equiv.Perm.mul_apply]

@[simp] lemma sumPerm_one {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    sumPerm e 1 1 = 1 := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j <;> simp only [sumPerm_left,sumPerm_right,Equiv.Perm.one_apply]

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PieriRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A horizontal strip removes at most one cell in each column. -/
def tableauInclusion {a n : ℕ} {ν μ : YoungDiagram} (s : Tableau a ν) (t : Tableau n μ)
    (h : ν ≤ μ) : Fin a ↪ Fin n where
  toFun i := t.symm ⟨(s i).val, h (s i).property⟩
  inj' := by
    intro i j hij
    apply s.injective
    apply Subtype.ext
    simpa using congrArg (fun k => (t k).val) hij


@[simp] lemma tableauInclusion_cell {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (h : ν ≤ μ) (k : Fin a) :
    (t (tableauInclusion s t h k)).val = (s k).val := by
  change (t (t.symm ⟨(s k).val, h (s k).property⟩)).val = _
  simp

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY

namespace Saxl



def intertwiningRangeEquiv {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f) :
    ρ.Equiv f.range.toRepresentation where
  toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap hf
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (f.isIntertwining' g) x

def intertwiningLiftSubrep {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f)
    (S : Subrepresentation σ) (hS : S ≤ f.range) :
    Representation.IntertwiningMap S.toRepresentation ρ := by
  let e : ρ.Equiv f.range.toRepresentation := intertwiningRangeEquiv f hf
  let i : Representation.IntertwiningMap S.toRepresentation f.range.toRepresentation :=
    { toLinearMap := Submodule.inclusion hS, isIntertwining' := fun _ => rfl }
  exact e.symm.toIntertwiningMap.comp i

attribute [irreducible] intertwiningLiftSubrep

/- The genuine cyclic module is embedded in the actual staircase Specht square. -/
def staircaseToTensor (m : ℕ) :
    Representation.IntertwiningMap (staircaseCyclic m).toRepresentation
      ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m))) :=
  @intertwiningLiftSubrep (Equiv.Perm (Fin (staircase m).card))
    (Specht (stairTableau m) ⊗[ℂ] Specht (stairTableau m))
    (WordSpace (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0))
    _ _ _ _ _
    ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m)))
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0))
    (staircaseTensorMap m) (staircaseTensorMap_injective m)
    (staircaseCyclic m) (staircaseCyclic_le_tensorRange m)

attribute [irreducible] staircaseToTensor

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SquareDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def spechtTensorMap {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) :
    Representation.IntertwiningMap ((spechtRep a).tprod (spechtRep b))
      (wordRep n (α.colLen 0 * β.colLen 0)) :=
  (wordTensorIntertwiner _ _ _).comp ((spechtInclusion a).tensor (spechtInclusion b))

attribute [irreducible] spechtTensorMap

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_DualPolytabloid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual Polytabloid. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl
open scoped MonoidAlgebra

theorem intertwining_extend_injective {G X Y Z : Type*}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (hF : Function.Injective F)
    (f : Representation.IntertwiningMap ρ τ) :
    ∃ h : Representation.IntertwiningMap σ τ, h.comp F = f := by
  let EF := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
  let EH := Representation.IntertwiningMap.equivLinearMapAsModule σ τ
  let Ef := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ
  obtain ⟨h, hh⟩ := IsSemisimpleModule.extension_property (EF F) hF (Ef f)
  refine ⟨EH.symm h, ?_⟩
  ext z
  exact LinearMap.congr_fun hh z

lemma cyclic_zero_mem_iff {G X : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (x : X) : x ∈ cyclic ρ 0 ↔ x = 0 := by
  change x ∈ Submodule.span ℂ (Set.range fun g : G => ρ g 0) ↔ _
  simp

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SymmetricPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def positionWordsEquiv {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    (Fin n → Fin d) ≃ (Fin a → Fin d) × (Fin b → Fin d) where
  toFun w := (leftWord e w, rightWord e w)
  invFun p := joinPositions e p.1 p.2
  left_inv := joinPositions_parts e
  right_inv p := by simp

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_PairForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Forms. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def pairWordsEquiv {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) :
    (Fin n → Fin d) ≃ (Fin m → Fin d × Fin d) :=
  (positionWordsEquiv e).trans
    (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Fin d) (fun _ => Fin d)).symm

@[simp] lemma pairWordsEquiv_apply {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (w : Fin n → Fin d) (i : Fin m) :
    pairWordsEquiv e w i = (leftWord e w i, rightWord e w i) := rfl

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_AttachmentTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Attachment Transfer. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl

theorem subrepresentation_embeds_of_le_range {G X Y : Type*}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (S : Subrepresentation σ) (hS : S ≤ F.range) :
    ∃ f : Representation.IntertwiningMap S.toRepresentation ρ, Function.Injective f := by
  let Q : Representation.IntertwiningMap ρ F.range.toRepresentation :=
    { toLinearMap := F.toLinearMap.rangeRestrict
      isIntertwining' := by
        intro g
        ext x
        exact LinearMap.congr_fun (F.isIntertwining' g) x }
  have hQ : Function.Surjective Q := by
    rintro ⟨y, x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  let I : Representation.IntertwiningMap S.toRepresentation F.range.toRepresentation :=
    { toLinearMap := S.toSubmodule.inclusion hS
      isIntertwining' := fun _ => rfl }
  obtain ⟨f,hf⟩ := intertwining_lift_surjective Q hQ I
  refine ⟨f, ?_⟩
  intro x y he
  apply Subtype.ext
  have hx := congrArg (fun H => (H x).val) hf
  have hy := congrArg (fun H => (H y).val) hf
  change (Q (f x)).val = x.val at hx
  change (Q (f y)).val = y.val at hy
  exact hx.symm.trans ((congrArg (fun z => (Q z).val) he).trans hy)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Projection. -/

section

noncomputable section
namespace Saxl.Balance

def FixedComponentSums {n d : ℕ} (c : Fin n → ℕ) (z : Fin d → ℤ)
    (σ : ℕ → ℤ) (x : WordSpace n d) : Prop :=
  ∀ w, x w ≠ 0 → ∀ k, ∑ i ∈ Finset.univ.filter (fun i => c i = k), z (w i) = σ k

def componentWords {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (w : Fin n → Fin d) : Prop :=
  (∀ i, A (w i)) ∧ ∀ i, label (w i) = c i

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_Neighboring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Neighboring. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl
namespace Balance

def output {d e : ℕ} (a : Fin (d*e)) : ℕ :=
  ((finProdFinEquiv : Fin d × Fin e ≃ Fin (d*e)).symm a).1.val +
  ((finProdFinEquiv : Fin d × Fin e ≃ Fin (d*e)).symm a).2.val + 1

end Balance
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Columns. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl.Balance

def fixedSumSpace {n d : ℕ} (c : Fin n → ℕ) (z : Fin d → ℤ)
    (σ : ℕ → ℤ) : Submodule ℂ (WordSpace n d) where
  carrier := {x | FixedComponentSums c z σ x}
  zero_mem' := by intro w h; exact False.elim (h rfl)
  add_mem' := by
    intro x y hx hy w hw
    by_cases hh : x w = 0
    · exact hy w (by intro hz; apply hw; simp [hh,hz])
    · exact hx w hh
  smul_mem' := by
    intro a x hx w hw
    exact hx w (by intro hz; apply hw; simp [hz])

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_CyclicRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cyclic Restriction. -/

section

noncomputable section
namespace Saxl

theorem intertwining_reverse_nonzero {G X Y : Type*}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (hF : F ≠ 0) :
    ∃ T : Representation.IntertwiningMap σ ρ, T ≠ 0 := by
  obtain ⟨S,hS⟩ := subrepresentation_embeds_of_le_range F F.range le_rfl
  obtain ⟨T,hT⟩ := intertwining_extend_injective (subrepInclusion F.range)
    Subtype.val_injective S
  refine ⟨T, ?_⟩
  intro h0
  apply hF
  ext x
  have he := congrArg (fun H : Representation.IntertwiningMap F.range.toRepresentation ρ =>
    H ⟨F x, x, rfl⟩) hT
  change T (F x) = S ⟨F x, x, rfl⟩ at he
  rw [h0] at he
  have hh : S ⟨F x, x, rfl⟩ = S 0 := by simpa using he.symm
  exact congrArg Subtype.val (hS hh)

def intertwiningRestrict {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (φ : H →* G) (F : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap (ρ.comp φ) (σ.comp φ) where
  toLinearMap := F.toLinearMap
  isIntertwining' h := F.isIntertwining' (φ h)

theorem cyclic_restriction_support {G H X Y Z : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ G X) [ρ.IsIrreducible]
    (σ : Representation ℂ H Y) (τ : Representation ℂ G Z)
    (φ : H →* G) (u : Z)
    (T : Representation.IntertwiningMap σ (τ.comp φ)) (hu : u ∈ T.range)
    (F : Representation.IntertwiningMap ρ (cyclic τ u).toRepresentation)
    (hF : F ≠ 0) :
    ∃ Q : Representation.IntertwiningMap (ρ.comp φ) σ, Q ≠ 0 := by
  let E := (subrepInclusion (cyclic τ u)).comp F
  have hEi : Function.Injective E := Subtype.val_injective.comp
    ((Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF)
  obtain ⟨R,hR⟩ := intertwining_extend_injective E hEi
    (Representation.IntertwiningMap.id ρ)
  have hRu : R u ≠ 0 := by
    intro h0
    apply hF
    ext x
    have hm := intertwiner_cyclic_mem R u (E x) (F x).property
    rw [h0, cyclic_zero_mem_iff] at hm
    have he := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hR
    change R (E x) = x at he
    rw [he] at hm
    rw [hm, map_zero]
    rfl
  let P := (intertwiningRestrict φ R).comp T
  have hP : P ≠ 0 := by
    obtain ⟨v,hv⟩ := hu
    change T v = u at hv
    intro h0
    apply hRu
    have he := congrArg (fun f : Representation.IntertwiningMap σ (ρ.comp φ) => f v) h0
    change R (T v) = 0 at he
    rwa [hv] at he
  exact intertwining_reverse_nonzero P hP

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SupportTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support Transport. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def SupportLE {G X Y : Type*} [Group G]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) : Prop :=
  ∀ x : X, x ≠ 0 → ∃ f : Representation.IntertwiningMap ρ σ, f x ≠ 0

namespace SupportLE
variable {G H X Y Z : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    [AddCommMonoid Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}

lemma trans (h₁ : SupportLE ρ σ) (h₂ : SupportLE σ τ) : SupportLE ρ τ := by
  intro x hx
  obtain ⟨f,hf⟩ := h₁ x hx
  obtain ⟨g,hg⟩ := h₂ (f x) hf
  exact ⟨g.comp f,hg⟩

lemma of_injective (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f) :
    SupportLE ρ σ := by
  intro x hx
  exact ⟨f,fun he => hx (hf (he.trans (map_zero f).symm))⟩

lemma coind (φ : G →* H) (h : SupportLE ρ σ) :
    SupportLE (Representation.coind φ ρ) (Representation.coind φ σ) := by
  intro x hx
  have hn : ∃ g, x.val g ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hx (Subtype.ext (funext hh))
  obtain ⟨g,hg⟩ := hn
  obtain ⟨f,hf⟩ := h (x.val g) hg
  refine ⟨Representation.coindMap φ f,?_⟩
  intro hz
  exact hf (congrArg (fun y : Representation.coindV φ σ => y.val g) hz)

end SupportLE

def outer {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ H Y) :
    Representation ℂ (G × H) (X ⊗[ℂ] Y) where
  toFun g := TensorProduct.map (ρ g.1) (σ g.2)
  map_one' := by ext x y; simp
  map_mul' g h := by ext x y; simp

def outerMap {G H X Y U V : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    [AddCommMonoid U] [Module ℂ U] [AddCommMonoid V] [Module ℂ V]
    {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    {τ : Representation ℂ G U} {υ : Representation ℂ H V}
    (f : Representation.IntertwiningMap ρ τ) (g : Representation.IntertwiningMap σ υ) :
    Representation.IntertwiningMap (outer ρ σ) (outer τ υ) where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  isIntertwining' h := by
    ext x y
    change f (ρ h.1 x) ⊗ₜ[ℂ] g (σ h.2 y) = τ h.1 (f x) ⊗ₜ[ℂ] υ h.2 (g y)
    rw [f.isIntertwining,g.isIntertwining]

def rightSlice {X Y : Type*} [AddCommMonoid X] [Module ℂ X]
    [AddCommMonoid Y] [Module ℂ Y] (l : Module.Dual ℂ Y) : X ⊗[ℂ] Y →ₗ[ℂ] X :=
  (TensorProduct.rid ℂ X).toLinearMap.comp (TensorProduct.map LinearMap.id l)

@[simp] lemma rightSlice_tmul {X Y : Type*} [AddCommMonoid X] [Module ℂ X]
    [AddCommMonoid Y] [Module ℂ Y] (l : Module.Dual ℂ Y) (x : X) (y : Y) :
    rightSlice l (x ⊗ₜ[ℂ] y) = l y • x := rfl

lemma rightSlice_map {X Y U V : Type*}
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    [AddCommMonoid U] [Module ℂ U] [AddCommMonoid V] [Module ℂ V]
    (f : X →ₗ[ℂ] U) (g : Y →ₗ[ℂ] V) (l : Module.Dual ℂ V)
    (z : X ⊗[ℂ] Y) :
    rightSlice l (TensorProduct.map f g z) = f (rightSlice (l.comp g) z) := by
  induction z using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => simp

lemma exists_rightSlice {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (z : X ⊗[ℂ] Y) (hz : z ≠ 0) :
    ∃ l : Module.Dual ℂ Y, rightSlice l z ≠ 0 := by
  let E := (TensorProduct.comm ℂ X Y).trans
    ((TensorProduct.congr (Module.evalEquiv ℂ Y) (LinearEquiv.refl ℂ X)).trans
      (dualTensorHomEquiv ℂ (Module.Dual ℂ Y) X))
  have he (z : X ⊗[ℂ] Y) (l : Module.Dual ℂ Y) : E z l = rightSlice l z := by
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy]
    | tmul x y => rfl
  by_contra hh
  push Not at hh
  have hez : E z = 0 := LinearMap.ext (fun l => (he z l).trans (hh l))
  exact hz (E.injective (hez.trans (map_zero E).symm))

theorem SupportLE.outer {G H X Y U V : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ Y] [FiniteDimensional ℂ U]
    {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    {τ : Representation ℂ G U} {υ : Representation ℂ H V}
    (h₁ : SupportLE ρ τ) (h₂ : SupportLE σ υ) :
    SupportLE (outer ρ σ) (outer τ υ) := by
  intro z hz
  obtain ⟨l,hl⟩ := exists_rightSlice z hz
  obtain ⟨f,hf⟩ := h₁ (rightSlice l z) hl
  let w := TensorProduct.map f.toLinearMap (LinearMap.id : Y →ₗ[ℂ] Y) z
  have hw : w ≠ 0 := by
    intro hh
    have he := rightSlice_map f.toLinearMap (LinearMap.id : Y →ₗ[ℂ] Y) l z
    rw [show TensorProduct.map f.toLinearMap (LinearMap.id : Y →ₗ[ℂ] Y) z = w from rfl,
      hh,map_zero] at he
    exact hf he.symm
  obtain ⟨k,hk⟩ := exists_rightSlice ((TensorProduct.comm ℂ U Y) w)
    (fun he => hw ((TensorProduct.comm ℂ U Y).injective (he.trans (map_zero _).symm)))
  obtain ⟨g,hg⟩ := h₂ (rightSlice k ((TensorProduct.comm ℂ U Y) w)) hk
  refine ⟨outerMap f g,?_⟩
  intro hh
  have he : rightSlice k ((TensorProduct.comm ℂ U V) (outerMap f g z)) =
      g (rightSlice k ((TensorProduct.comm ℂ U Y) w)) := by
    have ht : (rightSlice k).comp ((TensorProduct.comm ℂ U V).toLinearMap.comp
        (outerMap f g).toLinearMap) = g.toLinearMap.comp ((rightSlice k).comp
          ((TensorProduct.comm ℂ U Y).toLinearMap.comp
            (TensorProduct.map f.toLinearMap (LinearMap.id : Y →ₗ[ℂ] Y)))) := by
      ext x y
      change k (f x) • g y = g (k (f x) • y)
      rw [map_smul]
    exact LinearMap.congr_fun ht z
  rw [hh,map_zero,map_zero] at he
  exact hg he.symm

end Saxl

namespace Saxl

def coindLift {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap (ρ.comp φ) σ) :
    Representation.IntertwiningMap ρ (Representation.coind φ σ) where
  toLinearMap := {
    toFun x := ⟨fun g => f (ρ g x), fun h g => by
      change f (ρ (φ h*g) x) = σ h (f (ρ g x))
      rw [map_mul,Module.End.mul_apply]
      exact LinearMap.congr_fun (f.isIntertwining' h) (ρ g x)⟩
    map_add' x y := by ext g; simp
    map_smul' a x := by ext g; simp }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext h
    change f (ρ h (ρ g x)) = f (ρ (h*g) x)
    rw [map_mul,Module.End.mul_apply]

def coindEval {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap ρ (Representation.coind φ σ)) :
    Representation.IntertwiningMap (ρ.comp φ) σ where
  toLinearMap := {
    toFun x := (f x).val 1
    map_add' x y := by simp
    map_smul' a x := by simp }
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    change (f (ρ (φ h) x)).val 1 = σ h ((f x).val 1)
    rw [f.isIntertwining]
    change (f x).val (1*φ h) = σ h ((f x).val 1)
    simpa only [one_mul,mul_one] using (f x).property h 1

@[simp] lemma coindEval_lift {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap (ρ.comp φ) σ) :
    coindEval φ (coindLift φ f) = f := by
  ext x
  change f (ρ 1 x) = f x
  rw [map_one]
  rfl

@[simp] lemma coindLift_eval {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap ρ (Representation.coind φ σ)) :
    coindLift φ (coindEval φ f) = f := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext g
  change (f (ρ g x)).val 1 = (f x).val g
  rw [f.isIntertwining]
  change (f x).val (1*g) = (f x).val g
  rw [one_mul]

lemma coindLift_ne_zero {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap (ρ.comp φ) σ) (hf : f ≠ 0) :
    coindLift φ f ≠ 0 := by
  intro hz
  apply hf
  rw [← coindEval_lift φ f,hz]
  rfl

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CoindProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coind Product. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def functionTensor {G H X Y : Type*} [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y] :
    (G → X) ⊗[ℂ] (H → Y) ≃ₗ[ℂ] (G × H → X ⊗[ℂ] Y) :=
  (TensorProduct.piLeft ℂ (H → Y) (fun _ : G => X)).trans
    ((LinearEquiv.piCongrRight (fun _ : G =>
      TensorProduct.piRight ℂ ℂ X (fun _ : H => Y))).trans
      { toFun := fun f g => f g.1 g.2
        invFun := fun f g h => f (g,h)
        left_inv := by intro f; rfl
        right_inv := by intro f; rfl
        map_add' := by intros; rfl
        map_smul' := by intros; rfl })

@[simp] lemma functionTensor_tmul {G H X Y : Type*} [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (f : G → X) (g : H → Y) (h : G × H) :
    functionTensor (f ⊗ₜ[ℂ] g) h = f h.1 ⊗ₜ[ℂ] g h.2 := rfl

def coindOuter {G H K L X Y : Type*} [Group G] [Group H] [Group K] [Group L]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : K →* G) (ψ : L →* H)
    (ρ : Representation ℂ K X) (σ : Representation ℂ L Y) :
    Representation.IntertwiningMap
      (outer (Representation.coind φ ρ) (Representation.coind ψ σ))
      (Representation.coind (φ.prodMap ψ) (outer ρ σ)) where
  toLinearMap :=
    ((functionTensor).toLinearMap.comp
      (TensorProduct.map (Representation.coindV φ ρ).subtype
        (Representation.coindV ψ σ).subtype)).codRestrict _ (by
      intro z
      induction z using OAI.tensorInductionOn with
      | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
      | tmul a b =>
        intro k g
        change a.val (φ k.1 * g.1) ⊗ₜ[ℂ] b.val (ψ k.2 * g.2) =
          TensorProduct.map (ρ k.1) (σ k.2) (a.val g.1 ⊗ₜ[ℂ] b.val g.2)
        rw [a.property,b.property,TensorProduct.map_tmul])
  isIntertwining' g := by
    ext a b h
    rfl

@[simp] lemma coindOuter_tmul {G H K L X Y : Type*}
    [Group G] [Group H] [Group K] [Group L]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : K →* G) (ψ : L →* H)
    (ρ : Representation ℂ K X) (σ : Representation ℂ L Y)
    (a : Representation.coindV φ ρ) (b : Representation.coindV ψ σ) (g : G × H) :
    (coindOuter φ ψ ρ σ (a ⊗ₜ[ℂ] b)).val g = a.val g.1 ⊗ₜ[ℂ] b.val g.2 := rfl

lemma coindOuter_injective {G H K L X Y : Type*}
    [Group G] [Group H] [Group K] [Group L]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : K →* G) (ψ : L →* H)
    (ρ : Representation ℂ K X) (σ : Representation ℂ L Y) :
    Function.Injective (coindOuter φ ψ ρ σ) := by
  intro a b h
  exact (TensorProduct.map_injective_of_flat_flat _ _
    (Representation.coindV φ ρ).injective_subtype
    (Representation.coindV ψ σ).injective_subtype)
    (functionTensor.injective (congrArg Subtype.val h))

def coindTrans {G H K X : Type*} [Group G] [Group H] [Group K]
    [AddCommMonoid X] [Module ℂ X]
    (φ : K →* H) (ψ : H →* G) (ρ : Representation ℂ K X) :
    Representation.IntertwiningMap (Representation.coind ψ (Representation.coind φ ρ))
      (Representation.coind (ψ.comp φ) ρ) where
  toLinearMap := {
    toFun a := ⟨fun g => (a.val g).val 1, by
      intro k g
      change (a.val (ψ (φ k) * g)).val 1 = ρ k ((a.val g).val 1)
      rw [a.property]
      change (a.val g).val (1*φ k) = ρ k ((a.val g).val 1)
      simpa only [one_mul,mul_one] using (a.val g).property k 1⟩
    map_add' a b := by ext g; rfl
    map_smul' a b := by ext g; rfl }
  isIntertwining' g := by ext a h; rfl

lemma coindTrans_injective {G H K X : Type*} [Group G] [Group H] [Group K]
    [AddCommMonoid X] [Module ℂ X]
    (φ : K →* H) (ψ : H →* G) (ρ : Representation ℂ K X) :
    Function.Injective (coindTrans φ ψ ρ) := by
  intro a b hab
  apply Subtype.ext
  funext g
  apply Subtype.ext
  funext h
  have hh := congrArg (fun z : Representation.coindV (ψ.comp φ) ρ =>
    z.val (ψ h * g)) hab
  change (a.val (ψ h*g)).val 1 = (b.val (ψ h*g)).val 1 at hh
  rw [a.property,b.property] at hh
  change (a.val g).val (1*h) = (b.val g).val (1*h) at hh
  simpa only [one_mul] using hh

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ProductInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product Induction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def externalTensor {a b : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ (Equiv.Perm (Fin a)) X)
    (σ : Representation ℂ (Equiv.Perm (Fin b)) Y) :
    Representation ℂ (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) (X ⊗[ℂ] Y) where
  toFun g := TensorProduct.map (ρ g.1) (σ g.2)
  map_one' := by ext x y; simp
  map_mul' g h := by ext x y; simp

def sumPermHom {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    (Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) →* Equiv.Perm (Fin n) where
  toFun g := sumPerm e g.1 g.2
  map_one' := sumPerm_one e
  map_mul' g h := sumPerm_mul e g.1 h.1 g.2 h.2

def externalWordMap {n a b d : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin a)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin b)) Y}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (F : Representation.IntertwiningMap ρ (wordRep a d))
    (G : Representation.IntertwiningMap σ (wordRep b d)) :
    Representation.IntertwiningMap (externalTensor ρ σ)
      ((wordRep n d).comp (sumPermHom e)) where
  toLinearMap := (positionTensor e).toLinearMap.comp
    (TensorProduct.map F.toLinearMap G.toLinearMap)
  isIntertwining' g := by
    ext x y w
    apply congrFun (a := w)
    change positionTensor e (F (ρ g.1 x) ⊗ₜ[ℂ] G (σ g.2 y)) =
      wordRep n d (sumPerm e g.1 g.2) (positionTensor e (F x ⊗ₜ[ℂ] G y))
    rw [F.isIntertwining, G.isIntertwining, positionTensor_tmul,
      positionTensor_tmul, positionProduct_equivariant]

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_PackingSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packing Support. -/

section

noncomputable section
open scoped TensorProduct MonoidAlgebra
namespace Saxl

def cyclicProductMap {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (u : WordSpace b d) :
    Representation.IntertwiningMap
      (outer (cyclic (wordRep a d) v).toRepresentation (cyclic (wordRep b d) u).toRepresentation)
      ((wordRep n d).comp (sumPermHom e)) :=
  externalWordMap e (subrepInclusion (cyclic (wordRep a d) v))
    (subrepInclusion (cyclic (wordRep b d) u))

lemma cyclicProduct_mem_range {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (u : WordSpace b d) :
    positionProduct e v u ∈ (cyclicProductMap e v u).range := by
  refine ⟨(⟨v,mem_cyclic _ _⟩ : (cyclic (wordRep a d) v).toSubmodule) ⊗ₜ[ℂ]
    (⟨u,mem_cyclic _ _⟩ : (cyclic (wordRep b d) u).toSubmodule), ?_⟩
  exact positionTensor_tmul e v u

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_WordRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Relabel. -/

section

noncomputable section
namespace Saxl
open scoped TensorProduct

def relabelWord {n m d : ℕ} (e : Fin n ≃ Fin m) : WordSpace n d ≃ₗ[ℂ] WordSpace m d where
  toFun v := fun w => v (w ∘ e)
  invFun v := fun w => v (w ∘ e.symm)
  left_inv v := by ext w; simp only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  right_inv v := by ext w; simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma relabelWord_apply {n m d : ℕ} (e : Fin n ≃ Fin m)
    (v : WordSpace n d) (w : Fin m → Fin d) : relabelWord e v w = v (w ∘ e) := rfl

lemma wordTensor_positionProduct {n k l a b : ℕ} (e : Fin n ≃ Fin k ⊕ Fin l)
    (x : WordSpace k a) (y : WordSpace l a) (v : WordSpace k b) (w : WordSpace l b) :
    wordTensor n a b (positionProduct e x y ⊗ₜ[ℂ] positionProduct e v w) =
      positionProduct e (wordTensor k a b (x ⊗ₜ[ℂ] v))
        (wordTensor l a b (y ⊗ₜ[ℂ] w)) := by
  ext z
  simp only [wordTensor_tmul, positionProduct]
  change (x (splitLeft (leftWord e z)) * y (splitLeft (rightWord e z))) *
    (v (splitRight (leftWord e z)) * w (splitRight (rightWord e z))) = _
  ring

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Product. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

def cyclicSquareMap {n d : ℕ} (v : WordSpace n d) :
    Representation.IntertwiningMap
      ((cyclic (wordRep n d) v).toRepresentation.tprod (cyclic (wordRep n d) v).toRepresentation)
      (wordRep n (d*d)) where
  toLinearMap := (wordTensor n d d).toLinearMap.comp
    (TensorProduct.map (cyclic (wordRep n d) v).toSubmodule.subtype
      (cyclic (wordRep n d) v).toSubmodule.subtype)
  isIntertwining' g := by
    ext x y w
    exact congrFun (wordTensor_equivariant g (x.val ⊗ₜ[ℂ] y.val)) w

@[simp] lemma cyclicSquareMap_tmul {n d : ℕ} (v : WordSpace n d)
    (x y : (cyclic (wordRep n d) v).toSubmodule) :
    cyclicSquareMap v (x ⊗ₜ[ℂ] y) = wordTensor n d d (x.val ⊗ₜ[ℂ] y.val) := rfl

theorem product_mem_square {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (u : WordSpace b d)
    (x : WordSpace a (d*d)) (y : WordSpace b (d*d))
    (hx : x ∈ (cyclicSquareMap v).range) (hy : y ∈ (cyclicSquareMap u).range) :
    positionProduct e x y ∈ (cyclicSquareMap (positionProduct e v u)).range := by
  obtain ⟨X,rfl⟩ := hx
  obtain ⟨Y,rfl⟩ := hy
  let W := (cyclicSquareMap (positionProduct e v u)).range.toSubmodule
  change positionProduct e (cyclicSquareMap v X) (cyclicSquareMap u Y) ∈ W
  rw [← positionTensor_tmul e (cyclicSquareMap v X) (cyclicSquareMap u Y)]
  induction X using OAI.tensorInductionOn with
  | add X X' h h' => simpa only [map_add,TensorProduct.add_tmul] using W.add_mem h h'
  | tmul x x' =>
    induction Y using OAI.tensorInductionOn with
    | add Y Y' h h' => simpa only [map_add,TensorProduct.tmul_add] using W.add_mem h h'
    | tmul y y' =>
      rw [cyclicSquareMap_tmul,cyclicSquareMap_tmul,positionTensor_tmul,
        ← wordTensor_positionProduct]
      refine ⟨(⟨positionProduct e x.val y.val,product_mem_cyclic e v u _ _ x.property y.property⟩ :
        (cyclic (wordRep n d) (positionProduct e v u)).toSubmodule) ⊗ₜ[ℂ]
        (⟨positionProduct e x'.val y'.val,product_mem_cyclic e v u _ _ x'.property y'.property⟩ :
        (cyclic (wordRep n d) (positionProduct e v u)).toSubmodule), rfl⟩

def joinedLabels {n a b : ℕ} {α : Type*} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → α) (c' : Fin b → α) : Fin n → α := fun i => Sum.elim c c' (e i)

@[simp] lemma joinedLabels_left {n a b : ℕ} {α : Type*} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → α) (c' : Fin b → α) (i : Fin a) :
    joinedLabels e c c' (e.symm (Sum.inl i)) = c i := by simp [joinedLabels]

@[simp] lemma joinedLabels_right {n a b : ℕ} {α : Type*} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → α) (c' : Fin b → α) (i : Fin b) :
    joinedLabels e c c' (e.symm (Sum.inr i)) = c' i := by simp [joinedLabels]

def joinedFiberHom {n a b : ℕ} {α : Type*} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → α) (c' : Fin b → α) :
    (fiberGroup c × fiberGroup c') →* fiberGroup (joinedLabels e c c') where
  toFun g := ⟨sumPerm e g.1.val g.2.val,by
    intro i
    obtain ⟨j,rfl⟩ := e.symm.surjective i
    cases j with
    | inl j => simpa only [sumPerm_left,joinedLabels_left] using g.1.property j
    | inr j => simpa only [sumPerm_right,joinedLabels_right] using g.2.property j⟩
  map_one' := Subtype.ext (sumPerm_one e)
  map_mul' g h := Subtype.ext (sumPerm_mul e g.1.val h.1.val g.2.val h.2.val)

lemma joinedFiberHom_surjective {n a b : ℕ} {α : Type*} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → α) (c' : Fin b → α) (hd : ∀ i j, c i ≠ c' j) :
    Function.Surjective (joinedFiberHom e c c') := by
  intro g
  have hg : g.val ∈ sectorGroup (fun i => (e i).isLeft = true) := by
    intro i
    have h := g.property i
    change Sum.elim c c' (e (g.val i)) = Sum.elim c c' (e i) at h
    cases he : e i with
    | inl j =>
      cases hf : e (g.val i) with
      | inl k => simp only [he,hf,Sum.isLeft_inl]
      | inr k => simp only [he,hf,Sum.elim_inl,Sum.elim_inr] at h; exact False.elim (hd j k h.symm)
    | inr j =>
      cases hf : e (g.val i) with
      | inl k => simp only [he,hf,Sum.elim_inl,Sum.elim_inr] at h; exact False.elim (hd k j h)
      | inr k => simp only [he,hf,Sum.isLeft_inr]
  let g' : sectorGroup (fun i => (e i).isLeft = true) := ⟨g.val,hg⟩
  have hl : leftRestriction e g' ∈ fiberGroup c := by
    intro i
    have hh := g.property (e.symm (Sum.inl i))
    rw [← leftRestriction_apply e g',joinedLabels_left,joinedLabels_left] at hh
    exact hh
  have hr : rightRestriction e g' ∈ fiberGroup c' := by
    intro i
    have hh := g.property (e.symm (Sum.inr i))
    rw [← rightRestriction_apply e g',joinedLabels_right,joinedLabels_right] at hh
    exact hh
  exact ⟨(⟨_,hl⟩,⟨_,hr⟩),Subtype.ext (sumPerm_restrictions e g')⟩

lemma componentWords_joined {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → ℕ) (c' : Fin b → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (w : Fin n → Fin d) :
    componentWords (joinedLabels e c c') A label w ↔
      componentWords c A label (leftWord e w) ∧ componentWords c' A label (rightWord e w) := by
  constructor
  · rintro ⟨hA,hl⟩
    exact ⟨⟨fun i => hA _,fun i => (hl _).trans (joinedLabels_left e c c' i)⟩,
      ⟨fun i => hA _,fun i => (hl _).trans (joinedLabels_right e c c' i)⟩⟩
  · rintro ⟨⟨hA,hl⟩,⟨hA',hl'⟩⟩
    constructor
    · intro i
      obtain ⟨j,rfl⟩ := e.symm.surjective i
      cases j with
      | inl j => exact hA j
      | inr j => exact hA' j
    · intro i
      obtain ⟨j,rfl⟩ := e.symm.surjective i
      cases j with
      | inl j => exact (hl j).trans (joinedLabels_left e c c' j).symm
      | inr j => exact (hl' j).trans (joinedLabels_right e c c' j).symm

lemma component_projection_product {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → ℕ) (c' : Fin b → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (x : WordSpace a d) (y : WordSpace b d) :
    coordinateProjection (componentWords (joinedLabels e c c') A label) (positionProduct e x y) =
      positionProduct e (coordinateProjection (componentWords c A label) x)
        (coordinateProjection (componentWords c' A label) y) := by
  classical
  ext w
  simp only [coordinateProjection_apply,componentWords_joined,positionProduct]
  split_ifs <;> simp_all

lemma joined_component_sum {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → ℕ) (c' : Fin b → ℕ) (z : Fin d → ℤ)
    (w : Fin n → Fin d) (k : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i => joinedLabels e c c' i = k), z (w i) =
      (∑ i ∈ Finset.univ.filter (fun i => c i = k), z (leftWord e w i)) +
      ∑ i ∈ Finset.univ.filter (fun i => c' i = k), z (rightWord e w i) := by
  classical
  simp only [Finset.sum_filter]
  rw [← Equiv.sum_comp e.symm, Fintype.sum_sum_type]
  simp only [joinedLabels_left,joinedLabels_right,leftWord,rightWord]

lemma product_fixed_sums {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (c : Fin a → ℕ) (c' : Fin b → ℕ) (z : Fin d → ℤ)
    (σ σ' : ℕ → ℤ) (x : WordSpace a d) (y : WordSpace b d)
    (hx : FixedComponentSums c z σ x) (hy : FixedComponentSums c' z σ' y) :
    FixedComponentSums (joinedLabels e c c') z (σ+σ') (positionProduct e x y) := by
  intro w hw k
  obtain ⟨hxw,hyw⟩ := mul_ne_zero_iff.mp hw
  rw [joined_component_sum,hx _ hxw k,hy _ hyw k,Pi.add_apply]

def outerWordMap {n a b d : ℕ} {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (φ : G →* Equiv.Perm (Fin a)) (ψ : H →* Equiv.Perm (Fin b))
    (F : Representation.IntertwiningMap ρ ((wordRep a d).comp φ))
    (Q : Representation.IntertwiningMap σ ((wordRep b d).comp ψ)) :
    Representation.IntertwiningMap (outer ρ σ)
      ((wordRep n d).comp ((sumPermHom e).comp (φ.prodMap ψ))) where
  toLinearMap := (positionTensor e).toLinearMap.comp (TensorProduct.map F.toLinearMap Q.toLinearMap)
  isIntertwining' g := by
    ext x y w
    apply congrFun (a := w)
    change positionTensor e (F (ρ g.1 x) ⊗ₜ[ℂ] Q (σ g.2 y)) =
      wordRep n d (sumPerm e (φ g.1) (ψ g.2)) (positionTensor e (F x ⊗ₜ[ℂ] Q y))
    rw [F.isIntertwining,Q.isIntertwining,positionTensor_tmul,positionTensor_tmul]
    exact (positionProduct_equivariant e (φ g.1) (ψ g.2) (F x) (Q y)).symm

lemma outerWordMap_injective {n a b d : ℕ} {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (φ : G →* Equiv.Perm (Fin a)) (ψ : H →* Equiv.Perm (Fin b))
    (F : Representation.IntertwiningMap ρ ((wordRep a d).comp φ))
    (Q : Representation.IntertwiningMap σ ((wordRep b d).comp ψ))
    (hF : Function.Injective F) (hQ : Function.Injective Q) :
    Function.Injective (outerWordMap e φ ψ F Q) :=
  (positionTensor e).injective.comp (TensorProduct.map_injective_of_flat_flat _ _ hF hQ)

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Gluing. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

structure Piece {n d : ℕ} {G Y : Type*} [Group G] [AddCommGroup Y] [Module ℂ Y]
    (v : WordSpace n d) (c : Fin n → ℕ)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ) (σ : ℕ → ℤ)
    (φ : G →* fiberGroup c) (τ : Representation ℂ G Y) where
  surj : Function.Surjective φ
  raw : Y →ₗ[ℂ] WordSpace n (d*d)
  raw_mem : ∀ y, raw y ∈ (cyclicSquareMap v).range
  raw_sums : ∀ y, FixedComponentSums c (fun a => (output a : ℤ)) σ (raw y)
  projected : Representation.IntertwiningMap τ
    ((wordRep n (d*d)).comp ((fiberGroup c).subtype.comp φ))
  injective : Function.Injective projected
  projection_eq : ∀ y, coordinateProjection (componentWords c A label) (raw y) = projected y

def Piece.join {n a b d : ℕ} {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {v : WordSpace a d} {u : WordSpace b d}
    {c : Fin a → ℕ} {c' : Fin b → ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {σ σ' : ℕ → ℤ}
    {φ : G →* fiberGroup c} {ψ : H →* fiberGroup c'}
    {ρ : Representation ℂ G X} {τ : Representation ℂ H Y}
    (P : Piece v c A label σ φ ρ) (Q : Piece u c' A label σ' ψ τ)
    (e : Fin n ≃ Fin a ⊕ Fin b) (hd : ∀ i j, c i ≠ c' j) :
    letI : AddCommGroup (X ⊗[ℂ] Y) := Module.addCommMonoidToAddCommGroup ℂ
    Piece (positionProduct e v u) (joinedLabels e c c') A label (σ+σ')
      ((joinedFiberHom e c c').comp (φ.prodMap ψ)) (outer ρ τ) := by
  letI : AddCommGroup (X ⊗[ℂ] Y) := Module.addCommMonoidToAddCommGroup ℂ
  let L := (positionTensor e).toLinearMap.comp (TensorProduct.map P.raw Q.raw)
  let T := outerWordMap e ((fiberGroup c).subtype.comp φ)
    ((fiberGroup c').subtype.comp ψ) P.projected Q.projected
  refine {
    surj := (joinedFiberHom_surjective e c c' hd).comp (P.surj.prodMap Q.surj)
    raw := L
    raw_mem := ?_
    raw_sums := ?_
    projected := T
    injective := outerWordMap_injective e _ _ P.projected Q.projected P.injective Q.injective
    projection_eq := ?_ }
  · intro z
    change L z ∈ (cyclicSquareMap (positionProduct e v u)).range.toSubmodule
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul x y =>
      change positionTensor e (P.raw x ⊗ₜ[ℂ] Q.raw y) ∈ _
      rw [positionTensor_tmul]
      exact product_mem_square e v u _ _ (P.raw_mem x) (Q.raw_mem y)
  · intro z
    change L z ∈ fixedSumSpace (joinedLabels e c c') (fun a => (output a : ℤ)) (σ+σ')
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul x y =>
      change positionTensor e (P.raw x ⊗ₜ[ℂ] Q.raw y) ∈ _
      rw [positionTensor_tmul]
      exact product_fixed_sums e c c' _ σ σ' _ _ (P.raw_sums x) (Q.raw_sums y)
  · intro z
    induction z using OAI.tensorInductionOn with
    | add x y hx hy =>
      change coordinateProjection _ (L (x+y)) = T.toLinearMap (x+y)
      rw [map_add,map_add,hx,hy,map_add]
      rfl
    | tmul x y =>
      change coordinateProjection (componentWords (joinedLabels e c c') A label)
        (positionTensor e (P.raw x ⊗ₜ[ℂ] Q.raw y)) =
        positionTensor e (P.projected x ⊗ₜ[ℂ] Q.projected y)
      rw [positionTensor_tmul,positionTensor_tmul,component_projection_product,
        P.projection_eq,Q.projection_eq]

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalancePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Packing. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

structure Packing {n d e : ℕ} (v : WordSpace n d)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ) (w : WordSpace n e) where
  G : Type
  [groupG : Group G]
  [finiteG : Finite G]
  Y : Type
  [addY : AddCommGroup Y]
  [moduleY : Module ℂ Y]
  [finiteY : FiniteDimensional ℂ Y]
  c : Fin n → ℕ
  σ : ℕ → ℤ
  φ : G →* fiberGroup c
  τ : Representation ℂ G Y
  piece : Piece v c A label σ φ τ
  support : SupportLE (cyclic (wordRep n e) w).toRepresentation
    (Representation.coind ((fiberGroup c).subtype.comp φ) τ)

attribute [instance] Packing.groupG Packing.finiteG Packing.addY Packing.moduleY Packing.finiteY

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

namespace Balance
open Columns

def Packing.congr {n d e : ℕ} {v u : WordSpace n d}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {w z : WordSpace n e}
    (P : Packing v A label w) (hv : v = u) (hw : w = z) : Packing u A label z where
  G := P.G
  Y := P.Y
  c := P.c
  σ := P.σ
  φ := P.φ
  τ := P.τ
  piece := by rw [← hv]; exact P.piece
  support := by rw [← hw]; exact P.support

end Balance
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OutputBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Output Bands. -/

section

noncomputable section
namespace Saxl.Balance

structure OutputBands where
  starts : Finset ℕ
  upper : ℕ → ℕ
  nonempty : ∀ k ∈ starts, k ≤ upper k
  separated : ∀ k ∈ starts, ∀ l ∈ starts, k < l → upper k < l

def OutputBands.Allows (B : OutputBands) (x : ℕ) : Prop :=
  ∃ k ∈ B.starts, k ≤ x ∧ x ≤ B.upper k

def OutputBands.label (B : OutputBands) (x : ℕ) : ℕ := by
  classical
  exact if h : B.Allows x then Classical.choose h else 0

def OutputBands.alphabet (B : OutputBands) (d : ℕ) : Fin (d*d) → Prop :=
  fun a => B.Allows (output a)

def OutputBands.letterLabel (B : OutputBands) (d : ℕ) : Fin (d*d) → ℕ :=
  fun a => B.label (output a)

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_TwoStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Strip. -/

section

noncomputable section

namespace Saxl.Balance

def FourInterlacing (a b c d x y z w : ℕ) : Prop :=
  x ≤ a ∧ b ≤ x ∧ y ≤ b ∧ c ≤ y ∧ z ≤ c ∧ d ≤ z ∧ w ≤ d ∧
  x+y+z+w+2 = a+b+c+d ∧ (y < x ∨ w < z)

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Blocks. -/

section

noncomputable section
namespace Saxl.Balance

def bigColumns (q δ : ℕ) : List ℕ := [q+1+δ,q] ++ List.replicate (1+δ) 1

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_NumericBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric Bands. -/

section

noncomputable section
namespace Saxl.Balance

def BandsValid (es : List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ es, e.1 ≤ e.2) ∧ ∀ e ∈ es, ∀ f ∈ es,
    (e.1 = f.1 → e.2 = f.2) ∧ (e.1 < f.1 → e.2 < f.1)

end Saxl.Balance
end
end

end OAI
end


