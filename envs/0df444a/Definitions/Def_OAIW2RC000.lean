-- Prove2me | Definitions.Def_OAIW2RC000
-- name    : OAIW2RC000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T02:01:44.593793+00:00
-- url     : https://prove2.me/theorems/7e3dac44-d5d7-4868-96d4-5dfb2760fc7d
-- title:
--   Definitions bundle OAIW2RC000 of the split of OpenAI, Row–column symmetry and contraction of coordinate sweeps
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RowColumn.occupied_overlap` and `OAI.RowColumn.occupied_overlap_endpoint`, carved from OpenAI's openai/math development (OpenAI, *Row–column symmetry and contraction of coordinate sweeps*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 210 declarations of OpenAI's Lean: 143 definitions, 5 instances and 62 theorems. The definitions and types are `OAI.CubeShuffle.PermutationHilbert.act`, `OAI.CubeShuffle.Specht.columnEquiv`, `OAI.CubeShuffle.Specht.columnValues`, `OAI.CubeShuffle.Specht.fiberGroup`, `OAI.CubeShuffle.Specht.pairing`, `OAI.CubeShuffle.Specht.rankCell`, `OAI.CubeShuffle.Specht.rankPerm`, `OAI.CubeShuffle.Specht.rowGroup`, `OAI.CubeShuffle.Specht.symmetrizer`, `OAI.CubeShuffle.Specht.unitaryEquiv`, `OAI.RowColumn.FiniteStarAlgebra.Ambient`, `OAI.RowColumn.FiniteStarAlgebra.algebraCore`, `OAI.RowColumn.FiniteStarAlgebra.algebraToEnd`, `OAI.RowColumn.FiniteStarAlgebra.physicalTrace`, `OAI.RowColumn.FiniteStarAlgebra.restrictHom`, `OAI.RowColumn.FiniteStarAlgebra.unitarySpan`, `OAI.RowColumn.FiniteStarAlgebra.unitarySpanHom`, `OAI.RowColumn.HilbertSchmidt.endCore`, `OAI.RowColumn.HilbertSchmidt.hsInner`, `OAI.RowColumn.HookModel.Color`, `OAI.RowColumn.HookModel.IsOdd`, `OAI.RowColumn.HookModel.hookEmbedding`, `OAI.RowColumn.HookModel.hookRepresentation`, `OAI.RowColumn.HookModel.oddCount`, `OAI.RowColumn.HookModel.template`, `OAI.RowColumn.HookModel.templateWord`, `OAI.RowColumn.HookModel.youngVector`, `OAI.RowColumn.Isotypic.carrier`, `OAI.RowColumn.Isotypic.restrictIntertwiner`, `OAI.RowColumn.Isotypic.restricted`, `OAI.RowColumn.MatrixState.GlobalTypes`, `OAI.RowColumn.MatrixState.Sector`, `OAI.RowColumn.MatrixState.algebraMatrix`, `OAI.RowColumn.MatrixState.blockMask`, `OAI.RowColumn.MatrixState.discreteContinuousHom`, `OAI.RowColumn.MatrixState.evenAlgebra`, `OAI.RowColumn.MatrixState.extendMatrix`, `OAI.RowColumn.MatrixState.factorQuadratic`, `OAI.RowColumn.MatrixState.gramState`, `OAI.RowColumn.MatrixState.hsVector` and 103 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/RowColumn, in whole or in part: `FiniteUnitary_Coefficients`, `FiniteUnitary_Frames`, `FiniteUnitary_Reconstruction`, `FiniteUnitary_Uncertainty`, `MatrixState_HilbertSchmidt`, `MatrixState_Postselection`, `MatrixState_QuarterRoot`, `MatrixState_Whitening`, `RowColumn_CopyOverlap`, `RowColumn_Dephasing`, `RowColumn_Entropy`, `RowColumn_HookModel`, `RowColumn_LineStates`, `RowColumn_Multiplicity`, `RowColumn_OverlapBound`, `RowColumn_Postselection`, `RowColumn_Sectors`, `RowColumn_SignedWords`, `RowColumn_TensorFilter`, `YoungSymmetry_Dimensions`, `YoungSymmetry_Polytabloid`, `YoungSymmetry_UnitaryModel`.
--
--   **Imports.** It imports the published bundle `Def_OccupiedOverlap`.
--
--   **Imported by** (directly, in this split): the statements `OAI.RowColumn.MatrixState.occupied_commutant_trace` and `OAI.RowColumn.MatrixState.sector_filtered_trace_bound`; the proofs of `OAI.RowColumn.MatrixState.occupied_commutant_trace`, `OAI.RowColumn.MatrixState.sector_filtered_trace_bound`, `OAI.RowColumn.occupied_dimension_ratio` and `OAI.RowColumn.occupied_overlap_endpoint`.
-- source:
--   OpenAI, Row–column symmetry and contraction of coordinate sweeps, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/RowColumn at commit adc7f12

import Mathlib
import Definitions.Def_OccupiedOverlap

section
-- module Solutions.OAIW2_RowColumn.Compat
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
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.FiniteUnitary_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma unitary_inner_inv (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) (v w : V) :
    inner ℂ v (ρ g⁻¹ w) = inner ℂ (ρ g v) w := by
  have h := hρ g v (ρ g⁻¹ w)
  have he : ρ g (ρ g⁻¹ w) = w := by
    change (ρ g * ρ g⁻¹) w = w
    rw [←map_mul,mul_inv_cancel,map_one]
    rfl
  rw [he] at h
  exact h.symm

end CubeShuffle.UnitaryFinite

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.FiniteUnitary_Frames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace RowColumn.HilbertSchmidt
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The algebraic Hilbert--Schmidt scalar product, irrespective of the operator
norm on the carrier. A core is used to avoid changing any source norm. -/
def hsInner (T U : E →ₗ[ℂ] E) : ℂ :=
  LinearMap.trace ℂ E (LinearMap.adjoint T ∘ₗ U)

lemma hsInner_basis (T U : E →ₗ[ℂ] E) :
    hsInner T U = ∑ i, inner ℂ (T (stdOrthonormalBasis ℂ E i))
      (U (stdOrthonormalBasis ℂ E i)) := by
  rw [hsInner, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E)]
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right]

@[instance_reducible]
def endCore : InnerProductSpace.Core ℂ (E →ₗ[ℂ] E) where
  inner := hsInner
  conj_inner_symm T U := by
    simp only [hsInner_basis, map_sum, inner_conj_symm]
  re_inner_nonneg T := by
    rw [hsInner_basis, map_sum]
    exact Finset.sum_nonneg fun _ _ => inner_self_nonneg
  add_left T U V := by
    simp only [hsInner_basis, LinearMap.add_apply, inner_add_left, Finset.sum_add_distrib]
  smul_left T U z := by
    simp only [hsInner_basis, LinearMap.smul_apply, inner_smul_left, Finset.mul_sum]
  definite T h := by
    have hh : ∑ i, ‖T (stdOrthonormalBasis ℂ E i)‖^2 = 0 := by
      have he := congrArg (RCLike.re : ℂ → ℝ) h
      simpa only [hsInner_basis, map_sum, map_zero, inner_self_eq_norm_sq] using he
    have hz (i : Fin (Module.finrank ℂ E)) : T (stdOrthonormalBasis ℂ E i) = 0 := by
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
        sq_nonneg ‖T (stdOrthonormalBasis ℂ E j)‖)).mp hh i (Finset.mem_univ i)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
    apply (stdOrthonormalBasis ℂ E).toBasis.ext
    intro i
    simpa using hz i

lemma hsInner_conj (u : E ≃ₗᵢ[ℂ] E) (T V : E →ₗ[ℂ] E) :
    hsInner (u.toLinearEquiv.conj T) (u.toLinearEquiv.conj V) = hsInner T V := by
  rw [hsInner_basis]
  conv_rhs => rw [hsInner, LinearMap.trace_eq_sum_inner _
    ((stdOrthonormalBasis ℂ E).map u.symm)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    OrthonormalBasis.map_apply, LinearEquiv.conj_apply]
  change inner ℂ (u (T (u.symm (stdOrthonormalBasis ℂ E i))))
      (u (V (u.symm (stdOrthonormalBasis ℂ E i)))) = _
  exact u.inner_map_map _ _

end RowColumn.HilbertSchmidt

noncomputable section
open scoped RealInnerProductSpace

noncomputable section
open scoped BigOperators ComplexConjugate
namespace RowColumn.UnitaryFrame
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def quadraticForm (T : E →ₗ[ℂ] E) (x : E) : ℝ := (inner ℂ x (T x)).re

end RowColumn.UnitaryFrame

namespace RowColumn.UnitaryFrame
open scoped BigOperators ComplexOrder ComplexConjugate
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Group G]

local instance instNormedAddCommGroupLinearMapComplexId_solutions : NormedAddCommGroup (E →ₗ[ℂ] E) := HilbertSchmidt.endCore.toNormedAddCommGroup
local instance instInnerProductSpaceComplexLinearMapId_solutions : InnerProductSpace ℂ (E →ₗ[ℂ] E) :=
  InnerProductSpace.ofCore { __ := HilbertSchmidt.endCore (E := E) }
local instance instInnerProductSpaceRealLinearMapComplexId_solutions : InnerProductSpace ℝ (E →ₗ[ℂ] E) := InnerProductSpace.complexToReal

def conjugationIsometry (u : E ≃ₗᵢ[ℂ] E) :
    (E →ₗ[ℂ] E) →ₗᵢ[ℂ] (E →ₗ[ℂ] E) :=
  u.toLinearEquiv.conj.toLinearMap.isometryOfInner (HilbertSchmidt.hsInner_conj u)

def conjugationReal (u : E ≃ₗᵢ[ℂ] E) :
    (E →ₗ[ℂ] E) →ₗᵢ[ℝ] (E →ₗ[ℂ] E) where
  toLinearMap := (conjugationIsometry u).toLinearMap.restrictScalars ℝ
  norm_map' := (conjugationIsometry u).norm_map

def matrixEntry (x y : E) : (E →ₗ[ℂ] E) →ₗ[ℂ] ℂ where
  toFun T := inner ℂ x (T y)
  map_add' T V := by simp only [LinearMap.add_apply, inner_add_right]
  map_smul' c T := by simp only [LinearMap.smul_apply, inner_smul_right, smul_eq_mul, RingHom.id_apply]

def quadraticEval (x : E) : (E →ₗ[ℂ] E) →ₗ[ℝ] ℝ where
  toFun T := quadraticForm T x
  map_add' T V := by simp [quadraticForm]
  map_smul' c T := by
    simp only [quadraticForm, LinearMap.smul_apply, ← Complex.coe_smul, inner_smul_right]
    simp [Complex.mul_re]

def coerciveSet (ε : ℝ) : Set (E →ₗ[ℂ] E) :=
  {T | ∀ x, ε * ‖x‖^2 ≤ quadraticForm T x}

def frameHull (π : G →* E ≃ₗᵢ[ℂ] E) (x₀ : E) : Set (E →ₗ[ℂ] E) :=
  closure (convexHull ℝ (Set.range fun g : G =>
    (InnerProductSpace.rankOne ℂ (π g x₀) (π g x₀)).toLinearMap))

end RowColumn.UnitaryFrame
namespace RowColumn.UnitaryFrame
open scoped BigOperators ComplexOrder ComplexConjugate
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Group G]

def finiteFrame (s : Finset E) : E →ₗ[ℂ] E :=
  s.centerMass (fun _ => (1 : ℝ))
    (fun v => (InnerProductSpace.rankOne ℂ v v).toLinearMap)

end RowColumn.UnitaryFrame

end
end
end
end


end OAI
end

section
-- module Solutions.OAIW2_RowColumn.FiniteUnitary_Uncertainty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CubeShuffle.PermutationHilbert
open scoped BigOperators ComplexConjugate Classical
open Complex

variable {X : Type*} [Fintype X]

noncomputable def act (p : Equiv.Perm X) : H X ≃ₗᵢ[ℂ] H X :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ p

@[simp] lemma act_apply (p : Equiv.Perm X) (v : H X) (x : X) :
    act p v x = v (p⁻¹ x) := rfl

end CubeShuffle.PermutationHilbert

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.YoungSymmetry_Polytabloid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary polytabloid input for the symmetric-group step of FAC.7.
No branching or classification theorem is postulated here. -/
namespace CubeShuffle.Specht
open scoped BigOperators Classical

@[simp] lemma card_cell (μ : YoungDiagram) : Fintype.card (Cell μ) = μ.card := by
  simp [Cell, YoungDiagram.card]

noncomputable def columnEquiv (μ : YoungDiagram) (j : ℕ) :
    {x : Cell μ // col x = j} ≃ Fin (μ.colLen j) where
  toFun x := ⟨row x.1, by simpa [x.2] using row_lt_colLen x.1⟩
  invFun i := ⟨⟨(i,j), YoungDiagram.mem_iff_lt_colLen.mpr i.2⟩, rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl x.2.symm
  right_inv i := by rfl

noncomputable def columnValues {μ : YoungDiagram} (f : Cell μ → ℕ) (j : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun x => col x = j)).image f

lemma mem_columnValues {μ : YoungDiagram} (f : Cell μ → ℕ) (x : Cell μ) :
    f x ∈ columnValues f (col x) := by
  classical
  exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩

lemma card_columnValues {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) (j : ℕ) :
    (columnValues f j).card = μ.colLen j := by
  classical
  rw [columnValues, Finset.card_image_iff.mpr]
  · rw [← Fintype.card_subtype]
    exact Fintype.card_congr (columnEquiv μ j) |>.trans (Fintype.card_fin _)
  intro x hx y hy he
  exact hf x y ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) he

/-- Rank inside a column, sorted by an arbitrary column-injective row assignment. -/
noncomputable def rankCell {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) (x : Cell μ) : Cell μ :=
  let k := ((columnValues f (col x)).orderIsoOfFin (card_columnValues f hf (col x))).symm
    ⟨f x, mem_columnValues f x⟩
  ⟨(k.val,col x), YoungDiagram.mem_iff_lt_colLen.mpr k.isLt⟩

@[simp] lemma rankCell_col {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) (x : Cell μ) :
    col (rankCell f hf x) = col x := rfl

lemma rankCell_orderEmb {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) (x : Cell μ) :
    (columnValues f (col x)).orderEmbOfFin (card_columnValues f hf (col x))
      ⟨row (rankCell f hf x), row_lt_colLen (rankCell f hf x)⟩ = f x := by
  change ((columnValues f (col x)).orderIsoOfFin (card_columnValues f hf (col x))
    (((columnValues f (col x)).orderIsoOfFin (card_columnValues f hf (col x))).symm
      ⟨f x, mem_columnValues f x⟩)).val = f x
  simp

lemma rankCell_injective {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) :
    Function.Injective (rankCell f hf) := by
  intro x y h
  have hc : col x = col y := by simpa only [rankCell_col] using congrArg (fun z : Cell μ => col z) h
  apply hf x y hc
  have hx := rankCell_orderEmb f hf x
  have hy := rankCell_orderEmb f hf y
  change (columnValues f (col (rankCell f hf x))).orderEmbOfFin
    (card_columnValues f hf (col (rankCell f hf x)))
      ⟨row (rankCell f hf x), row_lt_colLen (rankCell f hf x)⟩ = f x at hx
  rw [h] at hx
  exact hx.symm.trans hy

noncomputable def rankPerm {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) : Equiv.Perm (Cell μ) :=
  Equiv.ofBijective (rankCell f hf) ((Finite.injective_iff_bijective).mp (rankCell_injective f hf))

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

@[simp] lemma mem_colGroup {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) :
    p ∈ colGroup μ ↔ ∀ x, col (p x) = col x := Iff.rfl

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

@[simp] lemma permSign_one {α : Type*} [Fintype α] [DecidableEq α] :
    permSign (1 : Equiv.Perm α) = 1 := by simp [permSign]
@[simp] lemma permSign_mul {α : Type*} [Fintype α] [DecidableEq α] (p q : Equiv.Perm α) :
    permSign (p*q) = permSign p * permSign q := by simp [permSign]
@[simp] lemma permSign_inv {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) :
    permSign p⁻¹ = permSign p := by simp [permSign,Equiv.Perm.inv_def]
@[simp] lemma permSign_swap {α : Type*} [Fintype α] [DecidableEq α] {x y : α} (h : x ≠ y) :
    permSign (Equiv.swap x y) = -1 := by simp [permSign, h]
@[simp] lemma conj_permSign {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) :
    starRingEnd ℂ (permSign p) = permSign p := by simp [permSign]

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

noncomputable def pairing {μ : YoungDiagram} (v w : Tabloid μ → ℂ) : ℂ :=
  ∑ f, w f * starRingEnd ℂ (v f)

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical

section Symmetrizer
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

noncomputable def symmetrizer (H : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) : Module.End ℂ V :=
  ∑ h : H, ρ h

noncomputable def fiberGroup {β : Type*} (f : α → β) : Subgroup (Equiv.Perm α) where
  carrier := {p | ∀ x, f (p x) = f x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro p q hp hq x; exact (hp (q x)).trans (hq x)
  inv_mem' := by intro p hp x; simpa using (hp (p⁻¹ x)).symm

end Symmetrizer

end CubeShuffle.Specht

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.YoungSymmetry_Dimensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CubeShuffle.Specht
open scoped BigOperators Classical

noncomputable def rowGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (Cell μ)) :=
  fiberGroup (rowIndex (μ := μ))

noncomputable instance tabloidMulAction (μ : YoungDiagram) : MulAction (Equiv.Perm (Cell μ)) (Tabloid μ) where
  smul p f := tabloidAct p f
  one_smul f := by change tabloidAct 1 f = f; rw [tabloidAct_one]; rfl
  mul_smul p q f := by change tabloidAct (p*q) f = tabloidAct p (tabloidAct q f); rw [tabloidAct_mul]; rfl

end CubeShuffle.Specht

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.YoungSymmetry_UnitaryModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CubeShuffle.Specht
open scoped BigOperators Classical

noncomputable def unitaryEquiv (μ : YoungDiagram) :
    Representation.Equiv (representation μ) (unitaryRepresentation μ) :=
  Representation.Equiv.mk (spaceHilbertEquiv μ) (by
    intro p
    apply LinearMap.ext
    intro v
    change spaceHilbertEquiv μ (representation μ p v) =
      spaceHilbertEquiv μ (representation μ p ((spaceHilbertEquiv μ).symm (spaceHilbertEquiv μ v)))
    rw [LinearEquiv.symm_apply_apply])

end CubeShuffle.Specht

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.FiniteUnitary_Reconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ComplexOrder
noncomputable section
open scoped ComplexConjugate

namespace RowColumn.FiniteStarAlgebra
open scoped ComplexOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

abbrev Ambient := E →L[ℂ] E

def algebraToEnd (A : StarSubalgebra ℂ (Ambient (E := E))) : A →ₗ[ℂ] (E →ₗ[ℂ] E) :=
  { toFun a := (a : Ambient (E := E)).toLinearMap
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

lemma algebraToEnd_injective (A : StarSubalgebra ℂ (Ambient (E := E))) :
    Function.Injective (algebraToEnd A) := by
  intro a b h
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.congr_fun h x

@[instance_reducible]
def algebraCore (A : StarSubalgebra ℂ (Ambient (E := E))) : InnerProductSpace.Core ℂ A where
  inner a b := HilbertSchmidt.endCore.inner (algebraToEnd A a) (algebraToEnd A b)
  conj_inner_symm a b := HilbertSchmidt.endCore.conj_inner_symm _ _
  re_inner_nonneg a := HilbertSchmidt.endCore.re_inner_nonneg _
  add_left a b c := by rw [map_add]; exact HilbertSchmidt.endCore.add_left _ _ _
  smul_left a b c := by rw [map_smul]; exact HilbertSchmidt.endCore.smul_left _ _ _
  definite a h := (algebraToEnd_injective A) (by simpa only [map_zero] using HilbertSchmidt.endCore.definite _ h)

def physicalTrace (A : StarSubalgebra ℂ (Ambient (E := E))) : A →ₗ[ℂ] ℂ :=
  (LinearMap.trace ℂ E).comp (algebraToEnd A)

/-- Restriction to a subspace preserved by the whole star algebra is a genuine
star homomorphism (both the subspace and its orthogonal complement are reducing). -/
def restrictHom (A : StarSubalgebra ℂ (Ambient (E := E))) (F : Submodule ℂ E)
    (hF : ∀ a : A, ∀ x ∈ F, (a : Ambient (E := E)) x ∈ F) : A →⋆ₐ[ℂ] (F →L[ℂ] F) where
  toFun a := (a : Ambient (E := E)).restrict (hF a)
  map_zero' := by ext x; rfl
  map_add' a b := by ext x; rfl
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl
  commutes' c := by ext x; rfl
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ ((star (a : Ambient (E := E))) (x : E)) (y : E) =
      inner ℂ (x : E) ((a : Ambient (E := E)) (y : E))
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

end RowColumn.FiniteStarAlgebra
noncomputable section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace RowColumn.Isotypic
variable {G V E : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (ρ : Representation ℂ G V) (τ : Representation ℂ G E)

def carrier : Submodule ℂ E := Submodule.span ℂ
  (Set.range fun p : Representation.IntertwiningMap ρ τ × V => p.1 p.2)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] in
lemma mem_carrier (f : Representation.IntertwiningMap ρ τ) (v : V) : f v ∈ carrier ρ τ :=
  Submodule.subset_span ⟨(f,v),rfl⟩

end RowColumn.Isotypic
namespace RowColumn.Isotypic
variable {G V E : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (ρ : Representation ℂ G V) (τ : Representation ℂ G E)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] in
lemma carrier_invariant (g : G) (x : E) (hx : x ∈ carrier ρ τ) : τ g x ∈ carrier ρ τ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨f,v⟩,rfl⟩ := hx
    rw [← Representation.IntertwiningMap.isIntertwining ρ τ f]
    exact mem_carrier ρ τ f _
  | zero => simpa only [map_zero] using (carrier ρ τ).zero_mem
  | add x y hx hy hx' hy' => simpa only [map_add] using (carrier ρ τ).add_mem hx' hy'
  | smul c x hx hx' => simpa only [map_smul] using (carrier ρ τ).smul_mem c hx'

def restricted : Representation ℂ G (carrier ρ τ) where
  toFun g := (τ g).restrict (carrier_invariant ρ τ g)
  map_one' := by ext x; exact LinearMap.congr_fun (map_one τ) x
  map_mul' g h := by ext x; exact LinearMap.congr_fun (map_mul τ g h) x

def restrictIntertwiner (f : Representation.IntertwiningMap ρ τ) :
    Representation.IntertwiningMap ρ (restricted ρ τ) where
  toLinearMap := f.toLinearMap.codRestrict (carrier ρ τ) (mem_carrier ρ τ f)
  isIntertwining' g := by
    ext v
    exact Representation.IntertwiningMap.isIntertwining ρ τ f g v

end RowColumn.Isotypic
end
end
end
end
end


section
noncomputable section
open scoped ComplexOrder
namespace RowColumn.FiniteStarAlgebra
variable {G V E : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

instance algebraFiniteDimensional (A : StarSubalgebra ℂ (E →L[ℂ] E)) : FiniteDimensional ℂ A :=
  FiniteDimensional.of_injective (algebraToEnd A) (algebraToEnd_injective A)

instance algebraIsClosed (A : StarSubalgebra ℂ (E →L[ℂ] E)) : IsClosed (A : Set (E →L[ℂ] E)) :=
  A.toSubalgebra.toSubmodule.closed_of_finiteDimensional

end RowColumn.FiniteStarAlgebra
end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.MatrixState_HilbertSchmidt
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J : Type*} [Fintype I] [Fintype J]

def hsVector : Matrix I J ℂ →ₗ[ℂ] EuclideanSpace ℂ (I × J) where
  toFun M := WithLp.toLp 2 (fun z => M z.1 z.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end RowColumn.MatrixState

end
end

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

instance matrixAlgebraIsClosed (A : StarSubalgebra ℂ (Matrix I I ℂ)) : IsClosed (A : Set (Matrix I I ℂ)) :=
  A.toSubalgebra.toSubmodule.closed_of_finiteDimensional

end RowColumn.MatrixState

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.MatrixState_QuarterRoot
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {C : Type*} [Fintype C] [DecidableEq C]

abbrev quarterRoot (A : Matrix C C ℂ) := CFC.sqrt (CFC.sqrt A)
def inverseQuarter (A : Matrix C C ℂ) : Matrix C C ℂ :=
  cfc (fun x : ℝ => x⁻¹) (quarterRoot A)
def quarterSupport (A : Matrix C C ℂ) : Matrix C C ℂ := quarterRoot A * inverseQuarter A

lemma quarter_positive (A : Matrix C C ℂ) : (quarterRoot A).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (CFC.sqrt A))

end RowColumn.MatrixState

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_SignedWords
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace RowColumn.Signed
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
variable (odd : C → Prop) [DecidablePred odd]

/-- Words with exactly k odd entries. This is the k-parity sector of the
literal signed slot space, not a formal unknown representation. -/
abbrev Words (k : ℕ) := {w : S → C // Fintype.card {x : S // odd (w x)} = k}


variable {odd} {k : ℕ}

/-- Odd slots of a word, genuinely a subset of the board slots. -/
abbrev OddSlots (w : Words (S := S) odd k) := {x : S // odd (w.1 x)}

def relabelOddEquiv (g : Equiv.Perm S) (w : S → C) :
    {x : S // odd (w x)} ≃ {x : S // odd (w (g⁻¹ x))} where
  toFun x := ⟨g x.1, by simpa using x.2⟩
  invFun x := ⟨g⁻¹ x.1, x.2⟩
  left_inv := by intro x; ext; simp
  right_inv := by intro x; ext; simp

def actWord (g : Equiv.Perm S) (w : Words (S := S) odd k) : Words (S := S) odd k :=
  ⟨fun x => w.1 (g⁻¹ x), (Fintype.card_congr (relabelOddEquiv g w.1)).symm.trans w.2⟩

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
@[simp] lemma actWord_apply (g : Equiv.Perm S) (w : Words (S := S) odd k) (x : S) :
    (actWord g w).1 x = w.1 (g⁻¹ x) := rfl

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
@[simp] lemma actWord_one (w : Words (S := S) odd k) : actWord 1 w = w := by
  apply Subtype.ext
  funext x
  rfl

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma actWord_mul (g h : Equiv.Perm S) (w : Words (S := S) odd k) :
    actWord (g * h) w = actWord g (actWord h w) := by
  apply Subtype.ext
  funext x
  simp [actWord, mul_inv_rev]

/-- Canonical frames choose the odd-slot orientation. Different choices conjugate
by a diagonal sign; the signed action is exactly reordering the odd slots. -/
def oddFrame (w : Words (S := S) odd k) : OddSlots w ≃ Fin k :=
  Fintype.equivFinOfCardEq w.2

def oddPerm (g : Equiv.Perm S) (w : Words (S := S) odd k) : Equiv.Perm (Fin k) :=
  (oddFrame w).symm |>.trans ((relabelOddEquiv g w.1).trans (oddFrame (actWord g w)))

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddFrame_congr {w v : Words (S := S) odd k} (he : w = v)
    (x : S) (hx : odd (w.1 x)) (hv : odd (v.1 x)) :
    oddFrame w ⟨x, hx⟩ = oddFrame v ⟨x, hv⟩ := by
  subst v
  rfl

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
@[simp] lemma oddPerm_one (w : Words (S := S) odd k) : oddPerm 1 w = 1 := by
  apply Equiv.ext
  intro i
  change oddFrame (actWord 1 w) ⟨(oddFrame w).symm i, _⟩ = i
  have h := oddFrame_congr (actWord_one w) ((oddFrame w).symm i).1
    (show odd ((actWord 1 w).1 ((oddFrame w).symm i)) from ((oddFrame w).symm i).2)
    ((oddFrame w).symm i).2
  exact h.trans ((oddFrame w).apply_symm_apply i)

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddPerm_mul (g h : Equiv.Perm S) (w : Words (S := S) odd k) :
    oddPerm (g * h) w = oddPerm g (actWord h w) * oddPerm h w := by
  apply Equiv.ext
  intro i
  change oddFrame (actWord (g * h) w)
    ((relabelOddEquiv (g * h) w.1) ((oddFrame w).symm i)) =
    oddFrame (actWord g (actWord h w))
      ((relabelOddEquiv g (actWord h w).1)
        ((oddFrame (actWord h w)).symm
          (oddFrame (actWord h w) ((relabelOddEquiv h w.1) ((oddFrame w).symm i)))))
  erw [Equiv.symm_apply_apply]
  exact oddFrame_congr (actWord_mul g h w) _ _ _

def wordsEquiv (g : Equiv.Perm S) : Equiv.Perm (Words (S := S) odd k) where
  toFun := actWord g
  invFun := actWord g⁻¹
  left_inv := by intro w; rw [← actWord_mul, inv_mul_cancel, actWord_one]
  right_inv := by intro w; rw [← actWord_mul, mul_inv_cancel, actWord_one]

/-- Signed slot action in the orthonormal word basis. It reorders the odd
subsequence, and does not introduce a sign for even slots. -/
def signedMap (g : Equiv.Perm S) :
    EuclideanSpace ℂ (Words (S := S) odd k) →ₗ[ℂ] EuclideanSpace ℂ (Words (S := S) odd k) where
  toFun v := WithLp.toLp 2 (fun w => permSign (oddPerm g⁻¹ w) * v (actWord g⁻¹ w))
  map_add' := by intro v z; ext w; simp [mul_add]
  map_smul' := by intro a v; ext w; simp [mul_left_comm]

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
@[simp] lemma signedMap_apply (g : Equiv.Perm S)
    (v : EuclideanSpace ℂ (Words (S := S) odd k)) (w : Words (S := S) odd k) :
    signedMap g v w = permSign (oddPerm g⁻¹ w) * v (actWord g⁻¹ w) := rfl

/-- The signs genuinely compose; no group-action relation is assumed. -/
def representation : Representation ℂ (Equiv.Perm S) (EuclideanSpace ℂ (Words (S := S) odd k)) where
  toFun := signedMap
  map_one' := by ext v w; simp
  map_mul' g h := by
    ext v w
    simp only [signedMap_apply, Module.End.mul_apply, mul_inv_rev, oddPerm_mul,
      permSign_mul, actWord_mul, mul_assoc]
    ring

end RowColumn.Signed

namespace RowColumn.Signed
open scoped BigOperators Classical
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

def wordVector (w : Words (S := S) odd k) : EuclideanSpace ℂ (Words (S := S) odd k) :=
  WithLp.toLp 2 (fun z => if z = w then 1 else 0)

end RowColumn.Signed

namespace RowColumn.Signed
open CubeShuffle.Specht
open scoped BigOperators Classical

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

variable {L : Type*} [Fintype L] [DecidableEq L] (line : S → L)

abbrev lineRepresentation :=
  (representation (S := S) (odd := odd) (k := k)).comp (RowColumn.lineGroup line).subtype

end RowColumn.Signed

namespace RowColumn.WordOrbits

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]

/-- A complete invariant of the simultaneous permutation orbit of finitely
many words: the counts of their joint symbols. -/
def counts (f : S → A) : A → Fin (Fintype.card S + 1) := fun a =>
  ⟨Fintype.card {x : S // f x = a},
    Nat.lt_succ_of_le (Fintype.card_subtype_le (fun x => f x = a))⟩

omit [Fintype A] in
lemma same_counts_permutation (f g : S → A) (he : counts f = counts g) :
    ∃ p : Equiv.Perm S, ∀ x, g (p x) = f x := by
  have hc (a : A) : Fintype.card {x : S // f x = a} = Fintype.card {x : S // g x = a} :=
    congrArg (fun z : A → Fin (Fintype.card S + 1) => (z a).1) he
  let e (a : A) : {x : S // f x = a} ≃ {x : S // g x = a} := Fintype.equivOfCardEq (hc a)
  let p : Equiv.Perm S := (Equiv.sigmaFiberEquiv f).symm |>.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g))
  refine ⟨p, ?_⟩
  intro x
  change g ((e (f x) ⟨x, rfl⟩).1) = f x
  exact (e (f x) ⟨x, rfl⟩).2

end RowColumn.WordOrbits

namespace RowColumn.Signed
open CubeShuffle.Specht
open scoped BigOperators Classical

variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] {odd : C → Prop} [DecidablePred odd] {k : ℕ}
  (line : S → L)

abbrev PairCountIndex := (L × C × C) → Fin (Fintype.card S + 1)

def pairCounts (wv : Words (S := S) odd k × Words (S := S) odd k) :
    PairCountIndex (S := S) (C := C) (L := L) :=
  RowColumn.WordOrbits.counts (fun x => (line x, wv.1.1 x, wv.2.1 x))

/-- Record one matrix coefficient per joint-symbol contingency table. Zero
coefficients in these representatives force every coefficient to be zero. -/
def commutantData :
    Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line) →ₗ[ℂ]
        (PairCountIndex (S := S) (C := C) (L := L) → ℂ) where
  toFun T a := if ha : ∃ wv, pairCounts (odd := odd) (k := k) line wv = a then
      T (wordVector (Classical.choose ha).2) (Classical.choose ha).1 else 0
  map_add' T U := by
    funext a
    dsimp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' z T := by
    funext a
    dsimp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

end RowColumn.Signed

end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.MatrixState_Postselection
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical Nat
namespace RowColumn.WordOrbits
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- All transporters between two words are exactly the independent bijections
between corresponding color fibres. -/
def transporterEquiv (a b : S → A) :
    {p : Equiv.Perm S // ∀ x, b (p x) = a x} ≃
      (∀ c : A, {x : S // a x = c} ≃ {x : S // b x = c}) where
  toFun p c :=
    { toFun := fun x => ⟨p.1 x.1, (p.2 x.1).trans x.2⟩
      invFun := fun y => ⟨p.1.symm y.1, by
        have h := p.2 (p.1.symm y.1)
        rw [Equiv.apply_symm_apply] at h
        exact h.symm.trans y.2⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp }
  invFun f := ⟨(Equiv.sigmaFiberEquiv a).symm |>.trans
    ((Equiv.sigmaCongrRight f).trans (Equiv.sigmaFiberEquiv b)), fun x => (f (a x) ⟨x,rfl⟩).2⟩
  left_inv := by intro p; apply Subtype.ext; ext x; rfl
  right_inv := by
    intro f
    funext c
    apply Equiv.ext
    rintro ⟨x,rfl⟩
    apply Subtype.ext
    rfl

end RowColumn.WordOrbits

namespace RowColumn.WordOrbits
open scoped BigOperators Classical Nat

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

omit [DecidableEq S] in
lemma prod_by_counts {M : Type*} [CommMonoid M] (w : S → A) (f : A → M) :
    (∏ x : S, f (w x)) = ∏ c : A, f c ^ (counts w c).val := by
  rw [← Fintype.prod_fiberwise w]
  apply Finset.prod_congr rfl
  intro c _
  simp only [counts]
  simp only [show ∀ x : {x : S // w x = c}, f (w x.1) = f c from fun x => congrArg f x.2]
  simp

end RowColumn.WordOrbits

namespace RowColumn.WordOrbits
open scoped BigOperators Classical Nat
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

def typeMass (a : S → A) (q : A → Fin (Fintype.card S + 1)) : ℕ :=
  Fintype.card {w : S → A // counts w = q} * ∏ c, (counts a c).val ^ (q c).val

end RowColumn.WordOrbits

namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

def empiricalAmplitude (a : S → A) (c : A) : ℂ :=
  Real.sqrt ((counts a c).val / (Fintype.card S : ℝ))

def tensorVector (z : A → ℂ) (w : S → A) : ℂ := ∏ x : S, z (w x)

end RowColumn.Postselection


noncomputable section
open scoped BigOperators Classical
namespace RowColumn.Postselection
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

abbrev CountIndex (A : Type*) (n : ℕ) := A → Fin (n+1)
abbrev Phases (A : Type*) (n : ℕ) := A → ZMod (n+1)

def countCharacter (q : CountIndex A n) : AddChar (Phases A n) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom
    { toFun := fun θ => ∑ c, ((q c).val : ZMod (n+1)) * θ c
      map_zero' := by simp
      map_add' := by intros; simp [mul_add, Finset.sum_add_distrib] }

@[simp] lemma countCharacter_single (q : CountIndex A n) (a : A) :
    countCharacter q (Pi.single a 1) = ZMod.stdAddChar ((q a).val : ZMod (n+1)) := by
  simp [countCharacter, Pi.single_apply]

lemma countCharacter_injective : Function.Injective (countCharacter (A := A) (n := n)) := by
  intro q r h
  funext a
  have he := congrArg (fun f : AddChar (Phases A n) ℂ => f (Pi.single a 1)) h
  simp only [countCharacter_single] at he
  have hc := ZMod.injective_stdAddChar he
  change ((q a).val : ZMod (n+1)) = (r a).val at hc
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (q a).isLt,
    Nat.mod_eq_of_lt (r a).isLt] at hc
  exact Fin.ext hc

lemma character_orthogonality (q r : CountIndex A n) :
    (∑ θ : Phases A n, countCharacter q θ * (starRingEnd ℂ) (countCharacter r θ)) =
      if q = r then (Fintype.card (Phases A n) : ℂ) else 0 := by
  have he (θ : Phases A n) : (countCharacter q - countCharacter r) θ =
      countCharacter q θ * (starRingEnd ℂ) (countCharacter r θ) := by
    rw [AddChar.sub_apply, AddChar.map_neg_eq_inv,
      Complex.inv_eq_conj ((countCharacter r).norm_apply θ)]
  simp_rw [← he]
  rw [AddChar.sum_eq_ite]
  simp only [sub_eq_zero, countCharacter_injective.eq_iff]

end RowColumn.Postselection
namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

abbrev Types := CountIndex A (Fintype.card S)
def typeSize (q : Types (S := S) (A := A)) := Fintype.card {w : S → A // counts w = q}
def typeSum (x : (S → A) → ℂ) (q : Types (S := S) (A := A)) : ℂ :=
  ∑ w : {w : S → A // counts w = q}, x w.1

def typeAverage (x : (S → A) → ℂ) (w : S → A) : ℂ :=
  typeSum x (counts w) / (typeSize (counts w) : ℂ)

def typeRepresentative (a₀ : S → A) (q : Types (S := S) (A := A)) : S → A :=
  if h : Nonempty {w : S → A // counts w = q} then h.some.1 else a₀

end RowColumn.Postselection

namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits

lemma char_sum {I G : Type*} [AddCommMonoid G] (ψ : AddChar G ℂ)
    (s : Finset I) (f : I → G) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => simp only [Finset.sum_cons, Finset.prod_cons, ψ.map_add_eq_mul, ih]

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

def typeAmplitude (z : A → ℂ) (q : Types (S := S) (A := A)) : ℂ :=
  ∏ c, z c ^ (q c).val

def twistedAmplitude (a : S → A) (θ : Phases A (Fintype.card S)) (c : A) : ℂ :=
  empiricalAmplitude a c * ZMod.stdAddChar (θ c)

omit [DecidableEq S] [DecidableEq A] in
lemma countCharacter_eq_prod (q : Types (S := S) (A := A)) (θ : Phases A (Fintype.card S)) :
    countCharacter q θ = ∏ c, ZMod.stdAddChar (θ c) ^ (q c).val := by
  change ZMod.stdAddChar (∑ c, ((q c).val : ZMod (Fintype.card S + 1)) * θ c) = _
  rw [char_sum]
  apply Finset.prod_congr rfl
  intro c _
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

end RowColumn.Postselection

namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- Truncating purification letters preserves positivity after partial trace.
It is how the postselection mixture is constrained to even one-slot states. -/
def truncateAmplitude (good : A → Prop) [DecidablePred good] (z : A → ℂ) : A → ℂ :=
  fun c => if good c then z c else 0

end RowColumn.Postselection
namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

def pairWordsEquiv : (S → C × C) ≃ (S → C) × (S → C) where
  toFun a := (fun i => (a i).1, fun i => (a i).2)
  invFun w := fun i => (w.1 i,w.2 i)
  left_inv := by intro a; rfl
  right_inv := by intro w; rfl

def purificationVector (B : (S → C) → (S → C) → ℂ) (a : S → C × C) : ℂ :=
  B (fun i => (a i).1) (fun i => (a i).2)

def purificationTest (x : (S → C) → ℂ) (v : S → C) (a : S → C × C) : ℂ :=
  if (fun i => (a i).2) = v then x (fun i => (a i).1) else 0

def purifierTrace (B : (S → C) → (S → C) → ℂ) : ℝ :=
  ∑ w : S → C, ∑ v : S → C, Complex.normSq (B w v)

end RowColumn.Postselection

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J : Type*} [Fintype I] [DecidableEq I]

lemma sqrt_commute (A T : Matrix I I ℂ) (_ : A.PosSemidef) (h : Commute A T) :
    Commute (CFC.sqrt A) T := by
  rw [CFC.sqrt_eq_cfc]
  exact h.cfc_nnreal _

lemma commute_diagonal_iff (A : Matrix I I ℂ) (d : I → ℂ) :
    Commute A (Matrix.diagonal d) ↔ ∀ i j, A i j * d j = d i * A i j := by
  change _ = _ ↔ _
  constructor
  · intro h i j
    simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul] using
      congrArg (fun M : Matrix I I ℂ => M i j) h
  · intro h; ext i j; simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul] using h i j

lemma sqrt_block_supported [DecidableEq J] (b : I → J)
    (A : Matrix I I ℂ) (hA : A.PosSemidef) (h : ∀ i j, b i ≠ b j → A i j = 0) :
    ∀ i j, b i ≠ b j → CFC.sqrt A i j = 0 := by
  intro i j hij
  let d : I → ℂ := fun k => if b k = b i then 1 else 0
  have hc : Commute A (Matrix.diagonal d) := by
    apply (commute_diagonal_iff A d).mpr
    intro k l
    by_cases he : b k = b l
    · simp [d, he, mul_comm]
    · simp [h k l he]
  have hs := (commute_diagonal_iff (CFC.sqrt A) d).mp (sqrt_commute A _ hA hc) i j
  simpa [d, Ne.symm hij] using hs.symm

/-- Bilinear-coordinate quadratic form. Complex conjugation is placed in the
second coordinate, matching the purification formulas used below. -/
def quadratic (A : Matrix I I ℂ) (x : I → ℂ) : ℝ :=
  (∑ i, ∑ j, A i j * x i * star (x j)).re

def factorQuadratic (B : Matrix I I ℂ) (x : I → ℂ) : ℝ :=
  ∑ v, Complex.normSq (∑ w, B w v * x w)

end RowColumn.MatrixState

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

def tensorMatrix (M : S → Matrix C C ℂ) : Matrix (S → C) (S → C) ℂ :=
  fun w v => ∏ i, M i (w i) (v i)

omit [DecidableEq C] in
lemma tensorMatrix_mul (A B : S → Matrix C C ℂ) :
    tensorMatrix A * tensorMatrix B = tensorMatrix (fun i => A i * B i) := by
  ext w v
  simp only [tensorMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i : S => fun c : C => A i (w i) c * B i c (v i))).symm

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma tensorMatrix_star (A : S → Matrix C C ℂ) :
    (tensorMatrix A).conjTranspose = tensorMatrix (fun i => (A i).conjTranspose) := by
  ext w v
  simp [tensorMatrix, Matrix.conjTranspose_apply, star_prod]

omit [DecidableEq S] [Fintype C] in
lemma tensorMatrix_one : tensorMatrix (fun _ : S => (1 : Matrix C C ℂ)) = 1 := by
  ext w v
  by_cases he : w = v
  · subst v; simp [tensorMatrix]
  · have hn : ∃ i, w i ≠ v i := Function.ne_iff.mp he
    obtain ⟨i,hi⟩ := hn
    rw [Matrix.one_apply_ne he]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

def letterMatrix (z : C × C → ℂ) : Matrix C C ℂ := fun c d => z (c,d)

/-- A purification letter z is an actual one-slot substate after partial trace. -/
def gramState (z : C × C → ℂ) : Matrix C C ℂ :=
  letterMatrix z * (letterMatrix z).conjTranspose

end RowColumn.MatrixState

namespace RowColumn.Postselection
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open MatrixState WordOrbits
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

def reindexWord (p : Equiv.Perm S) : Equiv.Perm (S → C) where
  toFun w := fun i => w (p i)
  invFun w := fun i => w (p.symm i)
  left_inv := by intro w; ext i; simp
  right_inv := by intro w; ext i; simp

end RowColumn.Postselection

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Sectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator MatrixOrder
namespace RowColumn.MatrixState
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

def evenAlgebra (odd : C → Prop) : StarSubalgebra ℂ (Matrix C C ℂ) where
  carrier := {M | ∀ c d, ¬(odd c ↔ odd d) → M c d=0}
  zero_mem' := by intro c d h; rfl
  add_mem' := by intro M N hM hN c d h; change M c d + N c d=0; simp only [hM c d h,hN c d h,add_zero]
  mul_mem' := by
    intro M N hM hN c d h
    change (∑ e, M c e * N e d)=0
    apply Finset.sum_eq_zero
    intro e _
    change M c e * N e d=0
    by_cases he : odd c ↔ odd e
    · rw [hN e d (fun hd => h (he.trans hd)), mul_zero]
    · rw [hM c e he, zero_mul]
  one_mem' := by
    intro c d h
    exact Matrix.one_apply_ne (fun he => h (he ▸ Iff.rfl))
  algebraMap_mem' := by
    intro z c d h
    have hcd : c≠d := fun he => h (he ▸ Iff.rfl)
    simp [Algebra.algebraMap_eq_smul_one, hcd]
  star_mem' := by
    intro M hM c d h
    change star (M d c)=0
    rw [hM d c (fun hh => h hh.symm), star_zero]

omit [DecidableEq S] in
lemma tensorMatrix_even_support (odd : C → Prop) (M : S → Matrix C C ℂ)
    (hM : ∀ i, M i ∈ evenAlgebra odd) (w v : S → C)
    (h : ¬ ∀ i, odd (w i) ↔ odd (v i)) : tensorMatrix M w v=0 := by
  obtain ⟨i,hi⟩ := not_forall.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hM i (w i) (v i) hi)

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddCount_eq (odd : C → Prop) [DecidablePred odd] (w v : S → C)
    (h : ∀ i, odd (w i) ↔ odd (v i)) :
    Fintype.card {i : S // odd (w i)} = Fintype.card {i : S // odd (v i)} := by
  exact Fintype.card_congr (Equiv.subtypeEquivRight h)

def sectorTensor (odd : C → Prop) [DecidablePred odd] (k : ℕ) (M : S → Matrix C C ℂ) :
    Matrix (Signed.Words (S := S) odd k) (Signed.Words (S := S) odd k) ℂ :=
  (tensorMatrix M).submatrix Subtype.val Subtype.val

lemma sectorTensor_mul (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M N : S → Matrix C C ℂ) (hM : ∀ i, M i ∈ evenAlgebra odd) :
    sectorTensor odd k (fun i => M i * N i) = sectorTensor odd k M * sectorTensor odd k N := by
  ext w v
  change tensorMatrix (fun i => M i*N i) w.1 v.1 = _
  rw [← tensorMatrix_mul]
  change (∑ z : S → C, tensorMatrix M w.1 z * tensorMatrix N z v.1) =
    ∑ z : Signed.Words (S := S) odd k, tensorMatrix M w.1 z.1 * tensorMatrix N z.1 v.1
  have hz : (∑ z : {z : S → C // ¬ Fintype.card {i : S // odd (z i)}=k},
      tensorMatrix M w.1 z.1 * tensorMatrix N z.1 v.1)=0 := by
    apply Finset.sum_eq_zero
    intro z _
    rw [tensorMatrix_even_support odd M hM w.1 z.1, zero_mul]
    intro hh
    exact z.2 ((oddCount_eq odd w.1 z.1 hh).symm.trans w.2)
  have he := Fintype.sum_subtype_add_sum_subtype
    (fun z : S → C => Fintype.card {i : S // odd (z i)}=k)
    (fun z : S → C => tensorMatrix M w.1 z * tensorMatrix N z v.1)
  rw [hz, add_zero] at he
  exact he.symm

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma sectorTensor_star (odd : C → Prop) [DecidablePred odd] (k : ℕ) (M : S → Matrix C C ℂ) :
    sectorTensor odd k (fun i => star (M i)) = star (sectorTensor odd k M) := by
  unfold sectorTensor
  change (tensorMatrix (fun i => (M i).conjTranspose)).submatrix Subtype.val Subtype.val = _
  rw [← tensorMatrix_star]
  rfl

omit [DecidableEq S] [Fintype C] in
lemma sectorTensor_one (odd : C → Prop) [DecidablePred odd] (k : ℕ) :
    sectorTensor odd k (fun _ : S => (1 : Matrix C C ℂ))=1 := by
  rw [sectorTensor, tensorMatrix_one]
  exact Matrix.submatrix_one Subtype.val Subtype.val_injective

def sectorPowerHom (odd : C → Prop) [DecidablePred odd] (k : ℕ) :
    evenAlgebra odd →⋆* Matrix (Signed.Words (S := S) odd k) (Signed.Words (S := S) odd k) ℂ where
  toFun M := sectorTensor odd k (fun _ : S => M.val)
  map_one' := sectorTensor_one odd k
  map_mul' M _ := sectorTensor_mul odd k _ _ (fun _ => M.property)
  map_star' _ := sectorTensor_star odd k _

end RowColumn.MatrixState

noncomputable section

noncomputable section
namespace RowColumn.FiniteStarAlgebra
variable {R A G : Type*} [CommSemiring R] [StarRing R] [Ring A] [Algebra R A]
  [StarRing A] [StarModule R A] [Group G]

def unitarySpan (u : G →* unitary A) : StarSubalgebra R A where
  __ := Algebra.adjoin R (Set.range fun g : G => (u g : A))
  star_mem' := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨g,rfl⟩ := ha
      apply Algebra.subset_adjoin
      refine ⟨g⁻¹,?_⟩
      change (u g⁻¹ : A) = star (u g : A)
      rw [map_inv]
      rfl
    | algebraMap r => rw [← algebraMap_star_comm]; exact (Algebra.adjoin R _).algebraMap_mem _
    | add a b ha hb iha ihb => rw [star_add]; exact (Algebra.adjoin R _).add_mem iha ihb
    | mul a b ha hb iha ihb => rw [star_mul]; exact (Algebra.adjoin R _).mul_mem ihb iha

lemma unitarySpan_mem (u : G →* unitary A) (g : G) : (u g : A) ∈ unitarySpan (R := R) u :=
  Algebra.subset_adjoin ⟨g,rfl⟩

def unitarySpanHom (u : G →* unitary A) : G →* unitary (unitarySpan (R := R) u) where
  toFun g := ⟨⟨(u g : A),unitarySpan_mem u g⟩,by
    constructor <;> apply Subtype.ext
    · exact (u g).property.1
    · exact (u g).property.2⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; change (u 1 : A)=1; simp
  map_mul' g h := by apply Subtype.ext; apply Subtype.ext; change (u (g*h) : A)=(u g : A)*(u h : A); simp

end RowColumn.FiniteStarAlgebra

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator
open ComplexConjugate
namespace RowColumn.MatrixState

def discreteContinuousHom (J : Type*) [TopologicalSpace J] [DiscreteTopology J] :
    (J → ℂ) →⋆ₐ[ℂ] C(J,ℂ) where
  toFun f := ⟨f,continuous_of_discreteTopology⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def precompFunctionHom {J K : Type*} (f : J → K) : (K → ℂ) →⋆ₐ[ℂ] (J → ℂ) where
  toFun g := g ∘ f
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

lemma sum_single_function {J : Type*} [Fintype J] [DecidableEq J] (z : J → ℂ) :
    (∑ i : J, z i • (Pi.single i 1 : J → ℂ)) = z := by
  ext j
  simp [Pi.single_apply]

lemma function_unitary {J : Type*} (z : J → ℂ) (hz : ∀ i, ‖z i‖=1) : z ∈ unitary (J → ℂ) := by
  constructor <;> ext i
  · change conj (z i)*z i=1
    rw [Complex.conj_mul', hz i]
    norm_num
  · change z i*conj (z i)=1
    rw [Complex.mul_conj', hz i]
    norm_num

/-- A genuine finite spectral phase family inside the prescribed closed
star algebra. In the application this is the even one-slot matrix algebra. -/
theorem exists_spectral_phase_family {C : Type*} [Fintype C] [DecidableEq C]
    (M : Matrix C C ℂ) (hM : M.IsHermitian)
    (K : StarSubalgebra ℂ (Matrix C C ℂ)) (hK : IsClosed (K : Set (Matrix C C ℂ)))
    (hMK : M ∈ K) :
    ∃ (d : ℕ) (P : Fin d → Matrix C C ℂ) (z : Fin d → ℂ),
      (∑ i, z i • P i) = M ∧ (∀ i, P i ∈ K) ∧
      ∀ θ : Fin d → ℂ, (∀ i, ‖θ i‖=1) → (∑ i, θ i • P i) ∈ unitary (Matrix C C ℂ) := by
  have hfin : (spectrum ℂ M).Finite := by
    rw [hM.spectrum_eq_image_range]
    exact (Set.finite_range hM.eigenvalues).image _
  let J := spectrum ℂ M
  let : Fintype J := hfin.fintype
  let : DiscreteTopology J := inferInstance
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let ψ := (cfcHom hM.isSelfAdjoint.isStarNormal (R := ℂ)).comp
    ((discreteContinuousHom J).comp (precompFunctionHom e))
  let P (i : Fin (Fintype.card J)) : Matrix C C ℂ := ψ (Pi.single i 1)
  let z (i : Fin (Fintype.card J)) : ℂ := (e.symm i).val
  have hsum (f : Fin (Fintype.card J) → ℂ) : ∑ i, f i • P i = ψ f := by
    simp only [P, ← map_smul, ← map_sum, sum_single_function]
  refine ⟨Fintype.card J,P,z,?_,?_,?_⟩
  · rw [hsum]
    have he : ((discreteContinuousHom J).comp (precompFunctionHom e)) z =
        (ContinuousMap.id ℂ).restrict (spectrum ℂ M) := by
      ext j
      exact congrArg Subtype.val (e.symm_apply_apply j)
    change cfcHom hM.isSelfAdjoint.isStarNormal (((discreteContinuousHom J).comp (precompFunctionHom e)) z) = M
    rw [he]
    exact cfcHom_id _
  · intro i
    apply StarAlgebra.elemental.le_of_mem hK hMK
    exact cfcHom_mem_elemental hM.isSelfAdjoint.isStarNormal _
  · intro θ hθ
    rw [hsum]
    exact Unitary.map_mem ψ (function_unitary θ hθ)

end RowColumn.MatrixState

noncomputable section
open scoped BigOperators Classical
namespace RowColumn.MatrixState
open WordOrbits Postselection
variable {S C J : Type*} [Fintype S] [DecidableEq S]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]

omit [Fintype C] [DecidableEq C] [DecidableEq J] in
lemma tensorMatrix_linear_combination (P : J → Matrix C C ℂ) (z : J → ℂ) :
    tensorMatrix (fun _ : S => ∑ j, z j • P j) =
      ∑ w : S → J, (∏ i, z (w i)) • tensorMatrix (fun i => P (w i)) := by
  ext a b
  simp only [tensorMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact Finset.prod_mul_distrib

def typeTensor (P : J → Matrix C C ℂ) (q : Types (S := S) (A := J)) :
    Matrix (S → C) (S → C) ℂ :=
  ∑ w : {w : S → J // counts w = q}, tensorMatrix (fun i => P (w.1 i))

omit [Fintype C] [DecidableEq C] in
lemma tensorMatrix_by_type (P : J → Matrix C C ℂ) (z : J → ℂ) :
    tensorMatrix (fun _ : S => ∑ j, z j • P j) =
      ∑ q : Types (S := S) (A := J), typeAmplitude z q • typeTensor P q := by
  rw [tensorMatrix_linear_combination]
  simp_rw [prod_by_counts _ z]
  change (∑ w : S → J, typeAmplitude z (counts w) • tensorMatrix (fun i => P (w i))) = _
  rw [← Fintype.sum_fiberwise counts (fun w : S → J =>
    typeAmplitude z (counts w) • tensorMatrix (fun i => P (w i)))]
  apply Finset.sum_congr rfl
  intro q _
  simp only [show ∀ w : {w : S → J // counts w = q}, counts w.1=q from fun w => w.2]
  exact (Finset.smul_sum).symm

def phaseMatrix (P : J → Matrix C C ℂ) (θ : Phases J (Fintype.card S)) : Matrix C C ℂ :=
  ∑ j, ZMod.stdAddChar (θ j) • P j

omit [Fintype C] [DecidableEq C] in
lemma tensorMatrix_phase (P : J → Matrix C C ℂ) (θ : Phases J (Fintype.card S)) :
    tensorMatrix (fun _ : S => phaseMatrix P θ) =
      ∑ q : Types (S := S) (A := J), countCharacter q θ • typeTensor P q := by
  rw [phaseMatrix, tensorMatrix_by_type]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  exact (countCharacter_eq_prod q θ).symm

omit [Fintype C] [DecidableEq C] in
lemma typeTensor_fourier (P : J → Matrix C C ℂ) (q : Types (S := S) (A := J)) :
    (∑ θ : Phases J (Fintype.card S), star (countCharacter q θ) •
      tensorMatrix (fun _ : S => phaseMatrix P θ)) =
      (Fintype.card (Phases J (Fintype.card S)) : ℂ) • typeTensor P q := by
  simp_rw [tensorMatrix_phase, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have he (r : Types (S := S) (A := J)) :
      (∑ θ : Phases J (Fintype.card S), star (countCharacter q θ) * countCharacter r θ) =
        if r=q then (Fintype.card (Phases J (Fintype.card S)) : ℂ) else 0 := by
    simpa only [starRingEnd_apply, mul_comm] using character_orthogonality r q
  simp_rw [he]
  simp

omit [Fintype C] [DecidableEq C] in
/-- Every identical tensor of a linear combination of a finite family lies
in the span of its finite phase tensors. Applied to an even spectral family,
all the spanning tensors are genuine global even unitaries. -/
theorem tensorMatrix_mem_phase_span (P : J → Matrix C C ℂ) (z : J → ℂ) :
    tensorMatrix (fun _ : S => ∑ j, z j • P j) ∈
      Submodule.span ℂ (Set.range fun θ : Phases J (Fintype.card S) =>
        tensorMatrix (fun _ : S => phaseMatrix P θ)) := by
  let K := Submodule.span ℂ (Set.range fun θ : Phases J (Fintype.card S) =>
        tensorMatrix (fun _ : S => phaseMatrix P θ))
  have hm (q : Types (S := S) (A := J)) : typeTensor P q ∈ K := by
    have hcard : (Fintype.card (Phases J (Fintype.card S)) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [← one_smul ℂ (typeTensor P q), ← inv_mul_cancel₀ hcard, mul_smul,
      ← typeTensor_fourier P q]
    apply K.smul_mem
    apply K.sum_mem
    intro θ _
    exact K.smul_mem _ (Submodule.subset_span ⟨θ,rfl⟩)
  rw [tensorMatrix_by_type]
  exact K.sum_mem (fun q _ => K.smul_mem _ (hm q))

end RowColumn.MatrixState

namespace RowColumn.MatrixState
open Signed WordOrbits Postselection FiniteStarAlgebra
open scoped BigOperators Classical Matrix.Norms.L2Operator MatrixOrder
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  (odd : C → Prop) [DecidablePred odd] (k : ℕ)

abbrev Sector := EuclideanSpace ℂ (Words (S := S) odd k)

def sectorUnitary : unitary (evenAlgebra odd) →* unitary (Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) :=
  ((Unitary.map (StarMonoidHom.ofClass (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)))).comp
    (Unitary.map (sectorPowerHom (S := S) odd k))).toMonoidHom

def sectorAlgebra : StarSubalgebra ℂ (Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) :=
  unitarySpan (sectorUnitary (S := S) odd k)

def tensorRestriction : Matrix (S → C) (S → C) ℂ →ₗ[ℂ]
    (Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) :=
  (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.comp
    ({ toFun M := M.submatrix Subtype.val Subtype.val
       map_add' _ _ := rfl
       map_smul' _ _ := by ext w v; rfl } :
        Matrix (S → C) (S → C) ℂ →ₗ[ℂ] Matrix (Words (S := S) odd k) (Words (S := S) odd k) ℂ)

/-- Identical even positive tensors really belong to the finite algebra of
actual global even unitary tensors. This is a proved phase-Fourier identity,
not a commutant-duality assumption. -/
theorem sectorTensor_mem_algebra (M : Matrix C C ℂ) (hM : M.IsHermitian) (heven : M ∈ evenAlgebra odd) :
    (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)) (sectorTensor odd k (fun _ : S => M)) ∈ sectorAlgebra (S := S) odd k := by
  have hclosed : IsClosed (evenAlgebra odd : Set (Matrix C C ℂ)) :=
    (evenAlgebra odd).toSubalgebra.toSubmodule.closed_of_finiteDimensional
  obtain ⟨d,P,z,he,hP,hU⟩ := exists_spectral_phase_family M hM (evenAlgebra odd) hclosed heven
  let F := tensorRestriction (S := S) odd k
  have ha (θ : Phases (Fin d) (Fintype.card S)) : F (tensorMatrix (fun _ : S => phaseMatrix (S := S) P θ)) ∈ sectorAlgebra (S := S) odd k := by
    have hphase : phaseMatrix (S := S) P θ ∈ evenAlgebra odd :=
      (evenAlgebra odd).sum_mem (fun i _ => (evenAlgebra odd).smul_mem (hP i) _)
    have hunit : phaseMatrix (S := S) P θ ∈ unitary (Matrix C C ℂ) :=
      hU _ (fun i => AddChar.norm_apply _ _)
    let U : unitary (evenAlgebra odd) := ⟨⟨phaseMatrix (S := S) P θ,hphase⟩,by
      constructor <;> apply Subtype.ext
      · exact hunit.1
      · exact hunit.2⟩
    exact unitarySpan_mem (R := ℂ) (sectorUnitary (S := S) odd k) U
  have hs : Submodule.span ℂ (Set.range fun θ : Phases (Fin d) (Fintype.card S) =>
      tensorMatrix (fun _ : S => phaseMatrix (S := S) P θ)) ≤
        (sectorAlgebra (S := S) odd k).toSubmodule.comap F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨θ,rfl⟩
    exact ha θ
  have hh := hs (tensorMatrix_mem_phase_span (S := S) P z)
  rw [he] at hh
  exact hh

end RowColumn.MatrixState

namespace RowColumn.MatrixState
open Signed WordOrbits Postselection FiniteStarAlgebra
open scoped BigOperators Classical Matrix.Norms.L2Operator MatrixOrder
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  (odd : C → Prop) [DecidablePred odd] (k : ℕ)

abbrev GlobalTypes := Types (S := S) (A := C × C)

def sectorTypeMatrix (q : GlobalTypes (S := S) (C := C)) :
    Matrix (Words (S := S) odd k) (Words (S := S) odd k) ℂ :=
  fun w v => if counts (fun i => (w.1 i,v.1 i))=q then 1 else 0

end RowColumn.MatrixState

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.MatrixState_Whitening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {C L : Type*} [Fintype C] [DecidableEq C] [Fintype L]

def stateMean (p : L → ℝ) (S : L → Matrix C C ℂ) : Matrix C C ℂ := ∑ i, p i • S i

def whitenState (A S : Matrix C C ℂ) : Matrix C C ℂ := inverseQuarter A * S * inverseQuarter A

lemma sqrt_even (odd : C → Prop) (A : Matrix C C ℂ) (hA : A.PosSemidef)
    (he : A ∈ evenAlgebra odd) : CFC.sqrt A ∈ evenAlgebra odd := by
  intro c d h
  exact sqrt_block_supported odd A hA
    (fun c d hh => he c d (fun hcd => hh (propext hcd))) c d
    (fun he => h (Iff.of_eq he))

lemma quarter_even (odd : C → Prop) (A : Matrix C C ℂ) (hA : A.PosSemidef)
    (he : A ∈ evenAlgebra odd) : quarterRoot A ∈ evenAlgebra odd :=
  sqrt_even odd _ (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)) (sqrt_even odd A hA he)

end RowColumn.MatrixState

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_HookModel
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace RowColumn.HookModel
open scoped BigOperators Classical
open CubeShuffle.Specht RowColumn.Signed

abbrev Color (h : ℕ) := Fin h ⊕ Fin h

def IsOdd {h : ℕ} : Color h → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

variable (μ : YoungDiagram) (h : ℕ) (H : RowColumn.InHook μ h)

def template (x : Cell μ) : Color h :=
  if hx : row x < h then Sum.inl ⟨row x, hx⟩
  else Sum.inr ⟨col x, (H x.1 x.2).resolve_left hx⟩

abbrev oddCount := Fintype.card {x : Cell μ // IsOdd (template μ h H x)}

def templateWord : Words (S := Cell μ) (IsOdd (h := h)) (oddCount μ h H) :=
  ⟨template μ h H, rfl⟩

end RowColumn.HookModel

namespace RowColumn
open CubeShuffle.Specht

section YoungMap
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (μ : YoungDiagram) (ρ : Representation ℂ (Equiv.Perm (Cell μ)) V) (v : V)

/-- The actual orbit sum giving the map out of the tabloid permutation module.
It is unnormalized, which is harmless for testing nonzero Young symmetrizers. -/
def tabloidOrbitMap : (Tabloid μ → ℂ) →ₗ[ℂ] V where
  toFun f := ∑ g : Equiv.Perm (Cell μ), f (tabloidAct g (baseTabloid μ)) • ρ g v
  map_add' := by
    intro f h
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a f
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

lemma tabloidOrbitMap_intertwines (g : Equiv.Perm (Cell μ)) (f : Tabloid μ → ℂ) :
    tabloidOrbitMap μ ρ v (tabloidRep μ g f) = ρ g (tabloidOrbitMap μ ρ v f) := by
  change (∑ h, f (tabloidAct g⁻¹ (tabloidAct h (baseTabloid μ))) • ρ h v) =
    ρ g (∑ h, f (tabloidAct h (baseTabloid μ)) • ρ h v)
  rw [map_sum]
  simp only [map_smul]
  apply Fintype.sum_equiv (Equiv.mulLeft g⁻¹)
  intro h
  simp only [Equiv.coe_mulLeft, tabloidAct_mul, Equiv.Perm.mul_apply,
    map_mul, Module.End.mul_apply]
  congr 1
  have hh : ρ g (ρ g⁻¹ (ρ h v)) = ρ h v := by
    change (ρ g * ρ g⁻¹) (ρ h v) = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  exact hh.symm

/-- Restricting the orbit map to the already constructed, proved irreducible
Specht module. -/
def youngIntertwiner : Representation.IntertwiningMap (CubeShuffle.Specht.representation μ) ρ where
  toLinearMap := (tabloidOrbitMap μ ρ v).comp (space μ).subtype
  isIntertwining' g := by
    ext f
    exact tabloidOrbitMap_intertwines μ ρ v g f.1

end YoungMap
end RowColumn

namespace RowColumn.HookModel
open scoped BigOperators Classical
open CubeShuffle.Specht RowColumn.Signed

variable (μ : YoungDiagram) (h : ℕ) (H : RowColumn.InHook μ h)

abbrev hookRepresentation :=
  Signed.representation (S := Cell μ) (odd := IsOdd (h := h)) (k := oddCount μ h H)

def youngVector : EuclideanSpace ℂ (Words (S := Cell μ) (IsOdd (h := h)) (oddCount μ h H)) :=
  alternator (colGroup μ) (hookRepresentation μ h H)
    (symmetrizer (CubeShuffle.Specht.rowGroup μ) (hookRepresentation μ h H)
      (wordVector (templateWord μ h H)))

/-- Explicit signed-slot realization of every (h,h)-hook Specht module.
The target, action, and intertwiner are concrete; no LR/Schur-Weyl occurrence
axiom is used. This supplies the first necessary step of weighted.tex:88–93. -/
def hookEmbedding : Representation.IntertwiningMap (CubeShuffle.Specht.representation μ)
    (hookRepresentation μ h H) :=
  RowColumn.youngIntertwiner μ (hookRepresentation μ h H) (wordVector (templateWord μ h H))

end RowColumn.HookModel

end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Multiplicity
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace RowColumn

section Retraction
variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

def algebraicAverage (A : V →ₗ[ℂ] W) : Representation.IntertwiningMap ρ σ where
  toLinearMap := ∑ g, (σ g).comp (A.comp (ρ g⁻¹))
  isIntertwining' h := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    apply Fintype.sum_equiv (Equiv.mulLeft h⁻¹)
    intro g
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
    have hh (w : W) : σ h (σ h⁻¹ w) = w := by
      change (σ h * σ h⁻¹) w = w
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hh]

def extendCommutant (L : Representation.IntertwiningMap ρ σ)
    (R : Representation.IntertwiningMap σ ρ) :
    Representation.IntertwiningMap ρ ρ →ₗ[ℂ] Representation.IntertwiningMap σ σ where
  toFun A := L.comp (A.comp R)
  map_add' A B := by ext v; simp
  map_smul' z A := by ext v; simp

end Retraction
end RowColumn
namespace RowColumn
open scoped BigOperators Classical
open CubeShuffle.UnitaryFinite

section CopyCount
variable {G V X : Type*} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  {ρ : Representation ℂ G V} {τ : Representation ℂ G X}
  {u : ℕ} (I : Fin u → V →ₗᵢ[ℂ] X)

lemma adjoint_intertwines (A : V →ₗ[ℂ] X) (hA : Intertwines ρ τ A)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ) :
    Intertwines τ ρ A.toContinuousLinearMap.adjoint.toLinearMap := by
  intro g x
  apply ext_inner_left ℂ
  intro v
  change inner ℂ v (A.toContinuousLinearMap.adjoint (τ g x)) =
    inner ℂ v (ρ g (A.toContinuousLinearMap.adjoint x))
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [← inv_inv g, unitary_inner_inv ρ hρ, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (A v) (τ (g⁻¹)⁻¹ x) = inner ℂ (A (ρ g⁻¹ v)) x
  rw [hA, unitary_inner_inv τ hτ]

def copyIdempotent (hI : ∀ i, Intertwines ρ τ (I i).toLinearMap)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ) (i : Fin u) :
    Representation.IntertwiningMap τ τ where
  toLinearMap := (I i).toLinearMap.comp (I i).toContinuousLinearMap.adjoint.toLinearMap
  isIntertwining' g := by
    ext x
    change I i ((I i).toContinuousLinearMap.adjoint (τ g x)) =
      τ g (I i ((I i).toContinuousLinearMap.adjoint x))
    rw [show (I i).toContinuousLinearMap.adjoint (τ g x) =
      ρ g ((I i).toContinuousLinearMap.adjoint x) from
      adjoint_intertwines (I i).toLinearMap (hI i) hρ hτ g x]
    exact hI i g _

end CopyCount
end RowColumn
namespace RowColumn
open scoped BigOperators Classical
open CubeShuffle.Specht CubeShuffle.UnitaryFinite

section Relabelling
variable {S T L : Type*}

def lineGroupCongr (e : S ≃ T) (f : S → L) :
    lineGroup f ≃* lineGroup (f ∘ e.symm) where
  toFun g := ⟨e.permCongr g.1, by
    intro x
    simpa only [Function.comp_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply] using g.2 (e.symm x)⟩
  invFun g := ⟨e.symm.permCongr g.1, by
    intro x
    simpa only [Function.comp_apply, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.symm_apply_apply] using g.2 (e x)⟩
  left_inv g := by apply Subtype.ext; exact e.permCongr.symm_apply_apply g.1
  right_inv g := by apply Subtype.ext; exact e.permCongr.apply_symm_apply g.1
  map_mul' g t := by apply Subtype.ext; exact e.permCongrHom.map_mul g.1 t.1

end Relabelling

section Transfer
variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

def commutantOfComp (ρ : Representation ℂ G V) (e : H ≃* G) :
    Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) →ₗ[ℂ]
      Representation.IntertwiningMap ρ ρ where
  toFun T :=
    { toLinearMap := T.toLinearMap
      isIntertwining' g := by simpa using T.isIntertwining' (e.symm g) }
  map_add' A B := rfl
  map_smul' z A := rfl

end Transfer

section HookMultiplicity
variable {S L : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
  (f : S → L) (a : YoungDiagram) (e : S ≃ Cell a) (h : ℕ) (H : InHook a h)

abbrev hookLineTarget :=
  (Signed.lineRepresentation (odd := HookModel.IsOdd (h := h))
    (k := HookModel.oddCount a h H) (f ∘ e.symm)).comp (lineGroupCongr e f).toMonoidHom

def hookLineEmbedding : Representation.IntertwiningMap
    ((relabelledUnitary a e).comp (lineGroup f).subtype) (hookLineTarget f a e h H) where
  toLinearMap := (HookModel.hookEmbedding a h H).toLinearMap.comp (spaceHilbertEquiv a).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    let T := (HookModel.hookEmbedding a h H).comp (unitaryEquiv a).symm.toIntertwiningMap
    exact Representation.IntertwiningMap.isIntertwining _ _ T (e.permCongr g.1) v

end HookMultiplicity
end RowColumn

end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_CopyOverlap
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace RowColumn
open scoped BigOperators ComplexConjugate Classical

section HilbertSchmidt
variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- Ordinary squared Hilbert--Schmidt norm on a possibly rectangular map. -/
def hilbertSchmidtSq (B : V →L[ℂ] W) : ℝ :=
  (LinearMap.trace ℂ V (B.adjoint.comp B).toLinearMap).re

end HilbertSchmidt

section CopyTrace
variable {V W X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  {u v : ℕ}

/-- Sum of the genuine range projections for the given isometric copies. -/
def copyProjection (I : Fin u → V →ₗᵢ[ℂ] X) : X →L[ℂ] X :=
  ∑ i, (I i).toContinuousLinearMap.comp (I i).toContinuousLinearMap.adjoint

end CopyTrace
end RowColumn

end
end


section
noncomputable section
open scoped BigOperators Classical
namespace RowColumn
open CubeShuffle.UnitaryFinite
variable {G V E : Type*} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (ρ : Representation ℂ G V) (τ : Representation ℂ G E)
  (hρ : IsUnitary ρ) (hτ : IsUnitary τ)

include hρ hτ
lemma isometric_adjoint_intertwines (f : Representation.IntertwiningMap ρ τ) (g : G) (x : E) :
    LinearMap.adjoint f.toLinearMap (τ g x) = ρ g (LinearMap.adjoint f.toLinearMap x) := by
  have hf : Intertwines ρ τ f.toLinearMap := by
    intro g y
    exact Representation.IntertwiningMap.isIntertwining ρ τ f g y
  have hh := adjoint_intertwines f.toLinearMap hf hρ hτ g x
  simpa only [LinearMap.adjoint_eq_toCLM_adjoint] using hh

def gramIntertwiner (f : Representation.IntertwiningMap ρ τ) : Representation.IntertwiningMap ρ ρ where
  toLinearMap := (LinearMap.adjoint f.toLinearMap).comp f.toLinearMap
  isIntertwining' g := by
    ext x
    change (LinearMap.adjoint f.toLinearMap) (f (ρ g x)) =
      ρ g ((LinearMap.adjoint f.toLinearMap) (f x))
    rw [Representation.IntertwiningMap.isIntertwining]
    exact isometric_adjoint_intertwines ρ τ hρ hτ f g (f x)

end RowColumn

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Entropy
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical
namespace RowColumn


/-- Marginal of the uniform distribution on `ι` along an actual line map. -/
def uniformMarginal {ι α : Type*} [Fintype ι] [DecidableEq α] (f : ι → α) (a : α) : ℝ :=
  ∑ i, if f i = a then (Fintype.card ι : ℝ)⁻¹ else 0

end RowColumn

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_TensorFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
open FiniteStarAlgebra Signed
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

/-- Matrix form of an actual algebra element, with the unchanged physical
coordinate basis on the signed tensor sector. -/
def algebraMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) :
    A →ₗ[ℂ] Matrix I I ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm.toAlgEquiv.toLinearMap.comp A.subtype.toLinearMap

def sandwichMap {I : Type*} [Fintype I] [DecidableEq I]
    (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (M N : Matrix I I ℂ) : A →ₗ[ℂ] EuclideanSpace ℂ (I × I) :=
  hsVector.comp ((LinearMap.mulRight ℂ N).comp ((LinearMap.mulLeft ℂ M).comp (algebraMatrix A)))

end RowColumn.MatrixState

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
open FiniteStarAlgebra Signed
variable {I : Type*} [Fintype I] [DecidableEq I]

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

def positiveTensor (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : Matrix C C ℂ) (hM : M.PosSemidef) (he : M ∈ evenAlgebra odd) :
    sectorAlgebra (S := S) odd k :=
  ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (sectorTensor odd k (fun _ : S => M)),
    sectorTensor_mem_algebra odd k M hM.isHermitian he⟩

end RowColumn.MatrixState

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_LineStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical
namespace RowColumn.Postselection
open WordOrbits
variable {S L A : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
  [Fintype A] [DecidableEq A]

def allocationPerm (line b : S → L) (hb : counts b = counts line) : Equiv.Perm S :=
  (same_counts_permutation line b hb.symm).choose

def symExtension (line : S → L) (v : (S → A) → ℂ) (w : S → L × A) : ℂ :=
  if hb : counts (fun i => (w i).1) = counts line then
    v (fun i => (w (allocationPerm line _ hb i)).2) else 0

abbrev Allocations (line : S → L) := {b : S → L // counts b = counts line}

def labelWordEquiv : (S → L × A) ≃ (S → L) × (S → A) where
  toFun w := (fun i => (w i).1, fun i => (w i).2)
  invFun w i := (w.1 i,w.2 i)
  left_inv := by intro w; rfl
  right_inv := by intro w; rfl

def precompWordEquiv (p : Equiv.Perm S) : Equiv.Perm (S → A) where
  toFun w := w ∘ p
  invFun w := w ∘ p.symm
  left_inv := by intro w; ext i; simp
  right_inv := by intro w; ext i; simp


def labelTest (line : S → L) (x : (S → A) → ℂ) (w : S → L × A) : ℂ :=
  if (fun i => (w i).1)=line then x (fun i => (w i).2) else 0

def lineMass (z : L × A → ℂ) (l : L) : ℝ := ∑ a, Complex.normSq (z (l,a))
def normalizedLine (z : L × A → ℂ) (l : L) (a : A) : ℂ :=
  (Real.sqrt (lineMass z l) : ℂ)⁻¹ * z (l,a)

def lineAmplitude (line : S → L) (a₀ : S → A) (good : A → Prop) [DecidablePred good]
    (q : Types (S := S) (A := L × A)) (θ : Phases (L × A) (Fintype.card S)) (l : L) (a : A) : ℂ :=
  normalizedLine (truncateAmplitude (fun c : L × A => good c.2)
    (twistedAmplitude (typeRepresentative (fun i => (line i,a₀ i)) q) θ)) l a

end RowColumn.Postselection

end
end


section
noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator ComplexOrder MatrixOrder
namespace RowColumn.Postselection
open MatrixState WordOrbits
variable {S L C : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
  [Fintype C] [DecidableEq C]

def lineState (line : S → L) (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (q : Types (S := S) (A := L × (C × C))) (θ : Phases (L × (C × C)) (Fintype.card S))
    (l : L) : Matrix C C ℂ :=
  gramState (lineAmplitude line a₀ (fun p : C × C => odd p.1 ↔ odd p.2) q θ l)

end RowColumn.Postselection

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Dephasing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace RowColumn.Signed
open scoped BigOperators Classical
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

abbrev ParityMismatch (w v : Words (S := S) odd k) :=
  {x : S // ¬ (odd (w.1 x) ↔ odd (v.1 x))}

end RowColumn.Signed

noncomputable section
open scoped BigOperators Classical
namespace RowColumn

variable {S : Type*} [Fintype S] [DecidableEq S]

abbrev ShortSubsets (q : ℕ) := {t : Finset S // t.card ≤ q}

def shortSubsetCode {q : ℕ} (t : ShortSubsets (S := S) q) (i : Fin q) : Option S :=
  if hi : i.1 < t.1.card then some ((t.1.equivFin).symm ⟨i.1, hi⟩).1 else none

def parityDifference (b c : S → Bool) : Finset S := Finset.univ.filter (fun x => b x ≠ c x)

def parityNear (q : ℕ) (b c : S → Bool) : Prop := (parityDifference b c).card ≤ q

instance instDecidableRelForallBoolParityNear (q : ℕ) : DecidableRel (parityNear (S := S) q) := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))

end RowColumn
noncomputable section
open scoped BigOperators Classical
namespace RowColumn

section PositiveBanded
variable {V B : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [Fintype B] [DecidableEq B]

def energy (A : V →ₗ[ℂ] V) (x : V) : ℝ := (inner ℂ x (A x)).re

end PositiveBanded
end RowColumn
namespace RowColumn.Signed
open scoped BigOperators Classical
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

def parityPattern (w : Words (S := S) odd k) : S → Bool := fun x => decide (odd (w.1 x))

def parityMask (b : S → Bool) (v : EuclideanSpace ℂ (Words (S := S) odd k)) :
    EuclideanSpace ℂ (Words (S := S) odd k) :=
  WithLp.toLp 2 (fun w => if parityPattern w = b then v w else 0)

end RowColumn.Signed

end
end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Postselection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J B : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Rectangular coordinate inclusion for an actual injective index map. -/
def indexInclusion (e : J ↪ I) : Matrix I J ℂ := fun i j => if i=e j then 1 else 0

def extendMatrix (e : J ↪ I) (A : Matrix J J ℂ) : Matrix I I ℂ := indexInclusion e * A * (indexInclusion e).conjTranspose

variable [Fintype B] [DecidableEq B]
def blockMask (b : I → B) (k : B) : Matrix I I ℂ := Matrix.diagonal (fun i => if b i=k then 1 else 0)
def pinchMatrix (b : I → B) (A : Matrix I I ℂ) : Matrix I I ℂ := ∑ k, blockMask b k * A * blockMask b k

end RowColumn.MatrixState

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace RowColumn.Signed
open RowColumn.MatrixState CubeShuffle.Specht
variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] {odd : C → Prop} [DecidablePred odd] {k : ℕ}

/-- Matrix in the actual orthonormal word basis, with no change of representation. -/
def intertwinerMatrix (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) :
    Matrix (Words (S := S) odd k) (Words (S := S) odd k) ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm T.toLinearMap.toContinuousLinearMap

end RowColumn.Signed

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace RowColumn.Signed
open RowColumn.MatrixState RowColumn.Postselection RowColumn.WordOrbits
variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] (odd : C → Prop) [DecidablePred odd] (k : ℕ)

def wordInclusion : Words (S := S) odd k ↪ (S → C) := ⟨Subtype.val, Subtype.val_injective⟩

def extendedPinch (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) : Matrix (S → C) (S → C) ℂ :=
  extendMatrix (wordInclusion odd k) (pinchMatrix parityPattern (intertwinerMatrix line T))

end RowColumn.Signed

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_OverlapBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.Signed
open MatrixState Postselection WordOrbits
variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L]

def lineCost : ℕ := (Fintype.card S+1)^(Fintype.card L*Fintype.card C^2)
abbrev MixtureIndex := Types (S := S) (A := L × (C × C)) × Phases (L × (C × C)) (Fintype.card S)

end RowColumn.Signed

end
end


end OAI
end


