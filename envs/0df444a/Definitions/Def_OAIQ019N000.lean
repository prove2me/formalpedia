-- Prove2me | Definitions.Def_OAIQ019N000
-- name    : OAIQ019N000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:57:36.794481+00:00
-- url     : https://prove2.me/theorems/36433b16-47dc-4475-97af-66e40574c965
-- title:
--   Definitions bundle OAIQ019N000 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 88 declarations of OpenAI's Lean: 39 definitions, 2 instances and 47 theorems. The definitions and types are `OAI.NuclearUltrapower.AlmostInvariant`, `OAI.NuclearUltrapower.CuntzAveraging.Target`, `OAI.NuclearUltrapower.CuntzAveraging.coordinate`, `OAI.NuclearUltrapower.CuntzAveraging.instDecidableEqIndex`, `OAI.NuclearUltrapower.CuntzAveraging.left`, `OAI.NuclearUltrapower.CuntzAveraging.right`, `OAI.NuclearUltrapower.CuntzModel.Index`, `OAI.NuclearUltrapower.CuntzModel.Space`, `OAI.NuclearUltrapower.CuntzModel.instDecidableEqIndex`, `OAI.NuclearUltrapower.CuntzModel.shift`, `OAI.NuclearUltrapower.CuntzModel.shiftIndex`, `OAI.NuclearUltrapower.CuntzPolynomial.Letter`, `OAI.NuclearUltrapower.CuntzPolynomial.Poly`, `OAI.NuclearUltrapower.CuntzPolynomial.Word`, `OAI.NuclearUltrapower.CuntzPolynomial.evalLetter`, `OAI.NuclearUltrapower.CuntzPolynomial.flip`, `OAI.NuclearUltrapower.CuntzWords.Word`, `OAI.NuclearUltrapower.CuntzWords.index`, `OAI.NuclearUltrapower.CuntzWords.value`, `OAI.NuclearUltrapower.IntegralVector3`, `OAI.NuclearUltrapower.L2`, `OAI.NuclearUltrapower.SOS.Mat3`, `OAI.NuclearUltrapower.SOS.Poly`, `OAI.NuclearUltrapower.SOS.entry`, `OAI.NuclearUltrapower.SOS.eval`, `OAI.NuclearUltrapower.SOS.generators`, `OAI.NuclearUltrapower.SOS.label1221`, `OAI.NuclearUltrapower.SOS.matOne`, `OAI.NuclearUltrapower.TensorHilbert`, `OAI.NuclearUltrapower.completedTensorMap`, `OAI.NuclearUltrapower.cosetCocycle`, `OAI.NuclearUltrapower.cosetRep`, `OAI.NuclearUltrapower.inducedUnitary`, `OAI.NuclearUltrapower.inductionInclusion`, `OAI.NuclearUltrapower.l2Embedding`, `OAI.NuclearUltrapower.l2Single`, `OAI.NuclearUltrapower.lpUnitary`, `OAI.NuclearUltrapower.tensorLeftHom`, `OAI.NuclearUltrapower.tensorRightHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`NuclearUltrapower_CuntzAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzAlgebra.lean), [`NuclearUltrapower_CuntzWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzWords.lean), [`NuclearUltrapower_DyadicGroup`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/DyadicGroup.lean), [`NuclearUltrapower_HilbertInduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/HilbertInduction.lean), [`NuclearUltrapower_HilbertTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/HilbertTensor.lean), [`NuclearUltrapower_InducedApproximation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/InducedApproximation.lean), [`NuclearUltrapower_SOSResidual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSResidual.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ019N039`, `OAIQ019N040` and `OAIQ019N041`; the statement `OAI_NuclearUltrapower_CuntzUniversal_nuclear`.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ019_Nuc.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped ENNReal InnerProductSpace
namespace NuclearUltrapower
universe u v

/-- A coordinate permutation with unitary entries on a Hilbert direct sum. -/
def lpUnitary {ι : Type u} {V : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (e : Equiv.Perm ι) (T : ι → V ≃ₗᵢ[ℂ] V) :
    lp (fun _ : ι => V) 2 ≃ₗᵢ[ℂ] lp (fun _ : ι => V) 2 := by
  have hm (e : Equiv.Perm ι) (T : ι → V ≃ₗᵢ[ℂ] V) (x : lp (fun _ : ι => V) 2) :
      Memℓp (fun i => T i (x (e i))) 2 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    have hx := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have hh := hx.comp_injective e.injective
    apply hh.congr
    intro i
    exact congrArg (fun r : ℝ => r ^ (2 : ℝ≥0∞).toReal) ((T i).norm_map (x (e i))).symm
  let L : lp (fun _ : ι => V) 2 ≃ₗ[ℂ] lp (fun _ : ι => V) 2 := {
    toFun x := ⟨fun i => T i (x (e i)), hm e T x⟩
    invFun x := ⟨fun i => (T (e.symm i)).symm (x (e.symm i)),
      hm e.symm (fun i => (T (e.symm i)).symm) x⟩
    left_inv x := by ext i; simp
    right_inv x := by ext i; simp
    map_add' x y := by ext i; exact map_add (T i) _ _
    map_smul' c x := by ext i; exact map_smul (T i) _ _ }
  refine ⟨L, fun x => ?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  -- Compute the square of the norm by the defining l2 sum.
  have hnorm (y : lp (fun _ : ι => V) 2) : ‖y‖ ^ 2 = ∑' i, ‖y i‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) y
  rw [hnorm, hnorm]
  simpa only [L, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    LinearIsometryEquiv.norm_map] using e.tsum_eq (fun i => ‖x i‖ ^ 2)

@[simp] theorem lpUnitary_apply {ι : Type u} {V : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (e : Equiv.Perm ι) (T : ι → V ≃ₗᵢ[ℂ] V)
    (x : lp (fun _ : ι => V) 2) (i : ι) : lpUnitary e T x i = T i (x (e i)) := rfl

section Induction
variable {G : Type u} [Group G] (H : Subgroup G)

/-- A normalized transversal; the identity coset is represented by the identity. -/
def cosetRep (i : G ⧸ H) : G := by
  classical
  exact if i = (QuotientGroup.mk 1 : G ⧸ H) then 1 else i.out

@[simp] theorem cosetRep_identity : cosetRep H (QuotientGroup.mk 1) = 1 := by
  simp [cosetRep]

theorem cosetRep_mk (i : G ⧸ H) : QuotientGroup.mk (cosetRep H i) = i := by
  classical
  unfold cosetRep
  split_ifs with hi
  · exact hi.symm
  · exact QuotientGroup.out_eq' i

/-- The transversal cocycle, with source coordinate `i` and target `g • i`. -/
def cosetCocycle (g : G) (i : G ⧸ H) : H :=
  ⟨(cosetRep H (g • i))⁻¹ * g * cosetRep H i, by
    rw [mul_assoc]
    apply QuotientGroup.eq.mp
    change (QuotientGroup.mk (cosetRep H (g • i)) : G ⧸ H) = g • (QuotientGroup.mk (cosetRep H i) : G ⧸ H)
    rw [cosetRep_mk, cosetRep_mk]⟩

@[simp] theorem cosetCocycle_one (i : G ⧸ H) : cosetCocycle H 1 i = 1 := by
  apply Subtype.ext
  simp [cosetCocycle]

theorem cosetCocycle_mul (g h : G) (i : G ⧸ H) :
    cosetCocycle H (g * h) i = cosetCocycle H g (h • i) * cosetCocycle H h i := by
  apply Subtype.ext
  simp only [cosetCocycle, Subgroup.coe_mul, mul_smul]
  group

variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (α : H →* (V ≃ₗᵢ[ℂ] V))

/-- Unitary induction with no finite-index assumption. -/
def inducedUnitary : G →* (lp (fun _ : G ⧸ H => V) 2 ≃ₗᵢ[ℂ]
    lp (fun _ : G ⧸ H => V) 2) where
  toFun g := lpUnitary (MulAction.toPerm g⁻¹)
    (fun i => α (cosetCocycle H g (g⁻¹ • i)))
  map_one' := by ext x i; simp
  map_mul' g h := by
    ext x i
    simp only [lpUnitary_apply, MulAction.toPerm_apply,
      mul_inv_rev, mul_smul]
    rw [cosetCocycle_mul, map_mul]
    simp

@[simp] theorem inducedUnitary_apply (g : G) (x : lp (fun _ : G ⧸ H => V) 2) (i : G ⧸ H) :
    inducedUnitary H α g x i = α (cosetCocycle H g (g⁻¹ • i)) (x (g⁻¹ • i)) := rfl

/-- The original representation embeds on the identity coordinate. -/
def inductionInclusion : V →ₗᵢ[ℂ] lp (fun _ : G ⧸ H => V) 2 := by
  classical
  refine { toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : G ⧸ H => V) 2 (QuotientGroup.mk 1), norm_map' := ?_ }
  intro v
  exact lp.norm_single (E := fun _ : G ⧸ H => V) (p := 2) (by norm_num) (QuotientGroup.mk 1) v

@[simp] theorem inductionInclusion_apply (v : V) (i : G ⧸ H) :
    inductionInclusion H v i = Pi.single (M := fun _ : G ⧸ H => V) (QuotientGroup.mk 1) v i := rfl

end Induction
end NuclearUltrapower
end
end

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped ENNReal InnerProductSpace
namespace NuclearUltrapower
universe u v
abbrev L2 (I : Type u) := lp (fun _ : I => ℂ) 2

/-- Coordinate lines in a Hilbert direct sum. -/
def l2Single {I : Type u} (i : I) : ℂ →ₗᵢ[ℂ] L2 I := by
  classical
  exact ⟨lp.lsingle (𝕜 := ℂ) (E := fun _ : I => ℂ) 2 i,
    fun c => lp.norm_single (E := fun _ : I => ℂ) (p := 2) (by norm_num) i c⟩

@[simp] theorem l2Single_apply {I : Type u} (i : I) (c : ℂ) :
    l2Single i c = lp.single 2 i c := rfl

theorem l2Single_orthogonal {I : Type u} :
    OrthogonalFamily ℂ (fun _ : I => ℂ) (l2Single (I := I)) := by
  classical
  intro i j hij x y
  rw [l2Single_apply, l2Single_apply, lp.inner_single_left]
  simp [lp.single_apply, hij]

/-- An injection of coordinate sets induces an honest Hilbert isometry. -/
def l2Embedding {I : Type u} {J : Type v} (e : I ↪ J) : L2 I →ₗᵢ[ℂ] L2 J :=
  (show OrthogonalFamily ℂ (fun _ : I => ℂ) (fun i => l2Single (e i)) from
    fun _ _ hij x y => l2Single_orthogonal (e.injective.ne hij) x y).linearIsometry

@[simp] theorem l2Embedding_single {I : Type u} {J : Type v} (e : I ↪ J)
    (i : I) (c : ℂ) : l2Embedding e (lp.single 2 i c) = lp.single 2 (e i) c := by
  classical
  exact OrthogonalFamily.linearIsometry_apply_single
    (G := fun _ : I => ℂ) (V := fun i => l2Single (e i)) _ c

/-- The adjoint of coordinate extension is coordinate restriction. -/
@[simp] theorem l2Embedding_adjoint_apply {I : Type u} {J : Type v} (e : I ↪ J)
    (x : L2 J) (i : I) : (l2Embedding e).toContinuousLinearMap.adjoint x i = x (e i) := by
  classical
  have h := ContinuousLinearMap.adjoint_inner_right (l2Embedding e).toContinuousLinearMap
    (lp.single 2 i (1 : ℂ)) x
  simpa only [LinearIsometry.coe_toContinuousLinearMap, l2Embedding_single,
    lp.inner_single_left, RCLike.inner_apply', map_one, one_mul] using h

end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped InnerProductSpace
namespace NuclearUltrapower.CuntzModel

abbrev Index := ℤ × ℕ
abbrev Space := L2 Index
local instance instDecidableEqIndex : DecidableEq Index := Classical.decEq _

/-- Integer height separates words of different lengths; the binary coordinate
partitions every level into the two isometric ranges. -/
def shiftIndex (i : Fin 2) : Index ↪ Index where
  toFun x := (x.1 + 1, 2*x.2+i.val)
  inj' := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp at h₁ h₂
    congr 1 <;> omega

@[simp] theorem shiftIndex_apply (i : Fin 2) (x : Index) :
    shiftIndex i x = (x.1+1,2*x.2+i.val) := rfl

theorem shiftIndex_disjoint {i j : Fin 2} (hij : i ≠ j) (x y : Index) :
    shiftIndex i x ≠ shiftIndex j y := by
  intro h
  have hh := congrArg Prod.snd h
  dsimp at hh
  have hi := i.isLt
  have hj := j.isLt
  apply hij
  apply Fin.ext
  omega

def shift (i : Fin 2) : Space →L[ℂ] Space := (l2Embedding (shiftIndex i)).toContinuousLinearMap

@[simp] theorem shift_single (i : Fin 2) (x : Index) (c : ℂ) :
    shift i (lp.single 2 x c) = lp.single 2 (shiftIndex i x) c :=
  by simpa only [shift, LinearIsometry.coe_toContinuousLinearMap] using
    l2Embedding_single (shiftIndex i) x c

@[simp] theorem shift_adjoint_apply (i : Fin 2) (x : Space) (k : Index) :
    (shift i).adjoint x k = x (shiftIndex i k) := l2Embedding_adjoint_apply _ _ _

@[simp] theorem shift_adjoint_single_same (i : Fin 2) (x : Index) (c : ℂ) :
    (shift i).adjoint (lp.single 2 (shiftIndex i x) c) = lp.single 2 x c := by
  ext y
  simp only [shift_adjoint_apply, lp.single_apply, Pi.single_apply,
    (shiftIndex i).injective.eq_iff]

@[simp] theorem shift_adjoint_single_ne {i j : Fin 2} (hij : i ≠ j) (x : Index) (c : ℂ) :
    (shift i).adjoint (lp.single 2 (shiftIndex j x) c) = 0 := by
  ext y
  rw [shift_adjoint_apply]
  change (lp.single (E := fun _ : Index => ℂ) 2 (shiftIndex j x) c) (shiftIndex i y) = 0
  exact lp.single_apply_ne 2 _ _ (shiftIndex_disjoint hij y x)

end NuclearUltrapower.CuntzModel
end
end

section

noncomputable section
open scoped MonoidAlgebra
namespace NuclearUltrapower.CuntzPolynomial
abbrev Letter := Fin 2 × Bool
abbrev Word := FreeMonoid Letter

def flip (a : Letter) : Letter := (a.1,!a.2)
@[simp] theorem flip_flip (a : Letter) : flip (flip a) = a := by
  rcases a with ⟨i,b⟩
  cases b <;> rfl

instance instStarWord : Star Word := ⟨fun w => FreeMonoid.ofList ((FreeMonoid.toList w).reverse.map flip)⟩
@[simp] theorem star_word_of (a : Letter) : star (FreeMonoid.of a) = FreeMonoid.of (flip a) := rfl
instance instInvolutiveStarWord : InvolutiveStar Word where
  star_involutive w := by
    apply FreeMonoid.toList.injective
    change ((FreeMonoid.toList w).reverse.map flip).reverse.map flip = FreeMonoid.toList w
    simp [List.map_reverse, List.map_map, Function.comp_def]

abbrev Poly := ℂ[Word]

variable {D : Type*} [CStarAlgebra D]
def evalLetter (r : Fin 2 → D) (a : Letter) : D := if a.2 then star (r a.1) else r a.1
@[simp] theorem evalLetter_flip (r : Fin 2 → D) (a : Letter) :
    evalLetter r (flip a) = star (evalLetter r a) := by
  rcases a with ⟨i,b⟩
  cases b <;> simp [evalLetter, flip]

end NuclearUltrapower.CuntzPolynomial
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertTensor
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower

section CompletionMaps
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Uniqueness on the dense original normed space. -/
theorem completion_map_ext {f g : UniformSpace.Completion E →L[ℂ] F}
    (h : ∀ x : E, f x = g x) : f = g := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq f.continuous g.continuous
  | ih x => exact h x

@[simp] theorem completed_add (f g : E →L[ℂ] F) :
    (f+g).completion = f.completion + g.completion := by
  apply completion_map_ext
  intro x
  simp [← UniformSpace.Completion.coe_add]

@[simp] theorem completed_smul (c : ℂ) (f : E →L[ℂ] F) :
    (c • f).completion = c • f.completion := by
  apply completion_map_ext
  intro x
  simp [← UniformSpace.Completion.coe_smul]

@[simp] theorem completed_zero : (0 : E →L[ℂ] F).completion = 0 := by
  apply completion_map_ext
  intro x
  simp

@[simp] theorem completed_comp (f : F →L[ℂ] G) (g : E →L[ℂ] F) :
    (f.comp g).completion = f.completion.comp g.completion := by
  apply completion_map_ext
  intro x
  simp

@[simp] theorem completed_one : (1 : E →L[ℂ] E).completion = 1 := by
  apply completion_map_ext
  intro x
  simp

end CompletionMaps

abbrev TensorHilbert (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] := UniformSpace.Completion (E ⊗[ℂ] F)

section TensorOperators
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def completedTensorMap (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    TensorHilbert E F →L[ℂ] TensorHilbert E F := (TensorProduct.mapL U V).completion

@[simp] theorem completedTensorMap_coe (U : E →L[ℂ] E) (V : F →L[ℂ] F)
    (z : E ⊗[ℂ] F) : completedTensorMap U V z = (TensorProduct.mapL U V z : TensorHilbert E F) :=
  ContinuousLinearMap.completion_apply_coe _ _

@[simp] theorem tensorMap_one : TensorProduct.mapL (1 : E →L[ℂ] E) (1 : F →L[ℂ] F) = 1 := by
  ext z
  induction z using OAI.tensorInductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem completedTensorMap_one : completedTensorMap (1 : E →L[ℂ] E) (1 : F →L[ℂ] F) = 1 := by
  simp [completedTensorMap]

@[simp] theorem completedTensorMap_mul (U U' : E →L[ℂ] E) (V V' : F →L[ℂ] F) :
    completedTensorMap (U * U') (V * V') = completedTensorMap U V * completedTensorMap U' V' := by
  change (TensorProduct.mapL (U.comp U') (V.comp V')).completion = _
  rw [TensorProduct.mapL_comp, completed_comp]
  rfl

@[simp] theorem completedTensorMap_add_left (U U' : E →L[ℂ] E) (V : F →L[ℂ] F) :
    completedTensorMap (U+U') V = completedTensorMap U V + completedTensorMap U' V := by
  simp [completedTensorMap, TensorProduct.mapL_add_left]

@[simp] theorem completedTensorMap_add_right (U : E →L[ℂ] E) (V V' : F →L[ℂ] F) :
    completedTensorMap U (V+V') = completedTensorMap U V + completedTensorMap U V' := by
  simp [completedTensorMap, TensorProduct.mapL_add_right]

@[simp] theorem completedTensorMap_smul_left (c : ℂ) (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    completedTensorMap (c • U) V = c • completedTensorMap U V := by
  simp [completedTensorMap, TensorProduct.mapL_smul_left]

@[simp] theorem completedTensorMap_smul_right (c : ℂ) (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    completedTensorMap U (c • V) = c • completedTensorMap U V := by
  simp [completedTensorMap, TensorProduct.mapL_smul_right]

@[simp] theorem completedTensorMap_zero_left (V : F →L[ℂ] F) : completedTensorMap (0 : E →L[ℂ] E) V = 0 := by
  simp [completedTensorMap]

@[simp] theorem completedTensorMap_zero_right (U : E →L[ℂ] E) : completedTensorMap U (0 : F →L[ℂ] F) = 0 := by
  simp [completedTensorMap]

variable [CompleteSpace E] [CompleteSpace F]

/-- Adjoint compatibility proved on the dense tensor product, not by assuming it complete. -/
@[simp] theorem completedTensorMap_star (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    completedTensorMap (star U) (star V) = star (completedTensorMap U V) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    induction y using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih y =>
      simp only [completedTensorMap_coe, UniformSpace.Completion.inner_coe]
      induction x using OAI.tensorInductionOn with
      | add x x' hx hx' => simp only [map_add, inner_add_left, hx, hx']
      | tmul a b =>
        induction y using OAI.tensorInductionOn with
        | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
        | tmul a' b' =>
          simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul, ContinuousLinearMap.star_eq_adjoint]
          rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

/-- The two commuting unital coordinate tensor embeddings. -/
def tensorLeftHom : (E →L[ℂ] E) →⋆ₐ[ℂ] (TensorHilbert E F →L[ℂ] TensorHilbert E F) where
  toFun U := completedTensorMap U 1
  map_zero' := by simp
  map_one' := completedTensorMap_one
  map_add' := by intros; simp
  map_mul' U V := by simpa using completedTensorMap_mul U V (1 : F →L[ℂ] F) 1
  commutes' c := by
    change completedTensorMap (c • 1) 1 = c • 1
    simp
  map_star' U := by simpa using completedTensorMap_star U (1 : F →L[ℂ] F)

def tensorRightHom : (F →L[ℂ] F) →⋆ₐ[ℂ] (TensorHilbert E F →L[ℂ] TensorHilbert E F) where
  toFun V := completedTensorMap 1 V
  map_zero' := by simp
  map_one' := completedTensorMap_one
  map_add' := by intros; simp
  map_mul' U V := by simpa using completedTensorMap_mul (1 : E →L[ℂ] E) 1 U V
  commutes' c := by
    change completedTensorMap 1 (c • 1) = c • 1
    simp
  map_star' U := by simpa using completedTensorMap_star (1 : E →L[ℂ] E) U

end TensorOperators
end NuclearUltrapower

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.CuntzWords

/-- Fixed-length binary words, with a product decomposition at every successor. -/
@[reducible] def Word : ℕ → Type
  | 0 => PUnit
  | n+1 => Fin 2 × Word n

def value {D : Type*} [Monoid D] (r : Fin 2 → D) : {n : ℕ} → Word n → D
  | 0, _ => 1
  | _+1, (i,w) => r i * value r w

@[simp] theorem value_zero {D : Type*} [Monoid D] (r : Fin 2 → D) (w : Word 0) :
    value r w = 1 := rfl
@[simp] theorem value_succ {D : Type*} [Monoid D] (r : Fin 2 → D) {n : ℕ}
    (i : Fin 2) (w : Word n) : value r (n := n+1) (i,w) = r i * value r w := rfl

def index : {n : ℕ} → Word n → CuntzModel.Index
  | 0, _ => (0,0)
  | _+1, (i,w) => CuntzModel.shiftIndex i (index w)

@[simp] theorem index_succ {n : ℕ} (i : Fin 2) (w : Word n) :
    index (n := n+1) (i,w) = CuntzModel.shiftIndex i (index w) := rfl

end NuclearUltrapower.CuntzWords
end
end

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords
local instance instDecidableEqIndex : DecidableEq Index := Classical.decEq _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev Target (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  TensorHilbert Space H

def coordinate (i : Index) : H →L[ℂ] Target H :=
  UniformSpace.Completion.toComplL.comp (TensorProduct.mkL ℂ Space H (lp.single 2 i 1))

@[simp] theorem coordinate_apply (i : Index) (x : H) :
    coordinate i x = ((lp.single 2 i 1) ⊗ₜ[ℂ] x : Space ⊗[ℂ] H) := rfl

@[simp] theorem inner_coordinate (i j : Index) (x y : H) :
    ⟪coordinate i x, coordinate j y⟫_ℂ = if i = j then ⟪x,y⟫_ℂ else 0 := by
  simp only [coordinate_apply,UniformSpace.Completion.inner_coe,TensorProduct.inner_tmul,
    lp.inner_single_left,RCLike.inner_apply',map_one,one_mul,lp.single_apply,Pi.single_apply]
  split_ifs with h <;> simp_all

@[simp] theorem coordinate_norm (i : Index) (x : H) : ‖coordinate i x‖ = ‖x‖ := by
  rw [coordinate_apply,UniformSpace.Completion.norm_coe,TensorProduct.norm_tmul]
  rw [lp.norm_single (by norm_num),norm_one,one_mul]

variable [CompleteSpace H]

def left (i : Fin 2) : Target H →L[ℂ] Target H := tensorLeftHom (shift i)
def right (T : H →L[ℂ] H) : Target H →L[ℂ] Target H := tensorRightHom T

@[simp] theorem left_coordinate (i : Fin 2) (k : Index) (x : H) :
    left i (coordinate k x) = coordinate (shiftIndex i k) x := by
  change completedTensorMap (shift i) 1 (coordinate k x) = _
  rw [coordinate_apply,completedTensorMap_coe]
  simp only [TensorProduct.mapL_tmul,shift_single,one_apply_eq_self,coordinate_apply]

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_DyadicGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v w
open scoped TensorProduct Topology
open Filter

namespace NuclearUltrapower

/-! The exact integral subgroup and dilation in the tensor-norm formulation. -/

abbrev IntegralVector3 := Fin 3 → ℤ

end NuclearUltrapower

end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_InducedApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u v w
section ApproxInvariant
variable {ι : Type u} {Γ : Type v} [Group Γ] {E : ι → Type w}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  (l : Filter ι) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i) (x : ∀ i, E i)

/-- Pointwise approximate invariance in a varying Hilbert family. -/
def AlmostInvariant (g : Γ) : Prop :=
  Tendsto (fun i => ‖U g i (x i) - x i‖) l (𝓝 0)

end ApproxInvariant
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {α A : Type*} [DecidableEq α]

/-- Sparse integral polynomials, before combining repeated labels. -/
abbrev Poly (α : Type*) := List (α × ℤ)

section Evaluation
variable [AddCommGroup A]

def eval (f : α → A) (ps : Poly α) : A :=
  (ps.map (fun p => p.2 • f p.1)).sum

omit [DecidableEq α] in
@[simp] theorem eval_nil (f : α → A) : eval f [] = 0 := rfl
omit [DecidableEq α] in
@[simp] theorem eval_cons (f : α → A) (p : α × ℤ) (ps : Poly α) :
    eval f (p::ps) = p.2 • f p.1 + eval f ps := rfl

end Evaluation

/-- Flat 3-by-3 integer matrices, used only as kernel-computable labels. -/
abbrev Mat3 := List ℤ

def entry (a : Mat3) (i j : Nat) : ℤ := a.getD (3*i+j) 0

def matOne : Mat3 := [1,0,0,0,1,0,0,0,1]

end NuclearUltrapower.SOS

namespace NuclearUltrapower.SOS
def label1221 : Mat3 := [1, -1, -1, 0, 1, 0, 0, 0, 1]
def generators : List Mat3 := [[1, -1, 0, 0, 1, 0, 0, 0, 1], [1, 1, 0, 0, 1, 0, 0, 0, 1], [1, 0, -1, 0, 1, 0, 0, 0, 1], [1, 0, 1, 0, 1, 0, 0, 0, 1], [1, 0, 0, -1, 1, 0, 0, 0, 1], [1, 0, 0, 1, 1, 0, 0, 0, 1], [1, 0, 0, 0, 1, -1, 0, 0, 1], [1, 0, 0, 0, 1, 1, 0, 0, 1], [1, 0, 0, 0, 1, 0, -1, 0, 1], [1, 0, 0, 0, 1, 0, 1, 0, 1], [1, 0, 0, 0, 1, 0, 0, -1, 1], [1, 0, 0, 0, 1, 0, 0, 1, 1]]
end NuclearUltrapower.SOS
end

end OAI
end


