-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Finite
-- name    : OAI_Analysis_C0Absorption_Finite
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:43:35.003675+00:00
-- url     : https://prove2.me/theorems/b92f317b-1c11-40cc-b36f-58e9d75aebd5
-- title:
--   Finite-dimensional sections of the frozen shift
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. Levels are pairs $(i,n)$, labels are (level, band, grid tag), and the coordinates of $c_0$ are split into row coordinates indexed by $\mathbb N$ and label coordinates indexed by labels. Fix $N$ and consider the levels $(i,n)$ with $i,n\le N$.
--
--   1. **Sparse embeddings.** An injective $j:A\to\mathbb N$ induces a linear isometric embedding $\ell^\infty(A)\to c_0$ by extension by zero. With the row and label coordinates, this gives the finite embedding of $\mathbb R^{F_N}$ into $c_0$. Here $F_N$ consists of the $N+1$ rows and the labels of the finitely many levels.
--   2. **Finite frozen map.** For frozen weights $W$, the map sends rows to $\mathrm{finiteRow}_{(i,N)}(x)$ and labels to $x_\gamma+v_\gamma(\mathrm{prev}(x)-\mathrm{row}(x))$. It agrees with the frozen shift on the embedded points and has norm at most $5$.
--   3. **Finite inverse.** Rows go to $\mathrm{finiteRow}_{(i,0)}(y)$, and labels to $y_\gamma-v_\gamma(\mathrm{row}(y)-\mathrm{next}(y))$. The row scalars satisfy $\mathrm{row}(\mathrm{inverse}(y))=\mathrm{next}(y)$ and $\mathrm{prev}(\mathrm{frozen}(x))=\mathrm{row}(x)$.
--   4. Hence the finite frozen map is a linear isomorphism of $\mathbb R^{F_N}$ with explicit inverse, the finite equivalence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Finite.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Finite.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles
import Definitions.Def_OAI_Analysis_C0Absorption_Blocks
import Definitions.Def_OAI_Analysis_C0Absorption_Correction
import Definitions.Def_OAI_Analysis_C0Absorption_Frozen
import Definitions.Def_OAI_Analysis_C0Absorption_Tags
import Definitions.Def_OAI_Analysis_C0Absorption_Operators
import Definitions.Def_OAI_Analysis_C0Absorption_Shift
import Definitions.Def_OAI_Analysis_C0Absorption_Space

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

section Sparse
variable {A : Type*} [Fintype A]

def sparseC0 (j : A → ℕ) (x : A → ℝ) : C0 :=
  cfunOfTendsto (Function.extend j x 0) (by
    apply tendsto_congr' (show Function.extend j x 0 =ᶠ[cofinite] fun _ => 0 from ?_) |>.mpr
      tendsto_const_nhds
    filter_upwards [(Set.finite_range j).compl_mem_cofinite] with k hk
    exact Function.extend_apply' _ _ _ hk)

@[simp] theorem sparseC0_apply (j : A → ℕ) (hj : Function.Injective j) (x : A → ℝ) (a : A) :
    sparseC0 j x (j a)=x a := hj.extend_apply _ _ a

theorem sparseC0_outside (j : A → ℕ) (x : A → ℝ) (k : ℕ) (hk : k∉Set.range j) :
    sparseC0 j x k=0 := Function.extend_apply' _ _ _ hk

theorem sparseC0_norm_le (j : A → ℕ) (hj : Function.Injective j) (x : A → ℝ) : ‖sparseC0 j x‖≤‖x‖ := by
  apply cfun_norm_le _ (norm_nonneg x)
  intro k
  by_cases hk : k∈Set.range j
  · obtain ⟨a,rfl⟩ := hk
    rw [sparseC0_apply j hj]
    exact norm_le_pi_norm x a
  · rw [sparseC0_outside j x k hk,abs_zero]
    exact norm_nonneg x

def sparseC0L (j : A → ℕ) (hj : Function.Injective j) : (A → ℝ) →L[ℝ] C0 :=
  LinearMap.mkContinuous
    { toFun := sparseC0 j
      map_add' := by
        intro x y
        ext k
        by_cases hk : k∈Set.range j
        · obtain ⟨a,rfl⟩ := hk
          simp only [sparseC0_apply j hj,ZeroAtInftyContinuousMap.add_apply,Pi.add_apply]
        · simp only [sparseC0_outside j _ k hk,ZeroAtInftyContinuousMap.add_apply,add_zero]
      map_smul' := by
        intro c x
        ext k
        by_cases hk : k∈Set.range j
        · obtain ⟨a,rfl⟩ := hk
          simp only [sparseC0_apply j hj,ZeroAtInftyContinuousMap.smul_apply,Pi.smul_apply,RingHom.id_apply]
        · simp only [sparseC0_outside j _ k hk,ZeroAtInftyContinuousMap.smul_apply,smul_zero] }
    1 (fun x => by
      change ‖sparseC0 j x‖≤1*‖x‖
      simpa only [one_mul] using sparseC0_norm_le j hj x)

theorem sparseC0_norm (j : A → ℕ) (hj : Function.Injective j) (x : A → ℝ) : ‖sparseC0 j x‖=‖x‖ := by
  apply le_antisymm (sparseC0_norm_le j hj x)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro a
  rw [← sparseC0_apply j hj x a]
  exact cfun_norm_apply_le _ _

def sparseC0Isometry (j : A → ℕ) (hj : Function.Injective j) : (A → ℝ) →ₗᵢ[ℝ] C0 where
  toLinearMap := (sparseC0L j hj).toLinearMap
  norm_map' := sparseC0_norm j hj

end Sparse

abbrev FLevel (N : ℕ) := Fin (N+1) × Fin (N+1)
abbrev FLabel (N : ℕ) := (lev : FLevel N) × Block (lev.1.val,lev.2.val)
abbrev FCoord (N : ℕ) := Sum (Fin (N+1)) (FLabel N)
abbrev FInput (N : ℕ) := FCoord N → ℝ

def fLabel {N : ℕ} (γ : FLabel N) : Label := blockLabel (γ.1.1.val,γ.1.2.val) γ.2

theorem fLabel_injective (N : ℕ) : Function.Injective (@fLabel N) := by
  rintro ⟨⟨i,n⟩,b⟩ ⟨⟨i',n'⟩,b'⟩ he
  have hl := congrArg Label.level he
  change (i.val,n.val)=(i'.val,n'.val) at hl
  have hi : i=i' := Fin.ext (Prod.mk.inj hl).1
  have hn : n=n' := Fin.ext (Prod.mk.inj hl).2
  subst i'; subst n'
  have hb : b=b' := blockLabel_injective _ he
  subst b'
  rfl

def fCoord {N : ℕ} : FCoord N → ℕ := Sum.elim (fun i => rowIndex i.val) (fun γ => labelIndex (fLabel γ))

theorem fCoord_injective (N : ℕ) : Function.Injective (@fCoord N) := by
  rintro (i|γ) (j|δ) he
  · exact congrArg Sum.inl (Fin.ext (rowIndex_injective he))
  · exact (rowIndex_ne_labelIndex i.val (fLabel δ) he).elim
  · exact (rowIndex_ne_labelIndex j.val (fLabel γ) he.symm).elim
  · exact congrArg Sum.inr (fLabel_injective N (labelIndex_injective he))

def finiteEmbed (N : ℕ) : FInput N →ₗᵢ[ℝ] C0 := sparseC0Isometry fCoord (fCoord_injective N)

@[simp] theorem finiteEmbed_apply {N : ℕ} (x : FInput N) (a : FCoord N) :
    finiteEmbed N x (fCoord a)=x a := sparseC0_apply _ (fCoord_injective N) x a

@[simp] theorem finiteEmbed_row {N : ℕ} (x : FInput N) (i : Fin (N+1)) :
    finiteEmbed N x (rowIndex i.val)=x (.inl i) := finiteEmbed_apply x (.inl i)

@[simp] theorem finiteEmbed_block {N : ℕ} (x : FInput N) (l : FLevel N) (b : Block (l.1.val,l.2.val)) :
    finiteEmbed N x (labelIndex (blockLabel (l.1.val,l.2.val) b))=x (.inr ⟨l,b⟩) := finiteEmbed_apply x (.inr ⟨l,b⟩)

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

def finiteRow (W : FrozenWeights) (l : FLevel N) (x : FInput N) : ℝ :=
  ∑ b : Block (l.1.val,l.2.val), W.row (l.1.val,l.2.val) b*x (.inr ⟨l,b⟩)

theorem finiteRow_eq (W : FrozenWeights) (l : FLevel N) (x : FInput N) :
    finiteRow W l x=rowScalar W (l.1.val,l.2.val) (finiteEmbed N x) := by
  rw [rowScalar_apply]
  simp only [finiteRow,blockInput,finiteEmbed_block]

theorem finiteRow_bound (W : FrozenWeights) (l : FLevel N) (x : FInput N) : |finiteRow W l x|≤2*‖x‖ := by
  unfold finiteRow
  exact (abs_finite_dot_le _ _ (fun b => norm_le_pi_norm x (.inr ⟨l,b⟩))).trans
    (mul_le_mul_of_nonneg_right (W.row_bound _) (norm_nonneg x))

def finPred (n : Fin (N+1)) : Fin (N+1) := ⟨n.val-1,(Nat.sub_le _ _).trans_lt n.isLt⟩

def finitePrev (W : FrozenWeights) (l : FLevel N) (x : FInput N) : ℝ :=
  if l.2.val=0 then x (.inl l.1) else finiteRow W (l.1,finPred l.2) x

theorem finitePrev_eq (W : FrozenWeights) (l : FLevel N) (x : FInput N) :
    finitePrev W l x=previousScalar W (l.1.val,l.2.val) (finiteEmbed N x) := by
  rcases l with ⟨i,⟨n,hn⟩⟩
  cases n with
  | zero => simp only [finitePrev,↓reduceIte,previousScalar,c0Eval_apply,finiteEmbed_row]
  | succ n =>
    simp only [finitePrev,Nat.succ_ne_zero,↓reduceIte,finiteRow_eq,finPred,Nat.add_sub_cancel,previousScalar]

def finiteFrozenFunction (W : FrozenWeights) (x : FInput N) : FInput N := fun a =>
  match a with
  | .inl i => finiteRow W (i,Fin.last N) x
  | .inr ⟨l,b⟩ => x (.inr ⟨l,b⟩)+W.vector (l.1.val,l.2.val) b*(finitePrev W l x-finiteRow W l x)

@[simp] theorem finiteFrozen_row (W : FrozenWeights) (x : FInput N) (i : Fin (N+1)) :
    finiteFrozenFunction W x (.inl i)=finiteRow W (i,Fin.last N) x := rfl

@[simp] theorem finiteFrozen_block (W : FrozenWeights) (x : FInput N) (γ : FLabel N) :
    finiteFrozenFunction W x (.inr γ)=frozenShift W (finiteEmbed N x) (fLabel γ) := by
  rcases γ with ⟨l,b⟩
  rw [frozenShift_apply,frozenCorrection_apply]
  change x (.inr ⟨l,b⟩)+W.vector (l.1.val,l.2.val) b*(finitePrev W l x-finiteRow W l x)=
    finiteEmbed N x (labelIndex (blockLabel (l.1.val,l.2.val) b))+W.vector (l.1.val,l.2.val) b*
      (previousScalar W (l.1.val,l.2.val) (finiteEmbed N x)-rowScalar W (l.1.val,l.2.val) (finiteEmbed N x))
  rw [finiteEmbed_block,finitePrev_eq,finiteRow_eq]

theorem finiteFrozen_bound (W : FrozenWeights) (x : FInput N) : ‖finiteFrozenFunction W x‖≤5*‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg x))).mpr
  rintro (i|γ)
  · change |finiteRow W (i,Fin.last N) x|≤_
    exact (finiteRow_bound W _ x).trans (by nlinarith [norm_nonneg x])
  · rw [finiteFrozen_block]
    exact (cfun_norm_apply_le _ _).trans ((frozenShift_bound W (finiteEmbed N x)).trans_eq (by rw [LinearIsometry.norm_map]))

def finiteFrozen (N : ℕ) (W : FrozenWeights) : FInput N →L[ℝ] FInput N :=
  LinearMap.mkContinuous
    { toFun := finiteFrozenFunction W
      map_add' := by
        intro x y
        funext a
        cases a with
        | inl i => simp only [finiteFrozen_row,finiteRow_eq,map_add,Pi.add_apply]
        | inr γ => simp only [finiteFrozen_block,map_add,ZeroAtInftyContinuousMap.add_apply,Pi.add_apply]
      map_smul' := by
        intro c x
        funext a
        cases a with
        | inl i => simp only [finiteFrozen_row,finiteRow_eq,map_smul,Pi.smul_apply,RingHom.id_apply]
        | inr γ => simp only [finiteFrozen_block,map_smul,ZeroAtInftyContinuousMap.smul_apply,Pi.smul_apply,RingHom.id_apply] }
    5 (finiteFrozen_bound W)

def finiteNext (W : FrozenWeights) (l : FLevel N) (y : FInput N) : ℝ :=
  if h : l.2.val<N then finiteRow W (l.1,⟨l.2.val+1,by omega⟩) y else y (.inl l.1)

def finiteInverseFunction (W : FrozenWeights) (y : FInput N) : FInput N := fun a =>
  match a with
  | .inl i => finiteRow W (i,0) y
  | .inr ⟨l,b⟩ => y (.inr ⟨l,b⟩)-W.vector (l.1.val,l.2.val) b*(finiteRow W l y-finiteNext W l y)

@[simp] theorem finiteInverse_row (W : FrozenWeights) (y : FInput N) (i : Fin (N+1)) :
    finiteInverseFunction W y (.inl i)=finiteRow W (i,0) y := rfl

@[simp] theorem finiteInverse_block (W : FrozenWeights) (y : FInput N) (l : FLevel N) (b : Block (l.1.val,l.2.val)) :
    finiteInverseFunction W y (.inr ⟨l,b⟩)=y (.inr ⟨l,b⟩)-W.vector (l.1.val,l.2.val) b*(finiteRow W l y-finiteNext W l y) := rfl

theorem finiteRow_inverse (W : FrozenWeights) (y : FInput N) (l : FLevel N) :
    finiteRow W l (finiteInverseFunction W y)=finiteNext W l y := by
  unfold finiteRow
  simp only [finiteInverse_block]
  rw [finite_row_cancel _ _ _ (W.pairing _)]
  change finiteRow W l y-(finiteRow W l y-finiteNext W l y)=_
  ring

theorem finitePrev_inverse (W : FrozenWeights) (y : FInput N) (l : FLevel N) :
    finitePrev W l (finiteInverseFunction W y)=finiteRow W l y := by
  unfold finitePrev
  split_ifs with hn
  · have he : l.2=0 := Fin.ext hn
    rcases l with ⟨i,n⟩
    dsimp at he
    subst n
    rfl
  · rw [finiteRow_inverse]
    have hp : (finPred l.2).val<N := by have := l.2.isLt; dsimp [finPred]; omega
    simp only [finiteNext,hp,↓reduceDIte]
    congr 2
    apply Fin.ext
    dsimp [finPred]
    omega

theorem finiteFrozen_inverse (W : FrozenWeights) (y : FInput N) : finiteFrozen N W (finiteInverseFunction W y)=y := by
  funext a
  cases a with
  | inl i =>
    change finiteRow W (i,Fin.last N) (finiteInverseFunction W y)=_
    rw [finiteRow_inverse]
    simp only [finiteNext,Fin.val_last,lt_self_iff_false,↓reduceDIte]
  | inr γ =>
    rcases γ with ⟨l,b⟩
    change finiteInverseFunction W y (.inr ⟨l,b⟩)+_=_
    rw [finiteInverse_block,finitePrev_inverse,finiteRow_inverse]
    ring

theorem finiteRow_frozen (W : FrozenWeights) (x : FInput N) (l : FLevel N) :
    finiteRow W l (finiteFrozen N W x)=finitePrev W l x := by
  unfold finiteRow
  change (∑ b : Block (l.1.val,l.2.val), W.row (l.1.val,l.2.val) b*
    (x (.inr ⟨l,b⟩)+W.vector (l.1.val,l.2.val) b*(finitePrev W l x-finiteRow W l x)))=_
  rw [finite_row_shift _ _ _ (W.pairing _)]
  change finiteRow W l x+(finitePrev W l x-finiteRow W l x)=_
  ring

theorem finiteNext_frozen (W : FrozenWeights) (x : FInput N) (l : FLevel N) :
    finiteNext W l (finiteFrozen N W x)=finiteRow W l x := by
  unfold finiteNext
  split_ifs with hn
  · rw [finiteRow_frozen]
    simp only [finitePrev,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte]
    congr 2
  · have he : l.2=Fin.last N := Fin.ext (by have := l.2.isLt; simp only [Fin.val_last]; omega)
    change finiteRow W (l.1,Fin.last N) x=finiteRow W l x
    rw [← he]

theorem finiteInverse_frozen (W : FrozenWeights) (x : FInput N) : finiteInverseFunction W (finiteFrozen N W x)=x := by
  funext a
  cases a with
  | inl i =>
    rw [finiteInverse_row,finiteRow_frozen]
    rfl
  | inr γ =>
    rcases γ with ⟨l,b⟩
    rw [finiteInverse_block,finiteRow_frozen,finiteNext_frozen]
    change x (.inr ⟨l,b⟩)+_ - _=x (.inr ⟨l,b⟩)
    ring

def finiteEquiv (N : ℕ) (W : FrozenWeights) : FInput N ≃L[ℝ] FInput N :=
  ContinuousLinearEquiv.ofBijective (finiteFrozen N W)
    (LinearMap.ker_eq_bot.mpr (fun x y h => by
      change finiteFrozen N W x=finiteFrozen N W y at h
      simpa only [finiteInverse_frozen] using congrArg (finiteInverseFunction W) h))
    (LinearMap.range_eq_top.mpr (fun y => ⟨finiteInverseFunction W y,finiteFrozen_inverse W y⟩))

end
end C0Absorption

end OAI


