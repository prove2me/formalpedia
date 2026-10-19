-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Operators
-- name    : OAI_Analysis_C0Absorption_Operators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:33:09.922767+00:00
-- url     : https://prove2.me/theorems/f0925c0e-1a87-4170-a3c7-9c0ab0a0ed11
-- title:
--   Coordinate splittings of c0 and the correction operators
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. Levels are pairs $(i,n)$, labels are (level, band, grid tag), and the coordinates of $c_0$ are split into row coordinates indexed by $\mathbb N$ and label coordinates indexed by labels. For a discrete index set $A$, $C_0(A)$ is the space of functions tending to zero along the cofinite filter, with the sup norm.
--
--   1. **Pullbacks.** A map $j:A\to B$ with finite fibres induces a norm-one operator $C_0(B)\to C_0(A)$, $f\mapsto f\circ j$.
--   2. **Splitting.** With the row and label enumerations, $x\mapsto(\text{row part},\text{label part})$ is a linear isometric isomorphism
--   $$
--   c_0\cong c_0\times C_0(\mathrm{Labels}).
--   $$
--   3. **Corrections.** For frozen weights $W$, the corrections $\gamma\mapsto\mathrm{corr}_W(\gamma)(x)$ tend to zero along labels. They define a bounded operator $c_0\to C_0(\mathrm{Labels})$ of norm at most $4$. For $s$ in the unit ball, $\mathrm{correctionC0}(s)$ uses the state weights of $s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Operators.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Operators.lean by skeleton subtraction
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

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section GeneralC0
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [DiscreteTopology A] [DiscreteTopology B]

def cfunOfTendsto (f : A → ℝ) (hf : Tendsto f cofinite (nhds 0)) : C₀(A,ℝ) where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by simpa only [cocompact_eq_cofinite] using hf

theorem cfun_tendsto (f : C₀(A,ℝ)) : Tendsto f cofinite (nhds 0) := by
  simpa only [cocompact_eq_cofinite] using zero_at_infty f

theorem cfun_norm_apply_le {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (f : C₀(A,ℝ)) (a : A) : |f a|≤‖f‖ := f.toBCF.norm_coe_le_norm a

theorem cfun_norm_le {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (f : C₀(A,ℝ)) {r : ℝ} (hr : 0≤r) (h : ∀ a,|f a|≤r) : ‖f‖≤r :=
  (f.toBCF.norm_le hr).mpr h

def cfunPull (j : A → B) (hj : Tendsto j cofinite cofinite) (f : C₀(B,ℝ)) : C₀(A,ℝ) :=
  cfunOfTendsto (fun a => f (j a)) ((cfun_tendsto f).comp hj)

@[simp] theorem cfunPull_apply (j : A → B) (hj : Tendsto j cofinite cofinite) (f : C₀(B,ℝ)) (a : A) :
    cfunPull j hj f a=f (j a) := rfl

def cfunPullL (j : A → B) (hj : Tendsto j cofinite cofinite) : C₀(B,ℝ) →L[ℝ] C₀(A,ℝ) :=
  LinearMap.mkContinuous
    { toFun := cfunPull j hj
      map_add' := by intro f g; ext a; rfl
      map_smul' := by intro c f; ext a; rfl } 1 (fun f => by
        change ‖cfunPull j hj f‖≤1*‖f‖
        rw [one_mul]
        exact cfun_norm_le _ (norm_nonneg _) (fun a => cfun_norm_apply_le f (j a)))

@[simp] theorem cfunPullL_apply (j : A → B) (hj : Tendsto j cofinite cofinite) (f : C₀(B,ℝ)) (a : A) :
    cfunPullL j hj f a=f (j a) := rfl

end GeneralC0

theorem tendsto_sumElim_cofinite {A B : Type*} {X : Type*} (f : A → X) (g : B → X)
    (l : Filter X) (hf : Tendsto f cofinite l) (hg : Tendsto g cofinite l) :
    Tendsto (Sum.elim f g) cofinite l := by
  intro s hs
  have h1 : {a | f a∉s}.Finite := hf hs
  have h2 : {b | g b∉s}.Finite := hg hs
  apply ((h1.image Sum.inl).union (h2.image Sum.inr)).subset
  intro x hx
  cases x with
  | inl a => exact Or.inl ⟨a,hx,rfl⟩
  | inr b => exact Or.inr ⟨b,hx,rfl⟩

abbrev BlockC0 := C₀(Label,ℝ)

def inputRows : C0 →L[ℝ] C0 := cfunPullL rowIndex rowIndex_injective.tendsto_cofinite

def inputBlocks : C0 →L[ℝ] BlockC0 := cfunPullL labelIndex labelIndex_injective.tendsto_cofinite

@[simp] theorem inputRows_apply (x : C0) (i : ℕ) : inputRows x i=x (rowIndex i) := rfl
@[simp] theorem inputBlocks_apply (x : C0) (γ : Label) : inputBlocks x γ=x (labelIndex γ) := rfl

def joinInputs (x : C0 × BlockC0) : C0 :=
  cfunOfTendsto (fun k => Sum.elim x.1 x.2 (coordinateEnumeration.symm k))
    ((tendsto_sumElim_cofinite x.1 x.2 (nhds 0) (cfun_tendsto x.1) (cfun_tendsto x.2)).comp
      coordinateEnumeration.symm.injective.tendsto_cofinite)

@[simp] theorem joinInputs_row (x : C0 × BlockC0) (i : ℕ) : joinInputs x (rowIndex i)=x.1 i := by
  change Sum.elim x.1 x.2 (coordinateEnumeration.symm (coordinateEnumeration (Sum.inl i)))=x.1 i
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem joinInputs_block (x : C0 × BlockC0) (γ : Label) : joinInputs x (labelIndex γ)=x.2 γ := by
  change Sum.elim x.1 x.2 (coordinateEnumeration.symm (coordinateEnumeration (Sum.inr γ)))=x.2 γ
  rw [Equiv.symm_apply_apply]
  rfl

theorem joinInputs_split (x : C0) : joinInputs (inputRows x,inputBlocks x)=x := by
  ext k
  obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
  cases a with
  | inl i => exact joinInputs_row _ i
  | inr γ => exact joinInputs_block _ γ

theorem joinInputs_norm (x : C0 × BlockC0) : ‖joinInputs x‖=‖x‖ := by
  apply le_antisymm
  · apply cfun_norm_le _ (norm_nonneg x)
    intro k
    obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
    cases a with
    | inl i => exact (show |joinInputs x (rowIndex i)|≤‖x.1‖ by rw [joinInputs_row]; exact cfun_norm_apply_le _ _).trans (le_max_left _ _)
    | inr γ => exact (show |joinInputs x (labelIndex γ)|≤‖x.2‖ by rw [joinInputs_block]; exact cfun_norm_apply_le _ _).trans (le_max_right _ _)
  · rw [Prod.norm_def]
    apply max_le
    · apply cfun_norm_le _ (norm_nonneg _)
      intro i
      rw [← joinInputs_row x i]
      exact cfun_norm_apply_le _ _
    · apply cfun_norm_le _ (norm_nonneg _)
      intro γ
      rw [← joinInputs_block x γ]
      exact cfun_norm_apply_le _ _

def inputCoordinates : (C0 × BlockC0) ≃ₗᵢ[ℝ] C0 where
  toFun := joinInputs
  invFun := fun x => (inputRows x,inputBlocks x)
  left_inv := by
    intro x
    apply Prod.ext <;> ext k
    · exact joinInputs_row x k
    · exact joinInputs_block x k
  right_inv := joinInputs_split
  map_add' := by
    intro x y
    ext k
    obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
    cases a with
    | inl i => simp only [show coordinateEnumeration (Sum.inl i)=rowIndex i from rfl,joinInputs_row,Prod.fst_add,ZeroAtInftyContinuousMap.add_apply]
    | inr γ => simp only [show coordinateEnumeration (Sum.inr γ)=labelIndex γ from rfl,joinInputs_block,Prod.snd_add,ZeroAtInftyContinuousMap.add_apply]
  map_smul' := by
    intro c x
    ext k
    obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
    cases a with
    | inl i => simp only [show coordinateEnumeration (Sum.inl i)=rowIndex i from rfl,joinInputs_row,ZeroAtInftyContinuousMap.smul_apply]; rfl
    | inr γ => simp only [show coordinateEnumeration (Sum.inr γ)=labelIndex γ from rfl,joinInputs_block,ZeroAtInftyContinuousMap.smul_apply]; rfl
  norm_map' := joinInputs_norm

theorem labelLevel_tendsto : Tendsto Label.level cofinite cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton (fun lev => labels_at_level_finite lev)

theorem labelRadius_tendsto (x : C0) : Tendsto (fun γ : Label => localRadius γ.level x) cofinite (nhds 0) :=
  (localRadius_tendsto x).comp labelLevel_tendsto

theorem frozenCorrection_tendsto (W : FrozenWeights) (x : C0) :
    Tendsto (fun γ => frozenCorrection W γ x) cofinite (nhds 0) := by
  apply squeeze_zero_norm (fun γ => frozenCorrection_local W γ x) _
  simpa only [mul_zero] using (labelRadius_tendsto x).const_mul 4

def frozenCorrectionC0 (W : FrozenWeights) (x : C0) : BlockC0 :=
  cfunOfTendsto (fun γ => frozenCorrection W γ x) (frozenCorrection_tendsto W x)

def frozenCorrectionL (W : FrozenWeights) : C0 →L[ℝ] BlockC0 :=
  LinearMap.mkContinuous
    { toFun := frozenCorrectionC0 W
      map_add' := by intro x y; ext γ; exact map_add (frozenCorrection W γ) x y
      map_smul' := by intro c x; ext γ; exact map_smul (frozenCorrection W γ) c x }
    4 (fun x => by
      change ‖frozenCorrectionC0 W x‖≤4*‖x‖
      exact cfun_norm_le _ (mul_nonneg (by norm_num) (norm_nonneg _)) (fun γ => frozenCorrection_bound W γ x))

@[simp] theorem frozenCorrectionL_apply (W : FrozenWeights) (x : C0) (γ : Label) :
    frozenCorrectionL W x γ=frozenCorrection W γ x := rfl

def correctionC0 (s : C0Ball) : BlockC0 := frozenCorrectionL (stateWeights s) s.val

@[simp] theorem correctionC0_apply (s : C0Ball) (γ : Label) : correctionC0 s γ=correction γ s := rfl

end
end C0Absorption

end OAI


