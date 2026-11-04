-- Prove2me | Definitions.Def_FreeGroupFactorProof09
-- name    : FreeGroupFactorProof09
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T01:37:58.836015+00:00
-- url     : https://prove2.me/theorems/145f21fb-260a-4e64-8bbf-055f891f1ded
-- title:
--   Free group factors: supporting development, part 9
-- statement:
--   Part 9 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof08

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.CyclicSpectral
open MeasureTheory ProbabilityTheory Set
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (ξ : E)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

end FreeGroupFactorMain.CyclicSpectral

section
open scoped ENNReal

namespace FreeGroupFactorMain.CyclicSpectral

section
open MeasureTheory
variable {H : Type u_2} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] fgfLocalInst_47_8
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
section
open MeasureTheory Filter
variable {H : Type u_3} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] fgfLocalInst_47_15
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
open MeasureTheory Filter
variable {H : Type u_4} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] fgfLocalInst_47_22
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end FreeGroupFactorMain.CyclicSpectral

end

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification MeasureTheory CyclicSpectral

variable (u v : ℝ)

end

open FreeFock Amplification
variable {ι : Type u_5} [DecidableEq ι]

theorem pRepresentation_vacuumTrace (u v : ℝ) (hu : u≠0) (x : PCorner ι) :
    pVacuumTrace u v (x:Operator ι)=inner ℂ (pRoot:PRange ι) (pRepresentation x pRoot) := by
  have he : inner ℂ ((P:Operator ι) (vacuum u v)) ((x:Operator ι) (P (vacuum u v)))=
      vacuumTrace u v (x:Operator ι) := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (vacuum u v) ((star (P:Operator ι)*(x:Operator ι)*P : Operator ι) (vacuum u v))=_
    rw [projection_P.isSelfAdjoint.star_eq,x.property.1,x.property.2]
    rfl
  rw [pRoot_vacuum u v, map_smul,inner_smul_left,inner_smul_right] at he
  rw [pVacuumTrace,← he]
  change (u:ℂ)⁻¹*(u:ℂ)⁻¹*(star (u:ℂ)*((u:ℂ)*inner ℂ ((pRoot:PRange ι):H ι)
    ((x:Operator ι) ((pRoot:PRange ι):H ι))))=_
  rw [Complex.star_def,Complex.conj_ofReal]
  have hu' := Complex.ofReal_ne_zero.mpr hu
  calc
    _ = inner ℂ ((pRoot:PRange ι):H ι) ((x:Operator ι) ((pRoot:PRange ι):H ι)) := by field_simp
    _ = _ := by rw [← pRepresentation_apply]; rfl

theorem pAnnihilator_root (u v : ℝ) (hu : u≠0) (X : PCorner ℕ)
    (hX : X∈oldAnnihilators u v) (a : Base u v) :
    star (pRepresentation X) (pRepresentation a.val pRoot)=0 := by
  have hr (x : PCorner ℕ) : (x:Operator ℕ) (vacuum u v)=(u:ℂ) • (x:Operator ℕ) ((pRoot:PRange ℕ):H ℕ) := by
    have he := DFunLike.congr_fun x.property.2 (vacuum u v)
    change (x:Operator ℕ) (P (vacuum u v))=(x:Operator ℕ) (vacuum u v) at he
    rw [pRoot_vacuum,map_smul] at he
    exact he.symm
  have hh := hX a
  rw [hr,map_smul] at hh
  have hz : star (X:Operator ℕ) ((a.val:Operator ℕ) ((pRoot:PRange ℕ):H ℕ))=0 :=
    (smul_eq_zero.mp hh).resolve_left (Complex.ofReal_ne_zero.mpr hu)
  have he := (pRepresentation (ι := ℕ)).map_star' X
  change pRepresentation (star X)=star (pRepresentation X) at he
  rw [← he]
  apply Subtype.ext
  change (pRepresentation (star X) (pRepresentation a.val pRoot) : H ℕ)=0
  rw [pRepresentation_apply,pRepresentation_apply]
  exact hz
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

section
namespace FreeGroupFactorMain.GramSpatial
variable {I : Type u_1} {E : Type u_2} {F : Type u_3}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem combination_inner (x : I → E) (y : I → F)
    (hg : ∀ i j, inner ℂ (y i) (y j)=inner ℂ (x i) (x j)) (a b : I →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ y a) (Finsupp.linearCombination ℂ y b)=
      inner ℂ (Finsupp.linearCombination ℂ x a) (Finsupp.linearCombination ℂ x b) := by
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,inner_sum, sum_inner,
    inner_smul_left,inner_smul_right,hg]

omit [CompleteSpace E] [CompleteSpace F] in
theorem combination_norm (x : I → E) (y : I → F)
    (hg : ∀ i j, inner ℂ (y i) (y j)=inner ℂ (x i) (x j)) (a : I →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ y a‖=‖Finsupp.linearCombination ℂ x a‖ := by
  have hs : ‖Finsupp.linearCombination ℂ y a‖^2=‖Finsupp.linearCombination ℂ x a‖^2 := by
    simpa only [inner_self_eq_norm_sq] using
      congrArg (RCLike.re : ℂ → ℝ) (combination_inner x y hg a a)
  nlinarith [norm_nonneg (Finsupp.linearCombination ℂ y a),
    norm_nonneg (Finsupp.linearCombination ℂ x a)]

omit [CompleteSpace E] in
theorem combination_dense (x : I → E)
    (hx : (Submodule.span ℂ (Set.range x)).topologicalClosure=⊤) :
    DenseRange (Finsupp.linearCombination ℂ x) := by
  rw [denseRange_iff_closure_range]
  change closure ((Finsupp.linearCombination ℂ x).range : Set E)=Set.univ
  rw [Finsupp.range_linearCombination,← Submodule.topologicalClosure_coe,hx]
  rfl

def spatial (x : I → E) (y : I → F)
    (hg : ∀ i j, inner ℂ (y i) (y j)=inner ℂ (x i) (x j))
    (hx : (Submodule.span ℂ (Set.range x)).topologicalClosure=⊤)
    (hy : (Submodule.span ℂ (Set.range y)).topologicalClosure=⊤) : E ≃ₗᵢ[ℂ] F :=
  (LinearEquiv.refl ℂ (I →₀ ℂ)).extendOfIsometry
    (Finsupp.linearCombination ℂ x) (Finsupp.linearCombination ℂ y)
    (combination_dense x hx) (combination_dense y hy) (combination_norm x y hg)

theorem spatial_combination (x : I → E) (y : I → F)
    (hg : ∀ i j, inner ℂ (y i) (y j)=inner ℂ (x i) (x j))
    (hx : (Submodule.span ℂ (Set.range x)).topologicalClosure=⊤)
    (hy : (Submodule.span ℂ (Set.range y)).topologicalClosure=⊤) (a : I →₀ ℂ) :
    spatial x y hg hx hy (Finsupp.linearCombination ℂ x a)=Finsupp.linearCombination ℂ y a :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ a

theorem spatial_family (x : I → E) (y : I → F)
    (hg : ∀ i j, inner ℂ (y i) (y j)=inner ℂ (x i) (x j))
    (hx : (Submodule.span ℂ (Set.range x)).topologicalClosure=⊤)
    (hy : (Submodule.span ℂ (Set.range y)).topologicalClosure=⊤) (i : I) :
    spatial x y hg hx hy (x i)=y i := by
  simpa only [Finsupp.linearCombination_single,one_smul] using
    spatial_combination x y hg hx hy (Finsupp.single i 1)

theorem spatial_intertwines (x : I → E) (y : I → F)
    (hg : ∀ i j, inner ℂ (y i) (y j)=inner ℂ (x i) (x j))
    (hx : (Submodule.span ℂ (Set.range x)).topologicalClosure=⊤)
    (hy : (Submodule.span ℂ (Set.range y)).topologicalClosure=⊤)
    (T : E →L[ℂ] E) (U : F →L[ℂ] F) (d : I → (I →₀ ℂ))
    (hT : ∀ i, T (x i)=Finsupp.linearCombination ℂ x (d i))
    (hU : ∀ i, U (y i)=Finsupp.linearCombination ℂ y (d i)) :
    (spatial x y hg hx hy).conjStarAlgEquiv T=U := by
  let W := spatial x y hg hx hy
  have hI (i : I) : W (T (x i))=U (W (x i)) := by
    rw [hT,show W (Finsupp.linearCombination ℂ x (d i))=
      Finsupp.linearCombination ℂ y (d i) from spatial_combination x y hg hx hy _,
      show W (x i)=y i from spatial_family x y hg hx hy _,hU]
  have hall (a : I →₀ ℂ) :
      W (T (Finsupp.linearCombination ℂ x a))=U (W (Finsupp.linearCombination ℂ x a)) := by
    simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,hI]
  have hd : ∀ z : E, W (T z)=U (W z) := by
    intro z
    exact (combination_dense x hx).induction_on z
      (isClosed_eq (W.continuous.comp T.continuous) (U.continuous.comp W.continuous)) hall
  apply ContinuousLinearMap.ext
  intro z
  change W (T (W.symm z))=U z
  rw [hd,W.apply_symm_apply]

end FreeGroupFactorMain.GramSpatial
namespace FreeGroupFactorMain.GaussianRecognition
variable (A : Type u_4) (E : Type u_5) (I : Type u_6) [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
abbrev Operator := E →L[ℂ] E

structure System (covariance : I → I → A → A) where
  coeff : A →⋆ₐ[ℂ] Operator E
  root : E
  create : I → Operator E
  contract : ∀ i j a, star (create i)*coeff a*create j=coeff (covariance i j a)
  annihilate : ∀ i a, star (create i) (coeff a root)=0

variable {A E I} {covariance : I → I → A → A}
variable (X : System A E I covariance)

abbrev Word (A : Type u_7) (I : Type u_8) := A × List (I × A)

namespace System

def normal (a : A) : List (I × A) → E
  | [] => X.coeff a X.root
  | (i,b)::w => X.coeff a (X.create i (normal b w))

def family (w : Word A I) : E := X.normal w.1 w.2

theorem coeff_normal (c a : A) (w : List (I × A)) :
    X.coeff c (X.normal a w)=X.normal (c*a) w := by
  cases w with
  | nil => simp only [normal,map_mul,mul_apply_eq_comp]
  | cons z w => rcases z with ⟨i,b⟩; simp only [normal,map_mul,mul_apply_eq_comp]

theorem create_normal (i : I) (a : A) (w : List (I × A)) :
    X.create i (X.normal a w)=X.normal 1 ((i,a)::w) := by
  simp only [normal,map_one,one_apply_eq_self]

theorem annihilate_normal_nil (i : I) (a : A) :
    star (X.create i) (X.normal a [])=0 := X.annihilate i a

theorem annihilate_normal_cons (i j : I) (a b : A) (w : List (I × A)) :
    star (X.create i) (X.normal a ((j,b)::w))=
      X.normal (covariance i j a*b) w := by
  have hc := DFunLike.congr_fun (X.contract i j a) (X.normal b w)
  simpa only [normal,mul_apply_eq_comp,coeff_normal] using hc

theorem left_inner (i j : I) (a b : A) (ξ ζ : E) :
    inner ℂ (X.coeff a (X.create i ξ)) (X.coeff b (X.create j ζ))=
      inner ℂ ξ (X.coeff (covariance i j (star a*b)) ζ) := by
  have hc := X.contract i j (star a*b)
  rw [map_mul,map_star] at hc
  calc
    _ = inner ℂ ξ ((star (X.create i)*(star (X.coeff a)*X.coeff b)*X.create j) ζ) := by
      simp only [mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    _ = _ := by rw [hc]

theorem old_left_inner (i : I) (a b : A) (ζ : E) :
    inner ℂ (X.coeff a X.root) (X.coeff b (X.create i ζ))=0 := by
  have hz := X.annihilate i (star b*a)
  rw [map_mul,map_star,mul_apply_eq_comp] at hz
  calc
    _ = inner ℂ (star (X.create i) (star (X.coeff b) (X.coeff a X.root))) ζ := by
      simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
    _ = _ := by rw [hz,inner_zero_left]

theorem root_inner (a b : A) :
    inner ℂ (X.normal a []) (X.normal b [])=
      inner ℂ X.root (X.coeff (star a*b) X.root) := by
  simp only [normal,map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

variable {F : Type u_9} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (Y : System A F I covariance)

theorem normal_inner_eq
    (hstate : ∀ a, inner ℂ Y.root (Y.coeff a Y.root)=inner ℂ X.root (X.coeff a X.root))
    (a b : A) (w z : List (I × A)) :
    inner ℂ (Y.normal a w) (Y.normal b z)=inner ℂ (X.normal a w) (X.normal b z) := by
  induction w generalizing a b z with
  | nil =>
    cases z with
    | nil => rw [root_inner,root_inner,hstate]
    | cons q z =>
      rcases q with ⟨j,c⟩
      simp only [normal,old_left_inner]
  | cons q w ih =>
    rcases q with ⟨i,c⟩
    cases z with
    | nil =>
      have hX := X.old_left_inner i b a (X.normal c w)
      have hY := Y.old_left_inner i b a (Y.normal c w)
      have hcX := inner_conj_symm (𝕜 := ℂ) (X.normal a ((i,c)::w)) (X.normal b [])
      have hcY := inner_conj_symm (𝕜 := ℂ) (Y.normal a ((i,c)::w)) (Y.normal b [])
      change star (inner ℂ (X.coeff b X.root) (X.coeff a (X.create i (X.normal c w))))=_ at hcX
      change star (inner ℂ (Y.coeff b Y.root) (Y.coeff a (Y.create i (Y.normal c w))))=_ at hcY
      rw [hX,star_zero] at hcX
      rw [hY,star_zero] at hcY
      exact hcY.symm.trans hcX
    | cons q z =>
      rcases q with ⟨j,d⟩
      change inner ℂ (Y.coeff a (Y.create i (Y.normal c w)))
        (Y.coeff b (Y.create j (Y.normal d z)))=
        inner ℂ (X.coeff a (X.create i (X.normal c w)))
          (X.coeff b (X.create j (X.normal d z)))
      rw [Y.left_inner,X.left_inner,Y.coeff_normal,X.coeff_normal]
      exact ih c (covariance i j (star a*b)*d) z

def generator (σ : I → I) (i : I) : Operator E := X.create i+star (X.create (σ i))

def generatorRule (σ : I → I) (covariance : I → I → A → A) (i : I)
    (w : Word A I) : Word A I →₀ ℂ := by
  classical
  exact Finsupp.single ((1:A),(i,w.1)::w.2) (1:ℂ) +
    match w.2 with
    | [] => 0
    | (j,b)::z => Finsupp.single (covariance (σ i) j w.1*b,z) (1:ℂ)

theorem generator_family (σ : I → I) (i : I) (w : Word A I) :
    X.generator σ i (X.family w)=
      Finsupp.linearCombination ℂ X.family (generatorRule σ covariance i w) := by
  classical
  rcases w with ⟨a,w⟩
  cases w with
  | nil =>
    simp only [generator,family,add_apply,annihilate_normal_nil,add_zero,
      generatorRule,Finsupp.linearCombination_single,one_smul,create_normal]
  | cons q w =>
    rcases q with ⟨j,b⟩
    simp only [generator,family,add_apply,annihilate_normal_cons,
      generatorRule,map_add,Finsupp.linearCombination_single,one_smul,create_normal]

def coeffRule (c : A) (w : Word A I) : Word A I →₀ ℂ := by
  classical
  exact Finsupp.single (c*w.1,w.2) 1

theorem coeff_family (c : A) (w : Word A I) :
    X.coeff c (X.family w)=Finsupp.linearCombination ℂ X.family (coeffRule c w) := by
  classical
  simp only [family,coeffRule,Finsupp.linearCombination_single,one_smul,coeff_normal]

variable
  (hstate : ∀ a, inner ℂ Y.root (Y.coeff a Y.root)=inner ℂ X.root (X.coeff a X.root))
  (hX : (Submodule.span ℂ (Set.range X.family)).topologicalClosure=⊤)
  (hY : (Submodule.span ℂ (Set.range Y.family)).topologicalClosure=⊤)

def spatial : E ≃ₗᵢ[ℂ] F :=
  GramSpatial.spatial X.family Y.family
    (fun w z => normal_inner_eq X Y hstate w.1 z.1 w.2 z.2) hX hY

theorem spatial_coeff (a : A) :
    (spatial X Y hstate hX hY).conjStarAlgEquiv (X.coeff a)=Y.coeff a := by
  apply GramSpatial.spatial_intertwines X.family Y.family _ hX hY
    (X.coeff a) (Y.coeff a) (coeffRule a)
  · exact X.coeff_family a
  · exact Y.coeff_family a

theorem spatial_generator (σ : I → I) (i : I) :
    (spatial X Y hstate hX hY).conjStarAlgEquiv (X.generator σ i)=Y.generator σ i := by
  apply GramSpatial.spatial_intertwines X.family Y.family _ hX hY
    (X.generator σ i) (Y.generator σ i) (generatorRule σ covariance i)
  · exact X.generator_family σ i
  · exact Y.generator_family σ i

end System
end FreeGroupFactorMain.GaussianRecognition

end

namespace FreeGroupFactorMain.GaussianRecognition
open CyclicSpectral

def uniformCovariance {I : Type u_10} [DecidableEq I] (i j : I) (a : UniformAlgebra) : UniformAlgebra :=
  if i=j then uniformState a • 1 else 0
end FreeGroupFactorMain.GaussianRecognition

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification CyclicSpectral GaussianRecognition WeightedCornerIndex

theorem weightedUniformBase_rep (u v : ℝ) (hv : 0<v) (hvu : v<u) (a : UniformAlgebra) :
    pRepresentation ((weightedUniformBase u v hv hvu a).val)=weightedUniform u v hv hvu a :=
  (pRepresentation (ι := ℕ)).apply_symm_apply _

theorem cornerAbsorption_trace (u v : ℝ) (hv : 0<v) (hvu : v<u) :
    (cornerAbsorption u v hv hvu).τ=pTrace u v 0 1 := rfl

theorem weightedUniformBase_trace (u v : ℝ) (hv : 0<v) (hvu : v<u) (a : UniformAlgebra) :
    pTrace u v 0 1 (weightedUniformBase u v hv hvu a)=uniformState a := by
  change pVacuumTrace u v ((weightedUniformBase u v hv hvu a).val:Operator ℕ)=_
  rw [pRepresentation_vacuumTrace u v (hv.trans hvu).ne',weightedUniformBase_rep]
  exact weightedUniform_state u v hv hvu a

def absorbedCreation (u v : ℝ) (hv : 0<v) (hvu : v<u) (i : WeightedCornerIndex.Index × ℕ) :
    PRange ℕ →L[ℂ] PRange ℕ :=
  pRepresentation ((cornerAbsorption u v hv hvu).output i.1 i.2)

end FreeGroupFactorMain.WeightedFock

end

end OAI
end


