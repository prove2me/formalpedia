-- Prove2me | Definitions.Def_FreeGroupFactorProof33
-- name    : FreeGroupFactorProof33
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T05:11:14.396871+00:00
-- url     : https://prove2.me/theorems/57f2675a-ab82-4ea6-a1d0-cf6166dfd6b7
-- title:
--   Free group factors: supporting development, part 33
-- statement:
--   Part 33 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof32

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25

namespace FreeGroupFactorMain.Amplification
namespace OperatorSum
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end OperatorSum
end FreeGroupFactorMain.Amplification
namespace FreeGroupFactorMain.Amplification.OperatorSum

section
variable {E : Type u_16} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type u_17} {U : ι → Operator E}

end
variable {E : Type u_18} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain.Amplification.OperatorSum
namespace FreeGroupFactorMain.Amplification.Polar
variable {E : Type u_21} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain.Amplification.Polar
namespace FreeGroupFactorMain.Amplification.OperatorSum
variable {E : Type u_22} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain.Amplification.OperatorSum
namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
open OperatorSum
variable {E : Type u_23} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 variable {G : Type u_24} [Group G]

 theorem finite_trace_equal_projection_of_le (p e : stabilization G)
    (_hp : IsStarProjection p) (he : IsStarProjection e) (hep : e*p=e)
    (htrace : stabilizedProjectionTrace p=stabilizedProjectionTrace e)
    (hfinite : stabilizedProjectionTrace p ≠ ⊤) : p=e := by
  have he' : e*(p-e)=0 := by rw [mul_sub,hep,he.isIdempotentElem,sub_self]
  have hs := stabilizedProjectionTrace_orthogonal_add e (p-e) he.isSelfAdjoint he'
  rw [add_sub_cancel,htrace] at hs
  have hzero : stabilizedProjectionTrace (p-e)=0 := by
    have hf : stabilizedProjectionTrace e ≠ ⊤ := htrace ▸ hfinite
    exact (ENNReal.add_right_inj hf).mp (by simpa only [add_zero] using hs.symm)
  exact sub_eq_zero.mp (stabilizedProjectionTrace_faithful (p-e) hzero)

end
open scoped ENNReal
open OperatorSum

 theorem equal_finite_trace_equivalence {G : Type u_25} [Group G]
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G, Commute T S) →
      ∃ c : ℂ, T=c • (1 : groupVonNeumann G))
    (p q : stabilization G) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (htrace : stabilizedProjectionTrace p=stabilizedProjectionTrace q)
    (hfinite : stabilizedProjectionTrace p ≠ ⊤) :
    ∃ V : stabilization G, star V*V=p ∧ V*star V=q := by
  have hfac := stabilization_center_projection hbase
  have hp' : IsStarProjection (p : GroupOperator (ℕ × G)) := hp.map (stabilization G).subtype
  have hq' : IsStarProjection (q : GroupOperator (ℕ × G)) := hq.map (stabilization G).subtype
  obtain ⟨V,hV,hpart,hqV,hVp,hside⟩ := factor_partial_comparison (stabilizedRightTranslations G)
    hfac p q hp' hq' p.property q.property
  let U : stabilization G := ⟨V,hV⟩
  have hpart' : IsPartial (U : GroupOperator (ℕ × G)) := hpart
  have hi : IsStarProjection (star U*U) := by
    constructor
    · apply Subtype.ext
      exact (initial_projection hpart).isIdempotentElem
    · apply Subtype.ext
      exact (initial_projection hpart).isSelfAdjoint
  have hf : IsStarProjection (U*star U) := by
    constructor
    · apply Subtype.ext
      change (V*star V)*(V*star V)=V*star V
      simpa only [star_star] using (initial_projection (partial_star hpart)).isIdempotentElem.eq
    · apply Subtype.ext
      change star (V*star V)=V*star V
      simpa only [star_star] using (initial_projection (partial_star hpart)).isSelfAdjoint.star_eq
  have hitrace := stabilizedProjectionTrace_initial_final U hpart'
  refine ⟨U,?_⟩
  rcases hside with he|he
  · have hu : star U*U=p := Subtype.ext he
    have hle : (U*star U)*q=U*star U := by
      apply Subtype.ext
      have he' := congrArg star hqV
      simp only [star_mul,hq'.isSelfAdjoint.star_eq] at he'
      change (V*star V)*(q : GroupOperator (ℕ × G))=V*star V
      rw [mul_assoc,he']
    rw [hu] at hitrace
    have ht : stabilizedProjectionTrace q=stabilizedProjectionTrace (U*star U) := htrace.symm.trans hitrace
    exact ⟨hu,(finite_trace_equal_projection_of_le q (U*star U) hq hf hle ht (htrace ▸ hfinite)).symm⟩
  · have hu : U*star U=q := Subtype.ext he
    have hle : (star U*U)*p=star U*U := by
      apply Subtype.ext
      change (star V*V)*(p : GroupOperator (ℕ × G))=star V*V
      rw [mul_assoc,hVp]
    rw [hu] at hitrace
    have ht : stabilizedProjectionTrace p=stabilizedProjectionTrace (star U*U) := htrace.trans hitrace.symm
    exact ⟨(finite_trace_equal_projection_of_le p (star U*U) hp hi hle ht hfinite).symm,hu⟩

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
variable {G : Type u_1} [Group G]

noncomputable def stabilizationDelta (G : Type u_2) [Group G] (j : ℕ) : GroupHilbert (ℕ × G) := by
  classical
  exact lp.single 2 (j,1) (1 : ℂ)

 theorem finite_weight_summable (T : stabilization G) (hT : stabilizedProjectionTrace T ≠ ⊤) :
    Summable (fun j => ‖(T : GroupOperator (ℕ × G)) (stabilizationDelta G j)‖^2) := by
  have hs := ENNReal.summable_toReal hT
  simpa only [stabilizedProjectionTrace,stabilizationDelta,ENNReal.toReal_ofReal (sq_nonneg _)] using hs

 theorem finite_weight_left_mul (A B : stabilization G) (hB : stabilizedProjectionTrace B ≠ ⊤) :
    stabilizedProjectionTrace (A*B) ≠ ⊤ := by
  have hs := (finite_weight_summable B hB).mul_left (‖(A : GroupOperator (ℕ × G))‖^2)
  have hle (j : ℕ) : ‖((A*B : stabilization G) : GroupOperator (ℕ × G)) (stabilizationDelta G j)‖^2 ≤
      ‖(A : GroupOperator (ℕ × G))‖^2*‖(B : GroupOperator (ℕ × G)) (stabilizationDelta G j)‖^2 := by
    change ‖(A : GroupOperator (ℕ × G)) ((B : GroupOperator (ℕ × G)) (stabilizationDelta G j))‖^2 ≤ _
    have h := (A : GroupOperator (ℕ × G)).le_opNorm ((B : GroupOperator (ℕ × G)) (stabilizationDelta G j))
    nlinarith [norm_nonneg ((A : GroupOperator (ℕ × G)) ((B : GroupOperator (ℕ × G)) (stabilizationDelta G j))),
      mul_nonneg (norm_nonneg (A : GroupOperator (ℕ × G))) (norm_nonneg ((B : GroupOperator (ℕ × G)) (stabilizationDelta G j)))]
  have hs' := Summable.of_nonneg_of_le (fun j => sq_nonneg _) hle hs
  exact hs'.tsum_ofReal_ne_top

 theorem finite_weight_star (T : stabilization G) (hT : stabilizedProjectionTrace T ≠ ⊤) :
    stabilizedProjectionTrace (star T) ≠ ⊤ := by
  classical
  rwa [stabilizedProjectionTrace_star]

 theorem finite_weight_toReal (T : stabilization G) :
    (stabilizedProjectionTrace T).toReal =
      ∑' j, ‖(T : GroupOperator (ℕ × G)) (stabilizationDelta G j)‖^2 := by
  rw [stabilizedProjectionTrace,ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro j
  exact ENNReal.toReal_ofReal (sq_nonneg _)

 theorem stabilizedTrace_star_mul (T : stabilization G) (hT : stabilizedProjectionTrace T ≠ ⊤) :
    stabilizedTrace (star T*T)=((stabilizedProjectionTrace T).toReal : ℂ) := by
  rw [finite_weight_toReal]
  have hs := finite_weight_summable T hT
  calc
    stabilizedTrace (star T*T) = ∑' j, ((‖(T : GroupOperator (ℕ × G)) (stabilizationDelta G j)‖^2 : ℝ) : ℂ) := by
      apply tsum_congr
      intro j
      change inner ℂ (stabilizationDelta G j)
        (star (T : GroupOperator (ℕ × G)) ((T : GroupOperator (ℕ × G)) (stabilizationDelta G j)))=_
      have he := (ContinuousLinearMap.adjoint_inner_right (T : GroupOperator (ℕ × G))
        (stabilizationDelta G j) ((T : GroupOperator (ℕ × G)) (stabilizationDelta G j))).trans
        (inner_self_eq_norm_sq_to_K ((T : GroupOperator (ℕ × G)) (stabilizationDelta G j)))
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact he.trans (Complex.ofReal_pow _ _).symm
    _ = _ := (Complex.ofRealCLM.map_tsum hs).symm

 theorem stabilizedTrace_star_mul_comm (T : stabilization G) (hT : stabilizedProjectionTrace T ≠ ⊤) :
    stabilizedTrace (star T*T)=stabilizedTrace (T*star T) := by
  classical
  rw [stabilizedTrace_star_mul T hT]
  have he := stabilizedTrace_star_mul (star T) (finite_weight_star T hT)
  rw [star_star,stabilizedProjectionTrace_star] at he
  exact he.symm

 theorem corner_diag_bound (p : stabilization G) (hp : IsStarProjection p) (x : Corner p hp) (j : ℕ) :
    ‖inner ℂ (stabilizationDelta G j)
      (((x : stabilization G) : GroupOperator (ℕ × G)) (stabilizationDelta G j))‖ ≤
      ‖x‖*‖(p : GroupOperator (ℕ × G)) (stabilizationDelta G j)‖^2 := by
  let P := (p : GroupOperator (ℕ × G))
  let X := ((x : stabilization G) : GroupOperator (ℕ × G))
  let ξ := stabilizationDelta G j
  have hself : star P=P := congrArg Subtype.val hp.isSelfAdjoint.star_eq
  have hleft : P*X=X := congrArg Subtype.val x.property.1
  have hright : X*P=X := congrArg Subtype.val x.property.2
  have hi : inner ℂ ξ (X ξ)=inner ℂ (P ξ) (X ξ) := by
    have he := ContinuousLinearMap.adjoint_inner_right P ξ (X ξ)
    rw [← ContinuousLinearMap.star_eq_adjoint,hself] at he
    have hh : P (X ξ)=X ξ := congrArg (fun U : GroupOperator (ℕ × G) => U ξ) hleft
    rw [hh] at he
    exact he
  change ‖inner ℂ ξ (X ξ)‖ ≤ ‖X‖*‖P ξ‖^2
  rw [hi,← congrArg (fun U : GroupOperator (ℕ × G) => U ξ) hright]
  change ‖inner ℂ (P ξ) (X (P ξ))‖ ≤ _
  calc
    _ ≤ ‖P ξ‖*‖X (P ξ)‖ := norm_inner_le_norm _ _
    _ ≤ ‖P ξ‖*(‖X‖*‖P ξ‖) := mul_le_mul_of_nonneg_left (X.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

 theorem corner_diag_summable (p : stabilization G) (hp : IsStarProjection p)
    (hfinite : stabilizedProjectionTrace p ≠ ⊤) (x : Corner p hp) :
    Summable (fun j => inner ℂ (stabilizationDelta G j)
      (((x : stabilization G) : GroupOperator (ℕ × G)) (stabilizationDelta G j))) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (corner_diag_bound p hp x)
    ((finite_weight_summable p hfinite).mul_left ‖x‖)

 def finiteCornerTraceLinear (p : stabilization G) (hp : IsStarProjection p)
    (hfinite : stabilizedProjectionTrace p ≠ ⊤) : Corner p hp →ₗ[ℂ] ℂ where
  toFun x := stabilizedTrace (x : stabilization G)
  map_add' x y := by
    change (∑' j, inner ℂ (stabilizationDelta G j)
      ((((x+y : Corner p hp) : stabilization G) : GroupOperator (ℕ × G)) (stabilizationDelta G j)))=_
    have he (j : ℕ) : inner ℂ (stabilizationDelta G j)
      ((((x+y : Corner p hp) : stabilization G) : GroupOperator (ℕ × G)) (stabilizationDelta G j))=
      inner ℂ (stabilizationDelta G j) (((x : stabilization G) : GroupOperator (ℕ × G)) (stabilizationDelta G j))+
      inner ℂ (stabilizationDelta G j) (((y : stabilization G) : GroupOperator (ℕ × G)) (stabilizationDelta G j)) :=
        inner_add_right _ _ _
    simp_rw [he]
    exact (corner_diag_summable p hp hfinite x).tsum_add (corner_diag_summable p hp hfinite y)
  map_smul' c x := by
    change (∑' j, inner ℂ (stabilizationDelta G j)
      ((((c • x : Corner p hp) : stabilization G) : GroupOperator (ℕ × G)) (stabilizationDelta G j)))=_
    have he (j : ℕ) : inner ℂ (stabilizationDelta G j)
      ((((c • x : Corner p hp) : stabilization G) : GroupOperator (ℕ × G)) (stabilizationDelta G j))=
      c • inner ℂ (stabilizationDelta G j) (((x : stabilization G) : GroupOperator (ℕ × G)) (stabilizationDelta G j)) :=
        inner_smul_right _ _ _
    simp_rw [he]
    exact (corner_diag_summable p hp hfinite x).tsum_mul_left c

 theorem finite_weight_corner (p : stabilization G) (hp : IsStarProjection p)
    (hfinite : stabilizedProjectionTrace p ≠ ⊤) (x : Corner p hp) :
    stabilizedProjectionTrace (x : stabilization G) ≠ ⊤ := by
  have he := finite_weight_left_mul (x : stabilization G) p hfinite
  rwa [x.property.2] at he

end

variable {A : Type u_3} [CStarAlgebra A]

 theorem quadratic_polarization (x : A) :
    (4 : ℂ) • x = star (x+1)*(x+1)-star (x-1)*(x-1)+
      Complex.I • (star (x+Complex.I • 1)*(x+Complex.I • 1)-
        star (x-Complex.I • 1)*(x-Complex.I • 1)) := by
  simp only [star_add,star_sub,star_smul,star_one,Complex.star_def,Complex.conj_I,
    add_mul,mul_add,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_smul,mul_one,one_mul,
    smul_add,smul_sub,smul_neg,neg_mul,Complex.I_mul_I,neg_neg,one_smul,neg_smul]
  module

 theorem linearMap_ext_star_mul (φ ψ : A →ₗ[ℂ] ℂ)
    (h : ∀ x, φ (star x*x)=ψ (star x*x)) : φ=ψ := by
  apply LinearMap.ext
  intro x
  have he := quadratic_polarization x
  have hφ := congrArg φ he
  have hψ := congrArg ψ he
  simp only [map_smul,map_add,map_sub,h] at hφ hψ
  have hh : (4 : ℂ)*φ x=4*ψ x := hφ.trans hψ.symm
  exact (mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0)) hh

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain

def operatorSequenceMap {G : Type u_4} {H : Type u_5} (A : GroupHilbert G →L[ℂ] GroupHilbert H)
    (ξ : lp (fun _ : ℕ => GroupHilbert G) 2) : lp (fun _ : ℕ => GroupHilbert H) 2 :=
  ⟨fun n => A (ξ n), ((lp.memℓp ξ).norm.const_smul ‖A‖).mono (fun n => A.le_opNorm (ξ n))⟩

 theorem ultraweak_mul_conjugate {G : Type u_6} (u : GroupOperator G) :
    @Continuous _ _ (ultraweakOperatorTopology G) (ultraweakOperatorTopology G)
      (fun T : GroupOperator G => u*T*star u) := by
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have heq :
      (fun T : GroupOperator G => ∑' k : ℕ, inner ℂ (η k) ((u*T*star u) (ξ k))) =
      (fun T : GroupOperator G => ∑' k : ℕ,
        inner ℂ (operatorSequenceMap (star u) η k) (T (operatorSequenceMap (star u) ξ k))) := by
    funext T
    apply tsum_congr
    intro k
    change inner ℂ (η k) (u (T ((star u) (ξ k)))) =
      inner ℂ ((star u) (η k)) (T ((star u) (ξ k)))
    exact (ContinuousLinearMap.adjoint_inner_left u _ _).symm
  change @Continuous _ _ (ultraweakOperatorTopology G) _
    (fun T : GroupOperator G => ∑' k : ℕ, inner ℂ (η k) ((u*T*star u) (ξ k)))
  rw [heq]
  exact continuous_iInf_dom (i := operatorSequenceMap (star u) ξ)
    (continuous_iInf_dom (i := operatorSequenceMap (star u) η) continuous_induced_dom)

end FreeGroupFactorMain

namespace FreeGroupFactorMain.Amplification
open scoped ENNReal
variable {G : Type u_8} [Group G]

 theorem equivalentCorner_finite_trace (p q : stabilization G)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpfinite : stabilizedProjectionTrace p ≠ ⊤) (hqfinite : stabilizedProjectionTrace q ≠ ⊤)
    (u : stabilization G) (hu : star u*u=p) (hu' : u*star u=q)
    (x : Corner p hp) :
    stabilizedTrace (equivalentCorner p q hp hq u hu hu' x : stabilization G)=
      stabilizedTrace (x : stabilization G) := by
  let Φ := equivalentCorner p q hp hq u hu hu'
  let φ := (finiteCornerTraceLinear q hq hqfinite).comp Φ.toAlgEquiv.toLinearMap
  let ψ := finiteCornerTraceLinear p hp hpfinite
  have he : φ=ψ := by
    apply linearMap_ext_star_mul
    intro z
    let Z := (z : stabilization G)
    have hZ := finite_weight_corner p hp hpfinite z
    have hZs := finite_weight_star Z hZ
    have hUZ := finite_weight_left_mul u (star Z) hZs
    have hr : Z*p=Z := z.property.2
    have halg : star (u*star Z)*(u*star Z)=Z*star Z := by
      simp only [star_mul,star_star]
      calc
        (Z*star u)*(u*star Z)=(Z*(star u*u))*star Z := by noncomm_ring
        _ = Z*star Z := by rw [hu,hr]
    change stabilizedTrace (u*(star Z*Z)*star u)=stabilizedTrace (star Z*Z)
    calc
      _ = stabilizedTrace ((u*star Z)*star (u*star Z)) := by
        simp only [star_mul,star_star,mul_assoc]
      _ = stabilizedTrace (star (u*star Z)*(u*star Z)) := (stabilizedTrace_star_mul_comm _ hUZ).symm
      _ = stabilizedTrace (Z*star Z) := congrArg stabilizedTrace halg
      _ = _ := (stabilizedTrace_star_mul_comm Z hZ).symm
  exact congrArg (fun f : Corner p hp →ₗ[ℂ] ℂ => f x) he

 theorem equivalentCorner_normalized_finite_trace (p q : stabilization G)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpfinite : stabilizedProjectionTrace p ≠ ⊤) (hqfinite : stabilizedProjectionTrace q ≠ ⊤)
    (u : stabilization G) (hu : star u*u=p) (hu' : u*star u=q)
    (t : ℝ) (x : Corner p hp) :
    normalizedCornerTrace stabilizedTrace t q hq (equivalentCorner p q hp hq u hu hu' x)=
      normalizedCornerTrace stabilizedTrace t p hp x := by
  unfold normalizedCornerTrace
  rw [equivalentCorner_finite_trace p q hp hq hpfinite hqfinite u hu hu']

 theorem stabilizationUltraweak_mul_conjugate (u : stabilization G) :
    @Continuous _ _ (stabilizationTopology G) (stabilizationTopology G)
      (fun T : stabilization G => u*T*star u) := by
  let : TopologicalSpace (GroupOperator (ℕ × G)) := ultraweakOperatorTopology (ℕ × G)
  let : TopologicalSpace (stabilization G) := stabilizationTopology G
  apply continuous_induced_rng.mpr
  exact (ultraweak_mul_conjugate (u : GroupOperator (ℕ × G))).comp continuous_induced_dom

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
variable {G : Type u_1}

@[simp] theorem productCoordinate_productSingle (i j : ℕ) (ξ : GroupHilbert G) :
    productCoordinate ℕ G i (productSingle ℕ G j ξ)=if i=j then ξ else 0 := by
  ext g
  simp only [productCoordinate_apply,productSingle_apply]
  split_ifs <;> rfl

@[simp] theorem matrixEntry_sum {ι : Type u_2} (s : Finset ι) (X : ι → GroupOperator (ℕ × G)) (i j : ℕ) :
    matrixEntry (∑ k∈s,X k) i j=∑ k∈s,matrixEntry (X k) i j := by
  classical
  induction s using Finset.induction_on with
  | empty => ext ξ g; simp [matrixEntry_apply]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [show matrixEntry (X a + ∑ k∈s,X k) i j=matrixEntry (X a) i j+matrixEntry (∑ k∈s,X k) i j by ext ξ g; simp [matrixEntry_apply],ih]

variable [Group G]

end

open scoped ENNReal
variable {G : Type u_4} [Group G]

variable {H : Type u_5} [Group H]

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
variable {G : Type u_1} [Group G]

section Singles
variable [DecidableEq G]

end Singles

end

section
variable {G : Type u_2} [Group G]

end

variable {G : Type u_3} {H : Type u_4} [Group G] [Group H]

theorem finite_corner_choice_both
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G, Commute T S) →
      ∃ c : ℂ, T=c • (1 : groupVonNeumann G))
    (t : ℝ) (p q : stabilization G) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (htrace : stabilizedProjectionTrace p=stabilizedProjectionTrace q)
    (hfinite : stabilizedProjectionTrace p ≠ ⊤) :
    ∃ Φ : Corner p hp ≃⋆ₐ[ℂ] Corner q hq,
      (∀ x, normalizedCornerTrace stabilizedTrace t q hq (Φ x)=
        normalizedCornerTrace stabilizedTrace t p hp x) ∧
      @Continuous _ _ (cornerTopology (stabilizationTopology G) p hp)
        (cornerTopology (stabilizationTopology G) q hq) Φ ∧
      @Continuous _ _ (cornerTopology (stabilizationTopology G) q hq)
        (cornerTopology (stabilizationTopology G) p hp) Φ.symm := by
  have hv : ∃ u : stabilization G, star u*u=p ∧ u*star u=q :=
    equal_finite_trace_equivalence (G := G) hbase p q hp hq htrace hfinite
  rcases hv with ⟨u,hu,hu'⟩
  refine ⟨equivalentCorner p q hp hq u hu hu',?_,?_,?_⟩
  · exact equivalentCorner_normalized_finite_trace p q hp hq hfinite (htrace ▸ hfinite) u hu hu' t
  · exact equivalentCorner_normal p q hp hq u hu hu' (stabilizationTopology G)
      (stabilizationUltraweak_mul_conjugate u)
  · have h1 : star (star u)*star u=q := by rwa [star_star]
    have h2 : star u*star (star u)=p := by rwa [star_star]
    have he : (equivalentCorner p q hp hq u hu hu').symm=equivalentCorner q p hq hp (star u) h1 h2 := by
      apply StarAlgEquiv.ext
      intro x
      apply Subtype.ext
      change star u*(x : stabilization G)*u=star u*(x : stabilization G)*star (star u)
      rw [star_star]
    rw [he]
    exact equivalentCorner_normal q p hq hp (star u) h1 h2 (stabilizationTopology G)
      (stabilizationUltraweak_mul_conjugate (star u))
end FreeGroupFactorMain.Amplification

end

end OAI
end


