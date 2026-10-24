-- Prove2me | Definitions.Def_OAIQWST002
-- name    : OAIQWST002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T19:34:37.112004+00:00
-- url     : https://prove2.me/theorems/9d6cbf90-1682-4af1-bebc-2954b811bcc3
-- title:
--   OpenAI split tangent bundles split: definitions bundle OAIQWST002
-- statement:
--   One of the three definitions bundles (`OAIQWST000`, `OAIQWST001`, `OAIQWST002`) of the split of OpenAI's proof that both summands of a holomorphic splitting of the tangent bundle of a rationally connected projective manifold are integrable (`OAI.SplitTangent.integrability_main`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Geometry/SplitTangent` (OpenAI, *Integrability of split tangent bundles on rationally connected manifolds*, OpenAI Math Release, September 23, 2026, result family 052, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. The bundles split the material only to keep each one within the platform's compile limits.
--
--   The definitions of the published statement (`ComplexManifold`, `ProjectiveEmbedding`, `RationalCurve`, `RationallyConnected`, `TangentSplitting`, `Integrable` and the rest) are not repeated: every bundle imports them from the published bundle `Def_SplitTangentIntegrability`. It also imports the bundles `OAIQWST000`, `OAIQWST001` of this split..
--
--   Modules (some only in part): `BoxFirstTransport`, `BoxTransportBase`, `BracketIntegrability`, `FamilyPropagationStep`, `FormalBoxes`, `RationalEncoding`, `RationalFamilies`, `RationalReparam`, `RationalTrivialization`.
--
--   The theorems the definitions do not need are proved in the four solutions of this split: three prove the published intermediate statements `OAI.SplitTangent.TangentSplitting.exists_projective_tangent_box`, `OAI.SplitTangent.RationalFamily.integrable_both_of_submersive` and `OAI.SplitTangent.RationallyConnected.exists_submersive_familyAlternative`, and the fourth proves `OAI.SplitTangent.integrability_main` from them. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Integrability of split tangent bundles on rationally connected manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integrability-of-split-tangent-bundles-on-rationally-connected-manifolds-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/SplitTangent at commit adc7f12

import Mathlib
import Definitions.Def_SplitTangentIntegrability
import Definitions.Def_OAIQWST000
import Definitions.Def_OAIQWST001

section
-- module Solutions.OAIQW_SplitTangent.BracketIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bracket Integrability. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

universe u
namespace SplitTangent
section

attribute [instance] ComplexManifold.topology ComplexManifold.charts
  ComplexManifold.holomorphicAtlas ComplexManifold.hausdorff
  ComplexManifold.secondCountable

open Filter Topology
end

section

 

structure RationalFamily (X T : ComplexManifold.{u}) where
  finite : ℂ × T.Carrier → X.Carrier
  infinity : ℂ × T.Carrier → X.Carrier
  finite_holomorphic : ContMDiff (𝓘(ℂ, ℂ).prod (ModelWithCorners T))
    (ModelWithCorners X) ω finite
  infinity_holomorphic : ContMDiff (𝓘(ℂ, ℂ).prod (ModelWithCorners T))
    (ModelWithCorners X) ω infinity
  overlap : ∀ z : ℂ, z ≠ 0 → ∀ τ, finite (z,τ) = infinity (z⁻¹,τ)



namespace RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)

def curve (τ : T.Carrier) : RationalCurve X where
  finite z := G.finite (z,τ)
  infinity z := G.infinity (z,τ)
  finite_holomorphic := G.finite_holomorphic.comp (contMDiff_id.prodMk contMDiff_const)
  infinity_holomorphic := G.infinity_holomorphic.comp (contMDiff_id.prodMk contMDiff_const)
  overlap z hz := G.overlap z hz τ

 

def parameterDerivative (H : ℂ × T.Carrier → X.Carrier)
    (τ : T.Carrier) (v : Tangent T τ) (z : ℂ) : Tangent X (H (z,τ)) :=
  mfderiv (ModelWithCorners T) (ModelWithCorners X) (fun t => H (z,t)) τ v

lemma parameterDerivative_eq {H : ℂ × T.Carrier → X.Carrier}
    (hH : ContMDiff (𝓘(ℂ, ℂ).prod (ModelWithCorners T)) (ModelWithCorners X) ω H)
    (τ : T.Carrier) (v : Tangent T τ) (z : ℂ) :
    parameterDerivative H τ v z =
      mfderiv (𝓘(ℂ, ℂ).prod (ModelWithCorners T)) (ModelWithCorners X) H (z,τ) (0,v) := by
  have he := mfderiv_comp τ (hH.mdifferentiable (by simp) (z,τ))
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id :
      MDifferentiableAt (ModelWithCorners T) (𝓘(ℂ, ℂ).prod (ModelWithCorners T))
        (fun t : T.Carrier => (z,t)) τ)
  unfold parameterDerivative
  rw [show (fun t => H (z,t)) = H ∘ (fun t => (z,t)) from rfl, he, mfderiv_prod_right]
  rfl

lemma parameterDerivative_holomorphic {H : ℂ × T.Carrier → X.Carrier}
    (hH : ContMDiff (𝓘(ℂ, ℂ).prod (ModelWithCorners T)) (ModelWithCorners X) ω H)
    (τ : T.Carrier) (v : Tangent T τ) :
    ContMDiff 𝓘(ℂ, ℂ) ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
      (fun z => (⟨H (z,τ), parameterDerivative H τ v z⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) := by
  have hz : ContMDiff 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)) ω
      (fun z : ℂ => (⟨z,0⟩ : TangentBundle 𝓘(ℂ, ℂ) ℂ)) :=
    Bundle.contMDiff_zeroSection ℂ (TangentSpace 𝓘(ℂ, ℂ))
  have hc : ContMDiff 𝓘(ℂ, ℂ)
      ((ModelWithCorners T).prod 𝓘(ℂ, Model T)) ω
      (fun _ : ℂ => (⟨τ,v⟩ : TangentBundle (ModelWithCorners T) T.Carrier)) := contMDiff_const
  have hp := hz.prodMk hc
  have hq := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℂ, ℂ)) (I' := ModelWithCorners T)).comp hp
  have hr := (hH.contMDiff_tangentMap (m := ω) (by simp)).comp hq
  convert hr using 1
  funext z
  simp only [Function.comp_apply, tangentMap]
  change (⟨H (z,τ), parameterDerivative H τ v z⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier) =
    ⟨H (z,τ), mfderiv (𝓘(ℂ, ℂ).prod (ModelWithCorners T))
      (ModelWithCorners X) H (z,τ) (0,v)⟩
  rw [parameterDerivative_eq hH]

 

def derivativeSection (τ : T.Carrier) (v : Tangent T τ) : CurveTangentSection (G.curve τ) where
  finite := parameterDerivative G.finite τ v
  infinity := parameterDerivative G.infinity τ v
  finite_holomorphic := parameterDerivative_holomorphic G.finite_holomorphic τ v
  infinity_holomorphic := parameterDerivative_holomorphic G.infinity_holomorphic τ v
  overlap z hz := by
    unfold parameterDerivative
    rw [show (fun t => G.finite (z,t)) = (fun t => G.infinity (z⁻¹,t)) from funext (G.overlap z hz)]
    rfl

 
def twoPointEvaluation (a b : ℂ) (τ : T.Carrier) : X.Carrier × X.Carrier :=
  (G.finite (a,τ), G.finite (b,τ))

end RationalFamily

open Filter


end




end SplitTangent

open scoped Topology
open Filter

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalTrivialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Trivialization. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

universe u

open scoped Topology
open Filter

namespace SplitTangent.TangentSplitting
section
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)


theorem coordinateProjector_idempotent (x : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target) (v : Model X) :
    S.coordinateProjector x z (S.coordinateProjector x z v) = S.coordinateProjector x z v := by
  let t := trivializationAt (Model X) (Tangent X) x
  have hy : (chartAt (Model X) x).symm z ∈ t.baseSet :=
    (chartAt (Model X) x).map_target hz
  simp only [coordinateProjector,ContinuousLinearMap.comp_apply]
  rw [t.symmL_continuousLinearMapAt hy, S.idempotent]

end

variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

def coordinateTransition (x y : X.Carrier) : Model X → Model X :=
  (chartAt (Model X) y) ∘ (chartAt (Model X) x).symm

theorem coordinateTransition_analytic (x y : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target)
    (hzy : (chartAt (Model X) x).symm z ∈ (chartAt (Model X) y).source) :
    AnalyticAt ℂ (coordinateTransition x y) z := by
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) y) hzy
  have hd := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hz
  exact (hc.comp z hd).contDiffAt.analyticAt

theorem coordinateTransition_derivative (x y : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target)
    (hzy : (chartAt (Model X) x).symm z ∈ (chartAt (Model X) y).source) :
    fderiv ℂ (coordinateTransition x y) z =
      ((trivializationAt (Model X) (Tangent X) y).continuousLinearMapAt ℂ
        ((chartAt (Model X) x).symm z)).comp
      ((trivializationAt (Model X) (Tangent X) x).symmL ℂ
        ((chartAt (Model X) x).symm z)) := by
  let c := chartAt (Model X) x
  let d := chartAt (Model X) y
  have hc := (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) y) hzy).mdifferentiableAt (by simp)
  have hd := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hz).mdifferentiableAt (by simp)
  have hA : (trivializationAt (Model X) (Tangent X) y).continuousLinearMapAt ℂ (c.symm z) =
      mfderiv (ModelWithCorners X) 𝓘(ℂ,Model X) d (c.symm z) := by
    exact TangentBundle.continuousLinearMapAt_trivializationAt (I := ModelWithCorners X) hzy
  have hB : (trivializationAt (Model X) (Tangent X) x).symmL ℂ (c.symm z) =
      mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm z := by
    have he := TangentBundle.symmL_trivializationAt (I := ModelWithCorners X) (c.map_target hz)
    have he' : (trivializationAt (Model X) (Tangent X) x).symmL ℂ (c.symm z) =
        mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (c (c.symm z)) := by
      simpa [extChartAt_coe_symm,extChartAt_coe,ModelWithCorners,c] using he
    rw [c.right_inv hz] at he'
    exact he' 
  change fderiv ℂ (d ∘ c.symm) z = _
  rw [hA,hB]
  exact mfderiv_eq_fderiv.symm.trans (mfderiv_comp z hc hd)

 
theorem coordinateProjector_intertwining (x y : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target)
    (hzy : (chartAt (Model X) x).symm z ∈ (chartAt (Model X) y).source) :
    (fderiv ℂ (coordinateTransition x y) z).comp (S.coordinateProjector x z) =
      (S.coordinateProjector y (coordinateTransition x y z)).comp
        (fderiv ℂ (coordinateTransition x y) z) := by
  rw [coordinateTransition_derivative x y hz hzy]
  let t := trivializationAt (Model X) (Tangent X) x
  let t' := trivializationAt (Model X) (Tangent X) y
  have hx : (chartAt (Model X) x).symm z ∈ t.baseSet := (chartAt (Model X) x).map_target hz
  have hy : (chartAt (Model X) x).symm z ∈ t'.baseSet := hzy
  have he : (chartAt (Model X) y).symm (coordinateTransition x y z) =
      (chartAt (Model X) x).symm z := (chartAt (Model X) y).left_inv hzy
  simp only [coordinateProjector]
  rw [he]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  rw [t.symmL_continuousLinearMapAt hx,t'.symmL_continuousLinearMapAt hy]

end SplitTangent.TangentSplitting

end

noncomputable section
universe u
open Filter Topology Set Bundle
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace SplitTangent.PullbackConnection
section
open HolomorphicLinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]



def equation (P : E → E →L[ℂ] E) (g : ℂ → E) : ℂ → E →L[ℂ] E :=
  projectorODE (P ∘ g) (coefficient P g)

lemma equation_analyticAt {P : E → E →L[ℂ] E} {g : ℂ → E} {z : ℂ}
    (hP : AnalyticAt ℂ P (g z)) (hg : AnalyticAt ℂ g z) :
    AnalyticAt ℂ (equation P g) z :=
  projectorODE_analyticAt (hP.comp hg) (coefficient_analyticAt hP hg)

omit [CompleteSpace E] in
lemma projectorODE_horizontal {P B : ℂ → E →L[ℂ] E} {z : ℂ} {v : E}
    (hP : DifferentiableAt ℂ P z) (hid : ∀ᶠ w in 𝓝 z, P w * P w = P w)
    (hv : P z v = v) :
    P z (projectorODE P B z v) + P z (B z v) = 0 := by
  have hi := hid.self_of_nhds
  have hz := projector_derivative_sandwich hi (idempotent_derivative hP.hasDerivAt hid)
  have hvz := congrArg (fun A : E →L[ℂ] E => A v) hz
  simp only [mul_apply_eq_comp,hv,zero_apply] at hvz
  have hi' : ∀ w, P z (P z w) = P z w := fun w =>
    congrArg (fun A : E →L[ℂ] E => A w) hi
  simp only [projectorODE,sub_apply,mul_apply_eq_comp,map_sub,hv,hi',hvz,map_zero]
  abel

omit [CompleteSpace E] in
lemma horizontal_of_equation {P : E → E →L[ℂ] E} {g v : ℂ → E} {z : ℂ}
    (hP : DifferentiableAt ℂ (P ∘ g) z)
    (hid : ∀ᶠ w in 𝓝 z, P (g w) * P (g w) = P (g w))
    (him : P (g z) (v z) = v z)
    (hv : HasDerivAt v (equation P g z (v z)) z) :
    covariantDerivative P g v z = 0 := by
  unfold covariantDerivative
  rw [hv.deriv]
  exact projectorODE_horizontal hP hid him

 

theorem exists_local_horizontal_transport {P : E → E →L[ℂ] E} {g : ℂ → E} {x : ℂ}
    (hP : AnalyticAt ℂ P (g x)) (hg : AnalyticAt ℂ g x)
    (hid : ∀ᶠ y in 𝓝 (g x), P y * P y = P y) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : ℂ → ℂ → E →L[ℂ] E,
      AnalyticOnNhd ℂ (fun w : ℂ × ℂ => T w.1 w.2)
        (Metric.ball x ε ×ˢ Metric.ball x ε) ∧
      (∀ s ∈ Metric.ball x ε, T s s=1) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε, IsUnit (T s t)) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε, ∀ u ∈ Metric.ball x ε,
        T t u*T s t=T s u) ∧
      (∀ s ∈ Metric.ball x ε, ∀ t ∈ Metric.ball x ε, ∀ v : E,
        P (g s) v = v →
        P (g t) (T s t v) = T s t v ∧
        covariantDerivative P g (fun w => T s w v) t = 0) := by
  have hpg := hP.comp hg
  have hip : ∀ᶠ z in 𝓝 x, (P ∘ g) z * (P ∘ g) z = (P ∘ g) z :=
    hg.continuousAt hid
  obtain ⟨r,hr,T,hTa,hT0,hTu,hTc,hTd,hTi⟩ :=
    exists_local_projector_transport hpg (coefficient_analyticAt hP hg) hip
  obtain ⟨q,hq,hqn⟩ := Metric.eventually_nhds_iff_ball.mp
    (hpg.eventually_analyticAt.and (eventually_eventually_nhds.mpr hip))
  have hmr : Metric.ball x (min r q) ⊆ Metric.ball x r := Metric.ball_subset_ball (min_le_left _ _)
  have hmq : Metric.ball x (min r q) ⊆ Metric.ball x q := Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨min r q,lt_min hr hq,T,?_,?_,?_,?_,?_⟩
  · exact hTa.mono (Set.prod_mono hmr hmr)
  · exact fun s hs => hT0 s (hmr hs)
  · exact fun s hs t ht => hTu s (hmr hs) t (hmr ht)
  · exact fun s hs t ht u hu => hTc s (hmr hs) t (hmr ht) u (hmr hu)
  · intro s hs t ht v hv
    have him : P (g t) (T s t v) = T s t v := by
      have hh := congrArg (fun A : E →L[ℂ] E => A v) (hTi s (hmr hs) t (hmr ht))
      simpa only [mul_apply_eq_comp,Function.comp_apply,hv] using hh
    refine ⟨him,horizontal_of_equation (hqn t (hmq ht)).1.differentiableAt
      (hqn t (hmq ht)).2 him ?_⟩
    have hd := (hTd s (hmr hs) t (hmr ht)).clm_apply (hasDerivAt_const t v)
    simpa only [equation,add_zero,map_zero,mul_apply_eq_comp] using hd


omit [CompleteSpace E] in
lemma familyEquation_eq {P : E → E →L[ℂ] E} {F : ℂ × ℂ → E} {s t : ℂ}
    (hP : DifferentiableAt ℂ P (F (s,t))) (hF : DifferentiableAt ℂ F (s,t)) :
    ParameterProjector.equation (P ∘ F) (familyCoefficient P F) (s,t) =
      equation P (fun v => F (s,v)) t := by
  rw [ParameterProjector.equation_eq (hP.comp (s,t) hF)]
  simp only [equation,projectorODE,familyCoefficient_eq hF,Function.comp_def]

 

theorem exists_horizontal_parameter_transport {P : E → E →L[ℂ] E} {F : ℂ × ℂ → E}
    (hP : AnalyticAt ℂ P (F (0,0))) (hF : AnalyticAt ℂ F (0,0))
    (hid : ∀ᶠ y in 𝓝 (F (0,0)), P y*P y=P y) :
    ∃ (T : ℂ → ℂ → ℂ → E →L[ℂ] E) (ε : ℝ), 0 < ε ∧
      (∀ s u, ‖s‖ < ε → ‖u‖ < ε → T s u u=1) ∧
      (∀ s u v, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε → IsUnit (T s u v)) ∧
      (∀ s u v w, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε → ‖w‖ < ε →
        T s v w*T s u v=T s u w) ∧
      (∀ s u v, ‖s‖ < ε → ‖u‖ < ε → ‖v‖ < ε → ∀ e : E,
        P (F (s,u)) e=e → P (F (s,v)) (T s u v e)=T s u v e ∧
          covariantDerivative P (fun t => F (s,t)) (fun t => T s u t e) v=0) ∧
      (∀ (q u v : ℂ → ℂ) z, AnalyticAt ℂ q z → AnalyticAt ℂ u z → AnalyticAt ℂ v z →
        ‖q z‖ < ε → ‖u z‖ < ε → ‖v z‖ < ε →
        AnalyticAt ℂ (fun w => T (q w) (u w) (v w)) z) := by
  have hidF : ∀ᶠ w in 𝓝 (0,0), (P ∘ F) w*(P ∘ F) w=(P ∘ F) w := hF.continuousAt hid
  obtain ⟨T,r,hr,hT0,hTu,hTc,hTd,hTa⟩ := ParameterProjector.exists_preserving_parameter_transport
    (hP.comp hF) (familyCoefficient_analyticAt hP hF) hidF
  have hhP : ∀ᶠ w in 𝓝 (0,0), AnalyticAt ℂ P (F w) := hF.continuousAt hP.eventually_analyticAt
  obtain ⟨η,hη,hηd⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hhP.and hF.eventually_analyticAt).and hidF)
  let ε := min r η
  have hε : 0 < ε := lt_min hr hη
  have hεr : ε ≤ r := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  have hpol (s t : ℂ) (hs : ‖s‖ < ε) (ht : ‖t‖ < ε) :
      AnalyticAt ℂ P (F (s,t)) ∧ AnalyticAt ℂ F (s,t) ∧ P (F (s,t))*P (F (s,t))=P (F (s,t)) := by
    have hm : (s,t) ∈ Metric.ball (0,0) η := by
      simp only [Metric.mem_ball,dist_eq_norm,Prod.mk_sub_mk,sub_zero,Prod.norm_def]
      exact max_lt (hs.trans_le hεη) (ht.trans_le hεη)
    exact ⟨(hηd (s,t) hm).1.1,(hηd (s,t) hm).1.2,(hηd (s,t) hm).2⟩
  refine ⟨T,ε,hε,?_,?_,?_,?_,?_⟩
  · exact fun s u hs hu => hT0 s u (hs.trans_le hεr) (hu.trans_le hεr)
  · exact fun s u v hs hu hv => hTu s u v (hs.trans_le hεr) (hu.trans_le hεr) (hv.trans_le hεr)
  · exact fun s u v w hs hu hv hw => hTc s u v w (hs.trans_le hεr) (hu.trans_le hεr) (hv.trans_le hεr) (hw.trans_le hεr)
  · intro s u v hs hu hv e he
    have hpoint := hpol s v hs hv
    have hdata := hTd s u v (hs.trans_le hεr) (hu.trans_le hεr) (hv.trans_le hεr)
    have him : P (F (s,v)) (T s u v e)=T s u v e := by
      have hh := congrArg (fun A : E →L[ℂ] E => A e) hdata.2
      simpa only [mul_apply_eq_comp,Function.comp_apply,he] using hh
    have hg : AnalyticAt ℂ (fun t => F (s,t)) v := hpoint.2.1.comp (analyticAt_const.prod analyticAt_id)
    have hi : ∀ᶠ t in 𝓝 v, P (F (s,t))*P (F (s,t))=P (F (s,t)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hv)] with t ht
      exact (hpol s t hs (mem_ball_zero_iff.mp ht)).2.2
    refine ⟨him,horizontal_of_equation (P := P) (g := fun t => F (s,t))
      (v := fun t => T s u t e) (hpoint.1.comp (f := fun t => F (s,t)) hg).differentiableAt hi him ?_⟩
    rw [familyEquation_eq hpoint.1.differentiableAt hpoint.2.1.differentiableAt] at hdata
    have hd := hdata.1.clm_apply (hasDerivAt_const v e)
    simpa only [add_zero,map_zero,mul_apply_eq_comp] using hd
  · exact fun q u v z hq hu hv hqs hus hvs => hTa q u v z hq hu hv
      (hqs.trans_le hεr) (hus.trans_le hεr) (hvs.trans_le hεr)

end

open HolomorphicLinearODE

end SplitTangent.PullbackConnection

namespace SplitTangent.PullbackConnection
section
open HolomorphicLinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 

omit [CompleteSpace E] in
lemma hasDerivAt_equation_of_horizontal {P : E → E →L[ℂ] E} {g v : ℂ → E} {z : ℂ}
    (hP : DifferentiableAt ℂ (P ∘ g) z) (hv : DifferentiableAt ℂ v z)
    (hid : ∀ᶠ w in 𝓝 z, P (g w) * P (g w) = P (g w))
    (him : ∀ᶠ w in 𝓝 z, P (g w) (v w) = v w)
    (hh : covariantDerivative P g v z = 0) :
    HasDerivAt v (equation P g z (v z)) z := by
  have hfix := ((hP.hasDerivAt.clm_apply hv.hasDerivAt).congr_of_eventuallyEq (him.mono fun _ h => h.symm)).unique
    hv.hasDerivAt
  have hp := hid.self_of_nhds
  have hi := him.self_of_nhds
  have hz := congrArg (fun A : E →L[ℂ] E => A (v z))
    (projector_derivative_sandwich hp (idempotent_derivative hP.hasDerivAt hid))
  simp only [mul_apply_eq_comp,hi,zero_apply] at hz
  have hvd : deriv v z = deriv (P ∘ g) z (v z) -
      P (g z) (coefficient P g z (v z)) := by
    unfold covariantDerivative at hh
    change deriv (P ∘ g) z (v z) + P (g z) (deriv v z) = deriv v z at hfix
    rw [eq_neg_of_add_eq_zero_left hh] at hfix
    simpa only [sub_eq_add_neg,add_comm] using hfix.symm
  convert! hv.hasDerivAt using 1
  rw [hvd]
  simp only [equation,projectorODE,sub_apply,mul_apply_eq_comp,
    Function.comp_apply,hi,hz,sub_zero]

lemma horizontal_local_uniqueness {P : E → E →L[ℂ] E} {g f h : ℂ → E} {x : ℂ}
    (hP : AnalyticAt ℂ P (g x)) (hg : AnalyticAt ℂ g x)
    (hid : ∀ᶠ y in 𝓝 (g x), P y * P y=P y)
    (hf : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ f z ∧ covariantDerivative P g f z=0)
    (hh : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ h z ∧ covariantDerivative P g h z=0)
    (hfi : ∀ᶠ z in 𝓝 x, P (g z) (f z)=f z)
    (hhi : ∀ᶠ z in 𝓝 x, P (g z) (h z)=h z)
    (he : f x=h x) : f =ᶠ[𝓝 x] h := by
  have hpg := hP.comp hg
  have hi := hg.continuousAt hid
  apply vector_local_uniqueness (equation_analyticAt hP hg) _ _ he
  · filter_upwards [hpg.eventually_analyticAt,eventually_eventually_nhds.mpr hi,
      eventually_eventually_nhds.mpr hfi,hf] with z hz hzi hzfi hzf
    exact hasDerivAt_equation_of_horizontal hz.differentiableAt hzf.1 hzi hzfi hzf.2
  · filter_upwards [hpg.eventually_analyticAt,eventually_eventually_nhds.mpr hi,
      eventually_eventually_nhds.mpr hhi,hh] with z hz hzi hzhi hzh
    exact hasDerivAt_equation_of_horizontal hz.differentiableAt hzh.1 hzi hzhi hzh.2

end

open HolomorphicLinearODE
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

 

theorem horizontal_chart_compatibility
    {P : E → E →L[ℂ] E} {Q : F → F →L[ℂ] F} {φ : E → F}
    {g f : ℂ → E} {h : ℂ → F} {z : ℂ}
    (hP : AnalyticAt ℂ P (g z)) (hQ : AnalyticAt ℂ Q (φ (g z)))
    (hφ : AnalyticAt ℂ φ (g z)) (hg : AnalyticAt ℂ g z)
    (hf : AnalyticAt ℂ f z) (hh : AnalyticAt ℂ h z)
    (hidQ : ∀ᶠ y in 𝓝 (φ (g z)), Q y*Q y=Q y)
    (hnat : ∀ᶠ y in 𝓝 (g z), ∀ v : E, Q (φ y) (fderiv ℂ φ y v)=fderiv ℂ φ y (P y v))
    (hvel : ∀ᶠ w in 𝓝 z, P (g w) (deriv g w)=0)
    (hfi : ∀ᶠ w in 𝓝 z, P (g w) (f w)=f w)
    (hhi : ∀ᶠ w in 𝓝 z, Q (φ (g w)) (h w)=h w)
    (hfh : ∀ᶠ w in 𝓝 z, covariantDerivative P g f w=0)
    (hhh : ∀ᶠ w in 𝓝 z, covariantDerivative Q (φ ∘ g) h w=0)
    (he : h z=fderiv ℂ φ (g z) (f z)) :
    h =ᶠ[𝓝 z] fun w => fderiv ℂ φ (g w) (f w) := by
  have hcurve : AnalyticAt ℂ (φ ∘ g) z := hφ.comp hg
  have ht : AnalyticAt ℂ (fun w => fderiv ℂ φ (g w) (f w)) z :=
    ((ContinuousLinearMap.apply ℂ F (E := E)).analyticAt_bilinear _).comp
      (hf.prod (hφ.fderiv.comp hg))
  have hNatLocal : ∀ᶠ w in 𝓝 z, ∀ᶠ y in 𝓝 (g w), ∀ v : E,
      Q (φ y) (fderiv ℂ φ y v)=fderiv ℂ φ y (P y v) :=
    hg.continuousAt (eventually_eventually_nhds.mpr hnat)
  have hti : ∀ᶠ w in 𝓝 z, Q (φ (g w)) (fderiv ℂ φ (g w) (f w)) =
      fderiv ℂ φ (g w) (f w) := by
    filter_upwards [hg.continuousAt hnat,hfi] with w hn hi
    rw [hn (f w),hi]
  have hth : ∀ᶠ w in 𝓝 z, covariantDerivative Q (φ ∘ g)
      (fun w => fderiv ℂ φ (g w) (f w)) w=0 := by
    filter_upwards [hg.continuousAt hP.eventually_analyticAt,
      hcurve.continuousAt hQ.eventually_analyticAt,hg.continuousAt hφ.eventually_analyticAt,
      hg.eventually_analyticAt,hf.eventually_analyticAt,hNatLocal,hvel,
      hcurve.continuousAt hidQ,hfh] with w hp hq hφw hgw hfw hn hv hq2 hhor
    have hq2' : ∀ v : F, Q (φ (g w)) (Q (φ (g w)) v)=Q (φ (g w)) v := by
      intro v
      exact congrArg (fun A : F →L[ℂ] F => A v) hq2
    rw [covariantDerivative_naturality hp.differentiableAt hq.differentiableAt hφw
      hgw.differentiableAt hfw.differentiableAt hn hv hq2',hhor,map_zero]
  apply horizontal_local_uniqueness (P := Q) (g := φ ∘ g) hQ hcurve hidQ _ _ hhi hti he
  · filter_upwards [hh.eventually_analyticAt,hhh] with w ha hb
    exact ⟨ha.differentiableAt,hb⟩
  · filter_upwards [ht.eventually_analyticAt,hth] with w ha hb
    exact ⟨ha.differentiableAt,hb⟩



end SplitTangent.PullbackConnection

open Filter Topology Set

open scoped Manifold LinearAlgebra.Projectivization
open Bundle

namespace SplitTangent.TangentSplitting
section
open Filter Topology Set
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem coordinateProjector_analytic (x : X.Carrier) :
    AnalyticOnNhd ℂ (S.coordinateProjector x) (chartAt (Model X) x).target := by
  let e : Matrix (Fin X.dim) (Fin X.dim) ℂ ≃L[ℂ] (Model X →L[ℂ] Model X) :=
    (Matrix.toLin'.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  intro z hz
  have hM : AnalyticAt ℂ (fun z i j => S.coordinateMatrix x i j z) z := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    exact S.coordinateMatrix_analytic x i j z hz
  have he : (fun z => e (fun i j => S.coordinateMatrix x i j z))=S.coordinateProjector x := by
    funext z
    apply ContinuousLinearMap.ext
    intro v
    change Matrix.toLin' (LinearMap.toMatrix' (S.coordinateProjector x z).toLinearMap) v=_
    rw [Matrix.toLin'_toMatrix']
    rfl
  rw [← he]
  exact (e.toContinuousLinearMap.analyticAt _).comp hM

lemma coordinateProjector_fixed (x : X.Carrier) {y : X.Carrier}
    (hy : y ∈ (chartAt (Model X) x).source) (v : Tangent X y) :
    S.coordinateProjector x ((chartAt (Model X) x) y)
      ((trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ y v) =
      (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ y (S.projector y v) := by
  dsimp only [coordinateProjector]
  rw [(chartAt (Model X) x).left_inv hy]
  simp only [ContinuousLinearMap.comp_apply]
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hy]

lemma coordinateCurve_analytic {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) {z : ℂ}
    (hz : g z ∈ (chartAt (Model X) x).source) :
    AnalyticAt ℂ ((chartAt (Model X) x) ∘ g) z := by
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hz
  exact (hc.comp z (hg z)).contDiffAt.analyticAt

lemma coordinateCurve_derivative {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) {z : ℂ}
    (hz : g z ∈ (chartAt (Model X) x).source) :
    deriv ((chartAt (Model X) x) ∘ g) z =
      (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (g z)
        (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ)) := by
  have hc := (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hz).mdifferentiableAt (by simp)
  have he := mfderiv_comp_apply z hc ((hg z).mdifferentiableAt (by simp)) (1 : ℂ)
  rw [mfderiv_eq_fderiv] at he
  change (fderiv ℂ ((chartAt (Model X) x) ∘ g) z) (1 : ℂ) =
    mfderiv (ModelWithCorners X) 𝓘(ℂ,Model X) (chartAt (Model X) x) (g z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ)) at he
  rw [fderiv_eq_smul_deriv,one_smul] at he
  have ht := TangentBundle.continuousLinearMapAt_trivializationAt (I := ModelWithCorners X) hz
  rw [ht]
  change deriv ((chartAt (Model X) x) ∘ g) z =
    mfderiv (ModelWithCorners X) 𝓘(ℂ,Model X) (chartAt (Model X) x) (g z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))
  exact he

lemma coordinateCurve_complementary {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
    (x : X.Carrier) {z : ℂ} (hz : g z ∈ (chartAt (Model X) x).source) :
    S.coordinateProjector x ((chartAt (Model X) x) (g z))
      (deriv ((chartAt (Model X) x) ∘ g) z)=0 := by
  rw [coordinateCurve_derivative hg x hz,S.coordinateProjector_fixed x hz,hv z,map_zero]

 
lemma coordinateProjector_eventually_idempotent (x : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target) :
    ∀ᶠ w in 𝓝 z, S.coordinateProjector x w*S.coordinateProjector x w=S.coordinateProjector x w := by
  filter_upwards [(chartAt (Model X) x).open_target.mem_nhds hz] with w hw
  apply ContinuousLinearMap.ext
  intro v
  exact S.coordinateProjector_idempotent x hw v

 

theorem exists_manifold_local_transport {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (a : ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : ℂ → ℂ → Model X →L[ℂ] Model X,
      (∀ z ∈ Metric.ball a ε, g z ∈ (chartAt (Model X) (g a)).source) ∧
      AnalyticOnNhd ℂ (fun w : ℂ × ℂ => T w.1 w.2) (Metric.ball a ε ×ˢ Metric.ball a ε) ∧
      (∀ s ∈ Metric.ball a ε, T s s=1) ∧
      (∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε, ∀ u ∈ Metric.ball a ε, T t u*T s t=T s u) ∧
      (∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε, ∀ v : Model X,
        S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g s)) v=v →
        S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g t)) (T s t v)=T s t v ∧
        PullbackConnection.covariantDerivative (S.coordinateProjector (g a))
          ((chartAt (Model X) (g a)) ∘ g) (fun w => T s w v) t=0) := by
  let c := chartAt (Model X) (g a)
  have ha : g a ∈ c.source := mem_chart_source (Model X) (g a)
  have hat : c (g a) ∈ c.target := c.map_source ha
  obtain ⟨r,hr,T,hTa,hT0,_,hTc,hTh⟩ := PullbackConnection.exists_local_horizontal_transport
    (S.coordinateProjector_analytic (g a) _ hat) (coordinateCurve_analytic hg (g a) ha)
    (S.coordinateProjector_eventually_idempotent (g a) hat)
  obtain ⟨q,hq,hqn⟩ := Metric.eventually_nhds_iff_ball.mp (hg.continuous.continuousAt (c.open_source.mem_nhds ha))
  have hrm : Metric.ball a (min r q) ⊆ Metric.ball a r := Metric.ball_subset_ball (min_le_left _ _)
  have hqm : Metric.ball a (min r q) ⊆ Metric.ball a q := Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨min r q,lt_min hr hq,T,?_,?_,?_,?_,?_⟩
  · exact fun z hz => hqn z (hqm hz)
  · exact hTa.mono (Set.prod_mono hrm hrm)
  · exact fun s hs => hT0 s (hrm hs)
  · exact fun s hs t ht u hu => hTc s (hrm hs) t (hrm ht) u (hrm hu)
  · exact fun s hs t ht v hv => hTh s (hrm hs) t (hrm ht) v hv

end

open Filter Topology Set PullbackConnection HorizontalCovering
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

abbrev TangentImageFiber (g : ℂ → X.Carrier) (z : ℂ) :=
  {v : Tangent X (g z) // S.projector (g z) v=v}

 

structure LocalChartImages (g : ℂ → X.Carrier) where
  radius : ℂ → ℝ
  positive : ∀ a, 0 < radius a
  chart_source : ∀ a z, z ∈ Metric.ball a (radius a) → g z ∈ (chartAt (Model X) (g a)).source
  trans : ℂ → ℂ → ℂ → Model X →L[ℂ] Model X
  analytic : ∀ a, AnalyticOnNhd ℂ (fun w : ℂ × ℂ => trans a w.1 w.2)
    (Metric.ball a (radius a) ×ˢ Metric.ball a (radius a))
  normalized : ∀ a s, s ∈ Metric.ball a (radius a) → trans a s s=1
  cocycle : ∀ a s, s ∈ Metric.ball a (radius a) → ∀ t, t ∈ Metric.ball a (radius a) →
    ∀ u, u ∈ Metric.ball a (radius a) → trans a t u*trans a s t=trans a s u
  horizontal : ∀ a s, s ∈ Metric.ball a (radius a) → ∀ t, t ∈ Metric.ball a (radius a) →
    ∀ v : Model X, S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g s)) v=v →
      S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g t)) (trans a s t v)=trans a s t v ∧
      covariantDerivative (S.coordinateProjector (g a)) ((chartAt (Model X) (g a)) ∘ g)
        (fun w => trans a s w v) t=0

namespace LocalChartImages
variable {S} {g : ℂ → X.Carrier} (L : LocalChartImages S g)

abbrev frame (_L : LocalChartImages S g) (a : ℂ) := trivializationAt (Model X) (Tangent X) (g a)
abbrev coords (a z : ℂ) := (L.frame a).continuousLinearMapAt ℂ (g z)
abbrev uncoords (a z : ℂ) := (L.frame a).symmL ℂ (g z)

lemma center (a : ℂ) : a ∈ Metric.ball a (L.radius a) := Metric.mem_ball_self (L.positive a)
lemma frame_mem {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) : g z ∈ (L.frame a).baseSet :=
  L.chart_source a z hz
lemma uncoords_coords {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) (v : Tangent X (g z)) :
    L.uncoords a z (L.coords a z v)=v := (L.frame a).symmL_continuousLinearMapAt (L.frame_mem hz) v
lemma coords_uncoords {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) (v : Model X) :
    L.coords a z (L.uncoords a z v)=v := (L.frame a).continuousLinearMapAt_symmL (L.frame_mem hz) v

lemma coords_fixed {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) (v : TangentImageFiber S g z) :
    S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g z)) (L.coords a z v)=L.coords a z v := by
  rw [S.coordinateProjector_fixed (g a) (L.chart_source a z hz),v.2]

lemma uncoords_fixed {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) {v : Model X}
    (hv : S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g z)) v=v) :
    S.projector (g z) (L.uncoords a z v)=L.uncoords a z v := by
  have h := S.coordinateProjector_fixed (g a) (L.chart_source a z hz) (L.uncoords a z v)
  change S.coordinateProjector (g a) ((chartAt (Model X) (g a)) (g z))
    (L.coords a z (L.uncoords a z v))=L.coords a z (S.projector (g z) (L.uncoords a z v)) at h
  rw [L.coords_uncoords hz,hv] at h
  have he := congrArg (L.uncoords a z) h
  rw [L.uncoords_coords hz] at he
  exact he.symm

lemma trans_analytic {a s t : ℂ} (hs : s ∈ Metric.ball a (L.radius a))
    (ht : t ∈ Metric.ball a (L.radius a)) (v : Model X) :
    AnalyticAt ℂ (fun w => L.trans a s w v) t := by
  have h := (L.analytic a (s,t) ⟨hs,ht⟩).comp (analyticAt_const.prod analyticAt_id)
  exact ((ContinuousLinearMap.apply ℂ (Model X) (E := Model X)).analyticAt_bilinear _).comp (analyticAt_const.prod h)

def forward (a z : ℂ) (v : TangentImageFiber S g a) : TangentImageFiber S g z := by
  classical
  exact if hz : z ∈ Metric.ball a (L.radius a) then
    ⟨L.uncoords a z (L.trans a a z (L.coords a a v)),
      L.uncoords_fixed hz ((L.horizontal a a (L.center a) z hz _ (L.coords_fixed (L.center a) v)).1)⟩
  else ⟨0,by simp⟩

def reverse (a z : ℂ) (v : TangentImageFiber S g z) : TangentImageFiber S g a := by
  classical
  exact if hz : z ∈ Metric.ball a (L.radius a) then
    ⟨L.uncoords a a (L.trans a z a (L.coords a z v)),
      L.uncoords_fixed (L.center a) ((L.horizontal a z hz a (L.center a) _ (L.coords_fixed hz v)).1)⟩
  else ⟨0,by simp⟩

lemma forward_val {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) (v : TangentImageFiber S g a) :
    (L.forward a z v).1=L.uncoords a z (L.trans a a z (L.coords a a v)) := by
  simp only [forward,dite_eq_left hz]
lemma reverse_val {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) (v : TangentImageFiber S g z) :
    (L.reverse a z v).1=L.uncoords a a (L.trans a z a (L.coords a z v)) := by
  simp only [reverse,dite_eq_left hz]

lemma left_inverse {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) :
    Function.LeftInverse (L.reverse a z) (L.forward a z) := by
  intro v
  apply Subtype.ext
  rw [L.reverse_val hz,L.forward_val hz,L.coords_uncoords hz]
  have he := congrArg (fun A : Model X →L[ℂ] Model X => A (L.coords a a v))
    (L.cocycle a a (L.center a) z hz a (L.center a))
  rw [L.normalized a a (L.center a)] at he
  change L.uncoords a a (L.trans a z a (L.trans a a z (L.coords a a v)))=v
  rw [show L.trans a z a (L.trans a a z (L.coords a a v))=L.coords a a v from he]
  exact L.uncoords_coords (L.center a) v

lemma right_inverse {a z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) :
    Function.RightInverse (L.reverse a z) (L.forward a z) := by
  intro v
  apply Subtype.ext
  rw [L.forward_val hz,L.reverse_val hz,L.coords_uncoords (L.center a)]
  have he := congrArg (fun A : Model X →L[ℂ] Model X => A (L.coords a z v))
    (L.cocycle a z hz a (L.center a) z hz)
  rw [L.normalized a z hz] at he
  change L.uncoords a z (L.trans a a z (L.trans a z a (L.coords a z v)))=v
  rw [show L.trans a a z (L.trans a z a (L.coords a z v))=L.coords a z v from he]
  exact L.uncoords_coords hz v

lemma normalized_forward (a : ℂ) (v : TangentImageFiber S g a) : L.forward a a v=v := by
  apply Subtype.ext
  rw [L.forward_val (L.center a),L.normalized a a (L.center a),one_apply_eq_self]
  exact L.uncoords_coords (L.center a) v

end LocalChartImages

 

theorem exists_local_chart_images {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) : Nonempty (LocalChartImages S g) := by
  have h := fun a => S.exists_manifold_local_transport hg a
  choose r hr T hsrc hTa hTn hTc hTh using h
  exact ⟨⟨r,hr,hsrc,T,hTa,hTn,hTc,hTh⟩⟩

end SplitTangent.TangentSplitting

namespace SplitTangent.TangentSplitting.LocalChartImages
open Filter Topology Set PullbackConnection HorizontalCovering
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)

lemma transition_curve {a b z : ℂ} (hz : z ∈ Metric.ball a (L.radius a)) :
    coordinateTransition (g a) (g b) ((chartAt (Model X) (g a)) (g z)) =
      (chartAt (Model X) (g b)) (g z) := by
  dsimp only [coordinateTransition,Function.comp_apply]
  rw [(chartAt (Model X) (g a)).left_inv (L.chart_source a z hz)]

lemma transition_derivative {a b z : ℂ} (ha : z ∈ Metric.ball a (L.radius a))
    (hb : z ∈ Metric.ball b (L.radius b)) :
    fderiv ℂ (coordinateTransition (g a) (g b)) ((chartAt (Model X) (g a)) (g z)) =
      (L.coords b z).comp (L.uncoords a z) := by
  have hsa := L.chart_source a z ha
  have hsb := L.chart_source b z hb
  have he := (chartAt (Model X) (g a)).left_inv hsa
  rw [coordinateTransition_derivative (g a) (g b) ((chartAt (Model X) (g a)).map_source hsa)
    (by rw [he]; exact hsb),he]

lemma overlap_locally_unique
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
    {a b z : ℂ} (ha : z ∈ Metric.ball a (L.radius a)) (hb : z ∈ Metric.ball b (L.radius b))
    (v : TangentImageFiber S g a) :
    ∀ᶠ w in 𝓝 z, L.forward b w (L.reverse b z (L.forward a z v))=L.forward a w v := by
  let c := chartAt (Model X) (g a)
  let d := chartAt (Model X) (g b)
  let φ := coordinateTransition (g a) (g b)
  let P := S.coordinateProjector (g a)
  let Q := S.coordinateProjector (g b)
  let u := L.reverse b z (L.forward a z v)
  let f := fun w => L.trans a a w (L.coords a a v)
  let h := fun w => L.trans b b w (L.coords b b u)
  have hsa : g z ∈ c.source := L.chart_source a z ha
  have hsb : g z ∈ d.source := L.chart_source b z hb
  have he : c.symm (c (g z))=g z := c.left_inv hsa
  have hφ : φ (c (g z))=d (g z) := L.transition_curve ha
  have hhp : AnalyticAt ℂ P (c (g z)) := S.coordinateProjector_analytic (g a) _ (c.map_source hsa)
  have hhq : AnalyticAt ℂ Q (φ (c (g z))) := by
    rw [hφ]
    exact S.coordinateProjector_analytic (g b) _ (d.map_source hsb)
  have hha : AnalyticAt ℂ φ (c (g z)) := coordinateTransition_analytic (g a) (g b)
    (c.map_source hsa) (by change c.symm (c (g z)) ∈ d.source; rw [he]; exact hsb)
  have hiq : ∀ᶠ y in 𝓝 (φ (c (g z))), Q y*Q y=Q y := by
    rw [hφ]
    exact S.coordinateProjector_eventually_idempotent (g b) (d.map_source hsb)
  have hnat : ∀ᶠ y in 𝓝 (c (g z)), ∀ t : Model X,
      Q (φ y) (fderiv ℂ φ y t)=fderiv ℂ φ y (P y t) := by
    have hcn : ContinuousAt c.symm (c (g z)) := c.continuousAt_symm (c.map_source hsa)
    have hy : ∀ᶠ y in 𝓝 (c (g z)), c.symm y ∈ d.source :=
      hcn (d.open_source.mem_nhds (by rw [he]; exact hsb))
    filter_upwards [c.open_target.mem_nhds (c.map_source hsa),hy] with y hy hy'
    intro t
    exact (congrArg (fun A : Model X →L[ℂ] Model X => A t)
      (S.coordinateProjector_intertwining (g a) (g b) hy hy')).symm
  have hnA : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball a (L.radius a) := Metric.isOpen_ball.mem_nhds ha
  have hnB : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball b (L.radius b) := Metric.isOpen_ball.mem_nhds hb
  have hcur : (φ ∘ (c ∘ g)) =ᶠ[𝓝 z] d ∘ g := by
    filter_upwards [hnA] with w hw
    exact L.transition_curve hw
  have hcur' := eventually_eventually_nhds.mpr hcur
  have hvel : ∀ᶠ w in 𝓝 z, P ((c ∘ g) w) (deriv (c ∘ g) w)=0 := by
    filter_upwards [hnA] with w hw
    exact S.coordinateCurve_complementary hg hv (g a) (L.chart_source a w hw)
  have hfi : ∀ᶠ w in 𝓝 z, P ((c ∘ g) w) (f w)=f w := by
    filter_upwards [hnA] with w hw
    exact (L.horizontal a a (L.center a) w hw _ (L.coords_fixed (L.center a) v)).1
  have hhi : ∀ᶠ w in 𝓝 z, Q (φ ((c ∘ g) w)) (h w)=h w := by
    filter_upwards [hnA,hnB] with w hw hw'
    rw [show φ ((c ∘ g) w)=d (g w) from L.transition_curve hw]
    exact (L.horizontal b b (L.center b) w hw' _ (L.coords_fixed (L.center b) u)).1
  have hfh : ∀ᶠ w in 𝓝 z, covariantDerivative P (c ∘ g) f w=0 := by
    filter_upwards [hnA] with w hw
    exact (L.horizontal a a (L.center a) w hw _ (L.coords_fixed (L.center a) v)).2
  have hhh : ∀ᶠ w in 𝓝 z, covariantDerivative Q (φ ∘ (c ∘ g)) h w=0 := by
    filter_upwards [hnB,hcur'] with w hw hc
    rw [covariantDerivative_curve_congr hc]
    exact (L.horizontal b b (L.center b) w hw _ (L.coords_fixed (L.center b) u)).2
  have hstart : h z=fderiv ℂ φ ((c ∘ g) z) (f z) := by
    have hs := congrArg (fun t : TangentImageFiber S g z => L.coords b z t.1)
      (L.right_inverse hb (L.forward a z v))
    rw [L.forward_val hb,L.forward_val ha,L.coords_uncoords hb] at hs
    rw [show fderiv ℂ φ ((c ∘ g) z)=(L.coords b z).comp (L.uncoords a z) from
      L.transition_derivative ha hb]
    exact hs
  have hu := horizontal_chart_compatibility hhp hhq hha (coordinateCurve_analytic hg (g a) hsa)
    (L.trans_analytic (L.center a) ha _) (L.trans_analytic (L.center b) hb _)
    hiq hnat hvel hfi hhi hfh hhh hstart
  filter_upwards [hu,hnA,hnB] with w hw hwA hwB
  apply Subtype.ext
  rw [L.forward_val hwB,L.forward_val hwA]
  change L.uncoords b w (h w)=L.uncoords a w (f w)
  change h w=fderiv ℂ φ ((c ∘ g) w) (f w) at hw
  rw [hw,show fderiv ℂ φ ((c ∘ g) w)=(L.coords b w).comp (L.uncoords a w) from
    L.transition_derivative hwA hwB,ContinuousLinearMap.comp_apply,L.uncoords_coords hwB]

end SplitTangent.TangentSplitting.LocalChartImages

namespace SplitTangent.TangentSplitting
open Filter Topology Set PullbackConnection HorizontalCovering
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

namespace LocalChartImages
variable {S} {g : ℂ → X.Carrier} (L : LocalChartImages S g)

 

def toData (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0) :
    LocalTransportData ℂ (TangentImageFiber S g) where
  domain := fun a => Metric.ball a (L.radius a)
  domain_open := fun _ => Metric.isOpen_ball
  domain_self := L.center
  forward := L.forward
  reverse := L.reverse
  left_inv := fun _ _ hz => L.left_inverse hz
  right_inv := fun _ _ hz => L.right_inverse hz
  forward_self := L.normalized_forward
  overlap := fun _ _ _ hz v => L.overlap_locally_unique hg hv hz.1 hz.2 v

end LocalChartImages



end SplitTangent.TangentSplitting

open Filter Topology

namespace SplitTangent.TangentSplitting.LocalChartImages
open Filter Topology Set PullbackConnection HorizontalCovering
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
variable (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)

lemma cover_section_coordinates {σ : ℂ → (z : ℂ) × TangentImageFiber S g z}
    (hσ : (L.toData hg hv).IsHorizontalAlong id σ) (z : ℂ) :
    ∃ u : TangentImageFiber S g z,
      (fun w => L.coords z w ((σ w).2.1)) =ᶠ[𝓝 z] fun w => L.trans z z w (L.coords z z u) := by
  obtain ⟨u,hu⟩ := hσ z
  refine ⟨u,?_⟩
  filter_upwards [hu,Metric.isOpen_ball.mem_nhds (L.center z)] with w hw hm
  rw [hw]
  change L.coords z w (L.forward z w u).1=_
  rw [L.forward_val hm,L.coords_uncoords hm]

lemma cover_section_holomorphic {σ : ℂ → (z : ℂ) × TangentImageFiber S g z}
    (hσ : (L.toData hg hv).IsHorizontalAlong id σ) :
    ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,(σ z).2.1⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) := by
  intro z
  obtain ⟨u,hu⟩ := L.cover_section_coordinates hg hv hσ z
  have han : AnalyticAt ℂ (fun w => L.coords z w ((σ w).2.1)) z :=
    (L.trans_analytic (L.center z) (L.center z) _).congr hu.symm
  let t := trivializationAt (Model X) (Tangent X) (g z)
  have hz : g z ∈ t.baseSet := L.frame_mem (L.center z)
  apply (t.contMDiffAt_iff (f := fun w => (⟨g w,(σ w).2.1⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
    (by simpa only [t.mem_source] using hz)).mpr
  refine ⟨hg z,?_⟩
  apply han.contDiffAt.contMDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds (L.center z)] with w hw
  exact (t.continuousLinearMapAt_apply_of_mem ℂ (L.frame_mem hw) ((σ w).2.1)).symm

end SplitTangent.TangentSplitting.LocalChartImages

namespace SplitTangent.TangentSplitting
open Filter Topology Set PullbackConnection HorizontalCovering
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

lemma rational_forward_germ (g : RationalCurve X)
    (Lf : LocalChartImages S g.finite) (Li : LocalChartImages S g.infinity)
    (v : TangentImageFiber S g.finite 1) (w : TangentImageFiber S g.infinity 1)
    (hvw : v.1=w.1) :
    (fun z => (Lf.forward 1 z v).1) =ᶠ[𝓝 (1 : ℂ)] fun z => (Li.forward 1 z⁻¹ w).1 := by
  have hb : g.finite 1=g.infinity 1 := by simpa using g.overlap 1 one_ne_zero
  let c := chartAt (Model X) (g.finite 1)
  let P := S.coordinateProjector (g.finite 1)
  let f := fun z => Lf.trans 1 1 z (Lf.coords 1 1 v)
  let h := fun z => Li.trans 1 1 z⁻¹ (Li.coords 1 1 w)
  have hi : Tendsto (fun z : ℂ => z⁻¹) (𝓝 1) (𝓝 1) := by simpa using (continuousAt_inv₀ (one_ne_zero : (1:ℂ)≠0)).tendsto
  have hnF : ∀ᶠ z : ℂ in 𝓝 1, z ∈ Metric.ball 1 (Lf.radius 1) := Metric.isOpen_ball.mem_nhds (Lf.center 1)
  have hnI : ∀ᶠ z : ℂ in 𝓝 1, z⁻¹ ∈ Metric.ball 1 (Li.radius 1) := hi (Metric.isOpen_ball.mem_nhds (Li.center 1))
  have hn0 : ∀ᶠ z : ℂ in 𝓝 1, z≠0 := eventually_ne_nhds one_ne_zero
  have hcur : (c ∘ g.finite) =ᶠ[𝓝 (1 : ℂ)] (c ∘ g.infinity) ∘ (fun z => z⁻¹) := by
    filter_upwards [hn0] with z hz
    exact congrArg c (g.overlap z hz)
  have hcur' := eventually_eventually_nhds.mpr hcur
  have hf : ∀ᶠ z : ℂ in 𝓝 1, DifferentiableAt ℂ f z ∧ covariantDerivative P (c ∘ g.finite) f z=0 := by
    filter_upwards [hnF] with z hz
    exact ⟨(Lf.trans_analytic (Lf.center 1) hz _).differentiableAt,
      (Lf.horizontal 1 1 (Lf.center 1) z hz _ (Lf.coords_fixed (Lf.center 1) v)).2⟩
  have hh : ∀ᶠ z : ℂ in 𝓝 1, DifferentiableAt ℂ h z ∧ covariantDerivative P (c ∘ g.finite) h z=0 := by
    filter_upwards [hnI,hn0,hcur'] with z hz hz0 hcz
    have hA := Li.trans_analytic (Li.center 1) hz (Li.coords 1 1 w)
    have hk : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) z := differentiableAt_inv hz0
    have hgA := coordinateCurve_analytic g.infinity_holomorphic (g.infinity 1) (Li.chart_source 1 z⁻¹ hz)
    have hh0 := (Li.horizontal 1 1 (Li.center 1) z⁻¹ hz _ (Li.coords_fixed (Li.center 1) w)).2
    have hrep := covariantDerivative_reparam (P := S.coordinateProjector (g.infinity 1)) hgA.differentiableAt hA.differentiableAt hk
    refine ⟨hA.differentiableAt.comp z hk,?_⟩
    rw [covariantDerivative_curve_congr hcz]
    dsimp only [P,c,h]
    rw [hb]
    change covariantDerivative (S.coordinateProjector (g.infinity 1))
      (((chartAt (Model X) (g.infinity 1)) ∘ g.infinity) ∘ (fun z => z⁻¹))
      ((fun z => Li.trans 1 1 z (Li.coords 1 1 w)) ∘ (fun z => z⁻¹)) z=0
    rw [hrep,hh0,smul_zero]
  have hfi : ∀ᶠ z : ℂ in 𝓝 1, P ((c ∘ g.finite) z) (f z)=f z := by
    filter_upwards [hnF] with z hz
    exact (Lf.horizontal 1 1 (Lf.center 1) z hz _ (Lf.coords_fixed (Lf.center 1) v)).1
  have hhi : ∀ᶠ z : ℂ in 𝓝 1, P ((c ∘ g.finite) z) (h z)=h z := by
    filter_upwards [hnI,hn0] with z hz hz0
    dsimp only [P,c,Function.comp_apply]
    rw [g.overlap z hz0,hb]
    exact (Li.horizontal 1 1 (Li.center 1) z⁻¹ hz _ (Li.coords_fixed (Li.center 1) w)).1
  have he : f 1=h 1 := by
    dsimp only [f,h]
    rw [inv_one,Lf.normalized 1 1 (Lf.center 1),Li.normalized 1 1 (Li.center 1)]
    simp only [one_apply_eq_self]
    change (trivializationAt (Model X) (Tangent X) (g.finite 1)).continuousLinearMapAt ℂ (g.finite 1) v.1=
      (trivializationAt (Model X) (Tangent X) (g.infinity 1)).continuousLinearMapAt ℂ (g.infinity 1) w.1
    simp only [hb,hvw]
    have hcbase (x y : X.Carrier) (hxy : x=y) (q : Model X) :
        (trivializationAt (Model X) (Tangent X) (g.infinity 1)).continuousLinearMapAt ℂ x q =
          (trivializationAt (Model X) (Tangent X) (g.infinity 1)).continuousLinearMapAt ℂ y q := by
      subst y
      rfl
    exact hcbase _ _ hb w.1
  have hsource : g.finite 1 ∈ c.source := mem_chart_source (Model X) (g.finite 1)
  have hu := horizontal_local_uniqueness (S.coordinateProjector_analytic _ _ (c.map_source hsource))
    (coordinateCurve_analytic g.finite_holomorphic _ hsource)
    (S.coordinateProjector_eventually_idempotent _ (c.map_source hsource)) hf hh hfi hhi he
  filter_upwards [hu,hnF,hnI,hn0] with z hz hzF hzI hz0
  rw [Lf.forward_val hzF,Li.forward_val hzI]
  change Lf.uncoords 1 z (f z)=Li.uncoords 1 z⁻¹ (h z)
  rw [hz]
  dsimp only [LocalChartImages.uncoords,LocalChartImages.frame]
  simp only [hb]
  have hubase (x y : X.Carrier) (hxy : x=y) (q : Model X) :
      (trivializationAt (Model X) (Tangent X) (g.infinity 1)).symmL ℂ x q =
        (trivializationAt (Model X) (Tangent X) (g.infinity 1)).symmL ℂ y q := by
    subst y
    rfl
  exact hubase _ _ (g.overlap z hz0) (h z)

end SplitTangent.TangentSplitting

namespace SplitTangent
open Filter Topology Set
variable {X : ComplexManifold.{u}}

 

lemma rational_section_gluing (g : RationalCurve X)
    (sf : ∀ z, Tangent X (g.finite z)) (si : ∀ z, Tangent X (g.infinity z))
    (hf : ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g.finite z,sf z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)))
    (hi : ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g.infinity z,si z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)))
    (he : sf =ᶠ[𝓝 (1:ℂ)] fun z => si z⁻¹) : ∀ z, z≠0 → sf z=si z⁻¹ := by
  have hconn : IsPreconnected ({0}ᶜ : Set ℂ) :=
    (isPathConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) (0 : ℂ)).isConnected.isPreconnected
  have hl : ∀ z ∈ ({0}ᶜ : Set ℂ), ∃ f : ℂ → Model X, AnalyticAt ℂ f z ∧
      ∀ᶠ w in 𝓝 z, sf w=si w⁻¹ ↔ f w=0 := by
    intro z hz
    let t := trivializationAt (Model X) (Tangent X) (g.finite z)
    have hzF : g.finite z ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
    have hzI : g.infinity z⁻¹ ∈ t.baseSet := (g.overlap z hz) ▸ hzF
    have hF := ((t.contMDiffAt_iff (f := fun w => (⟨g.finite w,sf w⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
      (t.mem_source.mpr hzF)).mp (hf z)).2.contDiffAt.analyticAt
    have hInv : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w : ℂ => w⁻¹) z :=
      (analyticAt_id.inv hz).contDiffAt.contMDiffAt
    have hI := ((t.contMDiffAt_iff (f := fun w => (⟨g.infinity w⁻¹,si w⁻¹⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
      (t.mem_source.mpr hzI)).mp ((hi z⁻¹).comp z hInv)).2.contDiffAt.analyticAt
    refine ⟨fun w => (t ⟨g.finite w,sf w⟩).2-(t ⟨g.infinity w⁻¹,si w⁻¹⟩).2,hF.sub hI,?_⟩
    filter_upwards [(g.finite_holomorphic.continuous.continuousAt.eventually (t.open_baseSet.mem_nhds hzF)),
      eventually_ne_nhds hz] with w hw hw0
    have hbw := g.overlap w hw0
    have hwF : (⟨g.finite w,sf w⟩ : TangentBundle (ModelWithCorners X) X.Carrier) ∈ t.source := t.mem_source.mpr hw
    have hwI : (⟨g.infinity w⁻¹,si w⁻¹⟩ : TangentBundle (ModelWithCorners X) X.Carrier) ∈ t.source := t.mem_source.mpr (hbw ▸ hw)
    constructor
    · intro h
      have htotal : (⟨g.finite w,sf w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)=⟨g.infinity w⁻¹,si w⁻¹⟩ :=
        Bundle.TotalSpace.ext hbw (heq_of_eq h)
      exact sub_eq_zero.mpr (congrArg (fun q => (t q).2) htotal)
    · intro h
      have hh : t ⟨g.finite w,sf w⟩=t ⟨g.infinity w⁻¹,si w⁻¹⟩ := by
        apply Prod.ext
        · rw [t.coe_fst hwF,t.coe_fst hwI]
          exact hbw
        · exact sub_eq_zero.mp h
      have hh' := t.injOn hwF hwI hh
      exact congrArg (fun q : TangentBundle (ModelWithCorners X) X.Carrier => q.2) hh'
  exact fun z hz => AnalyticContinuation.subset_of_local_analytic_equations hconn hl
    ⟨1,one_ne_zero,mem_interior_iff_mem_nhds.mpr he⟩ hz

end SplitTangent

namespace SplitTangent.TangentSplitting.LocalChartImages
section
open Filter Topology Set HorizontalCovering
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
  (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)

 

noncomputable def continuation (a b : ℂ) :
    TangentImageFiber S g a ≃ TangentImageFiber S g b :=
  (L.toData hg hv).globalTransport a b

lemma continuation_self (a : ℂ) (v : TangentImageFiber S g a) :
    L.continuation hg hv a a v=v :=
  (L.toData hg hv).globalTransport_self a v

lemma continuation_cocycle (a b c : ℂ) (v : TangentImageFiber S g a) :
    L.continuation hg hv b c (L.continuation hg hv a b v)=L.continuation hg hv a c v :=
  (L.toData hg hv).globalTransport_cocycle a b c v

lemma continuation_holomorphic (a : ℂ) (v : TangentImageFiber S g a) :
    ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,(L.continuation hg hv a z v).1⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) := by
  exact L.cover_section_holomorphic hg hv ((L.toData hg hv).globalSection_horizontal a v)

lemma continuation_add (a b : ℂ) (v w : TangentImageFiber S g a) :
    (L.continuation hg hv a b ⟨v.1+w.1,by simp only [map_add,v.2,w.2]⟩).1 =
      (L.continuation hg hv a b v).1+(L.continuation hg hv a b w).1 := by
  let D := L.toData hg hv
  let τ : (z : ℂ) → TangentImageFiber S g z := fun z => ⟨
    (D.globalTransport a z v).1+(D.globalTransport a z w).1,
    by rw [map_add,(D.globalTransport a z v).2,(D.globalTransport a z w).2]⟩
  have ht : D.IsHorizontalAlong id (fun z => ⟨z,τ z⟩) := by
    intro c
    refine ⟨τ c,?_⟩
    filter_upwards [D.globalTransport_germ a c v,D.globalTransport_germ a c w,
      Metric.ball_mem_nhds c (L.positive c)] with z hzv hzw hz
    apply congrArg (Sigma.mk z)
    apply Subtype.ext
    change (D.globalTransport a z v).1+(D.globalTransport a z w).1=(L.forward c z (τ c)).1
    rw [hzv,hzw]
    change (L.forward c z (D.globalTransport a c v)).1+
      (L.forward c z (D.globalTransport a c w)).1=(L.forward c z (τ c)).1
    rw [L.forward_val hz,L.forward_val hz,L.forward_val hz]
    simp only [τ,map_add]
  have he := congrFun (D.globalSection_unique ht a) b
  have hta : τ a=⟨v.1+w.1,by simp only [map_add,v.2,w.2]⟩ := by
    apply Subtype.ext
    dsimp only [τ]
    rw [D.globalTransport_self,D.globalTransport_self]
  rw [hta] at he
  exact congrArg Subtype.val he

lemma continuation_smul (a b : ℂ) (c : ℂ) (v : TangentImageFiber S g a) :
    (L.continuation hg hv a b ⟨c • v.1,by simp only [map_smul,v.2]⟩).1 =
      c • (L.continuation hg hv a b v).1 := by
  let D := L.toData hg hv
  let τ : (z : ℂ) → TangentImageFiber S g z := fun z => ⟨
    c • (D.globalTransport a z v).1,
    by rw [map_smul,(D.globalTransport a z v).2]⟩
  have ht : D.IsHorizontalAlong id (fun z => ⟨z,τ z⟩) := by
    intro d
    refine ⟨τ d,?_⟩
    filter_upwards [D.globalTransport_germ a d v,
      Metric.ball_mem_nhds d (L.positive d)] with z hzv hz
    apply congrArg (Sigma.mk z)
    apply Subtype.ext
    change c • (D.globalTransport a z v).1=(L.forward d z (τ d)).1
    rw [hzv]
    change c • (L.forward d z (D.globalTransport a d v)).1=(L.forward d z (τ d)).1
    rw [L.forward_val hz,L.forward_val hz]
    simp only [τ,map_smul]
  have he := congrFun (D.globalSection_unique ht a) b
  have hta : τ a=⟨c • v.1,by simp only [map_smul,v.2]⟩ := by
    apply Subtype.ext
    dsimp only [τ]
    rw [D.globalTransport_self]
  rw [hta] at he
  exact congrArg Subtype.val he

end

open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
  (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)

 

noncomputable def continuationLinear (a b : ℂ) :
    Tangent X (g a) →ₗ[ℂ] Tangent X (g b) where
  toFun v := (L.continuation hg hv a b ⟨S.projector (g a) v,S.idempotent (g a) v⟩).1
  map_add' v w := by
    simpa only [map_add] using L.continuation_add hg hv a b
      ⟨S.projector (g a) v,S.idempotent (g a) v⟩ ⟨S.projector (g a) w,S.idempotent (g a) w⟩
  map_smul' c v := by
    simpa only [map_smul,RingHom.id_apply] using L.continuation_smul hg hv a b c
      ⟨S.projector (g a) v,S.idempotent (g a) v⟩

noncomputable def continuationMap (a b : ℂ) :
    Tangent X (g a) →L[ℂ] Tangent X (g b) := by
  let t := trivializationAt (Model X) (Tangent X) (g a)
  let e := t.continuousLinearEquivAt ℂ (g a) (FiberBundle.mem_baseSet_trivializationAt' (g a))
  letI : FiniteDimensional ℂ (Tangent X (g a)) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  letI : T2Space (Tangent X (g a)) := inferInstanceAs (T2Space (Model X))
  exact (L.continuationLinear hg hv a b).toContinuousLinearMap

lemma continuationMap_apply (a b : ℂ) (v : Tangent X (g a)) :
    L.continuationMap hg hv a b v =
      (L.continuation hg hv a b ⟨S.projector (g a) v,S.idempotent (g a) v⟩).1 := rfl

lemma continuationMap_fixed (a b : ℂ) (v : Tangent X (g a)) :
    S.projector (g b) (L.continuationMap hg hv a b v)=L.continuationMap hg hv a b v :=
  (L.continuation hg hv a b ⟨S.projector (g a) v,S.idempotent (g a) v⟩).2

lemma continuationMap_self (a : ℂ) : L.continuationMap hg hv a a=S.projector (g a) := by
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg Subtype.val (L.continuation_self hg hv a
    ⟨S.projector (g a) v,S.idempotent (g a) v⟩)

lemma continuationMap_cocycle (a b c : ℂ) (v : Tangent X (g a)) :
    L.continuationMap hg hv b c (L.continuationMap hg hv a b v)=L.continuationMap hg hv a c v := by
  rw [L.continuationMap_apply]
  have he : (⟨S.projector (g b) (L.continuationMap hg hv a b v),
      S.idempotent (g b) (L.continuationMap hg hv a b v)⟩ : TangentImageFiber S g b)=
      L.continuation hg hv a b ⟨S.projector (g a) v,S.idempotent (g a) v⟩ := by
    apply Subtype.ext
    exact L.continuationMap_fixed hg hv a b v
  rw [he,L.continuation_cocycle]
  rfl

lemma continuationMap_reverse (a b : ℂ) (v : Tangent X (g a)) :
    L.continuationMap hg hv b a (L.continuationMap hg hv a b v)=S.projector (g a) v := by
  rw [L.continuationMap_cocycle,L.continuationMap_self]

lemma continuationMap_holomorphic (a : ℂ) (v : Tangent X (g a)) :
    ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,L.continuationMap hg hv a z v⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) :=
  L.continuation_holomorphic hg hv a ⟨S.projector (g a) v,S.idempotent (g a) v⟩

end SplitTangent.TangentSplitting.LocalChartImages

namespace SplitTangent.TangentSplitting.LocalChartImages
section
open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
  (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)

lemma continuationMap_reverse_local (b : ℂ) {z : ℂ} (hz : z ∈ Metric.ball b (L.radius b))
    (v : Tangent X (g z)) : L.continuationMap hg hv z b v=
      L.uncoords b b (L.trans b z b (L.coords b z (S.projector (g z) v))) := by
  rw [L.continuationMap_apply]
  have hc : IsConnected ((L.toData hg hv).domain b) :=
    ⟨⟨b,L.center b⟩,(convex_ball b (L.radius b)).isPreconnected⟩
  change ((L.toData hg hv).globalTransport z b
    ⟨S.projector (g z) v,S.idempotent (g z) v⟩).1=_
  rw [(L.toData hg hv).globalTransport_reverse_local b hc hz]
  exact L.reverse_val hz _

 

lemma continuationMap_reverse_holomorphic_at (a b : ℂ) (v : ∀ z, Tangent X (g z))
    (hvs : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) b) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g a,L.continuationMap hg hv z a (v z)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) b := by
  let t := L.frame b
  let u := trivializationAt (Model X) (Tangent X) (g a)
  have ht : g b ∈ t.baseSet := L.frame_mem (L.center b)
  have hu : g a ∈ u.baseSet := FiberBundle.mem_baseSet_trivializationAt' (g a)
  have hp : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,S.projector (g z) (v z)⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) b :=
    S.holomorphic.contMDiffAt.comp b hvs
  have hp' := ((t.contMDiffAt_iff (f := fun z => (⟨g z,S.projector (g z) (v z)⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using ht)).mp hp).2
  have hc : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,Model X) ω
      (fun z => L.coords b z (S.projector (g z) (v z))) b := by
    apply hp'.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds b (L.positive b)] with z hz
    exact t.continuousLinearMapAt_apply_of_mem ℂ (L.frame_mem hz) _
  have hTa : AnalyticAt ℂ (fun z => L.trans b z b) b :=
    (L.analytic b (b,b) ⟨L.center b,L.center b⟩).comp
      (g := fun w : ℂ × ℂ => L.trans b w.1 w.2)
      (f := fun z : ℂ => (z,b)) (analyticAt_id.prod analyticAt_const)
  have hf := hTa.contDiffAt.contMDiffAt.clm_apply hc
  let C : Model X →L[ℂ] Model X := (u.continuousLinearMapAt ℂ (g a)).comp
    ((L.continuationMap hg hv b a).comp (L.uncoords b b))
  have hCf : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,Model X) ω
      (fun z => C (L.trans b z b (L.coords b z (S.projector (g z) (v z))))) b :=
    C.contDiff.contMDiff.contMDiffAt.comp b hf
  apply (u.contMDiffAt_iff (f := fun z => (⟨g a,L.continuationMap hg hv z a (v z)⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [u.mem_source] using hu)).mpr
  refine ⟨contMDiffAt_const,?_⟩
  apply hCf.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds b (L.positive b)] with z hz
  rw [← L.continuationMap_cocycle hg hv z b a (v z),L.continuationMap_reverse_local hg hv b hz]
  exact (u.continuousLinearMapAt_apply_of_mem ℂ hu _).symm

end

open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
  (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
lemma continuation_germ (a b : ℂ) (v : TangentImageFiber S g a) :
    ∀ᶠ z in 𝓝 b, L.continuation hg hv a z v =
      L.forward b z (L.continuation hg hv a b v) :=
  (L.toData hg hv).globalTransport_germ a b v

lemma continuationMap_apply_fixed (a b : ℂ) (v : Tangent X (g a))
    (h : S.projector (g a) v=v) : L.continuationMap hg hv a b v=
      (L.continuation hg hv a b ⟨v,h⟩).1 := by
  rw [L.continuationMap_apply]
  congr 2
  exact Subtype.ext h
end SplitTangent.TangentSplitting.LocalChartImages

namespace SplitTangent.TangentSplitting
open Filter Topology Set
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

lemma rational_continuation_overlap (g : RationalCurve X)
    (Lf : LocalChartImages S g.finite) (Li : LocalChartImages S g.infinity)
    (hvf : ∀ z, S.projector (g.finite z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.finite z (1 : ℂ))=0)
    (hvi : ∀ z, S.projector (g.infinity z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.infinity z (1 : ℂ))=0)
    (a : ℂ) (v : Tangent X (g.finite a)) {z : ℂ} (hz : z ≠ 0) :
    Lf.continuationMap g.finite_holomorphic hvf a z v =
      Li.continuationMap g.infinity_holomorphic hvi 1 z⁻¹
        (Lf.continuationMap g.finite_holomorphic hvf a 1 v) := by
  let u0 : TangentImageFiber S g.finite a := ⟨S.projector (g.finite a) v,S.idempotent _ v⟩
  let u := Lf.continuation g.finite_holomorphic hvf a 1 u0
  have hb : g.finite 1=g.infinity 1 := by simpa using g.overlap 1 one_ne_zero
  let w : TangentImageFiber S g.infinity 1 := ⟨u.1,by rw [← hb]; exact u.2⟩
  let sf := fun q => (Lf.continuation g.finite_holomorphic hvf a q u0).1
  let si := fun q => (Li.continuation g.infinity_holomorphic hvi 1 q w).1
  have hsf := Lf.continuation_holomorphic g.finite_holomorphic hvf a u0
  have hsi := Li.continuation_holomorphic g.infinity_holomorphic hvi 1 w
  have hf := Lf.continuation_germ g.finite_holomorphic hvf a 1 u0
  have hi := Li.continuation_germ g.infinity_holomorphic hvi 1 1 w
  rw [Li.continuation_self] at hi
  have hloc := S.rational_forward_germ g Lf Li u w rfl
  have hinv : Tendsto (fun q : ℂ => q⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using (continuousAt_inv₀ (one_ne_zero : (1:ℂ)≠0)).tendsto
  have he : sf =ᶠ[𝓝 (1:ℂ)] fun q => si q⁻¹ := by
    filter_upwards [hf,hinv hi,hloc] with q hq hq' hqv
    dsimp only [sf,si]
    rw [hq,hq']
    exact hqv
  have hEq := rational_section_gluing g sf si hsf hsi he z hz
  rw [Lf.continuationMap_apply]
  change sf z=Li.continuationMap g.infinity_holomorphic hvi 1 z⁻¹ u.1
  rw [Li.continuationMap_apply_fixed _ _ _ _ _ w.2]
  exact hEq

end SplitTangent.TangentSplitting

namespace SplitTangent
section
open Filter Topology Set

lemma holomorphic_const_fiber_linear_at {X : ComplexManifold.{u}} {x y : X.Carrier}
    (A : Tangent X x →L[ℂ] Tangent X y) {v : ℂ → Tangent X x} {b : ℂ}
    (hv : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨x,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) b) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨y,A (v z)⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) b := by
  let t := trivializationAt (Model X) (Tangent X) x
  let u := trivializationAt (Model X) (Tangent X) y
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hy : y ∈ u.baseSet := FiberBundle.mem_baseSet_trivializationAt' y
  have hvc := ((t.contMDiffAt_iff (f := fun z => (⟨x,v z⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using hx)).mp hv).2
  let C : Model X →L[ℂ] Model X := (u.continuousLinearMapAt ℂ y).comp (A.comp (t.symmL ℂ x))
  have hc := C.contDiff.contMDiff.contMDiffAt.comp b hvc
  apply (u.contMDiffAt_iff (f := fun z => (⟨y,A (v z)⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [u.mem_source] using hy)).mpr
  refine ⟨contMDiffAt_const,?_⟩
  apply hc.congr_of_eventuallyEq
  filter_upwards [] with z
  change (u ⟨y,A (v z)⟩).2=C (t ⟨x,v z⟩).2
  rw [← t.continuousLinearMapAt_apply_of_mem ℂ hx]
  dsimp only [C,ContinuousLinearMap.comp_apply]
  rw [t.symmL_continuousLinearMapAt hx]
  exact (u.continuousLinearMapAt_apply_of_mem ℂ hy _).symm

namespace TangentSplitting.LocalChartImages
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
  (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
lemma continuationMap_source (a b : ℂ) (v : Tangent X (g a)) :
    L.continuationMap hg hv a b (S.projector (g a) v)=L.continuationMap hg hv a b v := by
  rw [L.continuationMap_apply,L.continuationMap_apply]
  congr 2
  exact Subtype.ext (S.idempotent _ v)
end TangentSplitting.LocalChartImages

namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)
lemma rational_reverse_overlap (g : RationalCurve X)
    (Lf : LocalChartImages S g.finite) (Li : LocalChartImages S g.infinity)
    (hvf : ∀ z, S.projector (g.finite z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.finite z (1 : ℂ))=0)
    (hvi : ∀ z, S.projector (g.infinity z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.infinity z (1 : ℂ))=0)
    (a : ℂ) {z : ℂ} (hz : z ≠ 0) (v : Tangent X (g.finite z)) :
    Lf.continuationMap g.finite_holomorphic hvf z a v =
      Lf.continuationMap g.finite_holomorphic hvf 1 a
        (Li.continuationMap g.infinity_holomorphic hvi z⁻¹ 1 v) := by
  let f := Lf.continuationMap g.finite_holomorphic hvf
  let i := Li.continuationMap g.infinity_holomorphic hvi
  let w := i z⁻¹ 1 v
  have hb : g.finite 1=g.infinity 1 := by simpa using g.overlap 1 one_ne_zero
  have hw : S.projector (g.finite 1) w=w := by
    rw [hb]
    exact Li.continuationMap_fixed _ _ _ _ _
  have hfw : f a 1 (f 1 a w)=w := by
    dsimp only [f]
    erw [Lf.continuationMap_reverse,hw]
  have hiw : i 1 z⁻¹ w=S.projector (g.finite z) v := by
    dsimp only [i,w]
    erw [Li.continuationMap_reverse,g.overlap z hz]
  change f z a v=f 1 a w
  calc
    _ = f z a (S.projector (g.finite z) v) := (Lf.continuationMap_source _ _ _ _ _).symm
    _ = f z a (i 1 z⁻¹ w) := by rw [hiw]
    _ = f z a (i 1 z⁻¹ (f a 1 (f 1 a w))) := by rw [hfw]
    _ = f z a (f a z (f 1 a w)) := by
      rw [S.rational_continuation_overlap g Lf Li hvf hvi a (f 1 a w) hz]
    _ = f 1 a w := by
      dsimp only [f]
      erw [Lf.continuationMap_reverse,Lf.continuationMap_fixed]

 

noncomputable def rationalReverseMap (g : RationalCurve X)
    (Lf : LocalChartImages S g.finite) (Li : LocalChartImages S g.infinity)
    (hvf : ∀ z, S.projector (g.finite z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.finite z (1 : ℂ))=0)
    (hvi : ∀ z, S.projector (g.infinity z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g.infinity z (1 : ℂ))=0)
    (a : ℂ) : CurveBundleMap g (RationalCurve.constant (g.finite a)) where
  finite z := Lf.continuationMap g.finite_holomorphic hvf z a
  infinity z := (Lf.continuationMap g.finite_holomorphic hvf 1 a).comp
    (Li.continuationMap g.infinity_holomorphic hvi z 1)
  overlap z hz := by
    apply ContinuousLinearMap.ext
    intro v
    exact S.rational_reverse_overlap g Lf Li hvf hvi a hz v
  finite_holomorphic U hU v hv z hz :=
    (Lf.continuationMap_reverse_holomorphic_at g.finite_holomorphic hvf a z v
      ((hv z hz).contMDiffAt (hU.mem_nhds hz))).contMDiffWithinAt
  infinity_holomorphic U hU v hv z hz := by
    have h := Li.continuationMap_reverse_holomorphic_at g.infinity_holomorphic hvi 1 z v
      ((hv z hz).contMDiffAt (hU.mem_nhds hz))
    have hb : g.finite 1=g.infinity 1 := by simpa using g.overlap 1 one_ne_zero
    rw [← hb] at h
    exact (holomorphic_const_fiber_linear_at
      (Lf.continuationMap g.finite_holomorphic hvf 1 a) h).contMDiffWithinAt

end TangentSplitting
end

open Filter Topology Set



end SplitTangent

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.BoxTransportBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Box Transport Base. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle
universe u

namespace SplitTangent
open Filter Topology Set

 

structure TangentBox {X : ComplexManifold.{u}} (S : TangentSplitting X) (g : RationalCurve X) where
  chart : Bool → Bool → ℂ × ℂ → X.Carrier
  holomorphic : ∀ a b, ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (chart a b)
  overlap : ∀ a b c d w, w ∈ ReciprocalCharts.overlap a b c d →
    chart a b w = chart c d (ReciprocalCharts.changeChart (Bool.xor a c) (Bool.xor b d) w)
  finite_diagonal : ∀ z, chart false false (z,z) = g.finite z
  infinity_diagonal : ∀ z, chart true true (z,z) = g.infinity z
  tangency : ∀ a b w,
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (chart a b) w (1,0) ∈ S.first (chart a b w) ∧
    mfderiv 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) (chart a b) w (0,1) ∈ S.second (chart a b w)

end SplitTangent

namespace SplitTangent.TangentBox
open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : RationalCurve X}
  (F : TangentBox S g)

 
def firstFactor (b : ℂ) : RationalCurve X where
  finite z := F.chart false false (z,b)
  infinity z := F.chart true false (z,b)
  finite_holomorphic := (F.holomorphic false false).comp
    ((contDiff_id.prodMk contDiff_const : ContDiff ℂ ω (fun z : ℂ => (z,b))).contMDiff)
  infinity_holomorphic := (F.holomorphic true false).comp
    ((contDiff_id.prodMk contDiff_const : ContDiff ℂ ω (fun z : ℂ => (z,b))).contMDiff)
  overlap z hz := by
    have h := F.overlap false false true false (z,b) ⟨fun _ => hz,by simp⟩
    simpa [ReciprocalCharts.changeChart,ReciprocalCharts.coord] using h

end SplitTangent.TangentBox

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.FamilyPropagationStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Family Propagation Step. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle
universe u

namespace SplitTangent.TangentSplitting
open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

structure LocalFamilyTransport (F : ℂ × ℂ → X.Carrier) where
  radius : ℝ
  positive : 0 < radius
  chart_source : ∀ s t, ‖s‖ < radius → ‖t‖ < radius →
    F (s,t) ∈ (chartAt (Model X) (F (0,0))).source
  trans : ℂ → ℂ → ℂ → Model X →L[ℂ] Model X
  normalized : ∀ s u, ‖s‖ < radius → ‖u‖ < radius → trans s u u=1
  cocycle : ∀ s u v w, ‖s‖ < radius → ‖u‖ < radius → ‖v‖ < radius → ‖w‖ < radius →
    trans s v w*trans s u v=trans s u w
  horizontal : ∀ s u v, ‖s‖ < radius → ‖u‖ < radius → ‖v‖ < radius → ∀ e : Model X,
    S.coordinateProjector (F (0,0)) ((chartAt (Model X) (F (0,0))) (F (s,u))) e=e →
    S.coordinateProjector (F (0,0)) ((chartAt (Model X) (F (0,0))) (F (s,v))) (trans s u v e)=trans s u v e ∧
    covariantDerivative (S.coordinateProjector (F (0,0)))
      (fun t => (chartAt (Model X) (F (0,0))) (F (s,t))) (fun t => trans s u t e) v=0
  analytic : ∀ (q u v : ℂ → ℂ) z, AnalyticAt ℂ q z → AnalyticAt ℂ u z → AnalyticAt ℂ v z →
    ‖q z‖ < radius → ‖u z‖ < radius → ‖v z‖ < radius →
    AnalyticAt ℂ (fun w => trans (q w) (u w) (v w)) z

 

theorem exists_local_family_transport {F : ℂ × ℂ → X.Carrier}
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F) :
    Nonempty (S.LocalFamilyTransport F) := by
  let x := F (0,0)
  let c := chartAt (Model X) x
  have hx : x ∈ c.source := mem_chart_source (Model X) x
  have hxt : c x ∈ c.target := c.map_source hx
  have hf : AnalyticAt ℂ (c ∘ F) (0,0) := by
    have hc := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hx
    exact (hc.comp (0,0) (hF (0,0))).contDiffAt.analyticAt
  obtain ⟨T,r,hr,hT0,_,hTc,hTh,hTa⟩ := exists_horizontal_parameter_transport
    (S.coordinateProjector_analytic x _ hxt) hf (S.coordinateProjector_eventually_idempotent x hxt)
  obtain ⟨q,hq,hqn⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hF (0,0)).continuousAt (c.open_source.mem_nhds hx))
  let ε := min r q
  have hε : 0 < ε := lt_min hr hq
  have her : ε ≤ r := min_le_left _ _
  have heq : ε ≤ q := min_le_right _ _
  refine ⟨⟨ε,hε,?_,T,?_,?_,?_,?_⟩⟩
  · intro s t hs ht
    apply hqn (s,t)
    simp only [Metric.mem_ball,dist_eq_norm,Prod.mk_sub_mk,sub_zero,Prod.norm_def]
    exact max_lt (hs.trans_le heq) (ht.trans_le heq)
  · exact fun s u hs hu => hT0 s u (hs.trans_le her) (hu.trans_le her)
  · exact fun s u v w hs hu hv hw => hTc s u v w (hs.trans_le her) (hu.trans_le her)
      (hv.trans_le her) (hw.trans_le her)
  · exact fun s u v hs hu hv e he => hTh s u v (hs.trans_le her) (hu.trans_le her) (hv.trans_le her) e he
  · exact fun q u v z hq hu hv hqr hur hvr => hTa q u v z hq hu hv
      (hqr.trans_le her) (hur.trans_le her) (hvr.trans_le her)

namespace LocalFamilyTransport
variable {S} {F : ℂ × ℂ → X.Carrier} (L : LocalFamilyTransport S F)
abbrev frame (_L : LocalFamilyTransport S F) := trivializationAt (Model X) (Tangent X) (F (0,0))

 

def map (s u v : ℂ) : Tangent X (F (s,u)) →L[ℂ] Tangent X (F (s,v)) :=
  (L.frame.symmL ℂ (F (s,v))).comp ((L.trans s u v).comp
    ((L.frame.continuousLinearMapAt ℂ (F (s,u))).comp (S.projector (F (s,u)))))

end LocalFamilyTransport
end SplitTangent.TangentSplitting

namespace SplitTangent.TangentSplitting.LocalFamilyTransport
section
open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {F : ℂ × ℂ → X.Carrier}
  (L : LocalFamilyTransport S F)

 

lemma map_holomorphic_at (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F)
    {q u v : ℂ → ℂ} {z : ℂ}
    (hq : AnalyticAt ℂ q z) (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z)
    (hqr : ‖q z‖ < L.radius) (hur : ‖u z‖ < L.radius) (hvr : ‖v z‖ < L.radius)
    (σ : ∀ w, Tangent X (F (q w,u w)))
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,u w),σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,v w),L.map (q w) (u w) (v w) (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z := by
  let t := L.frame
  have hs : F (q z,u z) ∈ t.baseSet := L.chart_source _ _ hqr hur
  have ht : F (q z,v z) ∈ t.baseSet := L.chart_source _ _ hqr hvr
  have hp : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,u w),S.projector (F (q w,u w)) (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z :=
    S.holomorphic.contMDiffAt.comp z hσ
  have hc := ((t.contMDiffAt_iff (f := fun w =>
    (⟨F (q w,u w),S.projector (F (q w,u w)) (σ w)⟩ :
      TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using hs)).mp hp).2
  have hT := L.analytic q u v z hq hu hv hqr hur hvr
  have hprod := hT.contDiffAt.contMDiffAt.clm_apply hc
  apply (t.contMDiffAt_iff (f := fun w =>
    (⟨F (q w,v w),L.map (q w) (u w) (v w) (σ w)⟩ :
      TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using ht)).mpr
  have hbase : ContMDiffAt 𝓘(ℂ,ℂ) (ModelWithCorners X) ω (fun w => F (q w,v w)) z :=
    (hF (q z,v z)).comp z (f := fun w => (q w,v w)) (hq.prod hv).contDiffAt.contMDiffAt
  refine ⟨hbase,?_⟩
  apply hprod.congr_of_eventuallyEq
  filter_upwards [hq.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hqr)),
    hu.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hur)),
    hv.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hvr))] with w hqw huw hvw
  have hsu : F (q w,u w) ∈ t.baseSet := L.chart_source _ _
    (mem_ball_zero_iff.mp hqw) (mem_ball_zero_iff.mp huw)
  have hsv : F (q w,v w) ∈ t.baseSet := L.chart_source _ _
    (mem_ball_zero_iff.mp hqw) (mem_ball_zero_iff.mp hvw)
  change (t ⟨F (q w,v w),L.map (q w) (u w) (v w) (σ w)⟩).2 =
    L.trans (q w) (u w) (v w) (t ⟨F (q w,u w),S.projector (F (q w,u w)) (σ w)⟩).2
  rw [← t.continuousLinearMapAt_apply_of_mem ℂ hsv,
    ← t.continuousLinearMapAt_apply_of_mem ℂ hsu]
  exact t.continuousLinearMapAt_symmL hsv _

end

section
open Filter Topology Set
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {F : ℂ × ℂ → X.Carrier}
  (L : LocalFamilyTransport S F)

 

lemma map_projector (s u v : ℂ) :
    (L.map s u v).comp (S.projector (F (s,u))) = L.map s u v := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply,map,S.idempotent]



end

section
open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {F : ℂ × ℂ → X.Carrier}
  (L : LocalFamilyTransport S F)

 

theorem map_eq_of_horizontal_germ
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F)
    {s u : ℂ} (hs : ‖s‖ < L.radius) (hu : ‖u‖ < L.radius)
    (σ : ∀ t, Tangent X (F (s,t)))
    (hσ : AnalyticAt ℂ
      (fun t => L.frame.continuousLinearMapAt ℂ (F (s,t)) (σ t)) u)
    (hfix : ∀ᶠ t in 𝓝 u, S.projector (F (s,t)) (σ t)=σ t)
    (hh : ∀ᶠ t in 𝓝 u,
      covariantDerivative (S.coordinateProjector (F (0,0)))
        (fun v => (chartAt (Model X) (F (0,0))) (F (s,v)))
        (fun v => L.frame.continuousLinearMapAt ℂ (F (s,v)) (σ v)) t=0) :
    (fun t => L.map s u t (σ u)) =ᶠ[𝓝 u] σ := by
  let c := chartAt (Model X) (F (0,0))
  let P := S.coordinateProjector (F (0,0))
  let g : ℂ → Model X := fun t => c (F (s,t))
  let e := L.frame.continuousLinearMapAt ℂ (F (s,u)) (σ u)
  let f : ℂ → Model X := fun t => L.trans s u t e
  let h : ℂ → Model X := fun t => L.frame.continuousLinearMapAt ℂ (F (s,t)) (σ t)
  have hsource : F (s,u) ∈ c.source := L.chart_source s u hs hu
  have hP : AnalyticAt ℂ P (g u) :=
    S.coordinateProjector_analytic (F (0,0)) _ (c.map_source hsource)
  have hg : AnalyticAt ℂ g u := by
    have hc := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) (F (0,0))) hsource
    have hk : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ × ℂ) ω (fun t : ℂ => (s,t)) u :=
      (contDiff_const.prodMk contDiff_id).contDiffAt.contMDiffAt
    exact (hc.comp u ((hF (s,u)).comp u hk)).contDiffAt.analyticAt
  have he : P (g u) e=e := by
    dsimp only [P,g,e,frame]
    rw [S.coordinateProjector_fixed _ hsource,hfix.self_of_nhds]
  have hn : ∀ᶠ t in 𝓝 u, ‖t‖ < L.radius := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hu)] with t ht
    exact mem_ball_zero_iff.mp ht
  have hfa (t : ℂ) (ht : ‖t‖ < L.radius) : AnalyticAt ℂ f t := by
    exact ((ContinuousLinearMap.apply ℂ (Model X) (E := Model X)).analyticAt_bilinear _).comp
      (analyticAt_const.prod (L.analytic (fun _ => s) (fun _ => u) id t analyticAt_const analyticAt_const
        analyticAt_id hs hu ht))
  have hfd : ∀ᶠ t in 𝓝 u, DifferentiableAt ℂ f t ∧ covariantDerivative P g f t=0 := by
    filter_upwards [hn] with t ht
    exact ⟨(hfa t ht).differentiableAt,(L.horizontal s u t hs hu ht e he).2⟩
  have hhd : ∀ᶠ t in 𝓝 u, DifferentiableAt ℂ h t ∧ covariantDerivative P g h t=0 := by
    filter_upwards [hσ.eventually_analyticAt,hh] with t ht hht
    exact ⟨ht.differentiableAt,hht⟩
  have hfi : ∀ᶠ t in 𝓝 u, P (g t) (f t)=f t := by
    filter_upwards [hn] with t ht
    exact (L.horizontal s u t hs hu ht e he).1
  have hhi : ∀ᶠ t in 𝓝 u, P (g t) (h t)=h t := by
    filter_upwards [hn,hfix] with t ht hft
    dsimp only [P,g,h,frame]
    rw [S.coordinateProjector_fixed _ (L.chart_source s t hs ht),hft]
  have hinit : f u=h u := by
    dsimp only [f,h,e]
    rw [L.normalized s u hs hu]
    rfl
  have heq := horizontal_local_uniqueness hP hg
    (S.coordinateProjector_eventually_idempotent (F (0,0)) (c.map_source hsource))
    hfd hhd hfi hhi hinit
  filter_upwards [heq,hn] with t ht htn
  change L.frame.symmL ℂ (F (s,t))
    (L.trans s u t (L.frame.continuousLinearMapAt ℂ (F (s,u))
      (S.projector (F (s,u)) (σ u))))=σ t
  rw [hfix.self_of_nhds]
  change L.frame.symmL ℂ (F (s,t)) (f t)=σ t
  rw [ht]
  exact L.frame.symmL_continuousLinearMapAt (L.chart_source s t hs htn) _

end

open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {F : ℂ × ℂ → X.Carrier}
  (L : LocalFamilyTransport S F)

 

theorem map_eq_on_ball_of_horizontal_germ
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F)
    {s u : ℂ} (hs : ‖s‖ < L.radius) (hu : ‖u‖ < L.radius)
    (σ : ∀ t, Tangent X (F (s,t)))
    (hσ : AnalyticOnNhd ℂ
      (fun t => L.frame.continuousLinearMapAt ℂ (F (s,t)) (σ t)) (Metric.ball 0 L.radius))
    (hfix : ∀ᶠ t in 𝓝 u, S.projector (F (s,t)) (σ t)=σ t)
    (hh : ∀ᶠ t in 𝓝 u,
      covariantDerivative (S.coordinateProjector (F (0,0)))
        (fun v => (chartAt (Model X) (F (0,0))) (F (s,v)))
        (fun v => L.frame.continuousLinearMapAt ℂ (F (s,v)) (σ v)) t=0) :
    ∀ t, ‖t‖ < L.radius → L.map s u t (σ u)=σ t := by
  let e := L.frame.continuousLinearMapAt ℂ (F (s,u)) (σ u)
  let f : ℂ → Model X := fun t => L.trans s u t e
  let h : ℂ → Model X := fun t => L.frame.continuousLinearMapAt ℂ (F (s,t)) (σ t)
  have he (t : ℂ) (ht : ‖t‖ < L.radius) :
      L.frame.continuousLinearMapAt ℂ (F (s,t)) (L.map s u t (σ u)) = f t := by
    change L.frame.continuousLinearMapAt ℂ (F (s,t))
      (L.frame.symmL ℂ (F (s,t)) (L.trans s u t
        (L.frame.continuousLinearMapAt ℂ (F (s,u)) (S.projector (F (s,u)) (σ u)))))=f t
    rw [hfix.self_of_nhds]
    exact L.frame.continuousLinearMapAt_symmL (L.chart_source s t hs ht) _
  have hf : AnalyticOnNhd ℂ f (Metric.ball 0 L.radius) := by
    intro t ht
    exact ((ContinuousLinearMap.apply ℂ (Model X) (E := Model X)).analyticAt_bilinear _).comp
      (analyticAt_const.prod (L.analytic (fun _ => s) (fun _ => u) id t analyticAt_const analyticAt_const
        analyticAt_id hs hu (mem_ball_zero_iff.mp ht)))
  have hgerm := L.map_eq_of_horizontal_germ hF hs hu σ
    (hσ u (mem_ball_zero_iff.mpr hu)) hfix hh
  have hfg : f =ᶠ[𝓝 u] h := by
    filter_upwards [hgerm,Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hu)] with t ht htr
    exact (he t (mem_ball_zero_iff.mp htr)).symm.trans
      (congrArg (L.frame.continuousLinearMapAt ℂ (F (s,t))) ht)
  have hall := hf.eqOn_of_preconnected_of_eventuallyEq hσ
    (convex_ball (0 : ℂ) L.radius).isPreconnected (mem_ball_zero_iff.mpr hu) hfg
  intro t ht
  have heq := (he t ht).trans (hall (mem_ball_zero_iff.mpr ht))
  have h := congrArg (L.frame.symmL ℂ (F (s,t))) heq
  rw [L.frame.symmL_continuousLinearMapAt (L.chart_source s t hs ht),
    L.frame.symmL_continuousLinearMapAt (L.chart_source s t hs ht)] at h
  exact h

end SplitTangent.TangentSplitting.LocalFamilyTransport

namespace SplitTangent.TangentSplitting
open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

lemma coordinate_covariantDerivative_change {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ)) = 0)
    (σ : ∀ z, Tangent X (g z)) (x y : X.Carrier) {z : ℂ}
    (hx : g z ∈ (chartAt (Model X) x).source)
    (hy : g z ∈ (chartAt (Model X) y).source)
    (hσ : AnalyticAt ℂ (fun w =>
      (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (g w) (σ w)) z) :
    covariantDerivative (S.coordinateProjector y) ((chartAt (Model X) y) ∘ g)
      (fun w => (trivializationAt (Model X) (Tangent X) y).continuousLinearMapAt ℂ (g w) (σ w)) z =
    fderiv ℂ (coordinateTransition x y) ((chartAt (Model X) x) (g z))
      (covariantDerivative (S.coordinateProjector x) ((chartAt (Model X) x) ∘ g)
        (fun w => (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (g w) (σ w)) z) := by
  let c := chartAt (Model X) x
  let d := chartAt (Model X) y
  let φ := coordinateTransition x y
  let P := S.coordinateProjector x
  let Q := S.coordinateProjector y
  let f := fun w => (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (g w) (σ w)
  let h := fun w => (trivializationAt (Model X) (Tangent X) y).continuousLinearMapAt ℂ (g w) (σ w)
  have he : c.symm (c (g z)) = g z := c.left_inv hx
  have hφ : φ (c (g z)) = d (g z) := by
    change d (c.symm (c (g z))) = d (g z)
    rw [he]
  have hnat : ∀ᶠ a in 𝓝 (c (g z)), ∀ v : Model X,
      Q (φ a) (fderiv ℂ φ a v) = fderiv ℂ φ a (P a v) := by
    have hcn : ContinuousAt c.symm (c (g z)) := c.continuousAt_symm (c.map_source hx)
    have hn : ∀ᶠ a in 𝓝 (c (g z)), c.symm a ∈ d.source :=
      hcn (d.open_source.mem_nhds (by rw [he]; exact hy))
    filter_upwards [c.open_target.mem_nhds (c.map_source hx),hn] with a ha ha'
    intro v
    exact (congrArg (fun A : Model X →L[ℂ] Model X => A v)
      (S.coordinateProjector_intertwining x y ha ha')).symm
  have hnA : ∀ᶠ w in 𝓝 z, g w ∈ c.source := (hg z).continuousAt (c.open_source.mem_nhds hx)
  have hnB : ∀ᶠ w in 𝓝 z, g w ∈ d.source := (hg z).continuousAt (d.open_source.mem_nhds hy)
  have hcurve : φ ∘ (c ∘ g) =ᶠ[𝓝 z] d ∘ g := by
    filter_upwards [hnA] with w hw
    change d (c.symm (c (g w))) = d (g w)
    rw [c.left_inv hw]
  have hsection : (fun w => fderiv ℂ φ ((c ∘ g) w) (f w)) =ᶠ[𝓝 z] h := by
    filter_upwards [hnA,hnB] with w hw hw'
    have hei : c.symm (c (g w)) = g w := c.left_inv hw
    have hd := coordinateTransition_derivative x y (c.map_source hw) (by rw [hei]; exact hw')
    rw [hei] at hd
    change fderiv ℂ (coordinateTransition x y) (c (g w)) (f w) = h w
    rw [hd]
    dsimp only [ContinuousLinearMap.comp_apply,f,h]
    rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hw]
  have hq : DifferentiableAt ℂ Q (φ ((c ∘ g) z)) := by
    rw [show (c ∘ g) z = c (g z) from rfl,hφ]
    exact (S.coordinateProjector_analytic y _ (d.map_source hy)).differentiableAt
  have hid : ∀ w : Model X, Q (φ ((c ∘ g) z)) (Q (φ ((c ∘ g) z)) w) = Q (φ ((c ∘ g) z)) w := by
    rw [show (c ∘ g) z = c (g z) from rfl,hφ]
    exact S.coordinateProjector_idempotent y (d.map_source hy)
  have hn := covariantDerivative_naturality
    (S.coordinateProjector_analytic x _ (c.map_source hx)).differentiableAt hq
    (coordinateTransition_analytic x y (c.map_source hx) (by
      change c.symm (c (g z)) ∈ d.source
      rw [he]; exact hy))
    (coordinateCurve_analytic hg x hx).differentiableAt hσ.differentiableAt hnat
    (S.coordinateCurve_complementary hg hv x hx) hid
  rw [covariantDerivative_curve_congr hcurve,covariantDerivative_congr hsection] at hn
  exact hn

end SplitTangent.TangentSplitting

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

namespace SplitTangent.TangentSplitting.LocalChartImages
open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : ℂ → X.Carrier}
  (L : LocalChartImages S g)
  (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
  (hv : ∀ z, S.projector (g z) (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)

 

lemma continuationMap_horizontal (a z : ℂ) (v : Tangent X (g a)) (x : X.Carrier)
    (hx : g z ∈ (chartAt (Model X) x).source) :
    covariantDerivative (S.coordinateProjector x) ((chartAt (Model X) x) ∘ g)
      (fun w => (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (g w)
        (L.continuationMap hg hv a w v)) z = 0 := by
  let v₀ : TangentImageFiber S g a := ⟨S.projector (g a) v,S.idempotent _ v⟩
  let v₁ := L.continuation hg hv a z v₀
  let σ := fun w => L.continuationMap hg hv a w v
  let f := fun w => L.coords z w (σ w)
  let h := fun w => L.trans z z w (L.coords z z v₁)
  have hfe : f =ᶠ[𝓝 z] h := by
    filter_upwards [L.continuation_germ hg hv a z v₀,
      Metric.ball_mem_nhds z (L.positive z)] with w hw hw'
    dsimp only [f,σ]
    rw [L.continuationMap_apply]
    change L.coords z w (L.continuation hg hv a w v₀).1 = h w
    rw [hw,L.forward_val hw',L.coords_uncoords hw']
  have hfa : AnalyticAt ℂ f z :=
    (L.trans_analytic (L.center z) (L.center z) (L.coords z z v₁)).congr hfe.symm
  have hh : covariantDerivative (S.coordinateProjector (g z)) ((chartAt (Model X) (g z)) ∘ g) f z = 0 := by
    rw [covariantDerivative_congr hfe]
    exact (L.horizontal z z (L.center z) z (L.center z) _ (L.coords_fixed (L.center z) v₁)).2
  have he := S.coordinate_covariantDerivative_change hg hv σ (g z) x
    (L.chart_source z z (L.center z)) hx hfa
  rw [hh,map_zero] at he
  exact he

 

lemma continuationMap_coordinates_analytic (a z : ℂ) (v : Tangent X (g a)) (x : X.Carrier)
    (hx : g z ∈ (chartAt (Model X) x).source) :
    AnalyticAt ℂ (fun w =>
      (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ (g w)
        (L.continuationMap hg hv a w v)) z := by
  let t := trivializationAt (Model X) (Tangent X) x
  have hc := ((t.contMDiffAt_iff (f := fun w =>
    (⟨g w,L.continuationMap hg hv a w v⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
    (t.mem_source.mpr (show g z ∈ t.baseSet from hx))).mp (L.continuationMap_holomorphic hg hv a v z)).2
  apply hc.contDiffAt.analyticAt.congr
  filter_upwards [(hg z).continuousAt ((chartAt (Model X) x).open_source.mem_nhds hx)] with w hw
  exact (t.continuousLinearMapAt_apply_of_mem ℂ hw _).symm

end SplitTangent.TangentSplitting.LocalChartImages

namespace SplitTangent.TangentSplitting
open Filter Topology Set PullbackConnection
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {F : ℂ × ℂ → X.Carrier}

lemma family_slice_holomorphic
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F) (s : ℂ) :
    ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω (fun t => F (s,t)) :=
  hF.comp (contDiff_const.prodMk contDiff_id).contMDiff

abbrev shiftedFamily (F : ℂ × ℂ → X.Carrier) (s₀ t₀ : ℂ) : ℂ × ℂ → X.Carrier :=
  fun p => F (s₀+p.1,t₀+p.2)

lemma shiftedFamily_holomorphic
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F) (s₀ t₀ : ℂ) :
    ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω (shiftedFamily F s₀ t₀) :=
  hF.comp ((contDiff_const.add contDiff_fst).prodMk (contDiff_const.add contDiff_snd)).contMDiff

variable (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F)
  (hvel : ∀ s t, S.projector (F (s,t))
    (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) (fun z => F (s,z)) t (1 : ℂ))=0)
  (K : ∀ s, LocalChartImages S (fun t => F (s,t)))

 

abbrev familyContinuation (s a b : ℂ) : Tangent X (F (s,a)) →L[ℂ] Tangent X (F (s,b)) :=
  (K s).continuationMap (family_slice_holomorphic hF s) (hvel s) a b

namespace LocalFamilyTransport
lemma map_eq_familyContinuation_shift (s₀ t₀ : ℂ)
    (L : LocalFamilyTransport S (shiftedFamily F s₀ t₀)) (s u v : ℂ)
    (hs : ‖s‖ < L.radius) (hu : ‖u‖ < L.radius) (hv : ‖v‖ < L.radius) :
    L.map s u v = familyContinuation hF hvel K (s₀+s) (t₀+u) (t₀+v) := by
  apply ContinuousLinearMap.ext
  intro e
  let k : ℂ → ℂ := fun t => t₀+t
  let σ := fun t => familyContinuation hF hvel K (s₀+s) (t₀+u) (k t) e
  have hsrc (t : ℂ) (ht : ‖t‖ < L.radius) :
      F (s₀+s,k t) ∈ (chartAt (Model X) (shiftedFamily F s₀ t₀ (0,0))).source := by
    simpa only [shiftedFamily,σ,familyContinuation,k,frame] using L.chart_source s t hs ht
  have hσ : AnalyticOnNhd ℂ (fun t => L.frame.continuousLinearMapAt ℂ
      (shiftedFamily F s₀ t₀ (s,t)) (σ t)) (Metric.ball 0 L.radius) := by
    intro t ht
    have hc := ((K (s₀+s)).continuationMap_coordinates_analytic (family_slice_holomorphic hF (s₀+s))
      (hvel (s₀+s)) (t₀+u) (k t) e (shiftedFamily F s₀ t₀ (0,0))
      (hsrc t (mem_ball_zero_iff.mp ht))).comp (analyticAt_const.add analyticAt_id)
    simpa only [shiftedFamily,σ,familyContinuation,k,frame,Function.comp_def] using hc
  have hfix : ∀ᶠ t in 𝓝 u,
      S.projector (shiftedFamily F s₀ t₀ (s,t)) (σ t) = σ t := by
    filter_upwards [] with t
    simpa only [shiftedFamily,σ,familyContinuation,k,frame] using
      (K (s₀+s)).continuationMap_fixed (family_slice_holomorphic hF (s₀+s)) (hvel (s₀+s)) (t₀+u) (k t) e
  have hn : ∀ᶠ t in 𝓝 u, ‖t‖ < L.radius := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hu)] with t ht
    exact mem_ball_zero_iff.mp ht
  have hh : ∀ᶠ t in 𝓝 u,
      covariantDerivative (S.coordinateProjector (shiftedFamily F s₀ t₀ (0,0)))
        (fun z => (chartAt (Model X) (shiftedFamily F s₀ t₀ (0,0)))
          (shiftedFamily F s₀ t₀ (s,z)))
        (fun z => L.frame.continuousLinearMapAt ℂ (shiftedFamily F s₀ t₀ (s,z)) (σ z)) t=0 := by
    filter_upwards [hn] with t ht
    let x := shiftedFamily F s₀ t₀ (0,0)
    have hc := (K (s₀+s)).continuationMap_coordinates_analytic (family_slice_holomorphic hF (s₀+s))
      (hvel (s₀+s)) (t₀+u) (k t) e x (hsrc t ht)
    have hg := coordinateCurve_analytic (family_slice_holomorphic hF (s₀+s)) x (hsrc t ht)
    have he := covariantDerivative_reparam (P := S.coordinateProjector x)
      hg.differentiableAt hc.differentiableAt ((analyticAt_const.add analyticAt_id).differentiableAt)
    rw [(K (s₀+s)).continuationMap_horizontal (family_slice_holomorphic hF (s₀+s)) (hvel (s₀+s))
      (t₀+u) (k t) e x (hsrc t ht),smul_zero] at he
    simpa only [shiftedFamily,σ,familyContinuation,k,frame,Function.comp_def,x] using he
  have he := L.map_eq_on_ball_of_horizontal_germ (shiftedFamily_holomorphic hF s₀ t₀)
    hs hu σ hσ hfix hh v hv
  have hinit : σ u = S.projector (F (s₀+s,t₀+u)) e := by
    change (K (s₀+s)).continuationMap _ _ (t₀+u) (t₀+u) e = _
    rw [(K (s₀+s)).continuationMap_self]
  rw [hinit] at he
  have hp := congrArg (fun A : Tangent X (F (s₀+s,t₀+u)) →L[ℂ] Tangent X (F (s₀+s,t₀+v)) => A e)
    (L.map_projector s u v)
  simp only [shiftedFamily,ContinuousLinearMap.comp_apply] at hp
  simpa only [σ,familyContinuation,k] using hp.symm.trans he

lemma familyContinuation_holomorphic_at_local (s₀ t₀ : ℂ)
    (L : LocalFamilyTransport S (shiftedFamily F s₀ t₀))
    {q u v : ℂ → ℂ} {z : ℂ}
    (hq : AnalyticAt ℂ q z) (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z)
    (hqr : ‖q z-s₀‖ < L.radius) (hur : ‖u z-t₀‖ < L.radius)
    (hvr : ‖v z-t₀‖ < L.radius)
    (σ : ∀ w, Tangent X (F (q w,u w)))
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,u w),σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,v w),familyContinuation hF hvel K (q w) (u w) (v w) (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z := by
  have hadd (a b : ℂ) : a+(b-a)=b := by ring
  let q' := fun w => q w-s₀
  let u' := fun w => u w-t₀
  let v' := fun w => v w-t₀
  have hσ' : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨shiftedFamily F s₀ t₀ (q' w,u' w),σ w⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z := by
    convert hσ using 1
    funext w
    dsimp only [shiftedFamily,q',u']
    erw [hadd,hadd]
  have h := L.map_holomorphic_at (shiftedFamily_holomorphic hF s₀ t₀)
    (hq.sub analyticAt_const) (hu.sub analyticAt_const) (hv.sub analyticAt_const)
    hqr hur hvr (fun w => σ w) hσ'
  have hqr' : ∀ᶠ w in 𝓝 z, ‖q' w‖ < L.radius :=
    (hq.sub analyticAt_const).continuousAt.norm.eventually (gt_mem_nhds hqr)
  have hur' : ∀ᶠ w in 𝓝 z, ‖u' w‖ < L.radius :=
    (hu.sub analyticAt_const).continuousAt.norm.eventually (gt_mem_nhds hur)
  have hvr' : ∀ᶠ w in 𝓝 z, ‖v' w‖ < L.radius :=
    (hv.sub analyticAt_const).continuousAt.norm.eventually (gt_mem_nhds hvr)
  apply h.congr_of_eventuallyEq
  filter_upwards [hqr',hur',hvr'] with w hwq hwu hwv
  dsimp only [Pi.sub_apply]
  erw [L.map_eq_familyContinuation_shift hF hvel K s₀ t₀ (q' w) (u' w) (v' w) hwq hwu hwv]
  dsimp only [shiftedFamily,q',u',v']
  erw [hadd,hadd,hadd]
  rfl

end LocalFamilyTransport

lemma familyContinuation_cocycle (s a b c : ℂ) (e : Tangent X (F (s,a))) :
    familyContinuation hF hvel K s b c (familyContinuation hF hvel K s a b e) =
      familyContinuation hF hvel K s a c e :=
  (K s).continuationMap_cocycle (family_slice_holomorphic hF s) (hvel s) a b c e

 

lemma familyContinuation_holomorphic_at_const_end
    {q u : ℂ → ℂ} {z : ℂ} (hq : AnalyticAt ℂ q z) (hu : AnalyticAt ℂ u z)
    (σ : ∀ w, Tangent X (F (q w,u w)))
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,u w),σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z)
    (b : ℂ) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,b),familyContinuation hF hvel K (q w) (u w) b (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z := by
  let Good : Set ℂ := {b | ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,b),familyContinuation hF hvel K (q w) (u w) b (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z}
  have spread (b : ℂ) : ∃ r : ℝ, 0 < r ∧ ∀ b₁ ∈ Metric.ball b r,
      ∀ b₂ ∈ Metric.ball b r, b₁ ∈ Good → b₂ ∈ Good := by
    obtain ⟨L⟩ := S.exists_local_family_transport (shiftedFamily_holomorphic hF (q z) b)
    refine ⟨L.radius,L.positive,?_⟩
    intro b₁ hb₁ b₂ hb₂ h₁
    have hq0 : ‖q z-q z‖ < L.radius := by simpa only [sub_self,norm_zero] using L.positive
    have h₁' : ‖b₁-b‖ < L.radius := by simpa only [Metric.mem_ball,dist_eq_norm] using hb₁
    have h₂' : ‖b₂-b‖ < L.radius := by simpa only [Metric.mem_ball,dist_eq_norm] using hb₂
    have ht := L.familyContinuation_holomorphic_at_local hF hvel K (q z) b
      hq analyticAt_const analyticAt_const hq0 h₁' h₂'
      (fun w => familyContinuation hF hvel K (q w) (u w) b₁ (σ w)) h₁
    change ContMDiffAt _ _ _ _ _
    apply ht.congr_of_eventuallyEq
    filter_upwards [] with w
    rw [familyContinuation_cocycle]
  have hg : Good.Nonempty := by
    obtain ⟨L⟩ := S.exists_local_family_transport (shiftedFamily_holomorphic hF (q z) (u z))
    have hq0 : ‖q z-q z‖ < L.radius := by simpa only [sub_self,norm_zero] using L.positive
    have hu0 : ‖u z-u z‖ < L.radius := by simpa only [sub_self,norm_zero] using L.positive
    exact ⟨u z,L.familyContinuation_holomorphic_at_local hF hvel K (q z) (u z)
      hq hu analyticAt_const hq0 hu0 hu0 σ hσ⟩
  have ho : IsOpen Good := isOpen_iff_mem_nhds.mpr fun b hb => by
    obtain ⟨r,hr,hs⟩ := spread b
    apply Filter.mem_of_superset (Metric.ball_mem_nhds b hr)
    intro b' hb'
    exact hs b (Metric.mem_ball_self hr) b' hb' hb
  have hc : IsOpen Goodᶜ := isOpen_iff_mem_nhds.mpr fun b hb => by
    obtain ⟨r,hr,hs⟩ := spread b
    apply Filter.mem_of_superset (Metric.ball_mem_nhds b hr)
    intro b' hb' hgood
    exact hb (hs b' hb' b (Metric.mem_ball_self hr) hgood)
  have he : Good = Set.univ := IsClopen.eq_univ (⟨isOpen_compl_iff.mp hc,ho⟩ : IsClopen Good) hg
  have hb : b ∈ Good := by rw [he]; trivial
  exact hb

 

theorem familyContinuation_holomorphic_at
    {q u v : ℂ → ℂ} {z : ℂ}
    (hq : AnalyticAt ℂ q z) (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z)
    (σ : ∀ w, Tangent X (F (q w,u w)))
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,u w),σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,v w),familyContinuation hF hvel K (q w) (u w) (v w) (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z := by
  obtain ⟨L⟩ := S.exists_local_family_transport (shiftedFamily_holomorphic hF (q z) (v z))
  have hq0 : ‖q z-q z‖ < L.radius := by simpa only [sub_self,norm_zero] using L.positive
  have hv0 : ‖v z-v z‖ < L.radius := by simpa only [sub_self,norm_zero] using L.positive
  have ht := L.familyContinuation_holomorphic_at_local hF hvel K (q z) (v z)
    hq analyticAt_const hv hq0 hv0 hv0
    (fun w => familyContinuation hF hvel K (q w) (u w) (v z) (σ w))
    (familyContinuation_holomorphic_at_const_end hF hvel K hq hu σ hσ (v z))
  apply ht.congr_of_eventuallyEq
  filter_upwards [] with w
  rw [familyContinuation_cocycle]

end SplitTangent.TangentSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.BoxFirstTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Box First Transport. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle
universe u

namespace SplitTangent.TangentSplitting
open Filter Topology Set
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

def canonicalChartImages {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) : LocalChartImages S g :=
  Classical.choice (S.exists_local_chart_images hg)

def entireMap {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
    (a b : ℂ) : Tangent X (g a) →L[ℂ] Tangent X (g b) :=
  (S.canonicalChartImages hg).continuationMap hg hv a b

lemma entireMap_congr {g h : ℂ → X.Carrier} (he : g=h)
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hh : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω h)
    (hvg : ∀ z, S.projector (g z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
    (hvh : ∀ z, S.projector (h z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) h z (1 : ℂ))=0)
    (a b : ℂ) : S.entireMap hg hvg a b=S.entireMap hh hvh a b := by
  subst h
  rfl

lemma entireMap_family_holomorphic_at {F : ℂ × ℂ → X.Carrier}
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F)
    (hvel : ∀ s t, S.projector (F (s,t))
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) (fun w => F (s,w)) t (1 : ℂ))=0)
    {q u v : ℂ → ℂ} {z : ℂ}
    (hq : AnalyticAt ℂ q z) (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z)
    (σ : ∀ w, Tangent X (F (q w,u w)))
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,u w),σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,v w),S.entireMap (family_slice_holomorphic hF (q w))
        (hvel (q w)) (u w) (v w) (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z :=
  familyContinuation_holomorphic_at hF hvel
    (fun s => S.canonicalChartImages (family_slice_holomorphic hF s)) hq hu hv σ hσ

end SplitTangent.TangentSplitting

namespace SplitTangent.TangentBox
open Filter Topology Set TangentSplitting
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : RationalCurve X}
  (F : TangentBox S g)

lemma vertical_holomorphic (a b : Bool) (s : ℂ) :
    ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω (fun t => F.chart a b (s,t)) :=
  family_slice_holomorphic (F.holomorphic a b) s

lemma vertical_tangent (a b : Bool) (s t : ℂ) :
    S.projector (F.chart a b (s,t))
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) (fun w => F.chart a b (s,w)) t (1 : ℂ))=0 := by
  have hd : HasFDerivAt (fun w : ℂ => (s,w))
      ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)) t :=
    (hasFDerivAt_const s t).prodMk (hasFDerivAt_id t)
  have hm : MDifferentiableAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ × ℂ) (fun w : ℂ => (s,w)) t :=
    hd.differentiableAt.mdifferentiableAt
  have hchain := mfderiv_comp t ((F.holomorphic a b (s,t)).mdifferentiableAt (by simp)) hm
  change S.projector _ ((mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X)
    ((F.chart a b) ∘ (fun w : ℂ => (s,w))) t) (1 : ℂ))=0
  rw [hchain,mfderiv_eq_fderiv,hd.fderiv]
  exact (F.tangency a b (s,t)).2

def vertical (a : Bool) (s : ℂ) : RationalCurve X where
  finite t := F.chart a false (s,t)
  infinity t := F.chart a true (s,t)
  finite_holomorphic := F.vertical_holomorphic a false s
  infinity_holomorphic := F.vertical_holomorphic a true s
  overlap t ht := by
    have h := F.overlap a false a true (s,t) ⟨by simp,fun _ => ht⟩
    cases a <;> simpa [ReciprocalCharts.changeChart,ReciprocalCharts.coord] using h

def chartTransport (a b : Bool) (s u v : ℂ) :
    Tangent X (F.chart a b (s,u)) →L[ℂ] Tangent X (F.chart a b (s,v)) :=
  S.entireMap (F.vertical_holomorphic a b s) (F.vertical_tangent a b s) u v

lemma chartTransport_horizontal_overlap (d : Bool) {s : ℂ} (hs : s≠0) (u v : ℂ) :
    F.chartTransport false d s u v = F.chartTransport true d s⁻¹ u v := by
  apply S.entireMap_congr
  funext t
  have h := F.overlap false d true d (s,t) ⟨fun _ => hs,by simp⟩
  cases d <;> simpa [ReciprocalCharts.changeChart,ReciprocalCharts.coord] using h

lemma chartTransport_vertical_overlap (d : Bool) (s a : ℂ) {z : ℂ} (hz : z≠0)
    (v : Tangent X (F.chart d false (s,z))) :
    F.chartTransport d false s z a v =
      F.chartTransport d false s 1 a (F.chartTransport d true s z⁻¹ 1 v) :=
  S.rational_reverse_overlap (F.vertical d s)
    (S.canonicalChartImages (F.vertical_holomorphic d false s))
    (S.canonicalChartImages (F.vertical_holomorphic d true s))
    (F.vertical_tangent d false s) (F.vertical_tangent d true s) a hz v

lemma chartTransport_holomorphic_at (a b : Bool) {q u v : ℂ → ℂ} {z : ℂ}
    (hq : AnalyticAt ℂ q z) (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z)
    (σ : ∀ w, Tangent X (F.chart a b (q w,u w)))
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F.chart a b (q w,u w),σ w⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F.chart a b (q w,v w),F.chartTransport a b (q w) (u w) (v w) (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z :=
  S.entireMap_family_holomorphic_at (F.holomorphic a b) (F.vertical_tangent a b) hq hu hv σ hσ

lemma vertical_one (a : Bool) (s : ℂ) : F.chart a true (s,1)=F.chart a false (s,1) := by
  have he := F.overlap a true a false (s,1) ⟨by simp,fun _ => one_ne_zero⟩
  cases a <;> simpa [ReciprocalCharts.changeChart,ReciprocalCharts.coord] using he

lemma section_holomorphic_congr_base {f h : ℂ → X.Carrier} (he : ∀ w, f w=h w)
    (σ : ∀ w, Tangent X (f w)) {z : ℂ}
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨f w,σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨h w,σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z := by
  apply hσ.congr_of_eventuallyEq
  filter_upwards [] with w
  erw [he w]

 

def firstMap (b : ℂ) : CurveBundleMap g (F.firstFactor b) where
  finite z := F.chartTransport false false z z b
  infinity z := (F.chartTransport true false z 1 b).comp (F.chartTransport true true z z 1)
  overlap z hz := by
    apply ContinuousLinearMap.ext
    intro v
    change F.chartTransport false false z z b v =
      F.chartTransport true false z⁻¹ 1 b (F.chartTransport true true z⁻¹ z⁻¹ 1 v)
    rw [F.chartTransport_vertical_overlap false z b hz v]
    erw [F.chartTransport_horizontal_overlap false hz 1 b,
      F.chartTransport_horizontal_overlap true hz z⁻¹ 1]
    rfl
  finite_holomorphic U hU v hv z hz := by
    have h₀ := section_holomorphic_congr_base (fun w => (F.finite_diagonal w).symm) v
      ((hv z hz).contMDiffAt (hU.mem_nhds hz))
    exact (F.chartTransport_holomorphic_at false false analyticAt_id analyticAt_id
      analyticAt_const v h₀).contMDiffWithinAt
  infinity_holomorphic U hU v hv z hz := by
    have h₀ := section_holomorphic_congr_base (fun w => (F.infinity_diagonal w).symm) v
      ((hv z hz).contMDiffAt (hU.mem_nhds hz))
    have h₁ := F.chartTransport_holomorphic_at true true analyticAt_id analyticAt_id
      analyticAt_const v h₀ (v := fun _ => (1 : ℂ))
    have h₂ := section_holomorphic_congr_base (F.vertical_one true)
      (fun w => F.chartTransport true true w w 1 (v w)) h₁
    exact (F.chartTransport_holomorphic_at true false analyticAt_id analyticAt_const
      analyticAt_const (fun w => F.chartTransport true true w w 1 (v w)) h₂).contMDiffWithinAt

end SplitTangent.TangentBox

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.FormalBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Formal Boxes. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology
universe u
open Set Filter Topology

namespace SplitTangent.TangentSplitting
section
open HolomorphicJets
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem coordinateMatrix_intertwining (x y : X.Carrier) {z : Model X}
    (hz : z ∈ (chartAt (Model X) x).target)
    (hzy : (chartAt (Model X) x).symm z ∈ (chartAt (Model X) y).source)
    (i j : Fin X.dim) :
    ∑ k, coordinatePartial (fun w => coordinateTransition x y w i) k z *
      S.coordinateMatrix x k j z =
    ∑ k, S.coordinateMatrix y i k (coordinateTransition x y z) *
      coordinatePartial (fun w => coordinateTransition x y w k) j z := by
  have hD := (coordinateTransition_analytic x y hz hzy).differentiableAt
  have he := congrArg (fun L : Model X →L[ℂ] Model X => LinearMap.toMatrix' L.toLinearMap)
    (S.coordinateProjector_intertwining x y hz hzy)
  change LinearMap.toMatrix' ((fderiv ℂ (coordinateTransition x y) z).toLinearMap.comp
    (S.coordinateProjector x z).toLinearMap) =
    LinearMap.toMatrix' ((S.coordinateProjector y (coordinateTransition x y z)).toLinearMap.comp
      (fderiv ℂ (coordinateTransition x y) z).toLinearMap) at he
  rw [LinearMap.toMatrix'_comp,LinearMap.toMatrix'_comp] at he
  have hj (i j : Fin X.dim) :
      coordinatePartial (fun w => coordinateTransition x y w i) j z =
        LinearMap.toMatrix' (fderiv ℂ (coordinateTransition x y) z).toLinearMap i j := by
    rw [coordinatePartial, fderiv_apply hD]
    rfl
  simpa only [Matrix.mul_apply,← hj,coordinateMatrix] using congrFun (congrFun he i) j



theorem localJet_target_glue {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x y : X.Carrier)
    (n : ℕ) {u : ℂ} (hx : u ∈ coordinateDomain g x) (hy : u ∈ coordinateDomain g y) :
    composeJet (coordinateTransition x y) (fun k => S.localJet hg x k u) n =
      S.localJet hg y n u := by
  let U := coordinateDomain g x ∩ coordinateDomain g y
  have hU : IsOpen U := (coordinateDomain_open hg x).inter (coordinateDomain_open hg y)
  have hgxy : Set.EqOn (coordinateCurve g y)
      (coordinateTransition x y ∘ coordinateCurve g x) U := by
    intro u hu
    change (chartAt (Model X) y) (g u) =
      (chartAt (Model X) y) ((chartAt (Model X) x).symm ((chartAt (Model X) x) (g u)))
    rw [(chartAt (Model X) x).left_inv hu.1]
  have htarget (u : ℂ) (hu : u ∈ U) :
      coordinateTransition x y (coordinateCurve g x u) = coordinateCurve g y u :=
    (hgxy hu).symm
  have hH : ∀ u ∈ U, AnalyticAt ℂ (coordinateTransition x y) (coordinateCurve g x u) := by
    intro u hu
    apply coordinateTransition_analytic x y ((chartAt (Model X) x).map_source hu.1)
    simpa only [coordinateCurve,Function.comp_apply,(chartAt (Model X) x).left_inv hu.1]
      using (show g u ∈ (chartAt (Model X) y).source from hu.2)
  have hP : ∀ i j u, u ∈ U → AnalyticAt ℂ (S.coordinateMatrix x i j) (coordinateCurve g x u) := by
    intro i j u hu
    exact S.coordinateMatrix_analytic x i j _ ((chartAt (Model X) x).map_source hu.1)
  have hQ : ∀ i j u, u ∈ U → AnalyticAt ℂ (S.coordinateMatrix y i j)
      (coordinateTransition x y (coordinateCurve g x u)) := by
    intro i j u hu
    rw [htarget u hu]
    exact S.coordinateMatrix_analytic y i j _ ((chartAt (Model X) y).map_source hu.2)
  apply cauchyOn_target_glue hU ((S.localJet_solution hg x).mono Set.inter_subset_left)
    (coordinateTransition x y) (S.coordinateMatrix y)
    (((S.localJet_solution hg y).mono Set.inter_subset_right).congr_initial hgxy)
    hH hP hQ ?_ n u ⟨hx,hy⟩
  intro u hu i j
  have hcx := (chartAt (Model X) x).map_source hu.1
  have hcy : (chartAt (Model X) x).symm (coordinateCurve g x u) ∈
      (chartAt (Model X) y).source := by
    simpa only [coordinateCurve,Function.comp_apply,(chartAt (Model X) x).left_inv hu.1] using (show g u ∈ (chartAt (Model X) y).source from hu.2)
  have hnear := ((chartAt (Model X) x).symm.continuousAt hcx).preimage_mem_nhds
    ((chartAt (Model X) y).open_source.mem_nhds hcy)
  filter_upwards [(chartAt (Model X) x).open_target.mem_nhds hcx,hnear] with z hz hzy
  exact S.coordinateMatrix_intertwining x y hz hzy i j

end

section
open HolomorphicJets PowerSeries
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

theorem scalarCoordinate_analytic {h : X.Carrier → ℂ} {x a : X.Carrier}
    (ha : a ∈ (chartAt (Model X) x).source)
    (hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h a) :
    AnalyticAt ℂ (scalarCoordinate h x) ((chartAt (Model X) x) a) := by
  have ht := (chartAt (Model X) x).map_source ha
  have hc := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) ht
  have hh' : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h
      ((chartAt (Model X) x).symm ((chartAt (Model X) x) a)) := by
    rw [(chartAt (Model X) x).left_inv ha]
    exact hh
  exact (hh'.comp _ hc).contDiffAt.analyticAt

 

theorem localJet_scalar_glue {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (h : X.Carrier → ℂ) (x y : X.Carrier) {u : ℂ}
    (hx : u ∈ coordinateDomain g x) (hy : u ∈ coordinateDomain g y)
    (hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h (g u)) :
    formalSubst (scalarCoordinate h y) (fun k => S.localJet hg y k u) =
      formalSubst (scalarCoordinate h x) (fun k => S.localJet hg x k u) := by
  have hf0 : S.localJet hg x 0 u = coordinateCurve g x u := (S.localJet_solution hg x).2.1 u hx
  have htx : coordinateTransition x y (coordinateCurve g x u) = coordinateCurve g y u := by
    simp only [coordinateTransition,coordinateCurve,Function.comp_apply,
      (chartAt (Model X) x).left_inv hx]
  have hH : AnalyticAt ℂ (coordinateTransition x y) (S.localJet hg x 0 u) := by
    rw [hf0]
    apply coordinateTransition_analytic x y ((chartAt (Model X) x).map_source hx)
    simpa only [coordinateCurve,Function.comp_apply,(chartAt (Model X) x).left_inv hx]
      using (show g u ∈ (chartAt (Model X) y).source from hy)
  have hh' : AnalyticAt ℂ (scalarCoordinate h y)
      (coordinateTransition x y (S.localJet hg x 0 u)) := by
    rw [hf0,htx]
    exact scalarCoordinate_analytic hy hh
  have hj : (fun k => S.localJet hg y k u) =
      composeJet (coordinateTransition x y) (fun k => S.localJet hg x k u) := by
    funext k
    exact (S.localJet_target_glue hg x y k hx hy).symm
  rw [hj,formalSubst_assoc _ _ _ hH hh']
  apply formalSubst_congr
  rw [hf0]
  have hcx := (chartAt (Model X) x).map_source hx
  have hcy : (chartAt (Model X) x).symm (coordinateCurve g x u) ∈
      (chartAt (Model X) y).source := by
    simpa only [coordinateCurve,Function.comp_apply,(chartAt (Model X) x).left_inv hx]
      using (show g u ∈ (chartAt (Model X) y).source from hy)
  have hnear := ((chartAt (Model X) x).symm.continuousAt hcx).preimage_mem_nhds
    ((chartAt (Model X) y).open_source.mem_nhds hcy)
  filter_upwards [hnear] with z hz
  change h ((chartAt (Model X) y).symm ((chartAt (Model X) y)
    ((chartAt (Model X) x).symm z))) = h ((chartAt (Model X) x).symm z)
  rw [(chartAt (Model X) y).left_inv hz]



theorem scalarJet_eq_local {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (h : X.Carrier → ℂ) (x : X.Carrier) {u : ℂ}
    (hx : u ∈ coordinateDomain g x)
    (hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h (g u)) :
    S.scalarJet hg h u = formalSubst (scalarCoordinate h x) (fun k => S.localJet hg x k u) :=
  S.localJet_scalar_glue hg h x (g u) hx (mem_chart_source (Model X) (g u)) hh



theorem scalarJet_analytic {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    {V : Set X.Carrier} (hV : IsOpen V) (h : X.Carrier → ℂ)
    (hh : ContMDiffOn (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h V)
    {u : ℂ} (hu : g u ∈ V) (n : ℕ) : AnalyticAt ℂ (fun z => coeff n (S.scalarJet hg h z)) u := by
  let x := g u
  have hx : u ∈ coordinateDomain g x := mem_chart_source (Model X) x
  have hf := S.localJet_solution hg x
  have hhAt := hh.contMDiffAt (hV.mem_nhds hu)
  have hcoord : AnalyticAt ℂ (scalarCoordinate h x) (S.localJet hg x 0 u) := by
    rw [hf.2.1 u hx]
    exact scalarCoordinate_analytic hx hhAt
  apply (composeCoefficient_analytic n (fun k _ i => hf.1 k i u hx) hcoord).congr
  have hnear := (coordinateDomain_open hg x).mem_nhds hx
  have hnearV := hg.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hu)
  filter_upwards [hnear,hnearV] with z hzx hzV
  simpa only [coeff_formalSubst] using
    (congrArg (coeff n) (S.scalarJet_eq_local hg h x hzx
      (hh.contMDiffAt (hV.mem_nhds hzV)))).symm





end

open HolomorphicJets PowerSeries
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 
theorem scalarJet_congr {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    {h k : X.Carrier → ℂ} (u : ℂ) (he : h =ᶠ[nhds (g u)] k) :
    S.scalarJet hg h u = S.scalarJet hg k u := by
  unfold scalarJet
  apply formalSubst_congr
  rw [(S.localJet_solution hg (g u)).2.1 u (mem_chart_source (Model X) (g u))]
  have hc := (chartAt (Model X) (g u)).symm.continuousAt
    ((chartAt (Model X) (g u)).map_source (mem_chart_source (Model X) (g u)))
  have ht : Tendsto (chartAt (Model X) (g u)).symm
      (nhds (coordinateCurve g (g u) u)) (nhds (g u)) := by
    simpa only [ContinuousAt,coordinateCurve,Function.comp_apply,
      (chartAt (Model X) (g u)).left_inv (mem_chart_source (Model X) (g u))] using hc
  exact he.comp_tendsto ht

theorem scalarJet_mul {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    {h k : X.Carrier → ℂ} (u : ℂ)
    (hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω h (g u))
    (hk : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω k (g u)) :
    S.scalarJet hg (fun x => h x * k x) u = S.scalarJet hg h u * S.scalarJet hg k u := by
  unfold scalarJet
  apply formalSubst_mul
  · rw [(S.localJet_solution hg (g u)).2.1 u (mem_chart_source (Model X) (g u))]
    exact scalarCoordinate_analytic (mem_chart_source (Model X) (g u)) hh
  · rw [(S.localJet_solution hg (g u)).2.1 u (mem_chart_source (Model X) (g u))]
    exact scalarCoordinate_analytic (mem_chart_source (Model X) (g u)) hk

end SplitTangent.TangentSplitting

namespace SplitTangent
open HolomorphicJets FormalProjective PowerSeries
variable {X : ComplexManifold.{u}}

 

theorem ProjectiveEmbedding.scalar_holomorphic (e : ProjectiveEmbedding X)
    (k j : Fin (e.N+1)) : ContMDiffOn (ModelWithCorners X) 𝓘(ℂ,ℂ) ω
      (fun x => projectiveCoordinates k (e.map x) j) {x | (e.map x).rep k ≠ 0} :=
  (ContinuousLinearMap.proj j : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).contMDiff.comp_contMDiffOn
    (e.holomorphic k)


theorem polynomial_presentation_patch (e : ProjectiveEmbedding X)
    {g : ℂ → X.Carrier} {p : Fin (e.N+1) → Polynomial ℂ}
    (hp : Finset.univ.gcd p = 1)
    (hpres : ∀ z k j, (e.map (g z)).rep k ≠ 0 →
      (p j).eval z = projectiveCoordinates k (e.map (g z)) j * (p k).eval z)
    (z : ℂ) (k : Fin (e.N+1)) : (p k).eval z ≠ 0 ↔ (e.map (g z)).rep k ≠ 0 := by
  constructor
  · intro hk hzero
    obtain ⟨l,hl⟩ : ∃ l, (e.map (g z)).rep l ≠ 0 := by
      by_contra! h
      exact (e.map (g z)).rep_nonzero (funext h)
    have he := hpres z l k hl
    simp only [projectiveCoordinates,hzero,mul_zero,zero_mul] at he
    exact hk he
  · intro hk hzero
    obtain ⟨j,hj⟩ := PolynomialTuple.basepoint_free p hp z
    have he := hpres z k j hk
    rw [hzero,mul_zero] at he
    exact hj he

namespace TangentSplitting
variable (S : TangentSplitting X)

 

def projectiveChartData (e : ProjectiveEmbedding X) {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (p : Fin (e.N+1) → Polynomial ℂ) (hp : Finset.univ.gcd p = 1)
    (hpres : ∀ z k j, (e.map (g z)).rep k ≠ 0 →
      (p j).eval z = projectiveCoordinates k (e.map (g z)) j * (p k).eval z) :
    ChartData p where
  basepoint_free := PolynomialTuple.basepoint_free p hp
  ratio k j z := S.scalarJet hg (fun x => projectiveCoordinates k (e.map x) j) z
  analytic k j z hk n := S.scalarJet_analytic hg (e.open_patch k) _
    (e.scalar_holomorphic k j) ((polynomial_presentation_patch e hp hpres z k).mp hk) n
  diagonal k j z hk := by
    rw [S.scalarJet_constant]
    exact (eq_div_iff hk).mpr (hpres z k j
      ((polynomial_presentation_patch e hp hpres z k).mp hk)).symm
  identity k z hk := by
    have ht := (polynomial_presentation_patch e hp hpres z k).mp hk
    calc
      S.scalarJet hg (fun x => projectiveCoordinates k (e.map x) k) z =
          S.scalarJet hg (fun _ => 1) z := by
        apply S.scalarJet_congr
        filter_upwards [(e.open_patch k).mem_nhds ht] with x hx
        exact inv_mul_cancel₀ hx
      _ = 1 := by simp
  overlap k l j z hk hl := by
    have htk := (polynomial_presentation_patch e hp hpres z k).mp hk
    have htl := (polynomial_presentation_patch e hp hpres z l).mp hl
    rw [← S.scalarJet_mul hg z
      ((e.scalar_holomorphic k l).contMDiffAt ((e.open_patch k).mem_nhds htk))
      ((e.scalar_holomorphic l j).contMDiffAt ((e.open_patch l).mem_nhds htl))]
    apply S.scalarJet_congr
    filter_upwards [(e.open_patch l).mem_nhds htl] with x hx
    exact projectiveCoordinates_mul (e.map x) k l j hx



end TangentSplitting
end SplitTangent

open Filter Topology

namespace SplitTangent.ProjectiveEmbedding
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

 
def withinChart (i : Fin (e.N+1)) (x : X.Carrier) : Model X → Fin (e.N+1) → ℂ :=
  (fun y => projectiveCoordinates i (e.map y)) ∘ (chartAt (Model X) x).symm

theorem withinChart_analytic (i : Fin (e.N+1)) (x : X.Carrier) {a : X.Carrier}
    (ha : a ∈ (chartAt (Model X) x).source) (hi : (e.map a).rep i ≠ 0) :
    AnalyticAt ℂ (e.withinChart i x) ((chartAt (Model X) x) a) := by
  apply analyticAt_pi_iff.mpr
  intro j
  exact TangentSplitting.scalarCoordinate_analytic ha
    (e.scalar_holomorphic i j |>.contMDiffAt (e.open_patch i |>.mem_nhds hi))

theorem withinChart_immersion (i : Fin (e.N+1)) (x : X.Carrier) {a : X.Carrier}
    (ha : a ∈ (chartAt (Model X) x).source) (hi : (e.map a).rep i ≠ 0) :
    Function.Injective (fderiv ℂ (e.withinChart i x) ((chartAt (Model X) x) a)) := by
  let c := chartAt (Model X) x
  let t := trivializationAt (Model X) (Tangent X) x
  have hc := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x)
      (c.map_source ha)).mdifferentiableAt (by simp)
  have he := (e.holomorphic i |>.contMDiffAt (e.open_patch i |>.mem_nhds hi)).mdifferentiableAt (by simp)
  have he' : MDifferentiableAt (ModelWithCorners X) 𝓘(ℂ,Fin (e.N+1) → ℂ)
      (fun y => projectiveCoordinates i (e.map y)) (c.symm (c a)) := by
    rw [c.left_inv ha]
    exact he
  have ht : t.symmL ℂ a = mfderiv 𝓘(ℂ,Model X) (ModelWithCorners X) c.symm (c a) := by
    simpa [t,c,extChartAt_coe_symm,extChartAt_coe,ModelWithCorners] using
      (TangentBundle.symmL_trivializationAt (I := ModelWithCorners X) ha)
  have hd : fderiv ℂ (e.withinChart i x) (c a) =
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,Fin (e.N+1) → ℂ)
        (fun y => projectiveCoordinates i (e.map y)) a).comp (t.symmL ℂ a) := by
    rw [ht]
    change fderiv ℂ ((fun y => projectiveCoordinates i (e.map y)) ∘ c.symm) (c a) = _
    rw [← mfderiv_eq_fderiv,mfderiv_comp _ he' hc,c.left_inv ha]
    rfl
  rw [hd]
  have hti : Function.Injective (t.symmL ℂ a) := by
    intro v w hv
    have ht' : a ∈ t.baseSet := ha
    calc
      v = t.continuousLinearMapAt ℂ a (t.symmL ℂ a v) := (t.continuousLinearMapAt_symmL ht' v).symm
      _ = t.continuousLinearMapAt ℂ a (t.symmL ℂ a w) := congrArg _ hv
      _ = w := t.continuousLinearMapAt_symmL ht' w
  exact (e.immersion a i hi).comp hti

end SplitTangent.ProjectiveEmbedding

open Filter Topology

namespace SplitTangent.ProjectiveEmbedding
section
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)


theorem isClosed_incidence : IsClosed {q : X.Carrier × (Fin (e.N+1) → ℂ) |
    e.Incidence q.1 q.2} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨x,v⟩ hx
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i ≠ 0 at hi
  change ¬ e.Incidence x v at hx
  rw [e.incidence_iff_coordinates hi] at hx
  push Not at hx
  obtain ⟨j,hj⟩ := hx
  have hc : ContinuousAt (fun y => projectiveCoordinates i (e.map y) j) x :=
    (continuous_apply j).continuousAt.comp
      (e.holomorphic i |>.contMDiffAt ((e.open_patch i).mem_nhds hi)).continuousAt
  have hg : ContinuousAt (fun q : X.Carrier × (Fin (e.N+1) → ℂ) =>
      projectiveCoordinates i (e.map q.1) j) (x,v) := by
    have hfst : ContinuousAt (Prod.fst : X.Carrier × (Fin (e.N+1) → ℂ) → X.Carrier) (x,v) :=
      continuous_fst.continuousAt
    exact hc.comp_of_eq hfst rfl
  have he : ∀ᶠ q : X.Carrier × (Fin (e.N+1) → ℂ) in 𝓝 (x,v),
      q.2 j ≠ q.2 i * projectiveCoordinates i (e.map q.1) j :=
    (((continuous_apply j).comp continuous_snd).continuousAt.ne_iff_eventually_ne
      (((continuous_apply i).comp continuous_snd).continuousAt.mul hg)).mp hj
  have hp : ∀ᶠ q : X.Carrier × (Fin (e.N+1) → ℂ) in 𝓝 (x,v),
      (e.map q.1).rep i ≠ 0 :=
    (continuous_fst.tendsto (x,v)).eventually ((e.open_patch i).mem_nhds hi)
  filter_upwards [he,hp] with q hq hqi
  exact fun hh => hq ((e.incidence_iff_coordinates hqi).mp hh j)



theorem incidence_localizes [CompactSpace X.Carrier] {x : X.Carrier}
    {v : Fin (e.N+1) → ℂ} (hv : v ≠ 0) (hx : e.Incidence x v)
    {U : Set X.Carrier} (hU : IsOpen U) (hxU : x ∈ U) :
    ∀ᶠ w in 𝓝 v, ∀ y, e.Incidence y w → y ∈ U := by
  let A : Set (X.Carrier × (Fin (e.N+1) → ℂ)) :=
    {q | e.Incidence q.1 q.2} ∩ (Prod.fst ⁻¹' Uᶜ)
  have hA : IsClosed A := e.isClosed_incidence.inter (hU.isClosed_compl.preimage continuous_fst)
  have hB := isClosedMap_snd_of_compactSpace A hA
  have hvB : v ∈ (Prod.snd '' A)ᶜ := by
    rintro ⟨⟨y,w⟩,hy,rfl⟩
    exact hy.2 (e.incidence_unique hv hy.1 hx ▸ hxU)
  filter_upwards [hB.isOpen_compl.mem_nhds hvB] with w hw y hy
  by_contra hyU
  exact hw ⟨(y,w),⟨hy,hyU⟩,rfl⟩

 
def normalize (i : Fin (e.N+1)) (v : Fin (e.N+1) → ℂ) : Fin (e.N+1) → ℂ :=
  fun j => (v i)⁻¹ * v j

theorem normalize_analytic {i : Fin (e.N+1)} {v : Fin (e.N+1) → ℂ}
    (hv : v i ≠ 0) : AnalyticAt ℂ (e.normalize i) v := by
  apply analyticAt_pi_iff.mpr
  intro j
  exact ((ContinuousLinearMap.proj i : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).analyticAt v).inv hv |>.mul
    ((ContinuousLinearMap.proj j : (Fin (e.N+1) → ℂ) →L[ℂ] ℂ).analyticAt v)

theorem incidence_iff_normalize {x : X.Carrier} {v : Fin (e.N+1) → ℂ}
    {i : Fin (e.N+1)} (hi : (e.map x).rep i ≠ 0) (hv : v i ≠ 0) :
    e.Incidence x v ↔ e.normalize i v = projectiveCoordinates i (e.map x) := by
  rw [e.incidence_iff_coordinates hi]
  constructor
  · intro h
    ext j
    dsimp [normalize]
    rw [h j,← mul_assoc,inv_mul_cancel₀ hv,one_mul]
  · intro h j
    have hj := congrFun h j
    dsimp [normalize] at hj
    rw [← hj,← mul_assoc,mul_inv_cancel₀ hv,one_mul]



end

variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]



theorem exists_local_lift [CompactSpace X.Carrier] {x : X.Carrier}
    {v : Fin (e.N+1) → ℂ} (hv : v ≠ 0) (hx : e.Incidence x v) :
    ∃ L : (Fin (e.N+1) → ℂ) → X.Carrier,
      ContMDiffAt 𝓘(ℂ,Fin (e.N+1) → ℂ) (ModelWithCorners X) ω L v ∧
      ∀ᶠ w in 𝓝 v, ∀ y, e.Incidence y w → L w = y := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i ≠ 0 at hi
  have hvi : v i ≠ 0 := by
    intro hz
    apply hv
    ext j
    rw [(e.incidence_iff_coordinates hi).mp hx j,hz,zero_mul]
    rfl
  let c := chartAt (Model X) x
  let H := e.withinChart i x
  let n := e.normalize i
  have hcx : x ∈ c.source := mem_chart_source (Model X) x
  have hn : n v = H (c x) := by
    rw [e.incidence_iff_normalize hi hvi] at hx
    simpa [H,withinChart,c] using hx
  have hH : AnalyticAt ℂ H (c x) := e.withinChart_analytic i x hcx hi
  obtain ⟨r,hr,hr0,hri⟩ := AnalyticRetraction.exists_left_inverse hH
    (e.withinChart_immersion i x hcx hi)
  have hrn : AnalyticAt ℂ (r ∘ n) v := (hn ▸ hr).comp (e.normalize_analytic hvi)
  have hrn0 : r (n v) = c x := hn ▸ hr0
  have heq : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ (e.map y).rep i ≠ 0 ∧
      r (projectiveCoordinates i (e.map y)) = c y := by
    have hri' := (c.continuousAt hcx).eventually hri
    filter_upwards [c.open_source.mem_nhds hcx,(e.open_patch i).mem_nhds hi,hri'] with y hy hiy hry
    refine ⟨hy,hiy,?_⟩
    change r (projectiveCoordinates i (e.map (c.symm (c y)))) = c y at hry
    rwa [c.left_inv hy] at hry
  obtain ⟨U,hUsub,hU,hxU⟩ := mem_nhds_iff.mp heq
  have hloc := e.incidence_localizes hv hx hU hxU
  refine ⟨c.symm ∘ (r ∘ n),?_,?_⟩
  · have hc := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x)
        (c.map_source hcx)
    exact hc.comp_of_eq hrn.contDiffAt.contMDiffAt hrn0
  · have hni : ∀ᶠ w in 𝓝 v, w i ≠ 0 := (continuous_apply i).continuousAt.eventually_ne hvi
    filter_upwards [hloc,hni] with w hw hiw y hy
    obtain ⟨hcy,hiy,hry⟩ := hUsub (hw y hy)
    have hnw : n w = projectiveCoordinates i (e.map y) :=
      (e.incidence_iff_normalize hiy hiw).mp hy
    dsimp only [Function.comp_apply]
    rw [hnw,hry,c.left_inv hcy]

 

theorem holomorphic_of_incidence [CompactSpace X.Carrier] {Q : E → Fin (e.N+1) → ℂ}
    {F : E → X.Carrier} {z : E} (hQ : AnalyticAt ℂ Q z) (hnz : Q z ≠ 0)
    (hF : ∀ᶠ w in 𝓝 z, e.Incidence (F w) (Q w)) :
    ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω F z := by
  obtain ⟨L,hL,hLinv⟩ := e.exists_local_lift hnz hF.self_of_nhds
  apply (hL.comp z hQ.contDiffAt.contMDiffAt).congr_of_eventuallyEq
  filter_upwards [hF,hQ.continuousAt.eventually hLinv] with w hw hLw
  exact (hLw (F w) hw).symm



end SplitTangent.ProjectiveEmbedding

namespace SplitTangent.TangentSplitting

open Filter Topology
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']


def projectedInChart (x : X.Carrier) (F : E → X.Carrier) (v : E) (z : E) : Model X :=
  S.coordinateProjector x ((chartAt (Model X) x) (F z))
    (fderiv ℂ ((chartAt (Model X) x) ∘ F) z v)

end SplitTangent.TangentSplitting

open Filter Topology Metric Set

 

open MvPowerSeries

open Filter Topology Set Metric

namespace SplitTangent.ProjectiveEmbedding
open Filter Topology
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

lemma incidence_smul_iff {x : X.Carrier} {v : Fin (e.N+1) → ℂ} {s : ℂ} (hs : s ≠ 0) :
    e.Incidence x (s • v) ↔ e.Incidence x v := by
  constructor <;> intro h i j
  · have H := h i j
    simp only [Pi.smul_apply,smul_eq_mul] at H
    apply mul_left_cancel₀ hs
    calc
      s * ((e.map x).rep i * v j) = (e.map x).rep i*(s*v j) := by ring
      _ = (e.map x).rep j*(s*v i) := H
      _ = s*((e.map x).rep j*v i) := by ring
  · simp only [Pi.smul_apply,smul_eq_mul]
    calc
      (e.map x).rep i*(s*v j) = s*((e.map x).rep i*v j) := by ring
      _ = s*((e.map x).rep j*v i) := by rw [h i j]
      _ = (e.map x).rep j*(s*v i) := by ring



lemma coneLift_eq (x₀ : X.Carrier) {v : Fin (e.N+1) → ℂ}
    {x : X.Carrier} (hv : v ≠ 0) (hx : e.Incidence x v) : e.coneLift x₀ v = x :=
  e.incidence_unique hv (e.coneLift_incidence x₀ ⟨x,hx⟩) hx

lemma coneLift_smul (x₀ : X.Carrier) {v : Fin (e.N+1) → ℂ} {s : ℂ}
    (hs : s ≠ 0) (hv : ∃ x, e.Incidence x v) : e.coneLift x₀ (s • v) = e.coneLift x₀ v := by
  by_cases hv0 : v = 0
  · simp only [hv0,smul_zero]
  · apply e.coneLift_eq x₀ (smul_ne_zero hs hv0)
    exact (e.incidence_smul_iff hs).mpr (e.coneLift_incidence x₀ hv)

end SplitTangent.ProjectiveEmbedding

namespace SplitTangent.RationalSurface
open PolynomialBlowup

def toMv : B →+* P :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)) (MvPolynomial.X 1)

end SplitTangent.RationalSurface

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Families. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

open Set Filter Topology
open scoped ContDiff

open Filter Topology Set
open scoped ContDiff

open Filter Topology Set

open scoped Manifold LinearAlgebra.Projectivization
open Bundle

open Filter Topology


open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology

open Set Filter Topology

open Filter Topology

open Filter Topology

open Filter Topology Metric Set

 

open MvPowerSeries

open Filter Topology Set Metric

 

open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff Manifold BigOperators

namespace SplitTangent.RationalParameters
open AnalyticZeroCover

abbrev Coeff (N d : ℕ) := Space ((N+1)*(d+1))

 
def ev {N d : ℕ} (b : Bool) (τ : Coeff N d) (z : ℂ) : Fin (N+1) → ℂ :=
  fun i => ∑ k : Fin (d+1), τ (finProdFinEquiv (i,k)) * z ^ (if b then d-k.val else k.val)

lemma ev_analytic {N d : ℕ} (b : Bool) (a : ℂ × Coeff N d) :
    AnalyticAt ℂ (fun z : ℂ × Coeff N d => ev b z.2 z.1) a := by
  apply analyticAt_pi_iff.mpr
  intro i
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact (((ContinuousLinearMap.proj (finProdFinEquiv (i,k)) : Coeff N d →L[ℂ] ℂ).analyticAt _).comp
    analyticAt_snd).mul (analyticAt_fst.pow _)

lemma ev_transition {N d : ℕ} (τ : Coeff N d) {z : ℂ} (hz : z≠0) :
    ev false τ z = z^d • ev true τ z⁻¹ := by
  ext i
  simp only [ev,Bool.false_eq_true,↓reduceIte,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk : k.val≤d := Nat.le_of_lt_succ k.isLt
  rw [inv_pow,← mul_assoc, mul_comm (z^d) (τ _),mul_assoc]
  congr 1
  rw [← div_eq_mul_inv,eq_div_iff (pow_ne_zero _ hz)]
  rw [← pow_add,Nat.add_sub_of_le hk]

 
def regular (N d : ℕ) : Set (Coeff N d) :=
  {τ | ∀ b : Bool, ∀ z∈Metric.closedBall (0 : ℂ) 1, ev b τ z≠0}

lemma regular_nonzero {N d : ℕ} {τ : Coeff N d} (hτ : τ∈regular N d)
    (b : Bool) (z : ℂ) : ev b τ z≠0 := by
  by_cases hz : ‖z‖≤1
  · exact hτ b z (by simpa using hz)
  · have hz0 : z≠0 := by intro h; simp [h] at hz
    have hzi : z⁻¹∈Metric.closedBall (0 : ℂ) 1 := by
      simp only [Metric.mem_closedBall,dist_zero_right,norm_inv]
      exact (inv_le_one₀ (norm_pos_iff.mpr hz0)).mpr (le_of_lt (lt_of_not_ge hz))
    cases b
    · rw [ev_transition τ hz0]
      exact smul_ne_zero (pow_ne_zero _ hz0) (hτ true z⁻¹ hzi)
    · intro he
      have htrans := ev_transition τ (inv_ne_zero hz0)
      simp only [inv_inv,he,smul_zero] at htrans
      exact hτ false z⁻¹ hzi htrans

 
def accepted {X : ComplexManifold} (e : ProjectiveEmbedding X) (d : ℕ) : Set (Coeff e.N d) :=
  {τ | ∀ b : Bool, ∀ z : ℂ, ∃ x, e.Incidence x (ev b τ z)}


variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) [CompactSpace X.Carrier]
variable (x₀ : X.Carrier) {d : ℕ} (P : Patch (Coeff e.N d))
variable (hP : P.image ⊆ regular e.N d ∩ accepted e d)

 
def evaluation (b : Bool) (w : ℂ × Space P.dim) : X.Carrier :=
  e.coneLift x₀ (ev b (P.map w.2) w.1)

include hP in
lemma evaluation_holomorphicAt (b : Bool) {w : ℂ × Space P.dim} (hw : w.2∈P.domain) :
    ContMDiffAt 𝓘(ℂ,ℂ × Space P.dim) (ModelWithCorners X) ω (evaluation e x₀ P b) w := by
  apply e.holomorphic_of_incidence
    (AnalyticAt.comp (f := fun y : ℂ × Space P.dim => (y.1,P.map y.2)) (ev_analytic b (w.1,P.map w.2))
      (analyticAt_fst.prod ((P.analytic w.2 hw).comp analyticAt_snd)))
    (regular_nonzero (hP ⟨w.2,hw,rfl⟩).1 b w.1)
  have hv : ∀ᶠ y : ℂ × Space P.dim in 𝓝 w, y.2∈P.domain :=
    continuous_snd.continuousAt.eventually (P.isOpen_domain.mem_nhds hw)
  exact hv.mono (fun y hy => e.coneLift_incidence x₀ ((hP ⟨y.2,hy,rfl⟩).2 b y.1))

include hP in
omit [CompactSpace X.Carrier] in
lemma evaluation_overlap (z : ℂ) (hz : z≠0) {τ : Space P.dim} (hτ : τ∈P.domain) :
    evaluation e x₀ P false (z,τ) = evaluation e x₀ P true (z⁻¹,τ) := by
  dsimp only [evaluation]
  rw [ev_transition _ hz,e.coneLift_smul x₀ (pow_ne_zero d hz) ((hP ⟨τ,hτ,rfl⟩).2 true z⁻¹)]

def pairEvaluation (τ : Space P.dim) : X.Carrier × X.Carrier :=
  (evaluation e x₀ P false (0,τ),evaluation e x₀ P false (1,τ))



def family {W : Set (Space P.dim)} (hW : IsOpen W) (hne : W.Nonempty) (hWP : W⊆P.domain) :
    RationalFamily X (OpenManifold.manifold.{u} W hW hne) where
  finite p := evaluation e x₀ P false (p.1,OpenManifold.val W p.2)
  infinity p := evaluation e x₀ P true (p.1,OpenManifold.val W p.2)
  finite_holomorphic := by
    intro p
    exact (evaluation_holomorphicAt e x₀ P hP false (hWP p.2.down.property)).comp p
      (contMDiffAt_fst.prodMk_space ((OpenManifold.val_holomorphic W hW hne).contMDiffAt.comp p contMDiffAt_snd))
  infinity_holomorphic := by
    intro p
    exact (evaluation_holomorphicAt e x₀ P hP true (hWP p.2.down.property)).comp p
      (contMDiffAt_fst.prodMk_space ((OpenManifold.val_holomorphic W hW hne).contMDiffAt.comp p contMDiffAt_snd))
  overlap z hz τ := evaluation_overlap e x₀ P hP z hz (hWP τ.down.property)

end SplitTangent.RationalParameters

 

open Set Filter Topology
open scoped ContDiff Manifold



open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff


 

open Set Filter Topology
open scoped ContDiff




open Set Filter Topology
open scoped ContDiff



open Set Filter Topology
open scoped ContDiff ENNReal



open Set Filter Topology
open scoped ContDiff ENNReal



open Set Filter Topology IsManifold
open scoped ContDiff Manifold

 

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Encoding. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold BigOperators
universe u
namespace SplitTangent.RationalParameters

 
def ofPolynomials {N : ℕ} (d : ℕ) (P : Fin (N+1) → Polynomial ℂ) : Coeff N d :=
  fun k => (P (finProdFinEquiv.symm k).1).coeff (finProdFinEquiv.symm k).2.val

end SplitTangent.RationalParameters

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalReparam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Reparam. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u
namespace SplitTangent.RationalCurve
variable {X : ComplexManifold.{u}} (g : RationalCurve X)


lemma homogeneousValue_finite {a b : ℂ} (hb : b≠0) :
    g.homogeneousValue a b = g.finite (a/b) := ite_eq_right hb

lemma homogeneousValue_infinity {a b : ℂ} (ha : a≠0) :
    g.homogeneousValue a b = g.infinity (b/a) := by
  by_cases hb : b=0
  · simp [homogeneousValue,hb]
  · rw [g.homogeneousValue_finite hb,g.overlap (a/b) (div_ne_zero ha hb),inv_div]

lemma homogeneousValue_holomorphicAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : E → ℂ} {z : E} (ha : AnalyticAt ℂ a z) (hb : AnalyticAt ℂ b z)
    (hnz : a z≠0 ∨ b z≠0) :
    ContMDiffAt 𝓘(ℂ,E) (ModelWithCorners X) ω (fun y => g.homogeneousValue (a y) (b y)) z := by
  rcases hnz with h | h
  · have H := g.infinity_holomorphic.contMDiffAt.comp z ((hb.div ha h).contDiffAt.contMDiffAt)
    apply H.congr_of_eventuallyEq
    filter_upwards [ha.continuousAt.eventually_ne h] with y hy
    exact g.homogeneousValue_infinity hy
  · have H := g.finite_holomorphic.contMDiffAt.comp z ((ha.div hb h).contDiffAt.contMDiffAt)
    apply H.congr_of_eventuallyEq
    filter_upwards [hb.continuousAt.eventually_ne h] with y hy
    exact g.homogeneousValue_finite hy

lemma homogeneousValue_smul {a b s : ℂ} (hs : s≠0) :
    g.homogeneousValue (s*a) (s*b)=g.homogeneousValue a b := by
  by_cases hb : b=0
  · simp [homogeneousValue,hb]
  · rw [g.homogeneousValue_finite (mul_ne_zero hs hb),g.homogeneousValue_finite hb,
      mul_div_mul_left _ _ hs]

 
def mobius (a b c d : ℂ) (hdet : a*d-b*c≠0) : RationalCurve X where
  finite z := g.homogeneousValue (a*z+b) (c*z+d)
  infinity z := g.homogeneousValue (a+b*z) (c+d*z)
  finite_holomorphic := by
    intro z
    apply g.homogeneousValue_holomorphicAt (by fun_prop) (by fun_prop)
    by_contra! h
    apply hdet
    linear_combination a*h.2-c*h.1
  infinity_holomorphic := by
    intro z
    apply g.homogeneousValue_holomorphicAt (by fun_prop) (by fun_prop)
    by_contra! h
    apply hdet
    linear_combination d*h.1-b*h.2
  overlap z hz := by
    rw [← g.homogeneousValue_smul (a := a+b*z⁻¹) (b := c+d*z⁻¹) hz]
    congr 1 <;> field_simp



end SplitTangent.RationalCurve

end

end OAI
end


