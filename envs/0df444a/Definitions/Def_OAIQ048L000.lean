-- Prove2me | Definitions.Def_OAIQ048L000
-- name    : OAIQ048L000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:20:51.944853+00:00
-- url     : https://prove2.me/theorems/36666df8-e699-46d2-ae94-c73083a06916
-- title:
--   Definitions bundle OAIQ048L000 of the split of OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 703 declarations of OpenAI's Lean: 229 definitions, 9 inductive types or structures, 1 instance and 464 theorems. The definitions and types are `OAI.LogConcaveSampling.AdjointRemoval.Adjacent`, `OAI.LogConcaveSampling.AdjointRemoval.ChainSlot`, `OAI.LogConcaveSampling.AdjointRemoval.FullColors`, `OAI.LogConcaveSampling.AdjointRemoval.Hessian`, `OAI.LogConcaveSampling.AdjointRemoval.Hessian.degree`, `OAI.LogConcaveSampling.AdjointRemoval.Hessian.hit`, `OAI.LogConcaveSampling.AdjointRemoval.Hessian.tokens`, `OAI.LogConcaveSampling.AdjointRemoval.InternalEdge`, `OAI.LogConcaveSampling.AdjointRemoval.Port`, `OAI.LogConcaveSampling.AdjointRemoval.PrimaryTraceSlot`, `OAI.LogConcaveSampling.AdjointRemoval.Regular`, `OAI.LogConcaveSampling.AdjointRemoval.State`, `OAI.LogConcaveSampling.AdjointRemoval.State.degree`, `OAI.LogConcaveSampling.AdjointRemoval.State.good`, `OAI.LogConcaveSampling.AdjointRemoval.State.tokens`, `OAI.LogConcaveSampling.AdjointRemoval.Step`, `OAI.LogConcaveSampling.AdjointRemoval.TargetVertex`, `OAI.LogConcaveSampling.AdjointRemoval.TraceColors`, `OAI.LogConcaveSampling.AdjointRemoval.TraceEdge`, `OAI.LogConcaveSampling.AdjointRemoval.branchIncidenceTensor`, `OAI.LogConcaveSampling.AdjointRemoval.branches`, `OAI.LogConcaveSampling.AdjointRemoval.chainBranch`, `OAI.LogConcaveSampling.AdjointRemoval.chainField`, `OAI.LogConcaveSampling.AdjointRemoval.chainPositionTensor`, `OAI.LogConcaveSampling.AdjointRemoval.chainSlotEquiv`, `OAI.LogConcaveSampling.AdjointRemoval.closeTrace`, `OAI.LogConcaveSampling.AdjointRemoval.coloringSplit`, `OAI.LogConcaveSampling.AdjointRemoval.cutDecEqAT`, `OAI.LogConcaveSampling.AdjointRemoval.cutDecEqBT`, `OAI.LogConcaveSampling.AdjointRemoval.cutDecEqCB`, `OAI.LogConcaveSampling.AdjointRemoval.cutDecEqPB`, `OAI.LogConcaveSampling.AdjointRemoval.cutDecEqQB`, `OAI.LogConcaveSampling.AdjointRemoval.derivativeEdgeEquiv`, `OAI.LogConcaveSampling.AdjointRemoval.destination`, `OAI.LogConcaveSampling.AdjointRemoval.edgeSource`, `OAI.LogConcaveSampling.AdjointRemoval.edgeTarget`, `OAI.LogConcaveSampling.AdjointRemoval.expand`, `OAI.LogConcaveSampling.AdjointRemoval.hessian`, `OAI.LogConcaveSampling.AdjointRemoval.hessianEdgeEquiv`, `OAI.LogConcaveSampling.AdjointRemoval.hessianIncidenceTensor` and 198 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `LogConcave_Analysis_CenteringPotential`, `LogConcave_Analysis_ConditionalPotential`, `LogConcave_Analysis_EulerDrift`, `LogConcave_Analysis_GaussianCoefficient`, `LogConcave_Analysis_GaussianProposalPotential`, `LogConcave_Analysis_InterpolationPotential`, `LogConcave_Analysis_Operator`, `LogConcave_Analysis_Poincare`, `LogConcave_Analysis_PrimitivePotentialModeBounds`, `LogConcave_Analysis_ProposalLog`, `LogConcave_Analysis_SymmetricGradientDerivative`, `LogConcave_Complexity_KernelActionRmsBudget`, `LogConcave_Dynamics_Curve`, `LogConcave_Dynamics_DistanceCoupled`, `LogConcave_Dynamics_Squared`, `LogConcave_Dynamics_StationaryPath`, `LogConcave_JetEstimates_AssignmentsFinset`, `LogConcave_JetEstimates_Bound`, `LogConcave_JetEstimates_CrossMoment`, `LogConcave_JetEstimates_DirLogLaplace`, `LogConcave_JetEstimates_Extension`, `LogConcave_JetEstimates_Growth`, `LogConcave_JetEstimates_JetNormalizedLaplaceMoments`, `LogConcave_JetEstimates_MixedJetAdd`, `LogConcave_JetEstimates_NormalizedLaplace`, `LogConcave_JetEstimates_PolyC1`, `LogConcave_Numerics_Basis`, `LogConcave_Numerics_BasisDerivative`, `LogConcave_Numerics_CenteringStateQuadratureBudget`, `LogConcave_Numerics_CenteringVelocityPicard`, `LogConcave_Numerics_CompositeAngle`, `LogConcave_Numerics_Correction`, `LogConcave_Numerics_LogMeshLength`, `LogConcave_Numerics_MeanTree`, `LogConcave_Numerics_NodePolynomial`, `LogConcave_Numerics_OrdinaryDerivativeWeight`, `LogConcave_Numerics_Picard`, `LogConcave_Numerics_ReanchorWeight`, `LogConcave_Numerics_Remainder`, `LogConcave_OraclePrograms_CenteringMeanCircuit`, `LogConcave_OraclePrograms_CircuitD`, `LogConcave_OraclePrograms_Program`, `LogConcave_Sampling_AngleNodes`, `LogConcave_Sampling_CenteringVelocityJoint`, `LogConcave_Sampling_ConditionalFieldMean`, `LogConcave_Sampling_ConditionalMeanScalar`, `LogConcave_Sampling_ConditionalPositionMoment`, `LogConcave_Sampling_ConditionalSlotEmbedding`, `LogConcave_Sampling_ContinuousFirstOrderReply`, `LogConcave_Sampling_CoordinateProjection`, `LogConcave_Sampling_CoordinateRank`, `LogConcave_Sampling_Directional`, `LogConcave_Sampling_IterTensorLie`, `LogConcave_Sampling_JointPosition`, `LogConcave_Sampling_KernelTransportAction`, `LogConcave_Sampling_LintegralFinNatProd`, `LogConcave_Sampling_PolynomialGrowth`, `LogConcave_Sampling_Primitive`, `LogConcave_Sampling_PrimitiveExpectedField`, `LogConcave_Sampling_PrimitiveField`, `LogConcave_Sampling_ProbabilityEndpoint`, `LogConcave_Sampling_ProbabilityNodes`, `LogConcave_Sampling_ProbabilityVelocity`, `LogConcave_Sampling_QuadraticExpectation`, `LogConcave_Sampling_StationaryMeanTarget`, `LogConcave_Sampling_TensorVector`, `LogConcave_Sampling_TerminalBackward`, `LogConcave_Sampling_TiltedExpectation`, `LogConcave_Sampling_TimeBump`, `LogConcave_TensorGraphs_AdjointMatrix`, `LogConcave_TensorGraphs_Chain`, `LogConcave_TensorGraphs_ColoringSplit`, `LogConcave_TensorGraphs_HessianIncidenceTensor`, `LogConcave_TensorGraphs_HessianIncidentEquiv`, `LogConcave_TensorGraphs_History`, `LogConcave_TensorGraphs_IncidentMatrix`, `LogConcave_TensorGraphs_Inside`, `LogConcave_TensorGraphs_PrimaryPositionTensor`, `LogConcave_TensorGraphs_RankEquiv`, `LogConcave_TensorGraphs_Vertex`.
--
--   **Imports.** It imports the published bundle `Def_LogConcaveQuery`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ048L002` and `OAIQ048L003`; the statements `OAI.LogConcaveSampling.centeringTrueVelocity_continuous`, `OAI.LogConcaveSampling.exists_centering_stationaryPath`, `OAI.LogConcaveSampling.stationaryMeanTarget_identity` and `OAI.LogConcaveSampling.stationaryMeanTarget_law`.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_LogConcaveQuery

section
-- module Solutions.OAIQ048_LC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_Curve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.GlobalODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} (t₀ : Icc a b) (f : ℝ → E → E)

abbrev Curve := C(Icc a b,E)

def extend (α : Curve (a:=a) (b:=b) (E:=E)) (t : ℝ) : E :=
  α (projIcc a b (le_trans t₀.2.1 t₀.2.2) t)

omit [NormedSpace ℝ E] in
lemma extend_of_mem (α : Curve (a:=a) (b:=b) (E:=E)) {t : ℝ} (ht : t∈Icc a b) :
    extend t₀ α t=α ⟨t,ht⟩ := by simp [extend,projIcc_of_mem _ ht]

omit [NormedSpace ℝ E] in
lemma extend_continuous (α : Curve (a:=a) (b:=b) (E:=E)) : Continuous (extend t₀ α) :=
  α.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] in
lemma continuous_comp (hf : Continuous (uncurry f)) (α : Curve (a:=a) (b:=b) (E:=E)) :
    Continuous (fun t => f t (extend t₀ α t)) :=
  hf.comp (continuous_id.prodMk (extend_continuous t₀ α))

def next (hf : Continuous (uncurry f)) (x : E) (α : Curve (a:=a) (b:=b) (E:=E)) :
    Curve (a:=a) (b:=b) (E:=E) where
  toFun t := x+∫ τ in (t₀:ℝ)..(t:ℝ),f τ (extend t₀ α τ)
  continuous_toFun := (continuous_const.add
    (intervalIntegral.continuous_primitive
      (fun _ _ => (continuous_comp t₀ f hf α).intervalIntegrable _ _) t₀)).comp continuous_subtype_val

lemma next_apply (hf : Continuous (uncurry f)) (x : E)
    (α : Curve (a:=a) (b:=b) (E:=E)) (t : Icc a b) :
    next t₀ f hf x α t=x+∫ τ in (t₀:ℝ)..(t:ℝ),f τ (extend t₀ α τ) := rfl

variable {f} (hf : Continuous (uncurry f)) {K : ℝ≥0}
  (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
include hf hL

lemma iterate_dist_point (x : E) (α β : Curve (a:=a) (b:=b) (E:=E)) (n : ℕ) (t : Icc a b) :
    dist ((next t₀ f hf x)^[n] α t) ((next t₀ f hf x)^[n] β t) ≤
      ((K:ℝ)*|(t:ℝ)-(t₀:ℝ)|)^n/(n.factorial:ℝ)*dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f:=α) (g:=β) t
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply',dist_eq_norm,next_apply,next_apply,
      add_sub_add_left_eq_sub,←intervalIntegral.integral_sub
        ((continuous_comp t₀ f hf _).intervalIntegrable _ _)
        ((continuous_comp t₀ f hf _).intervalIntegrable _ _)]
    calc
      _ ≤ ∫ τ in uIoc (t₀:ℝ) (t:ℝ), (K:ℝ)^(n+1)*|τ-(t₀:ℝ)|^n/(n.factorial:ℝ)*dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro s hs
        have hs' : s∈Icc a b := (uIoc_subset_uIcc.trans (uIcc_subset_Icc t₀.2 t.2)) hs
        rw [←dist_eq_norm,extend_of_mem _ _ hs',extend_of_mem _ _ hs']
        calc
          _ ≤ (K:ℝ)*dist ((next t₀ f hf x)^[n] α ⟨s,hs'⟩) ((next t₀ f hf x)^[n] β ⟨s,hs'⟩) :=
            (hL s hs').dist_le_mul _ _
          _ ≤ _ := by
            rw [pow_succ',mul_assoc,mul_div_assoc,mul_assoc]
            gcongr
            simpa only [←mul_pow] using ih ⟨s,hs'⟩
      _ ≤ ((K:ℝ)*|(t:ℝ)-(t₀:ℝ)|)^(n+1)/((n+1).factorial:ℝ)*dist α β := by
        apply le_of_abs_le
        rw [←intervalIntegral.abs_intervalIntegral_eq,intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div,intervalIntegral.integral_const_mul,abs_mul,abs_div,
          abs_mul,intervalIntegral.abs_intervalIntegral_eq,integral_pow_abs_sub_uIoc,abs_div,
          abs_pow,abs_pow,abs_dist,NNReal.abs_eq,abs_abs,mul_div,div_div,←abs_mul,
          ←Nat.cast_succ,←Nat.cast_mul,←Nat.factorial_succ,Nat.abs_cast,←mul_pow]

lemma iterate_dist (x : E) (α β : Curve (a:=a) (b:=b) (E:=E)) (n : ℕ) :
    dist ((next t₀ f hf x)^[n] α) ((next t₀ f hf x)^[n] β) ≤
      ((K:ℝ)*max (b-(t₀:ℝ)) ((t₀:ℝ)-a))^n/(n.factorial:ℝ)*dist α β := by
  have hmax : 0 ≤ max (b-(t₀:ℝ)) ((t₀:ℝ)-a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  apply (iterate_dist_point t₀ hf hL x α β n t).trans
  gcongr
  exact abs_sub_le_max_sub t.2.1 t.2.2 _

lemma contracting_iterate : ∃ n : ℕ, ∃ C : ℝ≥0, ∀ x : E,
    ContractingWith C (next t₀ f hf x)^[n] := by
  obtain ⟨n,hn⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop
    ((K:ℝ)*max (b-(t₀:ℝ)) ((t₀:ℝ)-a))).eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hmax : 0 ≤ max (b-(t₀:ℝ)) ((t₀:ℝ)-a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
  refine ⟨n,⟨_,by positivity⟩,fun x => ⟨hn,?_⟩⟩
  exact LipschitzWith.of_dist_le_mul fun α β => iterate_dist t₀ hf hL x α β n

theorem exists_curve [CompleteSpace E] (x : E) :
    ∃ α : ℝ → E, Continuous α ∧ α t₀=x ∧
      ∀ t∈Icc a b, HasDerivWithinAt α (f t (α t)) (Icc a b) t := by
  obtain ⟨n,C,hC⟩ := contracting_iterate t₀ hf hL
  let α : Curve (a:=a) (b:=b) (E:=E) := (hC x).fixedPoint _
  have hα : IsFixedPt (next t₀ f hf x) α := (hC x).isFixedPt_fixedPoint_iterate
  have he (t : ℝ) (ht : t∈Icc a b) : extend t₀ α t=ODE.picard f t₀ x (extend t₀ α) t := by
    rw [extend_of_mem _ _ ht]
    exact (congrArg (fun g : Curve (a:=a) (b:=b) (E:=E) => g ⟨t,ht⟩) hα).symm
  refine ⟨extend t₀ α,extend_continuous t₀ α,?_,fun t ht => ?_⟩
  · rw [he t₀ t₀.2,ODE.picard_apply₀]
  · exact (ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn
      (extend_continuous t₀ α).continuousOn (fun _ _ => Set.mem_univ _) x ht).congr
        (fun s hs => he s hs) (he t ht)
end LogConcaveSampling.GlobalODE

namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {f : ℝ → E → E} {K : ℝ≥0}
  (hL : ∀ t∈Icc a b,LipschitzWith K (f t))

variable [CompleteSpace E] (hf : Continuous (uncurry f))

def flow (s : Icc a b) (x : E) : ℝ → E := (exists_curve s hf hL x).choose

end LogConcaveSampling.GlobalODE

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ContinuousFirstOrderReply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof

namespace LogConcaveSampling
open scoped RealInnerProductSpace

theorem quadratic_lower_bound_of_hasDerivAt {f g h : ℝ → ℝ} {a : ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (ha : ∀ t, a ≤ h t) :
    f 0 + g 0 + a / 2 ≤ f 1 := by
  have hd : ∀ t, HasDerivAt (fun s => g s - a * s) (h t - a) t := fun t => by
    convert! (hg t).sub ((hasDerivAt_id t).const_mul a) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hm : Monotone (fun t => g t - a * t) :=
    monotone_of_hasDerivAt_nonneg hd (fun t => sub_nonneg.mpr (ha t))
  have hgt : ∀ t, 0 ≤ t → g 0 + a * t ≤ g t := by
    intro t ht
    have hh := hm ht
    dsimp at hh
    linarith
  have he : ∀ t, HasDerivAt (fun s => f s - g 0 * s - a / 2 * s ^ 2)
      (g t - g 0 - a * t) t := fun t => by
    convert! ((hf t).sub ((hasDerivAt_id t).const_mul (g 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (a / 2)) using 1
    all_goals try with_reducible_and_instances rfl
    simp
    ring
  have hem : MonotoneOn (fun t => f t - g 0 * t - a / 2 * t ^ 2) (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ => (he t).continuousAt.continuousWithinAt)
      (fun t _ => (he t).hasDerivWithinAt)
      (fun t ht => by
        have ht0 : 0 ≤ t := Set.mem_Ici.mp (interior_subset ht)
        have := hgt t ht0
        linarith)
  have hend := hem (by simp : (0 : ℝ) ∈ Set.Ici 0) (by simp : (1 : ℝ) ∈ Set.Ici 0)
      (by norm_num : (0 : ℝ) ≤ 1)
  dsimp at hend
  norm_num at hend
  linarith

theorem quadratic_bounds_of_hasDerivAt {f g h : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (hb : ∀ t, a ≤ h t ∧ h t ≤ b) :
    f 0 + g 0 + a / 2 ≤ f 1 ∧ f 1 ≤ f 0 + g 0 + b / 2 := by
  refine ⟨quadratic_lower_bound_of_hasDerivAt hf hg (fun t => (hb t).1), ?_⟩
  have hn := quadratic_lower_bound_of_hasDerivAt
    (fun t => (hf t).neg) (fun t => (hg t).neg)
    (a := -b) (fun t => neg_le_neg (hb t).2)
  dsimp at hn
  linarith

theorem integrable_gaussian_envelope (d : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Point d => Real.exp (-b * ‖x‖ ^ 2)) := by
  have hg := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Point d) (b := (b : ℂ)) (by exact hb) 0 0).norm
  convert! hg using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp [Complex.norm_exp, ← Complex.ofReal_pow, ← Complex.ofReal_mul]

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_SymmetricGradientDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace

theorem ContDiff.isSymmetric_gradient_derivative {d : ℕ} {V : Point d → ℝ}
    (hV : ContDiff ℝ 2 V) (x : Point d) :
    (fderiv ℝ (gradient V) x).IsSymmetric := by
  have hg : ContDiff ℝ 1 (gradient V) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp
      (hV.fderiv_right (by norm_num))
  have hd := ((InnerProductSpace.toDual ℝ (Point d)).hasFDerivAt).comp x
    ((hg.differentiable (by norm_num) x).hasFDerivAt)
  have he : fderiv ℝ (fderiv ℝ V) x =
      (InnerProductSpace.toDual ℝ (Point d)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (gradient V) x) := by
    have hid := toDual_comp_gradient (𝕜 := ℝ) (f := V)
    rw [hid] at hd
    exact hd.fderiv
  have hs := (hV.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num [minSmoothness])
  intro v w
  have h := hs.eq v w
  rw [he] at h
  change inner ℝ ((fderiv ℝ (gradient V) x) v) w =
    inner ℝ v ((fderiv ℝ (gradient V) x) w)
  conv_rhs => rw [real_inner_comm]
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, InnerProductSpace.toDual_apply_apply] using h

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Primitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

theorem quadratic_bounds_on_segment {d : ℕ} {F : Point d → ℝ}
    (hF : ContDiff ℝ 2 F) {a b : ℝ}
    (hH : ∀ x v, a * ‖v‖ ^ 2 ≤ inner ℝ v (fderiv ℝ (gradient F) x v) ∧
      inner ℝ v (fderiv ℝ (gradient F) x v) ≤ b * ‖v‖ ^ 2)
    (x v : Point d) :
    F x + inner ℝ v (gradient F x) + a * ‖v‖ ^ 2 / 2 ≤ F (x + v) ∧
    F (x + v) ≤ F x + inner ℝ v (gradient F x) + b * ‖v‖ ^ 2 / 2 := by
  let f : ℝ → ℝ := fun t => F (x + t • v)
  let g : ℝ → ℝ := fun t => inner ℝ v (gradient F (x + t • v))
  let h : ℝ → ℝ := fun t => inner ℝ v (fderiv ℝ (gradient F) (x + t • v) v)
  have hp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := fun t => by
    convert! (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hgF : ContDiff ℝ 1 (gradient F) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp
      (hF.fderiv_right (by norm_num))
  have hdg := hgF.differentiable (by norm_num)
  have hf : ∀ t, HasDerivAt f (g t) t := by
    intro t
    have hh := ((hF.differentiable (by norm_num) (x + t • v)).hasFDerivAt).comp_hasDerivAt t (hp t)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    change inner ℝ v (gradient F (x + t • v)) = fderiv ℝ F (x + t • v) v
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hg : ∀ t, HasDerivAt g (h t) t := by
    intro t
    have hh := (hdg (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hp t)
    simpa [g, h, Function.comp_def] using (hasDerivAt_const t v).inner ℝ hh
  have ht := quadratic_bounds_of_hasDerivAt hf hg (fun t => hH (x + t • v) v)
  simpa only [f, g, zero_smul, one_smul, add_zero] using ht

theorem hessian_bounds_of_gradient_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hg : LipschitzWith lam (gradient F)) (x v : Point d) :
    -(lam : ℝ) * ‖v‖ ^ 2 ≤ inner ℝ v (fderiv ℝ (gradient F) x v) ∧
    inner ℝ v (fderiv ℝ (gradient F) x v) ≤ (lam : ℝ) * ‖v‖ ^ 2 := by
  have hb := (fderiv ℝ (gradient F) x).le_of_opNorm_le (norm_fderiv_le_of_lipschitz ℝ hg) v
  have hi := (abs_real_inner_le_norm v (fderiv ℝ (gradient F) x v)).trans
    (mul_le_mul_of_nonneg_left hb (norm_nonneg v))
  rw [abs_le] at hi
  constructor <;> nlinarith [hi.1, hi.2]

theorem quadratic_remainder_of_gradient_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : ContDiff ℝ 2 F) (hg : LipschitzWith lam (gradient F)) (x v : Point d) :
    |F (x + v) - F x - inner ℝ v (gradient F x)| ≤ (lam : ℝ) * ‖v‖ ^ 2 / 2 := by
  have hb := quadratic_bounds_on_segment hF (a := -(lam : ℝ)) (b := lam)
    (hessian_bounds_of_gradient_lipschitz hg) x v
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

structure Primitive {d : ℕ} (F : Point d → ℝ) (lam : ℝ≥0) : Prop where
  smooth : ContDiff ℝ 2 F
  gradient_lipschitz : LipschitzWith lam (gradient F)

def primitivePotential {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (z : Point d) : ℝ :=
  ‖z‖ ^ 2 / 2 + F (x + r • z)

def modeStep {d : ℕ} (g : Point d → Point d) (x : Point d) (r : ℝ) (z : Point d) : Point d :=
  -r • g (x + r • z)

def modeIterates {d : ℕ} (g : Point d → Point d) (x : Point d) (r : ℝ) (k : ℕ) : Point d :=
  (modeStep g x r)^[k] 0

theorem modeStep_lipschitz {d : ℕ} {g : Point d → Point d} {lam : ℝ≥0}
    (hg : LipschitzWith lam g) (x : Point d) {r : ℝ} (hr : 0 ≤ r) :
    LipschitzWith (lam * (NNReal.mk r hr) ^ 2) (modeStep g x r) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  dsimp [modeStep]
  rw [dist_smul₀, Real.norm_eq_abs, abs_neg, abs_of_nonneg hr]
  have h := hg.dist_le_mul (x + r • z) (x + r • w)
  rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hr] at h
  calc
    r * dist (g (x + r • z)) (g (x + r • w)) ≤ r * (lam * (r * dist z w)) :=
      mul_le_mul_of_nonneg_left h hr
    _ = ↑(lam * (NNReal.mk r hr) ^ 2) * dist z w := by simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_mk]; ring

theorem exists_mode_with_iteration_bound {d : ℕ} {g : Point d → Point d} {lam : ℝ≥0}
    (hg : LipschitzWith lam g) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam : ℝ) * r ^ 2 < 1) :
    ∃ z₀ : Point d,
      z₀ = -r • g (x + r • z₀) ∧
      (∀ z : Point d, z = -r • g (x + r • z) → z = z₀) ∧
      ‖z₀‖ ≤ r * ‖g x‖ / (1 - (lam : ℝ) * r ^ 2) ∧
      ∀ k : ℕ, ‖modeIterates g x r k - z₀‖ ≤
        ((lam : ℝ) * r ^ 2) ^ k * (r * ‖g x‖) / (1 - (lam : ℝ) * r ^ 2) := by
  let l : ℝ≥0 := lam * (NNReal.mk r hr) ^ 2
  have hl' : l < 1 := by exact_mod_cast hl
  have hc : ContractingWith l (modeStep g x r) := ⟨hl', modeStep_lipschitz hg x hr⟩
  let z₀ := hc.fixedPoint (modeStep g x r)
  refine ⟨z₀, hc.fixedPoint_isFixedPt.symm, ?_, ?_, ?_⟩
  · intro z hz
    exact hc.fixedPoint_unique hz.symm
  · have h := hc.dist_fixedPoint_le 0
    simpa [NNReal.coe_pow, z₀, l, dist_eq_norm, modeStep, norm_smul, abs_of_nonneg hr] using h
  · intro k
    have h := hc.apriori_dist_iterate_fixedPoint_le 0 k
    simpa [NNReal.coe_pow, z₀, modeIterates, l, dist_eq_norm, modeStep, norm_smul, abs_of_nonneg hr,
      mul_comm] using h

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_PrimitivePotentialModeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

theorem primitivePotential_mode_bounds {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    {z₀ : Point d} (hz : z₀ = -r • gradient F (x + r • z₀)) (v : Point d) :
    primitivePotential F x r z₀ + (1 - (lam : ℝ) * r ^ 2) * ‖v‖ ^ 2 / 2 ≤
      primitivePotential F x r (z₀ + v) ∧
    primitivePotential F x r (z₀ + v) ≤
      primitivePotential F x r z₀ + (1 + (lam : ℝ) * r ^ 2) * ‖v‖ ^ 2 / 2 := by
  have hb := quadratic_remainder_of_gradient_lipschitz hF.smooth hF.gradient_lipschitz
    (x + r • z₀) (r • v)
  rw [abs_le] at hb
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] at hb
  have hlin : inner ℝ z₀ v + inner ℝ (r • v) (gradient F (x + r • z₀)) = 0 := by
    conv_lhs => arg 1; rw [hz]
    simp only [real_inner_smul_left]
    rw [real_inner_comm]
    ring
  dsimp only [primitivePotential]
  rw [norm_add_sq_real, smul_add, ← add_assoc]
  constructor <;> nlinarith [hb.1, hb.2]

theorem Primitive.exists_unique_mode {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam : ℝ) * r ^ 2 < 1) :
    ∃ z₀ : Point d, z₀ = -r • gradient F (x + r • z₀) ∧
      (∀ z : Point d, primitivePotential F x r z₀ ≤ primitivePotential F x r z) ∧
      (∀ z : Point d, primitivePotential F x r z ≤ primitivePotential F x r z₀ → z = z₀) := by
  obtain ⟨z₀, hz, _, _, _⟩ := exists_mode_with_iteration_bound hF.gradient_lipschitz x hr hl
  refine ⟨z₀, hz, ?_, ?_⟩
  · intro z
    have hb := (primitivePotential_mode_bounds hF x hr hz (z - z₀)).1
    rw [add_sub_cancel] at hb
    have hn : 0 ≤ (1 - (lam : ℝ) * r ^ 2) * ‖z - z₀‖ ^ 2 / 2 := by positivity
    linarith
  · intro z hzmin
    have hb := (primitivePotential_mode_bounds hF x hr hz (z - z₀)).1
    rw [add_sub_cancel] at hb
    have hnorm : ‖z - z₀‖ = 0 := by
      have hp : 0 < 1 - (lam : ℝ) * r ^ 2 := by linarith
      have hmul : (1 - (lam : ℝ) * r ^ 2) * ‖z - z₀‖ ^ 2 ≤ 0 := by linarith
      rcases eq_or_lt_of_le (norm_nonneg (z - z₀)) with hn | hn
      · exact hn.symm
      · have hpos := mul_pos hp (sq_pos_of_pos hn)
        linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

theorem Primitive.continuous_potential {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r : ℝ) :
    Continuous (primitivePotential F x r) := by
  exact (continuous_norm.pow 2 |>.div_const 2).add
    (hF.smooth.continuous.comp (continuous_const.add (continuous_id.const_smul r)))

theorem Primitive.integrable_exp_neg_potential {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam : ℝ) * r ^ 2 < 1) :
    Integrable (fun z => Real.exp (-primitivePotential F x r z)) := by
  obtain ⟨z₀, hz, _, _⟩ := hF.exists_unique_mode x hr hl
  let a := (1 - (lam : ℝ) * r ^ 2) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hi := (integrable_gaussian_envelope d ha).comp_sub_right z₀
  apply (hi.const_mul (Real.exp (-primitivePotential F x r z₀))).mono'
    ((Real.continuous_exp.comp (hF.continuous_potential x r).neg).aestronglyMeasurable)
  filter_upwards [] with z
  change |Real.exp (-primitivePotential F x r z)| ≤ _
  rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  have hb := (primitivePotential_mode_bounds hF x hr hz (z - z₀)).1
  rw [add_sub_cancel] at hb
  apply Real.exp_le_exp.mpr
  dsimp [a]
  linarith

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace

lemma polynomial_gaussian_absorb {b x : ℝ} (hb : 0 < b) (_hx : 0 ≤ x) :
    x * Real.exp (-b*x) ≤ (2/b) * Real.exp (-(b/2)*x) := by
  have he : (b/2)*x ≤ Real.exp ((b/2)*x) := by
    linarith [Real.add_one_le_exp ((b/2)*x)]
  have he' := mul_le_mul_of_nonneg_right he (Real.exp_pos (-b*x)).le
  rw [← Real.exp_add] at he'
  have hexp : (b/2)*x + -b*x = -(b/2)*x := by ring
  rw [hexp] at he'
  have hbp : 0 < b/2 := by positivity
  have hh : (x * Real.exp (-b*x)) * (b/2) ≤ Real.exp (-(b/2)*x) := by nlinarith only [he']
  have hh' := (le_div_iff₀ hbp).mpr hh
  calc
    _ ≤ Real.exp (-(b/2)*x) / (b/2) := hh'
    _ = _ := by field_simp

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace

lemma partition_toReal {d : ℕ} {H : Point d → ℝ}
    (hi : Integrable (fun x => Real.exp (-H x))) :
    (partition H).toReal = ∫ x, Real.exp (-H x) := by
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-H x)).le)
    hi.aestronglyMeasurable).symm

lemma integral_gibbs {d : ℕ} {H : Point d → ℝ} (hc : Continuous H)
    (hi : Integrable (fun x => Real.exp (-H x))) (f : Point d → ℝ) :
    (∫ x, f x ∂gibbs H) = (∫ x, Real.exp (-H x) * f x) / ∫ x, Real.exp (-H x) := by
  rw [gibbs,integral_smul_measure,ENNReal.toReal_inv,partition_toReal hi]
  have hden : Measurable (gibbsDensity H) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hden
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f]
  simp only [gibbsDensity,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]
  ring

lemma integrable_gibbs_of_weighted {d : ℕ} {H f : Point d → ℝ} (hc : Continuous H)
    (hi : Integrable (fun x => Real.exp (-H x)))
    (hf : Integrable (fun x => Real.exp (-H x) * f x)) : Integrable f (gibbs H) := by
  have hp : partition H ≠ ⊤ := (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-H x)).le)).2 hi
  have hpos : 0 < partition H := by
    have hmeasure : Measurable (gibbsDensity H) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
    rw [partition,lintegral_pos_iff_support hmeasure]
    have hh : Function.support (gibbsDensity H) = Set.univ := by
      ext x
      simp [Function.mem_support,gibbsDensity,not_le_of_gt (Real.exp_pos (-H x))]
    rw [hh]
    exact isOpen_univ.measure_pos volume Set.univ_nonempty
  have hw : Integrable f (volume.withDensity (gibbsDensity H)) := by
    have hden : Measurable (gibbsDensity H) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
    rw [integrable_withDensity_iff_integrable_smul' hden
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [gibbsDensity,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul] using hf
  exact hw.smul_measure (by simpa using hpos.ne')

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PolynomialGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace

lemma integrable_even_norm_pow_gaussian (d n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Point d => ‖x‖^(2*n) * Real.exp (-b*‖x‖^2)) := by
  induction n generalizing b with
  | zero => simpa using integrable_gaussian_envelope d hb
  | succ n ih =>
      have hc : Continuous (fun x : Point d => ‖x‖^(2*(n+1)) * Real.exp (-b*‖x‖^2)) := by fun_prop
      apply ((ih (b := b/2) (by positivity)).const_mul (2/b)).mono' hc.aestronglyMeasurable
      filter_upwards [] with x
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hh := mul_le_mul_of_nonneg_left (polynomial_gaussian_absorb hb (sq_nonneg ‖x‖))
        (show 0 ≤ ‖x‖^(2*n) by positivity)
      convert! hh using 1 <;> simp only [Nat.mul_add,pow_add,pow_two] <;> ring

lemma integrable_norm_pow_gaussian (d n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Point d => ‖x‖^n * Real.exp (-b*‖x‖^2)) := by
  have hc : Continuous (fun x : Point d => ‖x‖^n * Real.exp (-b*‖x‖^2)) := by fun_prop
  apply ((integrable_gaussian_envelope d hb).add
    (integrable_even_norm_pow_gaussian d n hb)).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hh : ‖x‖^n ≤ 1+‖x‖^(2*n) := by
    rw [mul_comm 2 n,pow_mul]
    nlinarith [sq_nonneg (‖x‖^n-1)]
  simpa only [Pi.add_apply,one_mul,add_mul] using mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

def HasPolynomialGrowth {d : ℕ} {E : Type*} [NormedAddCommGroup E] (h : Point d → E) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, ∀ z, ‖h z‖ ≤ C*(1+‖z‖^n)

def HasGaussianLowerTail {d : ℕ} (H : Point d → ℝ) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∃ C : ℝ, ∀ z, m*‖z‖^2 ≤ H z + C

lemma gaussian_tilt_bound {d : ℕ} {H : Point d → ℝ} {m C M : ℝ}
    (hm : 0 < m) (_hM : 0 ≤ M) (ht : ∀ z, m*‖z‖^2 ≤ H z+C)
    {θ : Point d} (hθ : ‖θ‖ ≤ M) (z : Point d) :
    Real.exp (inner ℝ θ z-H z) ≤
      Real.exp (C+M^2/(2*m)) * Real.exp (-(m/2)*‖z‖^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hip := (real_inner_le_norm θ z).trans (mul_le_mul_of_nonneg_right hθ (norm_nonneg z))
  have hy : M*‖z‖ ≤ (m/2)*‖z‖^2+M^2/(2*m) := by
    have hh := sq_nonneg (m*‖z‖-M)
    have hd : M^2/(2*m)*(2*m) = M^2 := by field_simp
    nlinarith
  linarith [ht z]

section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma integrable_tilted (H : Point d → ℝ) {h : Point d → E}
    (hH : Continuous H) (hh : Continuous h) (ht : HasGaussianLowerTail H)
    (hg : HasPolynomialGrowth h) (θ : Point d) :
    Integrable (fun z => Real.exp (inner ℝ θ z-H z) • h z) := by
  obtain ⟨m,hm,C,ht⟩ := ht
  obtain ⟨K,hK,n,hg⟩ := hg
  let B := Real.exp (C+‖θ‖^2/(2*m)) * K
  apply (((integrable_gaussian_envelope d (b := m/2) (by positivity)).add
    (integrable_norm_pow_gaussian d n (b := m/2) (by positivity))).const_mul B).mono'
      ((Real.continuous_exp.comp ((continuous_const.inner continuous_id).sub hH)).smul hh).aestronglyMeasurable
  filter_upwards [] with z
  change ‖Real.exp (inner ℝ θ z-H z) • h z‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he := mul_le_mul (gaussian_tilt_bound hm (norm_nonneg θ) ht le_rfl z)
    (hg z) (norm_nonneg _) (by positivity)
  convert! he using 1; dsimp [B]; ring

end
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_EulerDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open MeasureTheory Filter
open scoped RealInnerProductSpace NNReal ENNReal Topology

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}

theorem Primitive.contDiff_potential (hF : Primitive F lam) (x : Point d) (r : ℝ) :
    ContDiff ℝ 2 (primitivePotential F x r) :=
  ((contDiff_norm_sq ℝ).div_const 2).add
    (hF.smooth.comp (contDiff_const.add (contDiff_id.const_smul r)))

theorem Primitive.gradient_potential (hF : Primitive F lam) (x : Point d) (r : ℝ)
    (z : Point d) : gradient (primitivePotential F x r) z = z+r • gradient F (x+r • z) := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have ha : HasFDerivAt (fun w : Point d => x+r • w)
      (0+r • ContinuousLinearMap.id ℝ (Point d)) z :=
    (hasFDerivAt_const x z).add ((hasFDerivAt_id z).const_smul r)
  have hb := (hF.smooth.differentiable (by norm_num) (x+r • z)).hasFDerivAt.comp z ha
  have hd := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_smul (1/2 : ℝ)).add hb
  convert! hd using 1
  · funext w
    simp only [primitivePotential,Pi.add_apply,Pi.smul_apply,Function.comp_apply,smul_eq_mul]
    ring
  ext v
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,zero_add,
    ContinuousLinearMap.id_apply,smul_eq_mul,InnerProductSpace.toDual_apply_apply,
    inner_add_left,real_inner_smul_left,innerSL_apply_apply,
    map_smul,← toDual_gradient]
  ring

theorem Primitive.gradient_potential_lipschitz (hF : Primitive F lam)
    (x : Point d) {r : ℝ} (hr : 0 ≤ r) :
    LipschitzWith (1+lam*(NNReal.mk r hr)^2) (gradient (primitivePotential F x r)) := by
  have hh := LipschitzWith.id.add (modeStep_lipschitz hF.gradient_lipschitz x hr).neg
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [hF.gradient_potential,Pi.neg_apply,modeStep,neg_smul,neg_neg,id_eq]

theorem Primitive.gaussianLowerTail (hF : Primitive F lam) (x : Point d) {r : ℝ}
    (hr : 0 ≤ r) (hl : (lam:ℝ)*r^2 < 1) : HasGaussianLowerTail (primitivePotential F x r) := by
  let m := 1-(lam:ℝ)*r^2
  let a := r*‖gradient F x‖
  have hm : 0 < m := sub_pos.mpr hl
  refine ⟨m/4,by positivity,a^2/m-F x,fun z => ?_⟩
  have hb := quadratic_remainder_of_gradient_lipschitz hF.smooth hF.gradient_lipschitz x (r • z)
  rw [abs_le] at hb
  have hc := abs_real_inner_le_norm (r • z) (gradient F x)
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] at hb hc
  have hy := sq_nonneg (m*‖z‖-2*a)
  have hdiv : a^2/m*m=a^2 := div_mul_cancel₀ _ hm.ne'
  have hin : -a*‖z‖ ≤ inner ℝ (r • z) (gradient F x) := by
    have hh := neg_abs_le (inner ℝ (r • z) (gradient F x))
    dsimp [a]
    nlinarith only [hc,hh]
  dsimp only [primitivePotential]
  dsimp [m] at *
  nlinarith [mul_nonneg (show 0 ≤ 1-(lam:ℝ)*r^2 by linarith) (sq_nonneg ‖z‖)]

lemma partition_pos_of_continuous {H : Point d → ℝ} (hc : Continuous H) : 0 < partition H := by
  have hm : Measurable (gibbsDensity H) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
  rw [partition,lintegral_pos_iff_support hm]
  have hs : Function.support (gibbsDensity H) = Set.univ := by
    ext z
    simp [Function.mem_support,gibbsDensity,not_le_of_gt (Real.exp_pos (-H z))]
  rw [hs]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty

lemma partition_ne_top_of_integrable {H : Point d → ℝ}
    (hi : Integrable (fun z => Real.exp (-H z))) : partition H ≠ ⊤ :=
  (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => (Real.exp_pos (-H z)).le)).2 hi

lemma probability_gibbs_of_partition {H : Point d → ℝ}
    (hp : partition H ≠ 0) (ht : partition H ≠ ⊤) : IsProbabilityMeasure (gibbs H) := by
  constructor
  rw [gibbs,Measure.smul_apply,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel hp ht

lemma lipschitz_sq_norm_growth {g : Point d → Point d} {M : ℝ≥0} (hg : LipschitzWith M g) :
    HasPolynomialGrowth (fun z => ‖g z‖^2) := by
  refine ⟨2*((M:ℝ)^2+‖g 0‖^2),by positivity,2,fun z => ?_⟩
  have hb : ‖g z‖ ≤ (M:ℝ)*‖z‖+‖g 0‖ := by
    have hh := hg.dist_le_mul z 0
    rw [dist_eq_norm,dist_zero_right] at hh
    linarith only [norm_le_norm_sub_add (g z) (g 0),hh]
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hp := pow_le_pow_left₀ (norm_nonneg _) hb 2
  nlinarith [sq_nonneg ((M:ℝ)*‖z‖-‖g 0‖),mul_nonneg (sq_nonneg ‖g 0‖) (sq_nonneg ‖z‖)]

theorem Primitive.gradient_sq_integrable (hF : Primitive F lam) (x : Point d) {r : ℝ}
    (hr : 0 ≤ r) (hl : (lam:ℝ)*r^2 < 1) :
    Integrable (fun z => ‖gradient (primitivePotential F x r) z‖^2)
      (gibbs (primitivePotential F x r)) := by
  have hg := hF.gradient_potential_lipschitz x hr
  apply integrable_gibbs_of_weighted (hF.continuous_potential x r)
    (hF.integrable_exp_neg_potential x hr hl)
  have hh := integrable_tilted (primitivePotential F x r)
    (hF.continuous_potential x r) (hg.continuous.norm.pow 2)
    (hF.gaussianLowerTail x hr hl) (lipschitz_sq_norm_growth hg) 0
  simpa only [inner_zero_left,zero_sub,smul_eq_mul,Pi.pow_apply] using hh

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

def eulerDrift {d : ℕ} (H : Point d → ℝ) (h : ℝ) (z : Point d) : Point d :=
  z-h • gradient H z

lemma Primitive.eulerDrift_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r h : ℝ) (z : Point d) :
    eulerDrift (primitivePotential F x r) h z =
      (1-h) • z+h • modeStep (gradient F) x r z := by
  rw [eulerDrift,hF.gradient_potential]
  dsimp [modeStep]
  module

lemma Primitive.eulerDrift_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    LipschitzWith ⟨1-h+h*((lam:ℝ)*r^2),by positivity⟩
      (eulerDrift (primitivePotential F x r) h) := by
  have hl := modeStep_lipschitz hF.gradient_lipschitz x hr
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [hF.eulerDrift_eq]
  have hb := dist_add_add_le ((1-h) • z) (h • modeStep (gradient F) x r z)
    ((1-h) • w) (h • modeStep (gradient F) x r w)
  simp only [dist_smul₀, Real.norm_eq_abs,abs_of_nonneg hh,
    abs_of_nonneg (sub_nonneg.mpr hh1)] at hb
  have hd := hl.dist_le_mul z w
  simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_mk] at hd
  change _ ≤ (1-h+h*((lam:ℝ)*r^2))*dist z w
  nlinarith only [hb,mul_le_mul_of_nonneg_left hd hh]

lemma Primitive.contDiff_eulerDrift {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r h : ℝ) :
    ContDiff ℝ 1 (eulerDrift (primitivePotential F x r) h) := by
  have hg : ContDiff ℝ 1 (gradient F) := by
    have hd : ContDiff ℝ 1 (fderiv ℝ F) := hF.smooth.fderiv_right (by norm_num)
    exact (InnerProductSpace.toDual ℝ (Point d)).symm.toContinuousLinearEquiv.contDiff.comp hd
  have he : eulerDrift (primitivePotential F x r) h = fun z =>
      (1-h) • z+h • (-r • gradient F (x+r • z)) := by
    funext z
    exact hF.eulerDrift_eq x r h z
  rw [he]
  exact (contDiff_id.const_smul (1-h)).add
    (((hg.comp (contDiff_const.add (contDiff_id.const_smul r))).const_smul (-r)).const_smul h)

end LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace GaussianPoincare
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rotation (θ : ℝ) : E × E →L[ℝ] E × E :=
  ((Real.cos θ • ContinuousLinearMap.fst ℝ E E) +
    (Real.sin θ • ContinuousLinearMap.snd ℝ E E)).prod
  ((-Real.sin θ • ContinuousLinearMap.fst ℝ E E) +
    (Real.cos θ • ContinuousLinearMap.snd ℝ E E))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma rotation_apply (θ : ℝ) (x y : E) :
    rotation θ (x,y) = (Real.cos θ • x+Real.sin θ • y,
      -Real.sin θ • x+Real.cos θ • y) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rotation_energy (θ : ℝ) (x y : E) :
    ‖Real.cos θ • x+Real.sin θ • y‖^2+
      ‖-Real.sin θ • x+Real.cos θ • y‖^2 = ‖x‖^2+‖y‖^2 := by
  simp only [norm_add_sq_real,real_inner_smul_left,real_inner_smul_right,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rotation_gaussian (θ : ℝ) :
    ((stdGaussian E).prod (stdGaussian E)).map (rotation θ) =
      (stdGaussian E).prod (stdGaussian E) := by
  apply Measure.ext_of_charFunDual
  ext L
  let L₁ := L.comp (ContinuousLinearMap.inl ℝ E E)
  let L₂ := L.comp (ContinuousLinearMap.inr ℝ E E)
  have h₁ : (L.comp (rotation θ)).comp (ContinuousLinearMap.inl ℝ E E) =
      Real.cos θ • L₁ + (-Real.sin θ) • L₂ := by
    ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
      rotation_apply,smul_zero,add_zero]
    change L (Real.cos θ • x,-Real.sin θ • x) = _
    have hp : (Real.cos θ • x,-Real.sin θ • x) =
        Real.cos θ • (x,0) + (-Real.sin θ) • (0,x) := by simp
    rw [hp,L.map_add,L.map_smul,L.map_smul]
    rfl
  have h₂ : (L.comp (rotation θ)).comp (ContinuousLinearMap.inr ℝ E E) =
      Real.sin θ • L₁ + Real.cos θ • L₂ := by
    ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
      rotation_apply,smul_zero,zero_add]
    change L (Real.sin θ • x,Real.cos θ • x) = _
    have hp : (Real.sin θ • x,Real.cos θ • x) =
        Real.sin θ • (x,0) + Real.cos θ • (0,x) := by simp
    rw [hp,L.map_add,L.map_smul,L.map_smul]
    rfl
  rw [charFunDual_map,charFunDual_prod,h₁,h₂,charFunDual_prod]
  simp only [charFunDual_stdGaussian]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  have he := rotation_energy (-θ) ((InnerProductSpace.toDual ℝ E).symm L₁)
    ((InnerProductSpace.toDual ℝ E).symm L₂)
  simp only [← map_smul,← map_add,LinearIsometryEquiv.norm_map] at he
  simp only [Real.cos_neg,Real.sin_neg,neg_neg] at he
  norm_cast
  dsimp [L₁,L₂] at *
  linarith

lemma integral_dual_sq (L : StrongDual ℝ E) :
    ∫ x, (L x)^2 ∂stdGaussian E = ‖L‖^2 := by
  have hm : MemLp L 2 (stdGaussian E) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian E)).continuousLinearMap_comp L
  have hv := variance_dual_stdGaussian L
  rw [variance_eq_sub hm,integral_strongDual_stdGaussian,zero_pow (by norm_num),sub_zero] at hv
  exact hv

lemma interval_integral_sq_le {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ}
    (hf : Continuous f) : (∫ t in 0..T, f t)^2 ≤ T*∫ t in 0..T, (f t)^2 := by
  let j := ∫ t in 0..T, f t
  have hi := hf.intervalIntegrable (μ := volume) 0 T
  have hi2 : IntervalIntegrable (fun t => (f t)^2) volume 0 T :=
    (hf.pow 2).intervalIntegrable (μ := volume) 0 T
  have hp : 0 ≤ ∫ t in 0..T, (T*f t-j)^2 :=
    intervalIntegral.integral_nonneg hT.le (fun t _ => sq_nonneg _)
  have he : (fun t => (T*f t-j)^2) =
      fun t => T^2*(f t)^2-2*T*j*f t+j^2 := by funext t; ring_nf
  have hs : IntervalIntegrable (fun t => T^2*(f t)^2-2*T*j*f t) volume 0 T :=
    (hi2.const_mul _).sub (hi.const_mul _)
  rw [he,intervalIntegral.integral_add hs (intervalIntegrable_const),
    intervalIntegral.integral_sub (hi2.const_mul _) (hi.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hp
  dsimp [j] at *
  simp only [sub_zero] at hp
  nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rotation_first_deriv (θ : ℝ) (x y : E) : HasDerivAt
    (fun t => (rotation t (x,y)).1) ((rotation θ (x,y)).2) θ := by
  convert! ((Real.hasDerivAt_cos θ).smul_const x).add
    ((Real.hasDerivAt_sin θ).smul_const y) using 1
  all_goals try with_reducible_and_instances rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma along_rotation_deriv {h : E → ℝ} (hh : ContDiff ℝ 1 h) (x y : E) (θ : ℝ) :
    HasDerivAt (fun t => h ((rotation t (x,y)).1))
      (fderiv ℝ h ((rotation θ (x,y)).1) ((rotation θ (x,y)).2)) θ :=
  (hh.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt θ
    (rotation_first_deriv θ x y)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rotation_difference_bound {h : E → ℝ} (hh : ContDiff ℝ 1 h) (x y : E) :
    (h y-h x)^2 ≤ (Real.pi/2)*∫ θ in 0..Real.pi/2,
      (fderiv ℝ h ((rotation θ (x,y)).1) ((rotation θ (x,y)).2))^2 := by
  have hc : Continuous (fun θ =>
      fderiv ℝ h ((rotation θ (x,y)).1) ((rotation θ (x,y)).2)) := by
    have hd := hh.continuous_fderiv (by norm_num)
    exact (hd.comp (by simp only [rotation_apply]; fun_prop)).clm_apply
      (by simp only [rotation_apply]; fun_prop)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => along_rotation_deriv hh x y θ) (hc.intervalIntegrable 0 (Real.pi/2))
  simp only [rotation_apply,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,
    add_zero,Real.cos_pi_div_two,Real.sin_pi_div_two,zero_add] at he
  rw [← he]
  exact interval_integral_sq_le (by positivity) hc

lemma memLp_lipschitz {h : E → ℝ} {K : ℝ≥0} (hl : LipschitzWith K h) :
    MemLp h 2 (stdGaussian E) := by
  have hl₀ : LipschitzWith K (fun x => h x-h 0) :=
    LipschitzWith.of_dist_le_mul (fun x y => by simpa using hl.dist_le_mul x y)
  have hm := hl₀.comp_memLp (by simp) (IsGaussian.memLp_two_id (μ := stdGaussian E))
  have hp : MemLp (fun x => h x-h 0+h 0) 2 (stdGaussian E) :=
    hm.add (memLp_const (h 0))
  simpa only [sub_add_cancel] using hp

lemma independent_difference_variance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {h : Ω → ℝ} (hm : MemLp h 2 μ) :
    ∫ xy, (h xy.1-h xy.2)^2 ∂μ.prod μ = 2*Var[h;μ] := by
  have hi := hm.integrable (by norm_num)
  have hi2 := hm.integrable_sq
  have hc := hi.mul_prod hi
  have he : (fun xy : Ω × Ω => (h xy.1-h xy.2)^2) =
      fun xy => (h xy.1)^2-2*(h xy.1*h xy.2)+(h xy.2)^2 := by
    funext xy; ring_nf
  have hs : Integrable (fun xy : Ω × Ω => (h xy.1)^2-2*(h xy.1*h xy.2))
      (μ.prod μ) := (hi2.comp_fst μ).sub (hc.const_mul 2)
  rw [he,integral_add hs (hi2.comp_snd μ),
    integral_sub (hi2.comp_fst μ) (hc.const_mul 2),integral_const_mul,
    integral_fun_fst (μ := μ) (ν := μ) (fun x => h x^2),
    integral_fun_snd (μ := μ) (ν := μ) (fun x => h x^2),
    integral_prod_mul,variance_eq_sub hm]
  simp only [probReal_univ,one_smul,Pi.pow_apply]
  ring_nf

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma tangent_sq_bound {h : E → ℝ} {K : ℝ≥0} (hl : LipschitzWith K h)
    (θ : ℝ) (x y : E) :
    (fderiv ℝ h ((rotation θ (x,y)).1) ((rotation θ (x,y)).2))^2 ≤
      2*(K:ℝ)^2*(‖x‖^2+‖y‖^2) := by
  have hD := norm_fderiv_le_of_lipschitz ℝ hl (x₀ := (rotation θ (x,y)).1)
  have h₁ := (fderiv ℝ h ((rotation θ (x,y)).1)).le_opNorm ((rotation θ (x,y)).2)
  have h₂ : ‖(rotation θ (x,y)).2‖ ≤ ‖x‖+‖y‖ := by
    simp only [rotation_apply]
    calc
      ‖-Real.sin θ • x+Real.cos θ • y‖ ≤ ‖-Real.sin θ • x‖+‖Real.cos θ • y‖ := norm_add_le _ _
      _ ≤ ‖x‖+‖y‖ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_neg]
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg x) (Real.abs_sin_le_one θ))
          (mul_le_of_le_one_left (norm_nonneg y) (Real.abs_cos_le_one θ))
  have hb : ‖fderiv ℝ h ((rotation θ (x,y)).1) ((rotation θ (x,y)).2)‖ ≤
      (K:ℝ)*(‖x‖+‖y‖) := h₁.trans ((mul_le_mul_of_nonneg_right hD (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left h₂ K.coe_nonneg))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simp only [Real.norm_eq_abs,sq_abs,mul_pow] at hsq
  nlinarith [mul_nonneg (sq_nonneg (K:ℝ)) (sq_nonneg (‖x‖-‖y‖))]

lemma unrotated_integrable {h : E → ℝ} (hh : ContDiff ℝ 1 h)
    {K : ℝ≥0} (hl : LipschitzWith K h) :
    Integrable (fun xy : E × E => (fderiv ℝ h xy.1 xy.2)^2)
      ((stdGaussian E).prod (stdGaussian E)) := by
  have hn : Integrable (fun y : E => ‖y‖^2) (stdGaussian E) :=
    IsGaussian.memLp_two_id.norm.integrable_sq
  refine ((hn.comp_snd (stdGaussian E)).const_mul ((K:ℝ)^2)).mono'
    (by exact ((hh.continuous_fderiv (by norm_num)).comp continuous_fst |>.clm_apply
      continuous_snd |>.pow 2).aestronglyMeasurable) ?_
  filter_upwards [] with xy
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hb := (fderiv ℝ h xy.1).le_opNorm xy.2
  have hc := norm_fderiv_le_of_lipschitz ℝ hl (x₀ := xy.1)
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hb.trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))) 2
  simpa only [Real.norm_eq_abs,sq_abs,mul_pow] using hs

lemma integral_tangent_sq {h : E → ℝ} (hh : ContDiff ℝ 1 h)
    {K : ℝ≥0} (hl : LipschitzWith K h) (θ : ℝ) :
    ∫ xy : E × E, (fderiv ℝ h ((rotation θ xy).1) ((rotation θ xy).2))^2
      ∂(stdGaussian E).prod (stdGaussian E) =
    ∫ x, ‖fderiv ℝ h x‖^2 ∂stdGaussian E := by
  have hc : Continuous (fun xy : E × E => (fderiv ℝ h xy.1 xy.2)^2) :=
    ((hh.continuous_fderiv (by norm_num)).comp continuous_fst |>.clm_apply continuous_snd).pow 2
  rw [← integral_map (rotation θ).continuous.aemeasurable hc.aestronglyMeasurable,
    rotation_gaussian,integral_prod _ (unrotated_integrable hh hl)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => integral_dual_sq (fderiv ℝ h x))

lemma tangent_time_integrable {h : E → ℝ} (hh : ContDiff ℝ 1 h)
    {K : ℝ≥0} (hl : LipschitzWith K h) (T : ℝ) :
    Integrable (fun p : ℝ × (E × E) =>
      (fderiv ℝ h ((rotation p.1 p.2).1) ((rotation p.1 p.2).2))^2)
      ((volume.restrict (Set.uIoc 0 T)).prod
        ((stdGaussian E).prod (stdGaussian E))) := by
  have hn : Integrable (fun y : E => ‖y‖^2) (stdGaussian E) :=
    IsGaussian.memLp_two_id.norm.integrable_sq
  let : IsFiniteMeasure (volume.restrict (Set.uIoc 0 T)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
  have hb := ((hn.comp_fst (stdGaussian E)).add
    (hn.comp_snd (stdGaussian E))).const_mul (2*(K:ℝ)^2)
  refine (hb.comp_snd (volume.restrict (Set.uIoc 0 T))).mono' ?_ ?_
  · have hc : Continuous (fun p : ℝ × (E × E) =>
        (fderiv ℝ h ((rotation p.1 p.2).1) ((rotation p.1 p.2).2))^2) := by
      refine Continuous.pow (Continuous.clm_apply
        ((hh.continuous_fderiv (by norm_num)).comp ?_) ?_) 2
      · change Continuous (fun p : ℝ × (E × E) => Real.cos p.1 • p.2.1 +
          Real.sin p.1 • p.2.2)
        fun_prop
      · change Continuous (fun p : ℝ × (E × E) => -Real.sin p.1 • p.2.1 +
          Real.cos p.1 • p.2.2)
        fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with p
    change ‖(fderiv ℝ h ((rotation p.1 p.2).1) ((rotation p.1 p.2).2))^2‖ ≤
      2*(K:ℝ)^2*(‖p.2.1‖^2+‖p.2.2‖^2)
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact tangent_sq_bound hl p.1 p.2.1 p.2.2

theorem variance_le_gradient {h : E → ℝ} (hh : ContDiff ℝ 1 h)
    {K : ℝ≥0} (hl : LipschitzWith K h) :
    Var[h;stdGaussian E] ≤ (Real.pi^2/8)*
      ∫ x, ‖fderiv ℝ h x‖^2 ∂stdGaussian E := by
  let μ := (stdGaussian E).prod (stdGaussian E)
  let T := Real.pi/2
  have hT : 0 < T := by dsimp [T]; positivity
  have hi := tangent_time_integrable hh hl T
  have hinner : Integrable (fun xy : E × E => ∫ θ in 0..T,
      (fderiv ℝ h ((rotation θ xy).1) ((rotation θ xy).2))^2) μ := by
    simp only [intervalIntegral.integral_of_le hT.le]
    simpa only [Set.uIoc_of_le hT.le,Function.comp_apply,Prod.swap_prod_mk] using
      hi.swap.integral_prod_left
  have hdiff : Integrable (fun xy : E × E => (h xy.1-h xy.2)^2) μ := by
    exact ((memLp_lipschitz hl).comp_fst (stdGaussian E) |>.sub
      ((memLp_lipschitz hl).comp_snd (stdGaussian E))).integrable_sq
  have hb : (∫ xy : E × E, (h xy.1-h xy.2)^2 ∂μ) ≤
      T*∫ xy : E × E, (∫ θ in 0..T,
        (fderiv ℝ h ((rotation θ xy).1) ((rotation θ xy).2))^2) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hdiff (hinner.const_mul T)
    intro xy
    dsimp only
    have he : (h xy.1-h xy.2)^2 = (h xy.2-h xy.1)^2 := by ring_nf
    rw [he]
    exact rotation_difference_bound hh xy.1 xy.2
  dsimp [μ] at hb
  rw [independent_difference_variance (stdGaussian E) (memLp_lipschitz hl),
    ← intervalIntegral_integral_swap hi] at hb
  simp_rw [integral_tangent_sq hh hl] at hb
  rw [intervalIntegral.integral_const] at hb
  simp only [sub_zero,smul_eq_mul] at hb
  dsimp [T] at hb
  nlinarith

end GaussianPoincare
end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerGeometry
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def iterate (T : E → E) (σ : ℝ) : (n : ℕ) → E → (Fin n → E) → E
  | 0, x, _ => x
  | n+1, x, g => T (iterate T σ n x (fun i => g i.castSucc)) + σ • g (Fin.last n)

def energy (q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => q^2*energy q n+1

lemma energy_nonneg {q : ℝ} (n : ℕ) : 0 ≤ energy q n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [energy]; positivity

lemma energy_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    energy q n ≤ (1-q^2)⁻¹ := by
  have hp : 0 < 1-q^2 := by nlinarith
  induction n with
  | zero => simp only [energy]; positivity
  | succ n ih =>
      rw [energy]
      calc
        q^2*energy q n+1 ≤ q^2*(1-q^2)⁻¹+1 := by gcongr
        _ = (1-q^2)⁻¹ := by
          have hh := mul_inv_cancel₀ hp.ne'
          nlinarith only [hh]

lemma initial_contraction {q : ℝ≥0} {T : E → E} (hT : LipschitzWith q T)
    (σ : ℝ) (n : ℕ) (x y : E) (g : Fin n → E) :
    dist (iterate T σ n x g) (iterate T σ n y g) ≤ (q:ℝ)^n*dist x y := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
      simp only [iterate,dist_add_right]
      calc
        _ ≤ (q:ℝ)*dist (iterate T σ n x (fun i => g i.castSucc))
          (iterate T σ n y (fun i => g i.castSucc)) := hT.dist_le_mul _ _
        _ ≤ (q:ℝ)*((q:ℝ)^n*dist x y) :=
          mul_le_mul_of_nonneg_left (ih _) q.coe_nonneg
        _ = _ := by rw [pow_succ]; ring_nf

lemma noise_sensitivity {q : ℝ≥0} {T : E → E} (hT : LipschitzWith q T)
    {σ : ℝ} (hσ : 0 ≤ σ) (n : ℕ) (x : E) (g k : Fin n → E) :
    dist (iterate T σ n x g) (iterate T σ n x k) ≤
      σ*Real.sqrt (energy q n)*Real.sqrt (∑ i, dist (g i) (k i)^2) := by
  induction n with
  | zero => simp [iterate,energy]
  | succ n ih =>
      let D := ∑ i : Fin n, dist (g i.castSucc) (k i.castSucc)^2
      let b := dist (g (Fin.last n)) (k (Fin.last n))
      let S := energy (q:ℝ) n
      have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hS : 0 ≤ S := energy_nonneg n
      have hb : 0 ≤ b := dist_nonneg
      have hd : dist (iterate T σ (n+1) x g) (iterate T σ (n+1) x k) ≤
          σ*((q:ℝ)*Real.sqrt S*Real.sqrt D+b) := by
        calc
          _ ≤ dist (T (iterate T σ n x (fun i => g i.castSucc)))
              (T (iterate T σ n x (fun i => k i.castSucc))) +
              dist (σ • g (Fin.last n)) (σ • k (Fin.last n)) := dist_add_add_le _ _ _ _
          _ ≤ (q:ℝ)*dist (iterate T σ n x (fun i => g i.castSucc))
                (iterate T σ n x (fun i => k i.castSucc)) + σ*b := by
            rw [dist_smul₀,Real.norm_eq_abs,abs_of_nonneg hσ]
            exact add_le_add (hT.dist_le_mul _ _) le_rfl
          _ ≤ (q:ℝ)*(σ*Real.sqrt S*Real.sqrt D)+σ*b := by
            exact add_le_add (mul_le_mul_of_nonneg_left (ih _ _) q.coe_nonneg) le_rfl
          _ = _ := by ring_nf
      have hc : ((q:ℝ)*Real.sqrt S*Real.sqrt D+b)^2 ≤
          ((q:ℝ)^2*S+1)*(D+b^2) := by
        calc
          _ ≤ (((q:ℝ)*Real.sqrt S)^2+1)*((Real.sqrt D)^2+b^2) := by
            nlinarith [sq_nonneg ((q:ℝ)*Real.sqrt S*b-Real.sqrt D)]
          _ = _ := by rw [mul_pow,Real.sq_sqrt hS,Real.sq_sqrt hD]
      have hr : (q:ℝ)*Real.sqrt S*Real.sqrt D+b ≤
          Real.sqrt ((q:ℝ)^2*S+1)*Real.sqrt (D+b^2) := by
        have hp : 0 ≤ Real.sqrt ((q:ℝ)^2*S+1)*Real.sqrt (D+b^2) := by positivity
        have he : (Real.sqrt ((q:ℝ)^2*S+1)*Real.sqrt (D+b^2))^2 =
            ((q:ℝ)^2*S+1)*(D+b^2) := by
          rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
        nlinarith
      rw [energy,Fin.sum_univ_castSucc]
      exact hd.trans (by nlinarith [mul_le_mul_of_nonneg_left hr hσ])

lemma noise_lipschitz {q : ℝ≥0} {T : E → E} (hT : LipschitzWith q T)
    (σ : ℝ≥0) (n : ℕ) (x : E) :
    LipschitzWith ⟨(σ:ℝ)*Real.sqrt (energy q n),by positivity⟩
      (fun g : PiLp 2 (fun _ : Fin n => E) => iterate T σ n x g) := by
  apply LipschitzWith.of_dist_le_mul
  intro g k
  have hh := noise_sensitivity hT σ.coe_nonneg n x (fun i => g i) (fun i => k i)
  rw [← PiLp.dist_sq_eq_of_L2,Real.sqrt_sq (dist_nonneg)] at hh
  exact hh

lemma contDiff_iterate {T : E → E} (hT : ContDiff ℝ 1 T) (σ : ℝ) (n : ℕ)
    {x : F → E} (hx : ContDiff ℝ 1 x) {g : F → Fin n → E}
    (hg : ∀ i, ContDiff ℝ 1 (fun z => g z i)) :
    ContDiff ℝ 1 (fun z => iterate T σ n (x z) (g z)) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      exact (hT.comp (ih (fun i => hg i.castSucc))).add ((hg (Fin.last n)).const_smul σ)

lemma contDiff_noise {T : E → E} (hT : ContDiff ℝ 1 T) (σ : ℝ) (n : ℕ) (x : E) :
    ContDiff ℝ 1 (fun g : PiLp 2 (fun _ : Fin n => E) => iterate T σ n x g) := by
  apply contDiff_iterate hT σ n contDiff_const
  intro i
  exact (PiLp.proj 2 (fun _ : Fin n => E) i : PiLp 2 (fun _ : Fin n => E) →L[ℝ] E).contDiff

end EulerGeometry
end LogConcaveSampling

namespace LogConcaveSampling
namespace GaussianPoincare
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ F] in

theorem variance_lipschitz_image {T : E → F} (hT : ContDiff ℝ 1 T)
    {A : ℝ≥0} (hA : LipschitzWith A T) {h : F → ℝ} (hh : ContDiff ℝ 1 h)
    {K : ℝ≥0} (hK : LipschitzWith K h) :
    Var[h; (stdGaussian E).map T] ≤ (Real.pi^2/8)*(A:ℝ)^2*
      ∫ y, ‖fderiv ℝ h y‖^2 ∂(stdGaussian E).map T := by
  rw [variance_map hh.continuous.measurable.aemeasurable hT.continuous.measurable.aemeasurable]
  have hb := variance_le_gradient (hh.comp hT) (hK.comp hA)
  have hi : Integrable (fun x : E => ‖fderiv ℝ (h ∘ T) x‖^2) (stdGaussian E) := by
    apply Integrable.mono' (integrable_const (((K*A:ℝ≥0):ℝ)^2))
      (((hh.comp hT).continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ (hK.comp hA)) 2
  have hj : Integrable (fun x : E => (A:ℝ)^2*‖fderiv ℝ h (T x)‖^2) (stdGaussian E) := by
    apply Integrable.mono' (integrable_const ((A:ℝ)^2*(K:ℝ)^2))
      (((hh.continuous_fderiv (by norm_num)).comp hT.continuous |>.norm.pow 2).const_mul
        ((A:ℝ)^2) |>.aestronglyMeasurable)
    filter_upwards [] with x
    change ‖(A:ℝ)^2*‖fderiv ℝ h (T x)‖^2‖ ≤ (A:ℝ)^2*(K:ℝ)^2
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hK) 2) (sq_nonneg _)
  have he : (∫ x, ‖fderiv ℝ (h ∘ T) x‖^2 ∂stdGaussian E) ≤
      (A:ℝ)^2*∫ x, ‖fderiv ℝ h (T x)‖^2 ∂stdGaussian E := by
    rw [← integral_const_mul]
    apply integral_mono hi hj
    intro x
    dsimp only
    rw [fderiv_comp x (hh.differentiable (by norm_num) (T x))
      (hT.differentiable (by norm_num) x)]
    have hb' := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ h (T x)) (fderiv ℝ T x)
    have hs : ‖(fderiv ℝ h (T x)).comp (fderiv ℝ T x)‖ ≤ ‖fderiv ℝ h (T x)‖*(A:ℝ) :=
      hb'.trans (mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hA) (norm_nonneg _))
    have hc := pow_le_pow_left₀ (norm_nonneg _) hs 2
    simpa only [mul_pow,mul_comm] using hc
  have hmap : (∫ y, ‖fderiv ℝ h y‖^2 ∂(stdGaussian E).map T) =
      ∫ x, ‖fderiv ℝ h (T x)‖^2 ∂stdGaussian E :=
    integral_map hT.continuous.aemeasurable
      (((hh.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable)
  rw [hmap]
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ Real.pi^2/8 by positivity)])

end GaussianPoincare
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_LintegralFinNatProd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling

lemma lintegral_fin_nat_prod {n : ℕ} {E : Type*}
    [MeasurableSpace E] {μ : Fin n → Measure E}
    [∀ i, SigmaFinite (μ i)] (f : Fin n → E → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂Measure.pi μ =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : E × (Fin n → E),
          f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
          ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
        rw [((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_map_equiv]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ i.succ := by
        rw [lintegral_prod_mul (g := fun x : Fin n → E => ∏ i, f i.succ (x i))
          (hf 0).aemeasurable
          (Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable, ih _ (fun i => hf _)]
      _ = _ := by rw [Fin.prod_univ_succ]

theorem pi_withDensity_fin {n : ℕ} {E : Type*}
    [MeasurableSpace E] (μ : Fin n → Measure E)
    [∀ i, SigmaFinite (μ i)] (f : Fin n → E → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [Measure.restrict_pi_pi]
  rw [lintegral_fin_nat_prod _ hf]
  apply Finset.prod_congr rfl
  intro i _
  exact (withDensity_apply _ (hs i)).symm

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling

theorem map_withDensity_of_measurePreserving {E F : Type*}
    [MeasurableSpace E] [MeasurableSpace F] {μ : Measure E} {ν : Measure F}
    (e : E ≃ᵐ F) (he : MeasurePreserving e μ ν) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = ν.withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs]
  have h := he.setLIntegral_comp_preimage hs (hf.comp e.symm.measurable)
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using h

end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerDensity
open ProbabilityTheory MeasureTheory WithLp
open scoped ENNReal NNReal RealInnerProductSpace

def gaussianCoefficient (d : ℕ) : ℝ≥0∞ :=
  ∏ _ : Fin d, ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹)

lemma standard_pi_density (d : ℕ) :
    Measure.pi (fun _ : Fin d => gaussianReal 0 1) =
      (volume : Measure (Fin d → ℝ)).withDensity
        (fun x => gaussianCoefficient d*ENNReal.ofReal (Real.exp (-(∑ k, (x k)^2)/2))) := by
  have hg : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero _ (by norm_num)
  have : IsProbabilityMeasure (volume.withDensity (gaussianPDF 0 1)) := by rw [← hg]; infer_instance
  simp_rw [hg]
  rw [pi_withDensity_fin _ _ (fun _ => measurable_gaussianPDF _ _)]
  congr 1
  ext x
  have he (z : ℝ) : gaussianPDF 0 1 z =
      ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹)*ENNReal.ofReal (Real.exp (-z^2/2)) := by
    simp [gaussianPDF,gaussianPDFReal]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div,Finset.sum_neg_distrib]

theorem standard_density (d : ℕ) :
    stdGaussian (Point d) = gaussianCoefficient d •
      (volume : Measure (Point d)).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-‖z‖^2/2))) := by
  rw [← map_pi_eq_stdGaussian,standard_pi_density]
  let e : (Fin d → ℝ) ≃ᵐ Point d := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  change Measure.map e _ = _
  rw [map_withDensity_of_measurePreserving e (PiLp.volume_preserving_toLp (Fin d)) (by fun_prop)]
  have he : (fun y : Point d => gaussianCoefficient d*
      ENNReal.ofReal (Real.exp (-(∑ k, (e.symm y k)^2)/2))) =
      gaussianCoefficient d • (fun z : Point d => ENNReal.ofReal (Real.exp (-‖z‖^2/2))) := by
    funext y
    simp only [Pi.smul_apply,smul_eq_mul]
    congr 3
    change -(∑ k, (y k)^2)/2 = -‖y‖^2/2
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs,sq_abs]
  rw [he,withDensity_smul]
  fun_prop

lemma gaussianCoefficient_positive (d : ℕ) : 0 < gaussianCoefficient d := by
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)

lemma gaussianCoefficient_finite (d : ℕ) : gaussianCoefficient d ≠ ⊤ := by
  exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)

def shear {d : ℕ} (T : Point d → Point d) (hT : Measurable T) :
    Point d × Point d ≃ᵐ Point d × Point d where
  toFun p := (p.1,T p.1+p.2)
  invFun p := (p.1,p.2-T p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun := measurable_fst.prodMk ((hT.comp measurable_fst).add measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub (hT.comp measurable_fst))

lemma shear_measurePreserving {d : ℕ} {T : Point d → Point d} (hT : Measurable T) :
    MeasurePreserving (shear T hT) ((volume : Measure (Point d)).prod volume)
      ((volume : Measure (Point d)).prod volume) := by
  exact (MeasurePreserving.id volume).skew_product ((hT.comp measurable_fst).add measurable_snd)
    (Filter.Eventually.of_forall (fun x => map_add_left_eq_self volume (T x)))

end EulerDensity
end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerDensity
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

lemma map_withDensity_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (e : E ≃ᵐ F) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) :=
  map_withDensity_of_measurePreserving e ⟨e.measurable,rfl⟩ hf

def noiseCoefficient (d : ℕ) (σ : ℝ) : ℝ≥0∞ :=
  gaussianCoefficient d*ENNReal.ofReal |(σ^d)⁻¹|

lemma scaled_standard_density (d : ℕ) {σ : ℝ} (hσ : σ ≠ 0) :
    (stdGaussian (Point d)).map (fun z => σ • z) =
      noiseCoefficient d σ • (volume : Measure (Point d)).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-‖z‖^2/(2*σ^2)))) := by
  let e := (Homeomorph.smulOfNeZero (α := Point d) σ hσ).toMeasurableEquiv
  rw [standard_density,Measure.map_smul]
  change gaussianCoefficient d • (Measure.map e _) = _
  rw [map_withDensity_equiv volume e (by fun_prop)]
  have he : (volume : Measure (Point d)).map e =
      ENNReal.ofReal |(σ^d)⁻¹| • volume := by
    convert! Measure.map_addHaar_smul (volume : Measure (Point d)) hσ using 1
    all_goals try with_reducible_and_instances rfl
    simp [Point]
  rw [he,withDensity_smul_measure,smul_smul]
  congr 2
  funext z
  have hz : e.symm z = σ⁻¹ • z := by
    exact congrFun (Homeomorph.smulOfNeZero_symm_apply hσ) z
  rw [hz,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  congr 2
  field_simp

lemma noiseCoefficient_positive (d : ℕ) {σ : ℝ} (hσ : σ ≠ 0) :
    0 < noiseCoefficient d σ := by
  apply ENNReal.mul_pos_iff.mpr
  exact ⟨gaussianCoefficient_positive d,ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hσ)))⟩

lemma noiseCoefficient_finite (d : ℕ) (σ : ℝ) : noiseCoefficient d σ ≠ ⊤ :=
  ENNReal.mul_ne_top (gaussianCoefficient_finite d) ENNReal.ofReal_ne_top

theorem joint_density {d : ℕ} {H : Point d → ℝ} (hH : Measurable H)
    (T : Point d → Point d) (hT : Measurable T) {σ : ℝ} (hσ : σ ≠ 0) :
    ((gibbs H).prod (stdGaussian (Point d))).map (fun p => (p.1,T p.1+σ • p.2)) =
      ((partition H)⁻¹*noiseCoefficient d σ) •
        ((volume : Measure (Point d)).prod volume).withDensity
          (fun p => ENNReal.ofReal (Real.exp (-H p.1-‖p.2-T p.1‖^2/(2*σ^2)))) := by
  have : SFinite (gibbs H) := by unfold gibbs; infer_instance
  have hmap : ((gibbs H).prod (stdGaussian (Point d))).map
      (fun p => (p.1,T p.1+σ • p.2)) =
      (((gibbs H).prod ((stdGaussian (Point d)).map (fun z => σ • z))).map (shear T hT)) := by
    have hj := Measure.map_prod_map (gibbs H) (stdGaussian (Point d)) measurable_id
      (show Measurable (fun z : Point d => σ • z) by fun_prop)
    simp only [Measure.map_id] at hj
    rw [hj,Measure.map_map (shear T hT).measurable (by fun_prop)]
    rfl
  rw [hmap,scaled_standard_density d hσ]
  unfold gibbs
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,
    prod_withDensity (by unfold gibbsDensity; fun_prop) (by fun_prop),
    Measure.map_smul,
    map_withDensity_of_measurePreserving (shear T hT) (shear_measurePreserving hT) (by unfold gibbsDensity; fun_prop)]
  congr 2
  funext p
  change ENNReal.ofReal (Real.exp (-H p.1))*
    ENNReal.ofReal (Real.exp (-‖p.2-T p.1‖^2/(2*σ^2))) = _
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

end EulerDensity
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
namespace Trapezoid
open scoped RealInnerProductSpace Topology
open Asymptotics

variable {d : ℕ} {H : Point d → ℝ}

def remainder (H : Point d → ℝ) (x y : Point d) : ℝ :=
  H y-H x-inner ℝ (y-x) (gradient H x+gradient H y)/2

lemma contDiff_gradient (hH : ContDiff ℝ 2 H) : ContDiff ℝ 1 (gradient H) :=
  (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp
    (hH.fderiv_right (by norm_num))

lemma hasFDerivAt_remainder (hH : ContDiff ℝ 2 H) (x y : Point d) :
    HasFDerivAt (remainder H x)
      (InnerProductSpace.toDual ℝ (Point d)
        ((1/2:ℝ) • (gradient H y-gradient H x-fderiv ℝ (gradient H) y (y-x)))) y := by
  have hg := contDiff_gradient hH
  have hd := (hasFDerivAt_id y).sub_const x |>.inner ℝ
    ((hasFDerivAt_const (gradient H x) y).add
      (hg.differentiable (by norm_num) y).hasFDerivAt)
  have hh := ((hH.differentiable (by norm_num) y).hasFDerivAt.sub_const (H x)).sub
    (hd.const_mul (1/2:ℝ))
  convert! hh using 1
  · funext z; dsimp [remainder]; ring
  ext z
  have hs : inner ℝ (fderiv ℝ (gradient H) y (y-x)) z =
      inner ℝ (y-x) (fderiv ℝ (gradient H) y z) :=
    LogConcaveSampling.ContDiff.isSymmetric_gradient_derivative hH y (y-x) z
  have hgrad : fderiv ℝ H y z = inner ℝ (gradient H y) z :=
    InnerProductSpace.toDual_symm_apply.symm
  simp only [InnerProductSpace.toDual_apply_apply, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    fderivInnerCLM_apply, Pi.add_apply, id_eq, zero_add, smul_eq_mul]
  change inner ℝ ((1/2:ℝ) • (gradient H y-gradient H x-fderiv ℝ (gradient H) y (y-x))) z =
    fderiv ℝ H y z-(1/2:ℝ)*(inner ℝ (y-x) (fderiv ℝ (gradient H) y z)+
      inner ℝ z (gradient H x+gradient H y))
  rw [real_inner_smul_left,inner_sub_left,inner_sub_left,hgrad,← hs,inner_add_right]
  nlinarith [real_inner_comm z (gradient H x),real_inner_comm z (gradient H y)]

lemma derivative_remainder_littleO (hH : ContDiff ℝ 2 H) (x : Point d) :
    (fun y => InnerProductSpace.toDual ℝ (Point d)
      ((1/2:ℝ) • (gradient H y-gradient H x-fderiv ℝ (gradient H) y (y-x))))
      =o[𝓝 x] (fun y => ‖y-x‖) := by
  have hg := contDiff_gradient hH
  have hl := (hg.differentiable (by norm_num) x).hasFDerivAt.isLittleO
  have hc := (hg.continuous_fderiv (by norm_num)).continuousAt (x := x)
  rw [Asymptotics.isLittleO_iff]
  intro c hcpos
  have he₁ := hl.bound hcpos
  have he₂ : ∀ᶠ y in 𝓝 x, ‖fderiv ℝ (gradient H) y-fderiv ℝ (gradient H) x‖ < c := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hc c hcpos)
  filter_upwards [he₁,he₂] with y hy hz
  rw [LinearIsometryEquiv.norm_map,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),norm_norm]
  have hid : gradient H y-gradient H x-fderiv ℝ (gradient H) y (y-x) =
      (gradient H y-gradient H x-fderiv ℝ (gradient H) x (y-x))-
      (fderiv ℝ (gradient H) y-fderiv ℝ (gradient H) x) (y-x) := by
    simp only [sub_apply]; abel
  rw [hid]
  have hb := norm_sub_le (gradient H y-gradient H x-fderiv ℝ (gradient H) x (y-x))
    ((fderiv ℝ (gradient H) y-fderiv ℝ (gradient H) x) (y-x))
  have hh := (fderiv ℝ (gradient H) y-fderiv ℝ (gradient H) x).le_opNorm (y-x)
  have hc' := mul_le_mul_of_nonneg_right hz.le (norm_nonneg (y-x))
  nlinarith only [hy,hb,hh,hc']

theorem remainder_littleO (hH : ContDiff ℝ 2 H) (x : Point d) :
    remainder H x =o[𝓝 x] (fun y => ‖y-x‖^2) := by
  have hl := derivative_remainder_littleO hH x
  have hh := convex_univ.isLittleO_pow_succ (n := 1) (Set.mem_univ x)
    (fun y _ => (hasFDerivAt_remainder hH x y).hasFDerivWithinAt)
    (by simpa only [nhdsWithin_univ,pow_one] using hl)
  change (fun y => H y-H x-inner ℝ (y-x) (gradient H x+gradient H y)/2) =o[𝓝 x] (fun y => ‖y-x‖^2)
  simpa [remainder] using hh

lemma remainder_bound (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) (x y : Point d) :
    |remainder H x y| ≤ (M:ℝ)*‖y-x‖^2 := by
  have ht := quadratic_remainder_of_gradient_lipschitz hH hM x (y-x)
  rw [add_sub_cancel] at ht
  have hnorm : ‖gradient H y-gradient H x‖ ≤ (M:ℝ)*‖y-x‖ := hM.norm_sub_le y x
  have hi := (abs_real_inner_le_norm (y-x) (gradient H y-gradient H x)).trans
    (mul_le_mul_of_nonneg_left hnorm (norm_nonneg (y-x)))
  have he : remainder H x y =
      (H y-H x-inner ℝ (y-x) (gradient H x))-
        inner ℝ (y-x) (gradient H y-gradient H x)/2 := by
    dsimp [remainder]
    rw [inner_add_right,inner_sub_right]
    ring
  rw [he]
  have hb := abs_sub (H y-H x-inner ℝ (y-x) (gradient H x))
    (inner ℝ (y-x) (gradient H y-gradient H x)/2)
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at hb
  nlinarith only [hb,ht,hi]

end Trapezoid
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_ProposalLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
namespace EulerDefect
open scoped RealInnerProductSpace Topology
open Asymptotics

variable {d : ℕ} {H : Point d → ℝ}

def proposalLog (H : Point d → ℝ) (h : ℝ) (x y : Point d) : ℝ :=
  -H x-‖y-x+h • gradient H x‖^2/(4*h)

def proposal (H : Point d → ℝ) (s : ℝ) (x z : Point d) : Point d :=
  x-s^2 • gradient H x+(Real.sqrt 2*s) • z

lemma log_ratio (h : ℝ) (hh : h ≠ 0) (x y : Point d) :
    proposalLog H h x y-proposalLog H h y x =
      Trapezoid.remainder H x y+h/4*(‖gradient H y‖^2-‖gradient H x‖^2) := by
  have he : x-y = -(y-x) := by abel
  simp only [proposalLog,Trapezoid.remainder,he,norm_add_sq_real,norm_neg,norm_smul,
    Real.norm_eq_abs,real_inner_smul_right,inner_neg_left,inner_add_right,mul_pow,sq_abs]
  field_simp
  ring

lemma proposal_displacement (s : ℝ) (x z : Point d) :
    proposal H s x z-x = -s^2 • gradient H x+(Real.sqrt 2*s) • z := by
  dsimp [proposal]
  simp only [neg_smul]
  abel

lemma proposal_zero (x z : Point d) : proposal H 0 x z = x := by simp [proposal]

lemma differentiable_proposal (x z : Point d) : Differentiable ℝ (fun s => proposal H s x z) := by
  unfold proposal
  fun_prop

lemma continuous_proposal (x z : Point d) : Continuous (fun s => proposal H s x z) :=
  (differentiable_proposal x z).continuous

lemma remainder_scaled_tendsto (hH : ContDiff ℝ 2 H) (x z : Point d) :
    Filter.Tendsto (fun s => Trapezoid.remainder H x (proposal H s x z)/s^2) (𝓝 0) (𝓝 0) := by
  have ht : Filter.Tendsto (fun s => proposal H s x z) (𝓝 0) (𝓝 x) := by
    simpa only [proposal_zero] using (continuous_proposal (H := H) x z).tendsto 0
  have hl := (Trapezoid.remainder_littleO hH x).comp_tendsto ht
  have hb := (differentiable_proposal (H := H) x z 0).hasDerivAt.isBigO_sub.norm_left.pow 2
  simp only [proposal_zero,sub_zero] at hb
  exact (hl.trans_isBigO hb).tendsto_div_nhds_zero

lemma scaled_log_ratio (s : ℝ) (x z : Point d) :
    (proposalLog H (s^2) x (proposal H s x z)-
      proposalLog H (s^2) (proposal H s x z) x)/s^2 =
    Trapezoid.remainder H x (proposal H s x z)/s^2+
      (‖gradient H (proposal H s x z)‖^2-‖gradient H x‖^2)/4 := by
  by_cases hs : s = 0
  · subst s; simp [proposal_zero]
  rw [log_ratio (s^2) (pow_ne_zero _ hs)]
  field_simp

theorem scaled_log_ratio_tendsto (hH : ContDiff ℝ 2 H) (x z : Point d) :
    Filter.Tendsto (fun s =>
      (proposalLog H (s^2) x (proposal H s x z)-
        proposalLog H (s^2) (proposal H s x z) x)/s^2) (𝓝 0) (𝓝 0) := by
  simp_rw [scaled_log_ratio]
  have ht : Filter.Tendsto (fun s => proposal H s x z) (𝓝 0) (𝓝 x) := by
    simpa only [proposal_zero] using (continuous_proposal (H := H) x z).tendsto 0
  have hg := (Trapezoid.contDiff_gradient hH).continuous
  have hn := ((hg.tendsto x).comp ht).norm.pow 2
  have hdiff := (hn.sub_const (‖gradient H x‖^2)).div_const 4
  simpa only [sub_self,zero_div,add_zero,Function.comp_apply] using
    (remainder_scaled_tendsto hH x z).add hdiff

lemma displacement_bound {s : ℝ} (hs : |s| ≤ 1) (x z : Point d) :
    ‖proposal H s x z-x‖ ≤ |s| *(‖gradient H x‖+Real.sqrt 2*‖z‖) := by
  rw [proposal_displacement]
  have ht := norm_add_le (-s^2 • gradient H x) ((Real.sqrt 2*s) • z)
  simp only [norm_smul,Real.norm_eq_abs,abs_neg,abs_pow,abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg 2)] at ht
  have hh : |s|^2 ≤ |s| := by nlinarith [abs_nonneg s]
  have hb := mul_le_mul_of_nonneg_right hh (norm_nonneg (gradient H x))
  nlinarith only [ht,hb]

lemma gradient_norm_sq_difference_bound {M : ℝ≥0} (hM : LipschitzWith M (gradient H))
    (x y : Point d) :
    |‖gradient H y‖^2-‖gradient H x‖^2| ≤
      (M:ℝ)*‖y-x‖*(2*‖gradient H x‖+(M:ℝ)*‖y-x‖) := by
  have hd := hM.norm_sub_le y x
  have hn := norm_sub_norm_le (gradient H y) (gradient H x)
  have hab := abs_norm_sub_norm_le (gradient H y) (gradient H x)
  have hgy : ‖gradient H y‖ ≤ ‖gradient H x‖+(M:ℝ)*‖y-x‖ := by linarith
  have he : ‖gradient H y‖^2-‖gradient H x‖^2 =
      (‖gradient H y‖-‖gradient H x‖)*(‖gradient H y‖+‖gradient H x‖) := by ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ ‖gradient H y‖+‖gradient H x‖)]
  exact mul_le_mul (hab.trans hd) (by linarith) (by positivity) (by positivity)

lemma scaled_log_ratio_bound (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) {s : ℝ} (hs : |s| ≤ 1) (x z : Point d) :
    |(proposalLog H (s^2) x (proposal H s x z)-
      proposalLog H (s^2) (proposal H s x z) x)/s^2| ≤
    (M:ℝ)*(‖gradient H x‖+Real.sqrt 2*‖z‖)^2+
      (M:ℝ)*(‖gradient H x‖+Real.sqrt 2*‖z‖)*
        (2*‖gradient H x‖+(M:ℝ)*(‖gradient H x‖+Real.sqrt 2*‖z‖))/4 := by
  rw [scaled_log_ratio]
  let A := ‖gradient H x‖+Real.sqrt 2*‖z‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd := displacement_bound (H := H) hs x z
  have hdA : ‖proposal H s x z-x‖ ≤ A :=
    hd.trans (by exact mul_le_of_le_one_left hA hs)
  have hterm : |Trapezoid.remainder H x (proposal H s x z)/s^2| ≤ (M:ℝ)*A^2 := by
    by_cases hs0 : s = 0
    · simp [hs0]; positivity
    rw [abs_div,abs_of_nonneg (sq_nonneg s)]
    apply (div_le_iff₀ (sq_pos_of_ne_zero hs0)).mpr
    have hb := Trapezoid.remainder_bound hH hM x (proposal H s x z)
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2) M.coe_nonneg
    rw [mul_pow,sq_abs] at hh
    dsimp [A] at *
    nlinarith only [hb,hh]
  have hg := gradient_norm_sq_difference_bound hM x (proposal H s x z)
  have hmul : (M:ℝ)*‖proposal H s x z-x‖*(2*‖gradient H x‖+(M:ℝ)*‖proposal H s x z-x‖) ≤
      (M:ℝ)*A*(2*‖gradient H x‖+(M:ℝ)*A) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hdA M.coe_nonneg
    · linarith [mul_le_mul_of_nonneg_left hdA M.coe_nonneg]
    · positivity
    · positivity
  have ht := abs_add_le (Trapezoid.remainder H x (proposal H s x z)/s^2)
    ((‖gradient H (proposal H s x z)‖^2-‖gradient H x‖^2)/4)
  apply ht.trans
  apply add_le_add hterm
  simpa only [abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)] using
    div_le_div_of_nonneg_right (hg.trans hmul) (by norm_num : (0:ℝ) ≤ 4)

lemma quadratic_dominator_bound (M : ℝ≥0) (x z : Point d) :
    (M:ℝ)*(‖gradient H x‖+Real.sqrt 2*‖z‖)^2+
      (M:ℝ)*(‖gradient H x‖+Real.sqrt 2*‖z‖)*
        (2*‖gradient H x‖+(M:ℝ)*(‖gradient H x‖+Real.sqrt 2*‖z‖))/4 ≤
    (6*(M:ℝ)+M^2)*(‖gradient H x‖^2+‖z‖^2) := by
  let A := ‖gradient H x‖+Real.sqrt 2*‖z‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hg : ‖gradient H x‖ ≤ A := by
    exact le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hs : A^2 ≤ 4*(‖gradient H x‖^2+‖z‖^2) := by
    dsimp [A]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      sq_nonneg (‖gradient H x‖-Real.sqrt 2*‖z‖),sq_nonneg ‖gradient H x‖]
  have hh : (M:ℝ)*A*‖gradient H x‖ ≤ (M:ℝ)*A^2 := by
    simpa only [pow_two,mul_assoc] using mul_le_mul_of_nonneg_left hg (mul_nonneg M.coe_nonneg hA)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (M:ℝ)+(M:ℝ)/2+(M:ℝ)^2/4 by positivity)
  change (M:ℝ)*A^2+(M:ℝ)*A*(2*‖gradient H x‖+(M:ℝ)*A)/4 ≤ _
  nlinarith only [hh,hm]

open MeasureTheory ProbabilityTheory in

theorem expected_scaled_log_ratio_tendsto (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) (μ : Measure (Point d)) [IsFiniteMeasure μ]
    (hi : Integrable (fun x => ‖gradient H x‖^2) μ) :
    Filter.Tendsto (fun s => ∫ p : Point d × Point d,
      |(proposalLog H (s^2) p.1 (proposal H s p.1 p.2)-
        proposalLog H (s^2) (proposal H s p.1 p.2) p.1)/s^2|
      ∂μ.prod (stdGaussian (Point d))) (𝓝 0) (𝓝 0) := by
  have hg := (Trapezoid.contDiff_gradient hH).continuous
  have hz : Integrable (fun z : Point d => ‖z‖^2) (stdGaussian (Point d)) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian (Point d))).norm.integrable_sq
  have hb := ((hi.comp_fst (stdGaussian (Point d))).add (hz.comp_snd μ)).const_mul
    (6*(M:ℝ)+(M:ℝ)^2)
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ := μ.prod (stdGaussian (Point d))) (l := 𝓝 (0:ℝ))
    (f := fun _ => (0:ℝ))
    (fun p : Point d × Point d => (6*(M:ℝ)+(M:ℝ)^2)*(‖gradient H p.1‖^2+‖p.2‖^2))
    (F := fun s p => |(proposalLog H (s^2) p.1 (proposal H s p.1 p.2)-
      proposalLog H (s^2) (proposal H s p.1 p.2) p.1)/s^2|) ?_ ?_ hb ?_
  · simpa only [integral_zero] using hh
  · apply Filter.Eventually.of_forall
    intro s
    have hcont : Continuous (fun p : Point d × Point d =>
        |(proposalLog H (s^2) p.1 (proposal H s p.1 p.2)-
          proposalLog H (s^2) (proposal H s p.1 p.2) p.1)/s^2|) := by
      unfold proposalLog proposal
      fun_prop
    exact hcont.aestronglyMeasurable
  · have hs : ∀ᶠ s : ℝ in 𝓝 0, |s| ≤ 1 := by
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with s hs
      have hh : |s| < 1 := by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hs
      exact hh.le
    filter_upwards [hs] with s hs
    filter_upwards [] with p
    rw [Real.norm_eq_abs,abs_abs]
    exact (scaled_log_ratio_bound hH hM hs p.1 p.2).trans (quadratic_dominator_bound M p.1 p.2)
  · filter_upwards [] with p
    simpa only [abs_zero] using (scaled_log_ratio_tendsto hH p.1 p.2).abs

end EulerDefect
end LogConcaveSampling

namespace LogConcaveSampling
namespace MetropolisBalance

lemma exp_gap (a b : ℝ) :
    |Real.exp a-Real.exp b| ≤ (Real.exp a+Real.exp b)*|a-b| := by
  wlog hab : b ≤ a generalizing a b
  · simpa only [abs_sub_comm,add_comm] using this b a (le_of_not_ge hab)
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hab)),
    abs_of_nonneg (sub_nonneg.mpr hab)]
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b-a)) (Real.exp_pos a).le
  have he : Real.exp a*Real.exp (b-a) = Real.exp b := by rw [← Real.exp_add]; ring_nf
  rw [he] at hh
  nlinarith [mul_nonneg (Real.exp_pos b).le (sub_nonneg.mpr hab)]

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

def defectWeight (H : Ω × Ω → ℝ) (p : Ω × Ω) : ℝ :=
  Real.exp (H p)*|H p-H p.swap|

lemma reverse_defect_integrable {H : Ω × Ω → ℝ}
    (hi : Integrable (defectWeight H) (μ.prod μ)) :
    Integrable (fun p => Real.exp (H p.swap)*|H p-H p.swap|) (μ.prod μ) := by
  convert! hi.swap using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  simp only [defectWeight,Function.comp_apply,Prod.swap_swap,abs_sub_comm]

lemma integral_reverse_defect {H : Ω × Ω → ℝ} :
    (∫ p, Real.exp (H p.swap)*|H p-H p.swap| ∂μ.prod μ) =
      ∫ p, defectWeight H p ∂μ.prod μ := by
  have he : (fun p : Ω × Ω => Real.exp (H p.swap)*|H p-H p.swap|) =
      fun p => defectWeight H p.swap := by
    funext p
    simp only [defectWeight,Prod.swap_swap,abs_sub_comm]
  rw [he,integral_prod_swap]

lemma density_gap_integrable {H : Ω × Ω → ℝ} (hm : Measurable H)
    (hi : Integrable (defectWeight H) (μ.prod μ)) :
    Integrable (fun p => |Real.exp (H p)-Real.exp (H p.swap)|) (μ.prod μ) := by
  refine (hi.add (reverse_defect_integrable μ hi)).mono' (by fun_prop) ?_
  filter_upwards [] with p
  rw [Real.norm_eq_abs,abs_abs]
  have hh := exp_gap (H p) (H p.swap)
  dsimp [defectWeight]
  nlinarith only [hh]

lemma density_gap_bound {H : Ω × Ω → ℝ} (hm : Measurable H)
    (hi : Integrable (defectWeight H) (μ.prod μ)) :
    (∫ p, |Real.exp (H p)-Real.exp (H p.swap)| ∂μ.prod μ) ≤
      2*∫ p, defectWeight H p ∂μ.prod μ := by
  have hrev := reverse_defect_integrable μ hi
  have hb : (∫ p, |Real.exp (H p)-Real.exp (H p.swap)| ∂μ.prod μ) ≤
      ∫ p, defectWeight H p+Real.exp (H p.swap)*|H p-H p.swap| ∂μ.prod μ := by
    apply integral_mono (density_gap_integrable μ hm hi) (hi.add hrev)
    intro p
    dsimp [defectWeight]
    nlinarith only [exp_gap (H p) (H p.swap)]
  rw [integral_add hi hrev,integral_reverse_defect] at hb
  linarith only [hb]

omit [SFinite μ] in
lemma weighted_bounded_integrable {H : Ω × Ω → ℝ} (hm : Measurable H)
    (hi : Integrable (fun p => Real.exp (H p)) (μ.prod μ))
    {f : Ω × Ω → ℝ} (hf : Measurable f) {B : ℝ} (_hB : 0 ≤ B)
    (hb : ∀ p, |f p| ≤ B) :
    Integrable (fun p => Real.exp (H p)*f p) (μ.prod μ) := by
  refine (hi.mul_const B).mono' (by fun_prop) ?_
  filter_upwards [] with p
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb p) (Real.exp_pos _).le

theorem one_step_defect {H : Ω × Ω → ℝ} (hm : Measurable H)
    (hi : Integrable (fun p => Real.exp (H p)) (μ.prod μ))
    (hR : Integrable (defectWeight H) (μ.prod μ))
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) :
    |(∫ p : Ω × Ω, Real.exp (H p)*f p.2 ∂μ.prod μ)-
      ∫ p : Ω × Ω, Real.exp (H p)*f p.1 ∂μ.prod μ| ≤
      2*B*∫ p, defectWeight H p ∂μ.prod μ := by
  have h₁ : Integrable (fun p : Ω × Ω => Real.exp (H p)*f p.2) (μ.prod μ) :=
    weighted_bounded_integrable μ hm hi (hf.comp measurable_snd) hB (fun p => hb p.2)
  have h₂ : Integrable (fun p : Ω × Ω => Real.exp (H p.swap)*f p.2) (μ.prod μ) :=
    weighted_bounded_integrable μ (hm.comp measurable_swap) hi.swap
      (hf.comp measurable_snd) hB (fun p => hb p.2)
  have he : (∫ p : Ω × Ω, Real.exp (H p)*f p.1 ∂μ.prod μ) =
      ∫ p : Ω × Ω, Real.exp (H p.swap)*f p.2 ∂μ.prod μ := by
    rw [← integral_prod_swap (fun p : Ω × Ω => Real.exp (H p)*f p.1)]
    rfl
  rw [he,← integral_sub h₁ h₂]
  have hd := density_gap_integrable μ hm hR
  have hn : (∫ p : Ω × Ω, |Real.exp (H p)*f p.2-Real.exp (H p.swap)*f p.2| ∂μ.prod μ) ≤
      B*∫ p, |Real.exp (H p)-Real.exp (H p.swap)| ∂μ.prod μ := by
    rw [← integral_const_mul]
    apply integral_mono (h₁.sub h₂).abs (hd.const_mul B)
    intro p
    change |Real.exp (H p)*f p.2-Real.exp (H p.swap)*f p.2| ≤
      B*|Real.exp (H p)-Real.exp (H p.swap)|
    rw [← sub_mul,abs_mul]
    exact mul_le_mul (le_refl _) (hb p.2) (abs_nonneg _) (abs_nonneg _) |>.trans_eq (mul_comm _ _)
  have hh := norm_integral_le_integral_norm
    (fun p : Ω × Ω => Real.exp (H p)*f p.2-Real.exp (H p.swap)*f p.2) (μ := μ.prod μ)
  simp only [Real.norm_eq_abs] at hh
  have hg := mul_le_mul_of_nonneg_left (density_gap_bound μ hm hR) hB
  nlinarith only [hh,hn,hg]

end MetropolisBalance
end LogConcaveSampling

namespace LogConcaveSampling
namespace MetropolisBalance
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

def densityLaw (c : ℝ≥0∞) (H : Ω × Ω → ℝ) : Measure (Ω × Ω) :=
  c • (μ.prod μ).withDensity (fun p => ENNReal.ofReal (Real.exp (H p)))

omit [SFinite μ] in
lemma densityLaw_integral {H : Ω × Ω → ℝ} (hm : Measurable H) (c : ℝ≥0∞)
    (f : Ω × Ω → ℝ) :
    (∫ p, f p ∂densityLaw μ c H) = c.toReal*∫ p, Real.exp (H p)*f p ∂μ.prod μ := by
  rw [densityLaw,integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]

omit [SFinite μ] in
lemma densityLaw_integrable {H : Ω × Ω → ℝ} (hm : Measurable H) {c : ℝ≥0∞}
    (hc : c ≠ 0) (hct : c ≠ ⊤) (f : Ω × Ω → ℝ) :
    Integrable f (densityLaw μ c H) ↔ Integrable (fun p => Real.exp (H p)*f p) (μ.prod μ) := by
  rw [densityLaw,integrable_smul_measure hc hct,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]

theorem probability_one_step_defect {H : Ω × Ω → ℝ} (hm : Measurable H) {c : ℝ≥0∞}
    (hc : c ≠ 0) (hct : c ≠ ⊤) [IsFiniteMeasure (densityLaw μ c H)]
    (hR : Integrable (fun p => |H p-H p.swap|) (densityLaw μ c H))
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) :
    |(∫ p : Ω × Ω, f p.2 ∂densityLaw μ c H)-
      ∫ p : Ω × Ω, f p.1 ∂densityLaw μ c H| ≤
      2*B*∫ p, |H p-H p.swap| ∂densityLaw μ c H := by
  have hi := (densityLaw_integrable μ hm hc hct (fun _ => 1)).mp (integrable_const 1)
  simp only [mul_one] at hi
  have hr := (densityLaw_integrable μ hm hc hct (fun p => |H p-H p.swap|)).mp hR
  have hh := one_step_defect μ hm hi hr hf hB hb
  rw [densityLaw_integral μ hm,densityLaw_integral μ hm,densityLaw_integral μ hm,
    ← mul_sub,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
  have hh' := mul_le_mul_of_nonneg_left hh (ENNReal.toReal_nonneg (a := c))
  dsimp [defectWeight] at hh'
  nlinarith only [hh']

end MetropolisBalance
namespace EulerDefect
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {d : ℕ} {H : Point d → ℝ}

def joint (H : Point d → ℝ) (s : ℝ) : Measure (Point d × Point d) :=
  ((gibbs H).prod (stdGaussian (Point d))).map (fun p => (p.1,proposal H s p.1 p.2))

def jointCoefficient (H : Point d → ℝ) (s : ℝ) : ℝ≥0∞ :=
  (partition H)⁻¹*EulerDensity.noiseCoefficient d (Real.sqrt 2*s)

lemma joint_density (hH : ContDiff ℝ 2 H) {s : ℝ} (hs : s ≠ 0) :
    joint H s = MetropolisBalance.densityLaw volume (jointCoefficient H s)
      (fun p => proposalLog H (s^2) p.1 p.2) := by
  have hg := (Trapezoid.contDiff_gradient hH).continuous.measurable
  have he := EulerDensity.joint_density hH.continuous.measurable
    (fun x => x-s^2 • gradient H x) (by fun_prop)
    (mul_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)) hs)
  change joint H s = _ at he
  rw [he]
  congr 2
  funext p
  unfold proposalLog
  congr 2
  have he₁ : (p.2 : Point d)-(p.1-s^2 • gradient H p.1) = p.2-p.1+s^2 • gradient H p.1 := by abel
  rw [he₁,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

lemma measurable_joint_map (hH : ContDiff ℝ 2 H) (s : ℝ) :
    Measurable (fun p : Point d × Point d => (p.1,proposal H s p.1 p.2)) := by
  have hg := (Trapezoid.contDiff_gradient hH).continuous.measurable
  unfold proposal
  fun_prop

lemma jointCoefficient_ne_zero (hp : partition H ≠ ⊤) {s : ℝ} (hs : s ≠ 0) :
    jointCoefficient H s ≠ 0 := by
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hp)
    (ne_of_gt (EulerDensity.noiseCoefficient_positive d
      (mul_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)) hs)))

lemma jointCoefficient_ne_top (hp : partition H ≠ 0) (s : ℝ) :
    jointCoefficient H s ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp) (EulerDensity.noiseCoefficient_finite d _)

lemma scaled_log_ratio_integrable (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) (μ : Measure (Point d)) [IsFiniteMeasure μ]
    (hi : Integrable (fun x => ‖gradient H x‖^2) μ) {s : ℝ} (hs : |s| ≤ 1) :
    Integrable (fun p : Point d × Point d =>
      |(proposalLog H (s^2) p.1 (proposal H s p.1 p.2)-
        proposalLog H (s^2) (proposal H s p.1 p.2) p.1)/s^2|)
      (μ.prod (stdGaussian (Point d))) := by
  have hg := (Trapezoid.contDiff_gradient hH).continuous
  have hz : Integrable (fun z : Point d => ‖z‖^2) (stdGaussian (Point d)) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian (Point d))).norm.integrable_sq
  refine (((hi.comp_fst (stdGaussian (Point d))).add (hz.comp_snd μ)).const_mul
    (6*(M:ℝ)+(M:ℝ)^2)).mono' ?_ ?_
  · have hc : Continuous (fun p : Point d × Point d =>
        |(proposalLog H (s^2) p.1 (proposal H s p.1 p.2)-
          proposalLog H (s^2) (proposal H s p.1 p.2) p.1)/s^2|) := by
      unfold proposalLog proposal
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with p
    rw [Real.norm_eq_abs,abs_abs]
    exact (scaled_log_ratio_bound hH hM hs p.1 p.2).trans (quadratic_dominator_bound M p.1 p.2)

end EulerDefect
end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerDefect
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {d : ℕ} {H : Point d → ℝ}

def rate (H : Point d → ℝ) (s : ℝ) : ℝ :=
  ∫ p : Point d × Point d,
    |(proposalLog H (s^2) p.1 (proposal H s p.1 p.2)-
      proposalLog H (s^2) (proposal H s p.1 p.2) p.1)/s^2|
    ∂(gibbs H).prod (stdGaussian (Point d))

lemma rate_nonneg (H : Point d → ℝ) (s : ℝ) : 0 ≤ rate H s :=
  integral_nonneg (fun _ => abs_nonneg _)

lemma rate_tendsto (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) [IsFiniteMeasure (gibbs H)]
    (hi : Integrable (fun x => ‖gradient H x‖^2) (gibbs H)) :
    Filter.Tendsto (rate H) (𝓝 0) (𝓝 0) :=
  expected_scaled_log_ratio_tendsto hH hM (gibbs H) hi

lemma joint_log_ratio_integrable (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) [IsFiniteMeasure (gibbs H)]
    (hi : Integrable (fun x => ‖gradient H x‖^2) (gibbs H))
    {s : ℝ} (hs : s ≠ 0) (hs1 : |s| ≤ 1) :
    Integrable (fun p : Point d × Point d => |proposalLog H (s^2) p.1 p.2-proposalLog H (s^2) p.2 p.1|)
      (joint H s) := by
  have hg := (Trapezoid.contDiff_gradient hH).continuous
  have hc : Continuous (fun p : Point d × Point d =>
      |proposalLog H (s^2) p.1 p.2-proposalLog H (s^2) p.2 p.1|) := by
    unfold proposalLog
    fun_prop
  rw [joint,integrable_map_measure hc.aestronglyMeasurable (measurable_joint_map hH s).aemeasurable]
  have hb := (scaled_log_ratio_integrable hH hM (gibbs H) hi hs1).const_mul (s^2)
  convert! hb using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  dsimp only [Function.comp_apply]
  rw [abs_div,abs_of_nonneg (sq_nonneg s)]
  field_simp

lemma joint_log_ratio_integral (hH : ContDiff ℝ 2 H) {s : ℝ} (hs : s ≠ 0) :
    (∫ p : Point d × Point d, |proposalLog H (s^2) p.1 p.2-proposalLog H (s^2) p.2 p.1|
      ∂joint H s) = s^2*rate H s := by
  have hg := (Trapezoid.contDiff_gradient hH).continuous
  have hc : Continuous (fun p : Point d × Point d =>
      |proposalLog H (s^2) p.1 p.2-proposalLog H (s^2) p.2 p.1|) := by
    unfold proposalLog
    fun_prop
  rw [joint,integral_map (measurable_joint_map hH s).aemeasurable hc.aestronglyMeasurable,
    rate,← integral_const_mul]
  congr 1
  funext p
  rw [abs_div,abs_of_nonneg (sq_nonneg s)]
  field_simp

theorem one_step_gibbs_defect (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) [IsProbabilityMeasure (gibbs H)]
    (hp0 : partition H ≠ 0) (hpt : partition H ≠ ⊤)
    (hi : Integrable (fun x => ‖gradient H x‖^2) (gibbs H))
    {s : ℝ} (hs : s ≠ 0) (hs1 : |s| ≤ 1)
    {f : Point d → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    |(∫ p : Point d × Point d, f (proposal H s p.1 p.2)
        ∂(gibbs H).prod (stdGaussian (Point d)))-∫ x, f x ∂gibbs H| ≤
      B*(2*s^2*rate H s) := by
  have : IsProbabilityMeasure (joint H s) := by
    unfold joint
    exact Measure.isProbabilityMeasure_map (measurable_joint_map hH s).aemeasurable
  have he := joint_density hH hs
  have : IsProbabilityMeasure (MetropolisBalance.densityLaw volume (jointCoefficient H s)
      (fun p => proposalLog H (s^2) p.1 p.2)) := by rw [← he]; assumption
  have hg := (Trapezoid.contDiff_gradient hH).continuous
  have hm : Measurable (fun p : Point d × Point d => proposalLog H (s^2) p.1 p.2) := by
    have hc := hH.continuous
    unfold proposalLog
    fun_prop
  have hr := joint_log_ratio_integrable hH hM hi hs hs1
  rw [he] at hr
  have hh := MetropolisBalance.probability_one_step_defect volume hm
    (jointCoefficient_ne_zero hpt hs) (jointCoefficient_ne_top hp0 s) hr hf hB hb
  rw [← he] at hh
  simp only [Prod.swap] at hh
  rw [joint_log_ratio_integral hH hs] at hh
  have hfst : (∫ p : Point d × Point d, f p.1 ∂joint H s) = ∫ x, f x ∂gibbs H := by
    rw [joint,integral_map (f := fun p : Point d × Point d => f p.1) (measurable_joint_map hH s).aemeasurable
      (hf.comp measurable_fst).aestronglyMeasurable]
    simp only [integral_fun_fst,probReal_univ,one_smul]
  have hsnd : (∫ p : Point d × Point d, f p.2 ∂joint H s) =
      ∫ p : Point d × Point d, f (proposal H s p.1 p.2)
        ∂(gibbs H).prod (stdGaussian (Point d)) := by
    exact integral_map (measurable_joint_map hH s).aemeasurable
      (hf.comp measurable_snd).aestronglyMeasurable
  rw [hfst,hsnd] at hh
  nlinarith only [hh]

end EulerDefect
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_Operator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace EulerGeometry
open MeasureTheory ProbabilityTheory WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_noise_product (n : ℕ) :
    (Measure.pi (fun _ : Fin n => stdGaussian E)).map (toLp 2) =
      stdGaussian (PiLp 2 (fun _ : Fin n => E)) := by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [charFun_pi,charFun_stdGaussian,← Complex.exp_sum]
  congr 1
  rw [← Complex.ofReal_pow, PiLp.norm_sq_eq_of_L2]
  simp only [Complex.ofReal_sum,Complex.ofReal_pow]
  rw [← Finset.sum_neg_distrib,Finset.sum_div]

lemma bounded_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.mono' (integrable_const B) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

def operator (T : E → E) (σ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∫ z, f (T x+σ • z) ∂stdGaussian E

lemma measurable_operator {T : E → E} (hT : Measurable T) (σ : ℝ)
    {f : E → ℝ} (hf : Measurable f) : Measurable (operator T σ f) := by
  exact (hf.comp ((hT.comp measurable_fst).add (measurable_snd.const_smul σ))).stronglyMeasurable.integral_prod_right'.measurable

lemma operator_bound (T : E → E) (σ : ℝ) {f : E → ℝ} {B : ℝ}
    (hb : ∀ x, |f x| ≤ B) (x : E) : |operator T σ f x| ≤ B := by
  have hn := norm_integral_le_of_norm_le_const (μ := stdGaussian E)
    (f := fun z => f (T x+σ • z))
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hb (T x+σ • z)))
  simpa only [operator,Real.norm_eq_abs,probReal_univ,mul_one] using hn

theorem iterated_defect {T : E → E} (hT : Measurable T) (σ : ℝ)
    (μ : Measure E) [IsProbabilityMeasure μ] {D : ℝ}
    (hD : ∀ (f : E → ℝ), Measurable f → ∀ B : ℝ, 0 ≤ B →
      (∀ x, |f x| ≤ B) → |(∫ x, operator T σ f x ∂μ)-∫ x, f x ∂μ| ≤ B*D)
    {f : E → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B)
    (n : ℕ) :
    |(∫ x, ((operator T σ)^[n] f) x ∂μ)-∫ x, f x ∂μ| ≤ (n:ℝ)*B*D := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      have hm := measurable_operator hT σ hf
      have hbound := operator_bound T σ hb
      have ha := ih hm hbound
      have hd := hD f hf B hB hb
      have ht := abs_sub_le (∫ x, ((operator T σ)^[n] (operator T σ f)) x ∂μ)
        (∫ x, operator T σ f x ∂μ) (∫ x, f x ∂μ)
      push_cast
      nlinarith only [ha,hd,ht]

end EulerGeometry
end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerGeometry
open MeasureTheory ProbabilityTheory WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_iterate {T : E → E} (hT : Measurable T) (σ : ℝ) (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] {x : Ω → E} (hx : Measurable x)
    {g : Ω → Fin n → E} (hg : ∀ i, Measurable (fun z => g z i)) :
    Measurable (fun z => iterate T σ n (x z) (g z)) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      exact (hT.comp (ih (fun i => hg i.castSucc))).add ((hg (Fin.last n)).const_smul σ)

lemma integral_iterate {T : E → E} (hT : Measurable T) (σ : ℝ)
    {f : E → ℝ} (hf : Measurable f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (n : ℕ) (x : E) :
    (∫ g : Fin n → E, f (iterate T σ n x g) ∂Measure.pi (fun _ => stdGaussian E)) =
      ((operator T σ)^[n] f) x := by
  induction n generalizing f with
  | zero => simp [iterate]
  | succ n ih =>
      have hm : Measurable (fun p : E × (Fin n → E) => f (T (iterate T σ n x p.2)+σ • p.1)) := by
        exact hf.comp ((hT.comp (measurable_iterate hT σ n measurable_const
          (fun i => (measurable_pi_apply i).comp measurable_snd))).add (measurable_fst.const_smul σ))
      have hi := bounded_integrable (μ := (stdGaussian E).prod (Measure.pi (fun _ : Fin n => stdGaussian E)))
        hm (fun p => hb (T (iterate T σ n x p.2)+σ • p.1))
      have he : (∫ g : Fin (n+1) → E, f (iterate T σ (n+1) x g) ∂Measure.pi (fun _ => stdGaussian E)) =
          ∫ p : E × (Fin n → E), f (T (iterate T σ n x p.2)+σ • p.1)
            ∂(stdGaussian E).prod (Measure.pi (fun _ => stdGaussian E)) := by
        rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => stdGaussian E) (Fin.last n)).symm).integral_comp']
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
          Equiv.coe_fn_mk,Fin.insertNth_last',iterate,Fin.snoc_castSucc,Fin.snoc_last]
      rw [he,integral_prod_symm _ hi]
      change (∫ g : Fin n → E, operator T σ f (iterate T σ n x g) ∂Measure.pi (fun _ => stdGaussian E)) = _
      rw [ih (measurable_operator hT σ hf) (operator_bound T σ hb),Function.iterate_succ_apply]

lemma integral_iterate_gaussian {T : E → E} (hT : Measurable T) (σ : ℝ)
    {f : E → ℝ} (hf : Measurable f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (n : ℕ) (x : E) :
    (∫ g : PiLp 2 (fun _ : Fin n => E), f (iterate T σ n x g) ∂stdGaussian _) =
      ((operator T σ)^[n] f) x := by
  rw [← gaussian_noise_product (E := E) n,integral_map (measurable_toLp 2 (Fin n → E)).aemeasurable]
  · exact integral_iterate hT σ hf hb n x
  · exact (hf.comp (measurable_iterate hT σ n measurable_const
      (fun i => (PiLp.proj 2 (fun _ : Fin n => E) i : PiLp 2 (fun _ : Fin n => E) →L[ℝ] E).continuous.measurable))).aestronglyMeasurable

lemma iterate_operator_bound (T : E → E) (σ : ℝ) {f : E → ℝ} {B : ℝ}
    (hb : ∀ x, |f x| ≤ B) (n : ℕ) : ∀ x, |((operator T σ)^[n] f) x| ≤ B := by
  induction n generalizing f with
  | zero => exact hb
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (operator_bound T σ hb)

lemma measurable_iterate_operator {T : E → E} (hT : Measurable T) (σ : ℝ)
    {f : E → ℝ} (hf : Measurable f) (n : ℕ) : Measurable ((operator T σ)^[n] f) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (measurable_operator hT σ hf)

lemma iterate_operator_modulus {q : ℝ≥0} {T : E → E} (hT : LipschitzWith q T)
    (σ : ℝ) {f : E → ℝ} (hf : Measurable f) {B : ℝ} (hb : ∀ x, |f x| ≤ B)
    {δ ε : ℝ} (hmod : ∀ x y, dist x y < δ → |f x-f y| ≤ ε)
    (n : ℕ) {x y : E} (hxy : (q:ℝ)^n*dist x y < δ) :
    |((operator T σ)^[n] f) x-((operator T σ)^[n] f) y| ≤ ε := by
  have hi (x : E) : Integrable (fun g : Fin n → E => f (iterate T σ n x g))
      (Measure.pi (fun _ => stdGaussian E)) := bounded_integrable (μ := Measure.pi (fun _ : Fin n => stdGaussian E))
    (hf.comp (measurable_iterate hT.continuous.measurable σ n measurable_const
      (fun i => measurable_pi_apply i))) (fun g => hb (iterate T σ n x g))
  rw [← integral_iterate hT.continuous.measurable σ hf hb n x,
    ← integral_iterate hT.continuous.measurable σ hf hb n y,← integral_sub (hi x) (hi y)]
  have hh := norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin n => stdGaussian E))
    (f := fun g => f (iterate T σ n x g)-f (iterate T σ n y g))
    (Filter.Eventually.of_forall (fun g => by
      rw [Real.norm_eq_abs]
      exact hmod _ _ ((initial_contraction hT σ n x y g).trans_lt hxy)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

end EulerGeometry
end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerGeometry
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_collapse (μ : Measure E) [IsProbabilityMeasure μ]
    {q : ℕ → ℝ≥0} {T : ℕ → E → E} (hT : ∀ k, LipschitzWith (q k) (T k))
    (σ : ℕ → ℝ) (N : ℕ → ℕ)
    (hq : Tendsto (fun k => (q k:ℝ)^(N k)) atTop (𝓝 0))
    {f : E → ℝ} (hf : UniformContinuous f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (x₀ : E) :
    Tendsto (fun k => (∫ x, ((operator (T k) (σ k))^[N k] f) x ∂μ)-
      ((operator (T k) (σ k))^[N k] f) x₀) atTop (𝓝 0) := by
  let F := fun k x => ((operator (T k) (σ k))^[N k] f) x-
    ((operator (T k) (σ k))^[N k] f) x₀
  have hm k : Measurable (F k) :=
    (measurable_iterate_operator (hT k).continuous.measurable (σ k) hf.continuous.measurable (N k)).sub measurable_const
  have hpoint (x : E) : Tendsto (fun k => F k x) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp hf (ε/2) (by positivity)
    have hd : Tendsto (fun k => (q k:ℝ)^(N k)*dist x x₀) atTop (𝓝 0) := by
      simpa only [zero_mul] using hq.mul_const (dist x x₀)
    filter_upwards [hd.eventually (gt_mem_nhds hδ)] with k hk
    rw [dist_zero_right,Real.norm_eq_abs]
    have hh := iterate_operator_modulus (hT k) (σ k) hf.continuous.measurable hb
      (fun a b hab => (le_of_lt (hmod hab) : dist (f a) (f b) ≤ ε/2)) (N k) hk
    exact hh.trans_lt (by linarith)
  have hh := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ => (0:ℝ)) (fun _ => (2*B:ℝ))
    (fun k => (hm k).aestronglyMeasurable) (integrable_const _) (fun k => ?_) ?_
  · have he (k : ℕ) : (∫ x, F k x ∂μ) =
        (∫ x, ((operator (T k) (σ k))^[N k] f) x ∂μ)-((operator (T k) (σ k))^[N k] f) x₀ := by
      rw [show F k = (fun x => ((operator (T k) (σ k))^[N k] f) x-
          ((operator (T k) (σ k))^[N k] f) x₀) from rfl,
        integral_sub (bounded_integrable
          (measurable_iterate_operator (hT k).continuous.measurable (σ k) hf.continuous.measurable (N k))
          (iterate_operator_bound (T k) (σ k) hb (N k))) (integrable_const _),
        integral_const,probReal_univ,one_smul]
    simpa only [he,integral_zero] using hh
  · filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by
      have h₁ := iterate_operator_bound (T k) (σ k) hb (N k) x
      have h₂ := iterate_operator_bound (T k) (σ k) hb (N k) x₀
      linarith)
  · filter_upwards [] with x
    exact hpoint x

theorem expectations_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    {q : ℕ → ℝ≥0} {T : ℕ → E → E} (hT : ∀ k, LipschitzWith (q k) (T k))
    (σ : ℕ → ℝ) (N : ℕ → ℕ)
    (hq : Tendsto (fun k => (q k:ℝ)^(N k)) atTop (𝓝 0))
    {D : ℕ → ℝ} (hD : Tendsto (fun k => (N k:ℝ)*D k) atTop (𝓝 0))
    (hstep : ∀ k (f : E → ℝ), Measurable f → ∀ B : ℝ, 0 ≤ B →
      (∀ x, |f x| ≤ B) → |(∫ x, operator (T k) (σ k) f x ∂μ)-∫ x, f x ∂μ| ≤ B*D k)
    {f : E → ℝ} (hf : UniformContinuous f) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) (x₀ : E) :
    Tendsto (fun k => ((operator (T k) (σ k))^[N k] f) x₀) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have ha : Tendsto (fun k => (∫ x, ((operator (T k) (σ k))^[N k] f) x ∂μ)-∫ x, f x ∂μ)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hz : Tendsto (fun k => B*((N k:ℝ)*D k)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hD.const_mul B
    apply squeeze_zero (fun _ => norm_nonneg _) ?_ hz
    intro k
    simpa only [Real.norm_eq_abs,mul_assoc,mul_comm (N k:ℝ) B] using
      iterated_defect (hT k).continuous.measurable (σ k) μ (hstep k)
        hf.continuous.measurable hB hb (N k)
  have hb := integral_collapse μ hT σ N hq hf hb x₀
  have ht := (ha.sub hb).add_const (∫ x, f x ∂μ)
  convert! ht using 1
  · funext k; ring_nf
  · simp only [sub_self,zero_add]

end EulerGeometry
end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerGeometry
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma compact_test_lipschitz {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : ∃ K : ℝ≥0, LipschitzWith K f := by
  obtain ⟨K,hK⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hf.continuous_fderiv (by norm_num))
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ f 0)).trans (hK 0)
  exact ⟨⟨K,hK0⟩,lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by norm_num))
    (fun x => hK x)⟩

theorem poincare_of_euler_approximation (μ : Measure E) [IsProbabilityMeasure μ]
    {q : ℕ → ℝ≥0} {T : ℕ → E → E}
    (hT : ∀ k, ContDiff ℝ 1 (T k)) (hl : ∀ k, LipschitzWith (q k) (T k))
    (σ : ℕ → ℝ≥0) (N : ℕ → ℕ) (x₀ : E) {C : ℝ}
    (hC : ∀ k, (σ k:ℝ)^2*energy (q k) (N k) ≤ C)
    (hconv : ∀ f : E → ℝ, UniformContinuous f → (∃ B, ∀ x, |f x| ≤ B) →
      Tendsto (fun k => ((operator (T k) (σ k))^[N k] f) x₀) atTop (𝓝 (∫ x, f x ∂μ)))
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Var[f;μ] ≤ (Real.pi^2/8)*C*∫ x, ‖fderiv ℝ f x‖^2 ∂μ := by
  obtain ⟨K,hK⟩ := compact_test_lipschitz hf hc
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hf.continuous
  have hb : ∀ x, |f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB
  have hd := hf.continuous_fderiv (by norm_num)
  obtain ⟨D,hD⟩ := (hc.fderiv ℝ).exists_bound_of_continuous hd
  have hf2 : HasCompactSupport (fun x => (f x)^2) :=
    hc.comp_left (g := fun y : ℝ => y^2) (by norm_num)
  have hd2 : HasCompactSupport (fun x => ‖fderiv ℝ f x‖^2) :=
    (hc.fderiv ℝ).norm.comp_left (g := fun y : ℝ => y^2) (by norm_num)
  have hb2 (x : E) : |(f x)^2| ≤ B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg (f 0)).trans (hb 0))).mpr (hb x)
  have hd2b (x : E) : |‖fderiv ℝ f x‖^2| ≤ D^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hD x) 2
  have hm : MemLp f 2 μ := MemLp.of_bound hf.continuous.aestronglyMeasurable B
    (Filter.Eventually.of_forall hB)
  have hfconv := hconv f (hc.uniformContinuous_of_continuous hf.continuous) ⟨B,hb⟩
  have hf2conv := hconv (fun x => (f x)^2)
    (hf2.uniformContinuous_of_continuous (hf.continuous.pow 2)) ⟨B^2,hb2⟩
  have hdconv := hconv (fun x => ‖fderiv ℝ f x‖^2)
    (hd2.uniformContinuous_of_continuous (hd.norm.pow 2)) ⟨D^2,hd2b⟩
  rw [variance_eq_sub hm]
  apply le_of_tendsto_of_tendsto (hf2conv.sub (hfconv.pow 2))
    (hdconv.const_mul ((Real.pi^2/8)*C))
  filter_upwards [] with k
  let X := fun g : PiLp 2 (fun _ : Fin (N k) => E) => iterate (T k) (σ k) (N k) x₀ g
  let A : ℝ≥0 := σ k * ⟨Real.sqrt (energy (q k) (N k)),Real.sqrt_nonneg _⟩
  have hX : ContDiff ℝ 1 X := contDiff_noise (hT k) (σ k) (N k) x₀
  have hXL : LipschitzWith A X := noise_lipschitz (hl k) (σ k) (N k) x₀
  have hp := GaussianPoincare.variance_lipschitz_image hX hXL hf hK
  have hmap {g : E → ℝ} (hg : Measurable g) {b : ℝ} (hb : ∀ x, |g x| ≤ b) :
      (∫ y, g y ∂(stdGaussian _).map X) = ((operator (T k) (σ k))^[N k] g) x₀ := by
    rw [integral_map hX.continuous.aemeasurable hg.aestronglyMeasurable]
    exact integral_iterate_gaussian (hT k).continuous.measurable (σ k) hg hb (N k) x₀
  have : IsProbabilityMeasure ((stdGaussian _).map X) := Measure.isProbabilityMeasure_map hX.continuous.aemeasurable
  have hmf : MemLp f 2 ((stdGaussian _).map X) := MemLp.of_bound
    hf.continuous.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have hdm := hmap (g := fun x => ‖fderiv ℝ f x‖^2) (hd.norm.pow 2).measurable hd2b
  rw [variance_eq_sub hmf] at hp
  simp only [Pi.pow_apply] at hp
  rw [hmap (hf.continuous.measurable.pow_const 2) hb2,
    hmap hf.continuous.measurable hb,hdm] at hp
  have hA : (A:ℝ)^2 ≤ C := by
    change ((σ k:ℝ)*Real.sqrt (energy (q k) (N k)))^2 ≤ C
    rw [mul_pow,Real.sq_sqrt (energy_nonneg (q := (q k:ℝ)) (N k))]
    exact hC k
  exact hp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hA (by positivity)) (by
      rw [← hdm]
      exact integral_nonneg (fun _ => sq_nonneg _)))

end EulerGeometry
end LogConcaveSampling
namespace LogConcaveSampling
namespace EulerGeometry
open Filter
open scoped Topology

theorem exists_consistent_schedule {R : ℝ → ℝ} (hR : Tendsto R (𝓝 0) (𝓝 0))
    (hR0 : ∀ s, 0 ≤ R s) {a : ℝ} (ha : 0 < a) :
    ∃ (N : ℕ → ℕ) (s : ℕ → ℝ),
      (∀ k, 0 < s k ∧ s k ≤ 1 ∧ (s k)^2 ≤ a ∧ (N k:ℝ)*(s k)^2=(k:ℝ)+1) ∧
      Tendsto (fun k => (N k:ℝ)*(2*(s k)^2*R (s k))) atTop (𝓝 0) := by
  have hex (k : ℕ) : ∃ n : ℕ, ∃ s : ℝ,
      (0 < s ∧ s ≤ 1 ∧ s^2 ≤ a ∧ (n:ℝ)*s^2=(k:ℝ)+1) ∧
      (n:ℝ)*(2*s^2*R s) ≤ 1/((k:ℝ)+1) := by
    let h : ℕ → ℝ := fun n => ((k:ℝ)+1)/((n:ℝ)+1)
    have ht : Tendsto h atTop (𝓝 0) := by
      simpa only [h,mul_one_div,mul_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((k:ℝ)+1)
    have hs : Tendsto (fun n => Real.sqrt (h n)) atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero] using ht.sqrt
    have hr := hR.comp hs
    have hb : 0 < 1/(2*((k:ℝ)+1)^2) := by positivity
    obtain ⟨n,hn⟩ := ((ht.eventually (gt_mem_nhds ha)).and
      ((hs.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).and
        (hr.eventually (gt_mem_nhds hb)))).exists
    have hp : 0 < h n := by dsimp [h]; positivity
    refine ⟨n+1,Real.sqrt (h n),⟨Real.sqrt_pos.mpr hp,hn.2.1.le,?_,?_⟩,?_⟩
    · rw [Real.sq_sqrt hp.le]
      exact hn.1.le
    · rw [Real.sq_sqrt hp.le]
      dsimp [h]
      push_cast
      field_simp
    · rw [Real.sq_sqrt hp.le]
      have hh := mul_le_mul_of_nonneg_left hn.2.2.le (show 0 ≤ 2*((k:ℝ)+1) by positivity)
      have he : (n+1:ℝ)*(2*h n*R (Real.sqrt (h n))) = 2*((k:ℝ)+1)*R (Real.sqrt (h n)) := by
        dsimp [h]
        field_simp
      push_cast
      rw [he]
      convert! hh using 1
      all_goals try with_reducible_and_instances rfl
      field_simp
  choose N s hs using hex
  refine ⟨N,s,(fun k => (hs k).1),?_⟩
  apply squeeze_zero (fun k => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg _)) (hR0 _))) (fun k => (hs k).2)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

lemma contraction_geometric_bound {m h : ℝ} (_hm : 0 < m) (hh : 0 ≤ 1-m*h)
    (n k : ℕ) (hn : (n:ℝ)*h=(k:ℝ)+1) :
    (1-m*h)^n ≤ (Real.exp (-m))^(k+1) := by
  have hq : 1-m*h ≤ Real.exp (-m*h) := by
    nlinarith only [Real.add_one_le_exp (-m*h)]
  have hp := pow_le_pow_left₀ hh hq n
  rw [← Real.exp_nat_mul] at hp
  rw [← Real.exp_nat_mul]
  convert! hp using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  push_cast
  linear_combination m*hn

lemma schedule_contraction_tendsto {m : ℝ} (hm : 0 < m)
    (N : ℕ → ℕ) (s : ℕ → ℝ)
    (hq : ∀ k, 0 ≤ 1-m*(s k)^2)
    (hn : ∀ k, (N k:ℝ)*(s k)^2=(k:ℝ)+1) :
    Tendsto (fun k => (1-m*(s k)^2)^(N k)) atTop (𝓝 0) := by
  have he := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-m)).le
    (show Real.exp (-m) < 1 by simpa only [Real.exp_lt_one_iff] using neg_neg_of_pos hm)).comp
      (tendsto_add_atTop_nat 1)
  exact squeeze_zero (fun k => pow_nonneg (hq k) _) (fun k => contraction_geometric_bound hm (hq k) (N k) k (hn k)) he

end EulerGeometry
end LogConcaveSampling
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

lemma euler_noise_energy_bound {m h : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (hh : 0 < h) (hh1 : h ≤ 1) (n : ℕ) :
    2*h*EulerGeometry.energy (1-m*h) n ≤ 2/m := by
  have hq : 0 ≤ 1-m*h := by nlinarith
  have hq1 : 1-m*h < 1 := by nlinarith
  have hden : 0 < 1-(1-m*h)^2 := by nlinarith
  have he := mul_le_mul_of_nonneg_left (EulerGeometry.energy_le hq hq1 n) (by positivity : 0 ≤ 2*h)
  have hd : 2*h*(1-(1-m*h)^2)⁻¹ ≤ 2/m := by
    rw [← div_eq_mul_inv,div_le_div_iff₀ hden hm]
    have hp : m*h ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hm.le hh.le) (sub_nonneg.mpr hp)]
  exact he.trans hd

lemma euler_operator_gibbs_defect {d : ℕ} {H : Point d → ℝ}
    (hH : ContDiff ℝ 2 H) {M : ℝ≥0} (hM : LipschitzWith M (gradient H))
    [IsProbabilityMeasure (gibbs H)]
    (hp0 : partition H ≠ 0) (hpt : partition H ≠ ⊤)
    (hi : Integrable (fun z => ‖gradient H z‖^2) (gibbs H))
    {s : ℝ} (hs : s ≠ 0) (hs1 : |s| ≤ 1)
    {g : Point d → ℝ} (hg : Measurable g) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ z, |g z| ≤ B) :
    |(∫ z, EulerGeometry.operator (eulerDrift H (s^2)) (Real.sqrt 2*s) g z ∂gibbs H)-
      ∫ z, g z ∂gibbs H| ≤ B*(2*s^2*EulerDefect.rate H s) := by
  have he := EulerDefect.one_step_gibbs_defect hH hM hp0 hpt hi hs hs1 hg hB hb
  have hgm : Measurable (fun p : Point d × Point d => g (EulerDefect.proposal H s p.1 p.2)) :=
    hg.comp (EulerDefect.measurable_joint_map hH s).snd
  rw [integral_prod _ (EulerGeometry.bounded_integrable hgm
    (fun p => hb (EulerDefect.proposal H s p.1 p.2)))] at he
  exact he

theorem Primitive.poincare_compact {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) {f : Point d → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Var[f;gibbs (primitivePotential F x r)] ≤
      (Real.pi^2/8)*(2/(1-(lam:ℝ)*r^2))*∫ z, ‖fderiv ℝ f z‖^2 ∂gibbs (primitivePotential F x r) := by
  let H := primitivePotential F x r
  let m : ℝ := 1-(lam:ℝ)*r^2
  have hm : 0 < m := sub_pos.mpr hl
  have hm1 : m ≤ 1 := by
    dsimp [m]
    nlinarith [mul_nonneg lam.coe_nonneg (sq_nonneg r)]
  have hH : ContDiff ℝ 2 H := hF.contDiff_potential x r
  have hg := hF.gradient_potential_lipschitz x hr
  have hi := hF.gradient_sq_integrable x hr hl
  have hp0 : partition H ≠ 0 := (partition_pos_of_continuous hH.continuous).ne'
  have hpt : partition H ≠ ⊤ := partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl)
  have : IsProbabilityMeasure (gibbs H) := probability_gibbs_of_partition hp0 hpt
  obtain ⟨N,s,hs,hD⟩ := EulerGeometry.exists_consistent_schedule
    (EulerDefect.rate_tendsto hH hg hi) (EulerDefect.rate_nonneg H) (a := 1) (by norm_num)
  let q : ℕ → ℝ≥0 := fun k => ⟨1-m*(s k)^2,by
    have hp := (hs k).2.2.1
    have hz := sq_nonneg (s k)
    nlinarith⟩
  let σ : ℕ → ℝ≥0 := fun k => ⟨Real.sqrt 2*s k,mul_nonneg (Real.sqrt_nonneg _) (hs k).1.le⟩
  let T := fun k => eulerDrift H ((s k)^2)
  have hTL (k : ℕ) : LipschitzWith (q k) (T k) := by
    have hh := hF.eulerDrift_lipschitz x hr (sq_nonneg (s k)) (hs k).2.2.1
    apply hh.weaken
    change 1-(s k)^2+(s k)^2*((lam:ℝ)*r^2) ≤ 1-m*(s k)^2
    dsimp [m]
    nlinarith
  have hTC (k : ℕ) : ContDiff ℝ 1 (T k) := hF.contDiff_eulerDrift x r ((s k)^2)
  have hq : Tendsto (fun k => (q k:ℝ)^(N k)) atTop (𝓝 0) :=
    EulerGeometry.schedule_contraction_tendsto hm N s (fun k => (q k).coe_nonneg)
      (fun k => (hs k).2.2.2)
  have hstep (k : ℕ) (g : Point d → ℝ) (hg' : Measurable g) (B : ℝ) (hB : 0 ≤ B)
      (hb : ∀ z, |g z| ≤ B) :
      |(∫ z, EulerGeometry.operator (T k) (σ k) g z ∂gibbs H)-∫ z, g z ∂gibbs H| ≤
        B*(2*(s k)^2*EulerDefect.rate H (s k)) := by
    exact euler_operator_gibbs_defect hH hg hp0 hpt hi (hs k).1.ne'
      (by rw [abs_of_pos (hs k).1]; exact (hs k).2.1) hg' hB hb
  have hconv (g : Point d → ℝ) (hg' : UniformContinuous g) (hb : ∃ B, ∀ z, |g z| ≤ B) :
      Tendsto (fun k => ((EulerGeometry.operator (T k) (σ k))^[N k] g) 0)
        atTop (𝓝 (∫ z, g z ∂gibbs H)) := by
    obtain ⟨B,hb⟩ := hb
    exact EulerGeometry.expectations_tendsto (gibbs H) hTL (fun k => (σ k:ℝ)) N hq hD hstep
      hg' ((abs_nonneg (g 0)).trans (hb 0)) hb 0
  apply EulerGeometry.poincare_of_euler_approximation (gibbs H) hTC hTL σ N 0
    (C := 2/m) ?_ hconv hf hc
  intro k
  change (Real.sqrt 2*s k)^2*EulerGeometry.energy (1-m*(s k)^2) (N k) ≤ 2/m
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  exact euler_noise_energy_bound hm hm1 (sq_pos_of_pos (hs k).1) (hs k).2.2.1 (N k)

end LogConcaveSampling

namespace LogConcaveSampling
namespace PoincareCutoff
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def bump : ContDiffBump (0 : E) := ⟨1,2,by norm_num,by norm_num⟩
def cutoff (n : ℕ) (x : E) : ℝ := (bump (E := E)) (((n:ℝ)+1)⁻¹ • x)

lemma cutoff_smooth (n : ℕ) : ContDiff ℝ 1 (cutoff (E := E) n) :=
  ((bump (E := E)).contDiff).comp (contDiff_id.const_smul _)

lemma cutoff_compact (n : ℕ) : HasCompactSupport (cutoff (E := E) n) := by
  exact (bump (E := E)).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (((n:ℝ)+1)⁻¹) (by positivity))

lemma cutoff_nonneg (n : ℕ) (x : E) : 0 ≤ cutoff n x := (bump (E := E)).nonneg
lemma cutoff_le_one (n : ℕ) (x : E) : cutoff n x ≤ 1 := (bump (E := E)).le_one
lemma cutoff_abs (n : ℕ) (x : E) : |cutoff n x| ≤ 1 := by
  rw [abs_of_nonneg (cutoff_nonneg n x)]
  exact cutoff_le_one n x

lemma cutoff_tendsto (x : E) : Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0))
  have hh := (((bump (E := E)).contDiff (n := 1)).continuous.tendsto (0:E)).comp
    (show Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹ • x) atTop (𝓝 (0:E)) by simpa only [zero_smul] using ht.smul_const x)
  have he : (bump (E := E)) (0:E) = 1 :=
    (bump (E := E)).one_of_mem_closedBall (by simp [bump])
  simpa only [cutoff,he,Function.comp_def] using hh

lemma exists_derivative_bound : ∃ K : ℝ≥0, ∀ n x,
    ‖fderiv ℝ (cutoff (E := E) n) x‖ ≤ (K:ℝ)*((n:ℝ)+1)⁻¹ := by
  have hc : ContDiff ℝ 1 (bump (E := E)) := (bump (E := E)).contDiff
  obtain ⟨B,hB⟩ := ((bump (E := E)).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hc.continuous_fderiv (by norm_num))
  let K : ℝ≥0 := ⟨B,(norm_nonneg (fderiv ℝ (bump (E := E)) 0)).trans (hB 0)⟩
  have hl : LipschitzWith K (bump (E := E)) :=
    lipschitzWith_of_nnnorm_fderiv_le (hc.differentiable (by norm_num)) (fun x => hB x)
  refine ⟨K,fun n x => ?_⟩
  have hs : LipschitzWith (K * ‖((n:ℝ)+1)⁻¹‖₊) (cutoff (E := E) n) :=
    hl.comp (lipschitzWith_smul (((n:ℝ)+1)⁻¹) (β := E))
  have hd := norm_fderiv_le_of_lipschitz ℝ hs (x₀ := x)
  simpa only [NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ((n:ℝ)+1)⁻¹)] using hd

lemma cutoff_derivative_tendsto {K : ℝ≥0}
    (hK : ∀ n x, ‖fderiv ℝ (cutoff (E := E) n) x‖ ≤ (K:ℝ)*((n:ℝ)+1)⁻¹) (x : E) :
    Tendsto (fun n => fderiv ℝ (cutoff n) x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun n : ℕ => (K:ℝ)*((n:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div,mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (K:ℝ)
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hK n x) ht

def truncation (f : E → ℝ) (n : ℕ) : E → ℝ := fun x => cutoff n x*f x

lemma truncation_smooth {f : E → ℝ} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    ContDiff ℝ 1 (truncation f n) := (cutoff_smooth n).mul hf

lemma truncation_compact (f : E → ℝ) (n : ℕ) : HasCompactSupport (truncation f n) :=
  (cutoff_compact n).mul_right

lemma truncation_tendsto (f : E → ℝ) (x : E) :
    Tendsto (fun n => truncation f n x) atTop (𝓝 (f x)) := by
  simpa only [truncation,one_mul] using (cutoff_tendsto x).mul_const (f x)

lemma truncation_derivative {f : E → ℝ} (hf : ContDiff ℝ 1 f) (n : ℕ) (x : E) :
    fderiv ℝ (truncation f n) x = cutoff n x • fderiv ℝ f x + f x • fderiv ℝ (cutoff n) x :=
  fderiv_fun_mul ((cutoff_smooth n).differentiable (by norm_num) x)
    (hf.differentiable (by norm_num) x)

lemma truncation_derivative_tendsto {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x : E) :
    Tendsto (fun n => fderiv ℝ (truncation f n) x) atTop (𝓝 (fderiv ℝ f x)) := by
  obtain ⟨K,hK⟩ := exists_derivative_bound (E := E)
  simp_rw [truncation_derivative hf]
  simpa only [one_smul,smul_zero,add_zero] using
    ((cutoff_tendsto x).smul_const (fderiv ℝ f x)).add
      ((cutoff_derivative_tendsto hK x).const_smul (f x))

lemma truncation_abs (f : E → ℝ) (n : ℕ) (x : E) : |truncation f n x| ≤ |f x| := by
  rw [truncation,abs_mul]
  exact (mul_le_mul_of_nonneg_right (cutoff_abs n x) (abs_nonneg _)).trans_eq (one_mul _)

lemma truncation_derivative_bound {f : E → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ≥0}
    (hK : ∀ n x, ‖fderiv ℝ (cutoff (E := E) n) x‖ ≤ (K:ℝ)*((n:ℝ)+1)⁻¹) (n : ℕ) (x : E) :
    ‖fderiv ℝ (truncation f n) x‖ ≤ ‖fderiv ℝ f x‖ + (K:ℝ)*|f x| := by
  rw [truncation_derivative hf]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
  have hle : ((n:ℝ)+1)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hd := (hK n x).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hle K.coe_nonneg)
  calc
    _ ≤ 1*‖fderiv ℝ f x‖+|f x| * (K:ℝ) := add_le_add
      (mul_le_mul_of_nonneg_right (cutoff_abs n x) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
    _ = _ := by ring

variable [MeasurableSpace E] [BorelSpace E]

theorem extend (μ : Measure E) [IsProbabilityMeasure μ] {β : ℝ}
    (hP : ∀ (g : E → ℝ), ContDiff ℝ 1 g → HasCompactSupport g →
      Var[g;μ] ≤ β*∫ x, ‖fderiv ℝ g x‖^2 ∂μ)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hm : MemLp f 2 μ)
    (hd : Integrable (fun x => ‖fderiv ℝ f x‖^2) μ) :
    Var[f;μ] ≤ β*∫ x, ‖fderiv ℝ f x‖^2 ∂μ := by
  obtain ⟨K,hK⟩ := exists_derivative_bound (E := E)
  have hi : Integrable f μ := hm.integrable (by norm_num)
  have h2 : Integrable (fun x => (f x)^2) μ := hm.integrable_sq
  have ht1 : Tendsto (fun n => ∫ x, truncation f n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    exact tendsto_integral_of_dominated_convergence (fun x => |f x|)
      (fun n => (truncation_smooth hf n).continuous.aestronglyMeasurable)
      hi.abs (fun n => Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using truncation_abs f n))
      (Filter.Eventually.of_forall (truncation_tendsto f))
  have ht2 : Tendsto (fun n => ∫ x, (truncation f n x)^2 ∂μ) atTop (𝓝 (∫ x, (f x)^2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => (f x)^2)
      (fun n => ((truncation_smooth hf n).continuous.pow 2).aestronglyMeasurable) h2
    · intro n
      filter_upwards [] with x
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs,Pi.pow_apply] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (truncation_abs f n x)
    · exact Filter.Eventually.of_forall (fun x => (truncation_tendsto f x).pow 2)
  have htd : Tendsto (fun n => ∫ x, ‖fderiv ℝ (truncation f n) x‖^2 ∂μ)
      atTop (𝓝 (∫ x, ‖fderiv ℝ f x‖^2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => 2*(‖fderiv ℝ f x‖^2+(K:ℝ)^2*(f x)^2))
      (fun n => (((truncation_smooth hf n).continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable)
      ((hd.add (h2.const_mul ((K:ℝ)^2))).const_mul 2)
    · intro n
      filter_upwards [] with x
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      change ‖fderiv ℝ (truncation f n) x‖^2 ≤ _
      have hh := truncation_derivative_bound hf hK n x
      have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
      nlinarith [sq_nonneg (‖fderiv ℝ f x‖-(K:ℝ)*|f x|),sq_abs (f x)]
    · exact Filter.Eventually.of_forall (fun x => (truncation_derivative_tendsto hf x).norm.pow 2)
  rw [variance_eq_sub hm]
  simp only [Pi.pow_apply]
  apply le_of_tendsto_of_tendsto (ht2.sub (ht1.pow 2)) (htd.const_mul β)
  filter_upwards [] with n
  have hp := hP (truncation f n) (truncation_smooth hf n) (truncation_compact f n)
  have hmt : MemLp (truncation f n) 2 μ := hm.norm.mono'
    (truncation_smooth hf n).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using truncation_abs f n))
  simpa only [variance_eq_sub hmt,Pi.pow_apply] using hp

end PoincareCutoff
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianProposalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open scoped RealInnerProductSpace

def gaussianProposalPotential (d : ℕ) (x : Point d) : ℝ := inner ℝ x x / 2

lemma gaussianProposalPotential_hasGradientAt (d : ℕ) (x : Point d) :
    HasGradientAt (gaussianProposalPotential d) x x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := ((hasFDerivAt_id x).inner ℝ (hasFDerivAt_id x)).const_smul (1/2 : ℝ)
  convert! hd using 1
  · ext y
    simp only [gaussianProposalPotential,Pi.smul_apply,smul_eq_mul,id_eq]
    ring
  · ext y
    change inner ℝ x y = (1/2 : ℝ)*(inner ℝ x y+inner ℝ y x)
    rw [real_inner_comm y x]
    ring

@[simp] lemma gaussianProposalPotential_gradient (d : ℕ) :
    gradient (gaussianProposalPotential d) = id :=
  gradient_eq (gaussianProposalPotential_hasGradientAt d)

lemma gaussianProposalPotential_admissible (d : ℕ) :
    Admissible (gaussianProposalPotential d) := by
  refine ⟨(contDiff_id.inner ℝ contDiff_id).div_const 2, ?_, ?_, ?_⟩
  · simp [gaussianProposalPotential]
  · simp
  · intro x v
    simp only [gaussianProposalPotential_gradient,fderiv_id,ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq]
    constructor
    · rfl
    · nlinarith [sq_nonneg ‖v‖]

def gaussianAcceptance {d : ℕ} (V : Point d → ℝ) (x : Point d) : ℝ :=
  Real.exp (-V x+gaussianProposalPotential d x)

@[fun_prop] lemma measurable_gaussianAcceptance {d : ℕ} {V : Point d → ℝ} (hV : Admissible V) :
    Measurable (gaussianAcceptance V) :=
  (Real.continuous_exp.comp (hV.smooth.continuous.neg.add
    (gaussianProposalPotential_admissible d).smooth.continuous)).measurable

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_Poincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

def HasPoincare {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (β : ℝ) : Prop :=
  ∀ f : E → ℝ, ContDiff ℝ 1 f → MemLp f 2 μ →
    Integrable (fun x => ‖fderiv ℝ f x‖^2) μ →
    Var[f;μ] ≤ β*∫ x, ‖fderiv ℝ f x‖^2 ∂μ

section
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G] in
lemma derivative_comp_lipschitz_bound {S : E → G} {K : ℝ≥0}
    (hS : ContDiff ℝ 1 S) (hK : LipschitzWith K S)
    {f : G → ℝ} (hf : ContDiff ℝ 1 f) (x : E) :
    ‖fderiv ℝ (f ∘ S) x‖^2 ≤ (K:ℝ)^2*‖fderiv ℝ f (S x)‖^2 := by
  rw [fderiv_comp x (hf.differentiable (by norm_num) _) (hS.differentiable (by norm_num) _)]
  have hh := (ContinuousLinearMap.opNorm_comp_le (fderiv ℝ f (S x)) (fderiv ℝ S x)).trans
    (mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hK) (norm_nonneg _))
  have hp := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
  simpa only [mul_pow,mul_comm] using hp

theorem HasPoincare.map {μ : Measure E} [IsProbabilityMeasure μ] {β : ℝ}
    (hP : HasPoincare μ β) (hβ : 0 ≤ β) {S : E → G} {K : ℝ≥0}
    (hS : ContDiff ℝ 1 S) (hK : LipschitzWith K S) :
    HasPoincare (μ.map S) (β*(K:ℝ)^2) := by
  intro f hf hm hd
  have hc : ContDiff ℝ 1 (f ∘ S) := hf.comp hS
  have hm' : MemLp (f ∘ S) 2 μ := hm.comp_of_map hS.continuous.aemeasurable
  have hdm : AEStronglyMeasurable (fun y => ‖fderiv ℝ f y‖^2) (μ.map S) :=
    ((hf.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable
  have hi : Integrable (fun x => ‖fderiv ℝ f (S x)‖^2) μ :=
    (integrable_map_measure hdm hS.continuous.aemeasurable).1 hd
  have hb := derivative_comp_lipschitz_bound hS hK hf
  have hi' : Integrable (fun x => ‖fderiv ℝ (f ∘ S) x‖^2) μ := by
    apply (hi.const_mul ((K:ℝ)^2)).mono'
      ((hc.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hb x
  have hh := hP (f ∘ S) hc hm' hi'
  rw [variance_map hf.continuous.aemeasurable hS.continuous.aemeasurable,
    integral_map hS.continuous.aemeasurable hdm]
  calc
    _ ≤ β*∫ x, ‖fderiv ℝ (f ∘ S) x‖^2 ∂μ := hh
    _ ≤ β*∫ x, (K:ℝ)^2*‖fderiv ℝ f (S x)‖^2 ∂μ :=
      mul_le_mul_of_nonneg_left (integral_mono hi' (hi.const_mul _) hb) hβ
    _ = _ := by rw [integral_const_mul]; ring

omit [BorelSpace E] in
lemma HasPoincare.mono {μ : Measure E} {β γ : ℝ}
    (hP : HasPoincare μ β) (h : β ≤ γ) : HasPoincare μ γ := by
  intro f hf hm hd
  exact (hP f hf hm hd).trans (mul_le_mul_of_nonneg_right h
    (integral_nonneg (fun _ => sq_nonneg _)))

lemma HasPoincare.lipschitz_variance {μ : Measure E} [IsProbabilityMeasure μ] {β : ℝ}
    (hP : HasPoincare μ β) (hβ : 0 ≤ β) {f : E → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hK : LipschitzWith K f) (hm : MemLp f 2 μ) :
    Var[f;μ] ≤ β*(K:ℝ)^2 := by
  have hb (x : E) : ‖fderiv ℝ f x‖^2 ≤ (K:ℝ)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hK) 2
  have hi : Integrable (fun x => ‖fderiv ℝ f x‖^2) μ :=
    Integrable.mono' (integrable_const ((K:ℝ)^2))
      ((hf.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact hb x))
  apply (hP f hf hm hi).trans
  apply mul_le_mul_of_nonneg_left _ hβ
  simpa only [integral_const,probReal_univ,one_smul] using integral_mono hi (integrable_const _) hb
end
end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory

theorem Primitive.hasPoincare {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) :
    HasPoincare (gibbs (primitivePotential F x r))
      ((Real.pi^2/8)*(2/(1-(lam:ℝ)*r^2))) := by
  have : IsProbabilityMeasure (gibbs (primitivePotential F x r)) :=
    probability_gibbs_of_partition
      (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
      (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl))
  intro f hf hm hd
  exact PoincareCutoff.extend _ (fun g hg hc => hF.poincare_compact x hr hl hg hc) hf hm hd
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Growth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace Appell
open MeasureTheory
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

def HasGrowth (f : E → F) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C*(1+‖x‖^n)

lemma pow_le_one_add_pow_add {a : ℝ} (ha : 0 ≤ a) (n m : ℕ) :
    a^n ≤ 1+a^(n+m) := by
  by_cases h : a ≤ 1
  · exact (pow_le_one₀ ha h).trans (le_add_of_nonneg_right (by positivity))
  · have h' : 1 ≤ a := le_of_not_ge h
    have hp := mul_le_mul_of_nonneg_left (one_le_pow₀ h' : 1 ≤ a^m)
      (pow_nonneg ha n)
    rw [mul_one,← pow_add] at hp
    linarith

lemma HasGrowth.const (c : F) : HasGrowth (fun _ : E => c) := by
  exact ⟨‖c‖,norm_nonneg _,0,fun _ => by simp only [pow_zero]; nlinarith [norm_nonneg c]⟩

lemma HasGrowth.add {f g : E → F} (hf : HasGrowth f) (hg : HasGrowth g) :
    HasGrowth (fun x => f x+g x) := by
  obtain ⟨A,hA,n,hn⟩ := hf
  obtain ⟨B,hB,m,hm⟩ := hg
  refine ⟨2*(A+B),by positivity,n+m,fun x => ?_⟩
  have ha := pow_le_one_add_pow_add (norm_nonneg x) n m
  have hb := pow_le_one_add_pow_add (norm_nonneg x) m n
  rw [Nat.add_comm m n] at hb
  have h := (norm_add_le (f x) (g x)).trans (add_le_add (hn x) (hm x))
  nlinarith [mul_le_mul_of_nonneg_left ha hA,mul_le_mul_of_nonneg_left hb hB,
    mul_nonneg hA (pow_nonneg (norm_nonneg x) (n+m)),mul_nonneg hB (pow_nonneg (norm_nonneg x) (n+m))]

lemma HasGrowth.smul [NormedSpace ℝ F] {f : E → ℝ} {g : E → F}
    (hf : HasGrowth f) (hg : HasGrowth g) : HasGrowth (fun x => f x • g x) := by
  obtain ⟨A,hA,n,hn⟩ := hf
  obtain ⟨B,hB,m,hm⟩ := hg
  refine ⟨4*A*B,by positivity,n+m,fun x => ?_⟩
  rw [norm_smul]
  have h := mul_le_mul (hn x) (hm x) (norm_nonneg _) (by positivity)
  have ha := pow_le_one_add_pow_add (norm_nonneg x) n m
  have hb := pow_le_one_add_pow_add (norm_nonneg x) m n
  rw [Nat.add_comm m n] at hb
  have he : (1+‖x‖^n)*(1+‖x‖^m) ≤ 4*(1+‖x‖^(n+m)) := by
    rw [pow_add] at ha hb ⊢
    nlinarith [pow_nonneg (norm_nonneg x) n,pow_nonneg (norm_nonneg x) m]
  have hh := mul_le_mul_of_nonneg_left he (mul_nonneg hA hB)
  nlinarith

lemma HasGrowth.mul {f g : E → ℝ} (hf : HasGrowth f) (hg : HasGrowth g) :
    HasGrowth (fun x => f x*g x) := hf.smul hg

lemma HasGrowth.norm {f : E → F} (hf : HasGrowth f) : HasGrowth (fun x => ‖f x‖) := by
  simpa only [HasGrowth,norm_norm] using hf

lemma HasGrowth.pow {f : E → ℝ} (hf : HasGrowth f) (n : ℕ) :
    HasGrowth (fun x => (f x)^n) := by
  induction n with
  | zero => simpa using HasGrowth.const (E := E) (1:ℝ)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma HasGrowth.sum {ι : Type*} (s : Finset ι) {f : ι → E → F}
    (hf : ∀ i ∈ s, HasGrowth (f i)) : HasGrowth (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasGrowth.const (E := E) (0:F)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma HasGrowth.prod {ι : Type*} (s : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i ∈ s, HasGrowth (f i)) : HasGrowth (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasGrowth.const (E := E) (1:ℝ)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma HasGrowth.linear [NormedSpace ℝ E] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    HasGrowth L := by
  refine ⟨‖L‖,norm_nonneg _,1,fun x => ?_⟩
  exact (L.le_opNorm x).trans (by simp only [pow_one]; nlinarith [norm_nonneg L])

lemma HasGrowth.lipschitz {K : ℝ≥0} {f : E → F} (hf : LipschitzWith K f) : HasGrowth f := by
  refine ⟨(K:ℝ)+‖f 0‖,by positivity,1,fun x => ?_⟩
  have hh := hf.dist_le_mul x 0
  rw [dist_eq_norm,dist_zero_right] at hh
  simp only [pow_one]
  nlinarith [norm_le_norm_sub_add (f x) (f 0),mul_nonneg (norm_nonneg (f 0)) (norm_nonneg x)]

variable [MeasurableSpace E]

def HasMoments (μ : Measure E) : Prop := ∀ n : ℕ, Integrable (fun x : E => ‖x‖^n) μ

lemma HasGrowth.integrable {μ : Measure E} [IsFiniteMeasure μ] {f : E → F}
    (hf : HasGrowth f) (hm : AEStronglyMeasurable f μ) (hμ : HasMoments μ) : Integrable f μ := by
  obtain ⟨C,hC,n,hn⟩ := hf
  exact (((integrable_const (1:ℝ)).add (hμ n)).const_mul C).mono' hm
    (Filter.Eventually.of_forall hn)

lemma HasGrowth.memLp {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : HasGrowth f) (hm : AEStronglyMeasurable f μ) (hμ : HasMoments μ) : MemLp f 2 μ := by
  exact (memLp_two_iff_integrable_sq hm).2 ((hf.pow 2).integrable (hm.pow 2) hμ)

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

variable {ι : Type*} [DecidableEq ι]

def inverseMoment (m : Finset ι → ℝ) (s : Finset ι) : ℝ :=
  if _hs : s = ∅ then 1 else
    -∑ t ∈ (s.powerset.filter (fun t => t ≠ s)).attach, m (s \ t.1)*inverseMoment m t.1
termination_by s.card
decreasing_by
  have ht := (Finset.mem_filter.mp t.2)
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.mem_powerset.mp ht.1,ht.2⟩)

@[simp] lemma inverseMoment_empty (m : Finset ι → ℝ) : inverseMoment m ∅ = 1 := by
  rw [inverseMoment]
  simp

lemma inverseMoment_convolution (m : Finset ι → ℝ) (hm : m ∅ = 1) (s : Finset ι) :
    ∑ t ∈ s.powerset, m (s \ t)*inverseMoment m t = if s = ∅ then 1 else 0 := by
  by_cases hs : s = ∅
  · subst s
    simp [hm]
  have hmem : s ∈ s.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl s)
  have he : s.powerset.filter (fun t => t ≠ s) = s.powerset.erase s := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_erase]
    tauto
  have hi := inverseMoment.eq_def m s
  simp only [hs,↓reduceDIte] at hi
  change inverseMoment m s = -∑ t ∈ (s.powerset.filter (fun t => t ≠ s)).attach,
    (fun t => m (s \ t)*inverseMoment m t) t.1 at hi
  have hat := Finset.sum_attach (s.powerset.filter (fun t => t ≠ s))
    (fun t => m (s \ t)*inverseMoment m t)
  rw [hat,he] at hi
  rw [ite_eq_right hs,← Finset.sum_erase_add _ _ hmem]
  simp only [Finset.sdiff_self,hm,one_mul]
  linarith

lemma inverseMoment_nonempty (m : Finset ι → ℝ) {s : Finset ι} (hs : s ≠ ∅) :
    inverseMoment m s = -∑ t ∈ s.powerset.erase s, m (s \ t)*inverseMoment m t := by
  have h := inverseMoment.eq_def m s
  simp only [hs,↓reduceDIte] at h
  have hat := Finset.sum_attach (s.powerset.filter (fun t => t ≠ s))
    (fun t => m (s \ t)*inverseMoment m t)
  rw [hat] at h
  convert! h using 2
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext t
  simp only [Finset.mem_filter,Finset.mem_erase]
  tauto

lemma inverseMoment_image {κ : Type*} [DecidableEq κ] (e : ι → κ)
    (he : Function.Injective e) (m : Finset κ → ℝ) (s : Finset ι) :
    inverseMoment (fun t => m (t.image e)) s = inverseMoment m (s.image e) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s; simp
    have hs' : s.image e ≠ ∅ := by simpa using hs
    rw [inverseMoment_nonempty _ hs,inverseMoment_nonempty _ hs']
    have hi : Function.Injective (fun t : Finset ι => t.image e) := Finset.image_injective he
    have hp : (s.image e).powerset.erase (s.image e) =
        (s.powerset.erase s).image (fun t => t.image e) := by
      rw [Finset.powerset_image,← Finset.image_erase hi]
    rw [hp,Finset.sum_image]
    · congr 1
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.image_sdiff _ _ he,
        ih t (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2,
          (Finset.mem_erase.mp ht).1⟩)]
    · exact fun _ _ _ _ h => hi h

def polynomial (m : Finset ι → ℝ) (s : Finset ι) (z : ι → ℝ) : ℝ :=
  ∑ t ∈ s.powerset, inverseMoment m t * ∏ i ∈ s \ t, z i

@[simp] lemma polynomial_empty (m : Finset ι → ℝ) (z : ι → ℝ) : polynomial m ∅ z = 1 := by
  simp [polynomial]

lemma polynomial_image {κ : Type*} [DecidableEq κ] (e : ι → κ)
    (he : Function.Injective e) (m : Finset κ → ℝ) (s : Finset ι) (z : κ → ℝ) :
    polynomial (fun t => m (t.image e)) s (z ∘ e) = polynomial m (s.image e) z := by
  rw [polynomial,polynomial,Finset.powerset_image,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [inverseMoment_image e he m,← Finset.image_sdiff _ _ he,Finset.prod_image]
    · rfl
    · exact fun _ _ _ _ h => he h
  · exact fun _ _ _ _ h => Finset.image_injective he h

def moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ι → Ω → ℝ)
    (s : Finset ι) : ℝ := ∫ ω, ∏ i ∈ s, X i ω ∂μ

omit [DecidableEq ι] in
lemma moments_empty {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) : moments μ X ∅ = 1 := by simp [moments]

omit [DecidableEq ι] in
lemma moments_image {Ω κ : Type*} [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) (X : κ → Ω → ℝ) (e : ι → κ) (he : Function.Injective e) (s : Finset ι) :
    moments μ (X ∘ e) s = moments μ X (s.image e) := by
  unfold moments
  congr 1
  funext ω
  rw [Finset.prod_image]
  · rfl
  · exact fun _ _ _ _ h => he h

lemma integral_polynomial {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (s : Finset ι)
    (hX : ∀ t ⊆ s, Integrable (fun ω => ∏ i ∈ t, X i ω) μ) :
    (∫ ω, polynomial (moments μ X) s (fun i => X i ω) ∂μ) = if s = ∅ then 1 else 0 := by
  simp only [polynomial]
  rw [integral_finsetSum _ (fun t ht => (hX (s \ t) Finset.sdiff_subset).const_mul _)]
  simp only [integral_const_mul]
  simpa only [moments,mul_comm] using inverseMoment_convolution (moments μ X) (moments_empty μ X) s

lemma sum_powerset_sdiff {M : Type*} [AddCommMonoid M] (s : Finset ι)
    (F : ι → Finset ι → M) :
    (∑ t ∈ s.powerset, ∑ i ∈ s \ t, F i t) =
      ∑ i ∈ s, ∑ t ∈ (s.erase i).powerset, F i t := by
  have hsd (t : Finset ι) : ∑ i ∈ s \ t, F i t = ∑ i ∈ s, if i ∉ t then F i t else 0 := by
    have he : s \ t = s.filter (fun i => i ∉ t) := by ext i; simp
    rw [he,Finset.sum_filter]
  simp_rw [hsd]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext t
  simp only [Finset.mem_filter,Finset.mem_powerset,Finset.subset_erase]

section Derivatives
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma polynomial_contDiff (m : Finset ι → ℝ) (s : Finset ι) (a : ι → E →L[ℝ] ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : E => polynomial m s (fun i => a i z)) := by
  unfold polynomial
  apply ContDiff.sum
  intro t ht
  apply contDiff_const.mul
  apply contDiff_prod
  intro i hi
  exact (a i).contDiff

lemma hasFDerivAt_polynomial (m : Finset ι → ℝ) (s : Finset ι)
    (a : ι → E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (fun z : E => polynomial m s (fun i => a i z))
      (∑ i ∈ s, polynomial m (s.erase i) (fun j => a j x) • a i) x := by
  have hd : HasFDerivAt (fun z : E => polynomial m s (fun i => a i z))
      (∑ t ∈ s.powerset, inverseMoment m t •
        ∑ i ∈ s \ t, (∏ j ∈ (s \ t).erase i, a j x) • a i) x := by
    apply HasFDerivAt.fun_sum
    intro t ht
    exact (HasFDerivAt.finsetProd (fun i hi => (a i).hasFDerivAt)).const_mul _
  apply hd.congr_fderiv
  simp only [Finset.smul_sum,smul_smul]
  have hset (i : ι) (t : Finset ι) : (s \ t).erase i = s.erase i \ t := by
    ext j
    simp only [Finset.mem_erase,Finset.mem_sdiff]
    tauto
  simp_rw [hset]
  rw [sum_powerset_sdiff]
  simp only [polynomial,Finset.sum_smul]

end Derivatives
end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def coordinate (b : OrthonormalBasis κ ℝ E) (i : κ) : E →L[ℝ] ℝ := innerSL ℝ (b i)

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma coordinate_basis (b : OrthonormalBasis κ ℝ E) (i j : κ) :
    coordinate b i (b j) = if i = j then 1 else 0 := by
  exact orthonormal_iff_ite.mp b.orthonormal i j

def slotPolynomial (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (s : Finset ι) (x : E) : ℝ :=
  polynomial (moments μ (fun i => coordinate b (a i))) s (fun i => coordinate b (a i) x)

def tensorPolynomial (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) (x : E) : ℝ :=
  ∑ a, T a * slotPolynomial μ b a Finset.univ x

omit [MeasurableSpace E] [BorelSpace E] in
lemma growth_polynomial {J : Type*} [DecidableEq J] (m : Finset J → ℝ)
    (s : Finset J) (a : J → E →L[ℝ] ℝ) :
    HasGrowth (fun x => polynomial m s (fun i => a i x)) := by
  exact HasGrowth.sum _ (fun t ht => (HasGrowth.const _).mul
    (HasGrowth.prod _ (fun i hi => HasGrowth.linear (a i))))

omit [BorelSpace E] [Fintype ι] [DecidableEq κ] in
lemma slotPolynomial_growth (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (s : Finset ι) : HasGrowth (slotPolynomial μ b a s) :=
  growth_polynomial _ _ _

omit [DecidableEq κ] in
omit [BorelSpace E] in
lemma tensorPolynomial_growth (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) : HasGrowth (tensorPolynomial μ b T) :=
  HasGrowth.sum _ (fun a _ha => (HasGrowth.const _).mul (slotPolynomial_growth μ b a _))

omit [BorelSpace E] [Fintype ι] [DecidableEq κ] in
lemma slotPolynomial_smooth (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (s : Finset ι) : ContDiff ℝ (⊤ : ℕ∞) (slotPolynomial μ b a s) :=
  polynomial_contDiff _ _ _

omit [BorelSpace E] [DecidableEq κ] in
lemma tensorPolynomial_smooth (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (tensorPolynomial μ b T) :=
  ContDiff.sum (fun a _ha => contDiff_const.mul (slotPolynomial_smooth μ b a _))

omit [Fintype ι] [DecidableEq κ] in
lemma integral_slotPolynomial (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    (b : OrthonormalBasis κ ℝ E) (a : ι → κ) (s : Finset ι) :
    (∫ x, slotPolynomial μ b a s x ∂μ) = if s = ∅ then 1 else 0 := by
  apply integral_polynomial
  intro t ht
  exact (HasGrowth.prod t (fun i hi => HasGrowth.linear (coordinate b (a i)))).integrable
    (continuous_finsetProd _ (fun i hi => (coordinate b (a i)).continuous)).aestronglyMeasurable hμ

omit [DecidableEq κ] in
lemma integral_tensorPolynomial (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    (b : OrthonormalBasis κ ℝ E) (T : (ι → κ) → ℝ) [Nonempty ι] :
    (∫ x, tensorPolynomial μ b T x ∂μ) = 0 := by
  simp only [tensorPolynomial]
  rw [integral_finsetSum]
  · simp only [integral_const_mul,integral_slotPolynomial μ hμ,
      Finset.univ_eq_empty_iff,not_isEmpty_of_nonempty,↓reduceIte,mul_zero,Finset.sum_const_zero]
  · intro a ha
    exact ((slotPolynomial_growth μ b a _).integrable
      (slotPolynomial_smooth μ b a _).continuous.aestronglyMeasurable hμ).const_mul _

omit [BorelSpace E] [DecidableEq κ] in
lemma slotPolynomial_erase (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (i : ι) (x : E) :
    slotPolynomial μ b a (Finset.univ.erase i) x =
      slotPolynomial μ b (fun j : {j // j ≠ i} => a j) Finset.univ x := by
  have he : (Finset.univ : Finset {j : ι // j ≠ i}).image Subtype.val = Finset.univ.erase i := by
    ext j
    simp
  have hm : moments μ (fun j : {j : ι // j ≠ i} => coordinate b (a j)) =
      fun t => moments μ (fun j : ι => coordinate b (a j)) (t.image Subtype.val) := by
    funext t
    exact moments_image μ (fun j : ι => coordinate b (a j)) Subtype.val Subtype.val_injective t
  unfold slotPolynomial
  rw [hm]
  simpa only [Function.comp_def,he] using
    (polynomial_image (fun j : {j : ι // j ≠ i} => j.val) Subtype.val_injective
      (moments μ (fun j : ι => coordinate b (a j))) Finset.univ
      (fun j => coordinate b (a j) x)).symm

def slice (T : (ι → κ) → ℝ) (i : ι) (k : κ) (a : {j // j ≠ i} → κ) : ℝ :=
  T ((Equiv.piSplitAt i (fun _ => κ)).symm (k,a))

omit [BorelSpace E] [DecidableEq κ] in
lemma hasFDerivAt_tensorPolynomial (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) (x : E) :
    HasFDerivAt (tensorPolynomial μ b T)
      (∑ a, T a • ∑ i, slotPolynomial μ b a (Finset.univ.erase i) x • coordinate b (a i)) x := by
  exact HasFDerivAt.fun_sum (fun a _ha => (hasFDerivAt_polynomial _ _ _ x).const_mul (T a))

omit [BorelSpace E] in
lemma derivative_tensorPolynomial_basis (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) (x : E) (k : κ) :
    fderiv ℝ (tensorPolynomial μ b T) x (b k) =
      ∑ i, tensorPolynomial μ b (slice T i k) x := by
  rw [(hasFDerivAt_tensorPolynomial μ b T x).fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul,
    coordinate_basis,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← (Equiv.piSplitAt i (fun _ => κ)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.piSplitAt_symm_apply,dite_true]
  simp only [mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold tensorPolynomial
  apply Finset.sum_congr rfl
  intro a ha
  rw [slotPolynomial_erase]
  congr 1
  congr 1
  funext j
  simp [Equiv.piSplitAt_symm_apply,j.prop]

omit [DecidableEq κ] in
lemma tensorPolynomial_memLp (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    (b : OrthonormalBasis κ ℝ E) (T : (ι → κ) → ℝ) :
    MemLp (tensorPolynomial μ b T) 2 μ :=
  (tensorPolynomial_growth μ b T).memLp
    (tensorPolynomial_smooth μ b T).continuous.aestronglyMeasurable hμ

omit [DecidableEq κ] in
omit [BorelSpace E] in
lemma tensorPolynomial_derivative_growth (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) : HasGrowth (fun x => fderiv ℝ (tensorPolynomial μ b T) x) := by
  simp only [(hasFDerivAt_tensorPolynomial μ b T _).fderiv]
  exact HasGrowth.sum _ (fun a _ha => (HasGrowth.const _).smul
    (HasGrowth.sum _ (fun i _hi => (slotPolynomial_growth μ b a _).smul (HasGrowth.const _))))

omit [DecidableEq κ] in
lemma tensorPolynomial_derivative_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : HasMoments μ) (b : OrthonormalBasis κ ℝ E) (T : (ι → κ) → ℝ) :
    Integrable (fun x => ‖fderiv ℝ (tensorPolynomial μ b T) x‖^2) μ := by
  have hd : Continuous (fun x => fderiv ℝ (tensorPolynomial μ b T) x) :=
    (tensorPolynomial_smooth μ b T).continuous_fderiv (by simp)
  exact ((tensorPolynomial_derivative_growth μ b T).norm.pow 2).integrable
    (hd.norm.pow 2).aestronglyMeasurable hμ

omit [MeasurableSpace E] [BorelSpace E] [DecidableEq ι] in
lemma sq_sum_le_card_mul_sum_sq (f : ι → ℝ) :
    (∑ i, f i)^2 ≤ (Fintype.card ι:ℝ)*∑ i, (f i)^2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1:ℝ)) f

omit [BorelSpace E] in
lemma tensorPolynomial_derivative_bound (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) (x : E) :
    ‖fderiv ℝ (tensorPolynomial μ b T) x‖^2 ≤
      (Fintype.card ι:ℝ)*∑ i, ∑ k, (tensorPolynomial μ b (slice T i k) x)^2 := by
  rw [b.norm_dual]
  simp_rw [derivative_tensorPolynomial_basis μ b T]
  calc
    _ ≤ ∑ k, (Fintype.card ι:ℝ)*∑ i, (tensorPolynomial μ b (slice T i k) x)^2 :=
      Finset.sum_le_sum (fun k hk => sq_sum_le_card_mul_sum_sq _)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

lemma tensorPolynomial_one_step (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) [Nonempty ι] :
    (∫ x, (tensorPolynomial μ b T x)^2 ∂μ) ≤
      β*(Fintype.card ι:ℝ)*∑ i, ∑ k, ∫ x, (tensorPolynomial μ b (slice T i k) x)^2 ∂μ := by
  have hi (i : ι) (k : κ) : Integrable (fun x => (tensorPolynomial μ b (slice T i k) x)^2) μ :=
    (tensorPolynomial_memLp μ hμ b _).integrable_sq
  have hp := hP _ ((tensorPolynomial_smooth μ b T).of_le (by simp))
    (tensorPolynomial_memLp μ hμ b T) (tensorPolynomial_derivative_integrable μ hμ b T)
  rw [variance_eq_sub (tensorPolynomial_memLp μ hμ b T),integral_tensorPolynomial μ hμ,
    zero_pow (by norm_num : 2 ≠ 0),sub_zero] at hp
  have hh := integral_mono (tensorPolynomial_derivative_integrable μ hμ b T)
    ((integrable_finsetSum _ (fun i hi' => integrable_finsetSum _ (fun k hk => hi i k))).const_mul
      (Fintype.card ι:ℝ)) (tensorPolynomial_derivative_bound μ b T)
  rw [integral_const_mul,integral_finsetSum] at hh
  · simp_rw [integral_finsetSum _ (fun k hk => hi _ k)] at hh
    exact hp.trans ((mul_le_mul_of_nonneg_left hh hβ).trans_eq (by ring))
  · intro i hi'
    exact integrable_finsetSum _ (fun k hk => hi i k)

omit [MeasurableSpace E] [BorelSpace E] [DecidableEq κ] in
lemma slice_energy (T : (ι → κ) → ℝ) (i : ι) :
    (∑ k, ∑ a, (slice T i k a)^2) = ∑ a, (T a)^2 := by
  simpa only [slice,Fintype.sum_prod_type] using
    (Equiv.piSplitAt i (fun _ => κ)).symm.sum_comp (fun a => (T a)^2)

universe u

theorem tensorPolynomial_L2_aux (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E)
    (n : ℕ) : ∀ (J : Type u) [Fintype J] [DecidableEq J], Fintype.card J = n →
      ∀ T : (J → κ) → ℝ,
      (∫ x, (tensorPolynomial μ b T x)^2 ∂μ) ≤
        β^n*(n.factorial:ℝ)^2*∑ a, (T a)^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J _ _ hc T
    by_cases hn : n = 0
    · have : IsEmpty J := Fintype.card_eq_zero_iff.mp (hc.trans hn)
      let a : J → κ := fun j => isEmptyElim j
      let : Unique (J → κ) := ⟨⟨a⟩,fun f => funext (fun j => isEmptyElim j)⟩
      simp [hn,tensorPolynomial,slotPolynomial]
    have hp : 0 < n := Nat.pos_of_ne_zero hn
    have : Nonempty J := Fintype.card_pos_iff.mp (hc ▸ hp)
    have hcard (i : J) : Fintype.card {j : J // j ≠ i} = n-1 := by
      rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,hc]
    let C : ℝ := β^(n-1)*((n-1).factorial:ℝ)^2
    have hb (i : J) (k : κ) :
        (∫ x, (tensorPolynomial μ b (slice T i k) x)^2 ∂μ) ≤
          C*∑ a, (slice T i k a)^2 :=
      ih (n-1) (Nat.sub_lt hp (by norm_num)) _ (hcard i) (slice T i k)
    have hh := (tensorPolynomial_one_step μ hμ hβ hP b T).trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi =>
        Finset.sum_le_sum (fun k hk => hb i k))) (mul_nonneg hβ (Nat.cast_nonneg (Fintype.card J))))
    have he : (∑ i, ∑ k, C*∑ a, (slice T i k a)^2) = C*(n:ℝ)*∑ a, (T a)^2 := by
      simp_rw [← Finset.mul_sum,slice_energy]
      simp only [Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul]
      ring
    rw [he] at hh
    have hn' : n-1+1=n := Nat.sub_add_cancel hp
    have hf : (n.factorial:ℝ) = (n:ℝ)*((n-1).factorial:ℝ) := by
      have hf' := Nat.factorial_succ (n-1)
      rw [hn'] at hf'
      exact_mod_cast hf'
    have hpow : β^n=β^(n-1)*β := by
      calc β^n = β^(n-1+1) := congrArg (fun j => β^j) hn'.symm
           _ = β^(n-1)*β := pow_succ _ _
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [hc,hf,hpow]
    dsimp [C]
    ring

theorem tensorPolynomial_L2 (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) :
    (∫ x, (tensorPolynomial μ b T x)^2 ∂μ) ≤
      β^(Fintype.card ι)*((Fintype.card ι).factorial:ℝ)^2*∑ a, (T a)^2 :=
  tensorPolynomial_L2_aux μ hμ hβ hP b _ ι rfl T

end Appell
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_CrossMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma integral_mul_sq_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) := by
  have hi (f g : X → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x*g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp [hx,hy,mul_comm]
  have hh := sq_le_sq₀ (norm_nonneg (inner ℝ (hf.toLp f) (hg.toLp g)))
    (mul_nonneg (norm_nonneg (hf.toLp f)) (norm_nonneg (hg.toLp g))) |>.mpr
      (norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (hg.toLp g))
  rw [Real.norm_eq_abs,sq_abs,mul_pow,← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq,hi,hi,hi] at hh
  simpa only [pow_two] using hh

namespace Appell
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι ϑ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
  [Fintype κ] [DecidableEq κ]

def crossMoment (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) : ℝ :=
  ∫ x, slotPolynomial μ b a Finset.univ x * slotPolynomial μ b c Finset.univ x ∂μ

omit [DecidableEq κ] in
lemma sum_crossMoment (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    (b : OrthonormalBasis κ ℝ E) (T : (ι → κ) → ℝ) (U : (ϑ → κ) → ℝ) :
    (∑ a, ∑ c, T a * crossMoment μ b a c * U c) =
      ∫ x, tensorPolynomial μ b T x * tensorPolynomial μ b U x ∂μ := by
  have hh (a : ι → κ) (c : ϑ → κ) : Integrable
      (fun x => T a * slotPolynomial μ b a Finset.univ x *
        (U c * slotPolynomial μ b c Finset.univ x)) μ :=
    ((((slotPolynomial_growth μ b a _).mul (slotPolynomial_growth μ b c _)).integrable
      ((slotPolynomial_smooth μ b a _).continuous.mul
        (slotPolynomial_smooth μ b c _).continuous).aestronglyMeasurable hμ).const_mul
      (T a*U c)).congr (Filter.Eventually.of_forall (fun x => by ring))
  simp only [tensorPolynomial,Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun a ha => integrable_finsetSum _ (fun c hc => hh a c))]
  simp_rw [integral_finsetSum _ (fun c hc => hh _ c)]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  rw [show (fun x => T a * slotPolynomial μ b a Finset.univ x *
      (U c * slotPolynomial μ b c Finset.univ x)) =
      (fun x => (T a*U c) * (slotPolynomial μ b a Finset.univ x *
        slotPolynomial μ b c Finset.univ x)) by funext x; ring,integral_const_mul]
  simp only [crossMoment]
  ring

theorem crossMoment_sq_bound (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) (U : (ϑ → κ) → ℝ) :
    (∑ a, ∑ c, T a * crossMoment μ b a c * U c)^2 ≤
      (β^(Fintype.card ι)*((Fintype.card ι).factorial:ℝ)^2) *
      (β^(Fintype.card ϑ)*((Fintype.card ϑ).factorial:ℝ)^2) *
      (∑ a, (T a)^2)*(∑ c, (U c)^2) := by
  rw [sum_crossMoment μ hμ]
  have hh := (integral_mul_sq_le (tensorPolynomial_memLp μ hμ b T)
    (tensorPolynomial_memLp μ hμ b U)).trans
    (mul_le_mul (tensorPolynomial_L2 μ hμ hβ hP b T)
      (tensorPolynomial_L2 μ hμ hβ hP b U)
      (integral_nonneg (fun _ => sq_nonneg _)) (by positivity))
  exact hh.trans_eq (by ring)
end Appell
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace TensorEnergy
open scoped BigOperators

variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

def Bound (A : I → J → ℝ) (C : ℝ) : Prop :=
  ∀ v : J → ℝ, (∑ i, (∑ j, A i j*v j)^2) ≤ C*∑ j, (v j)^2

lemma energy_nonneg (v : I → ℝ) : 0 ≤ ∑ i, (v i)^2 :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma bound_of_bilinear {A : I → J → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (u : I → ℝ) (v : J → ℝ), (∑ i, ∑ j, u i*A i j*v j)^2 ≤ C*(∑ i, (u i)^2)*(∑ j, (v j)^2)) :
    Bound A C := by
  intro v
  let w : I → ℝ := fun i => ∑ j, A i j*v j
  have he : (∑ i, ∑ j, w i*A i j*v j) = ∑ i, (w i)^2 := by
    simp only [mul_assoc,← Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by dsimp [w]; ring)
  have hh := h w v
  rw [he] at hh
  have hw := energy_nonneg w
  by_cases hz : (∑ i, (w i)^2) = 0
  · change (∑ i, (w i)^2) ≤ _
    rw [hz]
    exact mul_nonneg hC (energy_nonneg v)
  · have hp : 0 < ∑ i, (w i)^2 := lt_of_le_of_ne hw (Ne.symm hz)
    have hh' : (∑ i, (w i)^2)*(∑ i, (w i)^2) ≤
        (C*∑ j, (v j)^2)*(∑ i, (w i)^2) := by nlinarith [hh]
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa only [mul_comm] using hh')

lemma Bound.kronecker {A : I → J → ℝ} {B : K → L → ℝ} {C D : ℝ}
    (hA : Bound A C) (hB : Bound B D) (hC : 0 ≤ C) :
    Bound (fun (i : I × K) (j : J × L) => A i.1 j.1*B i.2 j.2) (C*D) := by
  intro v
  simp only [Fintype.sum_prod_type]
  have he (i : I) (k : K) :
      (∑ j, ∑ l, (A i j*B k l)*v (j,l)) = ∑ j, A i j*(∑ l, B k l*v (j,l)) := by
    simp only [Finset.mul_sum,mul_assoc]
  simp_rw [he]
  rw [Finset.sum_comm]
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset K)) =>
    hA (fun j => ∑ l, B k l*v (j,l)))
  rw [← Finset.mul_sum] at hh
  conv at hh => rhs; arg 2; rw [Finset.sum_comm]
  have hg := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) =>
      hB (fun l => v (j,l)))) hC
  rw [← Finset.mul_sum] at hg
  exact hh.trans (hg.trans_eq (by ring))

lemma Bound.reindex {A : I → J → ℝ} {C : ℝ} (h : Bound A C)
    (e : K ≃ I) (f : L ≃ J) : Bound (fun k l => A (e k) (f l)) C := by
  intro v
  have hh := h (v ∘ f.symm)
  rw [← e.sum_comp] at hh
  simp_rw [← f.sum_comp] at hh
  simpa only [Function.comp_def,Equiv.symm_apply_apply] using hh

lemma prod_split {N : Type*} [Fintype N] [DecidableEq N] (i : N) (f : N → ℝ) :
    (∏ j, f j) = f i * ∏ j : {j : N // j ≠ i}, f j := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  congr 1
  exact Finset.prod_subtype _ (by simp) _

universe u v w
lemma bound_pi_aux (n : ℕ) : ∀ (N : Type u) [Fintype N] [DecidableEq N],
    Fintype.card N = n → ∀ (A : N → Type v) (B : N → Type w)
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (M : ∀ i, A i → B i → ℝ) (C : N → ℝ),
    (∀ i, 0 ≤ C i) → (∀ i, Bound (M i) (C i)) →
    Bound (fun (a : ∀ i, A i) (b : ∀ i, B i) => ∏ i, M i (a i) (b i)) (∏ i, C i) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro N _ _ hc A B _ _ M C hC hM
    by_cases hn : n=0
    · have : IsEmpty N := Fintype.card_eq_zero_iff.mp (hc.trans hn)
      let a : ∀ i, A i := fun i => isEmptyElim i
      let b : ∀ i, B i := fun i => isEmptyElim i
      let : Unique (∀ i, A i) := ⟨⟨a⟩,fun _ => funext (fun i => isEmptyElim i)⟩
      let : Unique (∀ i, B i) := ⟨⟨b⟩,fun _ => funext (fun i => isEmptyElim i)⟩
      intro _
      simp
    · have hp : 0<n := Nat.pos_of_ne_zero hn
      have : Nonempty N := Fintype.card_pos_iff.mp (hc ▸ hp)
      let i : N := Classical.choice this
      have hcard : Fintype.card {j : N // j ≠ i} = n-1 := by
        rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,hc]
      have hr := ih (n-1) (Nat.sub_lt hp (by norm_num)) {j : N // j ≠ i} hcard
        (fun j => A j) (fun j => B j) (fun j => M j) (fun j => C j)
        (fun j => hC j) (fun j => hM j)
      have hh := ((hM i).kronecker hr (hC i)).reindex
        (Equiv.piSplitAt i A) (Equiv.piSplitAt i B)
      rw [← prod_split] at hh
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      funext a b
      exact prod_split i (fun j => M j (a j) (b j))

lemma Bound.pi {N : Type u} [Fintype N] [DecidableEq N]
    {A : N → Type v} {B : N → Type w} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    {M : ∀ i, A i → B i → ℝ} {C : N → ℝ}
    (hC : ∀ i, 0 ≤ C i) (hM : ∀ i, Bound (M i) (C i)) :
    Bound (fun (a : ∀ i, A i) (b : ∀ i, B i) => ∏ i, M i (a i) (b i)) (∏ i, C i) :=
  bound_pi_aux _ N rfl A B M C hC hM

lemma Bound.fibers {N R S : Type*} [Fintype N] [DecidableEq N]
    [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (p : R → N) (q : S → N)
    {M : ∀ i, ({r : R // p r = i} → I) → ({s : S // q s = i} → J) → ℝ}
    {C : N → ℝ} (hC : ∀ i, 0 ≤ C i) (hM : ∀ i, Bound (M i) (C i)) :
    Bound (fun (a : R → I) (b : S → J) =>
      ∏ i, M i (fun r => a r) (fun s => b s)) (∏ i, C i) := by
  have hh := (Bound.pi hC hM).reindex
    (Equiv.piCongrFiberwise (γ₁ := fun _ => I) (f := p) (fun _ => Equiv.refl _))
    (Equiv.piCongrFiberwise (γ₁ := fun _ => J) (f := q) (fun _ => Equiv.refl _))
  exact hh

lemma Bound.mono {A : I → J → ℝ} {C D : ℝ} (h : Bound A C) (hCD : C ≤ D) :
    Bound A D := fun v => (h v).trans
      (mul_le_mul_of_nonneg_right hCD (energy_nonneg v))

lemma Bound.smul {A : I → J → ℝ} {C : ℝ} (h : Bound A C) (c : ℝ) :
    Bound (fun i j => c*A i j) (c^2*C) := by
  intro v
  simp only [mul_assoc,← Finset.mul_sum,mul_pow,← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (h v) (sq_nonneg c)).trans_eq (by ring)

lemma Bound.sum {N : Type*} [Fintype N] {M : N → I → J → ℝ} {C : N → ℝ}
    (hM : ∀ n, Bound (M n) (C n)) :
    Bound (fun i j => ∑ n, M n i j) ((Fintype.card N:ℝ)*∑ n, C n) := by
  intro v
  simp only [Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset J)) (t := (Finset.univ : Finset N))]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : N => (1:ℝ))
      (fun n => ∑ j, M n i j*v j))
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
  rw [← Finset.mul_sum] at hh
  conv at hh => rhs; arg 2; rw [Finset.sum_comm]
  have hh' := Finset.sum_le_sum (fun n (_ : n ∈ (Finset.univ : Finset N)) => hM n v)
  rw [← Finset.sum_mul] at hh'
  exact hh.trans ((mul_le_mul_of_nonneg_left hh' (Nat.cast_nonneg _)).trans_eq (by ring))

end TensorEnergy
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι ϑ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
  [Fintype κ] [DecidableEq κ]

def splitConstant (β : ℝ) (j k : ℕ) : ℝ :=
  β^(j+k)*((j.factorial:ℝ)*(k.factorial:ℝ))^2

omit [MeasurableSpace E] [BorelSpace E] in
lemma splitConstant_nonneg {β : ℝ} (hβ : 0 ≤ β) (j k : ℕ) :
    0 ≤ splitConstant β j k := by dsimp [splitConstant]; positivity

theorem crossMoment_energy (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E) :
    TensorEnergy.Bound (crossMoment μ b (ι := ι) (ϑ := ϑ))
      (splitConstant β (Fintype.card ι) (Fintype.card ϑ)) := by
  apply TensorEnergy.bound_of_bilinear (splitConstant_nonneg hβ _ _)
  intro T U
  convert crossMoment_sq_bound μ hμ hβ hP b T U using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [splitConstant]
  rw [pow_add]
  ring

def reducedCrossMoment (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) : ℝ :=
  if Fintype.card ι = 0 ∨ Fintype.card ϑ = 0 then 0 else crossMoment μ b a c

lemma reducedCrossMoment_energy (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E) :
    TensorEnergy.Bound (reducedCrossMoment μ b (ι := ι) (ϑ := ϑ))
      (splitConstant β (Fintype.card ι) (Fintype.card ϑ)) := by
  unfold reducedCrossMoment
  split_ifs
  · intro v
    simp only [zero_mul,Finset.sum_const_zero,zero_pow (by norm_num : 2≠0)]
    exact mul_nonneg (splitConstant_nonneg hβ _ _) (TensorEnergy.energy_nonneg v)
  · exact crossMoment_energy μ hμ hβ hP b

omit [MeasurableSpace E] [BorelSpace E] in
lemma card_fibers {N R : Type*} [Fintype N] [DecidableEq N] [Fintype R]
    (p : R → N) : (∑ i, Fintype.card {r : R // p r=i}) = Fintype.card R := by
  simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv p)

omit [MeasurableSpace E] [BorelSpace E] in
lemma prod_fiber_factorial_le {N R : Type*} [Fintype N] [DecidableEq N] [Fintype R]
    (p : R → N) :
    (∏ i, ((Fintype.card {r : R // p r=i}).factorial:ℝ)) ≤ ((Fintype.card R).factorial:ℝ) := by
  have hh := Nat.le_of_dvd (Nat.factorial_pos _)
    (Nat.prod_factorial_dvd_factorial_sum Finset.univ (fun i => Fintype.card {r : R // p r=i}))
  rw [card_fibers p] at hh
  exact_mod_cast hh

omit [MeasurableSpace E] [BorelSpace E] in
lemma prod_splitConstant_le {N R S : Type*} [Fintype N] [DecidableEq N]
    [Fintype R] [Fintype S] (p : R → N) (q : S → N) {β : ℝ} (hβ : 0 ≤ β) :
    (∏ i, splitConstant β (Fintype.card {r : R // p r=i})
      (Fintype.card {s : S // q s=i})) ≤ splitConstant β (Fintype.card R) (Fintype.card S) := by
  simp only [splitConstant,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
    Finset.prod_pow,Finset.sum_add_distrib,card_fibers]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hβ _)
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul (prod_fiber_factorial_le p) (prod_fiber_factorial_le q)
    (by positivity) (by positivity)

def crossBlockProduct {N : Type*} [Fintype N] [DecidableEq N]
    (μ : Measure E) (b : OrthonormalBasis κ ℝ E) (p : ι → N) (q : ϑ → N)
    (a : ι → κ) (c : ϑ → κ) : ℝ :=
  ∏ i, reducedCrossMoment μ b (fun j : {j : ι // p j=i} => a j)
    (fun j : {j : ϑ // q j=i} => c j)

lemma crossBlockProduct_energy {N : Type*} [Fintype N] [DecidableEq N]
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E)
    (p : ι → N) (q : ϑ → N) :
    TensorEnergy.Bound (crossBlockProduct μ b p q)
      (splitConstant β (Fintype.card ι) (Fintype.card ϑ)) := by
  exact (TensorEnergy.Bound.fibers p q
    (fun i => splitConstant_nonneg hβ _ _)
    (fun i => reducedCrossMoment_energy μ hμ hβ hP b)).mono (prod_splitConstant_le p q hβ)

abbrev LogTerms (ι ϑ : Type*) [Fintype ι] [Fintype ϑ] :=
  (m : Fin (Fintype.card ι+Fintype.card ϑ+1)) × (ι → Fin m.val) × (ϑ → Fin m.val)

def logCoefficient (m : ℕ) : ℝ := (-1)^(m+1)/(m:ℝ)

omit [MeasurableSpace E] [BorelSpace E] in
lemma logCoefficient_sq_le (m : ℕ) : (logCoefficient m)^2 ≤ 1 := by
  unfold logCoefficient
  by_cases hm : m=0
  · simp [hm]
  · have hpos : (1:ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    rw [div_pow,pow_right_comm,(by norm_num : (-1:ℝ)^2=1),one_pow]
    apply (div_le_one (by positivity : 0 < (m:ℝ)^2)).mpr
    nlinarith

def mixedCumulant (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) : ℝ :=
  ∑ t : LogTerms ι ϑ, logCoefficient t.1.val * crossBlockProduct μ b t.2.1 t.2.2 a c

omit [MeasurableSpace E] [BorelSpace E] in
lemma card_logTerms_le : Fintype.card (LogTerms ι ϑ) ≤
    (Fintype.card ι+Fintype.card ϑ+1)^(Fintype.card ι+Fintype.card ϑ+1) := by
  simp only [LogTerms,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    ← pow_add]
  have hh := Finset.sum_le_sum (fun m (_ : m ∈
      (Finset.univ : Finset (Fin (Fintype.card ι+Fintype.card ϑ+1)))) =>
    Nat.pow_le_pow_left (Nat.le_of_lt m.isLt) (Fintype.card ι+Fintype.card ϑ))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
  exact hh.trans_eq (by rw [pow_succ]; exact Nat.mul_comm _ _)

theorem mixedCumulant_energy (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E) :
    TensorEnergy.Bound (mixedCumulant μ b (ι := ι) (ϑ := ϑ))
      (((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(2*(Fintype.card ι+Fintype.card ϑ+1)) *
        splitConstant β (Fintype.card ι) (Fintype.card ϑ)) := by
  let C := splitConstant β (Fintype.card ι) (Fintype.card ϑ)
  have hC : 0 ≤ C := splitConstant_nonneg hβ _ _
  have hh (t : LogTerms ι ϑ) : TensorEnergy.Bound
      (fun a c => logCoefficient t.1.val * crossBlockProduct μ b t.2.1 t.2.2 a c) C :=
    ((crossBlockProduct_energy μ hμ hβ hP b t.2.1 t.2.2).smul _).mono
      ((mul_le_mul_of_nonneg_right (logCoefficient_sq_le _) hC).trans_eq (one_mul C))
  apply (TensorEnergy.Bound.sum hh).mono
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc : (Fintype.card (LogTerms ι ϑ):ℝ) ≤
      ((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(Fintype.card ι+Fintype.card ϑ+1) := by
    exact_mod_cast (card_logTerms_le (ι := ι) (ϑ := ϑ))
  have hc' := pow_le_pow_left₀ (Nat.cast_nonneg (Fintype.card (LogTerms ι ϑ))) hc 2
  have hh' := mul_le_mul_of_nonneg_right hc' hC
  rw [← pow_mul,Nat.mul_comm _ 2] at hh'
  simpa only [sq,mul_assoc] using hh'

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def HasExpMoments (μ : Measure E) : Prop := ∀ R : ℝ, Integrable (fun x : E => Real.exp (R*‖x‖)) μ

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def laplace (μ : Measure E) (h : E → F) (θ : E) : F :=
  ∫ x, Real.exp (inner ℝ θ x) • h x ∂μ

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
lemma growth_exp_bound {h : E → F} (hg : HasGrowth h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖h x‖ ≤ C*Real.exp ‖x‖ := by
  obtain ⟨C,hC,n,hn⟩ := hg
  refine ⟨C*(1+(n.factorial:ℝ)),by positivity,fun x => ?_⟩
  have hh := (div_le_iff₀ (by positivity : (0:ℝ)<n.factorial)).mp
    (Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) n)
  have he : 1 ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg x)
  have ht := mul_le_mul_of_nonneg_left (add_le_add he hh) hC
  exact (hn x).trans (ht.trans_eq (by ring))

omit [SecondCountableTopology E] in
lemma HasExpMoments.integrable_laplace {μ : Measure E} (hμ : HasExpMoments μ)
    {h : E → F} (hh : AEStronglyMeasurable h μ) (hg : HasGrowth h) (θ : E) :
    Integrable (fun x => Real.exp (inner ℝ θ x) • h x) μ := by
  obtain ⟨C,hC,hg⟩ := growth_exp_bound hg
  apply ((hμ (‖θ‖+1)).const_mul C).mono'
    (((continuous_const.inner continuous_id).rexp).aestronglyMeasurable.smul hh)
  filter_upwards [] with x
  change ‖Real.exp (inner ℝ θ x) • h x‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he := mul_le_mul (Real.exp_le_exp.mpr (real_inner_le_norm θ x))
    (hg x) (norm_nonneg _) (Real.exp_pos _).le
  exact he.trans_eq (by rw [show Real.exp (‖θ‖*‖x‖)*(C*Real.exp ‖x‖) =
    C*(Real.exp (‖θ‖*‖x‖)*Real.exp ‖x‖) by ring,← Real.exp_add]; congr 2; ring)

omit [SecondCountableTopology E] in
lemma HasExpMoments.hasMoments {μ : Measure E} (hμ : HasExpMoments μ) : HasMoments μ := by
  intro n
  have hg : HasGrowth (fun x : E => ‖x‖^n) :=
    (HasGrowth.lipschitz (LipschitzWith.id : LipschitzWith 1 (id : E → E))).norm.pow n
  simpa only [inner_zero_left,Real.exp_zero,one_smul,Pi.pow_apply] using
    hμ.integrable_laplace (continuous_norm.pow n).aestronglyMeasurable hg 0

def inserted (h : E → F) (x : E) : E →L[ℝ] F := (innerSL ℝ x).smulRight (h x)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma continuous_inserted {h : E → F} (hh : Continuous h) : Continuous (inserted h) :=
  isBoundedBilinearMap_smulRight.continuous.comp ((innerSL ℝ).continuous.prodMk hh)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma growth_inserted {h : E → F} (hg : HasGrowth h) : HasGrowth (inserted h) := by
  obtain ⟨C,hC,n,hn⟩ := hg
  refine ⟨2*C,by positivity,n+1,fun x => ?_⟩
  have hb : ‖inserted h x‖ ≤ ‖x‖*‖h x‖ := by
    simp [inserted,ContinuousLinearMap.norm_smulRight_apply]
  have hp := pow_le_one_add_pow_add (norm_nonneg x) 1 n
  rw [pow_one,Nat.add_comm 1 n] at hp
  have hh := mul_le_mul_of_nonneg_left (hn x) (norm_nonneg x)
  have hh' := hb.trans hh
  have hp' : ‖x‖*‖x‖^n=‖x‖^(n+1) := (pow_succ' _ _).symm
  nlinarith [mul_le_mul_of_nonneg_left hp hC,mul_nonneg hC (pow_nonneg (norm_nonneg x) (n+1)),congrArg (fun z : ℝ => C*z) hp']

lemma hasFDerivAt_laplace {μ : Measure E} (hμ : HasExpMoments μ)
    {h : E → F} (hh : Continuous h) (hg : HasGrowth h) (θ : E) :
    HasFDerivAt (laplace μ h) (laplace μ (inserted h) θ) θ := by
  obtain ⟨C,hC,hg'⟩ := growth_exp_bound (growth_inserted hg)
  let M := ‖θ‖+1
  let b : E → ℝ := fun x => C*Real.exp ((M+1)*‖x‖)
  have hd (x t : E) : HasFDerivAt (fun z : E => Real.exp (inner ℝ z x) • h x)
      (Real.exp (inner ℝ t x) • inserted h x) t := by
    have hh := ((innerSL ℝ x).hasFDerivAt (x := t)).exp.smul_const (h x)
    convert hh using 1
    · funext z; simp only [innerSL_apply_apply,real_inner_comm z x]
    · ext z; simp [inserted,real_inner_comm,smul_smul]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun t x => Real.exp (inner ℝ t x) • inserted h x)
    (bound := b) (Metric.ball_mem_nhds θ (show (0:ℝ)<1 by norm_num))
  · exact Eventually.of_forall fun t => (hμ.integrable_laplace hh.aestronglyMeasurable hg t).aestronglyMeasurable
  · exact hμ.integrable_laplace hh.aestronglyMeasurable hg θ
  · exact (hμ.integrable_laplace (continuous_inserted hh).aestronglyMeasurable (growth_inserted hg) θ).aestronglyMeasurable
  · filter_upwards [] with x t ht
    have htm : ‖t‖ ≤ M := by
      have hb : ‖t-θ‖<1 := by simpa [dist_eq_norm] using ht
      have hn := norm_add_le (t-θ) θ
      simp only [sub_add_cancel] at hn
      dsimp [M]; linarith
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have he := (real_inner_le_norm t x).trans (mul_le_mul_of_nonneg_right htm (norm_nonneg x))
    have h := mul_le_mul (Real.exp_le_exp.mpr he) (hg' x) (norm_nonneg _) (Real.exp_pos _).le
    exact h.trans_eq (by dsimp [b]; rw [show Real.exp (M*‖x‖)*(C*Real.exp ‖x‖) =
      C*(Real.exp (M*‖x‖)*Real.exp ‖x‖) by ring,← Real.exp_add]; congr 2; ring)
  · exact (hμ (M+1)).const_mul C
  · exact Eventually.of_forall fun x t _ => hd x t

lemma contDiff_laplace {μ : Measure E} (hμ : HasExpMoments μ)
    {h : E → F} (hh : Continuous h) (hg : HasGrowth h) :
    ContDiff ℝ (⊤ : ℕ∞) (laplace μ h) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr (show Differentiable ℝ (laplace μ h) from
      fun θ => (hasFDerivAt_laplace hμ hh hg θ).differentiableAt).continuous
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv]
    refine ⟨fun θ => (hasFDerivAt_laplace hμ hh hg θ).differentiableAt,by simp,?_⟩
    have he : fderiv ℝ (laplace μ h) = laplace μ (inserted h) := by
      funext θ; exact (hasFDerivAt_laplace hμ hh hg θ).fderiv
    rw [he]
    exact ih (continuous_inserted hh) (growth_inserted hg)

omit [SecondCountableTopology E] in
lemma laplace_one_pos {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) (θ : E) : 0 < laplace μ (fun _ => (1:ℝ)) θ := by
  exact (integral_pos_iff_support_of_nonneg (fun x => by
    simp only [smul_eq_mul,mul_one]; exact (Real.exp_pos _).le)
    (hμ.integrable_laplace aestronglyMeasurable_const (HasGrowth.const (1:ℝ)) θ)).2
    (by simp [Function.support,Real.exp_ne_zero])

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

def dir (v : E) (f : E → ℝ) : E → ℝ := fun x => fderiv ℝ f x v

def jet (v : ι → E) : List ι → (E → ℝ) → (E → ℝ)
  | [], f => f
  | i::l, f => dir (v i) (jet v l f)

lemma smooth_dir {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (dir v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma smooth_jet {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ι → E) (l : List ι) :
    ContDiff ℝ (⊤ : ℕ∞) (jet v l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact smooth_dir ih _

lemma dir_add {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (v : E) :
    dir v (fun x => f x+g x) = fun x => dir v f x+dir v g x := by
  funext x
  change (fderiv ℝ (f+g) x) v = _
  rw [fderiv_add (hf x) (hg x)]
  rfl

lemma dir_mul {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (v : E) :
    dir v (fun x => f x*g x) = fun x => dir v f x*g x+f x*dir v g x := by
  funext x
  change (fderiv ℝ (f*g) x) v = _
  rw [((hf x).hasFDerivAt.mul (hg x).hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,dir]
  ring

lemma dir_sum {κ : Type*} (s : Finset κ) {f : κ → E → ℝ}
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (v : E) :
    dir v (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, dir v (f i) x := by
  funext x
  simp only [dir,(HasFDerivAt.fun_sum (fun i hi => (hf i hi x).hasFDerivAt)).fderiv,
    sum_apply]

lemma jet_add {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : ι → E) (l : List ι) :
    jet v l (fun x => f x+g x) = fun x => jet v l f x+jet v l g x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [jet,ih]
    exact dir_add ((smooth_jet hf v l).differentiable (by simp))
      ((smooth_jet hg v l).differentiable (by simp)) _

lemma jet_sum {κ : Type*} (s : Finset κ) {f : κ → E → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f i)) (v : ι → E) (l : List ι) :
    jet v l (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, jet v l (f i) x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [jet,ih]
    exact dir_sum s (fun j hj => (smooth_jet (hf j hj) v l).differentiable (by simp)) _

lemma jet_const (v : ι → E) (l : List ι) (c : ℝ) :
    jet v l (fun _ => c) = if l=[] then (fun _ => c) else (fun _ => 0) := by
  induction l with
  | nil => simp [jet]
  | cons i l ih =>
    simp only [jet,ih,List.cons_ne_nil,↓reduceIte]
    split_ifs <;> funext x <;> simp [dir]

section
variable [DecidableEq ι]
lemma filter_insert_of_not_mem (l : List ι) (i : ι) (s : Finset ι) (hi : i ∉ l) :
    l.filter (fun j => j ∈ insert i s) = l.filter (fun j => j ∈ s) := by
  apply List.filter_congr
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact hi hj
  simp [hji]

lemma filter_not_insert_of_not_mem (l : List ι) (i : ι) (s : Finset ι) (hi : i ∉ l) :
    l.filter (fun j => j ∉ insert i s) = l.filter (fun j => j ∉ s) := by
  apply List.filter_congr
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact hi hj
  simp [hji]

theorem jet_mul {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : ι → E) (l : List ι) (hl : l.Nodup) :
    jet v l (fun x => f x*g x) = fun x =>
      ∑ s ∈ l.toFinset.powerset,
        jet v (l.filter (fun i => i ∈ s)) f x *
          jet v (l.filter (fun i => i ∉ s)) g x := by
  induction l with
  | nil => simp [jet]
  | cons i l ih =>
    have hi := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    rw [jet,ih hl',dir_sum _ (fun s hs =>
      ((smooth_jet hf v _).mul (smooth_jet hg v _)).differentiable (by simp))]
    funext x
    simp only [List.toFinset_cons,Finset.sum_powerset_insert (by simpa using hi : i ∉ l.toFinset)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have his : i ∉ s := fun h => hi (List.mem_toFinset.mp ((Finset.mem_powerset.mp hs) h))
    rw [dir_mul ((smooth_jet hf v _).differentiable (by simp))
      ((smooth_jet hg v _).differentiable (by simp))]
    simp only [List.filter_cons,Finset.mem_insert_self,decide_true,↓reduceIte,
      his,decide_false,Bool.false_eq_true,not_false_eq_true,Finset.mem_insert_self,
      not_true_eq_false,filter_insert_of_not_mem l i s hi,filter_not_insert_of_not_mem l i s hi,jet]
    ring
end
end JetCalculus
end LogConcaveSampling
namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

lemma jet_append (v : ι → E) (l k : List ι) (f : E → ℝ) :
    jet v (l++k) f = jet v l (jet v k f) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append,jet,ih]

lemma dir_const_mul {f : E → ℝ} (hf : Differentiable ℝ f) (v : E) (c : ℝ) :
    dir v (fun x => c*f x) = fun x => c*dir v f x := by
  funext x
  change (fderiv ℝ (fun x => c*f x) x) v = _
  rw [((hf x).hasFDerivAt.const_mul c).fderiv]
  simp [dir]

lemma jet_const_mul {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (l : List ι) (c : ℝ) :
    jet v l (fun x => c*f x) = fun x => c*jet v l f x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [jet,ih]
    exact dir_const_mul ((smooth_jet hf v l).differentiable (by simp)) _ _

lemma jet_sub {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : ι → E) (l : List ι) :
    jet v l (fun x => f x-g x) = fun x => jet v l f x-jet v l g x := by
  rw [show (fun x => f x-g x) = (fun x => f x+(-1)*g x) by funext x; ring,
    jet_add hf (contDiff_const.mul hg),jet_const_mul hg]
  funext x; ring

lemma filter_length_add (l : List ι) (p : ι → Bool) :
    (l.filter p).length+(l.filter (fun i => !(p i))).length=l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
    cases hp : p i <;> simp only [List.filter_cons, hp, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

section
variable [DecidableEq ι]

lemma jet_pow_zero {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (m : ℕ) (l : List ι) (hl : l.Nodup) {x : E}
    (hx : f x=0) (hm : l.length < m) : jet v l (fun x => (f x)^m) x=0 := by
  induction m generalizing l with
  | zero => omega
  | succ m ih =>
    rw [show (fun x => (f x)^(m+1)) = (fun x => f x*(f x)^m) by funext y; rw [pow_succ'],
      jet_mul hf (hf.pow m) v l hl]
    apply Finset.sum_eq_zero
    intro s hs
    by_cases hs0 : s=∅
    · subst s; simp [jet,hx]
    · have hlpos : 0 < (l.filter (fun j => j ∈ s)).length := by
        obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr hs0
        have hjl : j ∈ l := List.mem_toFinset.mp ((Finset.mem_powerset.mp hs) hj)
        exact List.length_pos_iff.mpr (fun hz => by
          have hmem : j ∈ l.filter (fun j => j ∈ s) := by simp [hjl,hj]
          rw [hz] at hmem; simp at hmem)
      have hlen := filter_length_add l (fun j => decide (j ∈ s))
      have hlen' : (l.filter (fun j => j ∉ s)).length < m := by
        simpa only [← decide_not] using (show (l.filter (fun j => !(decide (j ∈ s)))).length < m by omega)
      rw [ih _ (hl.filter _) hlen',mul_zero]

lemma jet_pow_mul_zero {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : ι → E) (m : ℕ) (l : List ι)
    (hl : l.Nodup) {x : E} (hx : f x=0) (hm : l.length < m) :
    jet v l (fun x => (f x)^m*g x) x=0 := by
  rw [jet_mul (hf.pow m) hg v l hl]
  apply Finset.sum_eq_zero
  intro s hs
  rw [jet_pow_zero hf v m _ (hl.filter _) hx
    ((List.length_filter_le _ _).trans_lt hm),zero_mul]
end
end JetCalculus
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_NormalizedLaplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace Appell
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι : Type*} [DecidableEq ι]

lemma dir_laplace {μ : Measure E} (hμ : HasExpMoments μ)
    {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h) (v : E) :
    JetCalculus.dir v (laplace μ h) = laplace μ (fun x => inner ℝ v x*h x) := by
  funext θ
  rw [JetCalculus.dir,(hasFDerivAt_laplace hμ hh hg θ).fderiv]
  rw [laplace,ContinuousLinearMap.integral_apply
    (hμ.integrable_laplace (continuous_inserted hh).aestronglyMeasurable (growth_inserted hg) θ)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [inserted,real_inner_comm]

lemma jet_laplace {μ : Measure E} (hμ : HasExpMoments μ)
    {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h)
    (v : ι → E) (l : List ι) (hl : l.Nodup) :
    JetCalculus.jet v l (laplace μ h) =
      laplace μ (fun x => (∏ i ∈ l.toFinset, inner ℝ (v i) x)*h x) := by
  induction l with
  | nil => simp [JetCalculus.jet]
  | cons i l ih =>
    have hi : i ∉ l.toFinset := by simpa using (List.nodup_cons.mp hl).1
    simp only [JetCalculus.jet,ih (List.nodup_cons.mp hl).2]
    have hc : Continuous (fun x => (∏ i ∈ l.toFinset,inner ℝ (v i) x)*h x) :=
      (continuous_finsetProd _ (fun _ _ => continuous_const.inner continuous_id)).mul hh
    have hg' : HasGrowth (fun x => (∏ i ∈ l.toFinset,inner ℝ (v i) x)*h x) :=
      (HasGrowth.prod _ (fun j _ => HasGrowth.linear (innerSL ℝ (v j)))).mul hg
    rw [dir_laplace hμ hc hg']
    congr 1
    funext x
    rw [List.toFinset_cons,Finset.prod_insert hi]
    ring

omit [BorelSpace E] [SecondCountableTopology E] in
lemma laplace_zero {μ : Measure E} (h : E → ℝ) : laplace μ h 0=∫ x,h x ∂μ := by
  simp [laplace]

lemma jet_laplace_zero {μ : Measure E} (hμ : HasExpMoments μ)
    (v : ι → E) (l : List ι) (hl : l.Nodup) :
    JetCalculus.jet v l (laplace μ (fun _ => (1:ℝ))) 0 =
      moments μ (fun i x => inner ℝ (v i) x) l.toFinset := by
  rw [jet_laplace hμ continuous_const (HasGrowth.const _) v l hl,laplace_zero]
  simp [moments]

lemma filter_toFinset_of_subset (l : List ι) (s : Finset ι) (hs : s ⊆ l.toFinset) :
    (l.filter (fun i => i ∈ s)).toFinset=s := by
  ext i
  simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
  exact ⟨fun h => h.2,fun h => ⟨List.mem_toFinset.mp (hs h),h⟩⟩

lemma filter_not_toFinset (l : List ι) (s : Finset ι) :
    (l.filter (fun i => i ∉ s)).toFinset=l.toFinset\s := by
  ext i
  simp

lemma jet_inverse_laplace_zero {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (v : ι → E) (l : List ι) (hl : l.Nodup) :
    JetCalculus.jet v l (fun θ => (laplace μ (fun _ => (1:ℝ)) θ)⁻¹) 0 =
      inverseMoment (moments μ (fun i x => inner ℝ (v i) x)) l.toFinset := by
  let M := laplace μ (fun _ => (1:ℝ))
  have hMs : ContDiff ℝ (⊤ : ℕ∞) M := contDiff_laplace hμ continuous_const (HasGrowth.const _)
  have hMi : ContDiff ℝ (⊤ : ℕ∞) (fun θ => (M θ)⁻¹) :=
    hMs.inv (fun θ => (laplace_one_pos hμ θ).ne')
  have hM0 : M 0=1 := by simp [M,laplace]
  have hne : ∀ θ, M θ≠0 := fun θ => (laplace_one_pos hμ θ).ne'
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases hl0 : l=[]
    · subst l
      simp [JetCalculus.jet,show laplace μ (fun _ => (1:ℝ)) 0=1 from hM0]
    have hs0 : l.toFinset ≠ ∅ := by simpa using hl0
    have hprod : (fun θ => (M θ)⁻¹*M θ)=(fun _ => (1:ℝ)) := by
      funext θ; exact inv_mul_cancel₀ (hne θ)
    have hj := congrFun (JetCalculus.jet_mul hMi hMs v l hl) 0
    rw [hprod,JetCalculus.jet_const,ite_eq_right hl0] at hj
    have hp := Finset.mem_powerset.mpr (Finset.Subset.refl l.toFinset)
    rw [← Finset.sum_erase_add _ _ hp] at hj
    have hfull : l.filter (fun i => i ∈ l.toFinset)=l := by
      apply List.filter_eq_self.mpr
      intro i hi; simpa using hi
    have hempty : l.filter (fun i => i ∉ l.toFinset)=[] := by simp
    simp only [hfull,hempty,JetCalculus.jet,hM0,mul_one] at hj
    rw [inverseMoment_nonempty _ hs0]
    have he : (∑ s ∈ l.toFinset.powerset.erase l.toFinset,
        JetCalculus.jet v (l.filter (fun i => i ∈ s)) (fun θ => (M θ)⁻¹) 0 *
        JetCalculus.jet v (l.filter (fun i => i ∉ s)) M 0) =
      ∑ s ∈ l.toFinset.powerset.erase l.toFinset,
        moments μ (fun i x => inner ℝ (v i) x) (l.toFinset\s) *
          inverseMoment (moments μ (fun i x => inner ℝ (v i) x)) s := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp hs).2
      have hlen : (l.filter (fun i => i ∈ s)).length < n := by
        have hh := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨hsub,(Finset.mem_erase.mp hs).1⟩)
        rw [← filter_toFinset_of_subset l s hsub,
          List.toFinset_card_of_nodup (hl.filter _),List.toFinset_card_of_nodup hl,hn] at hh
        exact hh
      rw [ih _ hlen _ (hl.filter _) rfl,filter_toFinset_of_subset l s hsub,
        jet_laplace_zero hμ v _ (hl.filter _),filter_not_toFinset,mul_comm]
    change JetCalculus.jet v l (fun θ => (M θ)⁻¹) 0 = _
    rw [he] at hj
    linarith

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι κ : Type*}

lemma dir_comp_affine {f : F → ℝ} (hf : Differentiable ℝ f)
    (L : E →L[ℝ] F) (b : F) (v : E) :
    dir v (fun x => f (L x+b)) = fun x => dir (L v) f (L x+b) := by
  funext x
  have hd := (hf (L x+b)).hasFDerivAt.comp x (L.hasFDerivAt.add_const b)
  change (fderiv ℝ (f ∘ fun x => L x+b) x) v = _
  rw [hd.fderiv]
  rfl

lemma jet_comp_affine {f : F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (L : E →L[ℝ] F) (b : F) (v : ι → E) (l : List ι) :
    jet v l (fun x => f (L x+b)) = fun x => jet (fun i => L (v i)) l f (L x+b) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [jet,ih,dir_comp_affine ((smooth_jet hf _ l).differentiable (by simp))]
    rfl

lemma jet_map (v : κ → E) (e : ι → κ) (l : List ι) (f : E → ℝ) :
    jet v (l.map e) f = jet (v ∘ e) l f := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons,jet,ih,Function.comp_apply]

end JetCalculus
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι : Type*} [DecidableEq ι]

def normalizedLaplace (μ : Measure E) (h : E → ℝ) (θ : E) : ℝ :=
  (laplace μ (fun _ => (1:ℝ)) θ)⁻¹*laplace μ h θ

lemma smooth_normalizedLaplace {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedLaplace μ h) :=
  ((contDiff_laplace hμ continuous_const (HasGrowth.const _)).inv
    (fun θ => (laplace_one_pos hμ θ).ne')).mul (contDiff_laplace hμ hh hg)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma growth_polynomial_inner (m : Finset ι → ℝ) (s : Finset ι) (v : ι → E) :
    HasGrowth (fun x => polynomial m s (fun i => inner ℝ (v i) x)) := by
  unfold polynomial
  apply HasGrowth.sum
  intro t ht
  exact (HasGrowth.const _).mul
    (HasGrowth.prod _ (fun i _ => HasGrowth.linear (innerSL ℝ (v i))))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma continuous_polynomial_inner (m : Finset ι → ℝ) (s : Finset ι) (v : ι → E) :
    Continuous (fun x => polynomial m s (fun i => inner ℝ (v i) x)) :=
  (polynomial_contDiff m s (fun i => innerSL ℝ (v i))).continuous

lemma jet_shift_laplace {μ : Measure E} (hμ : HasExpMoments μ)
    {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h)
    (v : ι → E) (l : List ι) (hl : l.Nodup) (θ : E) :
    JetCalculus.jet v l (fun ω => laplace μ h (θ+ω)) 0 =
      laplace μ (fun x => (∏ i ∈ l.toFinset,inner ℝ (v i) x)*h x) θ := by
  rw [show (fun ω => laplace μ h (θ+ω))=
    (fun ω => laplace μ h ((ContinuousLinearMap.id ℝ E) ω+θ)) by funext ω; simp [add_comm],
    JetCalculus.jet_comp_affine (contDiff_laplace hμ hh hg)]
  simp only [ContinuousLinearMap.id_apply,zero_add]
  rw [jet_laplace hμ hh hg v l hl]

lemma jet_normalized_at_zero {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h)
    (v : ι → E) (l : List ι) (hl : l.Nodup) (θ : E) :
    JetCalculus.jet v l (fun ω => (laplace μ (fun _ => (1:ℝ)) ω)⁻¹ *
      laplace μ h (θ+ω)) 0 =
    laplace μ (fun x => polynomial (moments μ (fun i x => inner ℝ (v i) x))
      l.toFinset (fun i => inner ℝ (v i) x)*h x) θ := by
  have hM := contDiff_laplace hμ continuous_const (HasGrowth.const (1:ℝ))
  have hMi : ContDiff ℝ (⊤ : ℕ∞) (fun θ => (laplace μ (fun _ => (1:ℝ)) θ)⁻¹) :=
    hM.inv (fun θ => (laplace_one_pos hμ θ).ne')
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun ω => laplace μ h (θ+ω)) :=
    (contDiff_laplace hμ hh hg).comp (contDiff_const.add contDiff_id)
  rw [JetCalculus.jet_mul hMi hc v l hl]
  conv_rhs => simp only [laplace,polynomial,Finset.sum_mul,Finset.mul_sum,smul_eq_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s hs
    rw [jet_inverse_laplace_zero hμ v _ (hl.filter _),
      filter_toFinset_of_subset l s (Finset.mem_powerset.mp hs),
      jet_shift_laplace hμ hh hg v _ (hl.filter _),filter_not_toFinset]
    rw [laplace,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [smul_eq_mul]
    ring
  · intro s hs
    have hpoly := (HasGrowth.const (inverseMoment (moments μ
      (fun i x => inner ℝ (v i) x)) s)).mul
      ((HasGrowth.prod (l.toFinset\s) (fun i _ => HasGrowth.linear (innerSL ℝ (v i)))).mul hg)
    have hct : Continuous (fun x => inverseMoment (moments μ
        (fun i x => inner ℝ (v i) x)) s * ((∏ i ∈ l.toFinset\s,inner ℝ (v i) x)*h x)) :=
      continuous_const.mul ((continuous_finsetProd _
        (fun _ _ => continuous_const.inner continuous_id)).mul hh)
    convert hμ.integrable_laplace hct.aestronglyMeasurable hpoly θ using 1
    all_goals try with_reducible_and_instances rfl
    funext x; simp only [smul_eq_mul]; ring

lemma jet_normalizedLaplace_zero {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h)
    (v : ι → E) (l : List ι) (hl : l.Nodup) :
    JetCalculus.jet v l (normalizedLaplace μ h) 0 =
      ∫ x, polynomial (moments μ (fun i x => inner ℝ (v i) x))
        l.toFinset (fun i => inner ℝ (v i) x)*h x ∂μ := by
  change JetCalculus.jet v l (fun θ => (laplace μ (fun _ => (1:ℝ)) θ)⁻¹*laplace μ h θ) 0 = _
  simpa only [zero_add,laplace_zero] using
    jet_normalized_at_zero hμ hh hg v l hl 0

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology BigOperators

def logTrunc (n : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, ((-1:ℝ)^m/(m+1))*(t-1)^(m+1)

lemma smooth_logTrunc (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (logTrunc n) := by
  apply ContDiff.sum
  intro m hm
  exact contDiff_const.mul ((contDiff_id.sub contDiff_const).pow _)

lemma hasDerivAt_logTrunc (n : ℕ) (t : ℝ) :
    HasDerivAt (logTrunc n) (∑ m ∈ Finset.range n, (1-t)^m) t := by
  have hd := HasDerivAt.sum (u := Finset.range n) (fun m _ =>
    ((((hasDerivAt_id t).sub_const 1).pow (m+1)).const_mul ((-1:ℝ)^m/(m+1))))
  convert! hd using 1
  · funext y; simp [logTrunc]
  · apply Finset.sum_congr rfl
    intro m hm
    have hm' : (m:ℝ)+1 ≠ 0 := by positivity
    simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,mul_one,id_eq]
    rw [show 1-t= -(t-1) by ring,neg_pow]
    field_simp

@[simp] lemma logTrunc_one (n : ℕ) : logTrunc n 1 = 0 := by simp [logTrunc]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [DecidableEq ι]

lemma dir_log_remainder {G : E → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hpos : ∀ x, 0 < G x) (n : ℕ) (v : E) :
    dir v (fun x => Real.log (G x)-logTrunc n (G x)) =
      fun x => (G x-1)^n*((-1:ℝ)^n*(G x)⁻¹*dir v G x) := by
  funext x
  have hd := ((hG.differentiable (by simp) x).hasFDerivAt.log (hpos x).ne').sub
    ((hasDerivAt_logTrunc n (G x)).comp_hasFDerivAt x
      (hG.differentiable (by simp) x).hasFDerivAt)
  change (fderiv ℝ ((fun x => Real.log (G x)) - logTrunc n ∘ G) x) v = _
  rw [hd.fderiv]
  simp only [sub_apply,smul_apply,smul_eq_mul]
  have hgeom := geom_sum_mul (1-G x) n
  have hpow : (1-G x)^n=(-1:ℝ)^n*(G x-1)^n := by
    rw [show 1-G x= -(G x-1) by ring,neg_pow]
  rw [hpow] at hgeom
  change (G x)⁻¹*dir v G x-(∑ m ∈ Finset.range n,(1-G x)^m)*dir v G x = _
  have hh : (G x)⁻¹-(∑ m ∈ Finset.range n,(1-G x)^m) =
      (G x-1)^n*((-1:ℝ)^n*(G x)⁻¹) := by
    apply (mul_left_cancel₀ (hpos x).ne')
    have hinv := mul_inv_cancel₀ (hpos x).ne'
    calc
      G x*((G x)⁻¹-∑ m ∈ Finset.range n,(1-G x)^m) =
          1-G x*(∑ m ∈ Finset.range n,(1-G x)^m) := by rw [mul_sub,hinv]
      _ = (-1:ℝ)^n*(G x-1)^n := by nlinarith only [hgeom]
      _ = (G x*(G x)⁻¹)*((-1:ℝ)^n*(G x-1)^n) := by rw [hinv,one_mul]
      _ = _ := by ring
  rw [show (G x)⁻¹*dir v G x-(∑ m ∈ Finset.range n,(1-G x)^m)*dir v G x =
    ((G x)⁻¹-(∑ m ∈ Finset.range n,(1-G x)^m))*dir v G x by ring,hh]
  ring

lemma jet_logTrunc {G : E → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hpos : ∀ x, 0 < G x) (n : ℕ) (v : ι → E) (l : List ι)
    (hl : l.Nodup) {x : E} (hx : G x=1) (hlen : l.length ≤ n) :
    jet v l (fun x => Real.log (G x)) x = jet v l (fun x => logTrunc n (G x)) x := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => Real.log (G x)) := hG.log (fun x => (hpos x).ne')
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun x => logTrunc n (G x)) := (smooth_logTrunc n).comp hG
  suffices h : jet v l (fun x => Real.log (G x)-logTrunc n (G x)) x=0 by
    rw [jet_sub hs ht] at h
    exact sub_eq_zero.mp h
  induction l using List.reverseRecOn with
  | nil => simp [jet,hx]
  | append_singleton l i ih =>
    rw [jet_append]
    change jet v l (dir (v i) (fun x => Real.log (G x)-logTrunc n (G x))) x=0
    rw [dir_log_remainder hG hpos]
    apply jet_pow_mul_zero (hG.sub contDiff_const)
      ((contDiff_const.mul (hG.inv (fun x => (hpos x).ne'))).mul (smooth_dir hG _)) v n l
    · exact (List.nodup_append.mp hl).1
    · exact sub_eq_zero.mpr hx
    · simp only [List.length_append,List.length_singleton] at hlen
      omega

end JetCalculus
end LogConcaveSampling

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι κ : Type*}

def mixedJet (v : ι → E) (w : κ → F) (l : List ι) (k : List κ)
    (f : E × F → ℝ) : ℝ := jet v l (fun θ => jet w k (fun ω => f (θ,ω)) 0) 0

lemma jet_right_slice {f : E × F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (w : κ → F) (k : List κ) (θ : E) (ω : F) :
    jet w k (fun ω => f (θ,ω)) ω=jet (fun i => ((0:E),w i)) k f (θ,ω) := by
  have hh := congrFun (jet_comp_affine hf
    ((0 : F →L[ℝ] E).prod (ContinuousLinearMap.id ℝ F)) (θ,0) w k) ω
  simpa using hh

lemma jet_left_slice {f : E × F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (l : List ι) (θ : E) (ω : F) :
    jet v l (fun θ => f (θ,ω)) θ=jet (fun i => (v i,(0:F))) l f (θ,ω) := by
  have hh := congrFun (jet_comp_affine hf
    ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] F)) (0,ω) v l) θ
  simpa using hh

lemma mixedJet_eq_joint {f : E × F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (w : κ → F) (l : List ι) (k : List κ) :
    mixedJet v w l k f=jet (Sum.elim (fun i => (v i,(0:F))) (fun j => ((0:E),w j)))
      (l.map Sum.inl++k.map Sum.inr) f 0 := by
  rw [jet_append,jet_map,jet_map]
  change mixedJet v w l k f=jet (fun i => (v i,(0:F))) l
    (jet (fun j => ((0:E),w j)) k f) (0,0)
  unfold mixedJet
  simp_rw [jet_right_slice hf]
  exact jet_left_slice (smooth_jet hf _ k) v l 0 0

lemma mixedJet_sub {f g : E × F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : ι → E) (w : κ → F) (l : List ι) (k : List κ) :
    mixedJet v w l k (fun x => f x-g x)=mixedJet v w l k f-mixedJet v w l k g := by
  rw [mixedJet_eq_joint (hf.sub hg),jet_sub hf hg,
    mixedJet_eq_joint hf,mixedJet_eq_joint hg]

lemma mixedJet_sum {N : Type*} (s : Finset N) {f : N → E × F → ℝ}
    (hf : ∀ n ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (v : ι → E) (w : κ → F) (l : List ι) (k : List κ) :
    mixedJet v w l k (fun x => ∑ n ∈ s,f n x)=∑ n ∈ s,mixedJet v w l k (f n) := by
  rw [mixedJet_eq_joint (ContDiff.sum hf),jet_sum s hf]
  apply Finset.sum_congr rfl
  intro n hn
  exact (mixedJet_eq_joint (hf n hn) v w l k).symm

lemma mixedJet_const_mul {f : E × F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (w : κ → F) (l : List ι) (k : List κ) (c : ℝ) :
    mixedJet v w l k (fun x => c*f x)=c*mixedJet v w l k f := by
  rw [mixedJet_eq_joint (contDiff_const.mul hf),jet_const_mul hf,mixedJet_eq_joint hf]

lemma mixedJet_const (v : ι → E) (w : κ → F) (l : List ι) (k : List κ) (c : ℝ) :
    mixedJet v w l k (fun _ => c)=if l=[] ∧ k=[] then c else 0 := by
  rw [mixedJet_eq_joint contDiff_const,jet_const]
  simp only [List.append_eq_nil_iff,List.map_eq_nil_iff]
  split_ifs <;> rfl

lemma nodup_sum_append {l : List ι} {k : List κ} (hl : l.Nodup) (hk : k.Nodup) :
    (l.map Sum.inl++k.map Sum.inr).Nodup := by
  rw [List.nodup_append]
  refine ⟨hl.map Sum.inl_injective,hk.map Sum.inr_injective,?_⟩
  intro x hx y hy hxy
  subst y
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  obtain ⟨j,hj,hji⟩ := List.mem_map.mp hy
  cases hji

lemma mixedJet_logTrunc [DecidableEq ι] [DecidableEq κ]
    {G : E × F → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hpos : ∀ x,0 < G x)
    (hG0 : G 0=1) (v : ι → E) (w : κ → F) (l : List ι) (k : List κ)
    (hl : l.Nodup) (hk : k.Nodup) :
    mixedJet v w l k (fun x => Real.log (G x)) =
      mixedJet v w l k (fun x => logTrunc (l.length+k.length) (G x)) := by
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun x => logTrunc (l.length+k.length) (G x)) :=
    (smooth_logTrunc _).comp hG
  rw [mixedJet_eq_joint (hG.log (fun x => (hpos x).ne')),mixedJet_eq_joint ht]
  apply jet_logTrunc hG hpos _ _ _ (nodup_sum_append hl hk) hG0
  simp

end JetCalculus
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

def crossMGF (μ : Measure E) (t : E × E) : ℝ :=
  (laplace μ (fun _ => (1:ℝ)) t.1)⁻¹ *
    ((laplace μ (fun _ => (1:ℝ)) t.2)⁻¹*laplace μ (fun _ => (1:ℝ)) (t.1+t.2))

lemma smooth_crossMGF {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ) :
    ContDiff ℝ (⊤ : ℕ∞) (crossMGF μ) := by
  have hM := contDiff_laplace hμ continuous_const (HasGrowth.const (1:ℝ))
  have hi := hM.inv (fun θ => (laplace_one_pos hμ θ).ne')
  exact (hi.comp contDiff_fst).mul
    ((hi.comp contDiff_snd).mul (hM.comp (contDiff_fst.add contDiff_snd)))

omit [SecondCountableTopology E] in
lemma crossMGF_pos {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (t : E × E) : 0 < crossMGF μ t := by
  exact mul_pos (inv_pos.mpr (laplace_one_pos hμ _))
    (mul_pos (inv_pos.mpr (laplace_one_pos hμ _)) (laplace_one_pos hμ _))

omit [BorelSpace E] [SecondCountableTopology E] in
@[simp] lemma crossMGF_zero {μ : Measure E} [IsProbabilityMeasure μ] : crossMGF μ 0=1 := by
  simp [crossMGF,laplace]

omit [SecondCountableTopology E] in
lemma crossMGF_left_zero {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (t : E) : crossMGF μ (0,t)=1 := by
  have hM0 : laplace μ (fun _ => (1:ℝ)) 0=1 := by simp [laplace]
  simp only [crossMGF,hM0,inv_one,one_mul,zero_add]
  exact inv_mul_cancel₀ (laplace_one_pos hμ t).ne'

omit [SecondCountableTopology E] in
lemma crossMGF_right_zero {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (t : E) : crossMGF μ (t,0)=1 := by
  have hM0 : laplace μ (fun _ => (1:ℝ)) 0=1 := by simp [laplace]
  simp only [crossMGF,hM0,inv_one,one_mul,add_zero]
  exact inv_mul_cancel₀ (laplace_one_pos hμ t).ne'

lemma mixedJet_crossMGF {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (v : ι → E) (w : κ → E) (l : List ι) (k : List κ) (hl : l.Nodup) (hk : k.Nodup) :
    JetCalculus.mixedJet v w l k (crossMGF μ) =
      ∫ x, polynomial (moments μ (fun i x => inner ℝ (v i) x)) l.toFinset
        (fun i => inner ℝ (v i) x)*
        polynomial (moments μ (fun i x => inner ℝ (w i) x)) k.toFinset
          (fun i => inner ℝ (w i) x) ∂μ := by
  have hc (θ : E) : ContDiff ℝ (⊤ : ℕ∞) (fun ω =>
      (laplace μ (fun _ => (1:ℝ)) ω)⁻¹*laplace μ (fun _ => (1:ℝ)) (θ+ω)) :=
    ((contDiff_laplace hμ continuous_const (HasGrowth.const _)).inv
      (fun θ => (laplace_one_pos hμ θ).ne')).mul
      ((contDiff_laplace hμ continuous_const (HasGrowth.const _)).comp
        (contDiff_const.add contDiff_id))
  unfold JetCalculus.mixedJet crossMGF
  simp_rw [JetCalculus.jet_const_mul (hc _),
    jet_normalized_at_zero hμ continuous_const (HasGrowth.const (1:ℝ)) w k hk]
  simp only [mul_one]
  exact jet_normalizedLaplace_zero hμ (continuous_polynomial_inner _ _ w) (growth_polynomial_inner _ _ w) v l hl

omit [DecidableEq ι] [DecidableEq κ] in
omit [SecondCountableTopology E] in
lemma mixedJet_reduced_unmixed {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (v : ι → E) (w : κ → E) (l : List ι) (k : List κ) (hempty : l=[] ∨ k=[]) :
    JetCalculus.mixedJet v w l k (fun x => crossMGF μ x-1)=0 := by
  rcases hempty with rfl | rfl
  · simp only [JetCalculus.mixedJet,JetCalculus.jet]
    simp_rw [crossMGF_left_zero hμ,sub_self]
    simp [JetCalculus.jet_const]
  · simp only [JetCalculus.mixedJet,JetCalculus.jet]
    simp_rw [crossMGF_right_zero hμ,sub_self]
    simp [JetCalculus.jet_const]

lemma mixedJet_reduced {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (v : ι → E) (w : κ → E) (l : List ι) (k : List κ) (hl : l.Nodup) (hk : k.Nodup)
    (hn : ¬(l=[] ∧ k=[])) :
    JetCalculus.mixedJet v w l k (fun x => crossMGF μ x-1) =
      ∫ x, polynomial (moments μ (fun i x => inner ℝ (v i) x)) l.toFinset
        (fun i => inner ℝ (v i) x)*
        polynomial (moments μ (fun i x => inner ℝ (w i) x)) k.toFinset
          (fun i => inner ℝ (w i) x) ∂μ := by
  rw [JetCalculus.mixedJet_sub (smooth_crossMGF hμ) contDiff_const,
    JetCalculus.mixedJet_const,ite_eq_right hn,sub_zero,mixedJet_crossMGF hμ v w l k hl hk]

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι N : Type*} [DecidableEq ι] [Fintype N] [DecidableEq N]

def assignments (n₀ : N) : List ι → List (ι → N)
  | [] => [fun _ => n₀]
  | i::l => (assignments n₀ l).flatMap (fun p =>
      (Finset.univ.toList : List N).map (fun j => Function.update p i j))

omit [DecidableEq N] in
lemma length_assignments (n₀ : N) (l : List ι) :
    (assignments n₀ l).length = (Fintype.card N)^l.length := by
  induction l with
  | nil => simp [assignments]
  | cons i l ih =>
    simp only [assignments,List.length_flatMap,List.length_map,Finset.length_toList,
      Finset.card_univ,List.map_const',List.sum_replicate,smul_eq_mul,ih,List.length_cons,pow_succ]

omit [DecidableEq N] in
lemma mem_assignments (n₀ : N) (l : List ι) (hl : l.Nodup) (p : ι → N)
    (hp : ∀ i, i ∉ l → p i=n₀) : p ∈ assignments n₀ l := by
  induction l generalizing p with
  | nil =>
    have : p=(fun _ => n₀) := funext (fun i => hp i (by simp))
    simp [assignments,this]
  | cons i l ih =>
    have hin := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    apply List.mem_flatMap.mpr
    refine ⟨Function.update p i n₀,ih hl' (Function.update p i n₀) (fun j hj => ?_),?_⟩
    · by_cases hji : j=i
      · simp [hji]
      · simpa [Function.update_of_ne hji] using hp j (by simp [hji,hj])
    · apply List.mem_map.mpr
      refine ⟨p i,by simp,?_⟩
      ext j
      by_cases hji : j=i <;> simp [hji,Function.update_of_ne]

omit [Fintype N] in
lemma filter_update (l : List ι) (i : ι) (hi : i ∉ l) (p : ι → N) (j n : N) :
    l.filter (fun a => Function.update p i j a=n) = l.filter (fun a => p a=n) := by
  apply List.filter_congr
  intro a ha
  have hai : a ≠ i := fun h => hi (h ▸ ha)
  simp [Function.update_of_ne hai]

lemma differentiable_list_sum {K : Type*} (l : List K) {f : K → E → ℝ}
    (hf : ∀ i ∈ l, Differentiable ℝ (f i)) :
    Differentiable ℝ (fun x => (l.map (fun i => f i x)).sum) := by
  induction l with
  | nil => simpa only [List.map_nil,List.sum_nil] using (differentiable_const (0:ℝ) : Differentiable ℝ (fun _ : E => (0:ℝ)))
  | cons i l ih =>
    simpa only [List.map_cons,List.sum_cons] using
      (hf i (by simp)).fun_add (ih (fun j hj => hf j (by simp [hj])))

lemma dir_list_sum {K : Type*} (l : List K) {f : K → E → ℝ}
    (hf : ∀ i ∈ l, Differentiable ℝ (f i)) (v : E) :
    dir v (fun x => (l.map (fun i => f i x)).sum) =
      fun x => (l.map (fun i => dir v (f i) x)).sum := by
  induction l with
  | nil =>
    funext x
    change fderiv ℝ (fun _ : E => (0:ℝ)) x v = 0
    simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [dir_add (hf i (by simp))]
    · rw [ih (fun j hj => hf j (by simp [hj]))]
    · exact differentiable_list_sum l (fun j hj => hf j (by simp [hj]))

lemma list_sum_flatMap {K : Type*} (l : List K) (f : K → List ℝ) :
    (l.flatMap f).sum=(l.map (fun i => (f i).sum)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ih]

omit [DecidableEq N] in
lemma sum_eq_list (f : N → ℝ) :
    (∑ n, f n) = ((Finset.univ.toList : List N).map f).sum := by
  classical
  simp only [← List.sum_toFinset f (Finset.nodup_toList (Finset.univ : Finset N)),
    Finset.toList_toFinset]

lemma dir_prod {f : N → E → ℝ} (hf : ∀ n, Differentiable ℝ (f n)) (v : E) :
    dir v (fun x => ∏ n, f n x) = fun x =>
      ∑ j, ∏ n, (if n=j then dir v (f n) x else f n x) := by
  funext x
  rw [dir,(HasFDerivAt.finsetProd (fun n (_ : n ∈ (Finset.univ : Finset N)) =>
    (hf n x).hasFDerivAt)).fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hh : (fun n => if n=j then dir v (f n) x else f n x)=
      Function.update (fun n => f n x) j (dir v (f j) x) := by ext n; by_cases h : n=j <;> simp [h]
  rw [hh,Finset.prod_update_of_mem hj]
  simp only [Finset.sdiff_singleton_eq_erase,dir]
  ring

theorem jet_prod {f : N → E → ℝ} (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (n₀ : N) (v : ι → E) (l : List ι) (hl : l.Nodup) :
    jet v l (fun x => ∏ n, f n x) = fun x =>
      ((assignments n₀ l).map (fun p => ∏ n, jet v (l.filter (fun i => p i=n)) (f n) x)).sum := by
  induction l with
  | nil => simp [jet,assignments]
  | cons i l ih =>
    have hi := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    rw [jet,ih hl',dir_list_sum _ (fun p hp =>
      (contDiff_prod (fun n _ => smooth_jet (hf n) v _)).differentiable (by simp))]
    funext x
    simp only [assignments,List.map_flatMap,list_sum_flatMap,List.map_map,Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [dir_prod (fun n => (smooth_jet (hf n) v _).differentiable (by simp))]
    dsimp only
    rw [sum_eq_list]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    apply Finset.prod_congr rfl
    intro n hn
    rw [List.filter_cons,filter_update l i hi]
    by_cases hnj : n=j
    · simp [hnj,jet]
    · simp [hnj,Ne.symm hnj]

end JetCalculus
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_DirLogLaplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling.Appell
open MeasureTheory
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma dir_log_laplace {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) (v : E) :
    JetCalculus.dir v (fun θ => Real.log (laplace μ (fun _ => (1:ℝ)) θ)) =
      normalizedLaplace μ (fun z => inner ℝ v z) := by
  funext θ
  have hM := hasFDerivAt_laplace hμ continuous_const (HasGrowth.const (1:ℝ)) θ
  have hd := congrFun (dir_laplace hμ continuous_const (HasGrowth.const (1:ℝ)) v) θ
  simp only [mul_one] at hd
  change (fderiv ℝ (fun θ => Real.log (laplace μ (fun _ => (1:ℝ)) θ)) θ) v = _
  rw [(hM.log (laplace_one_pos hμ θ).ne').fderiv]
  simp only [smul_apply,smul_eq_mul,normalizedLaplace]
  rw [← hd,JetCalculus.dir,hM.fderiv]

end LogConcaveSampling.Appell

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_MixedJetAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling.JetCalculus
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type*}

lemma mixedJet_add {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (w : κ → E) (l : List ι) (k : List κ) :
    mixedJet v w l k (fun x => f (x.1+x.2)) =
      jet (Sum.elim v w) (l.map Sum.inl++k.map Sum.inr) f 0 := by
  let A : E × E →L[ℝ] E := ContinuousLinearMap.fst ℝ E E+ContinuousLinearMap.snd ℝ E E
  have hh := congrFun (jet_comp_affine hf A 0
    (Sum.elim (fun i => (v i,(0:E))) (fun j => ((0:E),w j)))
    (l.map Sum.inl++k.map Sum.inr)) 0
  have hdir : (fun i => A (Sum.elim (fun i => (v i,(0:E)))
      (fun j => ((0:E),w j)) i))=Sum.elim v w := by
    funext i
    cases i <;> simp [A]
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : E × E => f (x.1+x.2)) :=
    hf.comp (contDiff_fst.add contDiff_snd)
  rw [mixedJet_eq_joint hs]
  rw [hdir] at hh
  simpa [A] using hh

end LogConcaveSampling.JetCalculus

namespace LogConcaveSampling.JetCalculus
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

lemma dir_dir {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v w : E) :
    dir v (dir w f)=dir w (dir v f) := by
  funext x
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd : Differentiable ℝ (fderiv ℝ f) := hs.differentiable (by simp)
  change (fderiv ℝ (fun y => fderiv ℝ f y w) x) v =
    (fderiv ℝ (fun y => fderiv ℝ f y v) x) w
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _),
    fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simpa only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,ContinuousLinearMap.map_zero,zero_add,
    ContinuousLinearMap.flip_apply,fderiv_const_apply] using
    ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))).eq v w

lemma jet_perm {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) {l k : List ι} (hp : l.Perm k) : jet v l f=jet v k f := by
  induction hp with
  | nil => rfl
  | cons i hp ih => simp only [jet,ih]
  | swap i j l => exact dir_dir (smooth_jet hf v l) (v j) (v i)
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

lemma dir_smul (v : E) (c : ℝ) (f : E → ℝ) :
    dir (c • v) f=fun x => c*dir v f x := by
  funext x
  simp only [dir,map_smul,smul_eq_mul]

end LogConcaveSampling.JetCalculus

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TiltedExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace

lemma growth_const {d : ℕ} {E : Type*} [NormedAddCommGroup E] (c : E) :
    HasPolynomialGrowth (fun _ : Point d => c) := by
  refine ⟨‖c‖,norm_nonneg _,0,fun z => ?_⟩
  simp only [pow_zero]
  nlinarith [norm_nonneg c]

lemma Primitive.hasGaussianLowerTail {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) : HasGaussianLowerTail (primitivePotential F x r) := by
  obtain ⟨z₀,hz,_,_⟩ := hF.exists_unique_mode x hr hl
  let a := (1-(lam:ℝ)*r^2)/2
  have ha : 0 < a := by dsimp [a]; linarith
  refine ⟨a/2,by positivity,a*‖z₀‖^2-primitivePotential F x r z₀,fun z => ?_⟩
  have hb := (primitivePotential_mode_bounds hF x hr hz (z-z₀)).1
  rw [add_sub_cancel] at hb
  have hn := norm_add_le (z-z₀) z₀
  simp only [sub_add_cancel] at hn
  have hs : ‖z‖^2 ≤ 2*‖z-z₀‖^2+2*‖z₀‖^2 := by
    have hsq := pow_le_pow_left₀ (norm_nonneg z) hn 2
    nlinarith [sq_nonneg (‖z-z₀‖-‖z₀‖)]
  have hh := mul_le_mul_of_nonneg_left hs ha.le
  dsimp [a] at *
  nlinarith

lemma growth_of_lipschitz {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {h : Point d → E} {K : ℝ≥0} (hh : LipschitzWith K h) : HasPolynomialGrowth h := by
  refine ⟨(K:ℝ)+‖h 0‖,by positivity,1,fun z => ?_⟩
  have hb := hh.dist_le_mul z 0
  rw [dist_zero_right,dist_eq_norm] at hb
  have hn := norm_add_le (h z-h 0) (h 0)
  simp only [sub_add_cancel] at hn
  simp only [pow_one]
  nlinarith [mul_nonneg (norm_nonneg (h 0)) (norm_nonneg z)]

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_ConditionalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory

lemma HasGaussianLowerTail.hasExpMoments {d : ℕ} {H : Point d → ℝ}
    (ht : HasGaussianLowerTail H) (hc : Continuous H) : Appell.HasExpMoments (gibbs H) := by
  have hi := integrable_tilted H hc continuous_const ht (growth_const (1:ℝ)) 0
  simp only [inner_zero_left,zero_sub,smul_eq_mul,mul_one] at hi
  obtain ⟨m,hm,C,ht⟩ := ht
  intro R
  apply integrable_gibbs_of_weighted hc hi
  have hct : Continuous (fun x => Real.exp (-H x)*Real.exp (R*‖x‖)) :=
    hc.neg.rexp.mul ((continuous_const.mul continuous_norm).rexp)
  apply ((integrable_gaussian_envelope d (b := m/2) (by positivity)).const_mul
    (Real.exp (C+R^2/(2*m)))).mono'
    hct.aestronglyMeasurable
  filter_upwards [] with x
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hyp : R*‖x‖ ≤ (m/2)*‖x‖^2+R^2/(2*m) := by
    have hh := sq_nonneg (m*‖x‖-R)
    have hd : R^2/(2*m)*(2*m)=R^2 := by field_simp
    nlinarith
  linarith [ht x]

lemma Primitive.hasExpMoments {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) : Appell.HasExpMoments (gibbs (primitivePotential F x r)) :=
  (hF.hasGaussianLowerTail x hr hl).hasExpMoments (hF.continuous_potential x r)

namespace Appell
lemma HasExpMoments.map_lipschitz {E F : Type} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] {μ : Measure E}
    (hμ : HasExpMoments μ) {S : E → F} {K : ℝ≥0} (hS : LipschitzWith K S) :
    HasExpMoments (μ.map S) := by
  intro R
  apply (integrable_map_measure ((continuous_const.mul continuous_norm).rexp).aestronglyMeasurable
    hS.continuous.aemeasurable).2
  apply ((hμ (|R| *K)).const_mul (Real.exp (|R| *‖S 0‖))).mono'
    ((continuous_const.mul hS.continuous.norm).rexp).aestronglyMeasurable
  filter_upwards [] with x
  change ‖Real.exp (R*‖S x‖)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb : ‖S x‖ ≤ K*‖x‖+‖S 0‖ := by
    have hh := hS.dist_le_mul x 0
    simp only [dist_eq_norm,sub_zero] at hh
    have hh' := norm_add_le (S x-S 0) (S 0)
    rw [sub_add_cancel] at hh'
    linarith
  have ht := mul_le_mul_of_nonneg_left hb (abs_nonneg R)
  have hr := mul_le_mul_of_nonneg_right (le_abs_self R) (norm_nonneg (S x))
  nlinarith
end Appell
end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped ENNReal

theorem gibbs_map_equiv {d : ℕ} {H : Point d → ℝ} (hH : Continuous H)
    (e : Point d ≃ᵐ Point d) {c : ℝ≥0∞} (hc0 : c≠0) (hct : c≠⊤)
    (he : (volume : Measure (Point d)).map e=c • volume) :
    (gibbs H).map e=gibbs (fun y => H (e.symm y)) := by
  have hm : ((volume : Measure (Point d)).withDensity (gibbsDensity H)).map e =
      c • volume.withDensity (gibbsDensity (fun y => H (e.symm y))) := by
    rw [EulerDensity.map_withDensity_equiv volume e (by unfold gibbsDensity; fun_prop),
      he,withDensity_smul_measure]
    rfl
  have hp : partition H=c*partition (fun y => H (e.symm y)) := by
    have hh := congrArg (fun μ : Measure (Point d) => μ Set.univ) hm
    simpa only [Measure.map_apply e.measurable MeasurableSet.univ,Set.preimage_univ,
      Measure.smul_apply,smul_eq_mul,withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ,partition] using hh
  unfold gibbs
  rw [Measure.map_smul,hm,hp,smul_smul,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  congr 1
  calc
    (c⁻¹*(partition (fun y => H (e.symm y)))⁻¹)*c =
        (c⁻¹*c)*(partition (fun y => H (e.symm y)))⁻¹ := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hc0 hct,one_mul]

lemma gibbs_map_smul {d : ℕ} {H : Point d → ℝ} (hH : Continuous H)
    {s : ℝ} (hs : s≠0) :
    (gibbs H).map (fun z => s • z)=gibbs (fun z => H (s⁻¹ • z)) := by
  let e := (Homeomorph.smulOfNeZero (α := Point d) s hs).toMeasurableEquiv
  have he : (volume : Measure (Point d)).map e =
      ENNReal.ofReal |(s^d)⁻¹| • volume := by
    convert! Measure.map_addHaar_smul (volume : Measure (Point d)) hs using 1
    all_goals try with_reducible_and_instances rfl
    simp [Point]
  have h := gibbs_map_equiv hH e
    (by positivity : ENNReal.ofReal |(s^d)⁻¹| ≠ 0)
    ENNReal.ofReal_ne_top he
  change (gibbs H).map e = _
  rw [h]
  congr 1

lemma gibbs_map_add {d : ℕ} {H : Point d → ℝ} (hH : Continuous H) (v : Point d) :
    (gibbs H).map (fun z => v+z)=gibbs (fun z => H (z-v)) := by
  let e := (Homeomorph.addLeft v).toMeasurableEquiv
  have he : (volume : Measure (Point d)).map e = (1:ℝ≥0∞) • volume := by
    change (volume : Measure (Point d)).map (fun z => v+z) = _
    simpa only [one_smul] using (measurePreserving_add_left (volume : Measure (Point d)) v).map_eq
  change (gibbs H).map e = _
  rw [gibbs_map_equiv hH e (by norm_num) (by norm_num) he]
  congr 1
  funext z
  apply congrArg H
  change -v+z=z-v
  abel

lemma gibbs_map_affine {d : ℕ} {H : Point d → ℝ} (hH : Continuous H)
    (v : Point d) {s : ℝ} (hs : s≠0) :
    (gibbs H).map (fun z => v+s • z)=gibbs (fun z => H (s⁻¹ • (z-v))) := by
  change (gibbs H).map ((fun z => v+z) ∘ (fun z => s • z)) = _
  rw [← Measure.map_map (show Measurable (fun z : Point d => v+z) by fun_prop)
    (show Measurable (fun z : Point d => s • z) by fun_prop),gibbs_map_smul hH hs]
  exact gibbs_map_add (show Continuous (fun z : Point d => H (s⁻¹ • z)) by fun_prop) v

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped NNReal RealInnerProductSpace

def conditionalPotential {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y z : Point d) : ℝ :=
  ‖z-ρ • y‖^2/(2*(1-ρ^2)) + F (x+r • z)

lemma probability_time {ρ : ℝ} (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    0 < 1-ρ^2 ∧ 1-ρ^2 ≤ 1 := by
  constructor
  · nlinarith
  · nlinarith [sq_nonneg ρ]

lemma conditionalPotential_pullback {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y z : Point d) (ha : 0<1-ρ^2) :
    primitivePotential F (x+r • (ρ • y)) (r*Real.sqrt (1-ρ^2))
      ((Real.sqrt (1-ρ^2))⁻¹ • (z-ρ • y)) = conditionalPotential F x r ρ y z := by
  have hs : Real.sqrt (1-ρ^2) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hv : x+r • (ρ • y)+(r*Real.sqrt (1-ρ^2)) •
      ((Real.sqrt (1-ρ^2))⁻¹ • (z-ρ • y))=x+r • z := by
    rw [← mul_smul r ρ y,smul_smul,mul_assoc,mul_inv_cancel₀ hs,mul_one,smul_sub]
    rw [smul_smul]
    abel
  unfold primitivePotential conditionalPotential
  rw [hv,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow,Real.sq_sqrt ha.le]
  congr 1
  field_simp

lemma conditionalLaw_map {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r ρ : ℝ) (y : Point d) (ha : 0<1-ρ^2) :
    (gibbs (primitivePotential F (x+r • (ρ • y)) (r*Real.sqrt (1-ρ^2)))).map
      (fun z => ρ • y+Real.sqrt (1-ρ^2) • z) =
      gibbs (conditionalPotential F x r ρ y) := by
  rw [gibbs_map_affine (hF.continuous_potential _ _)
    _ (Real.sqrt_pos.mpr ha).ne']
  congr 1
  funext z
  exact conditionalPotential_pullback F x r ρ y z ha

lemma conditional_smallness {lam : ℝ≥0} {r ρ : ℝ}
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (ha : 0<1-ρ^2) (ha1 : 1-ρ^2≤1) :
    (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 ≤ 1/2 := by
  rw [mul_pow,Real.sq_sqrt ha.le]
  have hn : 0≤(lam:ℝ)*r^2 := mul_nonneg lam.coe_nonneg (sq_nonneg r)
  calc
    (lam:ℝ)*(r^2*(1-ρ^2))=((lam:ℝ)*r^2)*(1-ρ^2) := by ring
    _ ≤ ((lam:ℝ)*r^2)*1 := mul_le_mul_of_nonneg_left ha1 hn
    _ ≤ 1/2 := by simpa using hl

lemma conditionalLaw_probability {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    IsProbabilityMeasure (gibbs (conditionalPotential F x r ρ y)) := by
  obtain ⟨ha,ha1⟩ := probability_time hρ0 hρ1
  have hs := conditional_smallness hl ha ha1
  have hsmall : (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 < 1 := by linarith
  have hrad : 0 ≤ r*Real.sqrt (1-ρ^2) := mul_nonneg hr (Real.sqrt_nonneg _)
  have : IsProbabilityMeasure (gibbs (primitivePotential F (x+r • (ρ • y))
      (r*Real.sqrt (1-ρ^2)))) := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential _ _)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential _ hrad hsmall))
  rw [← conditionalLaw_map hF x r ρ y ha]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

lemma conditionalLaw_hasPoincare {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    HasPoincare (gibbs (conditionalPotential F x r ρ y)) ((Real.pi^2/2)*(1-ρ^2)) := by
  obtain ⟨ha,ha1⟩ := probability_time hρ0 hρ1
  have hs := conditional_smallness hl ha ha1
  have hsmall : (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 < 1 := by linarith
  have hrad : 0 ≤ r*Real.sqrt (1-ρ^2) := mul_nonneg hr (Real.sqrt_nonneg _)
  have : IsProbabilityMeasure (gibbs (primitivePotential F (x+r • (ρ • y))
      (r*Real.sqrt (1-ρ^2)))) := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential _ _)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential _ hrad hsmall))
  let K : ℝ≥0 := ⟨Real.sqrt (1-ρ^2),Real.sqrt_nonneg _⟩
  have hK : LipschitzWith K (fun z : Point d => ρ • y+Real.sqrt (1-ρ^2) • z) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [dist_eq_norm,add_sub_add_left_eq_sub,← smul_sub,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    rfl
  have hB : 0≤(Real.pi^2/8)*(2/(1-(lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2)) := by positivity
  have hp := (hF.hasPoincare (x+r • (ρ • y)) hrad hsmall).map hB
    (show ContDiff ℝ 1 (fun z : Point d => ρ • y+Real.sqrt (1-ρ^2) • z) by fun_prop) hK
  rw [conditionalLaw_map hF x r ρ y ha] at hp
  apply hp.mono
  change (Real.pi^2/8)*(2/(1-(lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2)) *
    (Real.sqrt (1-ρ^2))^2 ≤ _
  rw [Real.sq_sqrt ha.le]
  apply mul_le_mul_of_nonneg_right _ ha.le
  have hd : 0<1-(lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 := sub_pos.mpr hsmall
  have hb : 2/(1-(lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2) ≤ 4 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ)≤Real.pi^2/8)]

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PrimitiveField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory

lemma conditionalLaw_hasExpMoments {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    Appell.HasExpMoments (gibbs (conditionalPotential F x r ρ y)) := by
  obtain ⟨ha,ha1⟩ := probability_time hρ0 hρ1
  have hs := conditional_smallness hl ha ha1
  have hsmall : (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 < 1 := by linarith
  have hrad : 0 ≤ r*Real.sqrt (1-ρ^2) := mul_nonneg hr (Real.sqrt_nonneg _)
  rw [← conditionalLaw_map hF x r ρ y ha]
  apply (hF.hasExpMoments (x+r • (ρ • y)) hrad hsmall).map_lipschitz
    (K := ⟨Real.sqrt (1-ρ^2),Real.sqrt_nonneg _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [dist_eq_norm,add_sub_add_left_eq_sub,← smul_sub,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  rfl
end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

def primitiveField {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (z : Point d) : Point d :=
  gradient F (x+r • z)

abbrev JointPoint (d : ℕ) := EuclideanSpace ℝ (Fin d ⊕ Fin d)

def jointImage {d : ℕ} (f : Point d → Point d) (L : ℝ) (z : Point d) : JointPoint d :=
  EuclideanSpace.sumEquivProd.symm (z,L⁻¹ • f z)

lemma primitiveField_contDiff {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r : ℝ) :
    ContDiff ℝ 1 (primitiveField F x r) :=
  (Trapezoid.contDiff_gradient hF.smooth).comp (show ContDiff ℝ 1 (fun z : Point d => x+r • z) by fun_prop)

lemma primitiveField_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r) :
    LipschitzWith (lam*(NNReal.mk r hr)) (primitiveField F x r) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hh := hF.gradient_lipschitz.dist_le_mul (x+r • u) (x+r • v)
  change _ ≤ ((lam:ℝ)*r)*dist u v
  simpa only [primitiveField,dist_add_left,dist_smul₀,Real.norm_eq_abs,abs_of_nonneg hr,
    mul_assoc] using hh

def jointConditionalLaw {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y : Point d) (L : ℝ) : Measure (JointPoint d) :=
  (gibbs (conditionalPotential F x r ρ y)).map (jointImage (primitiveField F x r) L)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ConditionalMeanScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma integral_gibbs_add_const {d : ℕ} {H : Point d → ℝ} (hc : Continuous H)
    (hi : Integrable (fun z => Real.exp (-H z))) (c : ℝ) (f : Point d → ℝ) :
    (∫ z,f z ∂gibbs (fun z => H z+c))=∫ z,f z ∂gibbs H := by
  have he : (fun z => Real.exp (-(H z+c)))=fun z => Real.exp (-c)*Real.exp (-H z) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  have hi' : Integrable (fun z => Real.exp (-(H z+c))) := by rw [he]; exact hi.const_mul _
  rw [integral_gibbs (hc.add_const c) hi', integral_gibbs hc hi]
  simp_rw [congrFun he,mul_assoc]
  rw [integral_const_mul,integral_const_mul,mul_div_mul_left _ _ (Real.exp_pos _).ne']

lemma HasGaussianLowerTail.integrable_exp {d : ℕ} {H : Point d → ℝ}
    (ht : HasGaussianLowerTail H) (hc : Continuous H) :
    Integrable (fun z => Real.exp (-H z)) := by
  simpa only [inner_zero_left,zero_sub,smul_eq_mul,mul_one] using
    integrable_tilted H hc continuous_const ht (growth_const (1:ℝ)) 0

lemma HasGaussianLowerTail.comp_inverse_affine {d : ℕ} {H : Point d → ℝ}
    (ht : HasGaussianLowerTail H) (v : Point d) {s : ℝ} (hs : 0 < s) :
    HasGaussianLowerTail (fun z => H (s⁻¹ • (z-v))) := by
  obtain ⟨m,hm,C,hb⟩ := ht
  refine ⟨m/(2*s^2),by positivity,C+(m/s^2)*‖v‖^2,fun z => ?_⟩
  have hh := hb (s⁻¹ • (z-v))
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),mul_pow,inv_pow] at hh
  have hn := norm_add_le (z-v) v
  rw [sub_add_cancel] at hn
  have hk := pow_le_pow_left₀ (norm_nonneg z) hn 2
  have hsq : ‖z‖^2 ≤ 2*‖z-v‖^2+2*‖v‖^2 := by
    nlinarith [sq_nonneg (‖z-v‖-‖v‖)]
  have hd : m/(2*s^2)*2=m/s^2 := by field_simp
  have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ m / (2*s^2))
  simp only [mul_add,← mul_assoc,hd] at hmul
  have he : m*(s^2)⁻¹=m/s^2 := by ring
  rw [← mul_assoc,he] at hh
  linarith

lemma normalizedLaplace_gibbs {d : ℕ} {H : Point d → ℝ} (hc : Continuous H)
    (hi : Integrable (fun z => Real.exp (-H z))) (θ : Point d)
    (hit : Integrable (fun z => Real.exp (inner ℝ θ z-H z))) (f : Point d → ℝ) :
    Appell.normalizedLaplace (gibbs H) f θ =
      ∫ z,f z ∂gibbs (fun z => H z-inner ℝ θ z) := by
  have he : ∀ z,Real.exp (-H z)*Real.exp (inner ℝ θ z)=Real.exp (inner ℝ θ z-H z) := by
    intro z
    rw [← Real.exp_add]
    congr 1
    ring
  have hit' : Integrable (fun z => Real.exp (-(H z-inner ℝ θ z))) := by
    simpa only [neg_sub] using hit
  rw [Appell.normalizedLaplace,Appell.laplace,Appell.laplace]
  have hct : Continuous (fun z => H z-inner ℝ θ z) := by fun_prop
  rw [integral_gibbs hc hi,integral_gibbs hc hi,integral_gibbs hct hit']
  simp only [smul_eq_mul,mul_one,← mul_assoc,he,neg_sub]
  have hA : (∫ z,Real.exp (-H z))≠0 := (integral_exp_pos hi).ne'
  have hB : (∫ z,Real.exp (inner ℝ θ z-H z))≠0 := (integral_exp_pos hit).ne'
  field_simp

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma conditionalPotential_continuous {d : ℕ} {F : Point d → ℝ} (hc : Continuous F)
    (x : Point d) (r ρ : ℝ) (y : Point d) : Continuous (conditionalPotential F x r ρ y) := by
  unfold conditionalPotential
  fun_prop

lemma conditional_hasGaussianLowerTail {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    HasGaussianLowerTail (conditionalPotential F x r ρ y) := by
  obtain ⟨ha,ha1⟩ := probability_time hρ0 hρ1
  have hs := conditional_smallness hl ha ha1
  have ht := (hF.hasGaussianLowerTail (x+r • (ρ • y))
    (mul_nonneg hr (Real.sqrt_nonneg _)) (by linarith :
      (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2<1)).comp_inverse_affine
      (ρ • y) (Real.sqrt_pos.mpr ha)
  simpa only [conditionalPotential_pullback F x r ρ y _ ha] using ht

lemma conditionalPotential_shift {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y h z : Point d) :
    conditionalPotential F x r ρ (y+h) z =
    conditionalPotential F x r ρ y z-inner ℝ ((ρ/(1-ρ^2)) • h) z+
      (ρ^2/(2*(1-ρ^2)))*(‖y+h‖^2-‖y‖^2) := by
  simp only [conditionalPotential,norm_sub_sq_real,inner_smul_right,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs,inner_add_right,inner_smul_left,starRingEnd_apply,star_trivial]
  rw [real_inner_comm h z]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

def conditionalMeanScalar {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (f : Point d → ℝ) (y : Point d) : ℝ := ∫ z,f z ∂gibbs (conditionalPotential F x r ρ y)

theorem conditionalMeanScalar_shift {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (f : Point d → ℝ) (y h : Point d) :
    conditionalMeanScalar F x r ρ f (y+h)=
      Appell.normalizedLaplace (gibbs (conditionalPotential F x r ρ y)) f
        ((ρ/(1-ρ^2)) • h) := by
  let H := conditionalPotential F x r ρ y
  let θ := (ρ/(1-ρ^2)) • h
  have hH : Continuous H := conditionalPotential_continuous hF.smooth.continuous x r ρ y
  have ht : HasGaussianLowerTail H := conditional_hasGaussianLowerTail hF x hr hl hρ0 hρ1 y
  have hi := ht.integrable_exp hH
  have hit : Integrable (fun z => Real.exp (inner ℝ θ z-H z)) := by
    simpa only [smul_eq_mul,mul_one] using
      integrable_tilted H hH continuous_const ht (growth_const (1:ℝ)) θ
  rw [normalizedLaplace_gibbs hH hi θ hit]
  unfold conditionalMeanScalar
  have hp : conditionalPotential F x r ρ (y+h) = fun z =>
      (H z-inner ℝ θ z)+(ρ^2/(2*(1-ρ^2)))*(‖y+h‖^2-‖y‖^2) := by
    funext z
    exact conditionalPotential_shift F x r ρ y h z
  rw [hp]
  apply integral_gibbs_add_const (hH.sub (continuous_const.inner continuous_id))
  simpa only [Pi.sub_apply,id_eq,neg_sub] using hit

theorem conditionalMeanScalar_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {f : Point d → ℝ} (hf : Continuous f) (hg : Appell.HasGrowth f) :
    ContDiff ℝ (⊤ : ℕ∞) (conditionalMeanScalar F x r ρ f) := by
  let μ := gibbs (conditionalPotential F x r ρ 0)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 (0 : Point d)
  have hμ := conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 (0 : Point d)
  have he : conditionalMeanScalar F x r ρ f = fun y =>
      Appell.normalizedLaplace μ f ((ρ/(1-ρ^2)) • y) := by
    funext y
    simpa only [zero_add] using conditionalMeanScalar_shift hF x hr hl hρ0 hρ1 f 0 y
  rw [he]
  exact (Appell.smooth_normalizedLaplace hμ hf hg).comp (by fun_prop)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_JointPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

def jointPosition (d : ℕ) : Point d →L[ℝ] JointPoint d :=
  EuclideanSpace.sumEquivProd.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _)

def jointField (d : ℕ) : Point d →L[ℝ] JointPoint d :=
  EuclideanSpace.sumEquivProd.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ _ _)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ConditionalFieldMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace Topology

lemma primitiveField_inner_growth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x u : Point d) {r : ℝ} (hr : 0 ≤ r) :
    Appell.HasGrowth (fun z => inner ℝ u (primitiveField F x r z)) :=
  Appell.HasGrowth.lipschitz ((innerSL ℝ u).lipschitz.comp (primitiveField_lipschitz hF x hr))

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

lemma covariance_sq_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (cov[f,g;μ])^2 ≤ Var[f;μ]*Var[g;μ] := by
  rw [covariance,variance_eq_integral hf.aemeasurable,variance_eq_integral hg.aemeasurable]
  exact integral_mul_sq_le (hf.sub (memLp_const _)) (hg.sub (memLp_const _))

namespace Appell
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma powerset_singleton {ι : Type*} [DecidableEq ι] (i : ι) :
    ({i}:Finset ι).powerset={∅,{i}} := by
  ext s
  simp [Finset.subset_singleton_iff]

lemma inverseMoment_singleton {ι : Type*} [DecidableEq ι] (m : Finset ι → ℝ) (i : ι) :
    inverseMoment m {i} = -m {i} := by
  rw [inverseMoment_nonempty _ (Finset.singleton_nonempty i).ne_empty]
  rw [powerset_singleton]
  simp

lemma polynomial_singleton {ι : Type*} [DecidableEq ι] (m : Finset ι → ℝ) (i : ι) (z : ι → ℝ) :
    polynomial m {i} z=z i-m {i} := by
  simp [polynomial, powerset_singleton, inverseMoment_singleton,sub_eq_add_neg]

lemma dir_normalizedLaplace_zero {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {f : E → ℝ} (hf : Continuous f) (hg : HasGrowth f) (v : E) :
    JetCalculus.dir v (normalizedLaplace μ f) 0=
      cov[(fun z => inner ℝ v z),f;μ] := by
  have hh := jet_normalizedLaplace_zero hμ hf hg (fun _ : Unit => v) [()]
    (by simp)
  simp only [JetCalculus.jet,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,
    polynomial_singleton,moments,Finset.prod_singleton] at hh
  rw [hh]
  let g : E → ℝ := fun z => inner ℝ v z
  have hgm : MemLp g 2 μ := (HasGrowth.linear (innerSL ℝ v)).memLp
    (by fun_prop) hμ.hasMoments
  have hfm := hg.memLp hf.aestronglyMeasurable hμ.hasMoments
  rw [covariance_eq_sub hgm hfm]
  simp only [sub_mul]
  change (∫ x, g x*f x-(∫ z, g z ∂μ)*f x ∂μ)=_
  simpa only [Pi.mul_apply,integral_const_mul] using
    integral_sub (hgm.integrable_mul hfm)
      ((hfm.integrable (by norm_num)).const_mul (∫ z, g z ∂μ))

end Appell

theorem conditionalFieldMean_dir_cov {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (u v y : Point d) :
    JetCalculus.dir v
      (conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z))) y=
      (ρ/(1-ρ^2))*cov[(fun z => inner ℝ v z),
        (fun z => inner ℝ u (primitiveField F x r z));gibbs (conditionalPotential F x r ρ y)] := by
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hm := conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y
  let f : Point d → ℝ := fun z => inner ℝ u (primitiveField F x r z)
  have hfc : Continuous f := continuous_const.inner (primitiveField_contDiff hF x r).continuous
  have hfg : Appell.HasGrowth f := primitiveField_inner_growth hF x u hr
  have hmean := conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 hfc hfg
  have hs := Appell.smooth_normalizedLaplace hm hfc hfg
  have he : (fun h => conditionalMeanScalar F x r ρ f (h+y))=
      fun h => Appell.normalizedLaplace μ f ((ρ/(1-ρ^2)) • h) := by
    funext h
    simpa only [add_comm h y] using conditionalMeanScalar_shift hF x hr hl hρ0 hρ1 f y h
  have htr := congrFun (JetCalculus.dir_comp_affine
    (hmean.differentiable (by simp)) (ContinuousLinearMap.id ℝ (Point d)) y v) 0
  simp only [ContinuousLinearMap.id_apply,zero_add] at htr
  rw [← htr,he]
  let B : Point d →L[ℝ] Point d := (ρ/(1-ρ^2)) • ContinuousLinearMap.id ℝ (Point d)
  have heB : (fun h => Appell.normalizedLaplace μ f ((ρ/(1-ρ^2)) • h))=
      fun h => Appell.normalizedLaplace μ f (B h+0) := by
    funext h; simp [B]
  rw [heB]
  rw [JetCalculus.dir_comp_affine (hs.differentiable (by simp))]
  simp only [map_zero,zero_add]
  change JetCalculus.dir ((ρ/(1-ρ^2)) • v) (Appell.normalizedLaplace μ f) 0=_
  rw [JetCalculus.dir_smul]
  change (ρ/(1-ρ^2))*JetCalculus.dir v (Appell.normalizedLaplace μ f) 0=_
  rw [Appell.dir_normalizedLaplace_zero hm hfc hfg]

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

def conditionalFieldMean {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y : Point d) : Point d := ∫ z, primitiveField F x r z ∂gibbs (conditionalPotential F x r ρ y)

lemma conditionalField_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    Integrable (primitiveField F x r) (gibbs (conditionalPotential F x r ρ y)) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  exact (Appell.HasGrowth.lipschitz (primitiveField_lipschitz hF x hr)).integrable
    (primitiveField_contDiff hF x r).continuous.aestronglyMeasurable
    (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments

lemma conditionalFieldMean_inner {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (u y : Point d) :
    inner ℝ u (conditionalFieldMean F x r ρ y)=
      conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z)) y := by
  exact (integral_inner (conditionalField_integrable hF x hr hl hρ0 hρ1 y) u).symm

lemma conditionalFieldMean_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    ContDiff ℝ (⊤ : ℕ∞) (conditionalFieldMean F x r ρ) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have he : conditionalFieldMean F x r ρ = fun y => ∑ i : Fin d,
      conditionalMeanScalar F x r ρ (fun z => inner ℝ (b i) (primitiveField F x r z)) y • b i := by
    funext y
    simp_rw [← conditionalFieldMean_inner hF x hr hl hρ0 hρ1,
      ← b.repr_apply_apply]
    exact (b.sum_repr _).symm
  rw [he]
  apply ContDiff.sum
  intro i _
  exact (conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1
    (continuous_const.inner (primitiveField_contDiff hF x r).continuous)
    (primitiveField_inner_growth hF x (b i) hr)).smul contDiff_const

lemma conditional_covariance_le {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (u v y : Point d) :
    |cov[(fun z => inner ℝ v z), (fun z => inner ℝ u (primitiveField F x r z));
      gibbs (conditionalPotential F x r ρ y)]| ≤
      ((Real.pi^2/2)*(1-ρ^2))*((lam:ℝ)*r)*‖u‖*‖v‖ := by
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hm := (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments
  let f : Point d → ℝ := fun z => inner ℝ v z
  let g : Point d → ℝ := fun z => inner ℝ u (primitiveField F x r z)
  have hf : MemLp f 2 μ := (Appell.HasGrowth.linear (innerSL ℝ v)).memLp (by fun_prop) hm
  have hg : MemLp g 2 μ := (primitiveField_inner_growth hF x u hr).memLp
    (continuous_const.inner (primitiveField_contDiff hF x r).continuous).aestronglyMeasurable hm
  have hP := conditionalLaw_hasPoincare hF x hr hl hρ0 hρ1 y
  have hβ : 0≤(Real.pi^2/2)*(1-ρ^2) := mul_nonneg (by positivity) (probability_time hρ0 hρ1).1.le
  have hv := hP.lipschitz_variance hβ (innerSL ℝ v).contDiff (innerSL ℝ v).lipschitz hf
  have hu := hP.lipschitz_variance hβ ((innerSL ℝ u).contDiff.comp (primitiveField_contDiff hF x r))
    ((innerSL ℝ u).lipschitz.comp (primitiveField_lipschitz hF x hr)) hg
  simp only [NNReal.coe_mul,coe_nnnorm,innerSL_apply_norm,NNReal.coe_mk] at hv hu
  change Var[f;μ] ≤ _ at hv
  change Var[g;μ] ≤ _ at hu
  have hb := (covariance_sq_le hf hg).trans
    (mul_le_mul hv hu (variance_nonneg g μ) (mul_nonneg hβ (sq_nonneg _)))
  change |cov[f,g;μ]| ≤ _
  have hh : 0≤((Real.pi^2/2)*(1-ρ^2))*((lam:ℝ)*r)*‖u‖*‖v‖ := by positivity
  apply (sq_le_sq₀ (abs_nonneg _) hh).mp
  rw [sq_abs]
  convert! hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma conditionalFieldMean_inner_deriv {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (u v y : Point d) :
    inner ℝ u (fderiv ℝ (conditionalFieldMean F x r ρ) y v)=
      (ρ/(1-ρ^2))*cov[(fun z => inner ℝ v z), (fun z => inner ℝ u (primitiveField F x r z));
        gibbs (conditionalPotential F x r ρ y)] := by
  have he : (fun y => inner ℝ u (conditionalFieldMean F x r ρ y))=
      conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z)) :=
    funext (conditionalFieldMean_inner hF x hr hl hρ0 hρ1 u)
  have hd := (conditionalFieldMean_smooth hF x hr hl hρ0 hρ1).differentiable (by simp)
  have hh := (innerSL ℝ u).hasFDerivAt.comp y (hd y).hasFDerivAt
  have hh' := congrArg (fun A : Point d →L[ℝ] ℝ => A v) hh.fderiv
  change JetCalculus.dir v (fun y => inner ℝ u (conditionalFieldMean F x r ρ y)) y=
    inner ℝ u (fderiv ℝ (conditionalFieldMean F x r ρ) y v) at hh'
  rw [←hh',he]
  exact conditionalFieldMean_dir_cov hF x hr hl hρ0 hρ1 u v y

theorem conditionalFieldMean_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    LipschitzWith ⟨(Real.pi^2/2)*ρ*((lam:ℝ)*r), by positivity⟩
      (conditionalFieldMean F x r ρ) := by
  have hd := (conditionalFieldMean_smooth hF x hr hl hρ0 hρ1).differentiable (by simp)
  apply lipschitzWith_of_nnnorm_fderiv_le hd
  intro y
  apply (show ‖fderiv ℝ (conditionalFieldMean F x r ρ) y‖ ≤ (Real.pi^2/2)*ρ*((lam:ℝ)*r) from ?_)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let w := fderiv ℝ (conditionalFieldMean F x r ρ) y v
  have he := conditionalFieldMean_inner_deriv hF x hr hl hρ0 hρ1 w v y
  have hb := mul_le_mul_of_nonneg_left (conditional_covariance_le hF x hr hl hρ0 hρ1 w v y)
    (div_nonneg hρ0 (probability_time hρ0 hρ1).1.le)
  have hh : ‖w‖^2 ≤ ((Real.pi^2/2)*ρ*((lam:ℝ)*r))*‖w‖*‖v‖ := by
    rw [←real_inner_self_eq_norm_sq w,he]
    calc
      _ ≤ (ρ/(1-ρ^2))*|cov[(fun z => inner ℝ v z),
        (fun z => inner ℝ w (primitiveField F x r z));gibbs (conditionalPotential F x r ρ y)]| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (div_nonneg hρ0 (probability_time hρ0 hρ1).1.le)
      _ ≤ _ := by
        convert! hb using 1
        all_goals try with_reducible_and_instances rfl
        field_simp [(probability_time hρ0 hρ1).1.ne']
  change ‖w‖ ≤ _
  by_cases hw : ‖w‖=0
  · rw [hw]; positivity
  · apply (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw))).mp
    convert! hh using 1 <;> ring

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

def quadraticTilt {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Point d → ℝ) (h : Point d → E) (p : Point d × ℝ) : E :=
  ∫ z, Real.exp (inner ℝ p.1 z-p.2*‖z‖^2-H z) • h z

def quadraticLinear {d : ℕ} (z : Point d) : (Point d × ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ z).comp (ContinuousLinearMap.fst ℝ (Point d) ℝ) -
    ‖z‖^2 • ContinuousLinearMap.snd ℝ (Point d) ℝ

def quadraticDerivative {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : Point d → E) (z : Point d) : (Point d × ℝ) →L[ℝ] E :=
  (quadraticLinear z).smulRight (h z)

lemma quadraticLinear_apply {d : ℕ} (z : Point d) (p : Point d × ℝ) :
    quadraticLinear z p=inner ℝ p.1 z-p.2*‖z‖^2 := by
  simp [quadraticLinear,real_inner_comm,mul_comm]

lemma continuous_quadraticLinear {d : ℕ} : Continuous (quadraticLinear (d:=d)) := by
  exact ((innerSL ℝ).continuous.clm_comp continuous_const).sub
    ((continuous_norm.pow 2).smul continuous_const)

lemma norm_quadraticLinear {d : ℕ} (z : Point d) :
    ‖quadraticLinear z‖  ≤  ‖z‖+‖z‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  rw [quadraticLinear_apply]
  calc
    ‖inner ℝ p.1 z-p.2*‖z‖^2‖  ≤  ‖p.1‖*‖z‖+‖p.2‖*‖z‖^2 := by
      exact (norm_sub_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (by simp [norm_mul]))
    _  ≤  ‖p‖*‖z‖+‖p‖*‖z‖^2 := add_le_add
      (mul_le_mul_of_nonneg_right (norm_fst_le p) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (norm_snd_le p) (sq_nonneg _))
    _ = (‖z‖+‖z‖^2)*‖p‖ := by ring

section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma continuous_quadraticDerivative {h : Point d → E} (hh : Continuous h) :
    Continuous (quadraticDerivative h) :=
  isBoundedBilinearMap_smulRight.continuous.comp (continuous_quadraticLinear.prodMk hh)

lemma growth_quadraticDerivative {h : Point d → E} (hg : HasPolynomialGrowth h) :
    HasPolynomialGrowth (quadraticDerivative h) := by
  obtain ⟨C,hC,n,hn⟩ := hg
  refine ⟨4*C,by positivity,n+2,fun z => ?_⟩
  have hz := norm_nonneg z
  have hb : ‖quadraticDerivative h z‖  ≤  (‖z‖+‖z‖^2)*(C*(1+‖z‖^n)) := by
    rw [quadraticDerivative,ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (norm_quadraticLinear z) (hn z) (norm_nonneg _) (by positivity)
  by_cases h1 : ‖z‖ ≤ 1
  · have hp : ‖z‖^n ≤ 1 := pow_le_one₀ hz h1
    have h2 : ‖z‖^2 ≤ 1 := pow_le_one₀ hz h1
    calc
      _  ≤  (‖z‖+‖z‖^2)*(C*(1+‖z‖^n)) := hb
      _  ≤  2*(C*2) := mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left (by linarith) hC)
        (by positivity) (by norm_num)
      _  ≤  _ := by nlinarith [mul_nonneg hC (pow_nonneg hz (n+2))]
  · have h1' : 1 ≤ ‖z‖ := le_of_not_ge h1
    have he (k : ℕ) (hk : k ≤ n+2) : ‖z‖^k ≤ ‖z‖^(n+2) := pow_le_pow_right₀ h1' hk
    have hA := he 1 (by omega)
    have hB := he 2 (by omega)
    have hD := he (n+1) (by omega)
    simp only [pow_one] at hA
    calc
      _  ≤  (‖z‖+‖z‖^2)*(C*(1+‖z‖^n)) := hb
      _ = C*(‖z‖+‖z‖^2+‖z‖^(n+1)+‖z‖^(n+2)) := by
        simp only [pow_add,pow_one]; ring
      _  ≤  C*(4*‖z‖^(n+2)) := mul_le_mul_of_nonneg_left (by linarith) hC
      _  ≤  _ := by nlinarith

lemma integrable_quadraticTilt {H : Point d → ℝ} {h : Point d → E}
    (hH : Continuous H) (hh : Continuous h) {m C : ℝ}
    (ht : ∀ z, m*‖z‖^2 ≤ H z+C) (hg : HasPolynomialGrowth h)
    (p : Point d × ℝ) (hp : 0 < m+p.2) :
    Integrable (fun z => Real.exp (inner ℝ p.1 z-p.2*‖z‖^2-H z) • h z) := by
  have ht' : HasGaussianLowerTail (fun z => H z+p.2*‖z‖^2) :=
    ⟨m+p.2,hp,C,fun z => by nlinarith [ht z]⟩
  convert! integrable_tilted _ (hH.add (continuous_const.mul (continuous_norm.pow 2))) hh ht' hg p.1 using 1
  all_goals try with_reducible_and_instances rfl
  funext z; congr 2; dsimp; ring

lemma hasFDerivAt_quadraticTilt {H : Point d → ℝ} {h : Point d → E}
    (hH : Continuous H) (hh : Continuous h) {m C : ℝ}
    (ht : ∀ z, m*‖z‖^2 ≤ H z+C) (hg : HasPolynomialGrowth h)
    (p : Point d × ℝ) (hp : 0 < m+p.2) :
    HasFDerivAt (quadraticTilt H h) (quadraticTilt H (quadraticDerivative h) p) p := by
  let δ := (m+p.2)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let M := ‖p.1‖+1
  obtain ⟨K,hK,n,hg'⟩ := growth_quadraticDerivative hg
  let B := Real.exp (C+M^2/(2*δ))*K
  let b : Point d → ℝ := fun z => B*(Real.exp (-(δ/2)*‖z‖^2)+‖z‖^n*Real.exp (-(δ/2)*‖z‖^2))
  have hi : Integrable b := ((integrable_gaussian_envelope d (b:=δ/2) (by positivity)).add
    (integrable_norm_pow_gaussian d n (b:=δ/2) (by positivity))).const_mul B
  let U : Set (Point d × ℝ) := {q | ‖q.1‖ < M ∧ p.2-δ < q.2}
  have hopen : IsOpen U := (isOpen_lt (continuous_fst.norm) continuous_const).inter
    (isOpen_lt continuous_const continuous_snd)
  have hU : U∈nhds p := by
    apply hopen.mem_nhds
    change ‖p.1‖ < M ∧ p.2-δ < p.2
    exact ⟨by dsimp [M]; linarith,by linarith⟩
  have hd (z : Point d) (q : Point d × ℝ) :
      HasFDerivAt (fun t => Real.exp (inner ℝ t.1 z-t.2*‖z‖^2-H z) • h z)
        (Real.exp (inner ℝ q.1 z-q.2*‖z‖^2-H z) • quadraticDerivative h z) q := by
    have hh' := (((quadraticLinear z).hasFDerivAt (x:=q)).sub_const (H z)).exp.smul_const (h z)
    convert! hh' using 1
    · funext t; rw [quadraticLinear_apply]
    · apply ContinuousLinearMap.ext; intro t
      simp [quadraticDerivative,quadraticLinear_apply,smul_smul]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F':=fun q z => Real.exp (inner ℝ q.1 z-q.2*‖z‖^2-H z) • quadraticDerivative h z)
    (bound:=b) hU
  · exact Filter.Eventually.of_forall fun q =>
      ((Real.continuous_exp.comp (((continuous_const.inner continuous_id).sub
        (continuous_const.mul (continuous_norm.pow 2))).sub hH)).smul hh).aestronglyMeasurable
  · exact integrable_quadraticTilt hH hh ht hg p hp
  · exact (integrable_quadraticTilt hH (continuous_quadraticDerivative hh) ht
      (growth_quadraticDerivative hg) p hp).aestronglyMeasurable
  · filter_upwards [] with z q hq
    have ht' : ∀ z, δ*‖z‖^2 ≤ (H z+q.2*‖z‖^2)+C := by
      intro z
      have hq' : δ ≤ m+q.2 := by dsimp [U,δ] at *; linarith [hq.2]
      nlinarith [ht z,mul_nonneg (sub_nonneg.mpr hq') (sq_nonneg ‖z‖)]
    have he := mul_le_mul (gaussian_tilt_bound hδ (by dsimp [M]; positivity) ht' hq.1.le z)
      (hg' z) (norm_nonneg _) (by positivity)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    convert! he using 1
    · congr 2; ring
    · dsimp [b,B]; ring
  · exact hi
  · exact Filter.Eventually.of_forall fun z q _ => hd z q

theorem contDiffAt_quadraticTilt {H : Point d → ℝ} {h : Point d → E}
    (hH : Continuous H) (hh : Continuous h) {m C : ℝ}
    (ht : ∀ z, m*‖z‖^2 ≤ H z+C) (hg : HasPolynomialGrowth h)
    (p : Point d × ℝ) (hp : 0 < m+p.2) :
    ContDiffAt ℝ (⊤ : ℕ∞) (quadraticTilt H h) p := by
  apply contDiffAt_infty.mpr
  intro n
  induction n generalizing E h with
  | zero =>
    apply contDiffAt_zero.mpr
    refine ⟨{q | 0 < m+q.2},?_,fun q hq =>
      (hasFDerivAt_quadraticTilt hH hh ht hg q hq).continuousAt.continuousWithinAt⟩
    exact (isOpen_lt continuous_const (continuous_const.add continuous_snd)).mem_nhds hp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨quadraticTilt H (quadraticDerivative h),?_,ih
      (continuous_quadraticDerivative hh) (growth_quadraticDerivative hg)⟩
    refine ⟨{q | 0 < m+q.2},?_,fun q hq => hasFDerivAt_quadraticTilt hH hh ht hg q hq⟩
    exact (isOpen_lt continuous_const (continuous_const.add continuous_snd)).mem_nhds hp

end
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_QuadraticExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma integral_gibbs_vector {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Point d → ℝ} (hc : Continuous H) (hi : Integrable (fun z => Real.exp (-H z)))
    (h : Point d → E) : (∫ z,h z ∂gibbs H) = (∫ z,Real.exp (-H z))⁻¹ •
      ∫ z,Real.exp (-H z) • h z := by
  rw [gibbs,integral_smul_measure,ENNReal.toReal_inv,partition_toReal hi]
  have hden : Measurable (gibbsDensity H) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hden
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) h]
  simp only [gibbsDensity,ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma integral_gibbs_add_const_vector {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Point d → ℝ} (hc : Continuous H) (hi : Integrable (fun z => Real.exp (-H z)))
    (c : ℝ) (h : Point d → E) :
    (∫ z,h z ∂gibbs (fun z => H z+c))=∫ z,h z ∂gibbs H := by
  have he : (fun z => Real.exp (-(H z+c)))=fun z => Real.exp (-c)*Real.exp (-H z) := by
    funext z; rw [←Real.exp_add]; congr 1; ring
  have hi' : Integrable (fun z => Real.exp (-(H z+c))) := by rw [he]; exact hi.const_mul _
  rw [integral_gibbs_vector (hc.add_const c) hi',integral_gibbs_vector hc hi]
  simp_rw [congrFun he,mul_smul]
  rw [integral_const_mul,integral_smul,mul_inv_rev,smul_smul]
  simp only [mul_assoc,inv_mul_cancel₀ (Real.exp_pos (-c)).ne',mul_one]

def quadraticExpectation {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Point d → ℝ) (h : Point d → E) (p : Point d × ℝ) : E :=
  (quadraticTilt H (fun _ => (1:ℝ)) p)⁻¹ • quadraticTilt H h p

lemma quadratic_partition_pos {d : ℕ} {H : Point d → ℝ} (hc : Continuous H)
    {m C : ℝ} (ht : ∀ z,m*‖z‖^2 ≤ H z+C) (p : Point d × ℝ) (hp : 0 < m+p.2) :
    0 < quadraticTilt H (fun _ => (1:ℝ)) p := by
  simp only [quadraticTilt,smul_eq_mul,mul_one]
  apply integral_exp_pos
  simpa only [smul_eq_mul,mul_one] using
    integrable_quadraticTilt hc continuous_const ht (growth_const (1:ℝ)) p hp

lemma contDiffAt_quadraticExpectation {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Point d → ℝ} {h : Point d → E} (hc : Continuous H) (hh : Continuous h)
    {m C : ℝ} (ht : ∀ z,m*‖z‖^2 ≤ H z+C) (hg : HasPolynomialGrowth h)
    (p : Point d × ℝ) (hp : 0 < m+p.2) :
    ContDiffAt ℝ (⊤:ℕ∞) (quadraticExpectation H h) p :=
  ((contDiffAt_quadraticTilt hc continuous_const ht (growth_const (1:ℝ)) p hp).inv
    (quadratic_partition_pos hc ht p hp).ne').smul
    (contDiffAt_quadraticTilt hc hh ht hg p hp)

def conditionalParameter {d : ℕ} (p : ℝ × Point d) : Point d × ℝ :=
  ((p.1/(1-p.1^2)) • p.2,p.1^2/(2*(1-p.1^2)))

lemma conditionalPotential_quadratic {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y z : Point d) (hρ : ρ^2≠1) :
    conditionalPotential F x r ρ y z=
      (primitivePotential F x r z+(conditionalParameter (ρ,y)).2*‖z‖^2-
        inner ℝ (conditionalParameter (ρ,y)).1 z)+
          (ρ^2/(2*(1-ρ^2)))*‖y‖^2 := by
  have ha : 1-ρ^2≠0 := sub_ne_zero.mpr (Ne.symm hρ)
  simp only [conditionalPotential,conditionalParameter,primitivePotential,norm_sub_sq_real,
    inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    inner_smul_left,starRingEnd_apply,star_trivial]
  rw [real_inner_comm y z]
  field_simp
  ring

lemma conditional_integral_quadratic {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) (hρ : ρ^2 < 1) (y : Point d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : Point d → E) :
    (∫ z,h z ∂gibbs (conditionalPotential F x r ρ y))=
      quadraticExpectation (primitivePotential F x r) h (conditionalParameter (ρ,y)) := by
  let H := primitivePotential F x r
  let p := conditionalParameter (ρ,y)
  have hc : Continuous H := (hF.continuous_potential x r)
  obtain ⟨m,hm,C,ht⟩ := hF.hasGaussianLowerTail x hr hl
  have hp : 0 < m+p.2 := by dsimp [p,conditionalParameter]; positivity
  let G : Point d → ℝ := fun z => H z+p.2*‖z‖^2-inner ℝ p.1 z
  have hGc : Continuous G := by dsimp [G]; fun_prop
  have he : ∀ z,Real.exp (-G z)=Real.exp (inner ℝ p.1 z-p.2*‖z‖^2-H z) := by
    intro z; congr 1; dsimp [G]; ring
  have hGi : Integrable (fun z => Real.exp (-G z)) := by
    simp_rw [he]
    simpa only [smul_eq_mul,mul_one] using
      integrable_quadraticTilt hc continuous_const ht (growth_const (1:ℝ)) p hp
  have hpot : conditionalPotential F x r ρ y=fun z => G z+(ρ^2/(2*(1-ρ^2)))*‖y‖^2 :=
    funext fun z => conditionalPotential_quadratic F x r ρ y z hρ.ne
  rw [hpot,integral_gibbs_add_const_vector hGc hGi,integral_gibbs_vector hGc hGi]
  simp only [quadraticExpectation,quadraticTilt,smul_eq_mul,mul_one,he]
  rfl

lemma conditionalParameter_smooth {d : ℕ} {p : ℝ × Point d} (hp : p.1^2 < 1) :
    ContDiffAt ℝ (⊤:ℕ∞) (conditionalParameter (d:=d)) p := by
  have ha : 1-p.1^2≠0 := by linarith
  have hdiv : ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => q.1/(1-q.1^2)) p :=
    contDiffAt_fst.div (contDiffAt_const.sub (contDiffAt_fst.pow 2)) ha
  have hdiv' : ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => q.1^2/(2*(1-q.1^2))) p :=
    (contDiffAt_fst.pow 2).div (contDiffAt_const.mul (contDiffAt_const.sub (contDiffAt_fst.pow 2)))
      (mul_ne_zero (by norm_num) ha)
  exact (hdiv.smul contDiffAt_snd).prodMk hdiv'

theorem conditionalFieldMean_joint_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) (p : ℝ × Point d) (hp : p.1^2 < 1) :
    ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => conditionalFieldMean F x r q.1 q.2) p := by
  obtain ⟨m,hm,C,ht⟩ := hF.hasGaussianLowerTail x hr hl
  have hp' : 0 < m+(conditionalParameter p).2 := by dsimp [conditionalParameter]; positivity
  have hh := (contDiffAt_quadraticExpectation (hF.continuous_potential x r)
    (primitiveField_contDiff hF x r).continuous ht (growth_of_lipschitz (primitiveField_lipschitz hF x hr))
    (conditionalParameter p) hp').comp p (conditionalParameter_smooth hp)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt (continuous_fst.pow 2) continuous_const).mem_nhds hp] with q hq
  exact conditional_integral_quadratic hF x hr hl hq q.2 (primitiveField F x r)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Directional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open scoped RealInnerProductSpace
open MeasureTheory

def directional {d : ℕ} (v : Point d) (f : Point d → ℝ) : Point d → ℝ :=
  fun x => fderiv ℝ f x v

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_PolyC1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

structure PolyC1 {d : ℕ} (f : Point d → ℝ) : Prop where
  smooth : ContDiff ℝ 1 f
  growth : HasPolynomialGrowth f
  derivative_growth : ∀ v : Point d, HasPolynomialGrowth (directional v f)

def adjointCoordinate {d : ℕ} (H : Point d → ℝ) (v : Point d) (f : Point d → ℝ) : Point d → ℝ :=
  fun x => -directional v f x+directional v H x*f x

def tensorAdjoint {d : ℕ} {ι : Type*} [Fintype ι] (H : Point d → ℝ)
    (b : ι → Point d) (V : ι → Point d → ℝ) : Point d → ℝ :=
  fun x => ∑i,adjointCoordinate H (b i) (V i) x

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_JetNormalizedLaplaceMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Appell
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι : Type*} [DecidableEq ι]

lemma jet_normalizedLaplace_zero_moments {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {h : E → ℝ} (hh : Continuous h) (hg : HasGrowth h)
    (v : ι → E) (l : List ι) (hl : l.Nodup) :
    JetCalculus.jet v l (normalizedLaplace μ h) 0=
      ∑s∈l.toFinset.powerset,inverseMoment (moments μ (fun i z => inner ℝ (v i) z)) s*
        ∫z,(∏i∈l.toFinset\s,inner ℝ (v i) z)*h z ∂μ := by
  rw [jet_normalizedLaplace_zero hμ hh hg v l hl]
  simp only [polynomial,Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    rw [show (fun z => (inverseMoment (moments μ (fun i z => inner ℝ (v i) z)) s*
        ∏i∈l.toFinset\s,inner ℝ (v i) z)*h z)=
      fun z => inverseMoment (moments μ (fun i z => inner ℝ (v i) z)) s*
        ((∏i∈l.toFinset\s,inner ℝ (v i) z)*h z) by funext z; ring,
      integral_const_mul]
  · intro s _
    exact ((HasGrowth.const _).mul ((HasGrowth.prod (l.toFinset\s)
      (fun i _ => HasGrowth.linear (innerSL ℝ (v i)))))).mul hg |>.integrable
      (((continuous_const.mul (continuous_finsetProd _
        (fun i _ => continuous_const.inner continuous_id))).mul hh).aestronglyMeasurable) hμ.hasMoments

end LogConcaveSampling.Appell

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ConditionalPositionMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical BigOperators NNReal RealInnerProductSpace

namespace Appell
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [DecidableEq ι]

lemma inverseMoment_contDiffAt {m : E → Finset ι → ℝ} {p : E}
    (hm : ∀s,ContDiffAt ℝ (⊤:ℕ∞) (fun x => m x s) p) (s : Finset ι) :
    ContDiffAt ℝ (⊤:ℕ∞) (fun x => inverseMoment (m x) s) p := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s=∅
    · subst s
      simp only [inverseMoment_empty]
      exact contDiffAt_const
    simp_rw [inverseMoment_nonempty _ hs]
    apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro t ht
    exact (hm (s\t)).mul (ih t (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2,(Finset.mem_erase.mp ht).1⟩))

end Appell

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_InterpolationPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

def interpolationPotential {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y : Point d) : ℝ := ‖y‖^2/(2*(1-ρ^2))-
      Real.log (quadraticTilt (primitivePotential F x r) (fun _ => (1:ℝ))
        (conditionalParameter (ρ,y)))

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_AssignmentsFinset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace JetCalculus
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι κ N : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype N] [DecidableEq N]

lemma assignments_toFinset (n₀ : N) (l : List ι) (hl : l.Nodup)
    (hall : l.toFinset=Finset.univ) : (assignments n₀ l).toFinset=Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro p
  apply List.mem_toFinset.mpr (mem_assignments n₀ l hl p ?_)
  intro i hi
  exfalso
  exact hi (List.mem_toFinset.mp (by rw [hall]; exact Finset.mem_univ i))

lemma assignments_nodup (n₀ : N) (l : List ι) (hl : l.Nodup)
    (hall : l.toFinset=Finset.univ) : (assignments n₀ l).Nodup := by
  classical
  change (↑(assignments n₀ l) : Multiset (ι → N)).Nodup
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  change (assignments n₀ l).toFinset.card=(assignments n₀ l).length
  rw [assignments_toFinset n₀ l hl hall,Finset.card_univ,Fintype.card_fun,length_assignments]
  congr 1
  simpa only [hall,Finset.card_univ] using (List.toFinset_card_of_nodup hl)

lemma assignments_sum (n₀ : N) (l : List ι) (hl : l.Nodup)
    (hall : l.toFinset=Finset.univ) (f : (ι → N) → ℝ) :
    ((assignments n₀ l).map f).sum=∑ p, f p := by
  classical
  rw [← List.sum_toFinset _ (assignments_nodup n₀ l hl hall),
    assignments_toFinset n₀ l hl hall]

theorem jet_prod_sum {f : N → E → ℝ} (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (n₀ : N) (v : ι → E) (l : List ι) (hl : l.Nodup) (hall : l.toFinset=Finset.univ) :
    jet v l (fun x => ∏ n, f n x) = fun x =>
      ∑ p : ι → N, ∏ n, jet v (l.filter (fun i => p i=n)) (f n) x := by
  rw [jet_prod hf n₀ v l hl]
  funext x
  exact assignments_sum n₀ l hl hall _

omit [Fintype κ] [DecidableEq κ] in
lemma smooth_right_jet {f : E × F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (w : κ → F) (k : List κ) (ω : F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun θ => jet w k (fun ω => f (θ,ω)) ω) := by
  simp_rw [jet_right_slice hf]
  exact (smooth_jet hf _ k).comp (contDiff_id.prodMk contDiff_const)

theorem mixedJet_prod_sum {f : N → E × F → ℝ}
    (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n)) (n₀ : N)
    (v : ι → E) (w : κ → F) (l : List ι) (k : List κ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ) :
    mixedJet v w l k (fun x => ∏ n, f n x) =
      ∑ p : ι → N, ∑ q : κ → N,
        ∏ n, mixedJet v w (l.filter (fun i => p i=n)) (k.filter (fun j => q j=n)) (f n) := by
  unfold mixedJet
  have hr (θ : E) : jet w k (fun ω => ∏ n, f n (θ,ω)) = fun ω =>
      ∑ q : κ → N, ∏ n, jet w (k.filter (fun j => q j=n)) (fun ω => f n (θ,ω)) ω :=
    jet_prod_sum (fun n => (hf n).comp (contDiff_const.prodMk contDiff_id)) n₀ w k hk hkall
  simp_rw [hr]
  rw [jet_sum _ (fun q hq => contDiff_prod (fun n _ => smooth_right_jet (hf n) w _ 0))]
  have hleft (q : κ → N) : jet v l (fun θ => ∏ n,
      jet w (k.filter (fun j => q j=n)) (fun ω => f n (θ,ω)) 0) = fun θ =>
      ∑ p : ι → N, ∏ n, jet v (l.filter (fun i => p i=n))
        (fun θ => jet w (k.filter (fun j => q j=n)) (fun ω => f n (θ,ω)) 0) θ :=
    jet_prod_sum (fun n => smooth_right_jet (hf n) w _ 0) n₀ v l hl hlall
  simp_rw [hleft]
  exact Finset.sum_comm

end JetCalculus
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι ϑ κ N : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
  [Fintype κ] [DecidableEq κ] [Fintype N] [DecidableEq N]

omit [BorelSpace E] [SecondCountableTopology E] [DecidableEq κ] [Fintype N] in
lemma slotPolynomial_fiber (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (p : ι → N) (n : N) (x : E) :
    slotPolynomial μ b a (Finset.univ.filter (fun i => p i=n)) x =
      slotPolynomial μ b (fun j : {j : ι // p j=n} => a j) Finset.univ x := by
  have he : (Finset.univ : Finset {j : ι // p j=n}).image Subtype.val =
      Finset.univ.filter (fun j => p j=n) := by ext j; simp
  have hm : moments μ (fun j : {j : ι // p j=n} => coordinate b (a j)) =
      fun t => moments μ (fun j : ι => coordinate b (a j)) (t.image Subtype.val) := by
    funext t
    exact moments_image μ (fun j : ι => coordinate b (a j)) Subtype.val Subtype.val_injective t
  unfold slotPolynomial
  rw [hm]
  simpa only [Function.comp_def,he] using
    (polynomial_image (fun j : {j : ι // p j=n} => j.val) Subtype.val_injective
      (moments μ (fun j : ι => coordinate b (a j))) Finset.univ
      (fun j => coordinate b (a j) x)).symm

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Fintype N] in
lemma filter_nil_iff_card_fiber (l : List ι) (hall : l.toFinset=Finset.univ)
    (p : ι → N) (n : N) :
    l.filter (fun i => p i=n)=[] ↔ Fintype.card {i : ι // p i=n}=0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  · intro h
    refine ⟨fun i => ?_⟩
    have hi : i.val ∈ l := List.mem_toFinset.mp (by rw [hall]; exact Finset.mem_univ _)
    have hh : i.val ∈ l.filter (fun j => p j=n) := List.mem_filter.mpr ⟨hi,by simpa using i.prop⟩
    simp [h] at hh
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    have hh := (List.mem_filter.mp hi).2
    exact h.false ⟨i,by simpa using hh⟩

omit [DecidableEq κ] [Fintype N] in
lemma mixedJet_reduced_fibers {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) (l : List ι) (k : List ϑ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ)
    (p : ι → N) (q : ϑ → N) (n : N) :
    JetCalculus.mixedJet (fun i => b (a i)) (fun j => b (c j))
      (l.filter (fun i => p i=n)) (k.filter (fun j => q j=n)) (fun x => crossMGF μ x-1) =
      reducedCrossMoment μ b (fun i : {i : ι // p i=n} => a i)
        (fun j : {j : ϑ // q j=n} => c j) := by
  unfold reducedCrossMoment
  split_ifs with hempty
  · apply mixedJet_reduced_unmixed hμ
    simpa only [filter_nil_iff_card_fiber l hlall p n,
      filter_nil_iff_card_fiber k hkall q n] using hempty
  · rw [mixedJet_reduced hμ _ _ _ _ (hl.filter _) (hk.filter _)]
    · change (∫ x, slotPolynomial μ b a (l.filter (fun i => p i=n)).toFinset x *
        slotPolynomial μ b c (k.filter (fun j => q j=n)).toFinset x ∂μ)=_
      simp only [List.toFinset_filter,decide_eq_true_eq,hlall,hkall]
      simp only [slotPolynomial_fiber,crossMoment]
    · intro h
      apply hempty
      exact Or.inl ((filter_nil_iff_card_fiber l hlall p n).mp h.1)

omit [DecidableEq κ] in

lemma mixedJet_reduced_pow {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) (l : List ι) (k : List ϑ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ) (m : ℕ) :
    JetCalculus.mixedJet (fun i => b (a i)) (fun j => b (c j)) l k
      (fun x => (crossMGF μ x-1)^(m+1)) =
      ∑ p : ι → Fin (m+1), ∑ q : ϑ → Fin (m+1), crossBlockProduct μ b p q a c := by
  have hp : (fun x => (crossMGF μ x-1)^(m+1)) =
      (fun x => ∏ _i : Fin (m+1), (crossMGF μ x-1)) := by funext x; simp
  rw [hp,JetCalculus.mixedJet_prod_sum (fun _ => (smooth_crossMGF hμ).sub contDiff_const)
    (0 : Fin (m+1)) _ _ l k hl hlall hk hkall]
  simp only [crossBlockProduct,mixedJet_reduced_fibers hμ b a c l k hl hlall hk hkall]

omit [BorelSpace E] [SecondCountableTopology E] [DecidableEq κ] in
lemma mixedCumulant_eq_range (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) :
    mixedCumulant μ b a c =
      ∑ m ∈ Finset.range (Fintype.card ι+Fintype.card ϑ),
        ((-1:ℝ)^m/(m+1)) *
          (∑ p : ι → Fin (m+1), ∑ q : ϑ → Fin (m+1), crossBlockProduct μ b p q a c) := by
  unfold mixedCumulant
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type,← Finset.mul_sum]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,logCoefficient,Nat.cast_zero,div_zero,zero_mul,zero_add,Fin.val_succ]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  simp only [Nat.cast_add,Nat.cast_one,pow_succ]
  ring

omit [DecidableEq κ] in

lemma mixedJet_log_crossMGF {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) (l : List ι) (k : List ϑ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ) :
    JetCalculus.mixedJet (fun i => b (a i)) (fun j => b (c j)) l k
      (fun x => Real.log (crossMGF μ x)) = mixedCumulant μ b a c := by
  have hlc : l.length=Fintype.card ι := by
    rw [← List.toFinset_card_of_nodup hl,hlall,Finset.card_univ]
  have hkc : k.length=Fintype.card ϑ := by
    rw [← List.toFinset_card_of_nodup hk,hkall,Finset.card_univ]
  rw [JetCalculus.mixedJet_logTrunc (smooth_crossMGF hμ) (crossMGF_pos hμ)
    crossMGF_zero _ _ _ _ hl hk,hlc,hkc,mixedCumulant_eq_range]
  unfold JetCalculus.logTrunc
  rw [JetCalculus.mixedJet_sum _ (fun m _ => contDiff_const.mul
    (((smooth_crossMGF hμ).sub contDiff_const).pow _))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [JetCalculus.mixedJet_const_mul (((smooth_crossMGF hμ).sub contDiff_const).pow _),
    mixedJet_reduced_pow hμ b a c l k hl hlall hk hkall]

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace JetCalculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι κ : Type*}

lemma mixedJet_fst (f : E → ℝ) (v : ι → E) (w : κ → F) (l : List ι) (k : List κ)
    (hk : k≠[]) : mixedJet v w l k (fun x => f x.1)=0 := by
  simp only [mixedJet,jet_const,hk,↓reduceIte]
  split_ifs <;> rfl

lemma mixedJet_snd (f : F → ℝ) (v : ι → E) (w : κ → F) (l : List ι) (k : List κ)
    (hl : l≠[]) : mixedJet v w l k (fun x => f x.2)=0 := by
  simp only [mixedJet,jet_const,hl,↓reduceIte]

end JetCalculus
namespace Appell
open MeasureTheory

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι ϑ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
  [Fintype κ] [DecidableEq κ]

omit [SecondCountableTopology E] in
lemma log_crossMGF {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasExpMoments μ)
    (x : E × E) :
    Real.log (crossMGF μ x) =
      Real.log (laplace μ (fun _ => (1:ℝ)) (x.1+x.2)) -
        Real.log (laplace μ (fun _ => (1:ℝ)) x.1) -
        Real.log (laplace μ (fun _ => (1:ℝ)) x.2) := by
  rw [crossMGF,Real.log_mul (inv_ne_zero (laplace_one_pos hμ _).ne')
      (mul_ne_zero (inv_ne_zero (laplace_one_pos hμ _).ne') (laplace_one_pos hμ _).ne'),
    Real.log_mul (inv_ne_zero (laplace_one_pos hμ _).ne') (laplace_one_pos hμ _).ne',
    Real.log_inv,Real.log_inv]
  ring

omit [DecidableEq κ] in

theorem mixedJet_log_laplace {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) (l : List ι) (k : List ϑ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ)
    (hlne : l≠[]) (hkne : k≠[]) :
    JetCalculus.mixedJet (fun i => b (a i)) (fun j => b (c j)) l k
      (fun x => Real.log (laplace μ (fun _ => (1:ℝ)) (x.1+x.2))) =
      mixedCumulant μ b a c := by
  have hs := (contDiff_laplace hμ continuous_const (HasGrowth.const (1:ℝ))).log
    (fun θ => (laplace_one_pos hμ θ).ne')
  have hsA : ContDiff ℝ (⊤ : ℕ∞) (fun x : E × E =>
      Real.log (laplace μ (fun _ => (1:ℝ)) (x.1+x.2))) :=
    hs.comp (contDiff_fst.add contDiff_snd)
  have hsL : ContDiff ℝ (⊤ : ℕ∞) (fun x : E × E =>
      Real.log (laplace μ (fun _ => (1:ℝ)) x.1)) := hs.comp contDiff_fst
  have hsR : ContDiff ℝ (⊤ : ℕ∞) (fun x : E × E =>
      Real.log (laplace μ (fun _ => (1:ℝ)) x.2)) := hs.comp contDiff_snd
  have hh := mixedJet_log_crossMGF hμ b a c l k hl hlall hk hkall
  simp_rw [log_crossMGF hμ] at hh
  rw [JetCalculus.mixedJet_sub (hsA.sub hsL) hsR,
    JetCalculus.mixedJet_sub hsA hsL,
    JetCalculus.mixedJet_fst (fun θ => Real.log (laplace μ (fun _ => (1:ℝ)) θ)) _ _ _ _ hkne,
    JetCalculus.mixedJet_snd (fun θ => Real.log (laplace μ (fun _ => (1:ℝ)) θ)) _ _ _ _ hlne,
    sub_zero,sub_zero] at hh
  exact hh

theorem actual_cumulant_energy {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β)
    (b : OrthonormalBasis κ ℝ E) (l : List ι) (k : List ϑ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ)
    (hlne : l≠[]) (hkne : k≠[]) :
    TensorEnergy.Bound (fun (a : ι → κ) (c : ϑ → κ) =>
      JetCalculus.mixedJet (fun i => b (a i)) (fun j => b (c j)) l k
        (fun x => Real.log (laplace μ (fun _ => (1:ℝ)) (x.1+x.2))))
      (((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(2*(Fintype.card ι+Fintype.card ϑ+1)) *
        splitConstant β (Fintype.card ι) (Fintype.card ϑ)) := by
  simp_rw [mixedJet_log_laplace hμ b _ _ l k hl hlall hk hkall hlne hkne]
  exact mixedCumulant_energy μ hμ.hasMoments hβ hP b

end Appell
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.Appell
open MeasureTheory

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι ϑ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
  [Fintype κ]

theorem actual_jet_cumulant_energy {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {β : ℝ} (hβ : 0≤β) (hP : HasPoincare μ β)
    (b : OrthonormalBasis κ ℝ E) (l : List ι) (k : List ϑ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ)
    (hlne : l≠[]) (hkne : k≠[]) (o : List (ι ⊕ ϑ))
    (ho : o.Perm (l.map Sum.inl++k.map Sum.inr)) :
    TensorEnergy.Bound (fun (a : ι → κ) (c : ϑ → κ) =>
      JetCalculus.jet (Sum.elim (fun i => b (a i)) (fun j => b (c j))) o
        (fun θ => Real.log (laplace μ (fun _ => (1:ℝ)) θ)) 0)
      (((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(2*(Fintype.card ι+Fintype.card ϑ+1)) *
        splitConstant β (Fintype.card ι) (Fintype.card ϑ)) := by
  classical
  have hs := (contDiff_laplace hμ continuous_const (HasGrowth.const (1:ℝ))).log
    (fun θ => (laplace_one_pos hμ θ).ne')
  simp_rw [JetCalculus.jet_perm hs _ ho, ← JetCalculus.mixedJet_add hs]
  exact actual_cumulant_energy hμ hβ hP b l k hl hlall hk hkall hlne hkne

end LogConcaveSampling.Appell

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ConditionalSlotEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

def conditionalU {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y u : Point d) (L : ℝ) {ι : Type*} (v : ι → Point d) (l : List ι) : ℝ :=
  L/(1-ρ^2)^l.length * JetCalculus.jet (fun i => jointPosition d (v i)) l
    (JetCalculus.dir (jointField d u)
      (fun θ => Real.log (Appell.laplace (jointConditionalLaw F x r ρ y L)
        (fun _ => (1:ℝ)) θ))) 0

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityVelocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open Function Set
open scoped Topology

def probabilityVelocity {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y : Point d) : Point d := -r • conditionalFieldMean F x r ρ y

lemma probabilityVelocity_joint_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) (p : ℝ × Point d) (hp : p.1^2<1) :
    ContDiffAt ℝ (⊤:ℕ∞) (uncurry (probabilityVelocity F x r)) p := by
  change ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => (-r) • conditionalFieldMean F x r q.1 q.2) p
  exact (contDiffAt_const (c:=(-r:ℝ))).smul (conditionalFieldMean_joint_smooth hF x hr hl p hp)

lemma probabilityVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ : ρ∈Icc 0 T) (hT : T<1) :
    LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩ (probabilityVelocity F x r ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change ‖-r • conditionalFieldMean F x r ρ u- -r • conditionalFieldMean F x r ρ v‖≤((Real.pi^2/2)*(lam:ℝ)*r^2)*dist u v
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hr]
  have hh := (conditionalFieldMean_lipschitz hF x hr hl hρ.1 (hρ.2.trans_lt hT)).dist_le_mul u v
  rw [dist_eq_norm] at hh
  calc
    _ ≤ r*((Real.pi^2/2)*ρ*((lam:ℝ)*r)*dist u v) := mul_le_mul_of_nonneg_left hh hr
    _ ≤ r*((Real.pi^2/2)*1*((lam:ℝ)*r)*dist u v) := by gcongr; exact hρ.2.trans hT.le
    _ = _ := by ring

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TimeBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function Filter Metric
open scoped Topology NNReal

def timeBump {T : ℝ} (hT0 : 0≤T) (hT1 : T<1) : ContDiffBump (T/2) :=
  ⟨(T+1)/4,(3-T)/4,by linarith,by linarith⟩
def smoothTimeClip {T : ℝ} (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) : ℝ :=
  T/2+timeBump hT0 hT1 t*(t-T/2)
lemma smoothTimeClip_contDiff {T : ℝ} (hT0 : 0≤T) (hT1 : T<1) (n : ℕ) :
    ContDiff ℝ (n:WithTop ℕ∞) (smoothTimeClip hT0 hT1) :=
  contDiff_const.add ((timeBump hT0 hT1).contDiff.mul (contDiff_id.sub contDiff_const))
lemma smoothTimeClip_sq_lt {T : ℝ} (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) :
    (smoothTimeClip hT0 hT1 t)^2<1 := by
  have hb : |timeBump hT0 hT1 t*(t-T/2)|≤(3-T)/4 := by
    by_cases ht : (3-T)/4≤dist t (T/2)
    · rw [(timeBump hT0 hT1).zero_of_le_dist ht,zero_mul,abs_zero]
      linarith
    · have hd : |t-T/2|≤(3-T)/4 := by simpa only [Real.dist_eq] using (le_of_lt (lt_of_not_ge ht))
      rw [abs_mul,abs_of_nonneg (timeBump hT0 hT1).nonneg]
      exact (mul_le_of_le_one_left (abs_nonneg _) (timeBump hT0 hT1).le_one).trans hd
  have hh := abs_le.mp hb
  dsimp [smoothTimeClip]
  have h1 : -1<T/2+timeBump hT0 hT1 t*(t-T/2) := by linarith [hh.1]
  have h2 : T/2+timeBump hT0 hT1 t*(t-T/2)<1 := by linarith [hh.2]
  nlinarith

def smoothProbabilityVelocity {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    {T : ℝ} (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) (y : Point d) : Point d :=
  probabilityVelocity F x r (smoothTimeClip hT0 hT1 t) y

lemma smoothProbabilityVelocity_contDiff {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (n : ℕ) :
    ContDiff ℝ (n:WithTop ℕ∞) (uncurry (smoothProbabilityVelocity F x r hT0 hT1)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hv : ContDiffAt ℝ (n:WithTop ℕ∞) (uncurry (probabilityVelocity F x r))
      (smoothTimeClip hT0 hT1 p.1,p.2) :=
    (probabilityVelocity_joint_smooth hF x hr (by linarith)
      (smoothTimeClip hT0 hT1 p.1,p.2) (smoothTimeClip_sq_lt hT0 hT1 p.1)).of_le (WithTop.coe_le_coe.mpr le_top)
  exact hv.comp (f:=fun q : ℝ × Point d => (smoothTimeClip hT0 hT1 q.1,q.2)) p
    (((smoothTimeClip_contDiff hT0 hT1 n).comp contDiff_fst).prodMk contDiff_snd).contDiffAt

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped NNReal Topology

lemma conditionalFieldMean_neg_time {d : ℕ} (F : Point d → ℝ) (x : Point d) (r t : ℝ) (y : Point d) :
    conditionalFieldMean F x r (-t) y=conditionalFieldMean F x r t (-y) := by
  have he : conditionalPotential F x r (-t) y = conditionalPotential F x r t (-y) := by
    funext z
    simp [conditionalPotential, neg_smul, smul_neg]
  simp only [conditionalFieldMean, he]
lemma probabilityVelocity_neg_time {d : ℕ} (F : Point d → ℝ) (x : Point d) (r t : ℝ) (y : Point d) :
    probabilityVelocity F x r (-t) y=probabilityVelocity F x r t (-y) := by
  simp only [probabilityVelocity,conditionalFieldMean_neg_time]

lemma probabilityVelocity_lipschitz_signed {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ : ρ^2<1) :
    LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩ (probabilityVelocity F x r ρ) := by
  by_cases hp : 0≤ρ
  · exact probabilityVelocity_lipschitz hF x hr hl ⟨hp,le_rfl⟩ (by nlinarith)
  · have hn : 0≤-ρ := by linarith
    have hL := probabilityVelocity_lipschitz hF x hr hl ⟨hn,le_rfl⟩ (by nlinarith : -ρ<1)
    have he : probabilityVelocity F x r ρ=fun y => probabilityVelocity F x r (-ρ) (-y) := by
      funext y
      simpa only [neg_neg] using probabilityVelocity_neg_time F x r (-ρ) y
    rw [he]
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_neg_neg] using hL.dist_le_mul (-y) (-z)

lemma smoothProbabilityVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) :
    LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩
      (smoothProbabilityVelocity F x r hT0 hT1 t) :=
  probabilityVelocity_lipschitz_signed hF x hr hl (smoothTimeClip_sq_lt hT0 hT1 t)

lemma smoothProbabilityVelocity_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    ContDiff ℝ (⊤:ℕ∞) (uncurry (smoothProbabilityVelocity F x r hT0 hT1)) :=
  contDiff_infty.mpr (smoothProbabilityVelocity_contDiff hF x hr hl hT0 hT1)
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TerminalBackward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter
open scoped Topology NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

def terminalBackward (p : ℝ × Point d) : Point d :=
  GlobalODE.flow (a:= -1) (b:=T+1)
    (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1).continuous
    ⟨T,by constructor <;> linarith⟩ p.2 (smoothTimeClip hT0 hT1 p.1)

def terminalForward (p : ℝ × Point d) : Point d :=
  GlobalODE.flow (a:= -1) (b:=T+1)
    (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1).continuous
    (projIcc (-1) (T+1) (by linarith) (smoothTimeClip hT0 hT1 p.1)) p.2 T

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CoordinateRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter MeasureTheory
open scoped Topology NNReal RealInnerProductSpace

def coordinateRankOne (d : ℕ) (i j : Fin d) : Point d →L[ℝ] Point d :=
  (innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ j)).smulRight
    (EuclideanSpace.basisFun (Fin d) ℝ i)

def conditionalFirstJet {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (p : ℝ × Point d) : Point d →L[ℝ] Point d :=
  ∑i,∑j,conditionalU F x r p.1 p.2 (EuclideanSpace.basisFun (Fin d) ℝ i) L
    (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ j) [()] • coordinateRankOne d i j

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

def terminalJacobian (p : ℝ × Point d) : Point d →L[ℝ] Point d :=
  (fderiv ℝ (terminalForward hF x hr.le hl hT0 hT1)
    (smoothTimeClip hT0 hT1 p.1,terminalBackward hF x hr.le hl hT0 hT1 p)).comp
      (ContinuousLinearMap.inr ℝ ℝ (Point d))

def steinIntegrand (p : ℝ × Point d) : Point d →L[ℝ] Point d :=
  (terminalJacobian hF x hr hl hT0 hT1 p).comp
    (conditionalFirstJet F x r ((lam:ℝ)*r)
      (smoothTimeClip hT0 hT1 p.1,terminalBackward hF x hr.le hl hT0 hT1 p))

def centeringKernel (y : Point d) : Point d →L[ℝ] Point d :=
  (∫ρ in Icc 0 T,steinIntegrand hF x hr hl hT0 hT1 (ρ,y)).adjoint

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_Vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

section
namespace LogConcaveSampling.AdjointRemoval
variable {P : Type*} [Fintype P] [DecidableEq P]

structure Hessian (P : Type*) where
  first : P
  second : P
  extra : List P
  deriving DecidableEq

def Hessian.degree (h : Hessian P) : ℕ := h.extra.length+2

def Hessian.hit (h : Hessian P) (i : P) : Hessian P :=
  ⟨h.first,h.second,i::h.extra⟩

structure State (P : Type*) [DecidableEq P] where
  pending : Finset P
  derivatives : P → List P
  hessians : Multiset (Hessian P)

def State.degree (S : State P) : ℕ :=
  S.pending.card+(∑j,(S.derivatives j).length)+(S.hessians.map Hessian.degree).sum

def initial : State P := ⟨Finset.univ,fun _ => [],0⟩

def hitPrimary (S : State P) (i j : P) : State P :=
  ⟨S.pending.erase i,Function.update S.derivatives j (i::S.derivatives j),S.hessians⟩

def pair (S : State P) (i j : P) : State P :=
  ⟨(S.pending.erase i).erase j,S.derivatives,⟨i,j,[]⟩::ₘS.hessians⟩

def hitHessian (S : State P) (i : P) (h : Hessian P) : State P :=
  ⟨S.pending.erase i,S.derivatives,h.hit i::ₘS.hessians.erase h⟩

inductive Step : State P → State P → Prop
  | primary (S : State P) (i j : P) (hi : i∈S.pending) (hij : i≠j) : Step S (hitPrimary S i j)
  | pair (S : State P) (i j : P) (hi : i∈S.pending) (hj : j∈S.pending) (hij : i≠j) : Step S (pair S i j)
  | hessian (S : State P) (i : P) (h : Hessian P) (hi : i∈S.pending) (hh : h∈S.hessians) :
      Step S (hitHessian S i h)

omit [Fintype P] in
lemma Step.pending_lt {S T : State P} (h : Step S T) : T.pending.card<S.pending.card := by
  cases h with
  | primary i j hi hij => exact Finset.card_erase_lt_of_mem hi
  | pair i j hi hj hij =>
    exact (Finset.card_erase_le).trans_lt (Finset.card_erase_lt_of_mem hi)
  | hessian i h hi hh => exact Finset.card_erase_lt_of_mem hi

def State.good (S : State P) : Prop :=
  (∀j i,i∈S.derivatives j → i≠j) ∧ ∀h∈S.hessians,h.first≠h.second

lemma initial_good : (initial (P:=P)).good := by simp [State.good,initial]

omit [Fintype P] in
lemma Step.good {S T : State P} (ht : Step S T) (hS : S.good) : T.good := by
  cases ht with
  | primary i j hi hij =>
    constructor
    · intro k a ha
      change a∈Function.update S.derivatives j (i::S.derivatives j) k at ha
      by_cases hk : k=j
      · subst k
        simp only [Function.update_self,List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact hij
        · exact hS.1 j a ha
      · rw [Function.update_of_ne hk] at ha
        exact hS.1 k a ha
    · exact hS.2
  | pair i j hi hj hij =>
    refine ⟨hS.1,?_⟩
    intro h hh
    change h∈(⟨i,j,[]⟩:Hessian P)::ₘS.hessians at hh
    rcases Multiset.mem_cons.mp hh with he | hh
    · subst h; exact hij
    · exact hS.2 h hh
  | hessian i h hi hh =>
    refine ⟨hS.1,?_⟩
    intro g hg
    change g∈h.hit i::ₘS.hessians.erase h at hg
    rcases Multiset.mem_cons.mp hg with he | hg
    · subst g; exact hS.2 h hh
    · exact hS.2 g (Multiset.mem_of_mem_erase hg)

theorem reachable_good {S : State P} (h : Relation.ReflTransGen Step initial S) : S.good := by
  induction h with
  | refl => exact initial_good
  | tail hstep h ih => exact h.good ih

def branches (S : State P) (i : P) : List (State P) :=
  ((Finset.univ.erase i).toList.map (hitPrimary S i))++
  ((S.pending.erase i).toList.map (pair S i))++
  (S.hessians.toList.map (hitHessian S i))

lemma branches_step (S : State P) {i : P} (hi : i∈S.pending) {T : State P}
    (hT : T∈branches S i) : Step S T := by
  simp only [branches,List.mem_append,List.mem_map] at hT
  rcases hT with (⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩) | ⟨h,hh,rfl⟩
  · have hj' := Finset.mem_erase.mp (Finset.mem_toList.mp hj)
    exact Step.primary S i j hi hj'.1.symm
  · have hj' := Finset.mem_erase.mp (Finset.mem_toList.mp hj)
    exact Step.pair S i j hi hj'.2 hj'.1.symm
  · exact Step.hessian S i h hi (Multiset.mem_toList.mp hh)

def expand : ℕ → State P → List (State P)
  | 0,S => [S]
  | n+1,S => if hp : S.pending.Nonempty then
      (branches S (Classical.choose hp)).flatMap (expand n)
    else [S]

lemma mem_expand_reachable {n : ℕ} {S T : State P} (h : T∈expand n S) :
    Relation.ReflTransGen Step S T := by
  induction n generalizing S with
  | zero =>
    simp only [expand,List.mem_singleton] at h
    subst T
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [expand] at h
    split_ifs at h with hp
    · obtain ⟨U,hU,hT⟩ := List.mem_flatMap.mp h
      exact (Relation.ReflTransGen.single (branches_step S (Classical.choose_spec hp) hU)).trans (ih hT)
    · simp only [List.mem_singleton] at h
      subst T
      exact Relation.ReflTransGen.refl

lemma mem_expand_terminal {n : ℕ} {S T : State P} (hn : S.pending.card≤n)
    (h : T∈expand n S) : T.pending=∅ := by
  induction n generalizing S with
  | zero =>
    simp only [expand,List.mem_singleton] at h
    subst T
    exact Finset.card_eq_zero.mp (by omega)
  | succ n ih =>
    simp only [expand] at h
    split_ifs at h with hp
    · obtain ⟨U,hU,hT⟩ := List.mem_flatMap.mp h
      have hh := (branches_step S (Classical.choose_spec hp) hU).pending_lt
      exact ih (by omega) hT
    · simp only [List.mem_singleton] at h
      subst T
      exact Finset.not_nonempty_iff_eq_empty.mp hp

end LogConcaveSampling.AdjointRemoval

end
end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_Inside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped RealInnerProductSpace NNReal

variable {d : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

def inside (b : P → Point d) (f : P → Point d → ℝ) (S : State P) (j : P) : Point d → ℝ :=
  JetCalculus.jet b (S.derivatives j) (f j)

def primary (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) (j : P) : Point d → ℝ :=
  if j∈S.pending then adjointCoordinate H (b j) (inside b f S j) else inside b f S j

def hessian (H : Point d → ℝ) (b : P → Point d) (h : Hessian P) : Point d → ℝ :=
  JetCalculus.jet b h.extra (directional (b h.first) (directional (b h.second) H))

def term (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) (x : Point d) : ℝ :=
  (∏j,primary H b f S j x)*(S.hessians.map (fun h => hessian H b h x)).prod

structure Regular (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (K : ℝ≥0) : Prop where
  smooth_H : ContDiff ℝ (⊤ : ℕ∞) H
  tail : HasGaussianLowerTail H
  lipschitz : LipschitzWith K (gradient H)
  smooth_f : ∀j,ContDiff ℝ (⊤ : ℕ∞) (f j)
  primary_jets : ∀j l,PolyC1 (JetCalculus.jet b l (f j))
  hessian_jets : ∀h : Hessian P,PolyC1 (hessian H b h)

end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_AdjointMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval
variable {P : Type*} [Fintype P] [DecidableEq P]

def Hessian.tokens (h : Hessian P) : Multiset P :=
  h.first::ₘh.second::ₘ(h.extra : Multiset P)

def State.tokens (S : State P) : Multiset P :=
  S.pending.val+(∑p,(S.derivatives p : Multiset P))+
    (S.hessians.map Hessian.tokens).sum

lemma initial_tokens : (initial (P:=P)).tokens=Finset.univ.val := by
  simp [State.tokens,initial]

lemma hitPrimary_tokens (S : State P) {i j : P} (hi : i∈S.pending) :
    (hitPrimary S i j).tokens=S.tokens := by
  have he : (∑k,(Function.update S.derivatives j (i::S.derivatives j) k : Multiset P))=
      i::ₘ(∑k,(S.derivatives k : Multiset P)) := by
    have hl : (fun k => (Function.update S.derivatives j (i::S.derivatives j) k : Multiset P))=
        Function.update (fun k => (S.derivatives k : Multiset P)) j (i::ₘ(S.derivatives j : Multiset P)) := by
      funext k
      by_cases hk : k=j
      · subst k; simp
      · simp [Function.update_of_ne hk]
    rw [hl,Finset.sum_update_of_mem (Finset.mem_univ j),Finset.sdiff_singleton_eq_erase]
    rw [←Finset.add_sum_erase Finset.univ (fun k => (S.derivatives k : Multiset P)) (Finset.mem_univ j)]
    simp only [Multiset.cons_add]
  have hp : i::ₘ(S.pending.erase i).val=S.pending.val := by
    exact Multiset.cons_erase hi
  simp only [State.tokens,hitPrimary,he]
  rw [Multiset.add_cons,←Multiset.cons_add,hp]

lemma pair_tokens (S : State P) {i j : P} (hi : i∈S.pending) (hj : j∈S.pending) (hij : i≠j) :
    (pair S i j).tokens=S.tokens := by
  have hj' : j∈S.pending.erase i := Finset.mem_erase.mpr ⟨hij.symm,hj⟩
  have hp : i::ₘj::ₘ((S.pending.erase i).erase j).val=S.pending.val := by
    rw [show j::ₘ((S.pending.erase i).erase j).val=(S.pending.erase i).val from Multiset.cons_erase hj']
    exact Multiset.cons_erase hi
  simp only [State.tokens,pair,Multiset.map_cons,Multiset.sum_cons,Hessian.tokens,Multiset.coe_nil]
  rw [Multiset.cons_add,Multiset.cons_add,zero_add,Multiset.add_cons,Multiset.add_cons,
    ←Multiset.cons_add,←Multiset.cons_add,←Multiset.cons_add,←Multiset.cons_add,hp]

lemma hitHessian_tokens (S : State P) {i : P} (hi : i∈S.pending)
    {h : Hessian P} (hh : h∈S.hessians) : (hitHessian S i h).tokens=S.tokens := by
  have hm := congrArg (fun t : Multiset (Hessian P) => (t.map Hessian.tokens).sum)
    (Multiset.cons_erase hh)
  simp only [Multiset.map_cons,Multiset.sum_cons] at hm
  have hp : i::ₘ(S.pending.erase i).val=S.pending.val := Multiset.cons_erase hi
  have hh' : (h.hit i).tokens=i::ₘh.tokens := by
    simp only [Hessian.tokens,Hessian.hit,←Multiset.cons_coe]
    rw [Multiset.cons_swap h.second i,Multiset.cons_swap h.first i]
  simp only [State.tokens,hitHessian,Multiset.map_cons,Multiset.sum_cons,hh']
  rw [Multiset.cons_add,hm,Multiset.add_cons,←Multiset.cons_add,←Multiset.cons_add,hp]

lemma Step.tokens {S T : State P} (h : Step S T) : T.tokens=S.tokens := by
  cases h with
  | primary i j hi hij => exact hitPrimary_tokens S hi
  | pair i j hi hj hij => exact pair_tokens S hi hj hij
  | hessian i h hi hh => exact hitHessian_tokens S hi hh

theorem mem_expand_tokens {n : ℕ} {S : State P}
    (hS : S∈expand n initial) : S.tokens=Finset.univ.val := by
  have hr := mem_expand_reachable hS
  clear hS
  have he : S.tokens=(initial (P:=P)).tokens := by
    induction hr with
    | refl => rfl
    | tail hr ht ih => exact ht.tokens.trans ih
  exact he.trans initial_tokens

theorem terminal_ports {S : State P} (hS : S∈expand (Fintype.card P) initial) :
    (∑p,(S.derivatives p : Multiset P))+(S.hessians.map Hessian.tokens).sum=Finset.univ.val := by
  have he := mem_expand_tokens hS
  have ht := mem_expand_terminal (by simp [initial]) hS
  simpa only [State.tokens,ht,Finset.empty_val,zero_add] using he
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
variable {P : Type*} [Fintype P] [DecidableEq P]

abbrev TargetVertex (S : State P) := P ⊕ S.hessians

def ports (S : State P) : TargetVertex S → Multiset P
  | Sum.inl p => (S.derivatives p : Multiset P)
  | Sum.inr h => (h : Hessian P).tokens

lemma sum_ports (S : State P) : (∑v,ports S v)=
    (∑p,(S.derivatives p : Multiset P))+(S.hessians.map Hessian.tokens).sum := by
  rw [Fintype.sum_sum_type]
  congr 1
  change (Finset.univ.val.map (fun h : S.hessians => (h : Hessian P).tokens)).sum=_
  rw [Multiset.map_univ]

abbrev Port (S : State P) := (v : TargetVertex S) × ports S v

def portLabel (S : State P) (p : Port S) : P := p.2

theorem portLabel_bijective {S : State P} (hS : S∈expand (Fintype.card P) initial) :
    Function.Bijective (portLabel S) := by
  have hs : (∑v,ports S v)=Finset.univ.val := (sum_ports S).trans (terminal_ports hS)
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro i
    have hi : i∈∑v,ports S v := by rw [hs]; exact Finset.mem_univ i
    obtain ⟨v,_,hv⟩ := Multiset.mem_sum.mp hi
    refine ⟨⟨v,(ports S v).mkToType i ⟨0,Multiset.count_pos.mpr hv⟩⟩,rfl⟩
  · simp only [Port,Fintype.card_sigma,Multiset.card_coe]
    rw [←Multiset.card_sum,hs]
    rfl

noncomputable def portEquiv {S : State P} (hS : S∈expand (Fintype.card P) initial) :
    Port S ≃ P := Equiv.ofBijective (portLabel S) (portLabel_bijective hS)

noncomputable def destination {S : State P} (hS : S∈expand (Fintype.card P) initial)
    (i : P) : TargetVertex S := ((portEquiv hS).symm i).1

lemma destination_label {S : State P} (hS : S∈expand (Fintype.card P) initial)
    (p : Port S) : destination hS (portLabel S p)=p.1 := by
  exact congrArg Sigma.fst ((portEquiv hS).symm_apply_apply p)

lemma label_mem_destination {S : State P} (hS : S∈expand (Fintype.card P) initial)
    (i : P) : i∈ports S (destination hS i) := by
  have hp := @Multiset.coe_mem P _ (ports S (destination hS i)) (((portEquiv hS).symm i).2)
  change portLabel S ((portEquiv hS).symm i)∈_ at hp
  change portEquiv hS ((portEquiv hS).symm i)∈_ at hp
  simpa only [Equiv.apply_symm_apply] using hp

lemma destination_primary_ne {S : State P} (hS : S∈expand (Fintype.card P) initial)
    {i j : P} (h : destination hS i=Sum.inl j) : i≠j := by
  have hi := label_mem_destination hS i
  rw [h] at hi
  exact (reachable_good (mem_expand_reachable hS)).1 j i hi

end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
variable {n : ℕ} {S : State (Fin (n+1))}

def Adjacent (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (u v : TargetVertex S) : Prop :=
  (∃k : Fin n,(u=Sum.inl k.castSucc ∧ v=Sum.inl k.succ) ∨
    (v=Sum.inl k.castSucc ∧ u=Sum.inl k.succ)) ∨
  (∃i : Fin (n+1),(u=Sum.inl i ∧ v=destination hS i) ∨
    (v=Sum.inl i ∧ u=destination hS i))

end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_ColoringSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval
open scoped BigOperators Classical

variable {X P Z W : Type*}

def coloringSplit : (((X ⊕ P) ⊕ Z) → W) ≃ (((X ⊕ Z) → W) × (P → W)) where
  toFun c := (fun t => match t with
    | Sum.inl x => c (Sum.inl (Sum.inl x))
    | Sum.inr z => c (Sum.inr z),fun p => c (Sum.inl (Sum.inr p)))
  invFun c t := match t with
    | Sum.inl (Sum.inl x) => c.1 (Sum.inl x)
    | Sum.inl (Sum.inr p) => c.2 p
    | Sum.inr z => c.1 (Sum.inr z)
  left_inv c := by
    funext t
    rcases t with (x|p)|z <;> rfl
  right_inv c := by
    apply Prod.ext
    · funext t
      cases t <;> rfl
    · rfl

end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

abbrev Edge (q : ℕ) := U ⊕ (Fin q ⊕ Fin q)

def emit (_first last : V) (q : ℕ) : Edge (U:=U) q → ℕ
  | Sum.inl e => min (key (src e)+1) (key (dst e)+1)
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr _) => key last+1

end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.AdjointRemoval
variable {n : ℕ} {S : State (Fin (n+1))}

abbrev InternalEdge (β : Fin n → ℕ) := ((k : Fin n) × Fin (β k)) ⊕ Fin (n+1)

def edgeSource (β : Fin n → ℕ) : InternalEdge β → TargetVertex S
  | Sum.inl e => Sum.inl e.1.castSucc
  | Sum.inr i => Sum.inl i

def edgeTarget (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) : InternalEdge β → TargetVertex S
  | Sum.inl e => Sum.inl e.1.succ
  | Sum.inr i => destination hS i

end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U C : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

def duplicate {q : ℕ} (c : U ⊕ Fin q → C) : Edge (U:=U) q → C
  | Sum.inl u => c (Sum.inl u)
  | Sum.inr (Sum.inl i) => c (Sum.inr i)
  | Sum.inr (Sum.inr i) => c (Sum.inr i)

end LogConcaveSampling.GraphSchedule

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_RankEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

def IncidentAt (first last v : V) (q : ℕ) : Edge (U:=U) q → Prop
  | Sum.inl u => src u=v ∨ dst u=v
  | Sum.inr (Sum.inl _) => first=v
  | Sum.inr (Sum.inr _) => last=v

end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.AdjointRemoval
open scoped BigOperators

variable {P : Type*} [Fintype P] [DecidableEq P] {S : State P}

lemma destination_iff_mem (hS : S∈expand (Fintype.card P) initial)
    (i : P) (v : TargetVertex S) : destination hS i=v ↔ i∈ports S v := by
  constructor
  · intro h
    simpa only [h] using label_mem_destination hS i
  · intro h
    let p : ports S v := (ports S v).mkToType i ⟨0,Multiset.count_pos.mpr h⟩
    exact destination_label hS ⟨v,p⟩

lemma ports_nodup (hS : S∈expand (Fintype.card P) initial) (v : TargetVertex S) :
    (ports S v).Nodup := by
  have hs : (∑v,ports S v)=Finset.univ.val := (sum_ports S).trans (terminal_ports hS)
  have hv := Finset.single_le_sum (s:=Finset.univ) (f:=ports S)
    (fun _ _ => Multiset.zero_le _) (Finset.mem_univ v)
  rw [hs] at hv
  exact Multiset.nodup_of_le hv (Finset.univ : Finset P).nodup

lemma derivatives_nodup (hS : S∈expand (Fintype.card P) initial) (i : P) :
    (S.derivatives i).Nodup := ports_nodup hS (Sum.inl i)

noncomputable def derivativeEdgeEquiv (hS : S∈expand (Fintype.card P) initial) (i : P) :
    Fin (S.derivatives i).length ≃ {j : P // destination hS j=Sum.inl i} :=
  (List.Nodup.getEquiv (S.derivatives i) (derivatives_nodup hS i)).trans
    (Equiv.subtypeEquivRight (fun j => (destination_iff_mem hS j (Sum.inl i)).symm))

lemma hessian_slots_nodup (hS : S∈expand (Fintype.card P) initial) (h : S.hessians) :
    ((h : Hessian P).first::(h : Hessian P).second::(h : Hessian P).extra).Nodup :=
  ports_nodup hS (Sum.inr h)

noncomputable def hessianEdgeEquiv (hS : S∈expand (Fintype.card P) initial) (h : S.hessians) :
    Fin ((h : Hessian P).first::(h : Hessian P).second::(h : Hessian P).extra).length ≃
      {j : P // destination hS j=Sum.inr h} :=
  (List.Nodup.getEquiv _ (hessian_slots_nodup hS h)).trans
    (Equiv.subtypeEquivRight (fun j => (destination_iff_mem hS j (Sum.inr h)).symm))

end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_IncidentMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory GraphSchedule TensorEnergy
open scoped BigOperators Classical ENNReal

variable {n : ℕ} {S : State (Fin (n+1))}
local instance cutDecEqAT (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (InternalEdge β ⊕ Fin q) :=
  @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)

end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_HessianIncidenceTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule
open scoped Classical

variable {n d : ℕ} {S : State (Fin (n+1))}

noncomputable def hessianIncidenceTensor
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (h : S.hessians) (x : Point d)
    (a : {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inr h) q t} → Fin d) : ℝ :=
  hessian H (fun i => if hi : destination hS i=Sum.inr h then
    b (a ⟨Sum.inl (Sum.inr i),Or.inr hi⟩) else 0) h x

end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule
open scoped Classical

variable {n d : ℕ} {S : State (Fin (n+1))}

abbrev TraceEdge (β : Fin n → ℕ) (q : ℕ) :=
  ((k : Fin n) × Fin (β k)) ⊕ (Fin q ⊕ Fin q)

def traceEmbed (β : Fin n → ℕ) (q : ℕ) : TraceEdge β q → Edge (U:=InternalEdge β) q
  | Sum.inl e => Sum.inl (Sum.inl e)
  | Sum.inr e => Sum.inr e

abbrev PrimaryTraceSlot
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :=
  {t : TraceEdge β q //
    IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
      (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inl i) q (traceEmbed β q t)}

noncomputable def primaryIncidenceTensor
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (i : Fin (n+1))
    (F : (PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ) (x : Point d)
    (a : {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inl i) q t} → Fin d) : ℝ :=
  JetCalculus.jet (fun j => if hj : destination hS j=Sum.inl i then
    b (a ⟨Sum.inl (Sum.inr j),Or.inr hj⟩) else 0) (S.derivatives i)
      (F (fun t => a ⟨traceEmbed β q t.val,t.property⟩)
        (a ⟨Sum.inl (Sum.inr i),Or.inl rfl⟩)) x

end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy MeasureTheory
open scoped BigOperators Classical ENNReal

variable {n d : ℕ} {S : State (Fin (n+1))}
local instance cutDecEqBT (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (InternalEdge β ⊕ Fin q) :=
  @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)

noncomputable def branchIncidenceTensor
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ)
    (x : Point d) (v : TargetVertex S) :
    ({t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) v q t} → Fin d) → ℝ :=
  match v with
  | Sum.inl i => primaryIncidenceTensor hS β q b i (F i) x
  | Sum.inr h => hessianIncidenceTensor hS β q H b h x

end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule
open scoped Classical

variable {n : ℕ} {S : State (Fin (n+1))}

noncomputable def primaryIncidentCases
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :
    {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inl i) q t} ≃
      PrimaryTraceSlot hS β q i ⊕ (Unit ⊕ {j : Fin (n+1) // destination hS j=Sum.inl i}) where
  toFun t := by
    rcases t with ⟨(e|j)|e,ht⟩
    · exact Sum.inl ⟨Sum.inl e,ht⟩
    · by_cases hj : j=i
      · exact Sum.inr (Sum.inl ())
      · exact Sum.inr (Sum.inr ⟨j,ht.resolve_left (fun h => hj (Sum.inl.inj h))⟩)
    · exact Sum.inl ⟨Sum.inr e,ht⟩
  invFun t := by
    rcases t with t | (u | j)
    · exact ⟨traceEmbed β q t.val,t.property⟩
    · exact ⟨Sum.inl (Sum.inr i),Or.inl rfl⟩
    · exact ⟨Sum.inl (Sum.inr j.val),Or.inr j.property⟩
  left_inv t := by
    rcases t with ⟨(e|j)|e,ht⟩
    · rfl
    · dsimp only
      split_ifs with hj
      · subst j; rfl
      · rfl
    · rfl
  right_inv t := by
    rcases t with ⟨e|e,ht⟩ | (u | ⟨j,hj⟩)
    · rfl
    · rfl
    · cases u
      dsimp only
      simp only [dite_true]
    · dsimp only
      rw [dite_eq_right (destination_primary_ne hS hj)]

noncomputable def primarySlotEquiv
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :
    (PrimaryTraceSlot hS β q i ⊕ (Unit ⊕ Fin (S.derivatives i).length)) ≃
      {t : Edge (U:=InternalEdge β) q //
        IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
          (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inl i) q t} :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) (derivativeEdgeEquiv hS i))).trans
    (primaryIncidentCases hS β q i).symm

end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_HessianIncidentEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule
open scoped Classical

variable {n : ℕ} {S : State (Fin (n+1))}

noncomputable def hessianIncidentEquiv
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (h : S.hessians) :
    {t : Edge (U:=InternalEdge β) q //
      IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
        (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inr h) q t} ≃
      {i : Fin (n+1) // destination hS i=Sum.inr h} where
  toFun t := by
    rcases t with ⟨(⟨k,j⟩|i)|(a|a),ht⟩
    · simp only [IncidentAt,edgeSource,edgeTarget,Sum.inl_ne_inr,or_self] at ht
    · exact ⟨i,ht.resolve_left (Sum.inl_ne_inr)⟩
    · exact False.elim (Sum.inl_ne_inr ht)
    · exact False.elim (Sum.inl_ne_inr ht)
  invFun i := ⟨Sum.inl (Sum.inr i.val),Or.inr i.property⟩
  left_inv t := by
    rcases t with ⟨(⟨k,j⟩|i)|(a|a),ht⟩
    · simp only [IncidentAt,edgeSource,edgeTarget,Sum.inl_ne_inr,or_self] at ht
    · rfl
    · exact False.elim (Sum.inl_ne_inr ht)
    · exact False.elim (Sum.inl_ne_inr ht)
  right_inv i := rfl

noncomputable def hessianSlotEquiv
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (h : S.hessians) :
    Fin ((h : Hessian (Fin (n+1))).first::(h : Hessian (Fin (n+1))).second::
      (h : Hessian (Fin (n+1))).extra).length ≃
      {t : Edge (U:=InternalEdge β) q //
        IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
          (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inr h) q t} :=
  (hessianEdgeEquiv hS h).trans (hessianIncidentEquiv hS β q h).symm

end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_PrimaryPositionTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy
open scoped Classical

variable {n d : ℕ} {S : State (Fin (n+1))}

noncomputable def primaryPositionTensor
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (i : Fin (n+1))
    (F : (PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ) (x : Point d)
    (a : PrimaryTraceSlot hS β q i ⊕ (Unit ⊕ Fin (S.derivatives i).length) → Fin d) : ℝ :=
  JetCalculus.jet (fun k => b (a (Sum.inr (Sum.inr k))))
    (List.finRange (S.derivatives i).length)
    (F (fun t => a (Sum.inl t)) (a (Sum.inr (Sum.inl ())))) x

end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy
open scoped Classical

variable {n d : ℕ} {S : State (Fin (n+1))}

def hessianPositionList {P : Type*} (h : Hessian P) : List P :=
  h.first::h.second::h.extra

noncomputable def hessianPositionTensor
    (H : Point d → ℝ) (b : Fin d → Point d) (h : Hessian (Fin (n+1))) (x : Point d)
    (a : Fin (h.first::h.second::h.extra).length → Fin d) : ℝ :=
  JetCalculus.jet (fun k : Fin h.extra.length => b (a ⟨k.val+2,by simp only [List.length_cons]; omega⟩))
    (List.finRange h.extra.length)
    (directional (b (a ⟨0,by simp⟩)) (directional (b (a ⟨1,by simp⟩)) H)) x

end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy MeasureTheory
open scoped BigOperators Classical ENNReal

variable {n d : ℕ} {S : State (Fin (n+1))}
local instance cutDecEqPB (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (InternalEdge β ⊕ Fin q) :=
  @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)

end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open GraphSchedule TensorEnergy MeasureTheory
open scoped BigOperators Classical ENNReal

variable {n d : ℕ} {S : State (Fin (n+1))}
local instance cutDecEqQB (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (InternalEdge β ⊕ Fin q) :=
  @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)

end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_Chain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory GraphSchedule
open scoped BigOperators Classical NNReal

variable {n d : ℕ}
local instance cutDecEqCB (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (InternalEdge β ⊕ Fin q) :=
  @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)

def onChain (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) : TraceEdge β q → Prop
  | Sum.inl e => e.1.castSucc=i ∨ e.1.succ=i
  | Sum.inr (Sum.inl _) => 0=i
  | Sum.inr (Sum.inr _) => Fin.last n=i

abbrev ChainSlot (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :=
  {t : TraceEdge β q // onChain β q i t}

lemma onChain_iff_incident {S : State (Fin (n+1))}
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) (t : TraceEdge β q) :
    onChain β q i t ↔ IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
      (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inl i) q (traceEmbed β q t) := by
  rcases t with e | (j | j) <;>
    simp only [onChain, traceEmbed, IncidentAt, edgeSource, edgeTarget, Sum.inl.injEq]

def chainSlotEquiv {S : State (Fin (n+1))}
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :
    ChainSlot β q i ≃ PrimaryTraceSlot hS β q i where
  toFun t := ⟨t.val,(onChain_iff_incident hS β q i t.val).mp t.property⟩
  invFun t := ⟨t.val,(onChain_iff_incident hS β q i t.val).mpr t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def closeTrace (β : Fin n → ℕ) (q : ℕ) :
    TraceEdge β q → ((k : Fin n) × Fin (β k)) ⊕ Fin q
  | Sum.inl e => Sum.inl e
  | Sum.inr (Sum.inl j) => Sum.inr j
  | Sum.inr (Sum.inr j) => Sum.inr j

abbrev TraceColors (β : Fin n → ℕ) (q d : ℕ) :=
  (((k : Fin n) × Fin (β k)) ⊕ Fin q) → Fin d

abbrev FullColors (β : Fin n → ℕ) (q d : ℕ) :=
  InternalEdge β ⊕ Fin q → Fin d

def chainField (β : Fin n → ℕ) (q : ℕ)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (t : TraceColors β q d) (i : Fin (n+1)) (z : Fin d) : Point d → ℝ :=
  F i (fun u => t (closeTrace β q u.val)) z

def chainBranch (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (S : State (Fin (n+1))) (x : Point d) : ℝ :=
  ∑c : FullColors β q d,
    (∏i,JetCalculus.jet (fun j => b (c (Sum.inl (Sum.inr j)))) (S.derivatives i)
      (F i (fun u => duplicate c (traceEmbed β q u.val)) (c (Sum.inl (Sum.inr i)))) x)*
    (S.hessians.map (fun h => hessian H (fun j => b (c (Sum.inl (Sum.inr j)))) h x)).prod

open TensorEnergy
open scoped ENNReal

def chainPositionTensor (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d)
    (i : Fin (n+1))
    (F : (ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (j : ℕ) (x : Point d)
    (a : ChainSlot β q i ⊕ (Unit ⊕ Fin j) → Fin d) : ℝ :=
  JetCalculus.jet (fun k => b (a (Sum.inr (Sum.inr k)))) (List.finRange j)
    (F (fun t => a (Sum.inl t)) (a (Sum.inr (Sum.inl ())))) x

end LogConcaveSampling.AdjointRemoval

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open scoped BigOperators

abbrev Primary (s : ℕ) := Fin ((2*s+1)+1)

def bundle {s : ℕ} (a b : ℕ) (k : Fin (2*s+1)) : ℕ :=
  if k.val%2=0 then b else a

abbrev Wire (s a b : ℕ) := ((k : Fin (2*s+1)) × Fin (bundle a b k)) ⊕ Fin a
abbrev CycleWire (s a b : ℕ) := (Fin (s+1) × Fin a) ⊕ (Fin (s+1) × Fin b)

lemma row_index_lt {s : ℕ} (t : Fin (s+1)) (_ht : t.val≠0) : 2*t.val-1<2*s+1 := by
  omega
lemma col_index_lt {s : ℕ} (t : Fin (s+1)) : 2*t.val<2*s+1 := by omega

lemma col_bundle {s : ℕ} (a b : ℕ) (t : Fin (s+1)) :
    bundle a b ⟨2*t.val,col_index_lt t⟩ = b := by simp [bundle]

end LogConcaveSampling.CycleTrace

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]

def advance {n : ℕ} (t : Fin (n+1)) : Fin (n+1) :=
  if h : t.val+1<n+1 then ⟨t.val+1,h⟩ else 0

def closedWeight (A : Matrix I J ℝ) {n : ℕ}
    (r : Fin (n+1) → I) (c : Fin (n+1) → J) : ℝ :=
  ∏t,A (r t) (c t)*A (r (advance t)) (c t)

end LogConcaveSampling.CycleTrace

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open AdjointRemoval
open scoped Classical BigOperators

variable {s a b : ℕ}

lemma right_row_lt (t : Fin (s+1)) (ht : t.val≠s) : 2*t.val+1<2*s+1 := by omega

end LogConcaveSampling.CycleTrace

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open AdjointRemoval MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {s a b d : ℕ}

abbrev RowColors (s a d : ℕ) := Fin (s+1) → Fin a → Fin d

def adjointMatrix (H : Point d → ℝ) (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ) (x : Point d) :
    Matrix (Fin a → Fin d) (Fin b → Fin d) ℝ :=
  fun r c => tensorAdjoint H v (F (Sum.elim r c)) x

end LogConcaveSampling.CycleTrace

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PrimitiveExpectedField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

def primitiveExpectedField {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) : Point d :=
  ∫z,primitiveField F x r z ∂gibbs (primitivePotential F x r)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CoordinateProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Function
open scoped Classical BigOperators
open TensorEnergy

def coordinateProjection {d D : ℕ} (e : Fin d ↪ Fin D) : Point D →L[ℝ] Point d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => PiLp.proj 2 (fun _ : Fin D => ℝ) (e i)))

@[simp] lemma coordinateProjection_apply {d D : ℕ} (e : Fin d ↪ Fin D)
    (y : Point D) (i : Fin d) : coordinateProjection e y i=y (e i) := rfl

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators RealInnerProductSpace

def productPointEquiv (d e : ℕ) : Point (d+e) ≃L[ℝ] Point d × Point e :=
  EuclideanSpace.finAddEquivProd

def productPotential {d e : ℕ} (H : Point d → ℝ) (G : Point e → ℝ)
    (y : Point (d+e)) : ℝ := H (productPointEquiv d e y).1+G (productPointEquiv d e y).2

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_IterTensorLie
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

def skewLieField {d : ℕ} (H : Point d → ℝ)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (y : Point d) : Point d :=
  ∑z : Fin d,(∑i : Fin d,adjointCoordinate H (EuclideanSpace.basisFun (Fin d) ℝ i)
    (A (Sum.elim (fun _ => i) (fun _ => z))) y) • EuclideanSpace.basisFun (Fin d) ℝ z

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TensorVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

def jointSkewEntry {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ)
    (i z : Fin (d+d)) (y : Point (d+d)) : ℝ :=
  s⁻¹ * Fin.addCases
    (fun a => Fin.addCases (fun _ => 0) (fun b =>
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ b)
        (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ a))) z)
    (fun a => Fin.addCases (fun b =>
      -inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ a)
        (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ b))) (fun _ => 0) z) i

def jointSkew {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ)
    (c : Unit ⊕ Unit → Fin (d+d)) : Point (d+d) → ℝ :=
  jointSkewEntry K s (c (.inl ())) (c (.inr ()))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def basis (u : I → ℝ) (i : I) (t : ℝ) : ℝ :=
  (Lagrange.basis Finset.univ u i).eval t

def weight (u : I → ℝ) (i : I) (a b : ℝ) : ℝ := ∫t in a..b,basis u i t

end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_CenteringPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

def centeringPotential {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ) : Point (d+d) → ℝ :=
  productPotential (interpolationPotential F x r T) (fun z : Point d => ‖z‖^2/2)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Correction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.FinitePicard
open scoped NNReal BigOperators

variable {I E X : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoMetricSpace X]

def correction (w : I → I → ℝ) (φ : I → E → E) (z : I → E) : I → E :=
  fun i => ∑j,w i j • φ j (z j)

def step (w : I → I → ℝ) (φ : I → E → E) (a z : I → E) : I → E :=
  a+correction w φ z

def nodes (w : I → I → ℝ) (φ : I → E → E) (a : X → I → E) : ℕ → X → I → E
  | 0 => a
  | n+1 => fun x => step w φ (a x) (nodes w φ a n x)

end LogConcaveSampling.FinitePicard

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_LogMeshLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Real

def logMeshLength (T : ℝ) : ℝ := -Real.log (1-T)
def logMeshCount (T h : ℝ) : ℕ := ⌈logMeshLength T/h⌉₊
def logMeshStep (T h : ℝ) : ℝ := logMeshLength T/(logMeshCount T h:ℝ)
def logMeshNode (T h : ℝ) (j : ℕ) : ℝ := 1-Real.exp (-(j:ℝ)*logMeshStep T h)

lemma logMeshLength_pos {T : ℝ} (hT0 : 0<T) (hT1 : T<1) : 0<logMeshLength T := by
  dsimp [logMeshLength]
  exact neg_pos.mpr (Real.log_neg (by linarith) (by linarith))

lemma logMeshCount_pos {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    0<logMeshCount T h := by
  have hp := div_pos (logMeshLength_pos hT0 hT1) hh
  have he := Nat.le_ceil (logMeshLength T/h)
  have hc : (0:ℝ)<logMeshCount T h := hp.trans_le he
  exact_mod_cast hc

@[simp] lemma logMeshNode_zero (T h : ℝ) : logMeshNode T h 0=0 := by
  simp [logMeshNode]

end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CompositeAngle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def compositeAngle {N : ℕ} (u : I → ℝ) (i : Fin N × I) (c : Fin N) : ℝ :=
  if c < i.1 then 1 else if c = i.1 then u i.2 else 0

def compositeWeight {N : ℕ} (u : I → ℝ) (ℓ : Fin N → ℝ)
    (i j : Fin N × I) : ℝ := ℓ j.1*weight u j.2 0 (compositeAngle u i j.1)

end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}

def derivativeWeight (u : I → ℝ) (i : I) : ℝ :=
  (Lagrange.basis Finset.univ u i).derivative.eval 0

def derivativeStencil (u : I → ℝ) (ψ : ℝ) (v : I → E) : E :=
  ∑i,(derivativeWeight u i/ψ) • v i

end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AngleNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

def angleNodes (n : ℕ) (i : Fin (n+1)) : ℝ := (i:ℝ)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def probabilityNodes (n : ℕ) (i : Fin (n+1)) : ℝ := (i:ℝ)/(n:ℝ)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

abbrev ProbabilityNode (T h : ℝ) (n : ℕ) := Fin (logMeshCount T h) × Fin (n+1)

def probabilityCellLength (T h : ℝ) (c : Fin (logMeshCount T h)) : ℝ :=
  logMeshNode T h (c.val+1)-logMeshNode T h c.val

def probabilityNodeTime (T h : ℝ) (n : ℕ) (i : ProbabilityNode T h n) : ℝ :=
  logMeshNode T h i.1.val+probabilityCellLength T h i.1*probabilityNodes n i.2

def probabilityWeight (T h : ℝ) (n : ℕ) : ProbabilityNode T h n → ProbabilityNode T h n → ℝ :=
  compositeWeight (probabilityNodes n) (probabilityCellLength T h)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

def probabilityMeanVelocity {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r t : ℝ) (y : Point d) : Point d := -r • conditionalFieldMean F x r t y

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

def harmonicWeight (n : ℕ) (z : ℝ) (i j : Fin (n+1)) : ℝ :=
  z*(∫v in 0..probabilityNodes n i,
    Real.sin (z*(probabilityNodes n i-v))*basis (probabilityNodes n) j v)

def harmonicFree {d : ℕ} (n : ℕ) (z : ℝ) (p : Point d × Point d) : Fin (n+1) → Point d :=
  fun i => Real.cos (z*probabilityNodes n i) • p.1+Real.sin (z*probabilityNodes n i) • p.2

def harmonicMeanVelocity {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ) (y : Point d) : Point d :=
  ρ • probabilityMeanVelocity F x r ρ y

def harmonicPicard {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ z : ℝ) (n N : ℕ) :
    Point d × Point d → Fin (n+1) → Point d :=
  nodes (harmonicWeight n z) (fun _ => harmonicMeanVelocity F x r ρ) (harmonicFree n z) N

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ReanchorWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.FinitePicard
open MeasureTheory
open scoped BigOperators

variable {I E Ω : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

def reanchorWeight (w : I → I → ℝ) (s : I) : I → I → ℝ := fun i j => w i j-w s j

end LogConcaveSampling.FinitePicard

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory FinitePicard
open scoped Classical BigOperators NNReal

def probabilityAnchoredPicard {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h : ℝ) (n N : ℕ) (s : ProbabilityNode T h n) :
    Point d → ProbabilityNode T h n → Point d :=
  nodes (reanchorWeight (probabilityWeight T h n) s)
    (fun j => probabilityMeanVelocity F x r (probabilityNodeTime T h n j)) (fun y _ => y) N

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_KernelTransportAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

def kernelActionPicard {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h ψ : ℝ) (n m N : ℕ) (s e : ProbabilityNode T h n)
    (p : Point d × Point d) : Point d :=
  derivativeStencil (angleNodes m) ψ (fun i =>
    let b := probabilityAnchoredPicard F x r T h n N e p.1 s
    let w := harmonicPicard F x r (probabilityNodeTime T h n s)
      (ψ*angleNodes m i) n N (b,p.2) (Fin.last n)
    probabilityAnchoredPicard F x r T h n (N+1) s w e-w)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set Quadrature

def probabilityEndpoint {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) (n : ℕ) :
    ProbabilityNode T h n :=
  (⟨logMeshCount T h-1,by have := logMeshCount_pos hT0 hT1 hh; omega⟩,Fin.last n)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelActionRmsBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def kernelQuadraturePicard {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h ψ : ℝ) (n m N : ℕ) (e : ProbabilityNode T h n)
    (w : ProbabilityNode T h n → ℝ) (p : Point d × Point d) : Point d :=
  ∑s,w s • kernelActionPicard F x r T h ψ n m N s e p

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Program
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LogConcaveSampling.OracleCompiler

structure Program (Ω : Type*) [MeasurableSpace Ω] (d q : ℕ)
    (O : Type*) [MeasurableSpace O] where
  query : Fin q → Ω × Transcript d q → Point d
  query_measurable : ∀ i, Measurable (query i)
  output : Ω × Transcript d q → O
  output_measurable : Measurable output

namespace Program
variable {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O] {d q : ℕ}

def history (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω) : ℕ → Transcript d q
  | 0 => 0
  | n + 1 =>
      let h := A.history V ω n
      if hn : n < q then
        Function.update h ⟨n, hn⟩ (firstOrderReply V (A.query ⟨n, hn⟩ (ω, h)))
      else h

def run (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω) : O :=
  A.output (ω, A.history V ω q)

end Program
end LogConcaveSampling.OracleCompiler

namespace LogConcaveSampling.OracleCompiler.Program
variable {Ω O R : Type*} [MeasurableSpace Ω] [MeasurableSpace O] [MeasurableSpace R]
  {d q r : ℕ}

def leftTrace (h : Transcript d (q+r)) : Transcript d q := fun i => h (Fin.castAdd r i)
def rightTrace (h : Transcript d (q+r)) : Transcript d r := fun i => h (Fin.natAdd q i)

@[simp] lemma leftTrace_append (h : Transcript d q) (k : Transcript d r) :
    leftTrace (Fin.append h k) = h := by
  funext i
  simp [leftTrace]
@[simp] lemma rightTrace_append (h : Transcript d q) (k : Transcript d r) :
    rightTrace (Fin.append h k) = k := by
  funext i
  simp [rightTrace]

def pure (f : Ω → O) (hf : Measurable f) : Program Ω d 0 O where
  query i := Fin.elim0 i
  query_measurable i := Fin.elim0 i
  output p := f p.1
  output_measurable := hf.comp measurable_fst

@[simp] lemma pure_run (f : Ω → O) (hf : Measurable f) (V : Point d → ℝ) (ω : Ω) :
    (pure (d:=d) f hf).run V ω = f ω := rfl

end LogConcaveSampling.OracleCompiler.Program

end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_Squared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped Classical

variable {X Ω Γ : Type*} [PseudoMetricSpace X] [SeparableSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω] [MeasurableSpace Γ]

def SquaredAt {d : ℕ} (μ : Measure Ω) (ν : Measure Γ)
    (f : Ω → Point d) (g : Γ → Point d) (B : ℝ) : Prop :=
  ∃κ : Measure (Ω × Γ),IsProbabilityMeasure κ ∧ κ.fst=μ ∧ κ.snd=ν ∧
    Integrable (fun z => ‖f z.1-g z.2‖^2) κ ∧ (∫z,‖f z.1-g z.2‖^2 ∂κ)≤B

end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
  [StandardBorelSpace B] [Nonempty B]

def lift (ν : Measure Ω) (κ : Measure (A × B)) [IsFiniteMeasure κ]
    (T : Ω → A) (hT : Measurable T) : Measure (Ω × B) :=
  ν ⊗ₘ κ.condKernel.comap T hT

instance lift_probability (ν : Measure Ω) [IsProbabilityMeasure ν]
    (κ : Measure (A × B)) [IsProbabilityMeasure κ] (T : Ω → A) (hT : Measurable T) :
    IsProbabilityMeasure (lift ν κ T hT) := by unfold lift; infer_instance

end LogConcaveSampling.Coupling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_DistanceCoupled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical

variable {E : Type*} [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

def DistanceCoupled (μ ν : Measure E) (R : ℝ) : Prop :=
  ∃κ : Measure (E×E),IsProbabilityMeasure κ ∧ κ.fst=μ ∧ κ.snd=ν ∧
    ∀ᵐ z ∂κ,dist z.1 z.2≤R

end LogConcaveSampling.Coupling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_NodePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def zeroNodePolynomial (u : I → ℝ) (i₀ : I) : ℝ[X] :=
  X*∏i∈Finset.univ.erase i₀,(X-C (u i))

def zeroHermiteBasis (u : I → ℝ) (i₀ i : I) : ℝ[X] :=
  Lagrange.basis Finset.univ u i-
    C (derivativeWeight u i/(zeroNodePolynomial u i₀).derivative.eval 0)*zeroNodePolynomial u i₀

def zeroHermiteRegularized (u : I → ℝ) (i₀ i : I) : ℝ[X] :=
  (zeroHermiteBasis u i₀ i).derivative.divX

def zeroHermiteWeight (u : I → ℝ) (i₀ i : I) : ℝ :=
  ∫z in (0:ℝ)..1,(zeroHermiteRegularized u i₀ i).eval z

end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_BasisDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def basisDerivative (u : I → ℝ) (i : I) (t : ℝ) : ℝ :=
  (Lagrange.basis Finset.univ u i).derivative.eval t

end LogConcaveSampling.Quadrature

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_OrdinaryDerivativeWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Filter
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def ordinaryDerivativeWeight (u : I → ℝ) (a b : ℝ) (i : I) : ℝ :=
  ∫t in a..b,(b-a)⁻¹*t⁻¹*basisDerivative u i ((t-a)/(b-a))

end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

def terminalQuadratureWeight (T h : ℝ) (n : ℕ) (i : ProbabilityNode T h (n+1)) : ℝ :=
  if i.1.val=0 then
    zeroHermiteWeight (probabilityNodes (n+1)) 0 i.2/probabilityCellLength T h i.1
  else ordinaryDerivativeWeight (probabilityNodes (n+1))
    (logMeshNode T h i.1.val) (logMeshNode T h (i.1.val+1)) i.2

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CenteringVelocityPicard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def centeringVelocityPicard {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h ψ s : ℝ) (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (p : Point d × Point d) : Point d × Point d :=
  (-(r*s)⁻¹ • kernelQuadraturePicard F x r T h ψ (n+1) m N e
      (terminalQuadratureWeight T h n) p,
    s⁻¹ • (conditionalFieldMean F x r T p.1-primitiveExpectedField F x r))

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CenteringVelocityJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal

def centeringVelocityJoint {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h ψ s : ℝ) (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (y : Point (d+d)) : Point (d+d) :=
  (productPointEquiv d d).symm
    (centeringVelocityPicard F x r T h ψ s n m N e (productPointEquiv d d y))

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_StationaryPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal

structure StationaryPath {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (V : E → E) where
  path : E → ℝ → E
  continuous : ∀y,Continuous (path y)
  initial : ∀y,path y 0=y
  derivative : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (path y) (V (path y t)) (Icc (0:ℝ) 1) t
  measurable : Measurable (fun p : ℝ × E => path p.2 p.1)
  law : ∀t∈Icc (0:ℝ) 1,μ.map (fun y => path y t)=μ

def centeringWeight (n : ℕ) (i j : Fin (n+1)) : ℝ :=
  weight (probabilityNodes n) j 0 (probabilityNodes n i)

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CenteringStateQuadratureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsFiniteMeasure μ] {V Vhat : E → E}

def stationaryPicard (n N : ℕ) (Vhat : E → E) (y : E) (i : Fin (n+1)) : E :=
  FinitePicard.nodes (centeringWeight n) (fun _ => Vhat) (fun y _ => y) N y i

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_MeanTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal

inductive MeanTree (X : Type*) [MeasurableSpace X] (d : ℕ) where
  | node (k : ℕ) (base : X → Point d) (measurable_base : Measurable base)
      (coeff scale : Fin k → ℝ) (center : Fin k → MeanTree X d)

namespace MeanTree
variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def eval (F : Point d → ℝ) : MeanTree X d → X → Point d
  | .node _ b _ a r E,z => b z+∑i,a i • primitiveExpectedField F (eval F (E i) z) (r i)

def depth : MeanTree X d → ℕ
  | .node _ _ _ _ _ E => Finset.univ.sup (fun i => depth (E i)+1)

def weight : MeanTree X d → ℝ
  | .node _ _ _ a _ _ => ∑i,|a i|

def anchor (b : X → Point d) (hb : Measurable b) : MeanTree X d :=
  .node 0 b hb Fin.elim0 Fin.elim0 Fin.elim0

def zero : MeanTree X d := anchor (fun _ => 0) measurable_const

def scale (s : ℝ) : MeanTree X d → MeanTree X d
  | .node k b hb a r E => .node k (fun z => s • b z) (by fun_prop) (fun i => s*a i) r E

def add : MeanTree X d → MeanTree X d → MeanTree X d
  | .node k b hb a r E,.node l c hc v t D =>
    .node (k+l) (fun z => b z+c z) (by fun_prop)
      (Fin.addCases a v) (Fin.addCases r t) (Fin.addCases E D)

def mean (r : ℝ) (E : MeanTree X d) : MeanTree X d :=
  .node 1 (fun _ => 0) measurable_const (fun _ => 1) (fun _ => r) (fun _ => E)

@[simp] theorem eval_anchor (F : Point d → ℝ) (b : X → Point d) (hb : Measurable b) (z : X) :
    eval F (anchor b hb) z=b z := by simp [eval,anchor]
@[simp] theorem eval_zero (F : Point d → ℝ) (z : X) : eval F zero z=0 := by simp [zero]
@[simp] theorem eval_scale (F : Point d → ℝ) (s : ℝ) (E : MeanTree X d) (z : X) :
    eval F (scale s E) z=s • eval F E z := by
  cases E
  simp only [eval,scale,smul_add,Finset.smul_sum,smul_smul]
@[simp] theorem eval_add (F : Point d → ℝ) (E D : MeanTree X d) (z : X) :
    eval F (add E D) z=eval F E z+eval F D z := by
  cases E; cases D
  simp only [eval,add,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]
  abel
@[simp] theorem eval_mean (F : Point d → ℝ) (r : ℝ) (E : MeanTree X d) (z : X) :
    eval F (mean r E) z=primitiveExpectedField F (eval F E z) r := by
  simp [mean,eval]

@[simp] theorem depth_anchor (b : X → Point d) (hb : Measurable b) : depth (anchor b hb)=0 := by
  simp [anchor,depth]
@[simp] theorem depth_zero : depth (zero : MeanTree X d)=0 := by simp [zero]
@[simp] theorem depth_scale (s : ℝ) (E : MeanTree X d) : depth (scale s E)=depth E := by
  cases E; rfl
@[simp] theorem depth_mean (r : ℝ) (E : MeanTree X d) : depth (mean r E)=depth E+1 := by
  simp [mean,depth]

def sumFin : (k : ℕ) → (Fin k → MeanTree X d) → MeanTree X d
  | 0,_ => zero
  | k+1,E => add (E 0) (sumFin k (fun i => E i.succ))

@[simp] lemma eval_sumFin (F : Point d → ℝ) (k : ℕ) (E : Fin k → MeanTree X d) (z : X) :
    eval F (sumFin k E) z=∑i,eval F (E i) z := by
  induction k with
  | zero => simp [sumFin]
  | succ k ih => simp only [sumFin,eval_add,ih,Fin.sum_univ_succ]

def sumFamily {I : Type*} [Fintype I] (E : I → MeanTree X d) : MeanTree X d :=
  sumFin (Fintype.card I) (fun i => E ((Fintype.equivFin I).symm i))

@[simp] lemma eval_sumFamily {I : Type*} [Fintype I] (F : Point d → ℝ)
    (E : I → MeanTree X d) (z : X) :
    eval F (sumFamily E) z=∑i,eval F (E i) z := by
  rw [sumFamily,eval_sumFin]
  exact (Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl))

def conditional (r ρ : ℝ) (x y : MeanTree X d) : MeanTree X d :=
  mean (r*Real.sqrt (1-ρ^2)) (add x (scale (r*ρ) y))

end MeanTree
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CenteringMeanCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

def centeringMeanCircuit {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h ψ s : ℝ) (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (y : Point (d+d)) : Point d :=
  s • (productPointEquiv d d y).2+
    ∑j,weight (probabilityNodes nc) j 0 1 • conditionalFieldMean F x r T
      (productPointEquiv d d (stationaryPicard nc Nc
        (centeringVelocityJoint F x r T h ψ s n m N e) y j)).1

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Picard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def base : MeanTree X d → X → Point d
  | .node _ b .. => b

@[simp] lemma base_anchor (b : X → Point d) (hb : Measurable b) : base (anchor b hb)=b := rfl
@[simp] lemma base_zero : base (zero : MeanTree X d)=fun _ => 0 := rfl
@[simp] lemma base_scale (s : ℝ) (E : MeanTree X d) : base (scale s E)=fun z => s • base E z := by cases E; rfl
@[simp] lemma base_add (E D : MeanTree X d) : base (add E D)=fun z => base E z+base D z := by cases E; cases D; rfl
@[simp] lemma base_mean (r : ℝ) (E : MeanTree X d) : base (mean r E)=fun _ => 0 := rfl
@[simp] lemma base_conditional (r ρ : ℝ) (x y : MeanTree X d) : base (conditional r ρ x y)=fun _ => 0 := rfl

@[simp] lemma base_sumFin (k : ℕ) (E : Fin k → MeanTree X d) :
    base (sumFin k E)=fun z => ∑i,base (E i) z := by
  induction k with
  | zero => funext z; simp [sumFin]
  | succ k ih => funext z; simp [sumFin,ih,Fin.sum_univ_succ]

@[simp] lemma base_sumFamily {I : Type*} [Fintype I] (E : I → MeanTree X d) :
    base (sumFamily E)=fun z => ∑i,base (E i) z := by
  funext z
  simp only [sumFamily,base_sumFin]
  exact Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)

def centers (P : ℝ → (X → Point d) → Prop) : MeanTree X d → Prop
  | .node _ _ _ _ r C => ∀i,P (r i) (base (C i)) ∧ centers P (C i)

@[simp] lemma centers_anchor (P : ℝ → (X → Point d) → Prop) (b : X → Point d) (hb : Measurable b) :
    centers P (anchor b hb) := by intro i; exact Fin.elim0 i
@[simp] lemma centers_zero (P : ℝ → (X → Point d) → Prop) : centers P (zero : MeanTree X d) := centers_anchor _ _ _
@[simp] lemma centers_scale (P : ℝ → (X → Point d) → Prop) (s : ℝ) (E : MeanTree X d) :
    centers P (scale s E)↔centers P E := by cases E; rfl
@[simp] lemma centers_add (P : ℝ → (X → Point d) → Prop) (E D : MeanTree X d) :
    centers P (add E D)↔centers P E ∧ centers P D := by
  cases E with | node k b hb a r C =>
    cases D with | node l c hc v t B =>
      simp only [centers,add]
      constructor
      · intro h
        constructor
        · intro i
          simpa only [Fin.addCases_left] using h (Fin.castAdd l i)
        · intro i
          simpa only [Fin.addCases_right] using h (Fin.natAdd k i)
      · rintro ⟨h₁,h₂⟩ i
        exact Fin.addCases (fun j => by simpa only [Fin.addCases_left] using h₁ j)
          (fun j => by simpa only [Fin.addCases_right] using h₂ j) i

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

@[simp] lemma weight_anchor (b : X → Point d) (hb : Measurable b) : weight (anchor b hb)=0 := by
  simp [anchor,weight]
@[simp] lemma weight_zero : weight (zero : MeanTree X d)=0 := by simp [zero]
@[simp] lemma weight_scale (s : ℝ) (E : MeanTree X d) : weight (scale s E)=|s| * weight E := by
  cases E
  simp only [weight,scale,abs_mul,Finset.mul_sum]
@[simp] lemma weight_add (E D : MeanTree X d) : weight (add E D)=weight E+weight D := by
  cases E; cases D
  simp [weight,add,Fin.sum_univ_add]
@[simp] lemma weight_mean (r : ℝ) (E : MeanTree X d) : weight (mean r E)=1 := by
  simp [weight,mean]
@[simp] lemma weight_sumFin (k : ℕ) (E : Fin k → MeanTree X d) :
    weight (sumFin k E)=∑i,weight (E i) := by
  induction k with
  | zero => simp [sumFin]
  | succ k ih => simp [sumFin,ih,Fin.sum_univ_succ]
@[simp] lemma weight_sumFamily {I : Type*} [Fintype I] (E : I → MeanTree X d) :
    weight (sumFamily E)=∑i,weight (E i) := by
  simp only [sumFamily,weight_sumFin]
  exact Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)
@[simp] lemma weight_conditional (r t : ℝ) (x y : MeanTree X d) :
    weight (conditional r t x y)=1 := by simp [conditional]

def centersBound (A : ℝ) : MeanTree X d → Prop
  | .node _ _ _ _ _ E => ∀i,weight (E i)≤A ∧ centersBound A (E i)

@[simp] lemma centersBound_anchor (A : ℝ) (b : X → Point d) (hb : Measurable b) :
    centersBound A (anchor b hb) := by
  intro i
  exact Fin.elim0 i

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CircuitD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

def circuitD {d : ℕ} (F : Point d → ℝ) (x : Point d) : ℝ :=
  Real.sqrt d+‖gradient F x‖
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_StationaryMeanTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T s : ℝ}
  (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
  (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0 < s)
  (X : StationaryPath (gibbs (centeringPotential F x r T))
    (skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)))

def stationaryMeanTarget (X : StationaryPath (gibbs (centeringPotential F x r T))
    (skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0 hT1) s))) (y : Point (d+d)) : Point d :=
  s • (productPointEquiv d d y).2+
    ∫t in (0:ℝ)..1,conditionalFieldMean F x r T (productPointEquiv d d (X.path y t)).1

end LogConcaveSampling

end

end

end OAI
end


