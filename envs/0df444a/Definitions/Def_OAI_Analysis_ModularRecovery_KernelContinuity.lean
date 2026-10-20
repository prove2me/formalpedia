-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_KernelContinuity
-- name    : OAI_Analysis_ModularRecovery_KernelContinuity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:28:25.914163+00:00
-- url     : https://prove2.me/theorems/f2ff9785-f2c7-4651-8433-3fdb56a87692
-- title:
--   Translated scalar kernels and continuity of modular kernels
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   1. **Translated kernel.** For $r\in\mathbb R$, the bounded continuous function
--   $$
--   u\mapsto\kappa(r-u)=\frac1{2\cosh((r-u)/2)},
--   $$
--   bounded by $\frac12$.
--
--   The kernel scalar $\kappa$ is even, integrable, Lipschitz and bounded by $e^{-|r|/2}$. The modular kernel satisfies $K_r(b)\xi=\kappa(r-D)\,Jb^*\xi$ for $b\in M'$. It has norm at most $8\|b\|$ and depends continuously on $r$ in the strong topology.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/KernelContinuity.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/KernelContinuity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BoundedRecovery mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_OAI_Analysis_ModularRecovery_Model
import Definitions.Def_OAI_Analysis_ModularRecovery_SpectralCalculus
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaResolvent
import Definitions.Def_OAI_Analysis_ModularRecovery_PolarCutoff
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaFundamental
import Definitions.Def_OAI_Analysis_ModularRecovery_RealGraph
import Definitions.Def_OAI_Analysis_ModularRecovery_Commutant
import Definitions.Def_OAI_Analysis_ModularRecovery_PositiveKernels

namespace OAI

/-! Scalar kernel bounds, continuity, and spectral representations. -/

universe u uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery

lemma continuous_kernelScalar : Continuous kernelScalar := by
  unfold kernelScalar
  fun_prop (disch := intros; positivity)

lemma kernelScalar_even (r : ℝ) : kernelScalar (-r) = kernelScalar r := by
  unfold kernelScalar
  have he := Real.exp_pos r
  have hh := Real.exp_pos (r/2)
  rw [show -r/2= -(r/2) by ring,Real.exp_neg,Real.exp_neg]
  have hs : Real.exp r = Real.exp (r/2)^2 := exp_eq_sq_exp_half r
  rw [hs]
  field_simp
  ring

lemma kernelScalar_le_exp_neg_abs (r : ℝ) :
    kernelScalar r ≤ Real.exp (-|r|/2) := by
  wlog hr : 0 ≤ r generalizing r
  · simpa only [kernelScalar_even,abs_neg] using this (-r) (by linarith)
  rw [abs_of_nonneg hr]
  unfold kernelScalar
  rw [div_le_iff₀ (by positivity)]
  have he : Real.exp (r/2) = Real.exp (-r/2)*Real.exp r := by rw [← Real.exp_add]; congr 1; ring
  rw [he]
  nlinarith [Real.exp_pos (-r/2)]

lemma hasDerivAt_kernelScalar (r : ℝ) :
    HasDerivAt kernelScalar
      (kernelScalar r * ((1-Real.exp r)/(2*(Real.exp r+1)))) r := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (x/2)) (Real.exp (r/2)/2) r := by
    convert ((hasDerivAt_id r).div_const 2).exp using 1 <;> simp; ring
  have ht := he.div ((Real.hasDerivAt_exp r).add_const 1) (by positivity : Real.exp r+1 ≠ 0)
  convert ht using 1 <;> try rfl
  unfold kernelScalar
  field_simp
  ring

lemma kernelScalar_deriv_bound (r : ℝ) :
    ‖kernelScalar r * ((1-Real.exp r)/(2*(Real.exp r+1)))‖ ≤ 1 := by
  rw [norm_mul,Real.norm_eq_abs, abs_of_pos (kernelScalar_pos r), Real.norm_eq_abs,
    abs_div,abs_of_pos (by positivity : 0 < 2*(Real.exp r+1))]
  have ha : |1-Real.exp r| ≤ Real.exp r+1 := by
    rw [abs_le]
    constructor <;> linarith [Real.exp_pos r]
  have hb : |1-Real.exp r|/(2*(Real.exp r+1)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.exp_pos r]
  have hk := kernelScalar_le r
  have hp := kernelScalar_pos r
  nlinarith

lemma kernelScalar_lipschitz : LipschitzWith 1 kernelScalar := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun r => (hasDerivAt_kernelScalar r).differentiableAt)
  intro r
  rw [(hasDerivAt_kernelScalar r).deriv]
  exact_mod_cast kernelScalar_deriv_bound r

lemma integrable_exp_neg_abs_half : Integrable (fun r : ℝ => Real.exp (-|r|/2)) := by
  have hp : IntegrableOn (fun r : ℝ => Real.exp (-|r|/2)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (by norm_num : (-1/2:ℝ)<0) 0).congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only
    rw [abs_of_pos (show 0 < r from hr)]
    congr 1
    ring
  have hn : IntegrableOn (fun r : ℝ => Real.exp (-|r|/2)) (Iio 0) := by
    have hp0 : IntegrableOn (fun r : ℝ => Real.exp (-|r|/2)) (Ioi (-(0:ℝ))) := by
      simpa only [neg_zero] using hp
    have ht : IntegrableOn (fun r : ℝ => Real.exp (-|-r|/2)) (Iio (0:ℝ)) :=
      hp0.comp_neg_Iio (c := 0)
    simpa only [abs_neg] using ht
  have hp' : IntegrableOn (fun r : ℝ => Real.exp (-|r|/2)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hp
  have hu := hn.union hp'
  rw [Iio_union_Ici] at hu
  simpa only [integrableOn_univ] using hu

lemma integrable_kernelScalar : Integrable kernelScalar := by
  apply integrable_exp_neg_abs_half.mono' continuous_kernelScalar.aestronglyMeasurable
  exact ae_of_all _ fun r => by
    rw [Real.norm_eq_abs,abs_of_pos (kernelScalar_pos r)]
    exact kernelScalar_le_exp_neg_abs r

def translatedKernel (r : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (kernelScalar (r-u):ℂ))
    (Complex.continuous_ofReal.comp (continuous_kernelScalar.comp (continuous_const.sub continuous_id)))
    (1/2) (by intro u; simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (kernelScalar_pos _)]
      using kernelScalar_le (r-u))

@[simp] lemma translatedKernel_apply (r u : ℝ) : translatedKernel r u = (kernelScalar (r-u):ℂ) := rfl

lemma norm_translatedKernel_le (r : ℝ) : ‖translatedKernel r‖ ≤ 1/2 := by
  apply BoundedContinuousFunction.norm_le (by norm_num) |>.mpr
  intro u
  simpa only [translatedKernel_apply,Complex.norm_real,Real.norm_eq_abs, abs_of_pos (kernelScalar_pos _)]
    using kernelScalar_le (r-u)

lemma continuous_translatedKernel : Continuous translatedKernel := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro r s
  rw [dist_eq_norm]
  apply BoundedContinuousFunction.norm_le (by positivity) |>.mpr
  intro u
  change ‖(kernelScalar (r-u):ℂ)-(kernelScalar (s-u):ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub,Complex.norm_real, Real.norm_eq_abs]
  have ht := kernelScalar_lipschitz.dist_le_mul (r-u) (s-u)
  simpa [Real.dist_eq,sub_sub_sub_cancel_right] using ht

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma modularKernel_sum {ι : Type uι} (S : StandardModularData H) (r : ℝ)
    (s : Finset ι) (b : ι → S.M.commutant.toStarSubalgebra) :
    S.modularKernel r (∑ i ∈ s, b i) = ∑ i ∈ s, S.modularKernel r (b i) := by
  classical
  have hz : S.modularKernel r 0 = 0 := by simpa using S.modularKernel_smul r 0 0
  induction s using Finset.induction_on with
  | empty => simpa using hz
  | @insert i s hi ih => simp only [Finset.sum_insert hi, S.modularKernel_add, ih]

lemma norm_modularKernel_le (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : ‖S.modularKernel r b‖ ≤ 8*‖b‖ := by
  obtain ⟨x,hx,hxn,he⟩ := CStarAlgebra.exists_sum_four_nonneg b
  nth_rw 1 [he]
  rw [S.modularKernel_sum]
  calc
    ‖∑ i : Fin 4, S.modularKernel r (Complex.I ^ (i:ℕ) • x i)‖ ≤
        ∑ i : Fin 4, 2*‖b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [S.modularKernel_smul,norm_smul,norm_pow,Complex.norm_I,one_pow,one_mul]
      exact (S.norm_modularKernel_of_nonneg r (x i) (hx i)).trans (by gcongr; exact hxn i)
    _ = 8*‖b‖ := by simp; ring

end StandardModularData

lemma modularResolvent_sub_norm_le (r s : ℝ) :
    ‖modularResolvent r-modularResolvent s‖ ≤
      |Real.exp r-Real.exp s|/(Real.exp r*Real.exp s) := by
  apply BoundedContinuousFunction.norm_le (by positivity) |>.mpr
  intro u
  change ‖(((Real.exp r+Real.exp u)⁻¹:ℝ):ℂ)-(((Real.exp s+Real.exp u)⁻¹:ℝ):ℂ)‖ ≤ _
  have heR : (Real.exp r+Real.exp u)⁻¹-(Real.exp s+Real.exp u)⁻¹ =
      (Real.exp s-Real.exp r)/((Real.exp r+Real.exp u)*(Real.exp s+Real.exp u)) := by
    field_simp
    ring
  have he := congrArg (fun x : ℝ => (x:ℂ)) heR
  simp only [Complex.ofReal_sub] at he
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_div,
    abs_of_pos (mul_pos (add_pos (Real.exp_pos r) (Real.exp_pos u))
      (add_pos (Real.exp_pos s) (Real.exp_pos u))),abs_sub_comm]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
  nlinarith [Real.exp_pos r,Real.exp_pos s,Real.exp_pos u]

lemma continuous_modularResolvent : Continuous (fun r : ℝ => modularResolvent r) := by
  rw [continuous_iff_continuousAt]
  intro r
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun s => modularResolvent_sub_norm_le s r)
  have ht : Tendsto (fun s : ℝ => |Real.exp s-Real.exp r|/(Real.exp s*Real.exp r))
      (𝓝 r) (𝓝 (|Real.exp r-Real.exp r|/(Real.exp r*Real.exp r))) :=
    ((Real.continuous_exp.tendsto r).sub tendsto_const_nhds).abs.div
      ((Real.continuous_exp.tendsto r).mul tendsto_const_nhds)
      (ne_of_gt (mul_pos (Real.exp_pos r) (Real.exp_pos r)))
  simpa using ht

namespace StandardModularData
lemma continuous_modularKernel_xi (S : StandardModularData H)
    (b : S.M.commutant.toStarSubalgebra) :
    Continuous (fun r : ℝ => (S.modularKernel r b:H →L[ℂ] H) S.xi) := by
  have he : (fun r : ℝ => (S.modularKernel r b:H →L[ℂ] H) S.xi) =
      fun r => (Real.exp (r/2):ℂ) • S.D.calculus (modularResolvent r) ((b:H →L[ℂ] H) S.xi) := by
    funext r
    change (Real.exp (r/2):ℂ) • (S.modularLift r b:H →L[ℂ] H) S.xi = _
    rw [S.modularLift_xi]
  rw [he]
  apply Continuous.smul (by fun_prop)
  exact (S.D.calculusCLM.continuous.comp continuous_modularResolvent).clm_apply continuous_const

lemma continuous_modularKernel_apply (S : StandardModularData H)
    (b : S.M.commutant.toStarSubalgebra) (h : H) :
    Continuous (fun r : ℝ => (S.modularKernel r b:H →L[ℂ] H) h) := by
  rw [continuous_iff_continuousAt]
  intro r
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hd := commutant_cyclic S.M S.xi S.separating
  obtain ⟨_,⟨c,hc,rfl⟩,hclose⟩ := hd.exists_dist_lt h (by positivity : 0 < ε/(3*(8*‖b‖+1)))
  have hcont : Continuous (fun s : ℝ => (S.modularKernel s b:H →L[ℂ] H) (c S.xi)) := by
    have hm : ∀ s, (S.modularKernel s b:H →L[ℂ] H) (c S.xi) =
        c ((S.modularKernel s b:H →L[ℂ] H) S.xi) := by
      intro s
      exact congrArg (fun a : H →L[ℂ] H => a S.xi)
        (VonNeumannAlgebra.mem_commutant_iff.mp hc _ (S.modularKernel s b).property)
    simp_rw [hm]
    exact c.continuous.comp (S.continuous_modularKernel_xi b)
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (ε/3) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro s hs
  have hbound : ∀ u, ‖(S.modularKernel u b:H →L[ℂ] H) (h-c S.xi)‖ < ε/3 := by
    intro u
    apply (ContinuousLinearMap.le_opNorm _ _).trans_lt
    apply (mul_le_mul_of_nonneg_right (S.norm_modularKernel_le u b) (norm_nonneg _)).trans_lt
    rw [dist_eq_norm] at hclose
    have hp : 0 < 8*‖b‖+1 := by positivity
    have hh := (lt_div_iff₀ (by positivity : 0 < 3*(8*‖b‖+1))).mp hclose
    nlinarith [norm_nonneg (h-c S.xi)]
  have hh := norm_add_le ((S.modularKernel s b:H →L[ℂ] H) (h-c S.xi))
    ((S.modularKernel s b:H →L[ℂ] H) (c S.xi)-(S.modularKernel r b:H →L[ℂ] H) (c S.xi))
  have ht := norm_add_le
    ((S.modularKernel s b:H →L[ℂ] H) (h-c S.xi)+
      ((S.modularKernel s b:H →L[ℂ] H) (c S.xi)-(S.modularKernel r b:H →L[ℂ] H) (c S.xi)))
    (- (S.modularKernel r b:H →L[ℂ] H) (h-c S.xi))
  simp only [map_sub,sub_add_sub_cancel,norm_neg] at ht hh ⊢
  rw [dist_eq_norm]
  have hm := hd hs
  rw [dist_eq_norm] at hm
  have hs' := hbound s
  have hr' := hbound r
  simp only [map_sub] at hs' hr'
  have he : (S.modularKernel s b:H →L[ℂ] H) h-(S.modularKernel r b:H →L[ℂ] H) h =
    ((S.modularKernel s b:H →L[ℂ] H) h-(S.modularKernel s b:H →L[ℂ] H) (c S.xi))+
    ((S.modularKernel s b:H →L[ℂ] H) (c S.xi)-(S.modularKernel r b:H →L[ℂ] H) (c S.xi))+
    -((S.modularKernel r b:H →L[ℂ] H) h-(S.modularKernel r b:H →L[ℂ] H) (c S.xi)) := by abel
  rw [he]
  apply (norm_add_le _ _).trans_lt
  simp only [sub_add_sub_cancel, norm_neg]
  linarith

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate NNReal
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace RealSpectralCalculus
lemma halfGraph_calculus (D : RealSpectralCalculus H) {x y : H}
    (hxy : (x,y) ∈ D.halfGraph) (f : BoundedContinuousFunction ℝ ℂ) :
    (D.calculus f x,D.calculus f y) ∈ D.halfGraph := by
  rw [D.halfGraph_iff_resolvent] at hxy ⊢
  rw [← map_add]
  change (D.calculus halfResolvent*D.calculus f) (x+y)=_
  rw [← map_mul,mul_comm,map_mul]
  change D.calculus f (D.calculus halfResolvent (x+y))=_
  rw [hxy]
end RealSpectralCalculus

lemma translatedKernel_eq_mixed (r : ℝ) :
    translatedKernel r = (Real.exp (r/2):ℂ) • modularMixedResolvent r := by
  ext u
  change ((Real.exp ((r-u)/2)/(Real.exp (r-u)+1):ℝ):ℂ) =
    (Real.exp (r/2):ℂ)*((Real.exp (u/2)/(Real.exp r+Real.exp u):ℝ):ℂ)
  rw [← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [show (r-u)/2=r/2-u/2 by ring,Real.exp_sub,Real.exp_sub,exp_eq_sq_exp_half u]
  have hp : Real.exp (u/2) ≠ 0 := (Real.exp_pos _).ne'
  have hq : Real.exp r+Real.exp (u/2)^2 ≠ 0 := by positivity
  field_simp

namespace StandardModularData
lemma modularKernel_xi (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    (S.modularKernel r b:H →L[ℂ] H) S.xi =
      S.D.calculus (translatedKernel r) (S.J ((↑(star b):H →L[ℂ] H) S.xi)) := by
  have hg := S.commutant_halfGraph (↑(star b)) (star b).property
  simp only [StarMemClass.coe_star,star_star] at hg
  have hh := S.D.halfGraph_calculus hg (modularResolvent r)
  have hq := S.D.modularResolvent_halfGraph r (S.J ((star (b:H →L[ℂ] H)) S.xi))
  have he := S.D.halfGraph_unique hh hq
  change (Real.exp (r/2):ℂ) • (S.modularLift r b:H →L[ℂ] H) S.xi = _
  rw [S.modularLift_xi,he,translatedKernel_eq_mixed,map_smul]
  rfl
end StandardModularData
end BoundedRecovery

end
end
end

end OAI


