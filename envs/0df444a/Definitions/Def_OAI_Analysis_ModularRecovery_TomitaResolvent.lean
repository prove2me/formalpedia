-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_TomitaResolvent
-- name    : OAI_Analysis_ModularRecovery_TomitaResolvent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:13:31.765372+00:00
-- url     : https://prove2.me/theorems/6f3281c2-157b-4b23-b7bc-b13e2bafa57f
-- title:
--   Resolvents of the half exponential
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   1. **Half resolvent.** $R(u)=(e^{u/2}+1)^{-1}$, so $R(D)=(\Delta^{1/2}+1)^{-1}$. A pair $(x,y)$ lies in the graph of $\Delta^{1/2}$ exactly when $R(D)(x+y)=x$; hence the graph is closed, symmetric and positive.
--   2. **Real multipliers and regularized quotients.** A real bounded function $g$ viewed as complex, and for $k>0$ the quotient
--   $$
--   f(u)\,\frac{g(u)}{g(u)^2+k},
--   $$
--   used to show that vectors killed by $g(D)$ have spectral support in the zero set of $g$.
--   3. **Centred half resolvent.** $(e^{u/2}+1)^{-1}-\frac12$, strictly decreasing and vanishing only at $0$.
--   4. **Modular resolvents.** For $a\in\mathbb R$, $u\mapsto(e^a+e^u)^{-1}$ and $u\mapsto e^{u/2}/(e^a+e^u)$, the resolvent $(e^a+\Delta)^{-1}$ and its mixed companion $\Delta^{1/2}(e^a+\Delta)^{-1}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/TomitaResolvent.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/TomitaResolvent.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BoundedRecovery mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_OAI_Analysis_ModularRecovery_Model
import Definitions.Def_OAI_Analysis_ModularRecovery_SpectralCalculus

namespace OAI

/-! Resolvents of the half-exponential and the closed Tomita graph. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def halfResolvent : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (((Real.exp (u/2) + 1)⁻¹ : ℝ) : ℂ))
    (by
      apply Complex.continuous_ofReal.comp
      apply Continuous.inv₀
      · fun_prop
      · intro u
        exact ne_of_gt (add_pos (Real.exp_pos _) zero_lt_one))
    1 (by
      intro u
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
      exact inv_le_one_of_one_le₀ (by have := Real.exp_pos (u/2); linarith))

@[simp] lemma halfResolvent_apply (u : ℝ) :
    halfResolvent u = (((Real.exp (u/2) + 1)⁻¹ : ℝ) : ℂ) := rfl

lemma halfResolvent_selfAdjoint : IsSelfAdjoint halfResolvent := by
  ext u
  change star ((((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ)) = _
  simp only [Complex.star_def,Complex.conj_ofReal]
  rfl

lemma halfResolvent_cutoff_norm (n : ℕ) : ‖halfExponentialCutoff n * halfResolvent‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro u
  change ‖(Real.exp (min (n:ℝ) u / 2) : ℂ) * (((Real.exp (u/2) + 1)⁻¹ : ℝ) : ℂ)‖ ≤ 1
  rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  have hh : Real.exp (min (n:ℝ) u / 2) ≤ Real.exp (u/2) :=
    Real.exp_le_exp.mpr (by linarith [min_le_right (n:ℝ) u])
  linarith

namespace RealSpectralCalculus

lemma tendsto_calculus_of_compact_eventual (D : RealSpectralCalculus H)
    (f : ℕ → BoundedContinuousFunction ℝ ℂ) (g : BoundedContinuousFunction ℝ ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (he : ∀ q : BoundedContinuousFunction ℝ ℂ, HasCompactSupport (q : ℝ → ℂ) →
      ∀ᶠ n in atTop, f n * q = g * q) (h : H) :
    Tendsto (fun n => D.calculus (f n) h) atTop (𝓝 (D.calculus g h)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨v,⟨q,hq,k,rfl⟩,hv⟩ := D.nondegenerate.exists_dist_lt h
    (show 0 < eps / (C + ‖g‖ + 1) by positivity)
  have hv' : ‖h - D.calculus q k‖ < eps / (C + ‖g‖ + 1) := by
    simpa only [dist_eq_norm] using hv
  obtain ⟨N,hN⟩ := eventually_atTop.mp (he q hq)
  refine ⟨N,fun n hn => ?_⟩
  have hqeq : D.calculus (f n) (D.calculus q k) = D.calculus g (D.calculus q k) := by
    change (D.calculus (f n) * D.calculus q) k = (D.calculus g * D.calculus q) k
    rw [← map_mul,← map_mul,hN n hn]
  rw [dist_eq_norm]
  have heq : D.calculus (f n) h - D.calculus g h =
      D.calculus (f n) (h - D.calculus q k) - D.calculus g (h - D.calculus q k) := by
    simp only [map_sub,hqeq]
    abel
  rw [heq]
  calc
    _ ≤ ‖D.calculus (f n) (h - D.calculus q k)‖ + ‖D.calculus g (h - D.calculus q k)‖ := norm_sub_le _ _
    _ ≤ C * ‖h-D.calculus q k‖ + ‖g‖ * ‖h-D.calculus q k‖ :=
      add_le_add ((D.norm_calculus_apply_le _ _).trans (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)))
        (D.norm_calculus_apply_le _ _)
    _ ≤ (C + ‖g‖ + 1) * ‖h-D.calculus q k‖ := by nlinarith [norm_nonneg (h-D.calculus q k)]
    _ < (C + ‖g‖ + 1) * (eps / (C+‖g‖+1)) := mul_lt_mul_of_pos_left hv' (by positivity)
    _ = eps := by field_simp

lemma halfResolvent_cutoff_tendsto (D : RealSpectralCalculus H) (h : H) :
    Tendsto (fun n => D.calculus (halfExponentialCutoff n * halfResolvent) h)
      atTop (𝓝 (D.calculus (1-halfResolvent) h)) := by
  apply D.tendsto_calculus_of_compact_eventual _ _ zero_le_one halfResolvent_cutoff_norm _ h
  intro q hq
  obtain ⟨R,_hR,hRq⟩ := hq.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨N,hN⟩ := exists_nat_ge R
  filter_upwards [eventually_ge_atTop N] with n hn
  ext u
  by_cases hu : q u = 0
  · simp [hu]
  · have huR : u ≤ R := (le_abs_self u).trans (hRq u (subset_closure hu))
    have hun : u ≤ (n:ℝ) := huR.trans (hN.trans (by exact_mod_cast hn))
    change (Real.exp (min (n:ℝ) u / 2) : ℂ) * (((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ) * q u =
      (1 - (((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ)) * q u
    rw [min_eq_right hun]
    congr 1
    have hp : Real.exp (u/2)+1 ≠ 0 := by positivity
    have heR : Real.exp (u/2) * (Real.exp (u/2)+1)⁻¹ = 1 - (Real.exp (u/2)+1)⁻¹ := by
      field_simp
      ring
    simpa only [Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one] using congrArg Complex.ofReal heR

lemma halfGraph_iff_resolvent (D : RealSpectralCalculus H) (x y : H) :
    (x,y) ∈ D.halfGraph ↔ D.calculus halfResolvent (x+y) = x := by
  constructor
  · intro hxy
    have ht : Tendsto (fun n => D.calculus halfResolvent (D.calculus (halfExponentialCutoff n) x))
      atTop (𝓝 (D.calculus halfResolvent y)) :=
      (D.calculus halfResolvent).continuous.tendsto y |>.comp hxy
    have heq : (fun n => D.calculus halfResolvent (D.calculus (halfExponentialCutoff n) x)) =
        (fun n => D.calculus (halfExponentialCutoff n * halfResolvent) x) := by
      funext n
      change (D.calculus halfResolvent * D.calculus (halfExponentialCutoff n)) x = _
      rw [← map_mul,mul_comm]
    rw [heq] at ht
    have hh := tendsto_nhds_unique ht (D.halfResolvent_cutoff_tendsto x)
    have hh' : D.calculus halfResolvent y = x - D.calculus halfResolvent x := by
      simpa using hh
    simp only [map_add,hh']
    abel
  · intro heq
    have ht := D.halfResolvent_cutoff_tendsto (x+y)
    have hfun : (fun n => D.calculus (halfExponentialCutoff n * halfResolvent) (x+y)) =
        (fun n => D.calculus (halfExponentialCutoff n) x) := by
      funext n
      rw [map_mul]
      change D.calculus (halfExponentialCutoff n) (D.calculus halfResolvent (x+y)) = _
      rw [heq]
    have hv : D.calculus (1-halfResolvent) (x+y) = y := by
      simp only [map_sub,map_one,sub_apply, one_apply_eq_self,heq]
      abel
    rw [hfun,hv] at ht
    exact ht

lemma halfGraph_isClosed (D : RealSpectralCalculus H) : IsClosed D.halfGraph := by
  have he : D.halfGraph = {p : H × H | D.calculus halfResolvent (p.1+p.2) = p.1} := by
    ext p
    exact D.halfGraph_iff_resolvent p.1 p.2
  rw [he]
  exact isClosed_eq ((D.calculus halfResolvent).continuous.comp (continuous_fst.add continuous_snd)) continuous_fst

lemma halfGraph_resolvent (D : RealSpectralCalculus H) (h : H) :
    (D.calculus halfResolvent h, h-D.calculus halfResolvent h) ∈ D.halfGraph := by
  rw [D.halfGraph_iff_resolvent]
  congr 1
  abel

lemma halfGraph_unique (D : RealSpectralCalculus H) {x y z : H}
    (hxy : (x,y) ∈ D.halfGraph) (hxz : (x,z) ∈ D.halfGraph) : y=z :=
  tendsto_nhds_unique hxy hxz

lemma halfGraph_add (D : RealSpectralCalculus H) {x y a b : H}
    (hxy : (x,y) ∈ D.halfGraph) (hab : (a,b) ∈ D.halfGraph) : (x+a,y+b) ∈ D.halfGraph := by
  simpa only [halfGraph,mem_ofPred_eq,map_add] using hxy.add hab

lemma halfGraph_sub (D : RealSpectralCalculus H) {x y a b : H}
    (hxy : (x,y) ∈ D.halfGraph) (hab : (a,b) ∈ D.halfGraph) : (x-a,y-b) ∈ D.halfGraph := by
  simpa only [halfGraph,mem_ofPred_eq,map_sub] using hxy.sub hab

lemma halfGraph_symmetric (D : RealSpectralCalculus H) {x y a b : H}
    (hxy : (x,y) ∈ D.halfGraph) (hab : (a,b) ∈ D.halfGraph) :
    inner ℂ y a = inner ℂ x b := by
  have hstar (n : ℕ) : star (D.calculus (halfExponentialCutoff n)) = D.calculus (halfExponentialCutoff n) := by
    rw [← map_star]
    congr 1
    ext u
    change star ((Real.exp (min (n:ℝ) u / 2) : ℝ) : ℂ) = _
    simp only [Complex.star_def,Complex.conj_ofReal]
    rfl
  have he (n : ℕ) : inner ℂ (D.calculus (halfExponentialCutoff n) x) a =
      inner ℂ x (D.calculus (halfExponentialCutoff n) a) := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ x (star (D.calculus (halfExponentialCutoff n)) a) = _
    rw [hstar]
  exact tendsto_nhds_unique (hxy.inner tendsto_const_nhds)
    (by simpa only [he] using tendsto_const_nhds.inner hab)

lemma halfGraph_adjoint_iff (D : RealSpectralCalculus H) (x y : H) :
    (x,y) ∈ D.halfGraph ↔ ∀ a b, (a,b) ∈ D.halfGraph → inner ℂ y a = inner ℂ x b := by
  refine ⟨fun hxy a b hab => D.halfGraph_symmetric hxy hab, ?_⟩
  intro hh
  have hr : star (D.calculus halfResolvent) = D.calculus halfResolvent :=
    (halfResolvent_selfAdjoint.map D.calculus).star_eq
  rw [D.halfGraph_iff_resolvent]
  apply ext_inner_right ℂ
  intro k
  have hk := hh (D.calculus halfResolvent k) (k - D.calculus halfResolvent k) (D.halfGraph_resolvent k)
  rw [inner_sub_right] at hk
  have hs (u : H) : inner ℂ u (D.calculus halfResolvent k) = inner ℂ (D.calculus halfResolvent u) k := by
    rw [← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ (star (D.calculus halfResolvent) u) k = _
    rw [hr]
  rw [hs,hs] at hk
  rw [map_add,inner_add_left]
  exact (eq_add_of_sub_eq' hk.symm).symm

end RealSpectralCalculus
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in

lemma antiunitary_inner (J : H ≃ₗᵢ⋆[ℂ] H) (x y : H) :
    inner ℂ (J x) (J y) = star (inner ℂ x y) := by
  have hre (a b : H) : (inner ℂ (J a) (J b)).re = (inner ℂ a b).re := by
    change RCLike.re (inner ℂ (J a) (J b)) = RCLike.re (inner ℂ a b)
    simp only [re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      ← map_add, J.norm_map]
  apply Complex.ext
  · rw [Complex.star_def, Complex.conj_re]
    exact hre x y
  · have hi := hre x (Complex.I • y)
    have hJy : J (Complex.I • y) = (-Complex.I) • J y := by
      rw [J.map_smulₛₗ]
      congr 1
      exact Complex.conj_I
    rw [hJy] at hi
    rw [Complex.star_def, Complex.conj_im]
    simpa only [inner_smul_right, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_zero, neg_one_mul,
      sub_neg_eq_add, zero_add] using hi

namespace RealSpectralCalculus

lemma halfGraph_nonneg (D : RealSpectralCalculus H) {x y : H}
    (hxy : (x,y) ∈ D.halfGraph) : 0 ≤ (inner ℂ x y).re := by
  have hpos (n : ℕ) : 0 ≤ (inner ℂ x (D.calculus (halfExponentialCutoff n) x)).re := by
    let f : BoundedContinuousFunction ℝ ℂ :=
      BoundedContinuousFunction.ofNormedAddCommGroup
        (fun u : ℝ => (Real.exp (min (n : ℝ) u / 4) : ℂ))
        (by fun_prop) (Real.exp ((n : ℝ) / 4)) (by
          intro u
          simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr
            (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)))
    have hf : halfExponentialCutoff n = star f * f := by
      ext u
      change (Real.exp (min (n:ℝ) u / 2) : ℂ) =
        star (Real.exp (min (n:ℝ) u / 4) : ℂ) * (Real.exp (min (n:ℝ) u / 4) : ℂ)
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    rw [hf, map_mul, map_star]
    change 0 ≤ (inner ℂ x ((D.calculus f).adjoint (D.calculus f x))).re
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_nonneg (𝕜 := ℂ)
  have ht : Tendsto (fun n => inner ℂ x (D.calculus (halfExponentialCutoff n) x))
      atTop (𝓝 (inner ℂ x y)) := tendsto_const_nhds.inner hxy
  exact ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp ht)
    (Filter.Eventually.of_forall hpos)

end RealSpectralCalculus
namespace StandardModularData

lemma J_inner_flip (S : StandardModularData H) (x y : H) :
    inner ℂ (S.J x) y = inner ℂ (S.J y) x := by
  rw [← S.conjugation y, antiunitary_inner, S.conjugation]
  exact inner_conj_symm _ _

lemma tomita_graph_inner_xi (S : StandardModularData H) {x y : H}
    (hxy : (x,y) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)}) :
    inner ℂ y S.xi = inner ℂ S.xi x := by
  have hc : IsClosed {p : H × H | inner ℂ p.2 S.xi = inner ℂ S.xi p.1} :=
    isClosed_eq (continuous_snd.inner continuous_const) (continuous_const.inner continuous_fst)
  apply (closure_minimal (s := {p : H × H | ∃ a : H →L[ℂ] H,
    a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)}) ?_ hc) hxy
  rintro p ⟨a, _ha, rfl⟩
  exact ContinuousLinearMap.adjoint_inner_left a S.xi S.xi

lemma halfGraph_xi_Jxi (S : StandardModularData H) :
    (S.xi, S.J S.xi) ∈ S.D.halfGraph := by
  have hcore : (S.xi,S.xi) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := by
    apply subset_closure
    exact ⟨1, S.M.one_mem, by simp⟩
  rw [S.tomita_graph] at hcore
  obtain ⟨q,hq,he⟩ := hcore
  dsimp only at he hq
  have hqeq : q = S.J S.xi := by
    rw [he, S.conjugation]
  rwa [hqeq] at hq

lemma halfGraph_Jxi_xi (S : StandardModularData H) :
    (S.J S.xi, S.xi) ∈ S.D.halfGraph := by
  rw [S.D.halfGraph_adjoint_iff]
  intro a b hab
  have htom : (a,S.J b) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := by
    rw [S.tomita_graph]
    exact ⟨b,hab,rfl⟩
  rw [← S.tomita_graph_inner_xi htom, S.J_inner_flip]

lemma J_fixes_xi (S : StandardModularData H) : S.J S.xi = S.xi := by
  have hg := S.D.halfGraph_sub S.halfGraph_xi_Jxi S.halfGraph_Jxi_xi
  have hp := S.D.halfGraph_nonneg hg
  have he : S.J S.xi - S.xi = -(S.xi - S.J S.xi) := by abel
  rw [he, inner_neg_right, Complex.neg_re] at hp
  change 0 ≤ -RCLike.re (inner ℂ (S.xi - S.J S.xi) (S.xi - S.J S.xi)) at hp
  rw [← norm_sq_eq_re_inner] at hp
  have hn : ‖S.xi - S.J S.xi‖ = 0 := by nlinarith [norm_nonneg (S.xi - S.J S.xi)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

lemma halfGraph_xi (S : StandardModularData H) :
    (S.xi, S.xi) ∈ S.D.halfGraph := by
  simpa only [S.J_fixes_xi] using S.halfGraph_xi_Jxi

lemma halfResolvent_xi (S : StandardModularData H) :
    S.D.calculus halfResolvent S.xi = (1/2:ℂ) • S.xi := by
  have he := (S.D.halfGraph_iff_resolvent _ _).mp S.halfGraph_xi
  rw [map_add] at he
  calc
    S.D.calculus halfResolvent S.xi = (1/2:ℂ) •
        (S.D.calculus halfResolvent S.xi + S.D.calculus halfResolvent S.xi) := by
      rw [smul_add, ← add_smul]
      norm_num
    _ = _ := by rw [he]

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

def realMultiplier (g : BoundedContinuousFunction ℝ ℝ) :
    BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun u => (g u : ℂ))
    (Complex.continuous_ofReal.comp g.continuous) ‖g‖ (by
      intro u
      simpa only [Complex.norm_real] using g.norm_coe_le_norm u)

@[simp] lemma realMultiplier_apply (g : BoundedContinuousFunction ℝ ℝ) (u : ℝ) :
    realMultiplier g u = (g u : ℂ) := rfl

def regularizedQuotient (f : BoundedContinuousFunction ℝ ℂ)
    (g : BoundedContinuousFunction ℝ ℝ) (k : ℝ) (hk : 0 < k) :
    BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u => f u * ((g u / ((g u)^2 + k) : ℝ) : ℂ))
    (f.continuous.mul (Complex.continuous_ofReal.comp
      (g.continuous.div ((g.continuous.pow 2).add continuous_const)
        (fun u => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hk)))))
    (‖f‖ * (‖g‖ / k)) (by
      intro u
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos (add_pos_of_nonneg_of_pos (sq_nonneg _) hk)]
      apply mul_le_mul (f.norm_coe_le_norm u) _ (by positivity) (norm_nonneg _)
      apply (div_le_div_iff₀ (add_pos_of_nonneg_of_pos (sq_nonneg _) hk) hk).mpr
      calc
        |g u| * k ≤ ‖g‖ * k := mul_le_mul_of_nonneg_right
          (by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm u) hk.le
        _ ≤ ‖g‖ * ((g u)^2 + k) := mul_le_mul_of_nonneg_left
          (by nlinarith [sq_nonneg (g u)]) (norm_nonneg _))

lemma regularizedQuotient_remainder (f : BoundedContinuousFunction ℝ ℂ)
    (g : BoundedContinuousFunction ℝ ℝ) {k : ℝ} (hk : 0 < k) (u : ℝ) :
    (f - regularizedQuotient f g k hk * realMultiplier g) u =
      f u * ((k / ((g u)^2 + k) : ℝ) : ℂ) := by
  change f u - (f u * ((g u / ((g u)^2 + k) : ℝ) : ℂ)) * (g u : ℂ) = _
  have hd : (g u)^2 + k ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hk)
  have hdc : ((g u : ℂ)^2 + (k : ℂ)) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
  ring

lemma exists_multiplier_approx (g : BoundedContinuousFunction ℝ ℝ) (s : ℝ)
    (hsep : ∀ d : ℝ, 0 < d → ∃ c : ℝ, 0 < c ∧
      ∀ u : ℝ, d ≤ |u-s| → c ≤ |g u|)
    (f : BoundedContinuousFunction ℝ ℂ) (hf : f s = 0) {eps : ℝ} (heps : 0 < eps) :
    ∃ q : BoundedContinuousFunction ℝ ℂ, ‖f - q * realMultiplier g‖ ≤ eps := by
  obtain ⟨d, hd, hdf⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt eps heps
  obtain ⟨c,hc,hcg⟩ := hsep d hd
  let k : ℝ := eps * c^2 / (‖f‖+1)
  have hk : 0 < k := by dsimp [k]; positivity
  have hkeq : (‖f‖+1)*k = eps*c^2 := by
    dsimp only [k]
    field_simp
  refine ⟨regularizedQuotient f g k hk, (BoundedContinuousFunction.norm_le heps.le).mpr ?_⟩
  intro u
  rw [regularizedQuotient_remainder, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos hk (add_pos_of_nonneg_of_pos (sq_nonneg _) hk)), ← mul_div_assoc]
  apply (div_le_iff₀ (add_pos_of_nonneg_of_pos (sq_nonneg _) hk)).mpr
  by_cases hu : |u-s| < d
  · have hfu : ‖f u‖ < eps := by
      simpa only [Real.dist_eq, hf, dist_zero_right] using hdf hu
    calc
      ‖f u‖ * k ≤ eps * k := mul_le_mul_of_nonneg_right hfu.le hk.le
      _ ≤ eps * ((g u)^2+k) := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (g u)]) heps.le
  · have hgu := hcg u (le_of_not_gt hu)
    have hgsq : c^2 ≤ (g u)^2 := by nlinarith [sq_abs (g u)]
    calc
      ‖f u‖ * k ≤ (‖f‖+1)*k := mul_le_mul_of_nonneg_right ((f.norm_coe_le_norm u).trans (by linarith)) hk.le
      _ = eps*c^2 := hkeq
      _ ≤ eps*((g u)^2+k) := mul_le_mul_of_nonneg_left (by linarith) heps.le

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace RealSpectralCalculus

lemma kernel_of_separated_zero (D : RealSpectralCalculus H)
    (g : BoundedContinuousFunction ℝ ℝ) (s : ℝ)
    (hsep : ∀ d : ℝ, 0 < d → ∃ c : ℝ, 0 < c ∧
      ∀ u : ℝ, d ≤ |u-s| → c ≤ |g u|)
    {x : H} (hx : D.calculus (realMultiplier g) x = 0)
    (f : BoundedContinuousFunction ℝ ℂ) (hf : f s = 0) : D.calculus f x = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro eps heps
  have hden : 0 < ‖x‖+1 := by positivity
  obtain ⟨q,hq⟩ := exists_multiplier_approx g s hsep f hf (div_pos heps hden)
  have hprod : D.calculus (q * realMultiplier g) x = 0 := by
    rw [map_mul]
    change D.calculus q (D.calculus (realMultiplier g) x) = 0
    rw [hx, map_zero]
  have heq : D.calculus f x = D.calculus (f - q * realMultiplier g) x := by
    rw [map_sub, sub_apply, hprod, sub_zero]
  rw [heq, zero_add]
  calc
    ‖D.calculus (f - q * realMultiplier g) x‖ ≤ ‖f - q * realMultiplier g‖ * ‖x‖ :=
      D.norm_calculus_apply_le _ _
    _ ≤ (eps/(‖x‖+1)) * ‖x‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
    _ ≤ eps := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith

end RealSpectralCalculus

def centeredHalfResolvent : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (Real.exp (u/2)+1)⁻¹ - 1/2)
    (by
      apply Continuous.sub _ continuous_const
      apply Continuous.inv₀
      · fun_prop
      · intro u
        exact ne_of_gt (add_pos (Real.exp_pos _) zero_lt_one))
    2 (by
      intro u
      rw [Real.norm_eq_abs, abs_le]
      have hp : 0 < (Real.exp (u/2)+1)⁻¹ := inv_pos.mpr (by positivity)
      have hle : (Real.exp (u/2)+1)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by have := Real.exp_pos (u/2); linarith)
      constructor <;> linarith)

@[simp] lemma centeredHalfResolvent_apply (u : ℝ) :
    centeredHalfResolvent u = (Real.exp (u/2)+1)⁻¹ - 1/2 := rfl

@[simp] lemma centeredHalfResolvent_zero : centeredHalfResolvent 0 = 0 := by
  norm_num [centeredHalfResolvent_apply]

lemma centeredHalfResolvent_strictAnti : StrictAnti centeredHalfResolvent := by
  intro a b hab
  change (Real.exp (b/2)+1)⁻¹ - 1/2 < (Real.exp (a/2)+1)⁻¹ - 1/2
  apply sub_lt_sub_right
  apply (inv_lt_inv₀ (by positivity) (by positivity)).mpr
  have he := Real.exp_lt_exp.mpr (show a/2 < b/2 by linarith)
  linarith

lemma centeredHalfResolvent_separated (d : ℝ) (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, d ≤ |u-0| → c ≤ |centeredHalfResolvent u| := by
  have hp : 0 < centeredHalfResolvent (-d) := by
    simpa only [centeredHalfResolvent_zero] using
      centeredHalfResolvent_strictAnti (show -d < 0 by linarith)
  have hn : centeredHalfResolvent d < 0 := by
    simpa only [centeredHalfResolvent_zero] using centeredHalfResolvent_strictAnti hd
  refine ⟨min (centeredHalfResolvent (-d)) (-centeredHalfResolvent d), lt_min hp (by linarith), ?_⟩
  intro u hu
  rw [sub_zero, le_abs] at hu
  rcases hu with hu | hu
  · have ht := centeredHalfResolvent_strictAnti.antitone hu
    have hneg : centeredHalfResolvent u < 0 := ht.trans_lt hn
    rw [abs_of_neg hneg]
    exact (min_le_right _ _).trans (neg_le_neg ht)
  · have ht := centeredHalfResolvent_strictAnti.antitone (show u ≤ -d by linarith)
    have hpos : 0 < centeredHalfResolvent u := hp.trans_le ht
    rw [abs_of_pos hpos]
    exact (min_le_left _ _).trans ht

lemma realMultiplier_centeredHalfResolvent :
    realMultiplier centeredHalfResolvent = halfResolvent - (1/2 : ℂ) • 1 := by
  ext u
  change (((Real.exp (u/2)+1)⁻¹ - 1/2 : ℝ) : ℂ) =
    (((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ) - (1/2 : ℂ) * 1
  push_cast
  ring

namespace StandardModularData

lemma xi_spectralSupport (S : StandardModularData H) :
    S.D.HasSpectralSupport {0} S.xi := by
  intro f hf
  apply S.D.kernel_of_separated_zero centeredHalfResolvent 0 centeredHalfResolvent_separated _ f
    (hf 0 (mem_singleton 0))
  rw [realMultiplier_centeredHalfResolvent, map_sub, map_smul, map_one, sub_apply,
    smul_apply, one_apply_eq_self, S.halfResolvent_xi, sub_self]

lemma fixes_xi (S : StandardModularData H) (t : ℝ) : S.D.unitary t S.xi = S.xi := by
  have he := S.xi_spectralSupport (spectralCharacter t - 1) (by
    intro u hu
    rcases mem_singleton_iff.mp hu with rfl
    simp)
  simpa only [map_sub, map_one, sub_apply, one_apply_eq_self, sub_eq_zero, RealSpectralCalculus.unitary] using he

end StandardModularData
end BoundedRecovery

namespace BoundedRecovery
namespace StandardModularData

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tomita_graph_swap (S : StandardModularData H) {x y : H}
    (hxy : (x,y) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)}) :
    (y,x) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := by
  have hc : IsClosed {p : H × H | p.swap ∈ closure {p : H × H |
      ∃ a : H →L[ℂ] H, a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)}} :=
    isClosed_closure.preimage continuous_swap
  apply (closure_minimal (s := {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)}) ?_ hc) hxy
  rintro p ⟨a, ha, rfl⟩
  apply subset_closure
  exact ⟨star a, star_mem ha, by simp⟩

lemma halfGraph_flip (S : StandardModularData H) {x y : H}
    (hxy : (x,y) ∈ S.D.halfGraph) : (S.J y,S.J x) ∈ S.D.halfGraph := by
  have ht : (x,S.J y) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := by
    rw [S.tomita_graph]
    exact ⟨y,hxy,rfl⟩
  have hs := S.tomita_graph_swap ht
  rw [S.tomita_graph] at hs
  obtain ⟨q,hq,he⟩ := hs
  dsimp only at hq he
  have hqeq : q = S.J x := by rw [he, S.conjugation]
  rwa [hqeq] at hq

lemma commutant_halfGraph (S : StandardModularData H) (b : H →L[ℂ] H)
    (hb : b ∈ S.M.commutant) :
    (S.J (b S.xi), (star b) S.xi) ∈ S.D.halfGraph := by
  rw [S.D.halfGraph_adjoint_iff]
  intro x y hxy
  have ht : (x,S.J y) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := by
    rw [S.tomita_graph]
    exact ⟨y,hxy,rfl⟩
  have hc : IsClosed {p : H × H |
      inner ℂ ((star b) S.xi) p.1 = inner ℂ p.2 (b S.xi)} :=
    isClosed_eq (continuous_const.inner continuous_fst) (continuous_snd.inner continuous_const)
  have he : inner ℂ ((star b) S.xi) x = inner ℂ (S.J y) (b S.xi) := by
    apply (closure_minimal (s := {p : H × H | ∃ a : H →L[ℂ] H,
        a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)}) ?_ hc) ht
    rintro p ⟨a,ha,rfl⟩
    change inner ℂ (ContinuousLinearMap.adjoint b S.xi) (a S.xi) =
      inner ℂ (ContinuousLinearMap.adjoint a S.xi) (b S.xi)
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ S.xi ((b*a) S.xi) = inner ℂ S.xi ((a*b) S.xi)
    rw [VonNeumannAlgebra.mem_commutant_iff.mp hb a ha]
  rw [he, S.J_inner_flip]

end StandardModularData
end BoundedRecovery

namespace BoundedRecovery

lemma exp_eq_sq_exp_half (u : ℝ) : Real.exp u = Real.exp (u/2) ^ 2 := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

def modularResolvent (a : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (((Real.exp a + Real.exp u)⁻¹ : ℝ) : ℂ))
    (by fun_prop (disch := intros; positivity)) (Real.exp a)⁻¹ (by
      intro u
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact (inv_le_inv₀ (by positivity) (Real.exp_pos a)).mpr (le_add_of_nonneg_right (Real.exp_pos u).le))

def modularMixedResolvent (a : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => ((Real.exp (u/2) / (Real.exp a + Real.exp u) : ℝ) : ℂ))
    (by fun_prop (disch := intros; positivity)) ((2 * Real.exp (a/2))⁻¹) (by
      intro u
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [← one_div (2 * Real.exp (a/2))]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      rw [exp_eq_sq_exp_half a, exp_eq_sq_exp_half u]
      nlinarith [sq_nonneg (Real.exp (u/2) - Real.exp (a/2))])

namespace RealSpectralCalculus
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularResolvent_halfGraph (D : RealSpectralCalculus H) (a : ℝ) (h : H) :
    (D.calculus (modularResolvent a) h, D.calculus (modularMixedResolvent a) h) ∈ D.halfGraph := by
  rw [D.halfGraph_iff_resolvent]
  change D.calculus halfResolvent ((D.calculus (modularResolvent a) +
    D.calculus (modularMixedResolvent a)) h) = D.calculus (modularResolvent a) h
  rw [← map_add]
  change (D.calculus halfResolvent * D.calculus (modularResolvent a + modularMixedResolvent a)) h = _
  rw [← map_mul]
  congr 2
  ext u
  change (((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ) *
    ((((Real.exp a+Real.exp u)⁻¹ : ℝ) : ℂ) +
      ((Real.exp (u/2)/(Real.exp a+Real.exp u) : ℝ) : ℂ)) =
    (((Real.exp a+Real.exp u)⁻¹ : ℝ) : ℂ)
  rw [← Complex.ofReal_add, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have h1 : Real.exp (u/2)+1 ≠ 0 := by positivity
  have h2 : Real.exp a+Real.exp u ≠ 0 := by positivity
  field_simp
  ring

lemma modularMixedResolvent_halfGraph (D : RealSpectralCalculus H) (a : ℝ) (h : H) :
    (D.calculus (modularMixedResolvent a) h,
      h - (Real.exp a : ℂ) • D.calculus (modularResolvent a) h) ∈ D.halfGraph := by
  rw [D.halfGraph_iff_resolvent]
  have he : D.calculus (modularMixedResolvent a) h +
      (h-(Real.exp a:ℂ) • D.calculus (modularResolvent a) h) =
      D.calculus (modularMixedResolvent a + (1-(Real.exp a:ℂ) • modularResolvent a)) h := by simp
  rw [he]
  change (D.calculus halfResolvent * D.calculus
    (modularMixedResolvent a + (1-(Real.exp a:ℂ) • modularResolvent a))) h = _
  rw [← map_mul]
  congr 2
  ext u
  change (((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ) *
    (((Real.exp (u/2)/(Real.exp a+Real.exp u) : ℝ) : ℂ) +
      (1-(Real.exp a:ℂ)*(((Real.exp a+Real.exp u)⁻¹ : ℝ) : ℂ))) =
    ((Real.exp (u/2)/(Real.exp a+Real.exp u) : ℝ) : ℂ)
  rw [← Complex.ofReal_mul (Real.exp a), ← Complex.ofReal_one,
    ← Complex.ofReal_sub, ← Complex.ofReal_add, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have h1 : Real.exp (u/2)+1 ≠ 0 := by positivity
  have h2 : Real.exp a+Real.exp u ≠ 0 := by positivity
  field_simp
  rw [exp_eq_sq_exp_half u]
  ring

end RealSpectralCalculus
end BoundedRecovery

end
end
end
end

end OAI


