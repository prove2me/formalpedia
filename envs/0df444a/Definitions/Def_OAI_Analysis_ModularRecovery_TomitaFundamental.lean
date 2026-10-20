-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_TomitaFundamental
-- name    : OAI_Analysis_ModularRecovery_TomitaFundamental
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:15:43.555523+00:00
-- url     : https://prove2.me/theorems/46a7e49c-c445-4137-ab42-998b6b87ec8e
-- title:
--   Modular energy, orbits and bounded lifts
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   1. **Modular energy.** For $\lambda\in\mathbb R$ and vectors $b,x,y$,
--   $$
--   E_{\lambda,b}(x,y)=\lambda\|x\|^2+\|y\|^2-2\,\mathrm{Re}\langle b,x\rangle .
--   $$
--   It is minimized along the graph of $\Delta^{1/2}$ to solve the resolvent equation.
--   2. **Vector state.** $a\mapsto\langle\xi,a\xi\rangle$ as a linear functional on operators.
--   3. **Operator orbit.** The subspace $\{a\xi:a\in M\}$.
--   4. **Evaluation.** The linear map $a\mapsto ah$ on $M$ for a fixed vector $h$.
--
--   With these, a vector in the closure of $\{a\xi:a\in M,\ \|a\|\le C\}$ is itself of this form. Also, $(e^r+\Delta)^{-1}b\xi$ for $b\in M'$ is $a\xi$ for some $a\in M$ of controlled norm.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/TomitaFundamental.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/TomitaFundamental.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BoundedRecovery mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_OAI_Analysis_ModularRecovery_Model
import Definitions.Def_OAI_Analysis_ModularRecovery_SpectralCalculus
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaResolvent
import Definitions.Def_OAI_Analysis_ModularRecovery_PolarCutoff

namespace OAI

/-! Closed Tomita relations and bounded transforms. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularEnergy (lam : ℝ) (b : H) (x y : H) : ℝ :=
  lam * ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (inner ℂ b x).re

namespace RealSpectralCalculus

lemma halfGraph_energy_identity (D : RealSpectralCalculus H) (lam : ℝ) (b : H)
    {z q x y : H} (hzq : (z,q) ∈ D.halfGraph)
    (hqb : (q,b-(lam:ℂ) • z) ∈ D.halfGraph) (hxy : (x,y) ∈ D.halfGraph) :
    modularEnergy lam b x y - modularEnergy lam b z q =
      lam * ‖x-z‖ ^ 2 + ‖y-q‖ ^ 2 := by
  have hh {u v : H} (huv : (u,v) ∈ D.halfGraph) :
      lam * (inner ℂ u z).re + (inner ℂ v q).re = (inner ℂ b u).re := by
    have he := congrArg Complex.re (D.halfGraph_symmetric huv hqb)
    simp only [inner_sub_right, inner_smul_right, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at he
    have hs : (inner ℂ b u).re = (inner ℂ u b).re := inner_re_symm (𝕜 := ℂ) b u
    rw [hs]
    linarith
  have he1 := hh hxy
  have he2 := hh hzq
  have hzsq : (inner ℂ z z).re = ‖z‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) z
  have hqsq : (inner ℂ q q).re = ‖q‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) q
  rw [hzsq, hqsq] at he2
  rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
  unfold modularEnergy
  change lam * ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (inner ℂ b x).re -
    (lam * ‖z‖ ^ 2 + ‖q‖ ^ 2 - 2 * (inner ℂ b z).re) =
    lam * (‖x‖ ^ 2 - 2 * (inner ℂ x z).re + ‖z‖ ^ 2) +
      (‖y‖ ^ 2 - 2 * (inner ℂ y q).re + ‖q‖ ^ 2)
  rw [← he1, ← he2]
  ring

end RealSpectralCalculus

namespace StandardModularData

lemma core_halfGraph (S : StandardModularData H) (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    (a S.xi, S.J ((star a) S.xi)) ∈ S.D.halfGraph := by
  have hh : (a S.xi, (star a) S.xi) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := subset_closure ⟨a, ha, rfl⟩
  rw [S.tomita_graph] at hh
  rcases hh with ⟨q, hq, he⟩
  change (star a) S.xi = S.J q at he
  rw [he, S.conjugation]
  exact hq

end StandardModularData

def vectorStateLM (xi : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun a := inner ℂ xi (a xi)
  map_add' a b := by simp
  map_smul' c a := by simp

lemma vectorState_star_mul (xi : H) (a : H →L[ℂ] H) :
    vectorStateLM xi (star a * a) = (‖a xi‖ ^ 2 : ℝ) := by
  change inner ℂ xi (ContinuousLinearMap.adjoint a (a xi)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

omit [CompleteSpace H] in
lemma re_vectorState_mono (xi : H) {a b : H →L[ℂ] H} (hab : a ≤ b) :
    (vectorStateLM xi a).re ≤ (vectorStateLM xi b).re := by
  have hp := ((ContinuousLinearMap.le_def a b).mp hab).re_inner_nonneg_right xi
  change 0 ≤ (inner ℂ xi ((b - a) xi)).re at hp
  change (inner ℂ xi (a xi)).re ≤ (inner ℂ xi (b xi)).re
  simpa only [sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using hp

lemma vonNeumannAlgebra_isClosed (M : VonNeumannAlgebra H) :
    IsClosed (M : Set (H →L[ℂ] H)) := by
  have he : (M : Set (H →L[ℂ] H)) =
      ⋂ (a : H →L[ℂ] H) (_ : a ∈ M.commutant), {b | a * b = b * a} := by
    ext b
    simp only [mem_iInter, mem_ofPred_eq, SetLike.mem_coe]
    have hh := @VonNeumannAlgebra.mem_commutant_iff H _ _ _ M.commutant b
    simpa only [M.commutant_commutant] using hh
  rw [he]
  exact isClosed_iInter (fun a => isClosed_iInter (fun _ =>
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)))

lemma polarCutoff_mem (M : VonNeumannAlgebra H) {z : H →L[ℂ] H} (hz : z ∈ M) (K : ℝ) :
    polarCutoff z K ∈ M := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := vonNeumannAlgebra_isClosed M
  have hc : cfc (cutoffFunction K) (star z * z) ∈ M.toStarSubalgebra :=
    cfc_mem (𝕜' := ℂ) (cutoffFunction K) (show star z * z ∈ M.toStarSubalgebra from mul_mem (star_mem hz) hz)
  exact mul_mem hz hc

lemma cutoffLeft_mem (M : VonNeumannAlgebra H) {a : H →L[ℂ] H} (ha : a ∈ M) (K : ℝ) :
    cutoffLeft a K ∈ M := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := vonNeumannAlgebra_isClosed M
  have hc : cfc (cutoffLeftFunction K) (star a * a) ∈ M.toStarSubalgebra :=
    cfc_mem (𝕜' := ℂ) (cutoffLeftFunction K) (show star a * a ∈ M.toStarSubalgebra from mul_mem (star_mem ha) ha)
  exact mul_mem ha hc

lemma vectorState_mul_star (xi : H) (a : H →L[ℂ] H) :
    vectorStateLM xi (a * star a) = (‖(star a) xi‖ ^ 2 : ℝ) := by
  simpa only [star_star] using vectorState_star_mul xi (star a)

lemma cutoffRight_vector_loss (xi : H) (a : H →L[ℂ] H) {K : ℝ} (hK : 0 < K) :
    (2*K) * ‖cutoffRight a K xi‖ ^ 2 ≤ ‖a xi‖ ^ 2 - ‖polarCutoff a K xi‖ ^ 2 := by
  have hh := re_vectorState_mono xi (cutoffRight_loss a hK)
  simpa only [map_sub, LinearMap.map_smul_of_tower, vectorState_star_mul,
    Complex.sub_re, Complex.smul_re, Complex.ofReal_re, smul_eq_mul] using hh

lemma cutoffLeft_vector_loss (xi : H) (a : H →L[ℂ] H) {K : ℝ} (hK : 0 < K) :
    (2*K) * ‖star (cutoffLeft a K) xi‖ ^ 2 ≤
      ‖(star a) xi‖ ^ 2 - ‖star (polarCutoff a K) xi‖ ^ 2 := by
  have hh := re_vectorState_mono xi (cutoffLeft_loss a hK)
  simpa only [map_sub, LinearMap.map_smul_of_tower, vectorState_mul_star,
    Complex.sub_re, Complex.smul_re, Complex.ofReal_re, smul_eq_mul] using hh

lemma cutoff_cross_term (M : VonNeumannAlgebra H) (xi : H)
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M.commutant) {K : ℝ} (hK : 0 < K) :
    2 * (inner ℂ (b xi) ((a-polarCutoff a K) xi)).re ≤
      ‖b‖ * (‖star (cutoffLeft a K) xi‖ ^ 2 + ‖cutoffRight a K xi‖ ^ 2) := by
  let l := cutoffLeft a K
  let r := cutoffRight a K
  have hc : (star l) * b = b * star l :=
    (VonNeumannAlgebra.mem_commutant_iff.mp hb) (star l) (star_mem (cutoffLeft_mem M ha K))
  have he : inner ℂ (b xi) ((a-polarCutoff a K) xi) =
      inner ℂ (b ((star l) xi)) (r xi) := by
    rw [← cutoffLeft_mul_right a hK]
    change inner ℂ (b xi) (l (r xi)) = _
    rw [← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ (((star l) * b) xi) (r xi) = _
    rw [hc]
    rfl
  rw [he]
  have hh : (inner ℂ (b ((star l) xi)) (r xi)).re ≤ ‖b‖ * ‖(star l) xi‖ * ‖r xi‖ :=
    (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (b.le_opNorm _) (norm_nonneg _)))
  have hs := mul_nonneg (norm_nonneg b) (sq_nonneg (‖(star l) xi‖ - ‖r xi‖))
  change 2 * (inner ℂ (b ((star l) xi)) (r xi)).re ≤
    ‖b‖ * (‖(star l) xi‖ ^ 2 + ‖r xi‖ ^ 2)
  nlinarith

lemma cutoff_energy_le (M : VonNeumannAlgebra H) (xi : H)
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M.commutant)
    {lam K : ℝ} (hlam : 0 ≤ lam) (hK : 0 < K) (h1 : ‖b‖ ≤ 2*K) (h2 : ‖b‖ ≤ lam*(2*K)) :
    modularEnergy lam (b xi) (polarCutoff a K xi) (star (polarCutoff a K) xi) ≤
      modularEnergy lam (b xi) (a xi) ((star a) xi) := by
  have hr := mul_le_mul_of_nonneg_left (cutoffRight_vector_loss xi a hK) hlam
  have hl := cutoffLeft_vector_loss xi a hK
  have hc := cutoff_cross_term M xi a b ha hb hK
  have h1' := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖star (cutoffLeft a K) xi‖)
  have h2' := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖cutoffRight a K xi‖)
  simp only [sub_apply, inner_sub_right, Complex.sub_re] at hc
  unfold modularEnergy
  nlinarith

def operatorOrbit (M : VonNeumannAlgebra H) (xi : H) : Submodule ℂ H where
  carrier := {h | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h}
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro h k ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, by simp⟩
  smul_mem' := by
    rintro c h ⟨a, ha, rfl⟩
    exact ⟨c • a, M.toStarSubalgebra.smul_mem ha c, by simp⟩

lemma operatorOrbit_invariant (M : VonNeumannAlgebra H) (xi : H)
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    operatorOrbit M xi ∈ Module.End.invtSubmodule a := by
  intro h hh
  rcases hh with ⟨b, hb, rfl⟩
  exact ⟨a * b, mul_mem ha hb, rfl⟩

lemma commutant_cyclic (M : VonNeumannAlgebra H) (xi : H)
    (hsep : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0) :
    Dense (operatorOrbit M.commutant xi : Set H) := by
  let K := (operatorOrbit M.commutant xi).topologicalClosure
  have hP : K.starProjection ∈ M := by
    apply (VonNeumannAlgebra.IsStarProjection.mem_iff
      (isStarProjection_starProjection (U := K)) M).mpr
    intro a ha
    rw [Submodule.range_starProjection]
    exact Submodule.topologicalClosure_mem_invtSubmodule (operatorOrbit_invariant _ _ a ha)
  have hxi : xi ∈ K := by
    apply Submodule.le_topologicalClosure
    exact ⟨1, one_mem _, by simp⟩
  have heq : (1 : H →L[ℂ] H) - K.starProjection = 0 := by
    apply hsep _ (sub_mem (one_mem _) hP)
    simp [K.starProjection_eq_self_iff.mpr hxi]
  have htop : K = ⊤ := by
    apply top_unique
    intro h _
    have hp : K.starProjection h = h := by
      have := congrArg (fun a : H →L[ℂ] H => a h) heq
      exact (sub_eq_zero.mp this).symm
    exact K.starProjection_eq_self_iff.mp hp
  exact dense_iff_closure_eq.mpr (show closure (operatorOrbit M.commutant xi : Set H) = univ from
    congrArg (fun S : Submodule ℂ H => (S : Set H)) htop)

def operatorEvaluation (M : VonNeumannAlgebra H) (h : H) : M.toStarSubalgebra →ₗ[ℂ] H where
  toFun a := a.val h
  map_add' a b := by simp
  map_smul' c a := by simp

lemma bounded_orbit_lift (M : VonNeumannAlgebra H) (xi : H)
    (hsep : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0)
    {C : ℝ} (hC : 0 ≤ C) {h : H}
    (hh : h ∈ closure {v : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ ‖a‖ ≤ C ∧ a xi = v}) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ ‖a‖ ≤ C ∧ a xi = h := by
  let e := operatorEvaluation M.commutant xi
  let f := operatorEvaluation M.commutant h
  have hd : DenseRange e := by
    change Dense (Set.range e)
    have heq : Set.range e = (operatorOrbit M.commutant xi : Set H) := by
      ext v
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.property, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
    rw [heq]
    exact commutant_cyclic M xi hsep
  have hb : ∀ b : M.commutant.toStarSubalgebra, ‖f b‖ ≤ C * ‖e b‖ := by
    intro b
    change ‖b.val h‖ ≤ C * ‖b.val xi‖
    apply (isClosed_le (b.val.continuous.norm) continuous_const).closure_subset_iff.mpr ?_ hh
    rintro v ⟨a, ha, han, rfl⟩
    have hc := (VonNeumannAlgebra.mem_commutant_iff.mp b.property) a ha
    change ‖(b.val * a) xi‖ ≤ _
    rw [← hc]
    exact (a.le_opNorm _).trans (mul_le_mul_of_nonneg_right han (norm_nonneg _))
  let a := f.extendOfNorm e
  have hext (b : M.commutant.toStarSubalgebra) : a (b.val xi) = b.val h :=
    LinearMap.extendOfNorm_eq hd ⟨C, hb⟩ b
  have ham : a ∈ M := by
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro b hbm
    let b' : M.commutant.toStarSubalgebra := ⟨b, hbm⟩
    apply ContinuousLinearMap.ext
    have heq : ∀ v ∈ Set.range e, (b * a) v = (a * b) v := by
      rintro v ⟨c, rfl⟩
      change b (a (c.val xi)) = a ((b * c.val) xi)
      rw [hext c]
      exact (hext (b' * c)).symm
    exact fun v => hd.induction heq (isClosed_eq (b * a).continuous (a * b).continuous) v
  refine ⟨a, ham, LinearMap.opNorm_extendOfNorm_le hd hC hb, ?_⟩
  simpa using hext 1

lemma isClosed_bounded_orbit (M : VonNeumannAlgebra H) (xi : H)
    (hsep : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0)
    {C : ℝ} (hC : 0 ≤ C) :
    IsClosed {v : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ ‖a‖ ≤ C ∧ a xi = v} := by
  rw [← closure_subset_iff_isClosed]
  intro h hh
  exact bounded_orbit_lift M xi hsep hC hh

namespace StandardModularData

lemma fundamental_resolvent_lift (S : StandardModularData H) (r : ℝ)
    (b : H →L[ℂ] H) (hb : b ∈ S.M.commutant) :
    ∃ a : H →L[ℂ] H, a ∈ S.M ∧ ‖a‖ ≤ ‖b‖ * (1+(Real.exp r)⁻¹)+1 ∧
      a S.xi = S.D.calculus (modularResolvent r) (b S.xi) := by
  let lam := Real.exp r
  let z := S.D.calculus (modularResolvent r) (b S.xi)
  let q := S.D.calculus (modularMixedResolvent r) (b S.xi)
  let K := ‖b‖ * (1+lam⁻¹)+1
  have hlam : 0 < lam := Real.exp_pos r
  have hK : 0 < K := by dsimp [K]; positivity
  have h1 : ‖b‖ ≤ 2*K := by
    have hh : 0 ≤ ‖b‖ * lam⁻¹ := mul_nonneg (norm_nonneg b) (inv_nonneg.mpr hlam.le)
    dsimp [K]
    nlinarith [norm_nonneg b]
  have h2 : ‖b‖ ≤ lam*(2*K) := by
    have he : lam * K = ‖b‖ * (lam+1)+lam := by
      dsimp [K]
      field_simp
    nlinarith [mul_nonneg (norm_nonneg b) hlam.le, norm_nonneg b]
  have hzq : (z,q) ∈ S.D.halfGraph := S.D.modularResolvent_halfGraph r (b S.xi)
  have hqb : (q,b S.xi-(lam:ℂ) • z) ∈ S.D.halfGraph :=
    S.D.modularMixedResolvent_halfGraph r (b S.xi)
  have hg : (z,S.J q) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := by
    rw [S.tomita_graph]
    exact ⟨q,hzq,rfl⟩
  rcases mem_closure_iff_seq_limit.mp hg with ⟨p,hp,hpt⟩
  choose a ha he using hp
  have hxt : Tendsto (fun n => a n S.xi) atTop (𝓝 z) := by
    simpa only [he] using hpt.fst_nhds
  have hyt : Tendsto (fun n => (star (a n)) S.xi) atTop (𝓝 (S.J q)) := by
    simpa only [he] using hpt.snd_nhds
  have hEt : Tendsto (fun n => modularEnergy lam (b S.xi) (a n S.xi) ((star (a n)) S.xi) -
      modularEnergy lam (b S.xi) z q) atTop (𝓝 0) := by
    have hinner : Tendsto (fun n => (inner ℂ (b S.xi) (a n S.xi)).re) atTop
        (𝓝 (inner ℂ (b S.xi) z).re) :=
      Complex.continuous_re.tendsto _ |>.comp
        (tendsto_const_nhds.inner (𝕜 := ℂ) hxt)
    have ht : Tendsto (fun n => lam * ‖a n S.xi‖ ^ 2 +
        ‖(star (a n)) S.xi‖ ^ 2 - 2 * (inner ℂ (b S.xi) (a n S.xi)).re) atTop
        (𝓝 (lam * ‖z‖ ^ 2 + ‖S.J q‖ ^ 2 - 2 * (inner ℂ (b S.xi) z).re)) :=
      ((tendsto_const_nhds.mul (hxt.norm.pow 2)).add (hyt.norm.pow 2)).sub
        (tendsto_const_nhds.mul hinner)
    have ht' := ht.sub_const (modularEnergy lam (b S.xi) z q)
    simpa only [S.J.norm_map, modularEnergy, sub_self] using ht'
  have hbound (n : ℕ) :
      lam * ‖polarCutoff (a n) K S.xi-z‖ ^ 2 ≤
      modularEnergy lam (b S.xi) (a n S.xi) ((star (a n)) S.xi) -
        modularEnergy lam (b S.xi) z q := by
    have hc := cutoff_energy_le S.M S.xi (a n) b (ha n) hb hlam.le hK h1 h2
    have hi := S.D.halfGraph_energy_identity lam (b S.xi) hzq hqb
      (S.core_halfGraph (polarCutoff (a n) K) (polarCutoff_mem S.M (ha n) K))
    simp only [modularEnergy, S.J.norm_map] at hc hi ⊢
    nlinarith [sq_nonneg ‖S.J (star (polarCutoff (a n) K) S.xi) - q‖]
  have hct : Tendsto (fun n => polarCutoff (a n) K S.xi) atTop (𝓝 z) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hsmall := (tendsto_order.mp hEt).2 (lam*ε^2) (mul_pos hlam (sq_pos_of_pos hε))
    rcases eventually_atTop.mp hsmall with ⟨N,hN⟩
    refine ⟨N,fun n hn => ?_⟩
    rw [dist_eq_norm]
    have hn' := (hbound n).trans_lt (hN n hn)
    have hs : ‖polarCutoff (a n) K S.xi-z‖^2 < ε^2 := (mul_lt_mul_iff_right₀ hlam).mp hn'
    nlinarith [norm_nonneg (polarCutoff (a n) K S.xi-z)]
  exact bounded_orbit_lift S.M S.xi S.separating hK.le
    (mem_closure_of_tendsto hct (Filter.Eventually.of_forall (fun n =>
      ⟨polarCutoff (a n) K, polarCutoff_mem S.M (ha n) K, norm_polarCutoff_le _ hK, rfl⟩)))

end StandardModularData
end BoundedRecovery

end

end OAI


