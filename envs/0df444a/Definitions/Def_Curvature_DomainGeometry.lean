-- Prove2me | Definitions.Def_Curvature_DomainGeometry
-- name    : Curvature_DomainGeometry
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:14:26.743376+00:00
-- url     : https://prove2.me/theorems/83fad391-8466-4600-8e06-67c935c62fd8
-- title:
--   Projection, input correction and Algorithm 4 with a dyadic description
-- statement:
--   This file connects a compact convex domain $\mathcal K\subset\mathbb R^d$ with the internal run of Algorithm 4. It defines the Euclidean projection $\Pi_{\mathcal K}$ onto a nonempty compact convex set $\mathcal K$ and the corrected input: for a point $x$ with $n\coloneqq x-\Pi_{\mathcal K}(x)$ and an input $g$, the correction $\bar g$ removes the component of $g$ along $n$ when $\langle g,n\rangle<0$ and equals $g$ otherwise. The correction satisfies $\lVert\bar g\rVert_2\le\lVert g\rVert_2$ and $\langle g,\Pi_{\mathcal K}(x)-u\rangle\le\langle\bar g,x-u\rangle$ for every $u\in\mathcal K$.
--
--   Given an admissible description $(w_\circ,A,\ell,J)$ of $\mathcal K$, a bound $G>0$ and a parameter $\varepsilon\in(0,1]$, the run keeps an internal iterate $z_t\in\mathbb R^N$ started from the dyadic initialization. In round $t$, it predicts $w_t\coloneqq\Pi_{\mathcal K}(w_\circ+Az_t)$, then observes $g_t$, and then feeds the internal input $A^\top\bar g_t/G$, where $\bar g_t$ is the correction of $g_t$ at $x=w_\circ+Az_t$. Thus $w_t$ depends only on $g_1,\ldots,g_{t-1}$. With $r_t\coloneqq\langle g_t,w_t-u\rangle$, the file proves $2\sum_{t=1}^Tr_t-\varepsilon\sum_{t=1}^T|r_t|\le(192G/\varepsilon)\,C_{\mathcal D}(\mathcal K)$ for every $u\in\mathcal K$ and every horizon $T$, whenever $\lVert g_t\rVert_2\le G$ for all $t$.
--
--   The file also defines $\omega_{\psi_1}(\mathcal K)$ for a set $\mathcal K$ of coordinate vectors as the maximal subexponential mean width of its image in the Euclidean space $\mathbb R^d$ with the standard inner product, and compares this width with the representation cost and the diameter of $\mathcal K$. These objects appear in Sections 2.2 and 3.5 and Appendix B.8.
-- source:
--   arXiv:2611.27572v1, Appendix B.8 and Algorithm 4, pp. 42–43; Section 2.2, p. 5. https://arxiv.org/html/2611.27572v1#A2.SS8

import Definitions.Def_Curvature_BallState
import Definitions.Def_Curvature_DyadicRun
import Definitions.Def_Curvature_WidthAndSignGame
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

section
set_option autoImplicit false
namespace Curvature

variable {d N : ℕ}

theorem euclidean_norm (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ = norm₂ x.ofLp := by
  rw [EuclideanSpace.norm_eq, norm₂, dotProduct]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs, pow_two]

theorem euclidean_inner (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ x y = dotProduct x.ofLp y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

private theorem exists_domainProjection {K : Set (Vec d)} (hne : K.Nonempty)
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (x : Vec d) :
    ∃ w : K, (∀ u ∈ K, norm₂ (x - w.val) ≤ norm₂ (x - u)) ∧
      (∀ u ∈ K, 0 ≤ dotProduct (x - w.val) (w.val - u)) := by
  let e := (EuclideanSpace.equiv (Fin d) ℝ).symm
  let S := e '' K
  have he (y : Vec d) : (e y).ofLp = y := rfl
  have hScompact : IsCompact S := hcompact.image e.continuous
  have hSconvex : Convex ℝ S := hconvex.linear_image e.toLinearEquiv.toLinearMap
  obtain ⟨_, ⟨w, hw, rfl⟩, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex (hne.image e) hScompact.isComplete hSconvex (e x)
  refine ⟨⟨w, hw⟩, ?_, ?_⟩
  · intro u hu
    have hlower : BddBelow (Set.range (fun y : S => ‖e x - y.val‖)) :=
      ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
    have hle : ‖e x - e w‖ ≤ ‖e x - e u‖ :=
      hmin.le.trans (ciInf_le hlower ⟨e u, Set.mem_image_of_mem e hu⟩)
    simpa only [euclidean_norm, WithLp.ofLp_sub, he] using hle
  · intro u hu
    have hnormal := (norm_eq_iInf_iff_real_inner_le_zero hSconvex
      (Set.mem_image_of_mem e hw)).mp hmin (e u) (Set.mem_image_of_mem e hu)
    rw [← neg_sub u w, dotProduct_neg]
    apply neg_nonneg.mpr
    simpa only [euclidean_inner, WithLp.ofLp_sub, he] using hnormal

/-- The Euclidean projection onto a nonempty compact convex domain. -/
noncomputable def domainProjection {K : Set (Vec d)} (hne : K.Nonempty)
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (x : Vec d) : K :=
  (exists_domainProjection hne hcompact hconvex x).choose


theorem domainProjection_normal_nonneg {K : Set (Vec d)} (hne : K.Nonempty)
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (x : Vec d) {u : Vec d} (hu : u ∈ K) :
    let w := (domainProjection hne hcompact hconvex x).val
    0 ≤ dotProduct (x - w) (w - u) :=
  (exists_domainProjection hne hcompact hconvex x).choose_spec.2 u hu

/-- Remove the normal component of the input when its inner product with the normal is negative. -/
noncomputable def correctDomainInput (x w g : Vec d) : Vec d :=
  let n := x - w
  g - (min 0 (dotProduct g n) / norm₂ n ^ 2) • n


theorem correctDomainInput_norm_le (x w g : Vec d) :
    norm₂ (correctDomainInput x w g) ≤ norm₂ g := by
  let n := x - w
  change norm₂ (g - (min 0 (dotProduct g n) / norm₂ n ^ 2) • n) ≤ norm₂ g
  by_cases hgn : 0 ≤ dotProduct g n
  · simp [min_eq_left hgn]
  rw [min_eq_right (le_of_not_ge hgn)]
  have hnn : dotProduct n n ≠ 0 := by
    intro hzero
    have hn := dotProduct_self_eq_zero.mp hzero
    exact hgn (by simp [hn])
  let a := dotProduct g n / norm₂ n ^ 2
  have ha : a * dotProduct n n = dotProduct g n := by
    dsimp [a]
    rw [norm₂_sq, div_mul_cancel₀ _ hnn]
  change norm₂ (g - a • n) ≤ norm₂ g
  apply le_of_sq_le_sq _ (norm₂_nonneg g)
  rw [norm₂_sq, norm₂_sq]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm n g]
  rw [ha, sub_self, mul_zero, sub_zero]
  apply sub_le_self
  rw [← ha, ← mul_assoc, ← pow_two, ← norm₂_sq]
  exact mul_nonneg (sq_nonneg a) (sq_nonneg _)

theorem excess_le_correctDomainInput (x w g u : Vec d)
    (hnormal : 0 ≤ dotProduct (x - w) (w - u)) :
    excess g w u ≤ excess (correctDomainInput x w g) x u := by
  let n := x - w
  change dotProduct g (w - u) ≤
    dotProduct (g - (min 0 (dotProduct g n) / norm₂ n ^ 2) • n) (x - u)
  have hsplit : x - u = (w - u) + n := by
    dsimp [n]
    abel
  rw [hsplit]
  by_cases hgn : 0 ≤ dotProduct g n
  · simp only [min_eq_left hgn, zero_div, zero_smul, sub_zero, dotProduct_add]
    linarith
  rw [min_eq_right (le_of_not_ge hgn)]
  have hnn : dotProduct n n ≠ 0 := by
    intro hzero
    have hn := dotProduct_self_eq_zero.mp hzero
    exact hgn (by simp [hn])
  let a := dotProduct g n / norm₂ n ^ 2
  have ha : a * dotProduct n n = dotProduct g n := by
    dsimp [a]
    rw [norm₂_sq, div_mul_cancel₀ _ hnn]
  have ha_sign : a ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hgn) (sq_nonneg _)
  have hc := mul_nonpos_of_nonpos_of_nonneg ha_sign hnormal
  change dotProduct g (w - u) ≤ dotProduct (g - a • n) ((w - u) + n)
  simp only [sub_dotProduct, dotProduct_add, smul_dotProduct, smul_eq_mul]
  linarith only [ha, hc]

/-- One round of projection and input correction, expressed in the internal coordinates. -/
theorem domainProjectionTransfer {K : Set (Vec d)} (hne : K.Nonempty)
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (center : Vec d)
    (A : Matrix (Fin d) (Fin N) ℝ) (z v : Vec N) (hv : center + A.mulVec v ∈ K)
    (g : Vec d) {G : ℝ} (hG : 0 < G) (hg : norm₂ g ≤ G) :
    let x := center + A.mulVec z
    let w := (domainProjection hne hcompact hconvex x).val
    let corrected := correctDomainInput x w g
    let normalized := G⁻¹ • corrected
    let internal := A.transpose.mulVec normalized
    norm₂ corrected ≤ norm₂ g ∧ norm₂ normalized ≤ 1 ∧
      excess g w (center + A.mulVec v) / G ≤ excess internal z v := by
  dsimp only
  set x := center + A.mulVec z
  set w := (domainProjection hne hcompact hconvex x).val
  set corrected := correctDomainInput x w g
  have hnorm : norm₂ corrected ≤ norm₂ g := correctDomainInput_norm_le x w g
  refine ⟨hnorm, ?_, ?_⟩
  · rw [norm₂_smul, abs_of_pos (inv_pos.mpr hG), ← div_eq_inv_mul]
    exact (div_le_one hG).mpr (hnorm.trans hg)
  · have htransfer := excess_le_correctDomainInput x w g (center + A.mulVec v)
      (domainProjection_normal_nonneg hne hcompact hconvex x hv)
    have hdiff : x - (center + A.mulVec v) = A.mulVec (z - v) := by
      rw [Matrix.mulVec_sub]
      change center + A.mulVec z - (center + A.mulVec v) = _
      abel
    calc
      _ ≤ excess corrected x (center + A.mulVec v) / G :=
        div_le_div_of_nonneg_right htransfer hG.le
      _ = excess (A.transpose.mulVec (G⁻¹ • corrected)) z v := by
        unfold excess
        rw [hdiff, dotProduct_comm _ (z - v), Matrix.dotProduct_transpose_mulVec,
          smul_dotProduct, smul_eq_mul, div_eq_inv_mul]

/-- Transfer the signed excess over any finite prefix using the same comparator coordinates. -/
theorem signedRegret_domainProjection_le_internal {K : Set (Vec d)} (hne : K.Nonempty)
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (center : Vec d)
    (A : Matrix (Fin d) (Fin N) ℝ) (z : ℕ → Vec N) (v : Vec N) (hv : center + A.mulVec v ∈ K)
    (g : ℕ → Vec d) {G ε : ℝ} (hG : 0 < G) (hg : ∀ t, norm₂ (g t) ≤ G)
    (hε : 0 ≤ ε) (hε' : ε ≤ 2) (T : ℕ) :
    let x := fun t => center + A.mulVec (z t)
    let w := fun t => (domainProjection hne hcompact hconvex (x t)).val
    let r := fun t => excess (g t) (w t) (center + A.mulVec v)
    let rInternal := fun t =>
      excess (A.transpose.mulVec (G⁻¹ • correctDomainInput (x t) (w t) (g t))) (z t) v
    (∑ t ∈ Finset.range T, (2 * r t - ε * |r t|)) ≤
      G * (∑ t ∈ Finset.range T, (2 * rInternal t - ε * |rInternal t|)) := by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have hround := (domainProjectionTransfer hne hcompact hconvex center A (z t) v hv
    (g t) hG (hg t)).2.2
  have hmono := signedExcess_mono ε hε hε' hround
  dsimp only at hmono
  rw [abs_div, abs_of_pos hG, ← mul_div_assoc, ← mul_div_assoc, ← sub_div] at hmono
  simpa only [mul_comm G] using (div_le_iff₀ hG).mp hmono

end Curvature

end

section
set_option autoImplicit false
noncomputable section
namespace Curvature
variable {d N : ℕ} {K : Set (Vec d)}

def normalizedDomainInput (hne : K.Nonempty) (hc : IsCompact K) (hv : Convex ℝ K)
    (center : Vec d) (A : Matrix (Fin d) (Fin N) ℝ) (G : ℝ) (g : ℕ → Vec d)
    (t : ℕ) (z : Vec N) : Vec d :=
  let x := center + A.mulVec z
  G⁻¹ • correctDomainInput x (domainProjection hne hc hv x).val (g t)

theorem normalizedDomainInput_norm (hne : K.Nonempty) (hc : IsCompact K) (hv : Convex ℝ K)
    (center : Vec d) (A : Matrix (Fin d) (Fin N) ℝ) {G : ℝ} (hG : 0 < G)
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ G) (t : ℕ) (z : Vec N) :
    norm₂ (normalizedDomainInput hne hc hv center A G g t z) ≤ 1 := by
  rw [normalizedDomainInput, norm₂_smul, abs_of_pos (inv_pos.mpr hG), ← div_eq_inv_mul]
  exact (div_le_one hG).mpr ((correctDomainInput_norm_le _ _ _).trans (hg t))

namespace AdmissibleDescription
variable (D : AdmissibleDescription K)

def state (hne : K.Nonempty) (hc : IsCompact K) (hv : Convex ℝ K)
    (G ε : ℝ) (g : ℕ → Vec d) : ℕ → BallState D.N :=
  generalStateAfter (generalInitial (dyadicBase ε D.ℓ) (dyadicTerms ε D.ℓ D.J)) ε
    (dyadicSkip D.ℓ D.J) (fun t z => D.A.transpose.mulVec
      (normalizedDomainInput hne hc hv D.center D.A G g t z))

def play (hne : K.Nonempty) (hc : IsCompact K) (hv : Convex ℝ K)
    (G ε : ℝ) (g : ℕ → Vec d) (t : ℕ) : K :=
  domainProjection hne hc hv (D.center + D.A.mulVec (D.state hne hc hv G ε g t).z)

theorem play_prefix (hne : K.Nonempty) (hc : IsCompact K) (hv : Convex ℝ K)
    (G ε : ℝ) (g g' : ℕ → Vec d) (t : ℕ) (heq : ∀ i < t, g i = g' i) :
    D.play hne hc hv G ε g t = D.play hne hc hv G ε g' t := by
  suffices D.state hne hc hv G ε g t = D.state hne hc hv G ε g' t by simp [play, this]
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs := ih (fun i hi => heq i (Nat.lt_succ_of_lt hi))
    let update (s : BallState D.N) (feedback : Vec d) :=
      let x := D.center + D.A.mulVec s.z
      generalStep ε (dyadicSkip D.ℓ D.J t) (t+1) s (D.A.transpose.mulVec
        (G⁻¹ • correctDomainInput x (domainProjection hne hc hv x).val feedback))
    change update (D.state hne hc hv G ε g t) (g t) = update (D.state hne hc hv G ε g' t) (g' t)
    rw [hs, heq t (Nat.lt_succ_self t)]

theorem playedRegret (hne : K.Nonempty) (hc : IsCompact K) (hK : Convex ℝ K)
    {G ε : ℝ} (hG : 0 < G) (hε : 0 < ε) (hε' : ε ≤ 1)
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ G) (u : K) (T : ℕ) :
    let r := fun t => excess (g t) (D.play hne hc hK G ε g t).val u.val
    2 * (∑ t ∈ Finset.range T, r t) - ε * (∑ t ∈ Finset.range T, |r t|) ≤
      (192 * G / ε) * D.representationCost := by
  let s := D.state hne hc hK G ε g
  let v := D.minimizingCoefficients u
  obtain ⟨hv, hu, _⟩ := D.minimizingCoefficients_spec u
  let ambient := normalizedDomainInput hne hc hK D.center D.A G g
  let q := fun t => D.A.transpose.mulVec (ambient t (s t).z)
  have hb := generalInternalBound D.A hε hε' D.positive D.J D.columns ambient
    (normalizedDomainInput_norm hne hc hK D.center D.A hG g hg) T v hv
  let rin := fun t => excess (q t) (s t).z v
  let r := fun t => excess (g t) (D.play hne hc hK G ε g t).val u.val
  have hpos : 0 ≤ dotProduct (v-(s T).z)
      ((dyadicBase ε D.ℓ).mulVec (v-(s T).z)) := by
    simpa using (dyadicBase_posDef hε D.positive).posSemidef.dotProduct_mulVec_nonneg (v-(s T).z)
  change 2 * (∑ t ∈ Finset.range T, rin t) - ε * (∑ t ∈ Finset.range T, |rin t|) +
    dotProduct (v-(s T).z) ((dyadicBase ε D.ℓ).mulVec (v-(s T).z)) ≤
    (192/ε) * coefficientCost D.ℓ (dyadicFloor D.J) v at hb
  have hm := D.minimum_le_representationCost u
  have hi : 2 * (∑ t ∈ Finset.range T, rin t) - ε * (∑ t ∈ Finset.range T, |rin t|) ≤
      192/ε * D.representationCost := by
    apply le_trans _ (mul_le_mul_of_nonneg_left hm (by positivity))
    exact (le_add_of_nonneg_right hpos).trans hb
  have ht := signedRegret_domainProjection_le_internal hne hc hK D.center D.A (fun t => (s t).z)
    v (hu ▸ u.2) g hG hg hε.le (hε'.trans (by norm_num)) T
  dsimp only at ht
  change D.center + D.A.mulVec v = u.val at hu
  rw [hu] at ht
  change (∑ t ∈ Finset.range T, (2*r t - ε*|r t|)) ≤
    G*(∑ t ∈ Finset.range T, (2*rin t - ε*|rin t|)) at ht
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at ht
  exact ht.trans ((mul_le_mul_of_nonneg_left hi hG.le).trans_eq (by ring))

end AdmissibleDescription
end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature
variable {d : ℕ}

/-- The paper's Euclidean width for domains written as coordinate functions. -/
def coordinateWidth (K : Set (Vec d)) : ℝ :=
  subexponentialWidth ((WithLp.toLp 2) '' K : Set (EuclideanSpace ℝ (Fin d)))


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
open MeasureTheory
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

private def symmetricPointLaw (z : E) : Measure E :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac z + (2⁻¹ : ℝ≥0∞) • Measure.dirac (-z)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private theorem integrable_symmetricPointLaw {F : Type*} [NormedAddCommGroup F]
    (z : E) (f : E → F) : Integrable f (symmetricPointLaw z) := by
  unfold symmetricPointLaw
  rw [integrable_add_measure, integrable_smul_measure (by norm_num) (by norm_num),
    integrable_smul_measure (by norm_num) (by norm_num)]
  exact ⟨integrable_dirac (by simp), integrable_dirac (by simp)⟩

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private theorem integral_symmetricPointLaw {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (z : E) (f : E → F) :
    ∫ x, f x ∂symmetricPointLaw z = ((2 : ℝ)⁻¹) • f z + ((2 : ℝ)⁻¹) • f (-z) := by
  have h := integrable_symmetricPointLaw z f
  unfold symmetricPointLaw at h ⊢
  obtain ⟨h₁,h₂⟩ := integrable_add_measure.mp h
  rw [integral_add_measure h₁ h₂]
  simp [integral_smul_measure, integral_dirac]

private theorem symmetricPointLaw_admissible {z : E} (hz : ‖z‖ ≤ Real.log 2) :
    AdmissibleWidthLaw (symmetricPointLaw z) := by
  refine ⟨⟨?_⟩, integrable_symmetricPointLaw z id, ?_,
    fun v _ => integrable_symmetricPointLaw z _, ?_⟩
  · simp only [symmetricPointLaw, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    simpa only [one_div] using (ENNReal.add_halves (1 : ℝ≥0∞))
  · rw [integral_symmetricPointLaw]
    simp
  · intro v hv
    rw [integral_symmetricPointLaw]
    simp only [inner_neg_right, abs_neg, smul_eq_mul]
    have h := (abs_real_inner_le_norm v z).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hv).trans hz)
    have he := Real.exp_le_exp.mpr h
    rw [Real.exp_log (by norm_num)] at he
    linarith only [he]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
private theorem widthSupport_ge_point (K : Set E) (hb : Bornology.IsBounded K) (x : K) (z : E) :
    ⟪x.val,z⟫_ℝ ≤ widthSupport K z := by
  obtain ⟨R,_,hR⟩ := hb.exists_pos_norm_le
  apply le_ciSup (f := fun w : K => ⟪w.val,z⟫_ℝ) _ x
  refine ⟨R*‖z‖, ?_⟩
  rintro _ ⟨w,rfl⟩
  exact (real_inner_le_norm w.val z).trans
    (mul_le_mul_of_nonneg_right (hR _ w.prop) (norm_nonneg _))

/-- The width bounds the distance between any two domain points. -/
theorem subexponentialWidth_pair {K : Set E} [FiniteDimensional ℝ E] (hb : Bornology.IsBounded K)
    (x y : K) : (Real.log 2 / 2) * ‖x.val-y.val‖ ≤ subexponentialWidth K := by
  have hK : K.Nonempty := ⟨x.val,x.prop⟩
  have hbdd := widthValues_bddAbove K hK hb
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hxy : x.val-y.val = 0
  · rw [hxy, norm_zero, mul_zero]
    exact le_csSup hbdd (zero_mem_widthValues K hK)
  · let z := (Real.log 2 / ‖x.val-y.val‖) • (x.val-y.val)
    have hn := norm_pos_iff.mpr hxy
    have hnorm : ‖z‖ = Real.log 2 := by
      dsimp [z]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_mul_cancel₀ _ hn.ne']
    have hμ := symmetricPointLaw_admissible hnorm.le
    have hE := le_width_of_law K hbdd hμ
    rw [integral_symmetricPointLaw] at hE
    have hx := widthSupport_ge_point K hb x z
    have hy := widthSupport_ge_point K hb y (-z)
    have heq : ⟪x.val,z⟫_ℝ + ⟪y.val,-z⟫_ℝ = Real.log 2 * ‖x.val-y.val‖ := by
      rw [inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left]
      dsimp [z]
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    simp only [smul_eq_mul] at hE
    linarith only [hE,hx,hy,heq]

variable {d : ℕ}

theorem coordinateWidth_pair {K : Set (Vec d)} (hc : IsCompact K) (x y : K) :
    norm₂ (x.val-y.val) ≤ 2*coordinateWidth K / Real.log 2 := by
  let e := (EuclideanSpace.equiv (Fin d) ℝ).symm
  let L := e '' K
  let xe : L := ⟨e x.val, Set.mem_image_of_mem e x.prop⟩
  let ye : L := ⟨e y.val, Set.mem_image_of_mem e y.prop⟩
  have h := subexponentialWidth_pair (hc.image e.continuous).isBounded xe ye
  have hnorm : ‖xe.val-ye.val‖ = norm₂ (x.val-y.val) := by
    rw [euclidean_norm, WithLp.ofLp_sub]
    rfl
  rw [hnorm] at h
  change _ ≤ coordinateWidth K at h
  apply (le_div_iff₀ (Real.log_pos (by norm_num))).mpr
  linarith only [h]

end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory

namespace Curvature

private theorem young_exp_log (x t : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t) :
    t*x ≤ Real.exp x - 1 + t*(1 + Real.log (max 1 t)) := by
  rcases le_or_gt t 1 with h | h
  · rw [max_eq_left h, Real.log_one]
    nlinarith [mul_le_mul_of_nonneg_right h hx, Real.add_one_le_exp x]
  · rw [max_eq_right h.le]
    have hl := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x - Real.log t)) ht
    rw [Real.exp_sub, Real.exp_log (by positivity : 0 < t)] at hl
    field_simp [h.trans' zero_lt_one |>.ne'] at hl
    nlinarith

private theorem weighted_young {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) (v s : ℝ) :
    v*(ℓ*s) ≤ ℓ*h*(Real.exp |s| - 2) + ℓ*(h + |v| * (1 + Real.log (max 1 (|v|/h)))) := by
  have hy := mul_le_mul_of_nonneg_left (young_exp_log |s| (|v|/h) (abs_nonneg _)
    (div_nonneg (abs_nonneg _) hh.le)) (mul_nonneg hℓ.le hh.le)
  have ha : v*s ≤ |v| * |s| := (le_abs_self _).trans_eq (abs_mul ..)
  have hm := mul_le_mul_of_nonneg_left ha hℓ.le
  calc
    v * (ℓ*s) ≤ ℓ*(|v| * |s|) := by linarith
    _ = ℓ*h*((|v|/h)*|s|) := by field_simp
    _ ≤ _ := hy
    _ = _ := by field_simp; ring

variable {d : ℕ} {K : Set (Vec d)} (D : AdmissibleDescription K)

theorem width_le_representationCost (hne : K.Nonempty) (hc : IsCompact K) :
    coordinateWidth K ≤ D.representationCost := by
  classical
  let e := (EuclideanSpace.equiv (Fin d) ℝ).symm
  let S := e '' K
  have hS : S.Nonempty := hne.image e
  let : Nonempty S := hS.to_subtype
  let h := dyadicFloor D.J
  let col (j : Fin D.N) := e (fun i => D.A i j)
  let dir (j : Fin D.N) := (D.ℓ j)⁻¹ • col j
  have hcol (j : Fin D.N) : ‖col j‖ ≤ D.ℓ j := by
    rw [euclidean_norm]; exact D.columns j
  have hdir (j : Fin D.N) : ‖dir j‖ ≤ 1 := by
    dsimp only [dir]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (D.positive j))]
    exact (inv_mul_le_iff₀ (D.positive j)).mpr (by simpa using hcol j)
  have hrepr (u : K) :
      e u.val = e D.center + ∑ j, D.minimizingCoefficients u j • col j := by
    have hu := (D.minimizingCoefficients_spec u).2.1
    rw [← hu]
    apply WithLp.ofLp_injective 2
    ext i
    simp [col, e, Matrix.mulVec, dotProduct, mul_comm, WithLp.ofLp_sum]
  let F (j : Fin D.N) (z : EuclideanSpace ℝ (Fin d)) :=
    D.ℓ j * h j * (Real.exp |⟪dir j,z⟫_ℝ| - 2)
  have hs (z : EuclideanSpace ℝ (Fin d)) : widthSupport S z ≤
      ⟪e D.center,z⟫_ℝ + ∑ j, F j z + D.representationCost := by
    apply ciSup_le
    rintro ⟨_, x, hx, rfl⟩
    let u : K := ⟨x,hx⟩
    change ⟪e u.val,z⟫_ℝ ≤ _
    rw [hrepr u, inner_add_left, sum_inner]
    have hj (j : Fin D.N) : ⟪D.minimizingCoefficients u j • col j,z⟫_ℝ ≤ F j z +
        D.ℓ j * (h j + |D.minimizingCoefficients u j| *
          (1 + Real.log (max 1 (|D.minimizingCoefficients u j| / h j)))) := by
      have heq : D.ℓ j * ⟪dir j,z⟫_ℝ = ⟪col j,z⟫_ℝ := by
        simp [dir, real_inner_smul_left, (D.positive j).ne']
      rw [real_inner_smul_left, ← heq]
      exact weighted_young (D.positive j) (dyadicFloor_pos D.J j) _ _
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
    rw [Finset.sum_add_distrib] at hsum
    have hmin := D.minimum_le_representationCost u
    unfold coefficientCost at hmin
    dsimp only [h] at hsum
    linarith
  apply width_le_of_forall S hS
  intro μ hμ
  let := hμ.prob
  have hI (j : Fin D.N) : Integrable (F j) μ :=
    ((hμ.exp_integrable (dir j) (hdir j)).sub (integrable_const 2)).const_mul _
  have hmean (j : Fin D.N) : (∫ z, F j z ∂μ) ≤ 0 := by
    simp only [F, integral_const_mul, integral_sub (hμ.exp_integrable _ (hdir j))
      (integrable_const 2), integral_const, probReal_univ, one_smul]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (D.positive j).le (dyadicFloor_pos D.J j).le)
      (sub_nonpos.mpr (hμ.exp_le _ (hdir j)))
  have hC := hμ.integrable.const_inner (𝕜 := ℝ) (e D.center)
  have hsum := integrable_finsetSum Finset.univ (fun j _ => hI j)
  have hmono := integral_mono (widthSupport_integrable S hS (hc.image e.continuous).isBounded hμ)
    ((hC.add hsum).add (integrable_const D.representationCost)) hs
  change (∫ z, widthSupport S z ∂μ) ≤
    ∫ z, (⟪e D.center,z⟫_ℝ + ∑ j, F j z) + D.representationCost ∂μ at hmono
  have hlin : Integrable (fun z => ⟪e D.center,z⟫_ℝ + ∑ j, F j z) μ := hC.add hsum
  rw [integral_add hlin (integrable_const D.representationCost), integral_add hC hsum,
    integral_finsetSum _ (fun j _ => hI j), integral_inner hμ.integrable, hμ.centered,
    inner_zero_right, zero_add, integral_const, probReal_univ, one_smul] at hmono
  linarith [Finset.sum_nonpos (s := Finset.univ) (fun j _ => hmean j)]

end Curvature

end
end


