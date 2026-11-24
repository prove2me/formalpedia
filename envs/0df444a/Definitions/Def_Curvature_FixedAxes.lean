-- Prove2me | Definitions.Def_Curvature_FixedAxes
-- name    : Curvature_FixedAxes
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:15:41.289808+00:00
-- url     : https://prove2.me/theorems/169746bf-c507-4673-9c72-182fb993a9ec
-- title:
--   Fixed diagonal initialization along orthogonal axes
-- statement:
--   This file defines the fixed-matrix initialization that Algorithm 4 uses when the domain is the image of a unit $\ell_p$ ball with $p\ge2$ under an affine map with orthogonal columns. Fix an integer $N\ge1$ and a parameter $\varepsilon\in(0,1]$. Let $a\in(0,\infty)^N$ be the axis lengths and $q\in[1,2]$ the conjugate exponent of $p$, so that $p=q/(q-1)$ for $q>1$ and $p=\infty$ for $q=1$. The unit coefficient set is $\{v\in\mathbb R^N:\lVert v\rVert_p\le1\}$. With the scale $\lVert a\rVert_q$ and the weights $b_i\coloneqq a_i/\lVert a\rVert_q$, the exact initial matrix is diagonal with entries
--
--   $$
--   D_i\coloneqq\frac{10\,\lVert a\rVert_q}{\varepsilon}\,b_i^{\,2-q},\qquad i=1,\ldots,N.
--   $$
--
--   A run uses a diagonal matrix $H$ with $D_i\le H_{ii}\le3D_i$, no initial terms, and the creation threshold $L/(t+1)^4$ in round $t$, where $L\coloneqq(10/\varepsilon)\operatorname{tr}(SH^{-1})$ and $S\coloneqq\operatorname{diag}(a_1^2,\ldots,a_N^2)$. One can use the exact diagonal $H_{ii}=D_i$. For equal axis lengths, one can also round the factor $N^{1-1/q}$ up to a power of two at most $3N^{1-1/q}$. For ellipsoids ($q=2$), one can start at $\max_i a_i$ and double until the value is at least $\lVert a\rVert_2$. For boxes ($q=1$), the exact diagonal simplifies to $D_i=10a_i/\varepsilon$.
--
--   Suppose that the internal inputs $\widetilde g_t$ satisfy $S-\widetilde g_t\widetilde g_t^\top\succeq0$. For the internal iterates $z_t$ and a point $v$ of the unit coefficient set, write $r_t\coloneqq\langle\widetilde g_t,z_t-v\rangle$. The file proves $2\sum_{t=1}^Tr_t-\varepsilon\sum_{t=1}^T|r_t|\le41\lVert a\rVert_q/\varepsilon$ for every such $v$ and every horizon $T$. If $A^\top A=S$ and a compact set $\mathcal K\subset\mathbb R^d$ contains $w_\circ+Av$ for every $v$ in the unit coefficient set, it also proves $\lVert a\rVert_q/4\le\omega_{\psi_1}(\mathcal K)$. Together, these give the guarantee of Algorithm 4 for $\ell_p$ balls with $p\ge2$, ellipsoids and boxes (Appendices B.1, B.6 and B.7).
-- source:
--   arXiv:2611.27572v1, Appendix B.7, pp. 40–42; Appendix D.3, pp. 54–55. https://arxiv.org/html/2611.27572v1#A2.SS7

import Definitions.Def_Curvature_DomainGeometry
import Definitions.Def_Curvature_DyadicRun
import Definitions.Def_Curvature_WeightedTrace
import Definitions.Def_Curvature_WidthAndSignGame
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.Nat.Log

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {N : ℕ}

def fixedAxisScale (a : Vec N) (q : ℝ) := (∑ i, a i ^ q) ^ q⁻¹

def fixedAxisWeight (a : Vec N) (q : ℝ) (i : Fin N) : ℝ := a i / fixedAxisScale a q

def fixedAxisBase (a : Vec N) (q ε : ℝ) : Mat N :=
  Matrix.diagonal fun i => (10 * fixedAxisScale a q / ε) * (fixedAxisWeight a q i)^(2-q)

def fixedUnitCoeffs (q : ℝ) (v : Vec N) : Prop :=
  if q=1 then ∀ i, |v i| ≤ 1 else ∑ i, |v i| ^ (q/(q-1)) ≤ 1

variable [NeZero N] {a : Vec N} {q ε : ℝ}

theorem fixedAxisScale_pos (ha : ∀ i, 0 < a i) (q : ℝ) : 0 < fixedAxisScale a q :=
  Real.rpow_pos_of_pos (Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (ha i) q) Finset.univ_nonempty) _

theorem fixedAxisWeight_pos (ha : ∀ i, 0 < a i) (q : ℝ) (i : Fin N) : 0 < fixedAxisWeight a q i :=
  div_pos (ha i) (fixedAxisScale_pos ha q)

theorem fixedAxisWeight_sum (ha : ∀ i, 0 < a i) (hq : 0 < q) :
    ∑ i, (fixedAxisWeight a q i)^q = 1 := by
  have hS := fixedAxisScale_pos ha q
  have he (i : Fin N) : (fixedAxisWeight a q i)^q = (a i)^q / (fixedAxisScale a q)^q :=
    Real.div_rpow (ha i).le hS.le q
  simp_rw [he]
  rw [← Finset.sum_div, div_eq_one_iff_eq (Real.rpow_pos_of_pos hS q).ne']
  unfold fixedAxisScale
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ => (Real.rpow_pos_of_pos (ha i) q).le),
    inv_mul_cancel₀ hq.ne', Real.rpow_one]

theorem fixedAxis_energy_le (ha : ∀ i, 0 < a i) (hq : 1 ≤ q) (hq' : q ≤ 2)
    (v : Vec N) (hv : fixedUnitCoeffs q v) :
    (∑ i, (fixedAxisWeight a q i)^(2-q) * v i ^ 2) ≤ 1 := by
  let b := fixedAxisWeight a q
  have hb := fixedAxisWeight_pos ha q
  have hqp : 0 < q := by linarith
  have hsum := fixedAxisWeight_sum ha hqp
  by_cases hone : q=1
  · subst q
    simp [fixedUnitCoeffs] at hv
    simp at hsum ⊢
    refine le_trans (Finset.sum_le_sum (g := fun i => fixedAxisWeight a 1 i) ?_) hsum.le
    intro i _
    have hi : v i ^ 2 ≤ 1 := by nlinarith [sq_abs (v i), hv i, abs_nonneg (v i)]
    norm_num only [show (2:ℝ)-1=1 by norm_num, Real.rpow_one]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hi (hb i).le
  · let p := q/(q-1)
    let x := (2-q)/q
    let y := 2/p
    have hq1 : 0 < q-1 := by grind
    have hp : 0 < p := div_pos hqp hq1
    have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr hq') hqp.le
    have hy : 0 ≤ y := (div_pos (by norm_num) hp).le
    have hxy : x + y = 1 := by dsimp [x,y,p]; field_simp; ring
    have hstats : ∑ i, |v i|^p ≤ 1 := by simpa [fixedUnitCoeffs, hone, p] using hv
    calc
      _ ≤ ∑ i, (x * (b i)^q + y * |v i|^p) := by
        apply Finset.sum_le_sum
        intro i _
        have h := Real.geom_mean_le_arith_mean2_weighted hx hy
          (Real.rpow_pos_of_pos (hb i) q).le (Real.rpow_nonneg (abs_nonneg (v i)) p) hxy
        rw [← Real.rpow_mul (hb i).le, ← Real.rpow_mul (abs_nonneg (v i)),
          show q*x = 2-q by dsimp [x]; field_simp, show p*y = 2 by dsimp [y]; field_simp,
          Real.rpow_two, sq_abs] at h
        exact h
      _ = x*(∑ i, (b i)^q) + y*(∑ i, |v i|^p) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 1 := by rw [show ∑ i, (b i)^q = 1 from hsum]; nlinarith [mul_le_mul_of_nonneg_left hstats hy]


theorem fixedAxisBase_quadratic (ha : ∀ i, 0 < a i) (hq : 1 ≤ q) (hq' : q ≤ 2) (hε : 0 < ε)
    (v : Vec N) (hv : fixedUnitCoeffs q v) :
    dotProduct v ((fixedAxisBase a q ε).mulVec v) ≤ 10 * fixedAxisScale a q / ε := by
  have he := fixedAxis_energy_le ha hq hq' v hv
  calc
    _ = (10 * fixedAxisScale a q / ε)*∑ i, (fixedAxisWeight a q i)^(2-q)*v i^2 := by
      simp only [fixedAxisBase, Matrix.mulVec_diagonal, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_left he (div_nonneg (mul_nonneg (by norm_num) (fixedAxisScale_pos ha q).le) hε.le)

theorem fixedAxisBase_trace (ha : ∀ i, 0 < a i) (hq : 0 < q) (hε : 0 < ε) :
    (Matrix.diagonal (fun i => a i^2) * (fixedAxisBase a q ε)⁻¹).trace = ε * fixedAxisScale a q / 10 := by
  let S := fixedAxisScale a q
  let b := fixedAxisWeight a q
  let D := fun i => (10*S/ε)*(b i)^(2-q)
  have hS := fixedAxisScale_pos ha q
  have hb := fixedAxisWeight_pos ha q
  have hD (i : Fin N) : 0 < D i := mul_pos (div_pos (mul_pos (by norm_num) hS) hε)
    (Real.rpow_pos_of_pos (hb i) _)
  have hinv : (fixedAxisBase a q ε)⁻¹ = Matrix.diagonal fun i => (D i)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    change Matrix.diagonal D * _ = _
    rw [Matrix.diagonal_mul_diagonal]
    simp [fun i => (hD i).ne', Matrix.diagonal_one]
  rw [hinv, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  calc
    _ = (ε*S/10)*∑ i, (b i)^q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have ha' : a i = S*b i := by dsimp [b, fixedAxisWeight, S]; field_simp
      have hpow : b i ^ (2-q) * b i ^ q = b i ^ 2 := by
        rw [← Real.rpow_add (hb i), sub_add_cancel, Real.rpow_two]
      change a i^2 * (D i)⁻¹ = _
      rw [← div_eq_mul_inv, div_eq_iff (hD i).ne', ha']
      dsimp only [D]
      field_simp
      linear_combination -S^2*hpow
    _ = _ := by rw [show ∑ i, (b i)^q = 1 from fixedAxisWeight_sum ha hq, mul_one]

end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Curvature

variable {N d : ℕ} [NeZero N]

def fixedAxisComparator (a : Vec N) (q : ℝ) (σ : Fin N → Bool) (i : Fin N) : ℝ :=
  (fixedAxisWeight a q i)^(q-1)*SignGame.sign (σ i)

theorem fixedAxisComparator_mem {q : ℝ} {a : Vec N} (ha : ∀ i, 0 < a i) (hq : 1 ≤ q)
    (σ : Fin N → Bool) : fixedUnitCoeffs q (fixedAxisComparator a q σ) := by
  by_cases h : q=1
  · subst q
    simp [fixedUnitCoeffs, fixedAxisComparator]
  · have hqp : 0 < q := by linarith
    simp only [fixedUnitCoeffs, if_neg h]
    refine le_of_eq (Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (fixedAxisWeight_sum ha hqp))
    rw [fixedAxisComparator, abs_mul, SignGame.abs_sign, mul_one,
      abs_of_pos (Real.rpow_pos_of_pos (fixedAxisWeight_pos ha q i) _),
      ← Real.rpow_mul (fixedAxisWeight_pos ha q i).le]
    congr 1
    field_simp

theorem fixedAxisWidth_lower {K : Set (Vec d)} (hK : IsCompact K) (center : Vec d)
    (A : Matrix (Fin d) (Fin N) ℝ) {a : Vec N} (ha : ∀ i, 0 < a i)
    (hgram : A.transpose*A = Matrix.diagonal fun i => a i^2) {q : ℝ} (hq : 1 ≤ q)
    (hbody : ∀ v, fixedUnitCoeffs q v → center + A.mulVec v ∈ K) :
    fixedAxisScale a q / 4 ≤ subexponentialWidth ((EuclideanSpace.equiv (Fin d) ℝ).symm '' K) := by
  let E := (EuclideanSpace.equiv (Fin d) ℝ).symm
  let e := fun i : Fin N => E (fun j => A j i / a i)
  let b := fixedAxisWeight a q
  let S := fixedAxisScale a q
  have he : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    have hm := congrArg (fun M : Mat N => M i j) hgram
    change (∑ k, A k i*A k j) = (Matrix.diagonal fun i => a i^2) i j at hm
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (star (fun k => A k j/a j)) ⬝ᵥ (fun k => A k i/a i) = _
    simp only [star_trivial, dotProduct]
    have hdiv : (∑ k, A k j/a j*(A k i/a i)) = (∑ k, A k i*A k j)/(a j*a i) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hdiv, hm]
    by_cases h : i=j
    · subst j; simp [pow_two, (ha i).ne']
    · simp [h]
  have hcoef : ∑ i, a i*(b i)^(q-1) = S := by
    have hb (i : Fin N) : a i*(b i)^(q-1) = S*(b i)^q := by
      have heq : a i = S*b i := by
        dsimp [b,S,fixedAxisWeight]
        field_simp [(fixedAxisScale_pos ha q).ne']
      calc
        _ = S*(b i * (b i)^(q-1)) := by rw [heq]; ring
        _ = S*(b i)^(1+(q-1)) := by rw [Real.rpow_add (fixedAxisWeight_pos ha q i), Real.rpow_one]
        _ = _ := by rw [show 1+(q-1)=q by ring]
    simp_rw [hb]
    rw [← Finset.mul_sum, show ∑ i, (b i)^q=1 from fixedAxisWeight_sum ha (by linarith), mul_one]
  rw [← show S/4 = fixedAxisScale a q/4 from rfl, ← hcoef]
  apply signVertices_width (E '' K) (hK.image E.continuous).isBounded (E center) e he
  intro σ
  refine ⟨center + A.mulVec (fixedAxisComparator a q σ), hbody _ (fixedAxisComparator_mem ha hq σ), ?_⟩
  apply E.symm.injective
  simp only [ContinuousLinearEquiv.symm_apply_apply, map_add, map_sum, map_smul, e]
  ext j
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct, fixedAxisComparator]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp [b]
  field_simp [(ha i).ne']

def fixedAdditionScale (S H : Mat N) (ε : ℝ) : ℝ := (10/ε)*(S*H⁻¹).trace

def fixedThreshold (L : ℝ) (i : ℕ) : ℝ := L/((i : ℝ)+2)^4

def fixedAxisDiagonal (a : Vec N) (q ε : ℝ) (i : Fin N) : ℝ :=
  (10 * fixedAxisScale a q / ε) * (fixedAxisWeight a q i)^(2-q)

omit [NeZero N] in
private theorem diagTrace (a D : Vec N) (hD : ∀ i, 0 < D i) :
    (Matrix.diagonal (fun i => a i^2) * (Matrix.diagonal D)⁻¹).trace =
      ∑ i, a i^2/D i := by
  have hi : (Matrix.diagonal D)⁻¹ = Matrix.diagonal fun i => (D i)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    simp [fun i => (hD i).ne', Matrix.diagonal_one]
  rw [hi, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [div_eq_mul_inv]

theorem fixedRoundedAxisBound {q ε : ℝ} {a D : Vec N} (ha : ∀ i, 0 < a i)
    (hq : 1 ≤ q) (hq' : q ≤ 2) (hε : 0 < ε) (hε' : ε ≤ 1)
    (hlo : ∀ i, fixedAxisDiagonal a q ε i ≤ D i)
    (hhi : ∀ i, D i ≤ 3*fixedAxisDiagonal a q ε i) (feed : ℕ → Vec N → Vec N)
    (hinput : ∀ t, let S := Matrix.diagonal (fun i => a i^2)
                   let H := Matrix.diagonal D
                   let z := (fixedRun H ε (fixedThreshold (fixedAdditionScale S H ε)) feed t).z
                   (S-Matrix.vecMulVec (feed t z) (feed t z)).PosSemidef)
    (v : Vec N) (hv : fixedUnitCoeffs q v) (T : ℕ) :
    let S := Matrix.diagonal (fun i => a i^2)
    let H := Matrix.diagonal D
    let s := fixedRun H ε (fixedThreshold (fixedAdditionScale S H ε)) feed
    let r := fun i => excess (feed i (s i).z) (s i).z v
    2*(∑ i ∈ Finset.range T, r i)-ε*(∑ i ∈ Finset.range T, |r i|)+
      dotProduct (v-(s T).z) (H.mulVec (v-(s T).z)) ≤ 41*fixedAxisScale a q/ε := by
  let S := Matrix.diagonal (fun i => a i^2)
  let H := Matrix.diagonal D
  let L := fixedAdditionScale S H ε
  let F := fixedAxisScale a q
  have hF := fixedAxisScale_pos ha q
  have hbase (i : Fin N) : 0 < fixedAxisDiagonal a q ε i := mul_pos
    (div_pos (mul_pos (by norm_num) hF) hε) (Real.rpow_pos_of_pos (fixedAxisWeight_pos ha q i) _)
  have hD : ∀ i, 0 < D i := fun i => (hbase i).trans_le (hlo i)
  have hS : S.PosSemidef := Matrix.PosSemidef.diagonal (fun i => sq_nonneg (a i))
  have hH : H.PosDef := Matrix.PosDef.diagonal hD
  have htrace : (S*H⁻¹).trace ≤ ε*F/10 := by
    rw [← fixedAxisBase_trace ha (show 0<q by linarith) hε]
    rw [show fixedAxisBase a q ε = Matrix.diagonal (fixedAxisDiagonal a q ε) from rfl,
      diagTrace _ _ hD, diagTrace _ _ hbase]
    exact Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_left (sq_nonneg _) (hbase i) (hlo i)
  have hL : 0 ≤ L := by
    dsimp [L, fixedAdditionScale, H, S]
    rw [diagTrace _ _ hD]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hD i).le)
  have hLupper : L ≤ F := by
    change (10/ε)*(S*H⁻¹).trace ≤ F
    have h := mul_le_mul_of_nonneg_left htrace (by positivity : 0 ≤ 10/ε)
    exact h.trans_eq (by field_simp)
  have hQuad : dotProduct v (H.mulVec v) ≤ 30*F/ε := by
    have he := fixedAxisBase_quadratic ha hq hq' hε v hv
    have hform (U : Vec N) : dotProduct v ((Matrix.diagonal U).mulVec v) =
        ∑ i, U i * v i^2 := by
      simp only [Matrix.mulVec_diagonal, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [show fixedAxisBase a q ε = Matrix.diagonal (fixedAxisDiagonal a q ε) from rfl, hform] at he
    rw [show H = Matrix.diagonal D from rfl, hform]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_right (hhi i) (sq_nonneg (v i)))
    calc
      _ ≤ _ := hsum
      _ = 3*(∑ i, fixedAxisDiagonal a q ε i * v i^2) := by simp only [Finset.mul_sum, mul_assoc]
      _ ≤ _ := (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 3)).trans_eq (by dsimp [F]; ring)
  have hbudget := generalSkipTail L hL T
  have hz (t : ℕ) : 0 ≤ fixedThreshold L t := div_nonneg hL (by positivity)
  have hl := fixedInitialization H S hH hS hε hε' (fixedThreshold L) hz feed hinput v T
  apply hl.trans
  have htr' : (100/ε^2)*(S*H⁻¹).trace ≤ 10*F/ε :=
    (mul_le_mul_of_nonneg_left htrace (by positivity)).trans_eq (by field_simp; ring)
  have hbudget' : (∑ i ∈ Finset.range T, fixedThreshold L i) ≤ F/8 := by
    refine hbudget.trans ?_
    nlinarith [mul_nonneg hL (by positivity : 0 ≤ 1/((T:ℝ)+1))]
  have hFle : F ≤ F/ε := (le_div_iff₀ hε).mpr (by nlinarith [mul_le_mul_of_nonneg_left hε' hF.le])
  change _ ≤ 41*F/ε
  have hF0 : 0 ≤ F/ε := div_nonneg hF.le hε.le
  calc
    _ ≤ (30*F/ε + 10*F/ε) + F/8 := add_le_add (add_le_add hQuad htr') hbudget'
    _ ≤ (30*F/ε + 10*F/ε) + F/ε := by
      apply add_le_add le_rfl
      exact (by linarith only [show 0 ≤ F from hF.le] : F/8 ≤ F).trans hFle
    _ = _ := by ring


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {N : ℕ} [NeZero N]

theorem fixedAxisDiagonal_eq {a : Vec N} (ha : ∀ i, 0 < a i) (q ε : ℝ) (i : Fin N) :
    fixedAxisDiagonal a q ε i = (10/ε)*(fixedAxisScale a q)^(q-1)*(a i)^(2-q) := by
  let S := fixedAxisScale a q
  have hS : 0 < S := fixedAxisScale_pos ha q
  have hprod : S^(q-1)*S^(2-q) = S := by
    rw [← Real.rpow_add hS, show q-1+(2-q)=1 by ring, Real.rpow_one]
  change 10*S/ε * (a i/S)^(2-q) = (10/ε)*S^(q-1)*a i^(2-q)
  rw [Real.div_rpow (ha i).le hS.le]
  have hdiv : S/S^(2-q)=S^(q-1) := (div_eq_iff (Real.rpow_pos_of_pos hS _).ne').mpr hprod.symm
  calc
    _ = (10/ε)*(a i)^(2-q)*(S/S^(2-q)) := by ring
    _ = _ := by rw [hdiv]; ring

theorem fixedAxisDiagonal_constant {q R ε : ℝ} (hq : 0 < q) (hR : 0 < R) (i : Fin N) :
    fixedAxisDiagonal (fun _ => R) q ε i = (10*R/ε)*(N : ℝ)^(1-q⁻¹) := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hS : fixedAxisScale (fun _ : Fin N => R) q = (N : ℝ)^q⁻¹ * R := by
    simp only [fixedAxisScale, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Real.mul_rpow hN.le (Real.rpow_pos_of_pos hR _).le, ← Real.rpow_mul hR.le,
      mul_inv_cancel₀ hq.ne', Real.rpow_one]
  rw [fixedAxisDiagonal_eq (fun _ => hR), hS, Real.mul_rpow (Real.rpow_pos_of_pos hN _).le hR.le,
    ← Real.rpow_mul hN.le, show q⁻¹*(q-1)=1-q⁻¹ by field_simp]
  have hr : R^(q-1)*R^(2-q)=R := by
    rw [← Real.rpow_add hR, show q-1+(2-q)=1 by ring, Real.rpow_one]
  linear_combination (10/ε)*(N : ℝ)^(1-q⁻¹)*hr

def ballRoundExponent (N : ℕ) (q : ℝ) : ℕ := ⌈(Nat.clog 2 N : ℝ)*(1-q⁻¹)⌉₊

theorem ballRoundExponent_bounds {q : ℝ} (hq : 1 ≤ q) (hq' : q ≤ 2) :
    (N : ℝ)^(1-q⁻¹) ≤ (2:ℝ)^ballRoundExponent N q ∧
      (2:ℝ)^ballRoundExponent N q ≤ 3*(N : ℝ)^(1-q⁻¹) := by
  let θ := 1-q⁻¹
  let m := Nat.clog 2 N
  let k := ballRoundExponent N q
  have hqp : 0 < q := by linarith
  have hθ : 0 ≤ θ := sub_nonneg.mpr ((inv_le_one₀ hqp).mpr hq)
  have hθ' : θ ≤ 1/2 := by
    change 1-q⁻¹ ≤ 1/2
    have hh := (inv_anti₀ hqp hq' : (2:ℝ)⁻¹ ≤ q⁻¹)
    linarith
  have hm : (N : ℝ) ≤ (2:ℝ)^m := by exact_mod_cast (Nat.le_pow_clog (by decide : 1 < 2) N)
  have hm' : (2:ℝ)^m ≤ 2 * (N:ℝ) := by
    cases h : m with
    | zero => simp only [pow_zero]; exact_mod_cast (show 1 ≤ 2*N by have := NeZero.pos N; omega)
    | succ j =>
      have hpre : j < Nat.clog 2 N := by change j<m; omega
      have hlt : (2:ℝ)^j < (N : ℝ) := by exact_mod_cast Nat.pow_lt_of_lt_clog hpre
      rw [pow_succ]; linarith
  have hk : (m:ℝ)*θ ≤ (k:ℝ) := Nat.le_ceil _
  have hk' : (k:ℝ) < (m:ℝ)*θ+1 := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) hθ)
  have hpow : ((2:ℝ)^m)^θ = (2:ℝ)^((m:ℝ)*θ) := by rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have htwo : (2:ℝ)^θ ≤ 3/2 := by
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hθ').trans ?_
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  change (N:ℝ)^θ ≤ (2:ℝ)^k ∧ (2:ℝ)^k ≤ 3*(N:ℝ)^θ
  constructor
  · calc
      _ ≤ ((2:ℝ)^m)^θ := Real.rpow_le_rpow (Nat.cast_nonneg _) hm hθ
      _ = _ := hpow
      _ ≤ (2:ℝ)^(k:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hk
      _ = _ := Real.rpow_natCast _ _
  · calc
      _ = (2:ℝ)^(k:ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2:ℝ)^((m:ℝ)*θ+1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hk'.le
      _ = ((2:ℝ)^m)^θ*2 := by rw [Real.rpow_add_one (by norm_num : (2:ℝ)≠0), hpow]
      _ ≤ (2*(N:ℝ))^θ*2 := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hm' hθ) (by norm_num)
      _ ≤ _ := by
        rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)]
        nlinarith [mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (Nat.cast_nonneg N) θ)]

def roundedBallDiagonal (N : ℕ) (q R ε : ℝ) : ℝ := 10*R/ε*(2:ℝ)^ballRoundExponent N q

theorem roundedBallDiagonal_bounds {q R ε : ℝ} (hq : 1 ≤ q) (hq' : q ≤ 2)
    (hR : 0 < R) (hε : 0 < ε) (i : Fin N) :
    fixedAxisDiagonal (fun _ => R) q ε i ≤ roundedBallDiagonal N q R ε ∧
      roundedBallDiagonal N q R ε ≤ 3*fixedAxisDiagonal (fun _ => R) q ε i := by
  rw [fixedAxisDiagonal_constant (by linarith) hR]
  obtain ⟨hl,hh⟩ := ballRoundExponent_bounds (N := N) hq hq'
  have hpos : 0 ≤ 10*R/ε := by positivity
  exact ⟨mul_le_mul_of_nonneg_left hl hpos, (mul_le_mul_of_nonneg_left hh hpos).trans_eq (by ring)⟩

def ellipsoidMax (a : Vec N) := Finset.univ.sup' Finset.univ_nonempty a

def ellipsoidDoublings (a : Vec N) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, (∑ i, a i^2) ≤ ((2:ℝ)^k * ellipsoidMax a)^2 then Nat.find h else 0

def roundedEllipsoidDiagonal (a : Vec N) (ε : ℝ) : ℝ :=
  (10/ε)*((2:ℝ)^ellipsoidDoublings a * ellipsoidMax a)

theorem roundedEllipsoidDiagonal_bounds {a : Vec N} (ha : ∀ i, 0 < a i) {ε : ℝ}
    (hε : 0 < ε) (i : Fin N) :
    fixedAxisDiagonal a 2 ε i ≤ roundedEllipsoidDiagonal a ε ∧
      roundedEllipsoidDiagonal a ε ≤ 3*fixedAxisDiagonal a 2 ε i := by
  classical
  let S := fixedAxisScale a 2
  let M := ellipsoidMax a
  have hS : 0 < S := fixedAxisScale_pos ha _
  have hM : 0 < M := (ha i).trans_le (Finset.le_sup' a (Finset.mem_univ i))
  have hS2 : S^2 = ∑ j, a j^2 := by
    dsimp [S, fixedAxisScale]
    simp_rw [Real.rpow_two]
    rw [← Real.rpow_two, ← Real.rpow_mul (Finset.sum_nonneg fun j _ => sq_nonneg (a j))]
    norm_num
  let P := fun k : ℕ => (∑ j, a j^2) ≤ ((2:ℝ)^k * M)^2
  have hex : ∃ k, P k := by
    obtain ⟨k,hk⟩ := exists_nat_ge (S/M)
    have hk2 : (k:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast (Nat.lt_pow_self (by decide : 1<2) (n:=k)).le
    refine ⟨k, ?_⟩
    exact hS2.ge.trans (pow_le_pow_left₀ hS.le ((div_le_iff₀ hM).mp (hk.trans hk2)) 2)
  have kdef : ellipsoidDoublings a = Nat.find hex := by unfold ellipsoidDoublings; rw [dif_pos hex]
  let k := Nat.find hex
  have hl : S ≤ (2:ℝ)^k*M := by
    have h := Nat.find_spec hex
    change (∑ j, a j^2) ≤ _ at h
    exact le_of_sq_le_sq (hS2.le.trans h) (mul_nonneg (by positivity) hM.le)
  have hh : (2:ℝ)^k*M ≤ 2*S := by
    cases hk : k with
    | zero =>
      rw [pow_zero, one_mul]
      obtain ⟨j,hj,hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty a
      have h := Finset.single_le_sum (f := fun l => a l^2) (fun l _ => sq_nonneg _) hj
      have hm : M = a j := hmax
      rw [← hS2, ← hm] at h
      linarith [le_of_sq_le_sq h hS.le]
    | succ j =>
      have hj : j < Nat.find hex := by change j < k; omega
      have h := Nat.find_min hex hj
      change ¬(∑ i, a i^2) ≤ ((2:ℝ)^j*M)^2 at h
      rw [← hS2] at h
      have hpre := le_of_sq_le_sq (le_of_not_ge h) hS.le
      rw [pow_succ]; linarith
  rw [fixedAxisDiagonal_eq ha]
  norm_num
  change 10/ε * S ≤ (10/ε)*((2:ℝ)^ellipsoidDoublings a*M) ∧ _
  change 10/ε * S ≤ (10/ε)*((2:ℝ)^ellipsoidDoublings a*M) ∧
    (10/ε)*((2:ℝ)^ellipsoidDoublings a*M) ≤ 3*(10/ε*S)
  rw [kdef]
  have hpos : 0 ≤ 10/ε := by positivity
  exact ⟨mul_le_mul_of_nonneg_left hl hpos, (mul_le_mul_of_nonneg_left
    (hh.trans (by linarith : 2*S ≤ 3*S)) hpos).trans_eq (by ring)⟩

theorem fixedBoxDiagonal {a : Vec N} (ha : ∀ i, 0 < a i) (ε : ℝ) (i : Fin N) :
    fixedAxisDiagonal a 1 ε i = (10/ε)*a i := by
  rw [fixedAxisDiagonal_eq ha]
  norm_num

end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Curvature
variable {N : ℕ} [NeZero N]


def canonicalUnitBall (N : ℕ) (p : ℝ) : Set (Vec N) := {v | ∑ j, |v j|^p ≤ 1}

omit [NeZero N] in
theorem canonicalUnitBall_coord {p : ℝ} (hp : 0 < p) (v : Vec N) (hv : v ∈ canonicalUnitBall N p) (j : Fin N) :
    |v j| ≤ 1 := by
  have h := (Finset.single_le_sum (f := fun j => |v j|^p) (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ j)).trans hv
  exact (Real.rpow_le_rpow_iff (abs_nonneg _) zero_le_one hp).mp (by simpa using h)


end Curvature

end
end


