-- Prove2me | solution 1 for AccelVI.MVC.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T09:34:34.329667+00:00
-- url     : https://prove2.me/submissions/1508c5ee-76e7-488a-bb6a-32ed5b84b21d

-- Directed by Alexander Richard Towell (queelius); formal proof by OpenAI Codex.
-- Source: Goyal and Grand-Clement, arXiv:1905.09963v7. Platform formulations and prior repairs: mikedeng1.
-- Statement review: Shuze Chen. Formal foundations: Lean and Mathlib contributors.
import Definitions.Def_AccelVI_MVC_Setting
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 800000
open Matrix
namespace ReversibleResearch
variable {S : Type*} [Fintype S] [DecidableEq S]
lemma stationary_positive (L : Matrix S S ℝ) (hL : ∀ i j, 0 ≤ L i j)
    (hirr : ∀ i j, ∃ t : ℕ, 0 < (L^t) i j) (v : S → ℝ)
    (hv : (∀ i,0 ≤ v i) ∧ ∑ i, v i = 1) (hstat : vecMul v L=v) : ∀ j,0 < v j := by
  have hp (t : ℕ) : vecMul v (L^t)=v := by
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ,← vecMul_vecMul,ih,hstat]
  have hsum : 0 < ∑ i,v i := by rw [hv.2];norm_num
  have hex : ∃ i,0 < v i := by
    by_contra h
    push_neg at h
    have hh : ∑ i,v i ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    linarith
  obtain ⟨i,hi⟩ := hex
  intro j
  obtain ⟨t,ht⟩ := hirr i j
  have hle : v i*(L^t) i j ≤ ∑ k,v k*(L^t) k j :=
    Finset.single_le_sum (fun k _ => mul_nonneg (hv.1 k) (Matrix.pow_apply_nonneg hL t k j)) (Finset.mem_univ i)
  have he := congrFun (hp t) j
  change (∑ k,v k*(L^t) k j)=v j at he
  rw [he] at hle
  exact (mul_pos hi ht).trans_le hle
lemma real_spectrum (L : Matrix S S ℝ) (v : S → ℝ) (hv : ∀ i,0 < v i)
    (hbal : ∀ i j,v i*L i j=v j*L j i) :
    ∀ μ ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)), μ.im=0 := by
  let d : S → ℝ := fun i => Real.sqrt (v i)
  have hd (i : S) : 0 < d i := Real.sqrt_pos.mpr (hv i)
  have hs (i : S) : d i*d i=v i := by simpa [pow_two] using Real.sq_sqrt (hv i).le
  have hdc (i : S) : (d i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hd i))
  let u : (Matrix S S ℂ)ˣ := {
    val := Matrix.diagonal fun i => (d i : ℂ)
    inv := Matrix.diagonal fun i => (d i : ℂ)⁻¹
    val_inv := by simp [Matrix.diagonal_mul_diagonal,hdc]
    inv_val := by simp [Matrix.diagonal_mul_diagonal,hdc] }
  let M : Matrix S S ℂ := (u : Matrix S S ℂ)*(L.map (algebraMap ℝ ℂ))*((u⁻¹ : (Matrix S S ℂ)ˣ) : Matrix S S ℂ)
  have hentry (i j : S) : M i j = ((d i*L i j/d j : ℝ) : ℂ) := by
    change ((Matrix.diagonal fun i => (d i : ℂ))*L.map (algebraMap ℝ ℂ)*(Matrix.diagonal fun i => (d i : ℂ)⁻¹)) i j = _
    simp [Matrix.mul_diagonal,Matrix.diagonal_mul,div_eq_mul_inv]
  have hM : M.IsHermitian := by
    unfold Matrix.IsHermitian
    ext i j
    have hij : d j*L j i/d i=d i*L i j/d j := by
      apply (div_eq_div_iff (ne_of_gt (hd i)) (ne_of_gt (hd j))).mpr
      calc
        d j*L j i*d j=(d j*d j)*L j i := by ring
        _=v j*L j i := by rw [hs]
        _=v i*L i j := (hbal i j).symm
        _=d i*L i j*d i := by rw [← hs];ring
    change star (M j i)=M i j
    rw [hentry,hentry]
    simpa using congrArg (fun x : ℝ => (x:ℂ)) hij
  intro μ hμ
  have hm : μ ∈ spectrum ℂ M := by simpa only [M,spectrum.units_conjugate] using hμ
  rw [hM.spectrum_eq_image_range] at hm
  obtain ⟨r,_,rfl⟩ := hm
  simp
end ReversibleResearch

set_option autoImplicit false
set_option maxHeartbeats 1200000
open Matrix
namespace MomentumResearch
variable {S : Type*} [Fintype S] [DecidableEq S]
lemma spectrum_vector (L : Matrix S S ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ L ↔ ∃ v : S → ℂ, v ≠ 0 ∧ L.mulVec v=μ • v := by
  rw [← Matrix.spectrum_toLin',← Module.End.hasEigenvalue_iff_mem_spectrum]
  constructor
  · intro h
    obtain ⟨v,hv⟩ := h.exists_hasEigenvector
    exact ⟨v,hv.2,Module.End.mem_eigenspace_iff.mp hv.1⟩
  · rintro ⟨v,hv,he⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr he,hv⟩
lemma block_eigen (L : Matrix S S ℂ) (a b ω : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hω : ω ∈ spectrum ℂ (Matrix.fromBlocks (a • L) (-b • (1 : Matrix S S ℂ)) (1 : Matrix S S ℂ) 0)) :
    ∃ μ ∈ spectrum ℂ L,ω^2-a*μ*ω+b=0 := by
  obtain ⟨v,hv,he⟩ := (spectrum_vector _ ω).mp hω
  let x : S → ℂ := fun i => v (Sum.inl i)
  let y : S → ℂ := fun i => v (Sum.inr i)
  have h1 : a • L.mulVec x-b • y=ω • x := by
    funext i
    have h := congrFun he (Sum.inl i)
    simpa [Matrix.fromBlocks_mulVec,Matrix.neg_mulVec,Matrix.smul_mulVec,x,y,Function.comp_def,sub_eq_add_neg] using h
  have h2 : x=ω • y := by
    funext i
    have h := congrFun he (Sum.inr i)
    simpa [Matrix.fromBlocks_mulVec,Matrix.neg_mulVec,Matrix.smul_mulVec,x,y,Function.comp_def] using h
  have hy : y ≠ 0 := by
    intro hy
    have hx : x=0 := by rw [h2,hy,smul_zero]
    apply hv
    funext i;cases i with
    | inl i => exact congrFun hx i
    | inr i => exact congrFun hy i
  have hw : ω ≠ 0 := by
    intro hw
    have hx : x=0 := by rw [h2,hw,zero_smul]
    rw [hx,Matrix.mulVec_zero,smul_zero,zero_sub,smul_zero] at h1
    have hyz : y=0 := by
      funext i
      have hi := congrFun h1 i
      have hi' : b*y i=0 := by simpa using hi
      exact (mul_eq_zero.mp hi').resolve_left hb
    exact hy hyz
  let μ := (ω^2+b)/(a*ω)
  have hLy : L.mulVec y=μ • y := by
    funext i
    have hi := congrFun h1 i
    rw [h2,Matrix.mulVec_smul] at hi
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hi ⊢
    dsimp [μ]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (mul_ne_zero ha hw)).mpr
    linear_combination hi
  refine ⟨μ,(spectrum_vector L μ).mpr ⟨y,hy,hLy⟩,?_⟩
  dsimp [μ]
  field_simp [ha,hw]
  ring
lemma stochastic_spectrum_norm (L : Matrix S S ℝ) (hL0 : ∀ i j,0 ≤ L i j)
    (hL1 : ∀ i,∑ j,L i j=1) (μ : ℂ) (hμ : μ ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ))) : ‖μ‖ ≤ 1 := by
  obtain ⟨v,hv,he⟩ := (spectrum_vector _ μ).mp hμ
  have hex : ∃ i,v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨i,hi⟩ := hex
  letI : Nonempty S := ⟨i⟩
  obtain ⟨j,hmax⟩ := Finite.exists_max (fun i => ‖v i‖)
  have hj : 0 < ‖v j‖ := (norm_pos_iff.mpr hi).trans_le (hmax i)
  have hb : ‖μ‖*‖v j‖ ≤ ‖v j‖ := by
    calc
      ‖μ‖*‖v j‖=‖((L.map (algebraMap ℝ ℂ)).mulVec v) j‖ := by rw [he];simp [norm_mul]
      _ ≤ ∑ i,L j i*‖v i‖ := by
        simp only [Matrix.mulVec,dotProduct]
        calc
          ‖∑ i,(L.map (algebraMap ℝ ℂ)) j i*v i‖ ≤ ∑ i,‖(L.map (algebraMap ℝ ℂ)) j i*v i‖ := norm_sum_le _ _
          _ = ∑ i,L j i*‖v i‖ := by simp [norm_mul,abs_of_nonneg (hL0 j _)]
      _ ≤ ∑ i,L j i*‖v j‖ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmax i) (hL0 j i)
      _ = ‖v j‖ := by rw [← Finset.sum_mul,hL1,one_mul]
  nlinarith
end MomentumResearch
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace MomentumScalar
lemma root_norm (k μ : ℝ) (hk : 0 ≤ k) (hμ1 : -1 ≤ μ) (hμ2 : μ ≤ 1) (ω : ℂ)
    (h : ω^2-2*(k:ℂ)*μ*ω+(k:ℂ)^2=0) : ‖ω‖=k := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  norm_num [pow_two,Complex.mul_re,Complex.mul_im] at hr hi
  have hm : 0 ≤ 1-μ^2 := by nlinarith
  have hn := Complex.sq_norm ω
  rw [Complex.normSq_apply] at hn
  by_cases hb : ω.im=0
  · rw [hb] at hr hn
    have hp := mul_nonneg (sq_nonneg k) hm
    have hs : (ω.re-k*μ)^2=0 := by nlinarith [sq_nonneg (ω.re-k*μ)]
    have he : ω.re=k*μ := sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    rw [he] at hr hn
    nlinarith [norm_nonneg ω]
  · have he : ω.re=k*μ := by
      have hz : 2*ω.im*(ω.re-k*μ)=0 := by nlinarith [hi]
      rcases mul_eq_zero.mp hz with h0 | h0
      · have hi0 : ω.im=0 := by linarith
        contradiction
      · linarith
    rw [he] at hr hn
    nlinarith [norm_nonneg ω]
lemma rates (l : ℝ) (h0 : 0 < l) (h1 : l < 1) :
    l/(1+Real.sqrt (1-l^2)) = (Real.sqrt (1+l)-Real.sqrt (1-l))/(Real.sqrt (1+l)+Real.sqrt (1-l)) ∧
    (Real.sqrt (1+l)-Real.sqrt (1-l))/(Real.sqrt (1+l)+Real.sqrt (1-l)) =
      (1-Real.sqrt ((1-l)/(1+l)))/(1+Real.sqrt ((1-l)/(1+l))) := by
  have ha : 0 < 1+l := by linarith
  have hb : 0 < 1-l := by linarith
  have hc : 0 ≤ 1-l^2 := by nlinarith
  have hsa := Real.sqrt_pos.mpr ha
  have hsb := Real.sqrt_pos.mpr hb
  have hsd : 0 < 1+Real.sqrt (1-l^2) := by positivity
  have he : Real.sqrt (1-l^2)=Real.sqrt (1+l)*Real.sqrt (1-l) := by
    rw [← Real.sqrt_mul ha.le]
    congr 1;ring
  have hs1 := Real.sq_sqrt ha.le
  have hs2 := Real.sq_sqrt hb.le
  constructor
  · apply (div_eq_div_iff (ne_of_gt hsd) (ne_of_gt (add_pos hsa hsb))).mpr
    rw [he]
    nlinarith [mul_pos hsa hsb,congrArg (fun x : ℝ => x*Real.sqrt (1-l)) hs1,
      congrArg (fun x : ℝ => x*Real.sqrt (1+l)) hs2]
  · rw [Real.sqrt_div hb.le]
    field_simp [ne_of_gt hsa,ne_of_gt (add_pos hsa hsb)]
end MomentumScalar
namespace MomentumResearch
variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
lemma radius (L : Matrix S S ℝ) (hL0 : ∀ i j,0 ≤ L i j) (hL1 : ∀ i,∑ j,L i j=1)
    (hreal : ∀ μ ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)),μ.im=0) (k : ℝ) (hk : 0 < k) :
    spectralRadius ℂ (Matrix.fromBlocks ((2*(k:ℂ)) • L.map (algebraMap ℝ ℂ))
      (-(k:ℂ)^2 • (1 : Matrix S S ℂ)) (1 : Matrix S S ℂ) 0) = ENNReal.ofReal k := by
  let Lc := L.map (algebraMap ℝ ℂ)
  let B := Matrix.fromBlocks ((2*(k:ℂ)) • Lc) (-(k:ℂ)^2 • (1 : Matrix S S ℂ)) (1 : Matrix S S ℂ) 0
  have hkc : (k:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hall (ω : ℂ) (hω : ω ∈ spectrum ℂ B) : ‖ω‖=k := by
    obtain ⟨μ,hμ,he⟩ := block_eigen Lc (2*(k:ℂ)) ((k:ℂ)^2) ω (mul_ne_zero (by norm_num) hkc) (pow_ne_zero _ hkc) hω
    have hr := hreal μ hμ
    have hm := stochastic_spectrum_norm L hL0 hL1 μ hμ
    have hμr : μ=(μ.re:ℂ) := by exact Complex.ext (by simp) (by simpa using hr)
    have hb : -1 ≤ μ.re ∧ μ.re ≤ 1 := by
      rw [hμr,Complex.norm_real,Real.norm_eq_abs] at hm
      exact abs_le.mp hm
    rw [hμr] at he
    exact MomentumScalar.root_norm k μ.re hk.le hb.1 hb.2 ω (by convert he using 1 <;> ring)
  have hone : Lc.mulVec (fun _ => (1:ℂ))=fun _ => 1 := by
    funext i
    change (∑ j,(L i j:ℂ)*1)=1
    simpa using congrArg (fun x : ℝ => (x:ℂ)) (hL1 i)
  have hkmem : (k:ℂ) ∈ spectrum ℂ B := by
    apply (spectrum_vector B (k:ℂ)).mpr
    let v : S ⊕ S → ℂ := Sum.elim (fun _ => (k:ℂ)) (fun _ => 1)
    refine ⟨v,?_,?_⟩
    · intro hv
      have hh := congrFun hv (Sum.inr (Classical.choice (inferInstance : Nonempty S)))
      simp [v] at hh
    · have hconst : Lc.mulVec (fun _ => (k:ℂ))=fun _ => (k:ℂ) := by
        have hc : (fun _ : S => (k:ℂ))=(k:ℂ) • (fun _ => (1:ℂ)) := by ext i;simp
        rw [hc,Matrix.mulVec_smul,hone]
      funext i
      cases i with
      | inl i => simp [B,v,Matrix.fromBlocks_mulVec,Matrix.smul_mulVec,Matrix.neg_mulVec,Function.comp_def,hconst];ring
      | inr i => simp [B,v,Matrix.fromBlocks_mulVec,Function.comp_def]
  change spectralRadius ℂ B=ENNReal.ofReal k
  apply le_antisymm
  · refine iSup_le fun ω => iSup_le fun hω => ?_
    rw [← enorm_eq_nnnorm,← ofReal_norm,hall ω hω]
  · have hl : (‖(k:ℂ)‖₊ : ENNReal) ≤ spectralRadius ℂ B := by
      unfold spectralRadius
      exact le_iSup_of_le (k:ℂ) (le_iSup_of_le hkmem le_rfl)
    simpa [← enorm_eq_nnnorm,← ofReal_norm,Complex.norm_real,abs_of_pos hk] using hl
end MomentumResearch

namespace MomentumPlatform
open AccelVI.MVC
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
lemma stochastic (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hp : IsPolicy pol) :
    MarkovMixing.IsStochastic (LPol M pol) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg fun a _ => mul_nonneg ((hp i).1 a) (hM.1 i a j)
  · intro i
    simp only [LPol]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,hM.2.1,mul_one]
    exact (hp i).2
lemma constants (l : ℝ) (h0 : 0 < l) (h1 : l < 1) :
    let k := l/(1+Real.sqrt (1-l^2))
    0 < k ∧ betaMVC l=k^2 ∧ l*(betaMVC l+1)=2*k ∧ rateMVC l=k := by
  dsimp only
  have hd : 0 < 1+Real.sqrt (1-l^2) := by positivity
  have hs := Real.sq_sqrt (show 0 ≤ 1-l^2 by nlinarith)
  have hb : betaMVC l=(l/(1+Real.sqrt (1-l^2)))^2 := by
    unfold betaMVC
    field_simp [ne_of_gt hd]
    nlinarith
  refine ⟨div_pos h0 hd,hb,?_,?_⟩
  · unfold betaMVC
    field_simp [ne_of_gt hd]
    ring
  · have hr := MomentumScalar.rates l h0 h1
    unfold rateMVC AccelVI.AVC.kappa
    rw [one_div_div]
    exact (hr.1.trans hr.2).symm
lemma block_form (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) :
    let k := M.lam/(1+Real.sqrt (1-M.lam^2))
    (Bpol M pol).map (algebraMap ℝ ℂ)=
      Matrix.fromBlocks ((2*(k:ℂ)) • (LPol M pol).map (algebraMap ℝ ℂ))
        (-(k:ℂ)^2 • (1 : Matrix S S ℂ)) (1 : Matrix S S ℂ) 0 := by
  dsimp only
  have hc := constants M.lam hM.2.2.1 hM.2.2.2
  unfold Bpol
  rw [hc.2.2.1,hc.2.1]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.map_apply,Matrix.one_apply] <;> split_ifs <;> simp
lemma radius (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hp : IsPolicy pol)
    (hrev : AccelVI.AVC.IsReversible (LPol M pol)) :
    spectralRadius ℂ ((Bpol M pol).map (algebraMap ℝ ℂ)) = ENNReal.ofReal (rateMVC M.lam) := by
  obtain ⟨hirr,v,hv,hbal⟩ := hrev
  haveI : Nonempty S := by
    by_contra h
    haveI : IsEmpty S := not_nonempty_iff.mp h
    have hs := hv.1.2
    simp at hs
  have hst := stochastic M hM pol hp
  have hreal := ReversibleResearch.real_spectrum (LPol M pol) v
    (ReversibleResearch.stationary_positive (LPol M pol) hst.1 hirr v hv.1 hv.2) hbal
  have hc := constants M.lam hM.2.2.1 hM.2.2.2
  rw [block_form M hM pol,hc.2.2.2]
  exact MomentumResearch.radius (LPol M pol) hst.1 hst.2 hreal _ hc.1
end MomentumPlatform
open AccelVI.MVC


variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- Lemma B.2, p. 21 (with the rate (1 − √(1/κ))/(1 + √(1/κ)) of its proof for the printed
(1 − √κ)/(1 + √κ)): if π defines an irreducible, reversible Markov chain, then for step sizes (4.2)
ρ(B_π) = (1 − √(1/κ))/(1 + √(1/κ)). -/
theorem solution (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : IsPolicy pol)
    (hrev : AccelVI.AVC.IsReversible (LPol M pol)) :
    spectralRadius ℂ ((Bpol M pol).map (algebraMap ℝ ℂ)) = ENNReal.ofReal (rateMVC M.lam) := by
  exact MomentumPlatform.radius M hM pol hpol hrev


