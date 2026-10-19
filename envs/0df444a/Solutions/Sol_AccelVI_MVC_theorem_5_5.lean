-- Prove2me | solution 1 for AccelVI.MVC.theorem_5_5
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T10:29:55.754743+00:00
-- url     : https://prove2.me/submissions/3e406b5f-b313-4b90-9916-e49d34cdcac0

-- Direction: Alexander Richard Towell (queelius); completion and verification: OpenAI Codex.
-- Mathematics: Vineet Goyal and Julien Grand-Clément, arXiv1905.09963v7.
-- Platform: mikedeng1, Shuze Chen. Prior alpha and rate-bound proofs: carlok (IDs in explanation).
-- Lean/Mathlib, including Jireh Loreaux’s Gelfand formula. No novelty claim.
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
open Filter Asymptotics
open scoped Topology NNReal Matrix.Norms.Operator
namespace MomentumDynamics
open AccelVI.MVC
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
lemma power_littleO {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (k r : ℝ) (hk : 0 ≤ k) (hr : k < r)
    (hB : spectralRadius ℂ B=ENNReal.ofReal k) :
    (fun n : ℕ => B^n)=o[atTop](fun n => r^n) := by
  let q := (k+r)/2
  have hq0 : 0 < q := by dsimp [q];linarith
  have hkq : k < q := by dsimp [q];linarith
  have hqr : q < r := by dsimp [q];linarith
  have ht := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius B
  rw [hB] at ht
  have hev := ht.eventually (gt_mem_nhds ((ENNReal.ofReal_lt_ofReal_iff hq0).mpr hkq))
  have hb : (fun n : ℕ => B^n)=O[atTop](fun n => q^n) := by
    apply IsBigO.of_bound 1
    filter_upwards [hev,eventually_gt_atTop 0] with n hn hn0
    have hroot : ‖B^n‖^(1/(n:ℝ)) < q := ENNReal.ofReal_lt_ofReal_iff hq0 |>.mp hn
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hroot.le n
    rw [one_div,Real.rpow_inv_natCast_pow (norm_nonneg _) (by omega)] at hp
    simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq0.le n)] using hp
  exact hb.trans_isLittleO (isLittleO_pow_pow_of_lt_left hq0.le hqr)

lemma stochastic_norm (L : Matrix S S ℝ) (h0 : ∀ i j,0 ≤ L i j)
    (h1 : ∀ i,∑ j,L i j=1) : ‖L‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast (show (Finset.univ.sup fun i => ∑ j,‖L i j‖₊) ≤ (1 : ℝ≥0) by
    apply Finset.sup_le
    intro i _
    have hh : ((∑ j,‖L i j‖₊ : ℝ≥0) : ℝ) ≤ 1 := by
      simpa only [NNReal.coe_sum,coe_nnnorm,Real.norm_eq_abs,abs_of_nonneg (h0 _ _)] using (h1 i).le
    exact_mod_cast hh)

lemma fixed_point (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hp : IsPolicy pol) :
    Tpol M pol (valuePol M pol)=valuePol M pol := by
  classical
  by_cases hn : Nonempty S
  swap
  · haveI : IsEmpty S := not_nonempty_iff.mp hn
    exact Subsingleton.elim _ _
  letI := hn
  let L := LPol M pol
  let r := rPol M pol
  let f := fun n : ℕ => M.lam^n • (L^n).mulVec r
  have hst := MomentumPlatform.stochastic M hM pol hp
  have hL : ‖L‖ ≤ 1 := stochastic_norm L hst.1 hst.2
  have hsum : Summable f := by
    apply Summable.of_norm_bounded (g := fun n => M.lam^n*‖r‖)
      ((summable_geometric_of_lt_one hM.2.2.1.le hM.2.2.2).mul_right ‖r‖)
    intro n
    dsimp [f]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hM.2.2.1.le n)]
    have hb := Matrix.linfty_opNorm_mulVec (L^n) r
    have hpow : ‖L^n‖ ≤ 1 := (norm_pow_le L n).trans (by simpa using pow_le_pow_left₀ (norm_nonneg L) hL n)
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hM.2.2.1.le n)
    exact hb.trans (by nlinarith [norm_nonneg r])
  let F : (S → ℝ) →L[ℝ] (S → ℝ) := M.lam • (Matrix.toLin' L).toContinuousLinearMap
  have hstep (n : ℕ) : f (n+1)=F (f n) := by
    change M.lam^(n+1) • (L^(n+1)).mulVec r = M.lam • L.mulVec (M.lam^n • (L^n).mulVec r)
    rw [pow_succ',pow_succ',← Matrix.mulVec_mulVec,Matrix.mulVec_smul,smul_smul]
  have hzero : f 0=r := by simp [f]
  have hv : (∑' n,f n)=r+F (∑' n,f n) := by
    calc
      (∑' n,f n)=f 0+∑' n,f (n+1) := hsum.tsum_eq_zero_add
      _ = r+F (∑' n,f n) := by
        rw [hzero,F.map_tsum hsum]
        congr 1
        exact tsum_congr hstep
  exact hv.symm
end MomentumDynamics

namespace MomentumDynamics
open AccelVI.MVC
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
-- carlok's accepted parameter identity, submission 41732d9a-934d-4f92-9a7b-29d3a8c6d9e0.
lemma alpha_eq (l : ℝ) : alphaMVC l=1+betaMVC l := by
  unfold alphaMVC betaMVC
  have h : 0 < 1+Real.sqrt (1-l^2) := by positivity
  field_simp
  ring
lemma recurrence (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hp : IsPolicy pol)
    (v0 v1 : S → ℝ) (s : ℕ) (hs : 1 ≤ s) :
    Sum.elim (mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1 s)
      (mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1 (s-1)) =
    Sum.elim (valuePol M pol) (valuePol M pol)+((Bpol M pol)^(s-1)).mulVec
      (Sum.elim v1 v0-Sum.elim (valuePol M pol) (valuePol M pol)) := by
  let v := mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1
  let z := valuePol M pol
  let Z := Sum.elim z z
  let e := Sum.elim v1 v0-Z
  have hf := fixed_point M hM pol hp
  have step (n : ℕ) : Sum.elim (v (n+2)) (v (n+1))=Z+(Bpol M pol).mulVec (Sum.elim (v (n+1)) (v n)-Z) := by
    ext i
    cases i with
    | inl i =>
      have hh := congrFun hf i
      change rPol M pol i+M.lam*(LPol M pol).mulVec z i=z i at hh
      change (v (n+2)) i = _
      simp only [v,mvc,Bpol,Matrix.fromBlocks_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
        Matrix.zero_mulVec,Matrix.mulVec_sub,Function.comp_def,Pi.add_apply,Pi.sub_apply,
        Pi.smul_apply,smul_eq_mul,Sum.elim_inl,Sum.elim_inr,Tpol,Z,z]
      rw [alpha_eq]
      dsimp only [z] at hh
      linear_combination (1+betaMVC M.lam)*hh
    | inr i => simp [Bpol,Matrix.fromBlocks_mulVec,Function.comp_def,Z]
  have hpow (n : ℕ) : Sum.elim (v (n+1)) (v n)=Z+((Bpol M pol)^n).mulVec e := by
    induction n with
    | zero => simp [v,mvc,e]
    | succ n ih =>
      rw [show n+1+1=n+2 by omega,step,ih]
      rw [add_sub_cancel_left,pow_succ',← Matrix.mulVec_mulVec]
  convert hpow (s-1) using 1 <;> congr 2 <;> omega
end MomentumDynamics

namespace MomentumDynamics
open AccelVI.MVC
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
lemma real_norm {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) :
    ‖B.map (algebraMap ℝ ℂ)‖=‖B‖ := by
  simp [Matrix.linfty_opNorm_def]
lemma error_littleO (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hp : IsPolicy pol)
    (hrev : AccelVI.AVC.IsReversible (LPol M pol)) (v0 v1 : S → ℝ)
    (r : ℝ) (hk : 0 ≤ rateMVC M.lam) (hr : rateMVC M.lam < r) :
    (fun s => mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1 s-valuePol M pol)
      =o[atTop](fun s => r^s) := by
  let B := Bpol M pol
  let v := mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1
  let z := valuePol M pol
  let e := Sum.elim v1 v0-Sum.elim z z
  have hr0 : 0 < r := hk.trans_lt hr
  have hc := power_littleO (B.map (algebraMap ℝ ℂ)) (rateMVC M.lam) r hk hr (MomentumPlatform.radius M hM pol hp hrev)
  have hreal : (fun n : ℕ => B^n)=o[atTop](fun n => r^n) := by
    apply IsLittleO.of_norm_left
    convert hc.norm_left using 1
    funext n
    rw [← Matrix.map_pow,real_norm]
  have hs : (fun n : ℕ => B^(n-1))=o[atTop](fun n => r^(n-1)) := hreal.comp_tendsto (tendsto_sub_atTop_nat 1)
  have hshift : (fun n : ℕ => r^(n-1))=O[atTop](fun n => r^n) := by
    apply IsBigO.of_bound (1/r)
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr0.le _)]
    have he : r^n=r^(n-1)*r := by rw [← pow_succ];congr 1;omega
    rw [he]
    field_simp <;> norm_num
  have hvec : (fun n : ℕ => (B^(n-1)).mulVec e)=O[atTop](fun n => B^(n-1)) := by
    apply IsBigO.of_bound ‖e‖
    exact Filter.Eventually.of_forall fun n => by simpa only [mul_comm] using Matrix.linfty_opNorm_mulVec (B^(n-1)) e
  have herr : (fun n => v n-z)=O[atTop](fun n => (B^(n-1)).mulVec e) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have he := congrFun (recurrence M hM pol hp v0 v1 n hn) (Sum.inl i)
    change v n i=z i+(B^(n-1)).mulVec e (Sum.inl i) at he
    change ‖v n i-z i‖ ≤ _
    rw [he,add_sub_cancel_left]
    exact norm_le_pi_norm _ (Sum.inl i)
  exact (herr.trans hvec).trans_isLittleO (hs.trans_isBigO hshift)
end MomentumDynamics

namespace MomentumDynamics
open AccelVI.MVC
-- carlok's accepted rate-bounds proof, submission f705cf48-789b-41eb-bba7-774b5eb83c97.
lemma rate_bounds (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    0 < rateMVC lam ∧ rateMVC lam < lam := by
  unfold rateMVC AccelVI.AVC.kappa
  have hk : 1 / ((1 + lam) / (1 - lam)) = (1 - lam) / (1 + lam) := by rw [one_div_div]
  rw [hk]
  have hpos : 0 < (1 - lam) / (1 + lam) := by apply div_pos <;> linarith
  have hlt : (1 - lam) / (1 + lam) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hs2 : Real.sqrt ((1 - lam) / (1 + lam)) ^ 2 = (1 - lam) / (1 + lam) := Real.sq_sqrt hpos.le
  have hs0 : 0 < Real.sqrt ((1 - lam) / (1 + lam)) := Real.sqrt_pos.2 hpos
  have hs1 : Real.sqrt ((1 - lam) / (1 + lam)) < 1 := by rw [Real.sqrt_lt' one_pos]; linarith
  generalize Real.sqrt ((1 - lam) / (1 + lam)) = s at *
  have hs2' : s ^ 2 * (1 + lam) = 1 - lam := by rw [hs2]; field_simp
  constructor
  · apply div_pos <;> linarith
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith [mul_pos (mul_pos hs0 (sub_pos.2 hs1)) (by linarith : (0:ℝ) < 1 + lam)]
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
lemma convergence (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hp : IsPolicy pol)
    (hrev : AccelVI.AVC.IsReversible (LPol M pol)) (v0 v1 : S → ℝ) :
    Tendsto (mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1) atTop (𝓝 (valuePol M pol)) ∧
    (∀ η : ℝ,0 < η → (fun s => mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1 s-valuePol M pol)
      =o[atTop](fun s => (rateMVC M.lam+η)^s)) ∧
    0 < rateMVC M.lam ∧ rateMVC M.lam < M.lam := by
  have hb := rate_bounds M.lam hM.2.2.1 hM.2.2.2
  refine ⟨?_,?_,hb⟩
  · let r := (rateMVC M.lam+1)/2
    have hr0 : 0 ≤ r := by dsimp [r];linarith [hb.1]
    have hr1 : r < 1 := by dsimp [r];linarith [hb.2,hM.2.2.2]
    have hk : rateMVC M.lam < r := by dsimp [r];linarith [hb.2,hM.2.2.2]
    have he := (error_littleO M hM pol hp hrev v0 v1 r hb.1.le hk).isBigO.trans_tendsto
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
    exact tendsto_sub_nhds_zero_iff.mp he
  · intro η hη
    exact error_littleO M hM pol hp hrev v0 v1 _ hb.1.le (by linarith)
end MomentumDynamics
open AccelVI.MVC


variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- Theorem 5.5, p. 10: if π defines an irreducible, reversible Markov chain, the M-VC iterates with step
sizes (4.2) converge to v^π, v_s = v^π + o(((1 − √(1/κ))/(1 + √(1/κ)) + η)^s) for every η > 0, and
0 < (1 − √(1/κ))/(1 + √(1/κ)) < λ. -/
theorem solution (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : IsPolicy pol)
    (hrev : AccelVI.AVC.IsReversible (LPol M pol)) (v0 v1 : S → ℝ) :
    Filter.Tendsto (mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1) Filter.atTop (nhds (valuePol M pol)) ∧
    (∀ η : ℝ, 0 < η →
      (fun s => mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1 s - valuePol M pol)
        =o[Filter.atTop] (fun s => (rateMVC M.lam + η) ^ s)) ∧
    0 < rateMVC M.lam ∧ rateMVC M.lam < M.lam := by
  exact MomentumDynamics.convergence M hM pol hpol hrev v0 v1


