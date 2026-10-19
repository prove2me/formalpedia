-- Prove2me | solution 1 for AccelVI.MVC.reversible_real_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T09:26:59.212405+00:00
-- url     : https://prove2.me/submissions/57e6bd79-e5a4-4184-a5db-0be4e9aad98a

-- Directed by Alexander Richard Towell (queelius); formal proof by OpenAI Codex.
-- Source: Vineet Goyal and Julien Grand-Clement, arXiv:1905.09963v7; classical Markov-chain fact.
-- Platform definitions/formulation: mikedeng1; review: Shuze Chen. Lean/Mathlib foundations.
import Mathlib
import Definitions.Def_mm_basic
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


variable {S : Type*} [Fintype S] [DecidableEq S]

/-- §2, p. 4 (after Definition 2.1): the eigenvalues of the transition matrix of an irreducible,
reversible Markov chain are all real. -/
theorem solution (L : Matrix S S ℝ) (hL : MarkovMixing.IsStochastic L)
    (hrev : AccelVI.AVC.IsReversible L) :
    ∀ μ ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)), μ.im = 0  := by
  obtain ⟨hirr,v,hstat,hbal⟩ := hrev
  exact ReversibleResearch.real_spectrum L v
    (ReversibleResearch.stationary_positive L hL.1 hirr v hstat.1 hstat.2) hbal


