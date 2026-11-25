-- Prove2me | Definitions.Def_DetDLP_W1_Bounds
-- name    : DetDLP_W1_Bounds
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:33:06.321078+00:00
-- url     : https://prove2.me/theorems/3bf8a766-37d3-4ba1-94a0-4e8ad19e71c5
-- title:
--   Uniform time and space bounds for word transformations
-- statement:
--   Parameterized families of executions are composed under distinct time and space exponent scales. Polynomial preprocessing and saved-input calls preserve these bounds, and the space exponent scale is at most four times the time exponent scale for every input bit length.

import Definitions.Def_DetDLP_W1_Pipeline
import Definitions.Def_DetDLP_PolyTBridge

set_option autoImplicit false
namespace DetDLP_W1_Bounds
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
noncomputable section
def sScale (b : ℕ) := (b:ℝ)/(logSafe b)^((1:ℝ)/4)
def tScale (b : ℕ) := (b:ℝ)/Real.sqrt (logLogSafe b)
def E (x : ℝ) (k : ℕ) := (2:ℝ)^((k:ℝ)*x)
theorem sEq (b k : ℕ) : E (sScale b) k = mainSpaceBound k b := by unfold E sScale mainSpaceBound; congr 1; ring
theorem tEq (b k : ℕ) : E (tScale b) k = mainTimeBound k b := by unfold E tScale mainTimeBound; congr 1; ring
private theorem scale_ge_one {b : ℕ} (hb : 1 ≤ b) : 1 ≤ (b : ℝ) / (logSafe b)^((1:ℝ)/4) := by
  have hbr : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hl : logSafe b ≤ (b:ℝ) := by
    apply max_le hbr
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (by positivity)).mpr
    rw [Real.rpow_natCast]; apply max_le
    · exact_mod_cast (show 2 ≤ 2^b by exact le_trans (by decide : 2 ≤ 2^1) (Nat.pow_le_pow_right (by decide) hb))
    · exact_mod_cast (show b < 2^b from Nat.lt_two_pow_self).le
  have hg : 1 ≤ logSafe (b:ℝ) := le_max_left _ _
  have hp : (logSafe (b:ℝ))^((1:ℝ)/4) ≤ logSafe b := by
    simpa using Real.rpow_le_rpow_of_exponent_le hg (by norm_num : (1:ℝ)/4 ≤ 1)
  apply (one_le_div (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hg) _)).mpr
  exact hp.trans hl

theorem compareScale (b : ℕ) : sScale b ≤ 4*tScale b := by
  let L := logSafe (b:ℝ)
  have hL : 1 ≤ L := le_max_left _ _
  have hL' : 0 < L := by linarith
  let D := L^((1:ℝ)/4)
  have hD : 1 ≤ D := Real.one_le_rpow hL (by norm_num)
  have sq : D^2 = L^((1:ℝ)/2) := by rw [← Real.rpow_mul_natCast (by positivity)]; norm_num
  have hm : max 2 (Real.logb 2 (max 2 (b:ℝ))) ≤ 2*L := max_le (by linarith) (by have hh : Real.logb 2 (max 2 (b:ℝ)) ≤ L := le_max_right _ _; linarith)
  have hh := Real.log_le_rpow_div (x:=2*L) (by positivity) (by norm_num : (0:ℝ)<1/2)
  have h2 : (2:ℝ)^((1:ℝ)/2) ≤ 2 := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by norm_num : (1:ℝ)/2≤1)
  rw [Real.mul_rpow (by norm_num) hL'.le,←sq] at hh
  have hlog : logLogSafe (b:ℝ) ≤ (4*D)^2 := by
    apply max_le (by nlinarith)
    unfold Real.logb; apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    apply (Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_left _ _)) hm).trans
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg D),mul_nonneg (sub_nonneg.mpr Real.log_two_gt_d9.le) (sq_nonneg D)]
  have hRoot := Real.sqrt_le_iff.mpr ⟨(by linarith : 0 ≤ 4*D),hlog⟩
  have hden : 0 < Real.sqrt (logLogSafe (b:ℝ)) := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  unfold sScale tScale; change (b:ℝ)/D ≤ _
  rw [← mul_div_assoc,div_le_div_iff₀ (by linarith : 0<D) hden]; nlinarith [mul_le_mul_of_nonneg_left hRoot (Nat.cast_nonneg (α:=ℝ) b)]

variable {ι : Type} {X : ι → ℝ} {f g : ι → ℝ}
def Dom (X f : ι → ℝ) := ∃ k : ℕ, ∀ i, f i ≤ E (X i) k

theorem monoE {x : ℝ} (hx : 0 ≤ x) {k l : ℕ} (h : k ≤ l) : E x k ≤ E x l := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num); gcongr

theorem dconst (hX : ∀ i, 1 ≤ X i) (n : ℕ) : Dom X (fun _ => (n:ℝ)) := by
  refine ⟨n,fun i => ?_⟩; calc (n:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
    _ ≤ E (X i) n := by unfold E; rw [← Real.rpow_natCast]; apply Real.rpow_le_rpow_of_exponent_le (by norm_num); nlinarith [hX i,Nat.cast_nonneg (α:=ℝ) n]

theorem Dom.weaken (hf : Dom X f) (h : ∀ i, g i ≤ f i) : Dom X g := by obtain ⟨k,hk⟩ := hf; exact ⟨k,fun i => (h i).trans (hk i)⟩

theorem Dom.add (hX : ∀ i, 1 ≤ X i) (hf : Dom X f) (hg : Dom X g) : Dom X (fun i => f i+g i) := by
  obtain ⟨k,hk⟩ := hf; obtain ⟨l,hl⟩ := hg
  refine ⟨max k l+1,fun i => ?_⟩
  have hx := hX i; have hz : 0 ≤ X i := by linarith
  have ha := (hk i).trans (monoE hz (le_max_left k l)); have hb := (hl i).trans (monoE hz (le_max_right k l))
  have ht : (2:ℝ) ≤ 2^(X i) := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hx
  unfold E at *; rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,Real.rpow_add (by norm_num)]; nlinarith [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ (2:ℝ)^((max k l:ℕ)*X i))]

theorem Dom.mul (hf : Dom X f) (hg : Dom X g) (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ i, 0 ≤ g i) : Dom X (fun i => f i*g i) := by
  obtain ⟨k,hk⟩ := hf; obtain ⟨l,hl⟩ := hg; refine ⟨k+l,fun i => ?_⟩
  unfold E; push_cast; rw [add_mul,Real.rpow_add (by norm_num)]; exact mul_le_mul (hk i) (hl i) (hg0 i) (by positivity)

theorem Dom.pow (hX : ∀ i, 1 ≤ X i) (hf : Dom X f) (hf0 : ∀ i, 0 ≤ f i) (k : ℕ) : Dom X (fun i => f i^k) := by
  induction k with
  | zero => simpa using dconst hX 1
  | succ k ih => simpa [pow_succ] using ih.mul hf (fun i => pow_nonneg (hf0 i) _) hf0

abbrev W := List Bool
variable (S T : ι → ℝ)
def Family (a b : ι → W) := ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (t s : ι → ℝ), Dom T t ∧ Dom S s ∧ ∀ i, RunsWithin M o (a i) (b i) (t i) (s i)
variable {S T} (hS : ∀ i, 1 ≤ S i) (hST : ∀ i, S i ≤ T i)
include hS hST
private theorem tOne : ∀ i, 1 ≤ T i := fun i => (hS i).trans (hST i)
theorem liftTime {f : ι → ℝ} (hf : Dom S f) : Dom T f := by
  obtain ⟨k,hk⟩ := hf; refine ⟨k,fun i => (hk i).trans ?_⟩
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num); exact mul_le_mul_of_nonneg_left (hST i) (Nat.cast_nonneg _)

theorem seq {a b c : ι → W} (ha : Family S T a b) (hb : Family S T b c) : Family S T a c := by
  obtain ⟨A,oa,atime,aspace,hat,has,hA⟩ := ha; obtain ⟨B,ob,bt,bs,hbt,hbs,hB⟩ := hb
  exact ⟨_,_,_,_,Dom.add (tOne hS hST) hat hbt,Dom.add hS (Dom.add hS has (dconst hS B.tapeCount)) (Dom.add hS hbs (dconst hS A.tapeCount)),fun i => DetDLP_W1_Pipeline.WordPipeline.run A oa B ob (hA i) (hB i)⟩

def Short (S : ι → ℝ) (w : ι → W) := Dom S (fun i => ((w i).length:ℝ))
omit hS hST in
private theorem pfLen (x : W) : (Encoding.frame x).length = 2*x.length+1 := by
  induction x with
  | nil => rfl
  | cons b x ih => change (Encoding.frame x).length+1+1 = 2*(x.length+1)+1; omega

def pack (x y : W) := Encoding.encodeList id [x,y]
omit hS hST in
theorem packLen (x y : W) : (pack x y).length = 2*(x.length+y.length)+5 := by simp [pack,Encoding.encodeList,pfLen]; omega

omit hST in
theorem shortPack {a b : ι → W} (ha : Short S a) (hb : Short S b) : Short S (fun i => pack (a i) (b i)) := by
  unfold Short; simp only [packLen,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]; apply Dom.add hS _ (dconst hS 5); exact (dconst hS 2).mul (Dom.add hS ha hb) (fun _ => by norm_num) (fun _ => by positivity)

private theorem oneDom : Dom S (fun _ => (1:ℝ)) := by simpa using dconst hS 1

theorem poly {w : ι → W} (hw : Short S w) (q : W → W) (hq : Groundwork.PolyT q) : Family S T w (fun i => q (w i)) := by
  obtain ⟨A,o,k,hA⟩ := PolyTBridge.polyT_listBool_runsWithin q hq
  have h : Dom S (fun i => polyBound k (w i).length) := (dconst hS k).mul ((Dom.add hS hw (oneDom hS hST)).pow hS (fun _ => by positivity) k) (fun _ => by positivity) (fun _ => by positivity)
  exact ⟨A,o,_,_,liftTime hS hST h,h,fun i => hA (w i)⟩

theorem save {a b : ι → W} (ha : Short S a) (hb : Short S b) (h : Family S T a b) : Family S T a (fun i => pack (a i) (b i)) := by
  obtain ⟨A,o,t,s,ht,hs,h⟩ := h
  have hp := shortPack hS ha hb
  have hpre : Dom S (fun i => (DetDLP_W1_SavedCall.preSteps (a i):ℝ)) := by
    unfold DetDLP_W1_SavedCall.preSteps; push_cast; apply Dom.add hS _ (dconst hS 6); exact (dconst hS 7).mul ha (fun _ => by norm_num) (fun _ => by positivity)
  have hpost : Dom S (fun i => (DetDLP_W1_SavedCall.postSteps (a i) (b i):ℝ)) := by
    unfold DetDLP_W1_SavedCall.postSteps; push_cast; apply Dom.add hS _ (dconst hS 15); apply Dom.add hS
    · exact (dconst hS 5).mul (Dom.add hS ha hb) (fun _ => by norm_num) (fun _ => by positivity)
    · exact (dconst hS 2).mul hp (fun _ => by norm_num) (fun _ => by positivity)
  have htime : Dom S (fun i => (DetDLP_W1_SavedCall.extraTime (a i) (b i):ℝ)) := by simpa only [DetDLP_W1_SavedCall.extraTime,Nat.cast_add] using Dom.add hS hpre hpost
  have hspace : Dom S (fun i => (DetDLP_W1_SavedCall.extraSpace A (a i) (b i):ℝ)) := by
    unfold DetDLP_W1_SavedCall.extraSpace; simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    have hc := Dom.add hS (dconst hS A.tapeCount) (dconst hS 2)
    apply Dom.add hS; apply Dom.add hS _ (dconst hS 2)
    · apply Dom.mul hc _ (fun _ => by positivity) (fun _ => by positivity); apply Dom.add hS _ (oneDom hS hST); apply Dom.add hS ha; exact (dconst hS 2).mul hpre (fun _ => by norm_num) (fun _ => by positivity)
    · apply Dom.mul hc _ (fun _ => by positivity) (fun _ => by positivity); exact (dconst hS 2).mul hpost (fun _ => by norm_num) (fun _ => by positivity)
  exact ⟨_,_,_,_,Dom.add (tOne hS hST) ht (liftTime hS hST htime),Dom.add hS hs hspace,fun i => DetDLP_W1_SavedCall.savedCall_run A o (h i)⟩

omit hS hST in
theorem scales_one {b : ℕ} (hb : 1 ≤ b) : 1 ≤ sScale b := scale_ge_one hb

end
end DetDLP_W1_Bounds


