-- Prove2me | Definitions.Def_Yukon_6c577048bc498ec04b5f518e
-- name    : Yukon_6c577048bc498ec04b5f518e
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T22:57:39.347693+00:00
-- url     : https://prove2.me/theorems/b5edf74a-81ef-4dcc-8319-b1a9c3d52f3f
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.WholeSpacePowerBox6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.WholeSpacePowerBox6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/WholeSpacePowerBox6814.lean
--
--   yukon-proof-operation:certificate-split-51aabbed9959ecd9061cc8edda519f08ca4a7e67fc957c99eaa024e4aaf304ec
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTJhMjllMDc1OTBkODdlMTQ1MTM3ZWU0NzQyMzgwN2E4ZWNkN2ZkOTg3Y2MxMWFiMTg2YTViNzVmZjRjYmMwMSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTUxYWFiYmVkOTk1OWVjZDkwNjFjYzhlZGRhNTE5ZjA4Y2E0YTdlNjdmYzk1N2M5OWVhYTAyNGU0YWFmMzA0ZWMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl82YzU3NzA0OGJjNDk4ZWMwNGI1ZjUxOGUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_3d5a9ed4cebf933826368088













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Power avoidance in the existing contact kernel. The coefficient box is
symbolic: no coefficient vectors or large finite bases are enumerated. -/
namespace ProximityPrize.SubmissionLower.WholeSpacePowerBox6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open scoped BigOperators
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814

variable {K : Type*} [Field K]

structure Box where
  q : ℕ
  loB : ℕ
  hiB : ℕ
  loU : ℕ
  loT : ℕ
  deriving DecidableEq

def Box.R (a : Box) := 31-a.q*a.loB
def Box.U (a : Box) := 98-a.q*a.loU
def Box.T (a : Box) := 1700-a.q*a.loT
def Box.C (a : Box) := 13050360-a.q*(131071*a.loU-a.hiB)
def Box.n (a : Box) := a.R/2+1
def Box.receipt (a : Box) : ℕ :=
  a.n*(a.R+2-a.n)*(a.U+1)*(2*a.C-131071*a.U)*(a.T+1)

def Box.Covers (a : Box) (b u t : ℕ) : Prop :=
  a.loB≤b ∧ b≤a.hiB ∧ a.loU≤u ∧ a.loT≤t

abbrev Index (a : Box) := Σ j : Fin a.n, Σ r : Fin (a.R+1-2*j.val),
  Σ y : Fin (a.U+1), Fin (a.C-131071*y.val) × Fin (a.T+1)

def exponent (a : Box) (i : Index a) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![i.2.2.2.1.val,i.1.val,i.2.2.1.val,i.2.1.val,i.2.2.2.2.val]

theorem twice_sum_affine (n c w : ℕ) (h : w*(n-1)≤c) :
    2*(∑ i : Fin n, (c-w*i.val))=n*(2*c-w*(n-1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n=0
    · subst n; simp
    have hnw : w*n≤c := by simpa using h
    have hprev : w*(n-1)≤c := (Nat.mul_le_mul_left w (Nat.sub_le n 1)).trans hnw
    have hi := ih hprev
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    simp only [Nat.add_sub_cancel]
    have hsub := Nat.sub_add_cancel hnw
    have hsub' := Nat.sub_add_cancel hprev
    have hdouble := Nat.sub_add_cancel (show w*n≤2*c by omega)
    have hdouble' := Nat.sub_add_cancel (show w*(n-1)≤2*c by omega)
    have hn1 : n-1+1=n := by omega
    nlinarith

theorem card_twice (a : Box) (h : 131071*a.U≤a.C) :
    2*Fintype.card (Index a)=a.receipt := by
  classical
  have hn : 2*(a.n-1)≤a.R := by dsimp [Box.n]; omega
  have hj := twice_sum_affine a.n (a.R+1) 2 (by omega)
  have hy := twice_sum_affine (a.U+1) a.C 131071 (by simpa using h)
  have hnj : a.n≤a.R+2 := by dsimp [Box.n]; omega
  have hclosed : (∑ j : Fin a.n, (a.R+1-2*j.val))=a.n*(a.R+2-a.n) := by
    have hp := Nat.sub_add_cancel hn
    have hq := Nat.sub_add_cancel hnj
    have hnn : a.n-1+1=a.n := by simp [Box.n]
    have hr := Nat.sub_add_cancel (show 2*(a.n-1)≤2*(a.R+1) by omega)
    nlinarith
  simp only [Index,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  simp only [←Finset.sum_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  rw [hclosed]
  simp only [Nat.add_sub_cancel] at hy
  unfold Box.receipt
  calc
    _ = a.n*(a.R+2-a.n)*(2*(∑ i : Fin (a.U+1), (a.C-131071*i.val)))*(a.T+1) := by ring
    _ = _ := by rw [hy]; ring

theorem support_box (a : Box) (Q : Poly (K := K))
    (hc : weightedTotalDegree codeWeights Q<a.C)
    (ht : weightedTotalDegree totalWeights Q≤a.T)
    (hu : weightedTotalDegree middleWeights Q≤a.U)
    (hb : weightedTotalDegree slopeWeights Q≤a.R) :
    ∀ e∈Q.support, e∈Set.range (exponent a) := by
  intro e he
  have hc' := (Finset.le_sup (f := Finsupp.weight codeWeights) he).trans_lt hc
  have ht' := (Finset.le_sup (f := Finsupp.weight totalWeights) he).trans ht
  have hu' := (Finset.le_sup (f := Finsupp.weight middleWeights) he).trans hu
  have hb' := (Finset.le_sup (f := Finsupp.weight slopeWeights) he).trans hb
  simp [weight_coords,codeWeights,totalWeights,middleWeights,slopeWeights] at hc' ht' hu' hb'
  refine ⟨⟨⟨e 1,?_⟩,⟨e 3,?_⟩,⟨e 2,by omega⟩,⟨e 0,?_⟩,⟨e 4,by omega⟩⟩,?_⟩
  · dsimp [Box.n]; omega
  · change e 3<a.R+1-2*e 1; omega
  · change e 0<a.C-131071*e 2; omega
  · ext i; fin_cases i <;> simp [exponent]

theorem factor_code_lower (J : Poly (K := K)) (hJ : J≠0) (u b : ℕ)
    (hu : u≤weightedTotalDegree middleWeights J)
    (hb : weightedTotalDegree slopeWeights J≤b) :
    131071*u-b≤weightedTotalDegree codeWeights J := by
  obtain ⟨e,he,hmax⟩ := Finset.exists_mem_eq_sup J.support
    (support_nonempty.mpr hJ) (Finsupp.weight middleWeights)
  have hm : u≤Finsupp.weight middleWeights e := by
    change u≤J.support.sup (Finsupp.weight middleWeights) at hu
    rwa [hmax] at hu
  have hs := (Finset.le_sup (f := Finsupp.weight slopeWeights) he).trans hb
  have hc : Finsupp.weight codeWeights e≤weightedTotalDegree codeWeights J := Finset.le_sup he
  simp [weight_coords,codeWeights,middleWeights,slopeWeights] at hm hs hc
  dsimp only [codeWeights]
  omega

def powerQuotient (V : Submodule K (Poly (K := K))) (J : Poly (K := K)) (q : ℕ)
    (hd : ∀ v : V, J^q∣v.val) (v : V) : Poly (K := K) := Classical.choose (hd v)

theorem powerQuotient_spec (V : Submodule K (Poly (K := K))) (J : Poly (K := K)) (q : ℕ)
    (hd : ∀ v : V, J^q∣v.val) (v : V) : v.val=J^q*powerQuotient V J q hd v :=
  Classical.choose_spec (hd v)

def powerQuotientLinear (V : Submodule K (Poly (K := K))) (J : Poly (K := K)) (q : ℕ)
    (hJ : J≠0) (hd : ∀ v : V, J^q∣v.val) : V →ₗ[K] Poly (K := K) where
  toFun := powerQuotient V J q hd
  map_add' v u := by
    apply mul_left_cancel₀ (pow_ne_zero q hJ)
    rw [mul_add,←powerQuotient_spec,←powerQuotient_spec,←powerQuotient_spec]
    rfl
  map_smul' c v := by
    apply mul_left_cancel₀ (pow_ne_zero q hJ)
    rw [←powerQuotient_spec]
    change c • v.val=J^q*(c • powerQuotient V J q hd v)
    rw [powerQuotient_spec V J q hd v]
    simp only [MvPolynomial.smul_eq_C_mul]
    ac_rfl

theorem exists_not_dvd_power
    (V : Submodule K (Poly (K := K))) [Module.Finite K V]
    (hdim : 627003341034≤Module.finrank K V)
    (hcode : ∀ P∈V, weightedTotalDegree codeWeights P<13050360)
    (htotal : ∀ P∈V, weightedTotalDegree totalWeights P≤1700)
    (hmiddle : ∀ P∈V, weightedTotalDegree middleWeights P≤98)
    (hslope : ∀ P∈V, weightedTotalDegree slopeWeights P≤31)
    (J : Poly (K := K)) (hJ : J≠0) (a : Box)
    (ha : a.Covers (weightedTotalDegree slopeWeights J)
      (weightedTotalDegree middleWeights J) (weightedTotalDegree totalWeights J))
    (hlin : 131071*a.U≤a.C) (hfit : a.receipt<2*627003341034) :
    ∃ P∈V, ¬J^a.q∣P := by
  classical
  by_contra hno
  have hd : ∀ P∈V, J^a.q∣P := by simpa only [not_exists,not_and,not_not] using hno
  let hv : ∀ v : V, J^a.q∣v.val := fun v => hd v.val v.property
  let f := powerQuotientLinear V J a.q hJ hv
  have hf : Function.Injective f := by
    intro v u he
    apply Subtype.ext
    rw [powerQuotient_spec V J a.q hv v,powerQuotient_spec V J a.q hv u]
    exact congrArg (fun Q => J^a.q*Q) he
  have hs : ∀ v : V, ∀ e∈(f v).support, e∈Set.range (exponent a) := by
    intro v e he
    have hq : f v≠0 := by intro hz; simpa [hz] using he
    have hval : v.val=J^a.q*f v := powerQuotient_spec V J a.q hv v
    have hc := hcode v.val v.property
    have ht := htotal v.val v.property
    have hu := hmiddle v.val v.property
    have hb := hslope v.val v.property
    rw [hval,weight_mul _ _ _ (pow_ne_zero _ hJ) hq,weight_pow _ _ hJ] at hc ht hu hb
    have hcJ := factor_code_lower J hJ a.loU a.hiB ha.2.2.1 ha.2.1
    have hcq := Nat.mul_le_mul_left a.q hcJ
    have hbq := Nat.mul_le_mul_left a.q ha.1
    have huq := Nat.mul_le_mul_left a.q ha.2.2.1
    have htq := Nat.mul_le_mul_left a.q ha.2.2.2
    apply support_box a (f v) _ _ _ _ e he
    · dsimp [Box.C]; omega
    · dsimp [Box.T]; omega
    · dsimp [Box.U]; omega
    · dsimp [Box.R]; omega
  have hcard := finrank_le_coefficients (exponent a) f hf hs
  have htwice := card_twice a hlin
  omega





end
end ProximityPrize.SubmissionLower.WholeSpacePowerBox6814


