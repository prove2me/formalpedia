-- Prove2me | Definitions.Def_Yukon_0652a097cb56b143b32610e0
-- name    : Yukon_0652a097cb56b143b32610e0
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T23:23:57.148816+00:00
-- url     : https://prove2.me/theorems/eb38dbd1-8e21-4fb1-b5b2-7129f0ca8b62
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.WholeSpaceTrimmedPowerBox6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.WholeSpaceTrimmedPowerBox6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/WholeSpaceTrimmedPowerBox6814.lean
--
--   yukon-proof-operation:certificate-r12-pair-split-8442ad080f05463a78425c80e7b42e9dac8ba051fadd92a7f90339b3064254a4
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMzM1NDQ3NDYzMmQxMTZjZjc2NmExNTljMDE5OWEwOWNkMjgxN2ZiMWNkYzg1M2Q0NDEyODVhYzhlMzUzZDI0ZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMi1wYWlyLXNwbGl0LTg0NDJhZDA4MGYwNTQ2M2E3ODQyNWM4MGU3YjQyZTlkYWM4YmEwNTFmYWRkOTJhN2Y5MDMzOWIzMDY0MjU0YTQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8wNjUyYTA5N2NiNTZiMTQzYjMyNjEwZTAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_6c577048bc498ec04b5f518e













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The old rectangular quotient box forgets the code degree consumed
by S and R. A single 131069-unit trim on every nonconstant (S,R) slice
is sufficient for the six new 270e15-threshold exceptions. -/
namespace ProximityPrize.SubmissionLower.WholeSpaceTrimmedPowerBox6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 15000
open scoped BigOperators
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpacePowerBox6814

variable {K : Type*} [Field K]

def dropCode (j r : ℕ) : ℕ := if j=0 ∧ r=0 then 0 else 131069

abbrev TrimIndex (a : Box) := Σ j : Fin a.n, Σ r : Fin (a.R+1-2*j.val),
  Σ y : Fin (a.U+1), Fin (a.C-dropCode j.val r.val-131071*y.val) × Fin (a.T+1)

def trimExponent (a : Box) (i : TrimIndex a) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![i.2.2.2.1.val,i.1.val,i.2.2.1.val,i.2.1.val,i.2.2.2.2.val]

def trimReceipt (a : Box) : ℕ :=
  ∑ j : Fin a.n, ∑ r : Fin (a.R+1-2*j.val),
    (a.U+1)*(2*(a.C-dropCode j.val r.val)-131071*a.U)*(a.T+1)

theorem trim_card_twice (a : Box) (hc : 131071*a.U+131069≤a.C) :
    2*Fintype.card (TrimIndex a)=trimReceipt a := by
  classical
  simp only [TrimIndex,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  unfold trimReceipt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hd : dropCode j.val r.val≤131069 := by unfold dropCode; split <;> omega
  have hh := twice_sum_affine (a.U+1) (a.C-dropCode j.val r.val) 131071 (by omega)
  simp only [Nat.add_sub_cancel] at hh
  rw [←Finset.sum_mul]
  nlinarith [hh]

theorem trim_support (a : Box) (Q : Poly (K:=K))
    (hc : weightedTotalDegree codeWeights Q<a.C)
    (ht : weightedTotalDegree totalWeights Q≤a.T)
    (hu : weightedTotalDegree middleWeights Q≤a.U)
    (hb : weightedTotalDegree slopeWeights Q≤a.R) :
    ∀ e∈Q.support, e∈Set.range (trimExponent a) := by
  intro e he
  have hc' := (Finset.le_sup (f := Finsupp.weight codeWeights) he).trans_lt hc
  have ht' := (Finset.le_sup (f := Finsupp.weight totalWeights) he).trans ht
  have hu' := (Finset.le_sup (f := Finsupp.weight middleWeights) he).trans hu
  have hb' := (Finset.le_sup (f := Finsupp.weight slopeWeights) he).trans hb
  simp [weight_coords,codeWeights,totalWeights,middleWeights,slopeWeights] at hc' ht' hu' hb'
  refine ⟨⟨⟨e 1,?_⟩,⟨e 3,?_⟩,⟨e 2,by omega⟩,⟨e 0,?_⟩,⟨e 4,by omega⟩⟩,?_⟩
  · dsimp [Box.n]; omega
  · change e 3<a.R+1-2*e 1; omega
  · change e 0<a.C-dropCode (e 1) (e 3)-131071*e 2
    unfold dropCode
    split <;> omega
  · ext i; fin_cases i <;> simp [trimExponent]

theorem exists_not_dvd_power_trimmed
    (V : Submodule K (Poly (K:=K))) [Module.Finite K V]
    (hdim : 627003341034≤Module.finrank K V)
    (hcode : ∀ P∈V, weightedTotalDegree codeWeights P<13050360)
    (htotal : ∀ P∈V, weightedTotalDegree totalWeights P≤1700)
    (hmiddle : ∀ P∈V, weightedTotalDegree middleWeights P≤98)
    (hslope : ∀ P∈V, weightedTotalDegree slopeWeights P≤31)
    (J : Poly (K:=K)) (hJ : J≠0) (a : Box)
    (ha : a.Covers (weightedTotalDegree slopeWeights J)
      (weightedTotalDegree middleWeights J) (weightedTotalDegree totalWeights J))
    (hlin : 131071*a.U+131069≤a.C) (hfit : trimReceipt a<2*627003341034) :
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
  have hs : ∀ v : V, ∀ e∈(f v).support, e∈Set.range (trimExponent a) := by
    intro v e he
    have hq : f v≠0 := by intro hz; simpa [hz] using he
    have hval : v.val=J^a.q*f v := powerQuotient_spec V J a.q hv v
    have hc := hcode v.val v.property
    have ht := htotal v.val v.property
    have hu := hmiddle v.val v.property
    have hb := hslope v.val v.property
    rw [hval,weight_mul _ _ _ (pow_ne_zero _ hJ) hq,weight_pow _ _ hJ] at hc ht hu hb
    have hcJ := WholeSpacePowerBox6814.factor_code_lower J hJ a.loU a.hiB ha.2.2.1 ha.2.1
    have hcq := Nat.mul_le_mul_left a.q hcJ
    have hbq := Nat.mul_le_mul_left a.q ha.1
    have huq := Nat.mul_le_mul_left a.q ha.2.2.1
    have htq := Nat.mul_le_mul_left a.q ha.2.2.2
    apply trim_support a (f v) _ _ _ _ e he
    · dsimp [Box.C]; omega
    · dsimp [Box.T]; omega
    · dsimp [Box.U]; omega
    · dsimp [Box.R]; omega
  have hcard := finrank_le_coefficients (trimExponent a) f hf hs
  have htwice := trim_card_twice a hlin
  omega





end
end ProximityPrize.SubmissionLower.WholeSpaceTrimmedPowerBox6814


