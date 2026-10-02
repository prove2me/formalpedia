-- Prove2me | Definitions.Def_Yukon_f3cc0d05eb1bfd64c84e78cc
-- name    : Yukon_f3cc0d05eb1bfd64c84e78cc
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T03:29:47.710294+00:00
-- url     : https://prove2.me/theorems/231ca6b7-e707-49d4-ae11-60a49ec98e7c
-- title:
--   LowerFoundation source section 10
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-direct-dependency-Yukon_f3cc0d05eb1bfd64c84e78cc
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNWU0ZWFmMDZkODE1NzA5MTE3MjM0OTYxMDU4YmJhODczMzQwZjVlYTFhZGE1ODMxNjkxZmZhZjRhMDNmZTRjNCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tZGlyZWN0LWRlcGVuZGVuY3ktWXVrb25fZjNjYzBkMDVlYjFiZmQ2NGM4NGU3OGNjIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fZjNjYzBkMDVlYjFiZmQ2NGM4NGU3OGNjIiwidiI6Mn0]

import Definitions.Def_Yukon_f65edb3ccd550257604dc1ba
import Definitions.Def_Yukon_d8ef6d7e0c97cedb755247de
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.EF. -/
section PackedLegacy_EF
namespace ProximityPrize.SubmissionLower.RCN126
open RCN077 RCN231 RCN229 RCN139 RCN319 RCN258
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 200000
variable {k L:Type*} [Field k] [Field L] [Algebra k L]
local instance _root_.ProximityPrize.SubmissionLower.RCN126.instDecidableEq_proximityPrize :DecidableEq k:=Classical.decEq k
local instance _root_.ProximityPrize.SubmissionLower.RCN126.instDecidableEq_proximityPrize_1 :DecidableEq L:=Classical.decEq L
def freshPoint (P:Polynomial L) (γ:L):Fin 4 → RatFunc L:=
 polynomialPoint (algebraMap L (RatFunc L)) P γ RatFunc.X
def jetField (P:Polynomial L) (γ:L):IntermediateField k (RatFunc L):=
 IntermediateField.adjoin k (Set.range (freshPoint P γ))
def coefficientField (P:Polynomial L) (γ:L):IntermediateField k (RatFunc L):=
 IntermediateField.adjoin k
   (insert RatFunc.X (insert (algebraMap L (RatFunc L) γ)
     (Set.range (fun j:ℕ => algebraMap L (RatFunc L) (P.coeff j)))))
@[simp] theorem freshPoint_X (P:Polynomial L) (γ:L):
   freshPoint P γ 0=RatFunc.X:=rfl
@[simp] theorem freshPoint_Z (P:Polynomial L) (γ:L):
   freshPoint P γ 3=algebraMap L (RatFunc L) γ:=rfl
theorem fresh_eval_eq (P:Polynomial L) (γ:L) (Q:Poly4 L):
   MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint P γ) Q=
     algebraMap (Polynomial L) (RatFunc L) (specialization L P γ Q):=by
 rw [freshPoint,eval_polynomialPoint_eq_specialization]
 exact RatFunc.aeval_X_left_eq_algebraMap _
theorem freshPoint_regular (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0):
   MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint P γ)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0:=by
 rw [fresh_eval_eq]
 exact RatFunc.algebraMap_ne_zero hreg
theorem coefficient_mem_of_freshPoint_mem
   (E:IntermediateField k (RatFunc L))
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (hv:∀ i,freshPoint P γ i∈E)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w) (j:ℕ):
   algebraMap L (RatFunc L) (P.coeff j)∈E:=by
 apply solution_coeff_mem_of_regular_point E.toSubfield (algebraMap k L)
   (algebraMap L (RatFunc L)) _ F P γ RatFunc.X hsolution
   (freshPoint_regular F P γ hreg) hv p w hw hP j
 intro a
 change algebraMap k (RatFunc L) a∈E
 exact E.algebraMap_mem a
theorem coefficient_mem_jetField
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w) (j:ℕ):
   algebraMap L (RatFunc L) (P.coeff j)∈jetField (k:=k) P γ:=by
 apply coefficient_mem_of_freshPoint_mem (jetField (k:=k) P γ)
   F P γ hsolution hreg _ p w hw hP j
 intro i
 exact IntermediateField.subset_adjoin k _ ⟨i,rfl⟩
theorem jetField_le_coefficientField (P:Polynomial L) (γ:L):
   jetField (k:=k) P γ ≤ coefficientField (k:=k) P γ:=by
 let E:=coefficientField (k:=k) P γ
 have hX:(RatFunc.X:RatFunc L)∈E:=
   IntermediateField.subset_adjoin k _ (Or.inl rfl)
 have hγ:algebraMap L (RatFunc L) γ∈E:=
   IntermediateField.subset_adjoin k _ (Or.inr (Or.inl rfl))
 have hc:∀ j,algebraMap L (RatFunc L) (P.coeff j)∈E:=
   fun j => IntermediateField.subset_adjoin k _ (Or.inr (Or.inr ⟨j,rfl⟩))
 apply IntermediateField.adjoin_le_iff.mpr
 rintro x ⟨i,rfl⟩
 fin_cases i
 · exact hX
 · exact polynomial_eval_mem E.toSubfield (algebraMap L (RatFunc L)) P hc
     RatFunc.X hX
 · apply polynomial_eval_mem E.toSubfield (algebraMap L (RatFunc L))
     P.derivative _ RatFunc.X hX
   intro j
   rw [Polynomial.coeff_derivative,map_mul]
   exact E.mul_mem (hc _) (by simpa using E.natCast_mem (j+1))
 · exact hγ
theorem coefficientField_le_jetField
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w):
   coefficientField (k:=k) P γ ≤ jetField (k:=k) P γ:=by
 apply IntermediateField.adjoin_le_iff.mpr
 intro x hx
 rcases hx with rfl | hx
 · exact IntermediateField.subset_adjoin k _ ⟨0,rfl⟩
 rcases hx with rfl | hx
 · exact IntermediateField.subset_adjoin k _ ⟨3,rfl⟩
 obtain ⟨j,rfl⟩:=hx
 exact coefficient_mem_jetField F P γ hsolution hreg p w hw hP j
theorem fresh_jetField_eq_coefficientField
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w):
   jetField (k:=k) P γ=coefficientField (k:=k) P γ:=
 le_antisymm (jetField_le_coefficientField P γ)
   (coefficientField_le_jetField F P γ hsolution hreg p w hw hP)
end
end ProximityPrize.SubmissionLower.RCN126
end PackedLegacy_EF

/-! Packed from ProximityPrize.SubmissionLower.GS. -/
section PackedLegacy_GS
namespace ProximityPrize.SubmissionLower.RCN321
noncomputable section
variable {k B E:Type} [Field k] [Field B] [Field E]
 [Algebra k B] [Algebra B E] [Algebra k E] [IsScalarTower k B E]
theorem trdeg_le_one_of_tower
   (hE:Algebra.trdeg k E ≤ 2) (htrans:Algebra.Transcendental B E):
   Algebra.trdeg k B ≤ 1:=by
 letI:Algebra.Transcendental B E:=htrans
 have hb:0 < Algebra.trdeg B E:=trdeg_pos B E
 have hsum:Algebra.trdeg k B+Algebra.trdeg B E=Algebra.trdeg k E:=
   trdeg_add_eq k B
 have hab:Algebra.trdeg k B+Algebra.trdeg B E ≤ 2:=by
   rw [hsum]
   exact hE
 by_contra hnot
 have ha:(1:Cardinal) < Algebra.trdeg k B:=lt_of_not_ge hnot
 have htwo:(2:Cardinal) ≤ Algebra.trdeg k B:=by
   have h:=Cardinal.add_one_le_of_lt ha
   norm_num at h
   exact h
 have hbone:(1:Cardinal) ≤ Algebra.trdeg B E:=Cardinal.one_le_iff_pos.mpr hb
 have hthree:(3:Cardinal) ≤ Algebra.trdeg k B+Algebra.trdeg B E:=by
   calc
     (3:Cardinal)=2+1:=by norm_num
     _ ≤ _:=add_le_add htwo hbone
 have:(3:Cardinal) ≤ 2:=hthree.trans hab
 norm_num at this
section RationalExtension
variable {k L:Type} [Field k] [Field L] [Algebra k L]
theorem coefficient_trdeg_le_one_of_rational_extension
   (B:IntermediateField k L) (E:IntermediateField k (RatFunc L))
   (hmap:B.map (IsScalarTower.toAlgHom k L (RatFunc L)) ≤ E)
   (hX:(RatFunc.X:RatFunc L)∈E)
   (hE:Algebra.trdeg k E ≤ 2):Algebra.trdeg k B ≤ 1:=by
 let f:L →ₐ[k] RatFunc L:=IsScalarTower.toAlgHom k L (RatFunc L)
 let bToE:B →ₐ[k] E:=
   (IntermediateField.inclusion hmap).comp (B.equivMap f).toAlgHom
 letI:Algebra B E:=bToE.toRingHom.toAlgebra
 letI:IsScalarTower k B E:=IsScalarTower.of_algebraMap_eq fun c => by
   change bToE (algebraMap k B c)=algebraMap k E c
   exact bToE.commutes c
 let xE:E:=⟨RatFunc.X,hX⟩
 have hcomp:RingHom.comp (algebraMap L (RatFunc L)) B.val=
     RingHom.comp E.val (algebraMap B E):=by
   ext b
   rfl
 have hxE:Transcendental B xE:=
   (show Transcendental L (RatFunc.X:RatFunc L) from RatFunc.transcendental_X).of_ringHom_of_comp_eq
     B.val E.val B.val.injective hcomp
 exact trdeg_le_one_of_tower hE ⟨xE,hxE⟩
end RationalExtension
end
end ProximityPrize.SubmissionLower.RCN321
end PackedLegacy_GS

/-! Packed from ProximityPrize.SubmissionLower.A7. -/
section PackedLegacy_A7
namespace ProximityPrize.SubmissionLower.RCN062
open RCN126
noncomputable section
variable {k L:Type} [Field k] [Field L] [Algebra k L]
def baseCoefficientField (P:Polynomial L) (γ:L):IntermediateField k L:=
 IntermediateField.adjoin k
   (insert γ (Set.range (fun j:ℕ => P.coeff j)))
theorem baseCoefficientField_map_le (P:Polynomial L) (γ:L):
   (baseCoefficientField (k:=k) P γ).map (IsScalarTower.toAlgHom k L (RatFunc L)) ≤
     coefficientField (k:=k) P γ:=by
 rw [IntermediateField.map_le_iff_le_comap]
 apply IntermediateField.adjoin_le_iff.mpr
 intro x hx
 rcases hx with h | hx
 · rw [h]
   change algebraMap L (RatFunc L) γ∈coefficientField (k:=k) P γ
   exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inl rfl))
 obtain ⟨j,hj⟩:=hx
 rw [←hj]
 change algebraMap L (RatFunc L) (P.coeff j)∈coefficientField (k:=k) P γ
 exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inr ⟨j,rfl⟩))
theorem baseCoefficientField_trdeg_le_one
   (P:Polynomial L) (γ:L)
   (hE:Algebra.trdeg k (coefficientField (k:=k) P γ) ≤ 2):
   Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1:=by
 apply RCN321.coefficient_trdeg_le_one_of_rational_extension
   (B:=baseCoefficientField (k:=k) P γ)
   (E:=coefficientField (k:=k) P γ)
   (baseCoefficientField_map_le P γ) _ hE
 exact IntermediateField.subset_adjoin k _ (Or.inl rfl)
end
end ProximityPrize.SubmissionLower.RCN062
end PackedLegacy_A7

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier21 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.EH. -/
section PackedLegacy_EH
namespace ProximityPrize.SubmissionLower.RCN129
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
 [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
theorem trdeg_le_one_of_functionField:Algebra.trdeg K L ≤ 1:=by
 classical
 unfold Algebra.trdeg
 refine ciSup_le' fun s↦Cardinal.mk_le_one_iff_set_subsingleton.mpr ?_
 intro x hx y hy
 by_contra hxy
 let i:s.1:=⟨x,hx⟩
 let j:s.1:=⟨y,hy⟩
 have ht:Transcendental K x:=s.2.transcendental i
 letI:FiniteDimensional (IntermediateField.adjoin K ({x}:Set L)) L:=
   FunctionField.finiteDimensional_of_adjoin_transcendental ht
 have hyalg:IsAlgebraic (Algebra.adjoin K ({x}:Set L)) y:=
   IntermediateField.isAlgebraic_adjoin_iff.mp
     (Algebra.IsAlgebraic.isAlgebraic y)
 have hji:j∉({i}:Set s.1):=by
   simpa only [Set.mem_singleton_iff] using
     (show j≠i from fun h↦hxy (congrArg Subtype.val h).symm)
 have hytr:=s.2.transcendental_adjoin hji
 have himage:(fun z:s.1↦(z:L)) '' ({i}:Set s.1)={x}:=by
   simp [i]
 change Transcendental (Algebra.adjoin K
   ((fun z:s.1↦(z:L)) '' ({i}:Set s.1))) y at hytr
 rw [himage] at hytr
 exact hytr hyalg
end
end ProximityPrize.SubmissionLower.RCN129
end PackedLegacy_EH
end Compact_PackedLegacy


