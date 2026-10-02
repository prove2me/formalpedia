-- Prove2me | Definitions.Def_Yukon_f65edb3ccd550257604dc1ba
-- name    : Yukon_f65edb3ccd550257604dc1ba
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T03:16:38.875982+00:00
-- url     : https://prove2.me/theorems/de1e0ac0-5b49-438a-a9f1-d2477b022ad2
-- title:
--   LowerFoundation source section 9
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-direct-dependency-Yukon_f65edb3ccd550257604dc1ba
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYTY2M2Q1NDNmODY3ZTQxMjQ4MjYzNDVhNDMyMTQyOWJiZGFiM2UyOTczYjdjNTA2YjFjYzkwYmRlYWRlY2NkMCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tZGlyZWN0LWRlcGVuZGVuY3ktWXVrb25fZjY1ZWRiM2NjZDU1MDI1NzYwNGRjMWJhIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fZjY1ZWRiM2NjZDU1MDI1NzYwNGRjMWJhIiwidiI6Mn0]

import Definitions.Def_Yukon_f80439d484eee6934f5592f5
import Definitions.Def_Yukon_d8ef6d7e0c97cedb755247de
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.A5. -/
section PackedLegacy_A5
namespace ProximityPrize.SubmissionLower.RCN048
open scoped BigOperators
open RCN077 RCN313 RCN217
noncomputable section
variable {K:Type*} [Field K]
public abbrev factorIdeal (F:Poly4 K):Ideal (Poly4 K):=Ideal.span {F}
public theorem H_scaling_mod (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (polyH K (F*Q))=
     Ideal.Quotient.mk (factorIdeal F) Q*Ideal.Quotient.mk (factorIdeal F) (polyH K F):=by
 unfold polyH
 rw [MvPolynomial.pderiv_mul]
 simp only [map_add,map_mul]
 have hz:Ideal.Quotient.mk (factorIdeal F) F=0:=
   Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F)
 rw [hz,zero_mul,add_zero]
 ring
public theorem numerator_scaling_mod (F Q:Poly4 K) (j:ℕ):
   Ideal.Quotient.mk (factorIdeal F) (numerator K (F*Q) j)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*j)*
       Ideal.Quotient.mk (factorIdeal F) (numerator K F j):=by
 have h:=numerator_sub_factor_power_mem F Q j
 rw [←Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul,map_pow,sub_eq_zero] at h
 exact h
public theorem commonTerm_scaling_mod (F Q:Poly4 K) (w j:ℕ) (hj:j≤w)
   (c:ℕ → K) (x:K):
   Ideal.Quotient.mk (factorIdeal F) (commonNumeratorTerm (F*Q) w c x j)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*w)*
       Ideal.Quotient.mk (factorIdeal F) (commonNumeratorTerm F w c x j):=by
 let ev:=Ideal.Quotient.mk (factorIdeal F)
 have he:2*j+2*(w-j)=2*w:=by omega
 unfold commonNumeratorTerm
 simp only [map_mul,map_pow,MvPolynomial.map_C]
 rw [numerator_scaling_mod,H_scaling_mod,mul_pow]
 calc
   _=ev Q^(2*j+2*(w-j))*
       (ev (MvPolynomial.C (c j))*ev (numerator K F j)*
         ev (polyH K F)^(2*(w-j))*ev (MvPolynomial.C x-MvPolynomial.X 0)^j):=by
     rw [pow_add]
     ring
   _=ev Q^(2*w)*
       (ev (MvPolynomial.C (c j))*ev (numerator K F j)*
         ev (polyH K F)^(2*(w-j))*ev (MvPolynomial.C x-MvPolynomial.X 0)^j):=by rw [he]
   _=_:=by ring
public theorem seed_scaling_mod (F Q:Poly4 K) (w:ℕ) (u0 u1:K):
   Ideal.Quotient.mk (factorIdeal F)
       (affineSeedPolynomial u0 u1*polyH K (F*Q)^(2*w))=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*w)*
       Ideal.Quotient.mk (factorIdeal F)
         (affineSeedPolynomial u0 u1*polyH K F^(2*w)):=by
 simp only [map_mul,map_pow]
 rw [H_scaling_mod,mul_pow]
 ring
theorem agreementNumerator_scaling_mod (F Q:Poly4 K) (w:ℕ)
   (c:ℕ → K) (x u0 u1:K):
   Ideal.Quotient.mk (factorIdeal F) (agreementNumerator (F*Q) w c x u0 u1)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*w)*
       Ideal.Quotient.mk (factorIdeal F) (agreementNumerator F w c x u0 u1):=by
 let ev:=Ideal.Quotient.mk (factorIdeal F)
 have hsum:ev (clearedTaylorNumerator (F*Q) w c x)=
     ev Q^(2*w)*ev (clearedTaylorNumerator F w c x):=by
   unfold clearedTaylorNumerator
   simp only [map_sum]
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro j hj
   exact commonTerm_scaling_mod F Q w j (by have:=Finset.mem_range.mp hj;omega) c x
 unfold agreementNumerator
 rw [map_sub,map_sub,hsum,seed_scaling_mod]
 ring
theorem factor_dvd_agreement_sub_power (F Q:Poly4 K) (w:ℕ)
   (c:ℕ → K) (x u0 u1:K):
   F∣agreementNumerator (F*Q) w c x u0 u1-
     Q^(2*w)*agreementNumerator F w c x u0 u1:=by
 rw [←Ideal.mem_span_singleton]
 rw [←Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul,map_pow,
   agreementNumerator_scaling_mod,sub_self]
end
end ProximityPrize.SubmissionLower.RCN048
end PackedLegacy_A5

/-! Packed from ProximityPrize.SubmissionLower.FH. -/
section PackedLegacy_FH
namespace ProximityPrize.SubmissionLower.RCN220
open RCN136 RCN135 RCN138 RCN137 RCN082 RCN350 RCN313 RCN159 RCN217 RCN002 RCN048 RCN095 RCN275 RCN065
noncomputable section
variable {K I:Type} [Field K]
local instance _root_.ProximityPrize.SubmissionLower.RCN220.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN220.instDecidableEq_proximityPrize_1 :DecidableEq I:=Classical.decEq I
abbrev Ω (K:Type) [Field K]:=GenericField K
theorem exists_original_factor_with_first_tail
   {Γ:Finset K} {x:I → K} {p e:ℕ} [CharP (Ω K) p]
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
   (hTail:S.G∣surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1))):
   ∃ F0 Q:MvPolynomial (Fin 4) K,
     Irreducible F0∧0 < F0.degreeOf 1+F0.degreeOf 2+F0.degreeOf 3∧
     S.F=F0*Q∧S.G∣surfaceMap (polynomialEmbedding K) F0∧
     ¬ S.G∣surfaceMap (polynomialEmbedding K) Q∧
     ¬ S.G∣surfaceMap (polynomialEmbedding K) (polyH K F0)∧
     F0∣numerator K F0 (w+1):=by
 classical
 let P:=S.componentIdeal
 letI:P.IsPrime:=S.componentIdeal_isPrime
 have hFne:S.F≠0:=by
   intro hzero
   apply S.regular_proper
   rw [hzero]
   simp [polyH]
 let φC:Polynomial K →+*CoordinateField (Ω K) P:=
   (algebraMap (Ω K) (CoordinateField (Ω K) P)).comp (polynomialEmbedding K)
 let vC:Fin 3 → CoordinateField (Ω K) P:=
   fun i => componentPoint (polynomialEmbedding K) P i.succ
 have hsurfaceZero:MvPolynomial.eval vC (surfaceMap φC S.F)=0:=by
   rw [eval_surfaceMap]
   change MvPolynomial.eval₂Hom (componentCoefficients (polynomialEmbedding K) P)
     (componentPoint (polynomialEmbedding K) P) S.F=0
   rw [component_evaluation]
   rw [coordinateEvaluation_eq_aeval,aeval_coordinate_eq_quotient,
     Ideal.Quotient.eq_zero_iff_mem.mpr S.surface_mem_componentIdeal,map_zero]
 have hφC:Function.Injective φC:=
   (algebraMap (Ω K) (CoordinateField (Ω K) P)).injective.comp
     (polynomialEmbedding_injective K)
 obtain ⟨F0,hF0mem,hF0zero⟩:=exists_active_factor_of_surface_zero
   φC hφC S.F hFne vC hsurfaceZero
 have hF0spec:=activeFactors_spec S.F F0 hF0mem
 have hmapF0mem:surfaceMap (polynomialEmbedding K) F0∈P:=by
   rw [←coordinateEvaluation_ker (Ω K) P]
   rw [eval_surfaceMap] at hF0zero
   change MvPolynomial.eval₂Hom (componentCoefficients (polynomialEmbedding K) P)
     (componentPoint (polynomialEmbedding K) P) F0=0 at hF0zero
   rw [component_evaluation] at hF0zero
   exact hF0zero
 have hGdivF0:S.G∣surfaceMap (polynomialEmbedding K) F0:=
   Ideal.mem_span_singleton.mp hmapF0mem
 obtain ⟨Q,hprod⟩:=hF0spec.2.1
 have hQnot:¬ S.G∣surfaceMap (polynomialEmbedding K) Q:=by
   intro hGQ
   apply S.regular_proper
   rw [hprod,MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul]
   exact dvd_add (dvd_mul_of_dvd_right hGQ _) (dvd_mul_of_dvd_left hGdivF0 _)
 have hH0not:¬ S.G∣surfaceMap (polynomialEmbedding K) (polyH K F0):=by
   intro hGH
   apply S.regular_proper
   rw [hprod,MvPolynomial.pderiv_mul]
   simp only [polyH,map_add,map_mul]
   exact dvd_add (dvd_mul_of_dvd_left hGH _) (dvd_mul_of_dvd_left hGdivF0 _)
 have hscale:=factor_dvd_numerator_sub_power F0 Q (w+1)
 have hdiff:S.G∣surfaceMap (polynomialEmbedding K)
     (numerator K (F0*Q) (w+1)-Q^(2*(w+1))*numerator K F0 (w+1)):=
   hGdivF0.trans (map_dvd (surfaceMap (polynomialEmbedding K)) hscale)
 have htail':S.G∣surfaceMap (polynomialEmbedding K) (numerator K (F0*Q) (w+1)):=by
   simpa only [hprod] using hTail
 have hmul:S.G∣surfaceMap (polynomialEmbedding K)
     (Q^(2*(w+1))*numerator K F0 (w+1)):=by
   simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using dvd_sub htail' hdiff
 have hfactor:S.G∣surfaceMap (polynomialEmbedding K) Q^(2*(w+1))∨
     S.G∣surfaceMap (polynomialEmbedding K) (numerator K F0 (w+1)):=by
   have hmul':S.G∣surfaceMap (polynomialEmbedding K) Q^(2*(w+1))*
       surfaceMap (polynomialEmbedding K) (numerator K F0 (w+1)):=by
     rw [map_mul,map_pow] at hmul
     exact hmul
   exact S.irreducible_G.prime.dvd_or_dvd hmul'
 have hnum:S.G∣surfaceMap (polynomialEmbedding K) (numerator K F0 (w+1)):=by
   rcases hfactor with hpow | hnum
   · exact False.elim (hQnot (Prime.dvd_of_dvd_pow S.irreducible_G.prime
       (by simpa only [map_pow] using hpow)))
   · exact hnum
 have hbase:F0∣numerator K F0 (w+1):=
   (geometric_factor_dvd_iff K (Ω K) F0 (numerator K F0 (w+1))
     hF0spec.1 hF0spec.2.2 S.G S.irreducible_G
     (by simpa only [canonical_geometricSurfaceMap] using hGdivF0)).mp
     (by simpa only [canonical_geometricSurfaceMap] using hnum)
 exact ⟨F0,Q,hF0spec.1,hF0spec.2.2,hprod,hGdivF0,hQnot,hH0not,hbase⟩
theorem original_factor_agreement_proper
   (φ:Polynomial K →+*Ω K) (F0 Q:MvPolynomial (Fin 4) K)
   (G:MvPolynomial (Fin 3) (Ω K))
   (hGdivF0:G∣surfaceMap φ F0)
   (w:ℕ) (c:ℕ → K) (x0 u0 u1:K)
   (hproper:¬G∣surfaceMap φ (agreementNumerator (F0*Q) w c x0 u0 u1)):
   ¬F0∣agreementNumerator F0 w c x0 u0 u1:=by
 intro hF0cut
 have hcut:G∣surfaceMap φ (agreementNumerator F0 w c x0 u0 u1):=
   hGdivF0.trans (map_dvd (surfaceMap φ) hF0cut)
 have hscaled:G∣surfaceMap φ
     (Q^(2*w)*agreementNumerator F0 w c x0 u0 u1):=by
   have h:=dvd_mul_of_dvd_right hcut (surfaceMap φ Q^(2*w))
   simpa only [map_mul,map_pow,mul_comm] using h
 have hdiff:G∣surfaceMap φ
     (agreementNumerator (F0*Q) w c x0 u0 u1-
       Q^(2*w)*agreementNumerator F0 w c x0 u0 u1):=
   hGdivF0.trans (map_dvd (surfaceMap φ)
     (factor_dvd_agreement_sub_power F0 Q w c x0 u0 u1))
 apply hproper
 simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using dvd_add hdiff hscaled
end
end ProximityPrize.SubmissionLower.RCN220
end PackedLegacy_FH

/-! Packed from ProximityPrize.SubmissionLower.FL. -/
section PackedLegacy_FL
namespace ProximityPrize.SubmissionLower.RCN228
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN231 RCN139 RCN229 RCN319 RCN347 RCN311 RCN174
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 30000
variable {K L M:Type} [Field K] [Field L] [Field M]
local instance _root_.ProximityPrize.SubmissionLower.RCN228.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN228.instDecidableEq_proximityPrize_1 :DecidableEq L:=Classical.decEq L
local instance _root_.ProximityPrize.SubmissionLower.RCN228.instDecidableEq_proximityPrize_2 :DecidableEq M:=Classical.decEq M
theorem canonical_polynomiality_of_first_tail
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w seedCap slopeCap:ℕ) [CharP L p]
   (hw:1≤w) (hshort:w+1≤bound) (hchar:bound<p)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hdiv:F∣numerator K F (w+1)):
   specialization L (globalPolynomial coefficients F v hF hreg w) (v 3)
     (MvPolynomial.map coefficients F)=0:=by
 apply global_polynomiality_of_all_tails coefficients F v hF hreg
   p bound w seedCap slopeCap hw hshort hchar hcaps
 intro j hj _
 exact all_tail_jets_zero_of_first_tail_dvd coefficients F v hF hreg w hdiv j hj
end
end ProximityPrize.SubmissionLower.RCN228
end PackedLegacy_FL

/-! Packed from ProximityPrize.SubmissionLower.E4. -/
section PackedLegacy_E4
namespace ProximityPrize.SubmissionLower.RCN258
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN231 RCN139 RCN229 RCN319 RCN347
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 200000
variable {k L M:Type*} [Field k] [Field L] [Field M]
local instance _root_.ProximityPrize.SubmissionLower.RCN258.instDecidableEq_proximityPrize :DecidableEq k:=Classical.decEq k
local instance _root_.ProximityPrize.SubmissionLower.RCN258.instDecidableEq_proximityPrize_1 :DecidableEq L:=Classical.decEq L
local instance _root_.ProximityPrize.SubmissionLower.RCN258.instDecidableEq_proximityPrize_2 :DecidableEq M:=Classical.decEq M
theorem mv_eval_mem (E:Subfield M) (c:k →+*M)
   (hc:∀ a,c a∈E) (v:Fin 4 → M) (hv:∀ i,v i∈E) (Q:Poly4 k):
   MvPolynomial.eval₂Hom c v Q∈E:=by
 induction Q using MvPolynomial.induction_on with
 | C a => simpa using hc a
 | add P Q hP hQ => simpa only [map_add] using E.add_mem hP hQ
 | mul_X P i hP =>
     simpa only [map_mul,MvPolynomial.eval₂Hom_X'] using E.mul_mem hP (hv i)
theorem polynomial_eval_mem (E:Subfield M) (c:L →+*M)
   (P:Polynomial L) (hP:∀ j,c (P.coeff j)∈E) (x:M) (hx:x∈E):
   P.eval₂ c x∈E:=by
 rw [Polynomial.eval₂_eq_sum_range]
 exact E.sum_mem fun j _ => E.mul_mem (hP j) (E.pow_mem hx j)
theorem taylor_coeff_mem (E:Subfield M) (P:Polynomial M)
   (hP:∀ j,P.coeff j∈E) (x:M) (hx:x∈E) (j:ℕ):
   (Polynomial.taylor x P).coeff j∈E:=by
 rw [Polynomial.taylor_coeff]
 apply polynomial_eval_mem E (RingHom.id M) (Polynomial.hasseDeriv j P) _ x hx
 intro n
 simp only [RingHom.id_apply,Polynomial.hasseDeriv_coeff]
 exact E.mul_mem (natCast_mem E _) (hP _)
theorem globalPolynomial_coeff_mem_of_evaluations
   (E:Subfield M) (c:k →+*M) (F:Poly4 k) (v:Fin 4 → M)
   (hF:MvPolynomial.eval₂Hom c v F=0)
   (hreg:MvPolynomial.eval₂Hom c v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (hv0:v 0∈E)
   (hnum:∀ j,MvPolynomial.eval₂Hom c v (numerator k F j)∈E)
   (hH:MvPolynomial.eval₂Hom c v (polyH k F)∈E) (j:ℕ):
   (globalPolynomial c F v hF hreg w).coeff j∈E:=by
 unfold globalPolynomial
 apply taylor_coeff_mem E _ _ _ (E.neg_mem hv0) j
 intro n
 simp only [reconstructedPolynomial,jetPolynomial_coeff]
 split_ifs with hn
 · rw [jetCoefficient_eq_evaluated_numerator]
   exact E.div_mem (E.mul_mem (hnum n) (E.pow_mem (E.inv_mem hH) _))
     (natCast_mem E _)
 · exact E.zero_mem
theorem map_numeratorStep (c:k →+*L) (F Q:Poly4 k) (n:ℕ):
   MvPolynomial.map c (numeratorStep k F n Q)=
     numeratorStep L (MvPolynomial.map c F) n (MvPolynomial.map c Q):=by
 simp only [numeratorStep,clearedStep,polyH,polyG,MvPolynomial.pderiv_map,
   map_sub,map_add,map_mul,map_pow,map_natCast,map_neg,MvPolynomial.map_X]
theorem map_numerator (c:k →+*L) (F:Poly4 k) (n:ℕ):
   MvPolynomial.map c (numerator k F n)=numerator L (MvPolynomial.map c F) n:=by
 induction n with
 | zero => simp
 | succ n ih => rw [numerator_succ,map_numeratorStep,ih,numerator_succ]
theorem mapped_globalPolynomial_coeff_mem
   (E:Subfield M) (c:k →+*L) (φ:L →+*M)
   (hc:∀ a,φ (c a)∈E) (F:Poly4 k) (v:Fin 4 → M)
   (hv:∀ i,v i∈E)
   (hF:MvPolynomial.eval₂Hom φ v (MvPolynomial.map c F)=0)
   (hreg:MvPolynomial.eval₂Hom φ v
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map c F))≠0)
   (w j:ℕ):
   (globalPolynomial φ (MvPolynomial.map c F) v hF hreg w).coeff j∈E:=by
 apply globalPolynomial_coeff_mem_of_evaluations E φ (MvPolynomial.map c F)
   v hF hreg w (hv 0) _ _ j
 · intro n
   rw [←map_numerator c F n,MvPolynomial.eval₂Hom_map_hom]
   exact mv_eval_mem E (φ.comp c) hc v hv (numerator k F n)
 · unfold polyH
   rw [MvPolynomial.pderiv_map,MvPolynomial.eval₂Hom_map_hom]
   exact mv_eval_mem E (φ.comp c) hc v hv (MvPolynomial.pderiv (2:Fin 4) F)
theorem solution_coeff_mem_of_regular_point
   (E:Subfield M) (c:k →+*L) (φ:L →+*M)
   (hc:∀ a,φ (c a)∈E) (F:Poly4 k) (P:Polynomial L) (γ:L) (ξ:M)
   (hsolution:specialization L P γ (MvPolynomial.map c F)=0)
   (hreg:MvPolynomial.eval₂Hom φ (polynomialPoint φ P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map c F))≠0)
   (hv:∀ i,polynomialPoint φ P γ ξ i∈E)
   (p w:ℕ) [CharP M p] (hw:w < p) (hP:P.natDegree ≤ w) (j:ℕ):
   φ (P.coeff j)∈E:=by
 have hmem:=mapped_globalPolynomial_coeff_mem E c φ hc F
   (polynomialPoint φ P γ ξ) hv
   (polynomialPoint_relation φ (MvPolynomial.map c F) P γ ξ hsolution)
   hreg w j
 rw [globalPolynomial_eq_map_of_solution φ (MvPolynomial.map c F) P γ ξ
   hsolution hreg p w hw hP,Polynomial.coeff_map] at hmem
 exact hmem
end
end ProximityPrize.SubmissionLower.RCN258
end PackedLegacy_E4

/-! Packed from ProximityPrize.SubmissionLower.J2. -/
section PackedLegacy_J2
namespace ProximityPrize.SubmissionLower.RCN083
open RCN077 RCN313 RCN269 RCN233 RCN139 RCN347 RCN047 RCN217 RCN048 RCN136 RCN258
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 15000
variable {K L Ω:Type} [Field K] [Field L] [Field Ω]
theorem map_agreementNumerator_base
   (c:K →+*L) (F:Poly4 K) (w:ℕ) (a:ℕ → K) (x u0 u1:K):
   MvPolynomial.map c (agreementNumerator F w a x u0 u1)=
     agreementNumerator (MvPolynomial.map c F) w (fun j => c (a j))
       (c x) (c u0) (c u1):=by
 simp only [agreementNumerator,clearedTaylorNumerator,commonNumeratorTerm,
   affineSeedPolynomial,map_sub,map_sum,map_add,map_mul,map_pow,MvPolynomial.map_C,
   MvPolynomial.map_X,map_numerator,polyH,MvPolynomial.pderiv_map]
theorem globalPolynomial_mul_factor
   (c:K →+*L) (F Q:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom c v F=0)
   (hQ:MvPolynomial.eval₂Hom c v Q≠0)
   (hregF:MvPolynomial.eval₂Hom c v (polyH K F)≠0)
   (hprod:MvPolynomial.eval₂Hom c v (F*Q)=0)
   (hregprod:MvPolynomial.eval₂Hom c v (polyH K (F*Q))≠0)
   (w:ℕ):
   globalPolynomial c (F*Q) v hprod hregprod w=
     globalPolynomial c F v hF hregF w:=by
 let ev:=MvPolynomial.eval₂Hom c v
 change ev F=0 at hF
 change ev Q≠0 at hQ
 change ev (polyH K F)≠0 at hregF
 have hHscale:ev (polyH K (F*Q))=ev (polyH K F)*ev Q:=by
   unfold polyH
   rw [MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul,hF,zero_mul,add_zero]
 have hNscale (j:ℕ):ev (numerator K (F*Q) j)=
     ev Q^(2*j)*ev (numerator K F j):=by
   obtain ⟨A,hA⟩:=factor_dvd_numerator_sub_power F Q j
   have h:=congrArg ev hA
   simp only [map_sub,map_mul,map_pow,hF,zero_mul] at h
   exact sub_eq_zero.mp h
 have hrecon:reconstructedPolynomial c (F*Q) v hprod hregprod w=
     reconstructedPolynomial c F v hF hregF w:=by
   ext j
   simp only [reconstructedPolynomial,jetPolynomial_coeff]
   by_cases hj:j<w+1
   · rw [if_pos hj,if_pos hj]
     rw [jetCoefficient_eq_evaluated_numerator,
       jetCoefficient_eq_evaluated_numerator]
     change ev (numerator K (F*Q) j)*(ev (polyH K (F*Q)))⁻¹^(2*j)/
         (j.factorial:L)=
       ev (numerator K F j)*(ev (polyH K F))⁻¹^(2*j)/
         (j.factorial:L)
     rw [hNscale,hHscale,mul_inv,mul_pow]
     have hcancel:ev Q^(2*j)*(ev Q)⁻¹^(2*j)=1:=by
       rw [←mul_pow,mul_inv_cancel₀ hQ,one_pow]
     calc
       _=(ev Q^(2*j)*(ev Q)⁻¹^(2*j))*
           (ev (numerator K F j)*(ev (polyH K F))⁻¹^(2*j))/
             (j.factorial:L):=by ring
       _=_:=by rw [hcancel,one_mul]
   · rw [if_neg hj,if_neg hj]
 unfold globalPolynomial
 rw [hrecon]
end
end ProximityPrize.SubmissionLower.RCN083
end PackedLegacy_J2
end Compact_PackedLegacy


