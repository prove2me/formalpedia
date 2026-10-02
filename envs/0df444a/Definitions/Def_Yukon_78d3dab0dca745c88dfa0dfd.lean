-- Prove2me | Definitions.Def_Yukon_78d3dab0dca745c88dfa0dfd
-- name    : Yukon_78d3dab0dca745c88dfa0dfd
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T00:14:32.813005+00:00
-- url     : https://prove2.me/theorems/249017f4-8f06-4eff-b5a4-41f063cd6ef9
-- title:
--   LowerFoundation source section 1/9
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-parser-sections-Yukon_78d3dab0dca745c88dfa0dfd
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNTMzMjQ3MWVjNTk3YzMzNWIwMjQ4ZmFkODE0ZGQyZWE4YjcxMTE1M2M4NWI1MDgwMDYwNjA2MTFiMjQ1YTQxZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24tcGFyc2VyLXNlY3Rpb25zLVl1a29uXzc4ZDNkYWIwZGNhNzQ1Yzg4ZGZhMGRmZCIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzc4ZDNkYWIwZGNhNzQ1Yzg4ZGZhMGRmZCIsInYiOjJ9]

import Definitions.Def_Yukon_d8ef6d7e0c97cedb755247de






















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.S. -/
section PackedLegacy_S
namespace ProximityPrize.SubmissionLower.RCN225
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {A:Type*} [CommRing A]
theorem maximalIdeal_pow_succ_lt_pow_of_noetherian_domain
   {S:Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S]
   [IsLocalRing S]
   (hmax:IsLocalRing.maximalIdeal S≠⊥) (n:ℕ):
   IsLocalRing.maximalIdeal S^(n+1) <
     IsLocalRing.maximalIdeal S^n:=by
 let m:=IsLocalRing.maximalIdeal S
 have hle:m^(n+1) ≤ m^n:=Ideal.pow_le_pow_right n.le_succ
 refine lt_of_le_of_ne hle ?_
 intro heq
 have hfg:(m^n).FG:=IsNoetherian.noetherian _
 have hsmul:m^n ≤ m • (m^n):=by
   rw [Ideal.smul_eq_mul, ←pow_succ', ←heq]
 have hzero:m^n=⊥:=
   Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m (m^n) hfg hsmul
     (IsLocalRing.maximalIdeal_le_jacobson ⊥)
 obtain ⟨x,hx,hx0⟩:=SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hmax)
 have hxpow:x^n∈m^n:=Ideal.pow_mem_pow hx n
 rw [hzero,Ideal.mem_bot] at hxpow
 exact pow_ne_zero n (by simpa only [Ideal.mem_bot] using hx0) hxpow
theorem exponent_le_length_local_maximal_pow_of_noetherian_domain
   {S:Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S]
   [IsLocalRing S]
   (hmax:IsLocalRing.maximalIdeal S≠⊥) (n:ℕ):
   (n:ℕ∞) ≤ Module.length S
     (S ⧸ IsLocalRing.maximalIdeal S^n):=by
 rw [Module.length_quotient]
 induction n with
 | zero => simp
 | succ n ih =>
     calc
       ((n+1:ℕ):ℕ∞)=(n:ℕ∞)+1:=by simp
       _ ≤ Order.coheight (IsLocalRing.maximalIdeal S^n)+1:=
         add_le_add_left ih 1
       _ ≤ Order.coheight (IsLocalRing.maximalIdeal S^(n+1)):=
         Order.coheight_add_one_le
           (maximalIdeal_pow_succ_lt_pow_of_noetherian_domain hmax n)
theorem exponent_mul_residueDegree_le_length_quotient_maximal_pow
   {R S:Type*} [CommRing R] [IsLocalRing R]
   [CommRing S] [IsDomain S] [IsNoetherianRing S] [Algebra R S]
   (p:Ideal S) [p.IsMaximal] (hp:p≠⊥)
   [IsLocalHom (algebraMap R (Localization.AtPrime p))]
   [FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime p))] (n:ℕ):
   ((n*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime p)):ℕ):ℕ∞) ≤
       Module.length R (S ⧸ p^n):=by
 let L:=Localization.AtPrime p
 let M:=L ⧸ IsLocalRing.maximalIdeal L^n
 have hmaxL:IsLocalRing.maximalIdeal L≠⊥:=by
   intro hbot
   apply hp
   rw [←IsLocalization.AtPrime.under_maximalIdeal L p,hbot]
   exact Ideal.comap_bot_of_injective (algebraMap S L)
     (IsLocalization.injective L p.primeCompl_le_nonZeroDivisors)
 have hlocal:(n:ℕ∞) ≤ Module.length L M:=
   exponent_le_length_local_maximal_pow_of_noetherian_domain hmaxL n
 have hresidue:Module.length (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField L)=
       Module.finrank (IsLocalRing.ResidueField R)
         (IsLocalRing.ResidueField L):=Module.length_eq_finrank _ _
 have hweighted:((n*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField L):ℕ):ℕ∞) ≤ Module.length R M:=by
   rw [Nat.cast_mul, ←hresidue,
     IsLocalRing.length_restrictScalars R L M]
   exact mul_le_mul_left hlocal _
 let e:=IsLocalization.AtPrime.equivQuotMaximalIdealPow p L n
 have heq:Module.length R (S ⧸ p^n)=Module.length R M:=
   (e.toLinearEquiv.restrictScalars R).length_eq
 exact hweighted.trans_eq heq.symm
abbrev SurfaceQuotient (surface:A):=A ⧸ Ideal.span {surface}
theorem exponent_mul_residueDegree_le_length_span_surface_sup_relation_pow
   {R:Type*} [CommRing R] [IsLocalRing R] [Algebra R A]
   (surface:A)
   (relation:Ideal A)
   (relationBar:Ideal (SurfaceQuotient surface)) [relationBar.IsMaximal]
   (hrelationBar:relationBar=
     Ideal.map (Ideal.Quotient.mk (Ideal.span {surface})) relation)
   [IsDomain (SurfaceQuotient surface)]
   [IsNoetherianRing (SurfaceQuotient surface)]
   (hrelationBarNe:relationBar≠⊥)
   [IsLocalHom (algebraMap R (Localization.AtPrime relationBar))]
   [FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime relationBar))]
   (n:ℕ):
   ((n*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime relationBar)):ℕ):ℕ∞) ≤
     Module.length R (A ⧸ (Ideal.span {surface} ⊔ relation^n)):=by
 let I:Ideal A:=Ideal.span {surface}
 let q:A →ₐ[R] A ⧸ I:=Ideal.Quotient.mkₐ R I
 have hpow:relationBar^n=Ideal.map q (relation^n):=by
   rw [hrelationBar,Ideal.map_pow]
   rfl
 let e₁:(SurfaceQuotient surface ⧸ relationBar^n) ≃ₐ[R]
     (SurfaceQuotient surface ⧸ Ideal.map q (relation^n)):=
   Ideal.quotientEquivAlgOfEq R hpow
 let e₂:(SurfaceQuotient surface ⧸ Ideal.map q (relation^n)) ≃ₐ[R]
     (A ⧸ (I ⊔ relation^n)):=
   DoubleQuot.quotQuotEquivQuotSupₐ R I (relation^n)
 have hlocal:=
   exponent_mul_residueDegree_le_length_quotient_maximal_pow
     (R:=R) relationBar hrelationBarNe n
 exact hlocal.trans_eq (e₁.trans e₂).toLinearEquiv.length_eq
end
end ProximityPrize.SubmissionLower.RCN225
end PackedLegacy_S

/-! Packed from ProximityPrize.SubmissionLower.N. -/
section PackedLegacy_N
namespace ProximityPrize.SubmissionLower.RCN102
open RCN011
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
abbrev FiberCoefficient
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):=
 @Localization.AtPrime (Polynomial (RatFunc Omega)) _ (Ideal.span {q})
   (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
@[reducible] instance fiberLocalizedPlaneSemiring
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Semiring (Polynomial (FiberCoefficient q hq)):=
 Polynomial.commSemiring.toSemiring
def fiberLocalizePlane
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   PlaneRing Omega →+*Polynomial (FiberCoefficient q hq):=
 Polynomial.mapRingHom
   (algebraMap (Polynomial (RatFunc Omega)) (FiberCoefficient q hq))
end
end ProximityPrize.SubmissionLower.RCN102
end PackedLegacy_N

/-! Packed from ProximityPrize.SubmissionLower.Y9. -/
section PackedLegacy_Y9
namespace ProximityPrize.SubmissionLower.RCN106
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN022 RCN264 RCN125 RCN093 RCN120 RCN102 RCN014 RCN226 RCN225 RCN191
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
def indexedComponentFactor (a:A):Polynomial (RatFunc Omega):=
 projectedFactor Omega (CoordinateField Omega (component a).1) order
   (flagEvaluation Omega (component a).1 lam mu nu) (ht a)
abbrev IndexedFactorFiber (q:Polynomial (RatFunc Omega)):=
 {a:A//q=indexedComponentFactor component lam mu nu order ht a}
def indexedFiberRelation
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   Ideal (Polynomial (FiberCoefficient q hq)):=
 Ideal.map (fiberLocalizePlane q hq)
   (relationKernel Omega (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
def indexedFiberRelationBar
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   Ideal (SurfaceQuotient (fiberLocalizePlane q hq surface)):=
 Ideal.map (Ideal.Quotient.mk
   (Ideal.span {fiberLocalizePlane q hq surface}))
     (indexedFiberRelation component lam mu nu order ht q hq a)
theorem indexedFiberRelation_under
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelation component lam mu nu order ht q hq a).comap
     (fiberLocalizePlane q hq)=
       relationKernel Omega (CoordinateField Omega (component a.1).1) order
         (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1):=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let J:=relationKernel Omega (CoordinateField Omega (component a.1).1) order
   (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
 let f:=fiberLocalizePlane q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hJprime:J.IsPrime:=RingHom.ker_isPrime _
 have hcomap:J.comap c=p:=by
   rw [relationKernel_comap_C]
   exact congrArg (fun r => Ideal.span {r}) a.property.symm
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing Omega))
       (J:Set (PlaneRing Omega)):=by
   rw [Set.disjoint_left]
   intro x hx hxJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp hx
   exact hr (hcomap ▸ hxJ)
 change (Ideal.map f J).comap f=J
 change (Ideal.map (algebraMap (PlaneRing Omega) (Polynomial R)) J).comap
   (algebraMap (PlaneRing Omega) (Polynomial R))=J
 exact IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R) hJprime hdisjoint
include hfinite hgen in
theorem indexedFiberRelation_isMaximal
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let J:=relationKernel Omega (CoordinateField Omega (component a.1).1) order
   (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 have hJmax:J.IsMaximal:=relationKernel_isMaximal Omega
   (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
       (hfinite a.1) (hgen a.1)
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hunder:=indexedFiberRelation_under component lam mu nu order ht q hq a
 letI:((indexedFiberRelation component lam mu nu order ht q hq a).under
     (PlaneRing Omega)).IsMaximal:=by
   change ((indexedFiberRelation component lam mu nu order ht q hq a).comap
     (algebraMap (PlaneRing Omega) (Polynomial R))).IsMaximal
   simpa only [fiberLocalizePlane] using hunder ▸ hJmax
 exact Ideal.IsMaximal.of_isLocalization_of_disjoint
   (p.primeCompl.map c.toMonoidHom)
include hcomponent in
theorem indexedFiberRelation_injective
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Function.Injective
     (indexedFiberRelation component lam mu nu order ht q hq):=by
 intro a b hab
 have hunder:=congrArg (Ideal.comap (fiberLocalizePlane q hq)) hab
 rw [indexedFiberRelation_under component lam mu nu order ht q hq a,
   indexedFiberRelation_under component lam mu nu order ht q hq b] at hunder
 have heval:=congrArg (Ideal.comap (planeMap Omega order)) hunder
 rw [relationKernel_contract,relationKernel_contract] at heval
 have hprime:=congrArg (Ideal.comap (flagAlgHom lam mu nu).toRingHom) heval
 rw [flagEvaluation_kernel_contract,flagEvaluation_kernel_contract] at hprime
 have hcomp:component a.1=component b.1:=Subtype.ext hprime
 exact Subtype.ext (hcomponent hcomp)
include hcomponent hfinite hgen in
theorem indexedFiberRelation_pairwise_coprime
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Pairwise fun a b:IndexedFactorFiber component lam mu nu order ht q =>
     IsCoprime (indexedFiberRelation component lam mu nu order ht q hq a)
       (indexedFiberRelation component lam mu nu order ht q hq b):=by
 intro a b hab
 apply Ideal.isCoprime_iff_sup_eq.mpr
 exact (indexedFiberRelation_isMaximal component lam mu nu order ht hfinite hgen
   q hq a).coprime_of_ne
     (indexedFiberRelation_isMaximal component lam mu nu order ht hfinite hgen
       q hq b)
     (fun heq => hab (indexedFiberRelation_injective
       component hcomponent lam mu nu order ht q hq heq))
end
end ProximityPrize.SubmissionLower.RCN106
end PackedLegacy_Y9
end Compact_PackedLegacy


