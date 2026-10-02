-- Prove2me | Definitions.Def_Yukon_badab604496abada22e6e52a
-- name    : Yukon_badab604496abada22e6e52a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-01T22:46:20.289856+00:00
-- url     : https://prove2.me/theorems/66c03b8e-0a2d-45f9-b4bd-2d3e96ae5099
-- title:
--   LowerFoundation source module
-- statement:
--   Source module ProximityPrize.SubmissionLower.LowerFoundation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/LowerFoundation.lean
--
--   yukon-proof-operation:lower-foundation-import-compact-Yukon_badab604496abada22e6e52a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNTkxYTg5NjgzNTEzNDY1NWQ2NWRkMjJkNzZkZmFmZDVlMDNhMTllOWQ3Yzg1NTE5OGY5ZjI5NzljNWQzMWNlNiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmxvd2VyLWZvdW5kYXRpb24taW1wb3J0LWNvbXBhY3QtWXVrb25fYmFkYWI2MDQ0OTZhYmFkYTIyZTZlNTJhIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fYmFkYWI2MDQ0OTZhYmFkYTIyZTZlNTJhIiwidiI6Mn0]

import Definitions.Def_Yukon_d8d3fd3210025fc23d8e89b5






















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
section Compact_PackedLegacy


/-! Packed from ProximityPrize.SubmissionLower.A2. -/
section PackedLegacy_A2
namespace ProximityPrize.SubmissionLower.RCN040
open scoped Classical BigOperators WithZero
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN046 RCN037 RCN038 RCN095 RCN114 RCN093 RCN123 RCN121 RCN117 RCN116 RCN125 RCN022
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def adaptiveUnitProjectionFamily_of_active_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   AdaptiveUnitProjectionFamily base p q:=by
 classical
 let lam:=D.lam
 let mu:=D.mu
 let nu:=D.mu*D.lam
 let zProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C =>
   coordinateOfGate (coordinate Omega C.1 2) (hZ C)
 let uProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C =>
   coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)
 let vProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C => Sum.inr {
   embedding:=elementEmbedding Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.allAffineTranscendental C)
   finite:=D.allFinite C
   separable:=D.allSeparable C}
 let gCaps:=flagTrapezoidCaps_flagAlgHom p G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom q T lam mu nu hTsupport
 have hTne:T≠0:=by
   intro hzero
   apply hproper
   rw [hzero]
   exact dvd_zero G
 let sZ:={C:RegularComponent Omega G T H//
   Transcendental Omega (coordinate Omega C.1 2)}
 have hinjZ:Function.Injective (fun C:sZ => C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htZ:∀ C:sZ,
     Transcendental Omega
       (flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (zOrder 0))):=by
   intro C
   simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using C.2
 have hembZ (C:sZ):
     elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 0))) (htZ C)=
       elementEmbedding Omega (CoordinateField Omega C.1.1)
         (coordinate Omega C.1.1 2) C.2:=
   elementEmbedding_congr (htZ C) C.2
     (by simp [zOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hgenZ:∀ C:sZ,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 0))) (htZ C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 2)),
         flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 1))}:
         Set (CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembZ C]
   simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using
     flag_generators_z Omega C.1.1 lam mu nu C.2
 have hfamilyZ:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:sZ => C.1.1) hinjZ lam mu nu zOrder
   htZ hgenZ G T hG
   (fun C => regularComponent_G_mem Omega G T H C.1)
   (fun C => regularComponent_T_mem Omega G T H C.1)
   hproper
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).2
   p.all q.all (p.yz+p.all) (q.yz+q.all)
   (flagMixed p q unitZFlag) hTne
   (by simpa only [gCaps] using gCaps.zOuter)
   (by simpa only [tCaps] using tCaps.zOuter)
   (by simpa only [gCaps] using gCaps.zTotal)
   (by simpa only [tCaps] using tCaps.zTotal)
   (z_flag_trapezoid_budget p q)
 have hsumZ:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (zProj C)) ≤
       flagMixed p q unitZFlag:=by
   have hsplit:=sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RegularComponent Omega G T H => CoordinateField Omega C.1)
     (x:=fun C => coordinate Omega C.1 2) hZ
   change (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (coordinate Omega C.1 2) (hZ C))) ≤ _
   rw [hsplit]
   calc
     (∑ C:sZ,
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1.1)
           (coordinate Omega C.1.1 2) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)))=
         ∑ C:sZ,
           (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
             (elementEmbedding Omega (CoordinateField Omega C.1.1)
               (flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (zOrder 0))) (htZ C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembZ C]
     _ ≤ _:=hfamilyZ.2
 let sU:={C:RegularComponent Omega G T H//
   Transcendental Omega (affineU Omega C.1 D.lam)}
 have hinjU:Function.Injective (fun C:sU => C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htU:∀ C:sU,
     Transcendental Omega
       (flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (uOrder 0))):=by
   intro C
   simpa [uOrder,lam,mu,nu] using C.2
 have hembU (C:sU):
     elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 0))) (htU C)=
       elementEmbedding Omega (CoordinateField Omega C.1.1)
         (affineU Omega C.1.1 D.lam) C.2:=
   elementEmbedding_congr (htU C) C.2
     (by simp [uOrder,lam,mu,nu])
 have hgenU:∀ C:sU,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 0))) (htU C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 2)),
         flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 1))}:
         Set (CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembU C]
   simpa [uOrder,lam,mu,nu] using
     flag_generators_u Omega C.1.1 lam mu nu C.2
 have hfamilyU:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:sU => C.1.1) hinjU lam mu nu uOrder
   htU hgenU G T hG
   (fun C => regularComponent_G_mem Omega G T H C.1)
   (fun C => regularComponent_T_mem Omega G T H C.1)
   hproper
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).1
   p.all q.all (p.zOnly+p.yz+p.all)
   (q.zOnly+q.yz+q.all) (flagMixed p q unitYZFlag) hTne
   (by simpa only [gCaps] using gCaps.uOuter)
   (by simpa only [tCaps] using tCaps.uOuter)
   (by simpa only [gCaps] using gCaps.uTotal)
   (by simpa only [tCaps] using tCaps.uTotal)
   (u_flag_trapezoid_budget p q)
 have hsumU:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (uProj C)) ≤
       flagMixed p q unitYZFlag:=by
   have hsplit:=sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RegularComponent Omega G T H => CoordinateField Omega C.1)
     (x:=fun C => affineU Omega C.1 D.lam) D.uGate
   change (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C))) ≤ _
   rw [hsplit]
   calc
     (∑ C:sU,
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1.1)
           (affineU Omega C.1.1 D.lam) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)))=
         ∑ C:sU,
           (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
             (elementEmbedding Omega (CoordinateField Omega C.1.1)
               (flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (uOrder 0))) (htU C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembU C]
     _ ≤ _:=hfamilyU.2
 let htV:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu
         (MvPolynomial.X (vOrder 0))):=by
   intro C
   simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
     D.allAffineTranscendental C
 have hembV (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 0))) (htV C)=
       elementEmbedding Omega (CoordinateField Omega C.1)
         (affineV Omega C.1 D.mu (D.mu*D.lam))
           (D.allAffineTranscendental C):=
   elementEmbedding_congr (htV C) (D.allAffineTranscendental C)
     (by simp [vOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hgenV:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 0))) (htV C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 2)),
         flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 1))}:
         Set (CoordinateField Omega C.1))=⊤:=by
   intro C
   rw [hembV C]
   simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
     flag_generators_v Omega C.1 lam mu nu (D.allAffineTranscendental C)
 have hinjV:Function.Injective
     (fun C:RegularComponent Omega G T H => C.1):=by
   intro C E hCE
   exact Subtype.ext hCE
 have hfamilyV:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:RegularComponent Omega G T H => C.1)
   hinjV lam mu nu vOrder htV hgenV G T hG
   (fun C => regularComponent_G_mem Omega G T H C)
   (fun C => regularComponent_T_mem Omega G T H C)
   hproper
   (flag_v_outer_positive_of_directional D.lam D.mu G D.directional)
   (p.yz+p.all) (q.yz+q.all)
   (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all)
   (flagMixed p q unitAllFlag) hTne
   (by simpa only [gCaps] using gCaps.vOuter)
   (by simpa only [tCaps] using tCaps.vOuter)
   (by simpa only [gCaps] using gCaps.vTotal)
   (by simpa only [tCaps] using tCaps.vTotal)
   (v_flag_trapezoid_budget p q)
 have hsumV:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (vProj C)) ≤
       flagMixed p q unitAllFlag:=by
   calc
     _=∑ C:RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (affineV Omega C.1 D.mu (D.mu*D.lam))
               (D.allAffineTranscendental C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rfl
     _=∑ C:RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (flagEvaluation Omega C.1 lam mu nu
               (MvPolynomial.X (vOrder 0))) (htV C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembV C]
     _ ≤ _:=hfamilyV.2
 have hvValue (C:RegularComponent Omega G T H):
     coordinateValue Omega (CoordinateField Omega C.1) (vProj C)=
       affineV Omega C.1 D.mu (D.mu*D.lam):=by
   dsimp only [vProj,coordinateValue,SeparableCoordinate.value,Sum.elim_inr]
   exact elementEmbedding_variable Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.allAffineTranscendental C)
 refine {
   zProjection:=zProj
   yzProjection:=uProj
   allProjection:=vProj
   zValue:=?_
   allTranscendental:=?_
   zPole_eq:=?_
   yzPole_eq:=?_
   allPole_eq:=?_
   sum_zDegree_le:=hsumZ
   sum_yzDegree_le:=hsumU
   sum_allDegree_le:=hsumV}
 · intro C
   exact coordinateOfGate_value _ _
 · intro C
   rw [hvValue C]
   exact D.allAffineTranscendental C
 · intro C v
   rw [exponentSetPoleWeight_unitZ]
   change _=RCN187.poleOrder v.val _
   rw [coordinateOfGate_value]
 · intro C v
   rw [exponentSetPoleWeight_unitYZ]
   change _=RCN187.poleOrder v.val _
   rw [coordinateOfGate_value]
   rw [←D.uValue C]
   exact (D.uPole C v).symm
 · intro C v
   rw [exponentSetPoleWeight_unitAll]
   change _=RCN187.poleOrder v.val _
   rw [hvValue C, ←D.allValue C]
   exact (D.allPole C v).symm
end
end ProximityPrize.SubmissionLower.RCN040
end PackedLegacy_A2

/-! Packed from ProximityPrize.SubmissionLower.E7. -/
section PackedLegacy_E7
namespace ProximityPrize.SubmissionLower.RCN265
open scoped Classical
open RCN002 RCN136 RCN243 RCN264 RCN267 RCN344 RCN341 RCN042 RCN037 RCN039 RCN046 RCN142 RCN093 RCN095
noncomputable section
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
def verticalPoint (y z:Omega):Fin 3 → Polynomial Omega:=
 ![Polynomial.C y,Polynomial.X,Polynomial.C z]
def verticalPolynomial (y z:Omega):
   MvPolynomial (Fin 3) Omega →ₐ[Omega] Polynomial Omega:=
 MvPolynomial.aeval (verticalPoint y z)
theorem verticalPolynomial_derivative (y z:Omega)
   (F:MvPolynomial (Fin 3) Omega):
   (verticalPolynomial y z F).derivative=
     verticalPolynomial y z (MvPolynomial.pderiv (1:Fin 3) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp [verticalPolynomial]
 | add P Q hP hQ => simp only [map_add,Polynomial.derivative_add,hP,hQ]
 | mul_X P i hP =>
     fin_cases i <;>
       simp [verticalPolynomial,verticalPoint,Polynomial.derivative_mul] at hP ⊢ <;>
       rw [hP] <;> ring
theorem aeval_verticalPolynomial_eq_coordinateEvaluation
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (y z:Omega)
   (hy:algebraMap Omega (CoordinateField Omega P) y=coordinate Omega P 0)
   (hz:algebraMap Omega (CoordinateField Omega P) z=coordinate Omega P 2)
   (F:MvPolynomial (Fin 3) Omega):
   Polynomial.aeval (coordinate Omega P 1) (verticalPolynomial y z F)=
     coordinateEvaluation Omega P F:=by
 let lhs:MvPolynomial (Fin 3) Omega →ₐ[Omega] CoordinateField Omega P:=
   (Polynomial.aeval (coordinate Omega P 1)).comp (verticalPolynomial y z)
 have hlhs:lhs=coordinateEvaluation Omega P:=by
   apply MvPolynomial.algHom_ext
   intro i
   fin_cases i <;>
     simp [lhs,verticalPolynomial,verticalPoint,coordinate,hy,hz]
 exact AlgHom.congr_fun hlhs F
theorem y_or_z_transcendental_of_regular_polynomial
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (F:MvPolynomial (Fin 3) Omega)
   (hF:F∈P)
   (hFR:MvPolynomial.pderiv (1:Fin 3) F∉P)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   Transcendental Omega (coordinate Omega P 0)∨
     Transcendental Omega (coordinate Omega P 2):=by
 by_contra hYZ
 push_neg at hYZ
 have hYalg:IsAlgebraic Omega (coordinate Omega P 0):=not_not.mp hYZ.1
 have hZalg:IsAlgebraic Omega (coordinate Omega P 2):=not_not.mp hYZ.2
 obtain ⟨y,hy⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 0 hYalg
 obtain ⟨z,hz⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 2 hZalg
 obtain ⟨i,hi⟩:=
   exists_transcendental_coordinate_of_ne_point_kernel Omega P hnonpoint
 have hiR:i=(1:Fin 3):=by
   fin_cases i <;> simp_all
 subst i
 let Q:=verticalPolynomial y z F
 have hQeval:Polynomial.aeval (coordinate Omega P 1) Q=0:=by
   rw [aeval_verticalPolynomial_eq_coordinateEvaluation P y z hy hz F]
   change coordinateEvaluation Omega P F=0
   have hm:F∈RingHom.ker (coordinateEvaluation Omega P).toRingHom:=by
     rwa [coordinateEvaluation_ker Omega P]
   exact hm
 have hQ:Q=0:=by
   apply transcendental_iff_injective.mp hi
   simpa using hQeval
 have hQderiv:Q.derivative=0:=by rw [hQ,Polynomial.derivative_zero]
 have hFReval:coordinateEvaluation Omega P
     (MvPolynomial.pderiv (1:Fin 3) F)=0:=by
   rw [←aeval_verticalPolynomial_eq_coordinateEvaluation P y z hy hz]
   rw [←verticalPolynomial_derivative]
   simpa [Q] using congrArg
     (Polynomial.aeval (coordinate Omega P 1)) hQderiv
 apply hFR
 rw [←coordinateEvaluation_ker Omega P,RingHom.mem_ker]
 exact hFReval
variable {K:Type} [Field K]
theorem regularComponent_y_or_z_transcendental
   (phi:Polynomial K →+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (G T:MvPolynomial (Fin 3) Omega)
   (hdiv:G∣surfaceMap phi F)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   Transcendental Omega (coordinate Omega C.1 0)∨
     Transcendental Omega (coordinate Omega C.1 2):=by
 let H:=regularitySurface phi F
 have hGmem:G∈C.1:=regularComponent_G_mem Omega G T H C
 have hFmem:surfaceMap phi F∈C.1:=by
   obtain ⟨Q,hQ⟩:=hdiv
   rw [hQ]
   exact C.1.mul_mem_right Q hGmem
 have hFRnot:MvPolynomial.pderiv (1:Fin 3) (surfaceMap phi F)∉C.1:=by
   rw [surfaceMap_pderiv_R]
   exact regularComponent_H_not_mem Omega G T H C
 exact y_or_z_transcendental_of_regular_polynomial C.1 (surfaceMap phi F)
   hFmem hFRnot (regularComponent_ne_point Omega G T H C)
section RefinedAdaptiveFamily
variable {G T H:MvPolynomial (Fin 3) Omega}
structure AdaptiveUnitProjectionFamilyYZ
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (p q:FlagDegree) where
 family:AdaptiveUnitProjectionFamily base p q
 lam:Omega
 yzValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1)
       (family.yzProjection C)=affineU Omega C.1 lam
theorem AdaptiveUnitProjectionFamilyYZ.one_le_zCost_add_yzCost
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree}
   (P:AdaptiveUnitProjectionFamilyYZ base p q)
   (phi:Polynomial K →+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (hH:H=regularitySurface phi F)
   (hdiv:G∣surfaceMap phi F)
   (C:RegularComponent Omega G T H):
   1 ≤ P.family.toPrimeFlagBudgetFamily.zCost C+
     P.family.toPrimeFlagBudgetFamily.yzCost C:=by
 subst H
 have hYZ:=regularComponent_y_or_z_transcendental phi F G T hdiv C
 by_cases hZ:Transcendental Omega (coordinate Omega C.1 2)
 · have hzpos:1 ≤ P.family.toPrimeFlagBudgetFamily.zCost C:=
     P.family.one_le_toPrimeFlagBudgetFamily_zCost C hZ
   omega
 · have hZalg:IsAlgebraic Omega (coordinate Omega C.1 2):=
     not_not.mp hZ
   have hY:Transcendental Omega (coordinate Omega C.1 0):=by
     rcases hYZ with hY | hZ'
     · exact hY
     · exact (hZ hZ').elim
   have hU:Transcendental Omega (affineU Omega C.1 P.lam):=by
     exact transcendental_add_smul_of_transcendental_isAlgebraic
       Omega C.1 (coordinate Omega C.1 0) (coordinate Omega C.1 2)
         P.lam hY hZalg
   have hyzpos:1 ≤ P.family.toPrimeFlagBudgetFamily.yzCost C:=by
     apply one_le_coordinateDegree_of_transcendental_value
     rw [P.yzValue C]
     exact hU
   omega
end RefinedAdaptiveFamily
end
end ProximityPrize.SubmissionLower.RCN265
end PackedLegacy_E7

/-! Packed from ProximityPrize.SubmissionLower.DQ. -/
section PackedLegacy_DQ
namespace ProximityPrize.SubmissionLower.RCN041
open scoped Classical
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN093 RCN037 RCN038 RCN040 RCN046 RCN265 RCN095
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def adaptiveUnitProjectionFamilyYZ_of_active_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   AdaptiveUnitProjectionFamilyYZ base p q where
 family:=adaptiveUnitProjectionFamily_of_active_nested p q base hactive hZ
   hSderiv D hG hproper hGsupport hTsupport
 lam:=D.lam
 yzValue:=by
   intro C
   exact coordinateOfGate_value (affineU Omega C.1 D.lam) (D.uGate C)
theorem exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   Nonempty (AdaptiveUnitProjectionFamilyYZ base p q):=by
 obtain ⟨D⟩:=exists_adaptiveNestedProjectionDataActive base hactive hSderiv
 exact ⟨adaptiveUnitProjectionFamilyYZ_of_active_nested p q base hactive hZ
   hSderiv D hG hproper hGsupport hTsupport⟩
end
end ProximityPrize.SubmissionLower.RCN041
end PackedLegacy_DQ

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier19 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.O6. -/
section PackedLegacy_O6
namespace ProximityPrize.SubmissionLower.RCN277
open scoped Classical
open RCN002 RCN005 RCN003 RCN009 RCN001 RCN072 RCN264 RCN136 RCN243 RCN341 RCN265
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
abbrev Poly3:=MvPolynomial (Fin 3) Omega
theorem exists_coordinate_difference_mem_of_isAlgebraic
   (P:Ideal (Poly3 (Omega:=Omega))) [P.IsPrime] (i:Fin 3)
   (hi:IsAlgebraic Omega (coordinate Omega P i)):
   ∃ c:Omega,MvPolynomial.X i-MvPolynomial.C c∈P:=by
 obtain ⟨c,hc⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P i hi
 refine ⟨c,?_⟩
 rw [←aeval_coordinate_ker Omega P]
 change MvPolynomial.aeval (coordinate Omega P)
     (MvPolynomial.X i-MvPolynomial.C c)=0
 simp only [map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C]
 rw [←hc,sub_self]
theorem not_dvd_coordinate_two_sub_C_of_degreeOf_one_pos
   (G:Poly3 (Omega:=Omega)) (hG:G≠0)
   (hdep:0 < G.degreeOf (1:Fin 3)) (c:Omega):
   ¬ G∣(MvPolynomial.X (2:Fin 3)-MvPolynomial.C c):=by
 let H:Poly3 (Omega:=Omega):=
   MvPolynomial.X (2:Fin 3)-MvPolynomial.C c
 have hHne:H≠0:=coordinate_difference_ne_zero Omega 2 c
 have hHdegree:H.degreeOf (1:Fin 3) ≤ 0:=by
   calc
     H.degreeOf (1:Fin 3) ≤
         max ((MvPolynomial.X (2:Fin 3):Poly3).degreeOf 1)
           ((MvPolynomial.C c:Poly3).degreeOf 1):=by
       simpa only [H] using MvPolynomial.degreeOf_sub_le (1:Fin 3)
         (MvPolynomial.X (2:Fin 3):Poly3) (MvPolynomial.C c)
     _=0:=by
       rw [MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2),
         MvPolynomial.degreeOf_C]
       rfl
 intro hdiv
 obtain ⟨A,hA⟩:=hdiv
 have hHA:H=G*A:=by simpa only [H] using hA
 have hAne:A≠0:=by
   intro hzero
   apply hHne
   rw [hHA,hzero,mul_zero]
 have hle:G.degreeOf (1:Fin 3) ≤ H.degreeOf (1:Fin 3):=by
   calc
     G.degreeOf (1:Fin 3) ≤
         G.degreeOf (1:Fin 3)+A.degreeOf (1:Fin 3):=
       Nat.le_add_right _ _
     _=(G*A).degreeOf (1:Fin 3):=by
       rw [MvPolynomial.degreeOf_mul_eq hG hAne]
     _=H.degreeOf (1:Fin 3):=by rw [hHA]
 omega
theorem finite_separable_at_y_of_z_algebraic
   (P:Ideal (Poly3 (Omega:=Omega))) [P.IsPrime]
   (p:ℕ) [CharP Omega p]
   (G:Poly3 (Omega:=Omega))
   (hG:Irreducible G) (hGmem:G∈P)
   (hdep:0 < G.degreeOf (1:Fin 3))
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hY:Transcendental Omega (coordinate Omega P 0))
   (hZ:IsAlgebraic Omega (coordinate Omega P 2)):
   letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
     rationalBaseAlgebra Omega P 0 hY
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=by
 obtain ⟨c,hHmem⟩:=
   exists_coordinate_difference_mem_of_isAlgebraic P 2 hZ
 let H:Poly3 (Omega:=Omega):=
   MvPolynomial.X (2:Fin 3)-MvPolynomial.C c
 have hproper:¬ G∣H:=
   not_dvd_coordinate_two_sub_C_of_degreeOf_one_pos G hG.ne_zero hdep c
 have hHone:H.degreeOf (1:Fin 3) ≤ 0:=by
   calc
     H.degreeOf (1:Fin 3) ≤
         max ((MvPolynomial.X (2:Fin 3):Poly3).degreeOf 1)
           ((MvPolynomial.C c:Poly3).degreeOf 1):=by
       simpa only [H] using MvPolynomial.degreeOf_sub_le (1:Fin 3)
         (MvPolynomial.X (2:Fin 3):Poly3) (MvPolynomial.C c)
     _=0:=by
       rw [MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2),
         MvPolynomial.degreeOf_C]
       rfl
 have hHtwo:H.degreeOf (2:Fin 3) ≤ 1:=by
   calc
     H.degreeOf (2:Fin 3) ≤
         max ((MvPolynomial.X (2:Fin 3):Poly3).degreeOf 2)
           ((MvPolynomial.C c:Poly3).degreeOf 2):=by
       simpa only [H] using MvPolynomial.degreeOf_sub_le (2:Fin 3)
         (MvPolynomial.X (2:Fin 3):Poly3) (MvPolynomial.C c)
     _=1:=by simp
 have hmixed:coordinateMixedDegree Omega G H 0 < p:=by
   rw [coordinateMixedDegree_zero]
   calc
     H.degreeOf 1*G.degreeOf 2+G.degreeOf 1*H.degreeOf 2 ≤
         0*G.degreeOf 2+G.degreeOf 1*1:=
       Nat.add_le_add (Nat.mul_le_mul hHone (Nat.le_refl _))
         (Nat.mul_le_mul (Nat.le_refl _) hHtwo)
     _=G.degreeOf 1:=by simp
     _ < p:=hdegree 1
 exact finite_separable_at_of_original_coordinate_gate Omega P 0 hY p G H
   hG hGmem hHmem hproper hdegree hmixed
theorem exists_separableLiteralCoordinate_y_or_z
   (P:Ideal (Poly3 (Omega:=Omega))) [P.IsPrime]
   (p:ℕ) [CharP Omega p]
   (G T:Poly3 (Omega:=Omega))
   (hG:Irreducible G) (hGmem:G∈P) (hTmem:T∈P)
   (hproper:¬ G∣T)
   (hdep:0 < G.degreeOf (1:Fin 3))
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedZ:coordinateMixedDegree Omega G T 2 < p)
   (hYZ:Transcendental Omega (coordinate Omega P 0)∨
     Transcendental Omega (coordinate Omega P 2)):
   ∃ D:SeparableLiteralCoordinate P,
     D.index=0∨D.index=2:=by
 by_cases hZ:Transcendental Omega (coordinate Omega P 2)
 · have hz:=finite_separable_at_of_original_coordinate_gate
     Omega P 2 hZ p G T hG hGmem hTmem hproper hdegree hmixedZ
   exact ⟨⟨2,hZ,hz.1,hz.2⟩,Or.inr rfl⟩
 · have hY:Transcendental Omega (coordinate Omega P 0):=
     hYZ.resolve_right hZ
   have hZalg:IsAlgebraic Omega (coordinate Omega P 2):=not_not.mp hZ
   have hy:=finite_separable_at_y_of_z_algebraic P p G hG hGmem hdep
     hdegree hY hZalg
   exact ⟨⟨0,hY,hy.1,hy.2⟩,Or.inl rfl⟩
theorem regularComponent_exists_separableLiteralCoordinate6630
   {K:Type} [Field K]
   (phi:Polynomial K →+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (G T:Poly3 (Omega:=Omega))
   (p:ℕ) [CharP Omega p]
   (hdiv:G∣surfaceMap phi F)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hdep:0 < G.degreeOf (1:Fin 3))
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedZ:coordinateMixedDegree Omega G T 2 < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   ∃ D:SeparableLiteralCoordinate C.1,
     D.index=0∨D.index=2:=by
 apply exists_separableLiteralCoordinate_y_or_z C.1 p G T hG
   (regularComponent_G_mem Omega G T (regularitySurface phi F) C)
   (regularComponent_T_mem Omega G T (regularitySurface phi F) C)
   hproper hdep hdegree hmixedZ
 exact regularComponent_y_or_z_transcendental phi F G T hdiv C
end
end ProximityPrize.SubmissionLower.RCN277
end PackedLegacy_O6

/-! Packed from ProximityPrize.SubmissionLower.EV. -/
section PackedLegacy_EV
namespace ProximityPrize.SubmissionLower.RCN153
open scoped Classical
open RCN159 RCN164 RCN213 RCN215 RCN214 RCN238 RCN095 RCN275
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 50000
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance _root_.ProximityPrize.SubmissionLower.RCN153.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN153.instDecidableEq_proximityPrize_1 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN153
end PackedLegacy_EV

/-! Packed from ProximityPrize.SubmissionLower.EW. -/
section PackedLegacy_EW
namespace ProximityPrize.SubmissionLower.RCN154
open scoped Classical
open RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN095 RCN159 RCN159.ResidualStage RCN151 RCN148 RCN149 RCN153 RCN156 RCN158 RCN275 RCN237 RCN213 RCN215 RCN214 RCN234 RCN276 RCN091
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 40000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar]
local instance _root_.ProximityPrize.SubmissionLower.RCN154.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN154.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN154.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN154
end PackedLegacy_EW

/-! Packed from ProximityPrize.SubmissionLower.DR. -/
section PackedLegacy_DR
namespace ProximityPrize.SubmissionLower.RCN043
open scoped Classical
open RCN213 RCN231 RCN238 RCN264 RCN243 RCN095 RCN159 RCN151 RCN156 RCN154 RCN237 RCN215 RCN214 RCN341 RCN046
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar]
local instance _root_.ProximityPrize.SubmissionLower.RCN043.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN043.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN043.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN043
end PackedLegacy_DR

/-! Packed from ProximityPrize.SubmissionLower.O5. -/
section PackedLegacy_O5
namespace ProximityPrize.SubmissionLower.RCN274
open RCN136 RCN267 RCN159 RCN095
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e d:ℕ} [CharP Omega p] {flag:FlagDegree}
end
end ProximityPrize.SubmissionLower.RCN274
end PackedLegacy_O5

/-! Packed from ProximityPrize.SubmissionLower.GN. -/
section PackedLegacy_GN
namespace ProximityPrize.SubmissionLower.RCN314
open scoped Classical
open RCN002 RCN005 RCN003 RCN001 RCN223 RCN238 RCN136 RCN243 RCN264 RCN095 RCN159 RCN158 RCN156 RCN037 RCN039 RCN043 RCN341 RCN274
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
local instance _root_.ProximityPrize.SubmissionLower.RCN314.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN314.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN314.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
theorem degree_bounds_of_polynomialInFlag
   {p:FlagDegree} {F:MvPolynomial (Fin 3) Omega}
   (hF:PolynomialInFlag p F):
   F.degreeOf 0 ≤ p.yz+p.all∧
     F.degreeOf 1 ≤ p.all∧
     F.degreeOf 2 ≤ p.zOnly+p.yz+p.all:=by
 refine ⟨?_,?_,?_⟩
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   exact (Nat.le_add_right (e 0) (e 1)).trans (hF e he).2.1
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   exact (hF e he).1
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   exact (Nat.le_add_left (e 2) (e 0+e 1)).trans (by
     simpa only [Nat.add_assoc] using (hF e he).2.2)
end
end ProximityPrize.SubmissionLower.RCN314
end PackedLegacy_GN

/-! Packed from ProximityPrize.SubmissionLower.GO. -/
section PackedLegacy_GO
namespace ProximityPrize.SubmissionLower.RCN315
open scoped Classical
open RCN002 RCN005 RCN003 RCN001 RCN223 RCN238 RCN136 RCN243 RCN264 RCN267 RCN095 RCN159 RCN158 RCN037 RCN039 RCN046 RCN341 RCN274 RCN275 RCN276
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
local instance _root_.ProximityPrize.SubmissionLower.RCN315.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN315.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN315.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
theorem residualStage_pderiv_one_ne_zero_of_support
   {p e d:ℕ} [CharP Omega p] {flag:FlagDegree}
   {support:ResidualSupportParameters}
   (S:ResidualStage phi Gamma x p e flag d support):
   MvPolynomial.pderiv (1:Fin 3) S.G≠0:=by
 intro hzero
 apply S.regular_proper
 rw [←surfaceMap_pderiv_R]
 obtain ⟨Q,hQ⟩:=S.G_dvd_surface
 refine ⟨MvPolynomial.pderiv (1:Fin 3) Q,?_⟩
 rw [hQ,MvPolynomial.pderiv_mul,hzero,zero_mul,zero_add]
end
end ProximityPrize.SubmissionLower.RCN315
end PackedLegacy_GO

/-! Packed from ProximityPrize.SubmissionLower.GP. -/

/-! Packed from ProximityPrize.SubmissionLower.FR. -/

/-! Packed from ProximityPrize.SubmissionLower.P3. -/

/-! Packed from ProximityPrize.SubmissionLower.B6. -/

/-! Packed from ProximityPrize.SubmissionLower.B7. -/
section PackedLegacy_B7
namespace ProximityPrize.SubmissionLower.RCN089
open RCN136 RCN313 RCN238 RCN275 RCN095 RCN198 RCN086 RCN262 RCN263
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
def reducedGlobalTailCut (phi:Polynomial K →+* Omega)
   (support:ResidualSupportParameters) (F:MvPolynomial (Fin 4) K)
   (d:ℕ):MvPolynomial (Fin 3) Omega :=
 surfaceMap phi
   (reducedAgreementNumerator F support.s d (tailSelector d) 0 0 0)
theorem globalTailCut_sub_reduced_dvd
   (phi:Polynomial K →+* Omega) (support:ResidualSupportParameters)
   (F:MvPolynomial (Fin 4) K) (d:ℕ) :
   surfaceMap phi F ∣ globalTailCut phi F d -
     reducedGlobalTailCut phi support F d:=by
 change surfaceMap phi F ∣
   surfaceMap phi (agreementNumerator F d (tailSelector d) 0 0 0) -
     surfaceMap phi
       (reducedAgreementNumerator F support.s d (tailSelector d) 0 0 0)
 rw [← map_sub]
 exact map_dvd (surfaceMap phi)
   (agreementNumerator_sub_reduced_dvd F support.s d
     (tailSelector d) 0 0 0)
theorem reducedGlobalTailCut_in_flag
   (phi:Polynomial K →+* Omega) (support:ResidualSupportParameters)
   {F:MvPolynomial (Fin 4) K} (H:ResidualSupportData support F)
   (d:ℕ) :
   PolynomialInFlag (reducedResidualAgreementFlag support d)
     (reducedGlobalTailCut phi support F d):=by
 exact surfaceMap_reducedAgreement_in_flag phi support H d
   (tailSelector d) 0 0 0
end
end ProximityPrize.SubmissionLower.RCN089
end PackedLegacy_B7

/-! Packed from ProximityPrize.SubmissionLower.J5. -/
section PackedLegacy_J5
namespace ProximityPrize.SubmissionLower.RCN090
open scoped Classical BigOperators
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN040 RCN041 RCN265 RCN274 RCN198 RCN086 RCN263 RCN089
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+* Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar e w a b s:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance _root_.ProximityPrize.SubmissionLower.RCN090.instDecidableEq_proximityPrize :DecidableEq K:=Classical.decEq K
local instance _root_.ProximityPrize.SubmissionLower.RCN090.instDecidableEq_proximityPrize_1 :DecidableEq Omega:=Classical.decEq Omega
local instance _root_.ProximityPrize.SubmissionLower.RCN090.instDecidableEq_proximityPrize_2 :DecidableEq Iota:=Classical.decEq Iota
theorem exists_reduced_firstTail_activeNestedData_of_caps
   (S:ResidualStage phi Gamma x pchar e flag w (support a b s))
   (hproper:¬ S.G ∣ globalTailCut phi S.F (w + 1))
   (hflagChar:flag.yz + flag.all < pchar ∧ flag.all < pchar ∧
     flag.zOnly + flag.yz + flag.all < pchar)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < pchar) :
   ∃ (base:∀ C:RegularComponent Omega S.G
       (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
       (regularitySurface phi S.F), SeparableLiteralCoordinate C.1),
     ∃ (hactive:∀ C:RegularComponent Omega S.G
         (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
         (regularitySurface phi S.F),
         KaehlerDifferential.D Omega (CoordinateField Omega C.1)
             (coordinate Omega C.1 0) ≠ 0 ∨
           KaehlerDifferential.D Omega (CoordinateField Omega C.1)
             (coordinate Omega C.1 2) ≠ 0),
       ∃ (hZ:∀ C:RegularComponent Omega S.G
           (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
           (regularitySurface phi S.F), LiteralProjectionGate C 2),
         Nonempty (AdaptiveNestedProjectionDataActive base hactive
           (RCN315.residualStage_pderiv_one_ne_zero_of_support S)):=by
 classical
 let supp:=support a b s
 let T:=globalTailCut phi S.F (w + 1)
 let Tred:=reducedGlobalTailCut phi supp S.F (w + 1)
 let H:=regularitySurface phi S.F
 have hd:S.G ∣ T - Tred :=
   S.G_dvd_surface.trans (globalTailCut_sub_reduced_dvd phi supp S.F (w + 1))
 have hproperRed:¬ S.G ∣ Tred:=by
   intro hr
   apply hproper
   have:=hd.add hr
   simpa only [T, Tred, sub_add_cancel] using this
 have hGflag:PolynomialInFlag flag S.G:=S.flag_support
 let Hsupport:ResidualSupportData supp S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 have hTflag:PolynomialInFlag
     (reducedResidualAgreementFlag supp (w + 1)) Tred :=
   reducedGlobalTailCut_in_flag phi supp Hsupport (w + 1)
 obtain ⟨hGY, hGS, hGZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hGflag
 obtain ⟨hTY, hTS, _hTZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hTflag
 have hTY':Tred.degreeOf 0 ≤ 1 + (w + 1) * (2 * (b + s + 3) - 2):=by
   apply hTY.trans_eq
   exact reducedResidualAgreementFlag_ys supp (w + 1)
 have hTS':Tred.degreeOf 1 ≤ (2 * (s + 2) - 2) * (w + 1):=by
   apply hTS.trans_eq
   rfl
 have hGdegree:∀ j:Fin 3, S.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixedZ:coordinateMixedDegree Omega S.G Tred 2 < pchar:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 let choiceData:∀ C:RegularComponent Omega S.G Tred H,
     ∃ B:SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 :=
   fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
     phi S.F S.G Tred pchar S.G_dvd_surface S.irreducible_G hproperRed
     S.y_dependent hGdegree hmixedZ C
 let base:∀ C:RegularComponent Omega S.G Tred H,
     SeparableLiteralCoordinate C.1:=fun C ↦ (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega S.G Tred H,
     (base C).index = 0 ∨ (base C).index = 2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega S.G Tred H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0) ≠ 0 ∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2) ≠ 0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 have hZ:∀ C:RegularComponent Omega S.G Tred H,
     LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     pchar S.G Tred S.irreducible_G
     (regularComponent_G_mem Omega S.G Tred H C)
     (regularComponent_T_mem Omega S.G Tred H C)
     hproperRed hGdegree hmixedZ
 exact ⟨base, hactive, hZ,
   exists_adaptiveNestedProjectionDataActive base hactive
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S)⟩
end
end ProximityPrize.SubmissionLower.RCN090
end PackedLegacy_J5

/-! Packed from ProximityPrize.SubmissionLower.CK. -/
section PackedLegacy_CK
namespace ProximityPrize.SubmissionLower.RCN337
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
variable {K:Type} [Field K] [DecidableEq K]
theorem sum_pairwise_power_factor_degrees_le
   {I:Type*} [Fintype I]
   (R:Polynomial K) (q:I → Polynomial K) (multiplicity:I → ℕ)
   (hR:R≠0)
   (hqMonic:∀ i,(q i).Monic)
   (hqCoprime:Pairwise fun i j↦IsCoprime (q i) (q j))
   (hpow:∀ i,q i^multiplicity i∣R):
   (∑ i,multiplicity i*(q i).natDegree) ≤ R.natDegree:=by
 classical
 have hpowersCoprime:Pairwise fun i j↦
     IsCoprime ((q i)^multiplicity i) ((q j)^multiplicity j):=by
   intro i j hij
   exact (hqCoprime hij).pow
 have hprodDvd:(∏ i,(q i)^multiplicity i)∣R:=
   Fintype.prod_dvd_of_coprime hpowersCoprime hpow
 have hdegree:(∏ i,(q i)^multiplicity i).natDegree=
     ∑ i,multiplicity i*(q i).natDegree:=by
   rw [Polynomial.natDegree_prod_of_monic
     (s:=Finset.univ) (f:=fun i↦(q i)^multiplicity i)
     (fun i _↦(hqMonic i).pow _)]
   apply Finset.sum_congr rfl
   intro i _
   exact Polynomial.natDegree_pow (q i) (multiplicity i)
 rw [←hdegree]
 exact Polynomial.natDegree_le_of_dvd hprodDvd hR
theorem sum_power_factor_degrees_le
   {I:Type*} [Fintype I]
   (R:Polynomial K) (q:I → Polynomial K) (multiplicity:I → ℕ)
   (hR:R≠0)
   (hqIrreducible:∀ i,Irreducible (q i))
   (hqMonic:∀ i,(q i).Monic)
   (hqInjective:Function.Injective q)
   (hpow:∀ i,q i^multiplicity i∣R):
   (∑ i,multiplicity i*(q i).natDegree) ≤ R.natDegree:=by
 apply sum_pairwise_power_factor_degrees_le R q multiplicity hR hqMonic
 · intro i j hij
   apply (hqIrreducible i).coprime_iff_not_dvd.mpr
   intro hdvd
   have hassociated:=
     (hqIrreducible i).associated_of_dvd (hqIrreducible j) hdvd
   have heq:q i=q j:=Polynomial.eq_of_monic_of_associated
     (hqMonic i) (hqMonic j) hassociated
   exact hij (hqInjective heq)
 · exact hpow
theorem sum_grouped_power_factor_degrees_le
   {I:Type*} [Fintype I]
   (R:Polynomial K) (q:I → Polynomial K) (multiplicity:I → ℕ)
   (hR:R≠0)
   (hqIrreducible:∀ i,Irreducible (q i))
   (hqMonic:∀ i,(q i).Monic)
   (hpow:∀ f∈Finset.univ.image q,
     f^(∑ i with q i=f,multiplicity i)∣R):
   (∑ i,multiplicity i*(q i).natDegree) ≤ R.natDegree:=by
 classical
 let roots:Finset (Polynomial K):=Finset.univ.image q
 let grouped:roots → ℕ:=fun f↦∑ i with q i=f.1,multiplicity i
 have hrootsMonic:∀ f:roots,f.1.Monic:=by
   intro f
   obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
   simpa only [hi] using hqMonic i
 have hrootsIrreducible:∀ f:roots,Irreducible f.1:=by
   intro f
   obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
   simpa only [hi] using hqIrreducible i
 have hrootsPow:∀ f:roots,f.1^grouped f∣R:=by
   intro f
   exact hpow f.1 f.2
 have hbound:=sum_power_factor_degrees_le R
   (fun f:roots↦f.1) grouped hR hrootsIrreducible hrootsMonic
     Subtype.val_injective hrootsPow
 have hregroup:
     (∑ f:roots,grouped f*f.1.natDegree)=
       ∑ i,multiplicity i*(q i).natDegree:=by
   change (∑ f:roots,
     (∑ i with q i=f.1,multiplicity i)*f.1.natDegree)=_
   have hattach:
       (∑ f:roots,
         (∑ i with q i=f.1,multiplicity i)*f.1.natDegree)=
       ∑ f∈roots,
         (∑ i with q i=f,multiplicity i)*f.natDegree:=by
     rw [show (Finset.univ:Finset roots)=roots.attach from
       Finset.univ_eq_attach roots]
     exact Finset.sum_attach roots (fun f:Polynomial K↦
       (∑ i with q i=f,multiplicity i)*f.natDegree)
   rw [hattach]
   simp_rw [Finset.sum_mul]
   calc
     (∑ f∈roots,∑ i with q i=f,
         multiplicity i*f.natDegree)=
         ∑ f∈roots,∑ i with q i=f,
           multiplicity i*(q i).natDegree:=by
       apply Finset.sum_congr rfl
       intro f _
       apply Finset.sum_congr rfl
       intro i hi
       rw [(Finset.mem_filter.mp hi).2]
     _=∑ i∈(Finset.univ:Finset I),
         multiplicity i*(q i).natDegree:=
       Finset.sum_fiberwise_of_maps_to
         (s:=Finset.univ) (t:=roots) (g:=q)
         (fun i _↦Finset.mem_image_of_mem q (Finset.mem_univ i)) _
     _=_:=by rfl
 rw [←hregroup]
 exact hbound
end
end ProximityPrize.SubmissionLower.RCN337
end PackedLegacy_CK

/-! Packed from ProximityPrize.SubmissionLower.GY. -/
section PackedLegacy_GY
namespace ProximityPrize.SubmissionLower.RCN328
open scoped Classical BigOperators
open RCN264 RCN095 RCN272 RCN237 RCN039 RCN046 RCN037 RCN341 RCN121
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega Seed:Type} [Field Omega]
 {G T1 T2 H:MvPolynomial (Fin 3) Omega}
 {flag tailFlag1 tailFlag2:FlagDegree}
variable [IsAlgClosed Omega]
end
end ProximityPrize.SubmissionLower.RCN328
end PackedLegacy_GY

/-! Packed from ProximityPrize.SubmissionLower.GX. -/
section PackedLegacy_GX
namespace ProximityPrize.SubmissionLower.RCN325
open scoped Classical BigOperators
open RCN264 RCN095 RCN237
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega Seed:Type} [Field Omega]
 {G T1 H:MvPolynomial (Fin 3) Omega}
 {flag tailFlag1 tailFlag2:FlagDegree}
end
end ProximityPrize.SubmissionLower.RCN325
end PackedLegacy_GX

/-! Packed from ProximityPrize.SubmissionLower.P7. -/
section PackedLegacy_P7
namespace ProximityPrize.SubmissionLower.RCN330
open scoped Classical
open RCN313 RCN231 RCN136 RCN238 RCN086 RCN055 RCN264 RCN243
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K Ω:Type} [Field K] [Field Ω]
theorem selected_globalTailCut_zero_of_lt
   (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (γ:K) (w d:ℕ)
   (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0)
   (hwd:w < d):
   MvPolynomial.aeval (selectedPoint φ selected γ)
     (globalTailCut φ F d)=0:=by
 rw [globalTailCut_eq,map_mul]
 have hzero:MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (numerator K F d))=0:=by
   rw [eval_surfaceMap]
   have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
       polynomialPoint (φ.comp Polynomial.C) (selected γ) γ
         (φ Polynomial.X):=by
     funext i
     fin_cases i <;> rfl
   rw [hv]
   exact polynomialPoint_numerator_zero (φ.comp Polynomial.C) F
     (selected γ) γ (φ Polynomial.X) hsolution d
     (hdegree.trans_lt hwd)
 change MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (numerator K F d))*_=0
 rw [hzero,zero_mul]
theorem globalTailCut_mem_iff
   (φ:Polynomial K →+*Ω) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (d:ℕ)
   (P:Ideal (MvPolynomial (Fin 3) Ω)):
   globalTailCut φ F d∈P ↔ surfaceMap φ (numerator K F d)∈P:=by
 rw [globalTailCut_eq]
 have hc:(-φ Polynomial.X)^d≠0:=tail_scalar_ne_zero φ hφ d
 have hu:IsUnit
     (MvPolynomial.C ((-φ Polynomial.X)^d):MvPolynomial (Fin 3) Ω):=
   (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
 exact P.mul_unit_mem_iff_mem hu
end
end ProximityPrize.SubmissionLower.RCN330
end PackedLegacy_P7

/-! Packed from ProximityPrize.SubmissionLower.B3. -/
section PackedLegacy_B3
namespace ProximityPrize.SubmissionLower.RCN074
open scoped Classical BigOperators
open RCN159 RCN136 RCN238 RCN264 RCN243 RCN086 RCN095 RCN237 RCN325
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar errors w:ℕ} [CharP Omega pchar]
 {flag tailFlag1 tailFlag2:FlagDegree}
 {support:RCN275.ResidualSupportParameters}
abbrev FirstTailComponent
   (S:ResidualStage phi Gamma x pchar errors flag w support):=
 RegularComponent Omega S.G (globalTailCut phi S.F (w+1))
   (regularitySurface phi S.F)
structure DelayedTailMultiplicityProvider
   (S:ResidualStage phi Gamma x pchar errors flag w support) where
 budgetFamily:PrimeFlagBudgetFamily
   (G:=S.G) (T:=globalTailCut phi S.F (w+1))
   (H:=regularitySurface phi S.F) flag tailFlag1
 multiplicity:FirstTailComponent S → ℕ
 cost:FirstTailComponent S → ℕ
 one_le_multiplicity:∀ C,1 ≤ multiplicity C
 tangentYZGate:errors+1 ≤ tailFlag2.yz
 cost_le:∀ C,
   cost C ≤ multiplicity C*budgetFamily.weightedCost tailFlag2 C
 divisor_le:
   (∑ C,multiplicity C*budgetFamily.weightedCost tailFlag2 C) ≤
     flagMixed flag tailFlag1 tailFlag2
 componentBound:∀ C,
   (componentSeeds Omega S.G (globalTailCut phi S.F (w+1))
     (regularitySurface phi S.F) Gamma
     (selectedPoint phi S.selected) C).card ≤ cost C
 dichotomy:∀ C,
   (∃ delay,1 ≤ delay∧delay ≤ multiplicity C∧
     globalTailCut phi S.F (w+1+delay)∉C.1)∨
   ((∀ delay,globalTailCut phi S.F (w+1+delay)∈C.1)∧
     (componentSeeds Omega S.G (globalTailCut phi S.F (w+1))
       (regularitySurface phi S.F) Gamma
       (selectedPoint phi S.selected) C).card ≤
         (errors+1)*budgetFamily.yzCost C)
theorem stage_card_le_flagMixed
   (S:ResidualStage phi Gamma x pchar errors flag w support)
   (P:DelayedTailMultiplicityProvider
     (tailFlag1:=tailFlag1) (tailFlag2:=tailFlag2) S):
   Gamma.card ≤ flagMixed flag tailFlag1 tailFlag2:=by
 classical
 let T1:=globalTailCut phi S.F (w+1)
 let H:=regularitySurface phi S.F
 let point:=selectedPoint phi S.selected
 have hG:∀ gamma∈Gamma,
     MvPolynomial.eval (point gamma) S.G=0:=S.on_component
 have hT1:∀ gamma∈Gamma,
     MvPolynomial.eval (point gamma) T1=0:=by
   intro gamma hgamma
   exact selected_globalTailCut_zero phi S.F S.selected gamma w
     (S.degree_le gamma hgamma) (S.solution gamma hgamma)
 have hH:∀ gamma∈Gamma,
     MvPolynomial.eval (point gamma) H≠0:=by
   intro gamma hgamma
   exact selectedPoint_evaluation phi S.selected gamma
     (MvPolynomial.pderiv (2:Fin 4) S.F) |>.symm ▸ S.regular gamma hgamma
 have hcover:Gamma.card ≤
     ∑ C:RegularComponent Omega S.G T1 H,
       (componentSeeds Omega S.G T1 H Gamma point C).card:=
   card_le_sum_componentSeeds Omega S.G T1 H Gamma point hG hT1 hH
 calc
   Gamma.card ≤ ∑ C:RegularComponent Omega S.G T1 H,
       (componentSeeds Omega S.G T1 H Gamma point C).card:=hcover
   _ ≤ ∑ C:RegularComponent Omega S.G T1 H,P.cost C:=
     Finset.sum_le_sum (fun C _↦P.componentBound C)
   _ ≤ ∑ C:RegularComponent Omega S.G T1 H,
       P.multiplicity C*P.budgetFamily.weightedCost tailFlag2 C:=
     Finset.sum_le_sum (fun C _↦P.cost_le C)
   _ ≤ flagMixed flag tailFlag1 tailFlag2:=P.divisor_le
end
end ProximityPrize.SubmissionLower.RCN074
end PackedLegacy_B3

/-! Packed from ProximityPrize.SubmissionLower.AM. -/
section PackedLegacy_AM
namespace ProximityPrize.SubmissionLower.RCN338
open scoped Classical BigOperators
open RCN095 RCN264 RCN237 RCN121 RCN337
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag firstTailFlag secondTailFlag:FlagDegree}
structure RegularComponentWeightedInertiaResultantCertificate
   (B:PrimeFlagBudgetFamily
     (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ) where
 z:(∑ C,multiplicity C*B.zCost C) ≤
   flagMixed surfaceFlag firstTailFlag unitZFlag
 yz:(∑ C,multiplicity C*B.yzCost C) ≤
   flagMixed surfaceFlag firstTailFlag unitYZFlag
 all:(∑ C,multiplicity C*B.allCost C) ≤
   flagMixed surfaceFlag firstTailFlag unitAllFlag
theorem RegularComponentWeightedInertiaResultantCertificate.divisor_le
   (B:PrimeFlagBudgetFamily
     (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ)
   (C:RegularComponentWeightedInertiaResultantCertificate B multiplicity):
   (∑ component,
     multiplicity component*B.weightedCost secondTailFlag component) ≤
       flagMixed surfaceFlag firstTailFlag secondTailFlag:=by
 have hz:=C.z
 have hyz:=C.yz
 have hall:=C.all
 calc
   (∑ component,
       multiplicity component*B.weightedCost secondTailFlag component)=
     secondTailFlag.zOnly*
         (∑ component,multiplicity component*B.zCost component)+
       secondTailFlag.yz*
         (∑ component,multiplicity component*B.yzCost component)+
       secondTailFlag.all*
         (∑ component,multiplicity component*B.allCost component):=by
     simp only [PrimeFlagBudgetFamily.weightedCost,
       Nat.mul_add,Finset.sum_add_distrib,Finset.mul_sum,
       Nat.mul_left_comm]
   _ ≤ secondTailFlag.zOnly*
         flagMixed surfaceFlag firstTailFlag unitZFlag+
       secondTailFlag.yz*
         flagMixed surfaceFlag firstTailFlag unitYZFlag+
       secondTailFlag.all*
         flagMixed surfaceFlag firstTailFlag unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add
         (Nat.mul_le_mul_left secondTailFlag.zOnly hz)
         (Nat.mul_le_mul_left secondTailFlag.yz hyz))
       (Nat.mul_le_mul_left secondTailFlag.all hall)
   _=flagMixed surfaceFlag firstTailFlag secondTailFlag:=
     (flagMixed_projection_decomposition
       surfaceFlag firstTailFlag secondTailFlag).symm
end
end ProximityPrize.SubmissionLower.RCN338
end PackedLegacy_AM

/-! Packed from ProximityPrize.SubmissionLower.Q3. -/
section PackedLegacy_Q3
namespace ProximityPrize.SubmissionLower.RCN336
open scoped Classical BigOperators
open RCN264 RCN095 RCN237 RCN066 RCN338
noncomputable section
set_option autoImplicit false
variable {Omega Seed:Type} [Field Omega]
 {G T T' T2 H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag firstTailFlag secondTailFlag:FlagDegree}
theorem component_secondTail_card_le_mod
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H)
     surfaceFlag firstTailFlag)
   (C:RegularComponent Omega G T H)
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hpoint_injective:Function.Injective point)
   (hT2flag:PolynomialInFlagMod C.1 secondTailFlag T2)
   (hproper:T2 ∉ C.1)
   (hzero:∀ gamma ∈ componentSeeds Omega G T H S point C,
     MvPolynomial.aeval (point gamma) T2 = 0) :
   (componentSeeds Omega G T H S point C).card ≤
     B.weightedCost secondTailFlag C:=by
 classical
 let component:=componentSeeds Omega G T H S point C
 let points:=component.image point
 have hpointsPrime:∀ v ∈ points,
     C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
   exact componentSeeds_on_prime Omega G T H S point C gamma hgamma
 have hpointsZero:∀ v ∈ points,MvPolynomial.aeval v T2 = 0:=by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
   exact hzero gamma hgamma
 have hbound :=
   RCN066.PrimeFlagZeroBudget.zero_le_congr
     (B.primeBudget C) secondTailFlag T2 hT2flag hproper
     points hpointsPrime hpointsZero
 have hcard:points.card = component.card :=
   Finset.card_image_of_injective component hpoint_injective
 simpa only [points,component,hcard,
   PrimeFlagBudgetFamily.weightedCost] using hbound
def transportedMultiplicity
   (h:G ∣ T - T')
   (multiplicity:RegularComponent Omega G T H → ℕ) :
   RegularComponent Omega G T' H → ℕ :=
 fun C => multiplicity ((regularComponentEquiv h).symm C)
theorem weightedCertificate_of_congruentCut
   (h:G ∣ T - T')
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T') (H:=H)
     surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ)
   (C:RegularComponentWeightedInertiaResultantCertificate B
     (transportedMultiplicity h multiplicity)) :
   RegularComponentWeightedInertiaResultantCertificate
     (PrimeFlagBudgetFamily.ofCongruentCut h B) multiplicity where
 z:=by
   have hz:=C.z
   dsimp only [transportedMultiplicity] at hz
   rw [← (regularComponentEquiv h).sum_comp] at hz
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hz
 yz:=by
   have hyz:=C.yz
   dsimp only [transportedMultiplicity] at hyz
   rw [← (regularComponentEquiv h).sum_comp] at hyz
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hyz
 all:=by
   have hall:=C.all
   dsimp only [transportedMultiplicity] at hall
   rw [← (regularComponentEquiv h).sum_comp] at hall
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hall
end
end ProximityPrize.SubmissionLower.RCN336
end PackedLegacy_Q3
end Compact_PackedLegacy


