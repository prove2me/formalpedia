-- Prove2me | Definitions.Def_Yukon_1dcaba27524a91653739dbc3
-- name    : Yukon_1dcaba27524a91653739dbc3
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T08:42:27.128842+00:00
-- url     : https://prove2.me/theorems/8a149530-28dc-43c2-ad70-fcc05ce78675
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailSharpGate.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailSharpGate.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailSharpGate.lean
--
--   yukon-proof-operation:foundation-direct-ba54a670a13fcef995890108f2b4c266f4a246010da89e35351f8b5f2ee03eff
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYmU4MTE4MDVlYjlmNDZmZmYwZjZjYzUxZGEwOTJhZDQ4NjYxMjRhNGViMzIwYjlkMDVjYzQzOTAyMWRkYzE5YyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWJhNTRhNjcwYTEzZmNlZjk5NTg5MDEwOGYyYjRjMjY2ZjRhMjQ2MDEwZGE4OWUzNTM1MWY4YjVmMmVlMDNlZmYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8xZGNhYmEyNzUyNGE5MTY1MzczOWRiYzMiLCJ2IjoyfQ]

import Definitions.Def_Yukon_52f7c2cb3790c155905697c9













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailSharpGate
set_option maxHeartbeats 1000000
open RCN002 RCN004 RCN005 RCN095 RCN125 RCN371
open scoped BigOperators

/-- A prime curve with two proper equations and a transcendental Z coordinate
has separating Z projection whenever its sharp flag-trapezoid degree is below
the characteristic. No rectangular coordinate-degree gate is required. -/
theorem finite_separable_z_of_flag_gate {Omega : Type} [Field Omega]
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (hZ : Transcendental Omega (coordinate Omega P 2))
    (prime : Nat) [CharP Omega prime]
    (G T : MvPolynomial (Fin 3) Omega)
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P)
    (hproper : ¬ G ∣ T)
    (hR : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (pG pT : FlagDegree)
    (hGflag : RCN095.PolynomialInFlag pG G)
    (hTflag : RCN095.PolynomialInFlag pT T)
    (hsmall : flagMixed pG pT unitZFlag < prime) :
    letI := rationalBaseAlgebra Omega P 2 hZ
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega P) ∧
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P) := by
  let Q : Unit → Ideal (MvPolynomial (Fin 3) Omega) := fun _ => P
  have hinj : Function.Injective Q := by
    intro i j _
    exact Subsingleton.elim i j
  letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
    rationalBaseAlgebra Omega P 2 hZ
  have htZ : ∀ i : Unit, Transcendental Omega
      (RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 0))) := by
    intro i
    simpa [Q, zOrder, Equiv.swap_apply_def] using hZ
  have hembZ (i : Unit) :
      RCN022.elementEmbedding Omega (CoordinateField Omega (Q i))
        (RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 0))) (htZ i) =
      RCN022.elementEmbedding Omega (CoordinateField Omega P) (coordinate Omega P 2) hZ :=
    by
      have hx : RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 0)) =
          coordinate Omega P 2 := by simp [Q, zOrder]
      simp only [hx]
      rfl
  have hgenZ : ∀ i : Unit,
      letI : Algebra (RatFunc Omega) (CoordinateField Omega (Q i)) :=
        (RCN022.elementEmbedding Omega (CoordinateField Omega (Q i))
          (RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 0)))
          (htZ i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc Omega)
        ({RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 2)),
          RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 1))} :
            Set (CoordinateField Omega (Q i))) = ⊤ := by
    intro i
    rw [hembZ i]
    simpa [Q, zOrder, Equiv.swap_apply_def] using RCN093.flag_generators_z Omega P 0 0 0 hZ
  have hfamily := RCN093.finite_sum_flag_finrank_trapezoid
    (K := Omega) (Q := Q) hinj 0 0 0 zOrder htZ hgenZ
      G T hG (fun _ => hGmem) (fun _ => hTmem) hproper
      (by simpa using (RCN117.flag_u_z_outer_positive_of_pderiv 0 0 G hR).2)
      pG.all pT.all (pG.yz + pG.all) (pT.yz + pT.all)
      (flagMixed pG pT unitZFlag) (by
        intro hzero
        apply hproper
        rw [hzero]
        exact dvd_zero G)
      (by
        simpa using (RCN123.flagTrapezoidCaps_flagAlgHom pG G 0 0 0
          ((support_subset_flagSupport_iff pG G).2 hGflag)).zOuter)
      (by
        simpa using (RCN123.flagTrapezoidCaps_flagAlgHom pT T 0 0 0
          ((support_subset_flagSupport_iff pT T).2 hTflag)).zOuter)
      (by
        simpa using (RCN123.flagTrapezoidCaps_flagAlgHom pG G 0 0 0
          ((support_subset_flagSupport_iff pG G).2 hGflag)).zTotal)
      (by
        simpa using (RCN123.flagTrapezoidCaps_flagAlgHom pT T 0 0 0
          ((support_subset_flagSupport_iff pT T).2 hTflag)).zTotal)
      (RCN121.z_flag_trapezoid_budget pG pT)
  have hfd : FiniteDimensional (RatFunc Omega) (CoordinateField Omega P) := by
    convert hfamily.1 () using 1
    congr 1
    exact congrArg (fun e : RatFunc Omega →ₐ[Omega] CoordinateField Omega P => e.toRingHom.toAlgebra) (hembZ ()).symm
  have hrank : Module.finrank (RatFunc Omega) (CoordinateField Omega P) ≤
      flagMixed pG pT unitZFlag := by
    have hs := hfamily.2
    simp only [Fintype.sum_unique] at hs
    convert hs using 1
    congr 2
    exact congrArg (fun e : RatFunc Omega →ₐ[Omega] CoordinateField Omega P => e.toRingHom.toAlgebra) (hembZ ()).symm
  letI := hfd
  refine ⟨hfd, ⟨fun x => ?_⟩⟩
  have hint : IsIntegral (RatFunc Omega) x := Algebra.IsIntegral.isIntegral x
  exact (RCN364.integral_and_separable_of_small_annihilator prime
    (minpoly (RatFunc Omega) x) x (minpoly.ne_zero hint) (minpoly.aeval _ _)
    ((minpoly.natDegree_le (A := RatFunc Omega) x).trans_lt (hrank.trans_lt hsmall))).2
end ProximityPrize.SubmissionLower.BoundaryTailSharpGate


