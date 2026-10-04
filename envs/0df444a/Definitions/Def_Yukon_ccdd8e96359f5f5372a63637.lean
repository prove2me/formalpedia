-- Prove2me | Definitions.Def_Yukon_ccdd8e96359f5f5372a63637
-- name    : Yukon_ccdd8e96359f5f5372a63637
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T02:07:55.489091+00:00
-- url     : https://prove2.me/theorems/a15a5640-a9ea-4c7e-89d5-067026b591c6
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourcePrimeFamily6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourcePrimeFamily6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourcePrimeFamily6814.lean
--
--   yukon-proof-operation:certificate-b56-8816f47da3702b23f27cc76636d2c95fb0c31490e8fa472aecd87e4f902b4ac8
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODk2NWMzMzYwY2Q4N2YwZGU1Yzc4MTRjMTcwZWVjNjkwMThiMGJlNmMxNGU0OTEwN2U5ZDY4YmY1NjI3NWJlNiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni04ODE2ZjQ3ZGEzNzAyYjIzZjI3Y2M3NjYzNmQyYzk1ZmIwYzMxNDkwZThmYTQ3MmFlY2Q4N2U0ZjkwMmI0YWM4IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fY2NkZDhlOTYzNTlmNWY1MzcyYTYzNjM3IiwidiI6Mn0]

import Definitions.Def_Yukon_dce13deb293f5cbe7d847dbd














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Apply the shared bound to actual prime coordinate fields. Coordinate
generation and distinct relation kernels are discharged by the canonical
coordinate-field construction, rather than requested as count suppliers. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePrimeFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN002 RCN011 RCN022 RCN116 RCN095 RCN093 RCN123 RCN121
open RCN125 (flagAlgHom zOrder uOrder vOrder)
open MovingSourceProjectionFamily6814 MovingSourceSharedFamily6814

public theorem embedding_congr
    {K E : Type} [Field K] [Field E] [Algebra K E]
    {x y : E} (hx : Transcendental K x) (hy : Transcendental K y) (h : x=y) :
    elementEmbedding K E x hx=elementEmbedding K E y hy := by
  subst y
  rfl

theorem flag_generators_axis
    (K : Type) [Field K] (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (axis : Axis) (lam mu nu : K)
    (ht : Transcendental K (flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0)))) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      (elementEmbedding K (CoordinateField K P)
        (flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra
    IntermediateField.adjoin (RatFunc K)
      ({flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 2)),
        flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 1))} :
        Set (CoordinateField K P))=⊤ := by
  cases axis with
  | z =>
    have hz : Transcendental K (coordinate K P 2) := by
      simpa [Axis.order,zOrder,Equiv.swap_apply_def] using ht
    have he : elementEmbedding K (CoordinateField K P)
        (flagEvaluation K P lam mu nu (MvPolynomial.X (Axis.z.order 0))) ht=
        elementEmbedding K (CoordinateField K P) (coordinate K P 2) hz :=
      embedding_congr ht hz (by simp [Axis.order,zOrder])
    rw [he]
    simpa [Axis.order,zOrder,Equiv.swap_apply_def] using flag_generators_z K P lam mu nu hz
  | u =>
    have hu : Transcendental K (affineU K P lam) := by
      simpa [Axis.order,uOrder] using ht
    have he : elementEmbedding K (CoordinateField K P)
        (flagEvaluation K P lam mu nu (MvPolynomial.X (Axis.u.order 0))) ht=
        elementEmbedding K (CoordinateField K P) (affineU K P lam) hu :=
      embedding_congr ht hu (by simp [Axis.order,uOrder])
    rw [he]
    simpa [Axis.order,uOrder] using flag_generators_u K P lam mu nu hu
  | v =>
    have hv : Transcendental K (affineV K P mu nu) := by
      simpa [Axis.order,vOrder,Equiv.swap_apply_def] using ht
    have he : elementEmbedding K (CoordinateField K P)
        (flagEvaluation K P lam mu nu (MvPolynomial.X (Axis.v.order 0))) ht=
        elementEmbedding K (CoordinateField K P) (affineV K P mu nu) hv :=
      embedding_congr ht hv (by simp [Axis.order,vOrder])
    rw [he]
    simpa [Axis.order,vOrder,Equiv.swap_apply_def] using flag_generators_v K P lam mu nu hv

theorem finite_sum_prime_fields
    (K : Type) [Field K] (axis : Axis) (lam mu nu : K) {I : Type} [Fintype I]
    (P : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (P i).IsPrime]
    (hinj : Function.Injective P)
    (ht : ∀ i, Transcendental K
      (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0))))
    (B H : MvPolynomial (Fin 3) K) (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBmem : ∀ i, B∈P i) (hHmem : ∀ i, H∈P i)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) := fun i =>
      (elementEmbedding K (CoordinateField K (P i))
        (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0)))
          (ht i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ flagMixed p q axis.flag := by
  have hroot (A : MvPolynomial (Fin 3) K) (ha : ∀ i, A∈P i) :
      ∀ i, flagEvaluation K (P i) lam mu nu (flagAlgHom lam mu nu A)=0 := by
    intro i
    rw [flagEvaluation_flag]
    change A∈RingHom.ker (coordinateEvaluation K (P i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact ha i
  exact finite_sum_finrank_coprime_flags K axis lam mu nu
    (fun i => CoordinateField K (P i)) (fun i => flagEvaluation K (P i) lam mu nu)
    ht (fun i => flag_generators_axis K (P i) axis lam mu nu (ht i))
    (flagEvaluation_kernel_family_injective K P hinj lam mu nu)
    B H hB hH hrel (hroot B hBmem) (hroot H hHmem) p q hp hq

/-- The three shared bounds used by the new source pair. -/
theorem source_pair_directional_prices (U T : ℕ) (hU : 25≤U) (hUmax : U≤30)
    (hUT : U≤T) (hT : T≤331) :
    flagMixed ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩ unitZFlag ≤ 1721 ∧
    flagMixed ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩ unitYZFlag ≤ 25470 ∧
    flagMixed ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩ unitAllFlag ≤ 88560 := by
  have hsub : T-U+U=T := Nat.sub_add_cancel hUT
  have hu : U-9+9=U := Nat.sub_add_cancel (by omega)
  simp only [flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
  constructor
  · omega
  constructor <;> omega





end
end ProximityPrize.SubmissionLower.MovingSourcePrimeFamily6814


