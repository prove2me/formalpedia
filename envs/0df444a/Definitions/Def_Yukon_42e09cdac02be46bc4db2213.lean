-- Prove2me | Definitions.Def_Yukon_42e09cdac02be46bc4db2213
-- name    : Yukon_42e09cdac02be46bc4db2213
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-04T00:20:04.286866+00:00
-- url     : https://prove2.me/theorems/4952c208-f5ac-40df-8ed4-24710d4f26a3
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceGammaProjections6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceGammaProjections6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceGammaProjections6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-97ce4b79fb3e41406c72a1cc119b79e20cd8ab8ad4dbe4f16791a1eee9a7b7d9
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNzVmYzIxOGNjMzk4NDhlMGMzMzA4Mzg2MmM4MGNlZDI1M2M0YTdiZWE0Y2IzMmMyZGM2NzkwYTQwNDkwNmMzNCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtOTdjZTRiNzlmYjNlNDE0MDZjNzJhMWNjMTE5Yjc5ZTIwY2Q4YWI4YWQ0ZGJlNGYxNjc5MWExZWVlOWE3YjdkOSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzQyZTA5Y2RhYzAyYmU0NmJjNGRiMjIxMyIsInYiOjJ9]

import Definitions.Def_Yukon_cfd2e7e9b4a5d9c97487b438














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Common pole-exact affine projections for an arbitrary finite subfamily
of gamma-nonconstant old primes. Gamma alone supplies the separating
base. The Y and R projection degrees need not be below the characteristic. -/
namespace ProximityPrize.SubmissionLower.MovingSourceGammaProjections6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped Classical WithZero
open RCN002 RCN022 RCN035 RCN042 RCN044 RCN093 RCN096 RCN099 RCN116 RCN341 RCN344

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem affine_poles_everywhere
    (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (base : SeparableLiteralCoordinate P)
    (a : Ω) (ha : a≠0) (x y : CoordinateField Ω P)
    (hval : ∀ v∈literalRelevantPlaces base, v.val (x+a • y)=max (v.val x) (v.val y))
    (hout : ∀ v : Place Ω (CoordinateField Ω P), v∉literalRelevantPlaces base →
      RCN187.poleOrder v.val x=0 ∧ RCN187.poleOrder v.val y=0)
    (v : Place Ω (CoordinateField Ω P)) :
    RCN187.poleOrder v.val (x+a • y)=max (RCN187.poleOrder v.val x) (RCN187.poleOrder v.val y) := by
  by_cases hv : v∈literalRelevantPlaces base
  · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (hval v hv)
  · obtain ⟨hx,hy⟩ := hout v hv
    have hxle := valuation_le_one_of_poleOrder_eq_zero v.val _ hx
    have hyle := valuation_le_one_of_poleOrder_eq_zero v.val _ hy
    letI : v.val.IsTrivialOn Ω := v.property.2
    have hs : v.val (a • y)=v.val y := by
      rw [Algebra.smul_def,map_mul,Valuation.IsTrivialOn.eq_one a ha,one_mul]
    have hle : v.val (x+a • y)≤1 :=
      (v.val.map_add _ _).trans (by rw [hs]; exact max_le hxle hyle)
    have hzero : RCN187.poleOrder v.val (x+a • y)=0 :=
      RCN346.poleOrder_eq_zero_of_le_one Ω (CoordinateField Ω P) v _ hle
    rw [hzero,hx,hy]
    rfl

structure GammaFrame {A : Type} [Fintype A]
    (P : A → Ideal (MvPolynomial (Fin 3) Ω)) [∀ a,(P a).IsPrime]
    (surface : MvPolynomial (Fin 3) Ω) where
  lam : Ω
  mu : Ω
  lam_ne : lam≠0
  mu_ne : mu≠0
  uTranscendental : ∀ a, Transcendental Ω (affineU Ω (P a) lam)
  vTranscendental : ∀ a, Transcendental Ω (affineV Ω (P a) mu (mu*lam))
  uFinite : ∀ a,
    letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (affineU Ω (P a) lam)
      (uTranscendental a)).toRingHom.toAlgebra
    FiniteDimensional (RatFunc Ω) (CoordinateField Ω (P a))
  uSeparable : ∀ a,
    letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (affineU Ω (P a) lam)
      (uTranscendental a)).toRingHom.toAlgebra
    Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (P a))
  vFinite : ∀ a,
    letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (affineV Ω (P a) mu (mu*lam))
      (vTranscendental a)).toRingHom.toAlgebra
    FiniteDimensional (RatFunc Ω) (CoordinateField Ω (P a))
  vSeparable : ∀ a,
    letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (affineV Ω (P a) mu (mu*lam))
      (vTranscendental a)).toRingHom.toAlgebra
    Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (P a))
  uPole : ∀ a (v : Place Ω (CoordinateField Ω (P a))),
    RCN187.poleOrder v.val (affineU Ω (P a) lam)=
      max (RCN187.poleOrder v.val (coordinate Ω (P a) 0))
        (RCN187.poleOrder v.val (coordinate Ω (P a) 2))
  vPole : ∀ a (v : Place Ω (CoordinateField Ω (P a))),
    RCN187.poleOrder v.val (affineV Ω (P a) mu (mu*lam))=
      max (RCN187.poleOrder v.val (coordinate Ω (P a) 1))
        (max (RCN187.poleOrder v.val (coordinate Ω (P a) 0))
          (RCN187.poleOrder v.val (coordinate Ω (P a) 2)))
  directional : MvPolynomial.pderiv (0 : Fin 3) surface-
    MvPolynomial.C mu*MvPolynomial.pderiv (1 : Fin 3) surface≠0

/-- Construct the two common projections, not an assumption that they
exist on the subfamily. -/
theorem exists_gamma_frame
    {A : Type} [Fintype A]
    (P : A → Ideal (MvPolynomial (Fin 3) Ω)) [∀ a,(P a).IsPrime]
    (hz : ∀ a, Transcendental Ω (coordinate Ω (P a) 2))
    (hgate : ∀ a,
      (letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
        (hz a)).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc Ω) (CoordinateField Ω (P a))) ∧
      (letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
        (hz a)).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (P a))))
    (surface : MvPolynomial (Fin 3) Ω) (hderiv : MvPolynomial.pderiv (1 : Fin 3) surface≠0) :
    Nonempty (GammaFrame P surface) := by
  classical
  let base (a : A) : SeparableLiteralCoordinate (P a) := ⟨2,hz a,(hgate a).1,(hgate a).2⟩
  let E (a : A) := CoordinateField Ω (P a)
  let z (a : A) : E a := coordinate Ω (P a) 2
  let y (a : A) : E a := coordinate Ω (P a) 0
  let r (a : A) : E a := coordinate Ω (P a) 1
  let W (a : A) := literalRelevantPlaces (base a)
  let bases (a : A) := literalToSeparableCoordinate (base a)
  have hzD (a : A) : KaehlerDifferential.D Ω (E a) (z a)≠0 :=
    differential_ne_zero_of_gate _ (hz a) (hgate a)
  obtain ⟨lam,hlam0,hlam⟩ := exists_common_exact_finite_separable_affine_adaptive
    E y z W bases (fun a => Or.inr (hzD a))
  let U (a : A) : E a := y a+lam • z a
  have huPole (a : A) (v : Place Ω (E a)) :
      RCN187.poleOrder v.val (U a)=max (RCN187.poleOrder v.val (y a)) (RCN187.poleOrder v.val (z a)) := by
    exact affine_poles_everywhere (P a) (base a) lam hlam0 (y a) (z a)
      (hlam a).choose_spec.2.2
      (fun v hv => ⟨coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant (base a) v hv 0,
        coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant (base a) v hv 2⟩) v
  have huD (a : A) : KaehlerDifferential.D Ω (E a) (U a)≠0 :=
    differential_ne_zero_of_gate _ (hlam a).choose
      ⟨(hlam a).choose_spec.1,(hlam a).choose_spec.2.1⟩
  let Extra (mu : Ω) := MvPolynomial.pderiv (0 : Fin 3) surface-
    MvPolynomial.C mu*MvPolynomial.pderiv (1 : Fin 3) surface=0
  have hextra : ∀ {a b}, Extra a → Extra b → a=b :=
    directional_bad_coefficient_subsingleton surface hderiv
  obtain ⟨mu,hmu0,hdir,hmu⟩ := exists_common_exact_finite_separable_affine_adaptive_avoiding_one
    E r U W Extra hextra bases (fun a => Or.inr (huD a))
  let V (a : A) : E a := r a+mu • U a
  have hvPole (a : A) (v : Place Ω (E a)) :
      RCN187.poleOrder v.val (V a)=max (RCN187.poleOrder v.val (r a)) (RCN187.poleOrder v.val (U a)) := by
    apply affine_poles_everywhere (P a) (base a) mu hmu0 (r a) (U a) (hmu a).choose_spec.2.2 ?_ v
    intro v hv
    refine ⟨coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant (base a) v hv 1,?_⟩
    rw [huPole a v]
    rw [coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant (base a) v hv 0,
      coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant (base a) v hv 2]
    rfl
  have hvEq (a : A) : affineV Ω (P a) mu (mu*lam)=V a := by
    simp only [V,U,r,y,z,affineV,smul_add,smul_smul,add_assoc]
  have hvt (a : A) : Transcendental Ω (affineV Ω (P a) mu (mu*lam)) :=
    hvEq a ▸ (hmu a).choose
  have hev (a : A) :
      elementEmbedding Ω (E a) (affineV Ω (P a) mu (mu*lam)) (hvt a)=
        elementEmbedding Ω (E a) (V a) (hmu a).choose :=
    elementEmbedding_congr (hvt a) (hmu a).choose (hvEq a)
  refine ⟨{
    lam := lam, mu := mu, lam_ne := hlam0, mu_ne := hmu0
    uTranscendental := fun a => (hlam a).choose
    vTranscendental := hvt
    uFinite := fun a => (hlam a).choose_spec.1
    uSeparable := fun a => (hlam a).choose_spec.2.1
    vFinite := ?_, vSeparable := ?_, uPole := huPole
    vPole := ?_, directional := hdir }⟩
  · intro a
    rw [hev a]
    exact (hmu a).choose_spec.1
  · intro a
    rw [hev a]
    exact (hmu a).choose_spec.2.1
  · intro a v
    rw [hvEq a,hvPole a v,huPole a v]



end
end ProximityPrize.SubmissionLower.MovingSourceGammaProjections6814


