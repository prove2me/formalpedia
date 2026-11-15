-- Prove2me | Definitions.Def_RPLib_S3_SBClosA
-- name    : RPLib_S3_SBClosA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:39:08.839735+00:00
-- url     : https://prove2.me/theorems/aa3ee72a-aba8-4171-b4ad-2f72a633a4e1
-- title:
--   Weight-two Ramanujan-Petersson library: S3-ZetaSB, E1 part A: a Galois closure of `F / K` with an arbitrary constant extension
-- statement:
--   S3-ZetaSB, E1 part A: a Galois closure of `F / K` with an arbitrary constant extension.
--
--   `K = RatFunc Fq`. `GalE0 Fq F` is the splitting field of the minimal polynomial of a primitive element of `F / K`;
--   `GalE Fq F n` is the splitting field over `GalE0` of `X ^ (q ^ (n+1)) - X`. Both carry the function-field instance
--   list; `GalE Fq F n` is Galois over `K` and `closureEmb Fq F n : F →ₐ[K] GalE Fq F n`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_SBGalC

/-!
# S3-ZetaSB, E1 part A: a Galois closure of `F / K` with an arbitrary constant extension

`K = RatFunc Fq`. `GalE0 Fq F` is the splitting field of the minimal polynomial of a primitive element of `F / K`;
`GalE Fq F n` is the splitting field over `GalE0` of `X ^ (q ^ (n+1)) - X`. Both carry the function-field instance
list; `GalE Fq F n` is Galois over `K` and `closureEmb Fq F n : F →ₐ[K] GalE Fq F n`.
-/

set_option autoImplicit false

open Polynomial Module IsDedekindDomain

namespace RamanujanPetersson.ZetaSB

/-- Towers compose: `A → B → C` and `A, B → C → D` give `A → B → D`. -/
theorem isScalarTower_of_towers (A B C D : Type*) [CommSemiring A] [CommSemiring B] [CommSemiring C]
    [Semiring D] [Algebra A B] [Algebra A C] [Algebra B C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A C D] [IsScalarTower B C D] [IsScalarTower A B C] : IsScalarTower A B D :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq A C D, IsScalarTower.algebraMap_eq B C D,
      IsScalarTower.algebraMap_eq A B C, RingHom.comp_assoc])

section Closure

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- A primitive-element power basis of `F / K`. -/
noncomputable abbrev primPB : PowerBasis (RatFunc Fq) F :=
  Field.powerBasisOfFiniteOfSeparable (RatFunc Fq) F

/-- The Galois closure `E0` of `F / K` (splitting field of the minimal polynomial of a primitive element). -/
abbrev GalE0 : Type _ := SplittingField (minpoly (RatFunc Fq) (primPB Fq F).gen)

instance : IsScalarTower Fq Fq[X] (GalE0 Fq F) :=
  isScalarTower_of_towers Fq Fq[X] (RatFunc Fq) (GalE0 Fq F)

instance : IsGalois (RatFunc Fq) (GalE0 Fq F) :=
  IsGalois.of_separable_splitting_field (Algebra.IsSeparable.isSeparable (RatFunc Fq) (primPB Fq F).gen)

instance : FunctionField Fq (GalE0 Fq F) := inferInstanceAs (FiniteDimensional (RatFunc Fq) (GalE0 Fq F))

/-- `X ^ (q ^ (n+1)) - X` over `K`. -/
noncomputable abbrev frobPoly (n : ℕ) : (RatFunc Fq)[X] := X ^ (Fintype.card Fq ^ (n + 1)) - X

/-- The Galois closure with constants `F_{q^(n+1)}` adjoined. -/
abbrev GalE (n : ℕ) : Type _ :=
  SplittingField ((frobPoly Fq n).map (algebraMap (RatFunc Fq) (GalE0 Fq F)))

variable (n : ℕ)

instance : IsScalarTower Fq[X] (RatFunc Fq) (GalE Fq F n) :=
  isScalarTower_of_towers Fq[X] (RatFunc Fq) (GalE0 Fq F) (GalE Fq F n)

instance : IsScalarTower Fq Fq[X] (GalE Fq F n) :=
  isScalarTower_of_towers Fq Fq[X] (GalE0 Fq F) (GalE Fq F n)

instance : IsScalarTower (RatFunc Fq) (GalE0 Fq F) (GalE Fq F n) := inferInstance

instance : FunctionField Fq (GalE Fq F n) :=
  Module.Finite.trans (GalE0 Fq F) (GalE Fq F n)

theorem charP_ringChar (R : Type*) [Field R] [Algebra Fq R] : CharP R (ringChar Fq) :=
  charP_of_injective_algebraMap (algebraMap Fq R).injective (ringChar Fq)

theorem ringChar_dvd_card_pow : ringChar Fq ∣ Fintype.card Fq ^ (n + 1) :=
  Dvd.dvd.mul_left ((CharP.cast_eq_zero_iff Fq (ringChar Fq) _).mp (FiniteField.cast_card_eq_zero Fq)) _

theorem one_lt_card_pow : 1 < Fintype.card Fq ^ (n + 1) :=
  Nat.one_lt_pow (Nat.succ_ne_zero n) Fintype.one_lt_card

theorem frobPoly_separable (R : Type*) [Field R] [Algebra Fq R] [Algebra (RatFunc Fq) R] :
    ((frobPoly Fq n).map (algebraMap (RatFunc Fq) R)).Separable := by
  haveI := charP_ringChar Fq R
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
  exact galois_poly_separable (ringChar Fq) _ (ringChar_dvd_card_pow Fq n)

instance : IsGalois (GalE0 Fq F) (GalE Fq F n) :=
  IsGalois.of_separable_splitting_field (frobPoly_separable Fq n (GalE0 Fq F))

instance : Algebra.IsSeparable (RatFunc Fq) (GalE Fq F n) :=
  Algebra.IsSeparable.trans (RatFunc Fq) (GalE0 Fq F) (GalE Fq F n)

instance : IsGalois (RatFunc Fq) (GalE Fq F n) := by
  refine isGalois_iff.mpr ⟨inferInstance, ?_⟩
  have h1 : minpoly (RatFunc Fq) (primPB Fq F).gen ≠ 0 :=
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
  have h2 : frobPoly Fq n ≠ 0 := by
    have := frobPoly_separable Fq n (RatFunc Fq)
    rw [Algebra.algebraMap_self, Polynomial.map_id] at this
    exact this.ne_zero
  have := Polynomial.IsSplittingField.mul (K := GalE0 Fq F) (L := GalE Fq F n) _ _ h1 h2
  exact Normal.of_isSplittingField (minpoly (RatFunc Fq) (primPB Fq F).gen * frobPoly Fq n)

/-- A root of the minimal polynomial of the primitive element in `E0`. -/
noncomputable def rootE0 : GalE0 Fq F :=
  rootOfSplits (SplittingField.splits (minpoly (RatFunc Fq) (primPB Fq F).gen))
    (by
      rw [degree_map]
      exact (minpoly.degree_pos (Algebra.IsIntegral.isIntegral (primPB Fq F).gen)).ne')

theorem aeval_rootE0 : aeval (rootE0 Fq F) (minpoly (RatFunc Fq) (primPB Fq F).gen) = 0 := by
  rw [aeval_def, eval₂_eq_eval_map]
  exact eval_rootOfSplits _ _

/-- `F ↪ E0` over `K`. -/
noncomputable def embE0 : F →ₐ[RatFunc Fq] GalE0 Fq F :=
  (primPB Fq F).lift (rootE0 Fq F) (aeval_rootE0 Fq F)

/-- `F ↪ GalE n` over `K`. -/
noncomputable def closureEmb : F →ₐ[RatFunc Fq] GalE Fq F n :=
  (IsScalarTower.toAlgHom (RatFunc Fq) (GalE0 Fq F) (GalE Fq F n)).comp (embE0 Fq F)

example : FunctionField Fq (GalE Fq F n) := inferInstance
example : Algebra.IsSeparable (RatFunc Fq) (GalE Fq F n) := inferInstance
example : IsScalarTower Fq Fq[X] (GalE Fq F n) := inferInstance

end Closure

end RamanujanPetersson.ZetaSB


