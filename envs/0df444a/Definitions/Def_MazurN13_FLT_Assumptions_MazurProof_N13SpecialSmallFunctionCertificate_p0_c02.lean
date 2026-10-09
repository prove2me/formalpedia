-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c02
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c02
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-09T01:24:22.540888+00:00
-- url     : https://prove2.me/theorems/515f0f83-b469-4a37-9f13-4d0c7c27c676
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate source foundation (part 2 of 50)
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate

import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallFunctionCertificate_p0_c01
/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate
Original leading source comments and nonproject imports are retained below. -/

set_option autoImplicit false




/-!
Source pin: b07243d72093bec5686e15b1208cb50d000f3e8d.
Source-only repair of the certificate candidate from
4109ba77745784c1a9f8c4c7b304df4124bf5ac4. Lean and axiom checks NOT RUN.

Finite polynomial certificates for all 32 * 4 coefficient pairs in the
GOOD F2 model. Polynomial divisibility is never passed to a decision
procedure. The six local equations have explicit cofactors. Each of the
58 unsupported nonzero norms has an explicit factor coprime to both X
and X - 1; its two Bezout identities rule out support. The zero norm is
excluded separately. The 69 supported rows have explicit six-polynomial
normal forms and first-nonzero-coefficient certificates.

All public definition values and theorem statements are unchanged.
The link between these nine-jet orders and the six geometric local
orders is a separate theorem.
-/

namespace MazurProof.N13SpecialSmallFunctionCertificate

noncomputable section
open Polynomial

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
def weightedJetCode (a : Fin 5 → K) (b : Fin 2 → K) : ZMod 19 :=
  (sixJetOrders a b 0 : ZMod 19) - sixJetOrders a b 1 +
    7 * (sixJetOrders a b 2 : ZMod 19) - 7 * sixJetOrders a b 3 +
    8 * (sixJetOrders a b 4 : ZMod 19) - 8 * sixJetOrders a b 5


/-- A first nonzero coefficient below nine determines `jetOrder`.
This is a proved bridge from finite coefficient data to `List.findIdx`. -/
theorem jetOrder_of_coefficients (p : K[X]) (n : ℕ) (hn : n < 9)
    (hne : p.coeff n ≠ 0)
    (hzero : ∀ j : Fin 9, (j : ℕ) < n → p.coeff j = 0) :
    jetOrder p = n := by
  unfold jetOrder
  apply (List.findIdx_eq (xs := List.range 9) (i := n) (by simpa using hn)).2
  constructor
  · simpa using hne
  · intro j hj
    have hz := hzero ⟨j, hj.trans hn⟩ hj
    simpa using hz

def GoodJets (p : Fin 6 → K[X]) : Prop :=
  (∀ i : Fin 6, jetOrder (p i) < 9 ∧
    (p i).coeff (jetOrder (p i)) ≠ 0 ∧
    ∀ j : Fin 9, (j : ℕ) < jetOrder (p i) → (p i).coeff j = 0) ∧
  (jetOrder (p 0) : ZMod 19) - jetOrder (p 1) +
    7 * (jetOrder (p 2) : ZMod 19) - 7 * jetOrder (p 3) +
    8 * (jetOrder (p 4) : ZMod 19) - 8 * jetOrder (p 5) = 0

theorem goodJets_of_coefficients (p : Fin 6 → K[X]) (n : Fin 6 → ℕ)
    (hlt : ∀ i, n i < 9)
    (hne : ∀ i, (p i).coeff (n i) ≠ 0)
    (hzero : ∀ i, ∀ j : Fin 9, (j : ℕ) < n i → (p i).coeff j = 0)
    (hcode : (n 0 : ZMod 19) - n 1 + 7 * (n 2 : ZMod 19) - 7 * n 3 +
      8 * (n 4 : ZMod 19) - 8 * n 5 = 0) : GoodJets p := by
  have ho (i : Fin 6) : jetOrder (p i) = n i :=
    jetOrder_of_coefficients (p i) (n i) (hlt i) (hne i) (hzero i)
  constructor
  · intro i
    rw [ho i]
    exact ⟨hlt i, hne i, hzero i⟩
  · simpa only [ho] using hcode

def PairCertificate (a : Fin 5 → K) (b : Fin 2 → K) : Prop :=
  N13SpecialAffineNorm.normPolynomial (numerator a) (ordinate b) ∣
    (X : K[X]) ^ 16 * (X - 1) ^ 16 → GoodJets (sixJetPolynomials a b)

/-- Two explicit Bezout identities exclude a monic nonconstant factor. -/
theorem obstruction (f u v : K[X]) (hm : f.Monic) (hne : f ≠ 1)
    (hx : f + u * X = 1) (hx1 : f + v * (X - 1) = 1) :
    ¬ f ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  have h0 : IsCoprime f X := ⟨1, u, by simpa only [one_mul] using hx⟩
  have h1 : IsCoprime f (X - 1) := ⟨1, v, by simpa only [one_mul] using hx1⟩
  have hc : IsCoprime f ((X : K[X]) ^ 16 * (X - 1) ^ 16) :=
    h0.pow_right.mul_right h1.pow_right
  intro hd
  exact hne (hm.eq_one_of_isUnit (hc.isUnit_of_dvd hd))

theorem obstruction_11 :
    ¬ (1 + X + X ^ 3 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (1 + X ^ 2) (X + X ^ 2)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 3) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X + X ^ 3) * two_poly
  · linear_combination (X ^ 3) * two_poly

theorem obstruction_21 :
    ¬ (1 + X ^ 2 + X ^ 4 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 3) (X ^ 2 + X ^ 3)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 4) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 4) * two_poly
  · linear_combination (X ^ 4) * two_poly

theorem obstruction_37 :
    ¬ (1 + X ^ 2 + X ^ 5 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 4) (X ^ 2 + X ^ 3 + X ^ 4)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 5) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 5) * two_poly
  · linear_combination (X ^ 5) * two_poly

theorem obstruction_59 :
    ¬ (1 + X + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (1 + X ^ 2 + X ^ 3 + X ^ 4) (X + X ^ 2 + X ^ 4)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 5) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X + X ^ 3 + X ^ 4 + X ^ 5) * two_poly
  · linear_combination (X ^ 3 + X ^ 5) * two_poly

theorem obstruction_61 :
    ¬ (1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 2 + X ^ 3 + X ^ 4) (X ^ 2 + X ^ 4)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 5) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5) * two_poly
  · linear_combination (X ^ 3 + X ^ 5) * two_poly

theorem obstruction_67 :
    ¬ (1 + X + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (1 + X ^ 5) (X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X + X ^ 6) * two_poly
  · linear_combination (X ^ 6) * two_poly

theorem obstruction_69 :
    ¬ (1 + X ^ 2 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 5) (X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 6) * two_poly
  · linear_combination (X ^ 6) * two_poly

theorem obstruction_73 :
    ¬ (1 + X ^ 3 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X ^ 2 + X ^ 5) (X ^ 3 + X ^ 4 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 3 + X ^ 6) * two_poly
  · linear_combination (X ^ 6) * two_poly

end
end MazurProof.N13SpecialSmallFunctionCertificate


