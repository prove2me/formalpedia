-- Prove2me | Definitions.Def_OAIQWKAP001
-- name    : OAIQWKAP001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:37:31.679959+00:00
-- url     : https://prove2.me/theorems/ec6148e6-913d-4ebf-a4d3-3736c56e911d
-- title:
--   OpenAI Kaplansky direct-finiteness counterexample (characteristic two) split: parameter definitions bundle
-- statement:
--   A small definitions bundle of the split of OpenAI's proof of `OAI.KaplanskyCounterexample.finitelyPresented_counterexample`. It holds OpenAI's definitions of the numerical parameters of the prescribed construction for an input $h$, with the lemmas these definitions use in their bodies: the subfield size `Qcard h` $= 2^h$, the prime `prime h` (the least prime with the property of `prime_exists h`), `degree`, `exponent`, `blockdim` and `dimension`, the predicate `irreducibleCoeffs` on coefficient lists over `ZMod 2`, and the subfield `rootSubfield h`. They are ported to Lean 4.33.1 and Mathlib 0df444a from the modules `LexicographicOrder`, `PrescribedDirections`, `PrescribedPairing`, `PrescribedParameters`, `PrescribedSlots`, `PrescribedSubfield`, `PrimeCertificate`, `QuotientField` and `SimplexBound` of `lean/OAI/RingTheory/DirectFiniteness` (OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two*, OpenAI Math Release, September 23, 2026, result family 197, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0).
--
--   It imports only Mathlib. The bundle `OAIQWKAP002` builds the prescribed counterexample from it and from `OAIQWKAP000`.
-- source:
--   OpenAI, A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 197; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/DirectFiniteness at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_Kaplansky.PrimeCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-- A Lucas–Lehmer certificate for the Mersenne prime used in the degree bound. -/
theorem mersenne_21701_prime : (mersenne 21701).Prime := by
  apply lucas_lehmer_sufficiency
  · norm_num
  · norm_num

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

def Qcard (h : ℕ) : ℕ := 2^h

lemma prime_exists (h : ℕ) : ∃ p : ℕ, p.Prime ∧ (Qcard h)^100 ∣ p+1 := by
  have hq : (Qcard h)^100 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by decide : 2 ≠ 0))
  let : NeZero ((Qcard h)^100) := ⟨hq⟩
  obtain ⟨p,_,hp,he⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((isUnit_one : IsUnit (1 : ZMod ((Qcard h)^100))).neg) 0
  refine ⟨p,hp,?_⟩
  apply (ZMod.natCast_eq_zero_iff (p+1) ((Qcard h)^100)).mp
  simp only [Nat.cast_add,Nat.cast_one,he,neg_add_cancel]

local instance instDecidablePredNatAndPrimeDvdHPowQcardOfNatHAdd (h : ℕ) : DecidablePred (fun p : ℕ => p.Prime ∧ (Qcard h)^100 ∣ p+1) :=
  Classical.decPred _

def prime (h : ℕ) : ℕ := Nat.find (prime_exists h)
def degree (h : ℕ) : ℕ := prime h + 1
def exponent (h : ℕ) : ℕ := Nat.log (Qcard h) (degree h)
def blockdim (h : ℕ) : ℕ := exponent h + 20
def dimension (h : ℕ) : ℕ := 10*blockdim h

lemma prime_prime (h : ℕ) : (prime h).Prime := (Nat.find_spec (prime_exists h)).1
lemma prime_congruent (h : ℕ) : (Qcard h)^100 ∣ prime h+1 :=
  (Nat.find_spec (prime_exists h)).2
lemma prime_le (h p : ℕ) (hp : p.Prime) (hc : (Qcard h)^100 ∣ p+1) : prime h ≤ p :=
  Nat.find_min' _ ⟨hp,hc⟩
lemma prime_ge (h : ℕ) (hh : 2 ≤ h) : 3 ≤ prime h := by
  have hq : 4 ≤ Qcard h := by exact Nat.pow_le_pow_right (by decide : 0 < 2) hh
  have hpow : Qcard h ≤ (Qcard h)^100 := by
    simpa using pow_le_pow_right₀ (by omega : 1 ≤ Qcard h) (by decide : 1 ≤ 100)
  have hl : Qcard h ≤ prime h+1 := hpow.trans
    (Nat.le_of_dvd (by omega) (prime_congruent h))
  omega
lemma prime_odd (h : ℕ) (hh : 2 ≤ h) : Odd (prime h) :=
  (prime_prime h).odd_of_ne_two (by have := prime_ge h hh; omega)

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.LexicographicOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

/-- Lexicographic order on coefficient/coordinate vectors, increasing index first. -/
@[instance_reducible] def vectorOrder {ι : Type u_4} [LinearOrder ι] [WellFoundedLT ι]
    {α : Type u_5} [LinearOrder α] : LinearOrder (ι → α) :=
  LinearOrder.lift' (toLex : (ι → α) → Lex (ι → α)) (fun _ _ h => h)

@[instance_reducible] def subsetOrder (α : Type u_6) [Fintype α] [LinearOrder α] : LinearOrder (Finset α) :=
  @LinearOrder.lift' (Finset α) (Lex (α → Bool)) inferInstance
    (fun S => toLex (fun x => decide (x ∈ S))) (by
      intro S T h
      apply Finset.ext
      intro x
      have hx := congrFun (congrArg ofLex h) x
      simpa using congrArg (fun b => b=true) hx)

/-- Residues are ordered 0,...,p-1, independently of their field operations. -/
@[instance_reducible] def residueOrder (p : ℕ) [NeZero p] : LinearOrder (ZMod p) :=
  LinearOrder.lift' ZMod.val (ZMod.val_injective p)

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.QuotientField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Polynomial Module
namespace KaplanskyCounterexample.Prescription

local instance two_neZero : NeZero (2 : ℕ) := inferInstance

local instance polynomialResidueOrder : LinearOrder (ZMod 2) := @residueOrder 2 two_neZero
local instance polynomialVectorOrder (d : ℕ) : LinearOrder (Fin (d+1) → ZMod 2) := vectorOrder

def irreducibleCoeffs (d : ℕ) (c : Fin (d+1) → ZMod 2) : Prop :=
  (ofFn (d+1) c).Monic ∧ (ofFn (d+1) c).natDegree=d ∧ Irreducible (ofFn (d+1) c)

lemma irreducibleCoeffs_exists (d : ℕ) (hd : 0 < d) : ∃ c, irreducibleCoeffs d c := by
  let K := GaloisField 2 d
  let b := Field.powerBasisOfFiniteOfSeparable (ZMod 2) K
  have hb : b.dim=d := b.finrank.symm.trans (GaloisField.finrank 2 (Nat.ne_of_gt hd))
  have hi := b.isIntegral_gen
  have hdeg : (minpoly (ZMod 2) b.gen).natDegree=d := b.natDegree_minpoly.trans hb
  refine ⟨toFn (d+1) (minpoly (ZMod 2) b.gen),?_⟩
  unfold irreducibleCoeffs
  rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega : (minpoly (ZMod 2) b.gen).natDegree < d+1)]
  exact ⟨minpoly.monic hi,hdeg,minpoly.irreducible hi⟩

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedSubfield
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Polynomial Module
namespace KaplanskyCounterexample.Prescription
variable (K : Type) [Field K] [CharP K 2]

def rootSubfield (h : ℕ) : Subfield K :=
  RingHom.eqLocusField (iterateFrobenius K 2 h) (RingHom.id K)

@[simp] lemma mem_rootSubfield (h : ℕ) (x : K) : x ∈ rootSubfield K h ↔ x^(2^h)=x := Iff.rfl

variable [Fintype K]

lemma rootSubfield_card_le (h : ℕ) (hh : 0 < h) :
    Fintype.card (rootSubfield K h) ≤ 2^h := by
  let p : K[X] := X^(2^h)-X
  have hq : 1 < (2:ℕ)^h := one_lt_pow₀ (by decide) (Nat.ne_of_gt hh)
  have hdeg : p.natDegree=2^h := by
    change (X^(2^h)-X : K[X]).natDegree=2^h
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq)]
    simp
  have hp : p ≠ 0 := by
    intro hz
    have hz' : p.natDegree=0 := hz ▸ natDegree_zero
    omega
  let f (x : rootSubfield K h) : p.roots.toFinset :=
    ⟨x.val,by
      rw [Multiset.mem_toFinset,mem_roots hp]
      change eval x.val (X^(2^h)-X : K[X])=0
      simp only [eval_sub,eval_pow,eval_X]
      exact sub_eq_zero.mpr x.property⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (show x.val=y.val from congrArg (fun z : p.roots.toFinset => z.val) he)
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe] at hc
  exact hc.trans ((Multiset.toFinset_card_le _).trans (hdeg ▸ card_roots' p))

lemma rootSubfield_card (h : ℕ) (hh : 0 < h) [Algebra (ZMod 2) K]
    (hd : h ∣ finrank (ZMod 2) K) :
    Fintype.card (rootSubfield K h)=2^h := by
  let F := GaloisField 2 h
  let : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F=2^h := by
    rw [Fintype.card_eq_nat_card,GaloisField.card 2 h (Nat.ne_of_gt hh)]
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (K := F) (L := K)
    (by rwa [GaloisField.finrank 2 (Nat.ne_of_gt hh)])
  let g (x : F) : rootSubfield K h := ⟨f x,by
    change (f x)^(2^h)=f x
    rw [← map_pow,← hF,FiniteField.pow_card]⟩
  have hg : Function.Injective g := by
    intro x y he
    exact f.injective (congrArg Subtype.val he)
  apply le_antisymm (rootSubfield_card_le K h hh)
  exact hF ▸ Fintype.card_le_of_injective g hg

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.SimplexBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.PolynomialPairing
variable {Q : Type u_1} [Field Q] [Fintype Q] {q n d t : ℕ}

lemma small_cube_cutoff (hn : 0 < n) (hq : 2*n ≤ q) :
    n * (q/(2*n)-1) ≤ (q-2)/2 ∧ q ≤ 4*n*(q/(2*n)) := by
  have hd : 0 < 2*n := by omega
  have ht : 0 < q/(2*n) := Nat.div_pos hq hd
  have hm := Nat.div_mul_le_self q (2*n)
  have hr := Nat.mod_lt q hd
  have he := Nat.mod_add_div q (2*n)
  have hs := Nat.sub_add_cancel (show 1 ≤ q/(2*n) by omega)
  constructor
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    have hq2 : 2 ≤ q := by omega
    have hsub := Nat.sub_add_cancel hq2
    nlinarith
  · nlinarith

end KaplanskyCounterexample.PolynomialPairing
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance directionModulusNeZero : NeZero ℓ := inferInstance

local instance directionResidueOrder : LinearOrder (ZMod ℓ) := residueOrder ℓ

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
variable (ℓ : ℕ) [Fact ℓ.Prime]
variable {V m : Type} [Fintype V] [Fintype m] [LinearOrder V] [LinearOrder m]

local instance slotModulusNeZero : NeZero ℓ := inferInstance

local instance slotIndexWellFounded : WellFoundedLT (Fin 2) := inferInstance

@[instance_reducible] def slotPairOrder : LinearOrder (m × (Fin 2 → ZMod ℓ)) :=
  letI : LinearOrder (ZMod ℓ) := residueOrder ℓ
  letI : LinearOrder (Fin 2 → ZMod ℓ) := vectorOrder
  LinearOrder.lift' (toLex : (m × (Fin 2 → ZMod ℓ)) → Lex (m × (Fin 2 → ZMod ℓ)))
    (fun _ _ he => he)

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample
open PolynomialPairing

/-- The numerical interval for the holes gives exactly the strict rectangular
inequality and the ell-squared packing bound, without rounding assumptions. -/
lemma hole_size_inequalities {N m ℓ : ℕ} (hN : 0 < N) (hmN : m ≤ N)
    (hℓ : 3 ≤ ℓ) (hlo : 2 * N ≤ m * (ℓ+1)^2)
    (hhi : m * (ℓ+1)^2 ≤ 7 * N) :
    0 < m ∧ m < N-m ∧ N-m ≤ m * ℓ^2 := by
  have hm : 0 < m := by
    by_contra hh
    have he : m = 0 := by omega
    rw [he,zero_mul] at hlo
    omega
  have hsq : 16 ≤ (ℓ+1)^2 := by nlinarith
  have hmb : 16*m ≤ 7*N := (by nlinarith : 16*m ≤ m*(ℓ+1)^2).trans hhi
  have hsmall : 2*m < N := by nlinarith
  have hs : (ℓ+1)^2 ≤ 2*(ℓ^2+1) := by nlinarith [sq_nonneg (ℓ-1 : ℤ)]
  have hn : N ≤ m*ℓ^2 + m := by nlinarith
  exact ⟨hm,by omega,by omega⟩

end KaplanskyCounterexample
end

end OAI
end


