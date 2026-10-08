-- Prove2me | Definitions.Def_LaughlinGap
-- name    : LaughlinGap
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:17.142976+00:00
-- url     : https://prove2.me/theorems/121e6b7d-c70a-46c2-983a-6ba3f988a9ed
-- statement:
--   A configuration of N particles with maximal single-particle angular momentum Q (spin Q/2) is a function assigning each particle i an occupation value a(i) in {0,...,Q}, and a State is a complex-valued function on configurations. A state ψ is Antisymmetric if swapping the values at any two distinct particle positions i and j negates it: ψ(a∘swap(i,j)) = -ψ(a). The pairCoefficient(Q,p,x,y) vanishes unless x+y = p+1, in which case it equals (x-y)/√2 times the square root of [Q!/(Q-x)! · Q!/(Q-y)! · p!] divided by [Q · (2Q-2)!/(2Q-2-p)! · x! · y!]. The pairAmplitude of ψ for particles i, j, index p and background configuration a sums this coefficient times ψ over all values x, y substituted at positions i and j. The energy of ψ sums, over pairs i<j, over p from 0 to 2Q-2, and over configurations a with a(i)=a(j)=0, the squared modulus of the pair amplitude. For the Laughlin side, with spinor variables (i,false) and (i,true), bracket(i,j) is the determinant X_{i,false}X_{j,true} - X_{j,false}X_{i,true}, the Laughlin polynomial is the product of bracket(i,j)^3 over all i<j, and monomialExponent assigns exponent a(i) to the true variable and Q-a(i) to the false variable of particle i. The laughlinVector at configuration a is the coefficient of that monomial in the Laughlin polynomial divided by the product over i of √C(Q,a(i)). The distanceToLaughlinSq of ψ is the infimum over complex scalars c of the squared l2 distance ∑_a |ψ(a) - c·laughlinVector(a)|². MainTarget is a defined proposition, not an established theorem: it asserts there exists N₀ ≥ 2 such that for every N ≥ N₀ and every antisymmetric state ψ on N particles with Q = 3(N-1), (1/25) times the squared distance of ψ to the Laughlin line is at most the energy of ψ, a spectral-gap-type bound.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LaughlinGap.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LaughlinGap.lean; bytes 16..2697
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Laughlin
open scoped BigOperators

abbrev Configuration (N Q : ℕ) := Fin N → Fin (Q+1)
abbrev State (N Q : ℕ) := Configuration N Q → ℂ

 
def Antisymmetric {N Q : ℕ} (ψ : State N Q) : Prop :=
  ∀ (i j : Fin N), i ≠ j → ∀ a, ψ (a ∘ Equiv.swap i j) = -ψ a

 
noncomputable def pairCoefficient (Q p : ℕ) (x y : Fin (Q+1)) : ℝ :=
  if x.val + y.val = p+1 then
    ((x.val : ℝ) - (y.val : ℝ)) *
      Real.sqrt (((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) *
        (p.factorial : ℝ)) /
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) *
          (x.val.factorial : ℝ) * (y.val.factorial : ℝ))) / Real.sqrt 2
  else 0

 

noncomputable def pairAmplitude {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (p : ℕ) (a : Configuration N Q) : ℂ :=
  ∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
    (pairCoefficient Q p x y : ℂ) * ψ (Function.update (Function.update a i x) j y)

 

noncomputable def energy {N Q : ℕ} (ψ : State N Q) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if i < j then
    ∑ p ∈ Finset.range (2*Q-1), ∑ a : Configuration N Q,
      if a i = 0 ∧ a j = 0 then ‖pairAmplitude ψ i j p a‖ ^ 2 else 0
  else 0

abbrev SpinorVariables (N : ℕ) := Fin N × Bool

 
noncomputable def bracket {N : ℕ} (i j : Fin N) : MvPolynomial (SpinorVariables N) ℂ :=
  MvPolynomial.X (i,false) * MvPolynomial.X (j,true) -
    MvPolynomial.X (j,false) * MvPolynomial.X (i,true)

 
noncomputable def laughlinPolynomial (N : ℕ) : MvPolynomial (SpinorVariables N) ℂ :=
  ∏ i : Fin N, ∏ j : Fin N, if i < j then bracket i j ^ 3 else 1

 
noncomputable def monomialExponent {N Q : ℕ} (a : Configuration N Q) : SpinorVariables N →₀ ℕ :=
  Finsupp.onFinset Finset.univ
    (fun ib => if ib.2 then (a ib.1).val else Q - (a ib.1).val)
    (by intro; simp)

 

noncomputable def laughlinVector (N Q : ℕ) : State N Q := fun a =>
  (laughlinPolynomial N).coeff (monomialExponent a) /
    ((∏ i : Fin N, Real.sqrt (Nat.choose Q (a i).val : ℝ) : ℝ) : ℂ)

 

noncomputable def distanceToLaughlinSq {N Q : ℕ} (ψ : State N Q) : ℝ :=
  sInf (Set.range (fun c : ℂ => ∑ a : Configuration N Q,
    ‖ψ a - c * laughlinVector N Q a‖ ^ 2))
end Laughlin

namespace LaughlinGap
export _root_.OAI.Laughlin (Configuration State Antisymmetric pairCoefficient pairAmplitude energy SpinorVariables bracket laughlinPolynomial monomialExponent laughlinVector distanceToLaughlinSq)

def MainTarget : Prop :=
  ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ ψ : State N (3*(N-1)), Antisymmetric ψ →
      (1/25 : ℝ) * distanceToLaughlinSq ψ ≤ energy ψ



end LaughlinGap
end OAI


