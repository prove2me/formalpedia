-- Prove2me | Definitions.Def_Laughlin
-- name    : Laughlin
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:17.009986+00:00
-- url     : https://prove2.me/theorems/0755656e-b739-4ba8-9a21-5c37222a1887
-- statement:
--   A configuration of N particles with maximal single-particle angular momentum Q is a function a from Fin N to {0,...,Q}, and a state is a complex-valued function on configurations. A state ψ is Antisymmetric if swapping the entries of a at any two distinct positions i and j negates ψ. pairCoefficient(Q,p,x,y) is zero unless x+y=p+1, and then equals (x−y)·sqrt( Q!/(Q−x)! · Q!/(Q−y)! · p! / ( Q · (2Q−2)!/(2Q−2−p)! · x! · y! ) )/√2. pairAmplitude(ψ,i,j,p,a) sums this coefficient against ψ over all values x,y placed at positions i and j (other entries of a kept fixed). The energy of ψ sums, over pairs i<j, over p from 0 to 2Q−2, and over configurations a with a_i=a_j=0, the squared modulus of pairAmplitude. With spinor variables (i,false) and (i,true) for each particle i, bracket(i,j) is the polynomial u_i v_j − u_j v_i, and laughlinPolynomial(N) is the product over i<j of bracket(i,j)^3. monomialExponent(a) is the exponent vector giving v_i the power a_i and u_i the power Q−a_i, and laughlinVector(N,Q) at a is the coefficient of that monomial in the Laughlin polynomial divided by the product over i of sqrt(binomial(Q,a_i)). distanceToLaughlinSq(ψ) is the infimum over complex scalars c of the sum over configurations of |ψ(a)−c·laughlinVector(a)|², the squared distance from ψ to the line spanned by the Laughlin vector. MainTarget is a defined proposition, not an established theorem: there exists N₀≥2 such that for all N≥N₀, every antisymmetric state ψ on N particles with Q=3(N−1) satisfies (1/100)·distanceToLaughlinSq(ψ) ≤ energy(ψ).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Laughlin.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Laughlin.lean; bytes 16..2444
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

def MainTarget : Prop :=
  ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ ψ : State N (3*(N-1)), Antisymmetric ψ →
      (1/100 : ℝ) * distanceToLaughlinSq ψ ≤ energy ψ



end Laughlin
end OAI


