-- Prove2me | Definitions.Def_LaughlinFock
-- name    : LaughlinFock
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:17.072408+00:00
-- url     : https://prove2.me/theorems/232da18e-a7c2-4b68-9a58-53247bf61829
-- statement:
--   This block sets up the full fermionic Fock space on the Q+1 orbitals 0,…,Q (an occupation is a subset of orbitals, and operators are complex matrices indexed by occupations) and defines a spherical V₁ Hamiltonian together with a quadratic inequality about it. The real pair coefficient of orbital indices x and y at level p vanishes unless x+y=p+1, in which case it equals (x−y)·√(Q!/(Q−x)! · Q!/(Q−y)! · p! / (Q · (2Q−2)!/(2Q−2−p)! · x! · y!))/√2 using descending factorials; the Fock version multiplies this by √2. The annihilator of orbital j sends an occupation B containing j to B with j removed, with sign (−1)^k where k is the number of occupied orbitals below j, and is zero otherwise. For each p, the pair annihilator is the sum over orbital pairs i<j of the pair coefficient times (annihilator j)(annihilator i). The Hamiltonian is the sum over p from 0 to 2Q−2 of the conjugate transpose of the pair annihilator times itself, so it is a sum of positive operators. The constant gammaStar is the rational number 4616733319001/10^14, about 0.46167. FockInequality(Q,γ) is a defined proposition, not an established theorem, asserting that H² − γH is positive semidefinite on this Fock space, where H is the Hamiltonian for Q.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LaughlinFock.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LaughlinFock.lean; bytes 16..1791
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! The spherical V₁ Hamiltonian inequality on the full fermionic Fock space. -/

noncomputable section

namespace Laughlin

noncomputable def pairCoefficient (Q p : ℕ) (x y : Fin (Q+1)) : ℝ :=
  if x.val + y.val = p+1 then
    ((x.val : ℝ) - (y.val : ℝ)) *
      Real.sqrt (((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) *
        (p.factorial : ℝ)) /
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) *
          (x.val.factorial : ℝ) * (y.val.factorial : ℝ))) / Real.sqrt 2
  else 0

end Laughlin


namespace LaughlinFock

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

abbrev Orbital (Q : ℕ) := Fin (Q + 1)
abbrev Occupation (Q : ℕ) := Finset (Orbital Q)
abbrev FockMatrix (Q : ℕ) := Matrix (Occupation Q) (Occupation Q) ℂ

def tensorPairCoefficient (Q p : ℕ) (i j : Orbital Q) : ℝ :=
  _root_.OAI.Laughlin.pairCoefficient Q p i j

def pairCoefficient (Q p : ℕ) (i j : Orbital Q) : ℝ :=
  Real.sqrt 2 * tensorPairCoefficient Q p i j

def annihilator (Q : ℕ) (j : Orbital Q) : FockMatrix Q := fun A B =>
  if j ∈ B ∧ A = B.erase j then
    (-1 : ℂ) ^ (B.filter (fun i => i < j)).card
  else 0

def pairAnnihilator (Q p : ℕ) : FockMatrix Q :=
  ∑ i : Orbital Q, ∑ j : Orbital Q,
    if i < j then
      (pairCoefficient Q p i j : ℂ) • (annihilator Q j * annihilator Q i)
    else 0

def hamiltonian (Q : ℕ) : FockMatrix Q :=
  ∑ p ∈ Finset.range (2 * Q - 1),
    (pairAnnihilator Q p)ᴴ * pairAnnihilator Q p

def gammaStar : ℝ := 4616733319001 / 10 ^ 14

def FockInequality (Q : ℕ) (γ : ℝ) : Prop :=
  (hamiltonian Q * hamiltonian Q - γ • hamiltonian Q).PosSemidef



end LaughlinFock
end
end OAI


