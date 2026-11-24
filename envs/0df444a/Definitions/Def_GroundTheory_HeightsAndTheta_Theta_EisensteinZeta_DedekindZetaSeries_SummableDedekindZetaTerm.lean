-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:23.818986+00:00
-- url     : https://prove2.me/theorems/6b1c9a2a-062a-4d67-9864-b2fbca7ebe19
-- title:
--   Summable Dedekind Zeta Term
-- statement:
--   Definitions and structural lemmas for Summable Dedekind Zeta Term, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid
noncomputable section
namespace ZetaSevenHalvesBounds
variable (K : Type*) [Field K] [NumberField K]
def ratPrime (P : Ideal (𝓞 K)) : ℕ :=
  absNorm (under ℤ P)
variable {K}
theorem ratPrime_prime {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (ratPrime K P).Prime := by
  have : NeZero P := ⟨hP0⟩
  exact Nat.absNorm_under_prime P
theorem mem_primesOver_ratPrime {P : Ideal (𝓞 K)} (hP : P.IsPrime) :
    P ∈ primesOver (Ideal.span {((ratPrime K P : ℕ) : ℤ)}) (𝓞 K) :=
  ⟨hP, Int.liesOver_span_absNorm P⟩
theorem natCard_primesOver_le {p : ℕ} (hp : p.Prime) :
    Nat.card (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) ≤ Module.finrank ℚ K := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) :=
    (IsDedekindDomain.primesOver_finite _ _).to_subtype
  let : Fintype (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← RingOfIntegers.rank K,
    ← Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K),
    Fintype.card_eq_sum_ones]
  refine Finset.sum_le_sum fun q _ => ?_
  have : q.1.IsPrime := q.2.1
  exact Right.one_le_mul (Ideal.ramificationIdx_pos (R := ℤ) q.1)
    (Ideal.inertiaDeg_pos (R := ℤ) q.1)
variable (K) in

def primeLabel (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K))
    (h : P ∈ primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) : Fin (Module.finrank ℚ K) :=
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) :=
    (IsDedekindDomain.primesOver_finite _ _).to_subtype
  Fin.castLE (natCard_primesOver_le hp) (Finite.equivFin _ ⟨P, h⟩)
theorem finrank_pos' : 0 < Module.finrank ℚ K := Module.finrank_pos
open Classical in
variable (K) in

def label (P : Ideal (𝓞 K)) : Fin (Module.finrank ℚ K) :=
  if h : P.IsPrime ∧ P ≠ ⊥ then
    primeLabel K (ratPrime K P) (ratPrime_prime h.1 h.2) P (mem_primesOver_ratPrime h.1)
  else ⟨0, finrank_pos'⟩
variable (K) in

def tuple (I : Ideal (𝓞 K)) (j : Fin (Module.finrank ℚ K)) : ℕ :=
  ∏ P ∈ (normalizedFactors I).toFinset,
    if label K P = j then absNorm P ^ (normalizedFactors I).count P else 1
end ZetaSevenHalvesBounds
end
end GroundTheory.Heights₂.Theta


