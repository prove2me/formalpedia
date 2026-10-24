-- Prove2me | Definitions.Def_eventualTransverseJetSurjectiveForSpatialVolume_360483bd
-- name    : eventualTransverseJetSurjectiveForSpatialVolume_360483bd
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-23T17:28:20.79516+00:00
-- url     : https://prove2.me/theorems/7e990cc4-9fc2-4337-a844-9aab63af47f7
-- title:
--   Eventual transverse polynomial jet surjectivity for the spatial volume bound
-- statement:
--   For all sufficiently large natural cutoffs divisible by one fixed positive integer, every assignment of coefficients to the transverse jets below the strict weighted cutoff at each center is realized by a polynomial supported within the non-strict weighted source cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_DeterminantSetup

open scoped BigOperators

noncomputable def OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_360483bd
    (m K : Nat) (alpha : Rat) (w : Fin m → Nat)
    (c : Fin K → Fin m → Complex) : Prop :=
  ∃ D : Nat, 0 < D ∧ ∃ H0 : Nat,
    ∀ H : Nat, H0 ≤ H → D ∣ H →
      ∀ J : Fin K → (Fin m →₀ Nat) → Complex,
        ∃ Q : MvPolynomial (Fin m) Complex,
          (∀ e ∈ Q.support,
            (∑ i : Fin m, (w i : Real) * (e i : Real)) ≤ (H : Real)) ∧
          ∀ (j : Fin K) (e : Fin m →₀ Nat),
            (∑ i : Fin m, ((w i : Real) / (alpha : Real)) * (e i : Real)) < (H : Real) →
              MvPolynomial.coeff e
                (MvPolynomial.aeval
                  (fun i => MvPolynomial.C (c j i) + MvPolynomial.X i) Q) = J j e


