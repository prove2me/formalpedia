-- Prove2me | Definitions.Def_eventualTransverseJetSurjective
-- name    : eventualTransverseJetSurjective
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-23T17:19:40.823115+00:00
-- url     : https://prove2.me/theorems/81ed12fe-cd5c-450d-bab2-f48f05beb0c8
-- title:
--   Eventual transverse polynomial jet surjectivity
-- statement:
--   For all sufficiently large cutoffs divisible by some fixed positive integer, every assignment of coefficients to the transverse weighted jets below the strict cutoff at each center is realized by one polynomial whose support has source weighted degree at most the cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_DeterminantSetup

noncomputable def OAI.PiExponent.eventualTransverseJetSurjective
    (m K : ℕ) (alpha : ℝ) (w : Fin m → ℕ)
    (c : Fin K → Fin m → ℂ) : Prop :=
  ∃ D : ℕ, 0 < D ∧ ∃ H0 : ℕ,
    ∀ H : ℕ, H0 ≤ H → D ∣ H →
      ∀ J : Fin K → (Fin m →₀ ℕ) → ℂ,
        ∃ Q : MvPolynomial (Fin m) ℂ,
          (∀ e ∈ Q.support,
            (∑ i : Fin m, (w i : ℝ) * (e i : ℝ)) ≤ (H : ℝ)) ∧
          ∀ (j : Fin K) (e : Fin m →₀ ℕ),
            (∑ i : Fin m, ((w i : ℝ) / alpha) * (e i : ℝ)) < (H : ℝ) →
              MvPolynomial.coeff e
                (MvPolynomial.aeval
                  (fun i => MvPolynomial.C (c j i) + MvPolynomial.X i) Q) = J j e


