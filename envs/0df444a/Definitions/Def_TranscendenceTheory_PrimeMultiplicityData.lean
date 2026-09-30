-- Prove2me | Definitions.Def_TranscendenceTheory_PrimeMultiplicityData
-- name    : TranscendenceTheory_PrimeMultiplicityData
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-20T17:05:30.63399+00:00
-- url     : https://prove2.me/theorems/a6613fc6-db68-4e99-aacf-3c0efae59145
-- title:
--   Global prime-ideal data with a component length bound
-- statement:
--   For nonnegative integers $T,e$, prime multiplicity data consist of a commutative $\mathbb Q$-algebra $R$, a prime ideal $\mathfrak p$, a $\mathbb Q$-linear derivation $D:R\to R$, an element $q\in\mathfrak p$ with $Dq\notin\mathfrak p$, and an ideal $I$ satisfying
--
--   $$
--   D^j f\in\mathfrak p\qquad(f\in I,\ 0\le j\le T).
--   $$
--
--   Let $\iota:R\to R_{\mathfrak p}$ be the canonical localization map. The data also include the finite local-length upper bound
--
--   $$
--   \operatorname{length}_{R_{\mathfrak p}}
--   \bigl(R_{\mathfrak p}/I R_{\mathfrak p}\bigr)\le e,
--   \qquad I R_{\mathfrak p}=\operatorname{ideal}(\iota(I)).
--   $$
--
--   These data specify the original ring, prime, ideal, and derivation. They do not provide a derivation on the localized ring or assume that localized elements retain the derivative containment property. Those facts are proved in the separate localization theorem.
--
--   The definition does not assert that these data exist for the mission's geometric components or that their lengths obey a uniform degree bound. Those assertions form the remaining frontier.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, Proposition 4.7, especially p. 379, and section 5, Lemma 5.1, pp. 380-382. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. Algebraic auxiliary theorem: construct the derivation on the prime localization and prove exact transfer of finite-order derivative containment. Component selection, global transversality, and the total local-length degree budget remain open.

import Definitions.Def_TranscendenceTheory_DifferentialMultiplicity
import Mathlib.RingTheory.Localization.AtPrime.Basic

noncomputable section
namespace TranscendenceTheory

/-- Global ideal data and an upper bound on its length at a chosen prime.
No derivation on the localization or localized jet condition is assumed. -/
structure PrimeMultiplicityData (T e : ℕ) where
  R : Type
  [commRing : CommRing R]
  [algebra : Algebra ℚ R]
  p : Ideal R
  [prime : p.IsPrime]
  D : Derivation ℚ R R
  q : R
  q_mem : q ∈ p
  deriv_not_mem : D q ∉ p
  I : Ideal R
  jets : ∀ f ∈ I, ∀ j ≤ T, (D^[j]) f ∈ p
  length_le : Module.length (Localization.AtPrime p)
    ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≤ (e : ℕ∞)

attribute [instance] PrimeMultiplicityData.commRing PrimeMultiplicityData.algebra
  PrimeMultiplicityData.prime

end TranscendenceTheory


