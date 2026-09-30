-- Prove2me | Definitions.Def_TranscendenceTheory_MinimalPrimeMultiplicityData
-- name    : TranscendenceTheory_MinimalPrimeMultiplicityData
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-20T18:44:15.045494+00:00
-- url     : https://prove2.me/theorems/51f0e583-fcee-489e-8bb0-1ffc80a59ee8
-- title:
--   Noetherian minimal-prime data with differential contact and a local length bound
-- statement:
--   For nonnegative integers $T,e$, minimal-prime multiplicity data consist of a commutative Noetherian $\mathbb Q$-algebra $R$, an ideal $I$, a minimal prime $\mathfrak p$ over $I$, a $\mathbb Q$-linear derivation $D$, and an element $q$ satisfying
--
--   $$
--   q\in\mathfrak p,\qquad Dq\notin\mathfrak p.
--   $$
--
--   The data also require
--
--   $$
--   D^k f\in\mathfrak p\quad(f\in I,\ 0\le k\le T),
--   \qquad
--   \operatorname{length}_{R_{\mathfrak p}}
--   \bigl(R_{\mathfrak p}/IR_{\mathfrak p}\bigr)\le e.
--   $$
--
--   No primary component, ideal decomposition, or separator is supplied. These are constructed by the separate canonical-component theorem. That theorem also proves that the local length is finite, but the particular upper bound $e$ and the later total degree bound remain part of the geometric data to be established.
--
--   These are sufficient data for the isolated-component frontier. Noetherianity and minimality of the chosen prime are explicit additional hypotheses appropriate to the intended coordinate-ring construction; this definition is not claimed to be equivalent to arbitrary witnesses in the previous interface.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, Proposition 4.7, especially p. 379, and section 5, Lemma 5.1, pp. 380-382. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Stacks Project, Lemmas 10.62.3 and 10.62.5, https://stacks.math.columbia.edu/tag/00KY. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. Algebraic auxiliary theorem: construct the canonical primary component at a minimal prime in a Noetherian ring and prove finite local length and preservation of finite-order derivative containment. Geometric prime selection, transversality, and the total local-length degree budget remain open.

import Definitions.Def_TranscendenceTheory_PrimeMultiplicityData
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Noetherian.Defs

noncomputable section
namespace TranscendenceTheory

/-- Original ideal data at a minimal prime in a Noetherian ring.
No primary component, component family, or separator is supplied. -/
structure MinimalPrimeMultiplicityData (T e : ℕ) where
  R : Type
  [commRing : CommRing R]
  [algebra : Algebra ℚ R]
  [noetherian : IsNoetherianRing R]
  I : Ideal R
  p : Ideal R
  [prime : p.IsPrime]
  minimal : p ∈ I.minimalPrimes
  D : Derivation ℚ R R
  q : R
  q_mem : q ∈ p
  deriv_not_mem : D q ∉ p
  jets : ∀ f ∈ I, ∀ k ≤ T, (D^[k]) f ∈ p
  length_le : Module.length (Localization.AtPrime p)
    ((Localization.AtPrime p) ⧸ I.map
      (algebraMap R (Localization.AtPrime p))) ≤ (e : ℕ∞)

attribute [instance] MinimalPrimeMultiplicityData.commRing MinimalPrimeMultiplicityData.algebra
  MinimalPrimeMultiplicityData.noetherian MinimalPrimeMultiplicityData.prime

end TranscendenceTheory


