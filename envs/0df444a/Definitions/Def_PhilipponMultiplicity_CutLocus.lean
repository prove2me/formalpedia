-- Prove2me | Definitions.Def_PhilipponMultiplicity_CutLocus
-- name    : PhilipponMultiplicity_CutLocus
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-27T11:35:26.737647+00:00
-- url     : https://prove2.me/theorems/0442d76d-ee15-43fb-8193-3f9d2a29849c
-- title:
--   Proposition 3.3: shrinking open loci and discarded relevant components
-- statement:
--   For an ideal $A$, its away locus consists of the maximal ideals not containing $A$. Given intermediate and final ideals $J,I$ and the original open locus $U$, the cut locus is $U$ with the irrelevant support and the retained isolated support of $J$ removed. The discarded relevant part is the intersection of the actual canonical primary components of $J$ whose primes are relevant and are not associated to $I$. These are only set and ideal constructions; no regularity, local equality or degree inequality is assumed.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, proof of Proposition 3.3, printed pp. 366–369: https://www.numdam.org/articles/10.24033/bsmf.2060/ .

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport

/-! The actual shrinking open sets used in the proof of Proposition 3.3,
printed pp. 366–369. These definitions contain no regularity or degree claims. -/

set_option autoImplicit false
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport
variable {K : Type*} [Field K]

/-- The maximal ideals outside the closed support of an ideal. -/
def awayLocus (M : MultiProjectiveSpace K) (A : Ideal M.CoordinateRing) :
    MaximalOpenLocus M :=
  ⟨{m | ¬ A ≤ m.asIdeal},
    (PrimeSpectrum.isClosed_zeroLocus (A : Set M.CoordinateRing)).isOpen_compl.preimage
      MaximalSpectrum.toPrimeSpectrum_continuous⟩

/-- The source's current open set: restrict the original locus to relevant
points and remove the retained isolated components. -/
def cutLocus (M : MultiProjectiveSpace K) (J I : Ideal M.CoordinateRing)
    (U : MaximalOpenLocus M) : MaximalOpenLocus M :=
  U ⊓ awayLocus M (Hilbert.irrelevantIdeal K M.factorCount M.ambientDimension) ⊓
    awayLocus M (retainedPart M J I)

/-- The intersection of the discarded relevant isolated primary components;
the empty intersection is the unit ideal. -/
def discardedRelevantPart (M : MultiProjectiveSpace K) (J I : Ideal M.CoordinateRing) :
    Ideal M.CoordinateRing :=
  ⨅ q : {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J //
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
      q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)},
    Hilbert.primaryComponent K M.factorCount M.ambientDimension J q.1.1

end PhilipponMultiplicity.SectionThreeSupport


