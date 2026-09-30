-- Prove2me | Definitions.Def_TranscendenceTheory_FiniteAlgebraMultiplicityModel
-- name    : TranscendenceTheory_FiniteAlgebraMultiplicityModel
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-21T00:36:18.446829+00:00
-- url     : https://prove2.me/theorems/183fe525-bce2-4f32-b385-d6a778528385
-- title:
--   Finite complex algebras with distinctly indexed local multiplicities
-- statement:
--   Let $I$ be an indexing set. A finite algebra multiplicity model consists of a finite-dimensional commutative complex algebra $A$ and an injective map
--
--   $$p:I\longrightarrow\operatorname{Spec}(A).$$
--
--   Its multiplicity at $i\in I$ is the module length
--
--   $$e_i=\ell_{A_{p(i)}}(A_{p(i)}).$$
--
--   Thus different indices denote different support primes. The algebra may contain nilpotents, and the lengths retain their multiplicities. No relation to a particular chart ideal, section space, or analytic vanishing condition is part of this definition; those relations must be supplied separately in an application.
--
--   **Formalization Note** Local length is defined by converting extended natural module length to a natural number. Finiteness of these lengths follows from finite dimensionality and is established explicitly by the accompanying theorem, rather than being assumed as a field of the structure. The definition also permits an empty indexing set and the zero algebra.
-- source:
--   Stacks Project, Lemma 10.53.5 (tag 00JA) and Lemma 10.53.6 (tag 00JB), https://stacks.math.columbia.edu/tag/00JA and https://stacks.math.columbia.edu/tag/00JB: Artinian decomposition into prime localizations; Lemma 10.52.3 (tag 00IV), https://stacks.math.columbia.edu/tag/00IV: additivity of module length. For a finite algebra over an algebraically closed field, the residue fields have degree one, so the local lengths sum exactly to the vector-space dimension. An injectively indexed subfamily has no greater sum. This is the finite-algebra, dimension-zero supporting case of the multiplicity relation in Philippon (1986), section 3, Lemma 3.2, p. 364, https://www.numdam.org/item/10.24033/bsmf.2060.pdf. The frontier child asks for a finite complex algebra realizing the chart multiplicity budgets at distinct primes, with its dimension bounded by the relevant section-space dimension. This is a sufficient finite-model route, not a quotation or proof of the full Lemma 3.2. Locus selection, finite-algebra realization, local-length comparisons and the uniform section-degree bound remain required. Application: Senthil Kumar K (2026), Appendix A, Theorem A.2, https://doi.org/10.1017/S001309152610145X.

import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Length
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section

namespace TranscendenceTheory

/-- A finite complex algebra with distinct support primes indexed by `ι`.
No connection to chart ideals or section degrees is built into the definition. -/
structure FiniteAlgebraMultiplicityModel (ι : Type) where
  A : Type
  [commRing : CommRing A]
  [algebra : Algebra ℂ A]
  [finite : Module.Finite ℂ A]
  point : ι → PrimeSpectrum A
  point_injective : Function.Injective point

attribute [instance] FiniteAlgebraMultiplicityModel.commRing
  FiniteAlgebraMultiplicityModel.algebra FiniteAlgebraMultiplicityModel.finite

/-- Natural local length. Finiteness is a theorem, not a field of the model. -/
def FiniteAlgebraMultiplicityModel.localLength {ι : Type}
    (M : FiniteAlgebraMultiplicityModel ι) (i : ι) : ℕ :=
  (Module.length (Localization.AtPrime (M.point i).asIdeal)
    (Localization.AtPrime (M.point i).asIdeal)).toNat

end TranscendenceTheory


