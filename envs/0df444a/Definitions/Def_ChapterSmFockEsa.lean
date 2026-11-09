-- Prove2me | Definitions.Def_ChapterSmFockEsa
-- name    : ChapterSmFockEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-09T02:34:57.955302+00:00
-- url     : https://prove2.me/theorems/d3de09da-d024-43ce-aec6-c247a6df382f
-- title:
--   ChapterSmFockEsa
-- statement:
--   ChapterSmFockEsa

import Definitions.Def_ChapterSmOuterFock
import Definitions.Def_ChapterSmHamiltonian
import Mathlib


/-!
# The Standard-Model Hamiltonian of record is essentially self-adjoint on the outer Fock space

`BookProof/ChapterSmComparisonEsa.lean` proves that the bosonic Standard-Model one-particle
Hamiltonian `h` is essentially self-adjoint on the Gauss–polynomial core of `L²(ℝ¹⁶³)`
(`sm_h_esa`); `BookProof/ChapterSmOuterFock.lean` builds the Hamiltonian of record
`smFockHam = dΓ(h)` on the nested Fock space `⊕ₙ L²(ℝ^{163n})` and gives it a Friedrichs
extension.  This module closes the enclosure step for the bosonic sector, in both spellings
of the enclosure:

* `smSectorHam_eq_weylPoly`, **`smSectorHam_esa`** — every particle-number sector
  `smSectorHam P n` (one copy of `h` per excitation) is a Weyl-type operator with momenta in
  distinct coordinates and real polynomial fields, hence essentially self-adjoint on the
  Gauss–polynomial core of `L²(ℝ^{163n})` by the Kato-type theorem
  (`BookProof.YangMillsNonAbelianEsa.weylPoly_esa`);
* **`smFockHam_esa`** — the Hamiltonian of record `smFockHam P` is essentially self-adjoint on
  the finite-particle core `smFockCore` (a direct sum of essentially self-adjoint blocks);
* **`sm_dGamma_esa`** — in the creation-left / annihilation-right spelling
  `dΓ(h) = Σ_{i,j} h_{ij} C†(e_i) A(e_j)` of the general second quantization,
  `dΓ(h)` is essentially self-adjoint on the finite-particle domain over the
  Gauss–polynomial core, by the lift `EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa`
  applied to `sm_h_esa`.

## Honest boundary

The inner operator is the **bosonic** sector (gauge fields, their spatial derivatives, the
Higgs doublet), exactly as in `BookProof.ChapterSmOuterFock`.  The Dirac and Yukawa terms act
on the finite-dimensional CAR algebra (`BookProof.ChapterSmDiracYukawa`) and are not part of
the operator enclosed here.  No spectral information and no mass gap is claimed.  The
Friedrichs certificate (`sm_dGamma_friedrichs_extension`) and the essential
self-adjointness proved here are independent statements.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.SmFockEsa

open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian BookProof.SmOuterFock
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.DirectSumEsa

noncomputable section

/-! ## 1. Every particle-number sector is essentially self-adjoint -/

/-- The coordinate carrying the `m`-th momentum of the `n`-particle sector. -/
def smSecMomIdx (n : ℕ) (m : Fin (n * 40)) : Fin (n * 163) :=
  scoord ((smMomFinN n).symm m).1 (smMomCoord ((smMomFinN n).symm m).2)

/-- The `r`-th field polynomial of the `n`-particle sector. -/
def smSecFieldPoly (P : SmParams) (n : ℕ) (r : Fin (n * 49)) : MvPolynomial (Fin (n * 163)) ℂ :=
  smFormPoly P (scoord ((smFormFinN n).symm r).1) ((smFormFinN n).symm r).2







/-! ## 2. The Hamiltonian of record -/





end

end BookProof.SmFockEsa


