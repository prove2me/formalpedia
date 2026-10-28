-- Prove2me | Definitions.Def_ChapterSmOuterFock
-- name    : ChapterSmOuterFock
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T13:08:44.653137+00:00
-- url     : https://prove2.me/theorems/1f1a328f-9d45-49e8-a812-d6ef889c74f4
-- title:
--   Chapter SmOuterFock
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmOuterFock.lean`): generated def bundle for ChapterSmOuterFock. See BookProof/ChapterSmOuterFock.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmOuterFock.lean

import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterYangMillsFockFriedrichs
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Mathlib


/-!
# The Standard Model Hamiltonian of record: the outer second quantization `dΓ(h)`

Step 4 of the Standard-Model work order of `CONSOLIDATED_PLAN.md` (§D6b-SM.4), in the
enclosure spelling of the Hamiltonian doctrine (§B of the 2026-09-22c state section): the
**final Hamiltonian of record is the outer second quantization of the one-particle
operator**, never the bare one-particle operator.  For the Standard Model that is

```
H = dΓ(h) :  ⊕ₙ L²(ℝ^{163 n}) → ⊕ₙ L²(ℝ^{163 n}),
```

one copy of the bosonic one-particle operator `h` of `BookProof.ChapterSmHamiltonian` per
excitation, in every particle-number sector.  A statement about the bare `h` is a
*one-particle* statement and is labelled as such there.

The route is the one the doctrine prescribes for an inner operator that is **bounded
below**: the Standard-Model `h` is a positive sum of squares — the three magnetic energies
(non-abelian included), the covariant Higgs kinetic energy and the Higgs wall — so the
Friedrichs extension applies directly, exactly as for Yang–Mills
(`BookProof.YmFockFriedrichs`), and no Faris–Lavine commutator certificate is needed.  Both
ingredients — symmetry and positivity of the quadratic form — are fibrewise, so they lift
from `L²(ℝ¹⁶³)` to the nested Fock space.

## What is proved

* `smSectorHam` — the `n`-particle Standard-Model Hamiltonian on the Gauss–polynomial core
  of `L²(ℝ^{163n})`: the `40n` momenta and the `49n` squared forms, one copy per
  excitation; `smSectorHam_symmetricOn`, `smSectorHam_quadForm_nonneg`,
  `smSector_friedrichs_extension`;
* `smFockSpace`, `smFockCore`, `smFockCore_dense`, **`smFockHam`** — the Hamiltonian of
  record on the nested Fock space and its finite-particle core;
* `smFockHam_symmetricOn`, `smFockHam_quadForm_nonneg`,
  **`sm_dGamma_friedrichs_extension`** — the enclosed Hamiltonian is symmetric, bounded
  below, and has a positive self-adjoint (Friedrichs) extension;
* `sm_dGamma_stone_flow` — the unitary time evolution it generates;
* `smFockHam_sector`, `smFockHam_number_conserving` — the enclosure is block diagonal in
  the particle number, and its restriction to the `n`-particle sector is the `n`-particle
  Hamiltonian.

## Honest boundary

As in `BookProof.ChapterSmHamiltonian`: the inner operator is the **bosonic** sector
(gauge fields, their spatial derivatives, the Higgs doublet).  The Dirac and Yukawa terms
require the CAR/Grassmann algebra and are not enclosed here; the CKM/PMNS unitarity algebra
they rest on is `BookProof.ChapterSmOneParticle`.  No spectral information, no electroweak
symmetry breaking as dynamics, and no mass gap is claimed.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmOuterFock

open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge
open BookProof.ChapterStoneResolvent

noncomputable section

/-! ## 1. The coordinates of the `n`-particle sector -/

/-- The global coordinate of the `i`-th field-space direction of the `p`-th excitation. -/
def scoord {n : ℕ} (p : Fin n) (i : Fin 163) : Fin (n * 163) := finProdFinEquiv (p, i)

/-- The `40n` momentum labels of the `n`-particle sector. -/
def smMomFinN (n : ℕ) : (Fin n × SmMom) ≃ Fin (n * 40) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) smMomFin).trans finProdFinEquiv

/-- The `49n` form labels of the `n`-particle sector. -/
def smFormFinN (n : ℕ) : (Fin n × SmForm) ≃ Fin (n * 49) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) smFormFin).trans finProdFinEquiv

/-! ## 2. The `n`-particle Hamiltonian -/

/-- The momentum operators of the `n`-particle sector: the `40` momenta of each of the `n`
excitations. -/
def smSecPi (n : ℕ) (m : Fin (n * 40)) :
    (polyGaussCore (d := n * 163)) →ₗ[ℂ] (polyGaussCore (d := n * 163)) :=
  (coreRepPoly (n * 163)).op
    (momOp (scoord ((smMomFinN n).symm m).1 (smMomCoord ((smMomFinN n).symm m).2)))

/-- The field operators of the `n`-particle sector: multiplication by the `49` real field
polynomials of each of the `n` excitations. -/
def smSecField (P : SmParams) (n : ℕ) (r : Fin (n * 49)) :
    (polyGaussCore (d := n * 163)) →ₗ[ℂ] (polyGaussCore (d := n * 163)) :=
  (coreRepPoly (n * 163)).op
    (mulOp (smFormPoly P (scoord ((smFormFinN n).symm r).1) ((smFormFinN n).symm r).2))





/-- **The `n`-particle Standard-Model Hamiltonian** on the Gauss–polynomial core of
`L²(ℝ^{163n})`: the kinetic term of every excitation, the full magnetic energy of every
excitation (quartic in the non-abelian case), the covariant Higgs kinetic energy and the
Higgs wall of every excitation. -/
def smSectorHam (P : SmParams) (n : ℕ) :
    (polyGaussCore (d := n * 163)) →ₗ[ℂ] L2d (n * 163) :=
  weylOp (smSecPi n) (smSecField P n)







/-! ## 3. The nested Fock space and the Hamiltonian of record -/

/-- The nested Fock space `⊕ₙ L²(ℝ^{163n})` of the Standard-Model excitations. -/
abbrev smFockSpace := lp (fun n : ℕ => L2d (n * 163)) 2

/-- The finite-particle core: finitely many sectors, each in its Gauss–polynomial core. -/
def smFockCore : Submodule ℂ smFockSpace := dsCore (fun n : ℕ => polyGaussCore (d := n * 163))



/-- **The Standard-Model Hamiltonian of record**: the outer second quantization `dΓ(h)` of
the one-particle operator `h`, one copy per excitation in every number sector. -/
def smFockHam (P : SmParams) : smFockCore →ₗ[ℂ] smFockSpace :=
  dsOp (fun n : ℕ => smSectorHam P n)









/-! ## 4. Particle-number conservation -/





end

end BookProof.SmOuterFock


