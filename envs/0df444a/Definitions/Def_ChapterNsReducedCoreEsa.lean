-- Prove2me | Definitions.Def_ChapterNsReducedCoreEsa
-- name    : ChapterNsReducedCoreEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-11T10:06:40.711874+00:00
-- url     : https://prove2.me/theorems/b0808406-f381-46bc-ab75-cf7b604e055f
-- title:
--   ChapterNsReducedCoreEsa
-- statement:
--   ChapterNsReducedCoreEsa

import Definitions.Def_ChapterNsFourierElimination
import Definitions.Def_ChapterNavierStokesFullEulerianFock
import Mathlib

/-!
# The reduced Navier–Stokes Hamiltonian is essentially self-adjoint on its finite-parcel core

`BookProof/ChapterNsFourierElimination.lean` builds the reduced (Fourier-eliminated)
Navier–Stokes Hamiltonian on the nested Fock space `⊕ₙ L²(ℝ^{6n})`,
`nsRedFullFockHam = ⊕ₙ redHam n`, where the `n`-parcel sector `redHam n` is the positive sum of
Weyl-ordered squares — the six momenta of every parcel and the seven reduced forms of every
parcel (three viscous residual parts, the three **advection** parts `(k·u) u_i`, and the
eliminated incompressibility `k·u`).  Essential self-adjointness was available there only on
the domain of its own Friedrichs realization (`nsRedFullOuterN_esa`, the `H = N` case).

The Kato-type theorem of `BookProof/ChapterDegKatoEsa.lean`, transferred to the
Gauss–polynomial core and packaged for Weyl-type operators by
`BookProof.YangMillsNonAbelianEsa.weylPoly_esa`, gives it on the finite-parcel core itself:

* `redHam_eq_weylPoly`, **`redHam_esa`** — every sector `redHam n` is essentially self-adjoint
  on the Gauss–polynomial core of `L²(ℝ^{6n})`; the case `n = 1` is the reduced one-particle
  Hamiltonian (a one-particle statement);
* **`nsRedFullFockHam_esa`** — the reduced Hamiltonian of record on the nested Fock space is
  essentially self-adjoint on the finite-parcel core `nsRedFockCore`.

## Scope

This concerns the positive auxiliary sum of squares of the reduced sector — the operator that
the Navier–Stokes route encloses — and **not** the mainstream Koopman–von Neumann generator,
which is never the enclosed operator.  The momentum-space convolution content of the Fourier
elimination is already inside the reduced forms; nothing here is a statement about the
Navier–Stokes flow, global regularity, or a spectral gap.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.NsReducedCoreEsa

open MvPolynomial BookProof.NsFullEuler

noncomputable section

/-- The coordinate carrying the `m`-th momentum of the `n`-parcel sector. -/
def redMomIdx (n : ℕ) (m : Fin (n * 6)) : Fin (n * 6) :=
  redIdx (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2





/-- The `m`-th reduced form polynomial of the `n`-parcel sector. -/
def redFieldPoly (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (m : Fin (n * 7)) :
    MvPolynomial (Fin (n * 6)) ℂ :=
  redFormPoly nu k n (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2







end

end BookProof.NsReducedCoreEsa


