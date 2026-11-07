-- Prove2me | Definitions.Def_SpectrumLB_haarProj
-- name    : SpectrumLB_haarProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:41.353261+00:00
-- url     : https://prove2.me/theorems/e989cded-a065-4976-b264-46deb74fa85c
-- title:
--   Projection $\Pi=URU^\dagger$ (Eq. (3.1))
-- statement:
--   For a unitary $U\in U(d)$ and the reference rank-$r$ projection $R$, set
--
--   $$
--   \Pi=U R\,U^\dagger .
--   $$
--
--   When $U$ is Haar distributed, $\Pi$ is a Haar-random rank-$r$ projection on $\mathbb C^d$, the quantum analogue of the indicator of a uniformly random $r$-subset of $[d]$. Its tensor moments are computed in Proposition 3.2.
--
--   **Formalization Note** Any fixed rank-$r$ projection in place of $R$ gives the same law; the diagonal one is the paper's.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §3, Eq. (3.1), p. 13

import Mathlib
import Definitions.Def_SpectrumLB_stdProj

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **The projection `Π = U R U†`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, §3, Eq. (3.1), p. 13: "Π ≡ U R U†, … where U ∼ U(d) is a Haar-random unitary".

`haarProj r U = U · stdProj d r · U†`; a Haar-random rank-`r` projection is this map applied to a
Haar-distributed `U`.

**Formalization Note.** Any fixed rank-`r` projection in place of `R` gives the same law of `Π`; the diagonal
one is the paper's choice. -/
def haarProj {d : ℕ} (r : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) * stdProj d r * star (U : Matrix (Fin d) (Fin d) ℂ)

end SpectrumLB


