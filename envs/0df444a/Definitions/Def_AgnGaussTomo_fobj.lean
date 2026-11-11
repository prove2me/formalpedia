-- Prove2me | Definitions.Def_AgnGaussTomo_fobj
-- name    : AgnGaussTomo_fobj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:56.684059+00:00
-- url     : https://prove2.me/theorems/63e9e507-19a1-4c6e-993f-2133ab5d1b3f
-- title:
--   Infidelity objective $f_\rho(\theta)=1-\langle\psi(\theta)|\rho|\psi(\theta)\rangle$
-- statement:
--   For a density operator $\rho$ and Bargmann parameters $\theta\in\mathcal P_n$,
--
--   $$
--   f_\rho(\theta)=1-\langle\psi(\theta)|\rho|\psi(\theta)\rangle
--   $$
--
--   is the infidelity of $\rho$ with the pure Gaussian state $|\psi(\theta)\rangle$. The refinement stage minimizes $f_\rho$ by gradient descent over a small ball around $\theta=0$ (the vacuum).
--
--   **Formalization Note** The quadratic form is the iterated Fock-basis series $\sum_i\sum_j\overline{\psi_i}\rho_{ij}\psi_j$ (real part).
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), §3.4, printed p. 19 (PDF p. 22)

import Mathlib
import Definitions.Def_AgnGaussTomo_psi

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **The infidelity objective `f_ρ(θ) = 1 − ⟨ψ(θ)|ρ|ψ(θ)⟩`.** Arulandu, Chen, Chen, Li, Ma, *Finding
Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), §3.4, printed
p. 19 (PDF p. 22): "the geometry of the infidelity objective f_ρ(θ) = 1 − ⟨ψ(θ)| ρ |ψ(θ)⟩ as a
function of the Bargmann parameters expressed as reals: θ = (b, A) ∈ P".

**Formalization Note.** `ψ(θ)` is `psi θ`; the quadratic form is the iterated Fock-basis series
`Σᵢ Σⱼ conj(ψᵢ) ρᵢⱼ ψⱼ` (real part). The argument `σ` is a coefficient array; in every statement it
is a density operator. -/
noncomputable def fobj {n : ℕ} (σ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (θ : Pspace n) : ℝ :=
  1 - (∑' i, ∑' j, star (psi θ i) * σ i j * psi θ j).re

end AgnGaussTomo


