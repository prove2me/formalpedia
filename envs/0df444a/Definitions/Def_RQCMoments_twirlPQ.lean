-- Prove2me | Definitions.Def_RQCMoments_twirlPQ
-- name    : RQCMoments_twirlPQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:23.313722+00:00
-- url     : https://prove2.me/theorems/bdd22d9b-ef8a-4205-b142-5d9ff7508a1c
-- title:
--   The $(p,q)$-twirl $\Delta^{(p,q)}_\nu$ of a distribution on $U(N)$
-- statement:
--   Let $p,q\ge 0$ be integers and let $\nu$ be a distribution on $U(N)$. Write $U^*$ for the entrywise complex conjugate and $U^\top$ for the transpose of $U$, and
--   $$
--   R_{p,q}(U)=U^{\otimes p}\otimes (U^*)^{\otimes q},
--   $$
--   an operator on $(\mathbb C^N)^{\otimes (p+q)}$. The **$(p,q)$-twirl** of $\nu$ is the linear map on operators $X$ of $(\mathbb C^N)^{\otimes(p+q)}$
--   $$
--   \Delta^{(p,q)}_\nu(X)=\mathbb E_{U\sim\nu}\Big[\big(U^{\otimes p}\otimes (U^*)^{\otimes q}\big)\,X\,\big((U^\dagger)^{\otimes p}\otimes (U^\top)^{\otimes q}\big)\Big]=\mathbb E_{U\sim\nu}\big[R_{p,q}(U)\,X\,R_{p,q}(U)^\dagger\big].
--   $$
--
--   Comparing $\Delta^{(p,q)}_\nu$ with $\Delta^{(p,q)}_{\mathrm{Haar}}$ defines strong approximate designs (Definition 2.2).
--
--   **Formalization Note** Basis states of $(\mathbb C^N)^{\otimes(p+q)}$ are pairs of index tuples $(\mathrm{Fin}\,p\to\mathrm{Fin}\,N)\times(\mathrm{Fin}\,q\to\mathrm{Fin}\,N)$. The expectation is taken entry by entry (a complex Bochner integral per matrix entry); the integrand is continuous on the compact group, hence integrable for every finite measure.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 2.2, (11); proof of Lemma 3.1, (36), p.13 and p.18 (PDF pp.15, 20)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles

set_option autoImplicit false

open MeasureTheory
open scoped Matrix

namespace RQCMoments

/-- Index set of `(ℂ^N)^{⊗p} ⊗ (ℂ^N)^{⊗q}`: a basis state of each of the `p + q` tensor factors. -/
abbrev Idx (N p q : ℕ) := (Fin p → Fin N) × (Fin q → Fin N)

/-- `R_{p,q}(U) = U^{⊗p} ⊗ (U*)^{⊗q}`, with `U*` the entrywise complex conjugate
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), (11), p.13, and (36), p.18). Its conjugate transpose is `(U†)^{⊗p} ⊗ (U^⊤)^{⊗q}`. -/
def tensorPQ {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (p q : ℕ) :
    Matrix (Idx N p q) (Idx N p q) ℂ :=
  fun a b => (∏ i, U (a.1 i) (b.1 i)) * ∏ j, star (U (a.2 j) (b.2 j))

/-- The `(p,q)`-twirl of a distribution `ν` on `U(N)`
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 2.2, (11), p.13):
`Δ^{(p,q)}_ν(X) = E_{U∼ν}[(U^{⊗p} ⊗ (U*)^{⊗q}) X ((U†)^{⊗p} ⊗ (U^⊤)^{⊗q})]`.

**Formalization Note** The expectation of the matrix-valued integrand is taken entrywise (a
Bochner integral of each complex entry), which is the matrix-valued expectation. The integrand
is continuous on the compact group `U(N)`, hence integrable for every finite measure. `U(N)` is
the subtype `Matrix.unitaryGroup (Fin N) ℂ` with the published Borel σ-algebra
(`QAlgorithms.Schur.unitaryMeasurable`). -/
noncomputable def twirlPQ {N : ℕ} (ν : Measure (Matrix.unitaryGroup (Fin N) ℂ)) (p q : ℕ)
    (X : Matrix (Idx N p q) (Idx N p q) ℂ) : Matrix (Idx N p q) (Idx N p q) ℂ :=
  fun a b => ∫ U, (tensorPQ (U : Matrix (Fin N) (Fin N) ℂ) p q * X *
    (tensorPQ (U : Matrix (Fin N) (Fin N) ℂ) p q)ᴴ) a b ∂ν

end RQCMoments


