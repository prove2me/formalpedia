-- Prove2me | Definitions.Def_FowlerLSQC_Canonical_IsCanonicalDecomposition
-- name    : FowlerLSQC_Canonical_IsCanonicalDecomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:15.185254+00:00
-- url     : https://prove2.me/theorems/ba5f5f62-fc89-4998-94a3-6446dcf74d1a
-- title:
--   Canonical decomposition $G\cong(G_{2A}\otimes G_{2B})G_{\vec\theta}(G_{1A}\otimes G_{1B})$
-- statement:
--   Let $G$ be a $4\times4$ complex matrix (a two-qubit gate), let $G_{1A},G_{1B},G_{2A},G_{2B}\in U(2)$ be single-qubit gates and $\vec\theta\in\mathbb R^3$. These data form a **canonical decomposition** of $G$ when
--   $$
--   G\cong(G_{2A}\otimes G_{2B})\,G_{\vec\theta}\,(G_{1A}\otimes G_{1B}),
--   $$
--   where $\cong$ denotes equality up to a global phase: there is a real $\varphi$ with $G=e^{i\varphi}(G_{2A}\otimes G_{2B})G_{\vec\theta}(G_{1A}\otimes G_{1B})$.
--
--   The gates $G_{1A}\otimes G_{1B}$ act first; qubit A is the first tensor factor. The single-qubit gates are arbitrary unitaries, not required to have determinant one.
--
--   **Formalization Note** The single-qubit gates are elements of `Matrix.unitaryGroup Bool ℂ`, and the argument order is `G G1A G1B G2A G2B θ`.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §4.2, (4.4), pp.48–49 (PDF pp.66–67); §4.4, p.53 (PDF p.71)

import Mathlib
import Definitions.Def_FowlerLSQC_Canonical_nonlocalGate

open scoped Kronecker

namespace FowlerLSQC.Canonical

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §4.2, (4.4),
pp.48–49 (PDF pp.66–67): `G1A, G1B, G2A, G2B` and the non-local parameters `θ` form a canonical
decomposition of the two-qubit gate `G`, i.e.
`G ≅ (G2A ⊗ G2B) G_θ (G1A ⊗ G1B)`, where `≅` is equality up to global phase.

**Formalization Note.** Equality up to global phase is `∃ φ : ℝ, G = e^{iφ} • …`. The four
single-qubit gates are arbitrary elements of `U(2)` (`Matrix.unitaryGroup Bool ℂ`), as on p.53
("We have not restricted the single-qubit unitaries to be special"). In `⊗` qubit A is the first
Kronecker factor; `G1A ⊗ G1B` acts first. Argument order: `G1A G1B G2A G2B θ`. -/
def IsCanonicalDecomposition (G : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (G1A G1B G2A G2B : Matrix.unitaryGroup Bool ℂ) (θ : Fin 3 → ℝ) : Prop :=
  ∃ φ : ℝ, G = Complex.exp ((φ : ℂ) * Complex.I) •
    (((G2A : Matrix Bool Bool ℂ) ⊗ₖ (G2B : Matrix Bool Bool ℂ)) * nonlocalGate θ *
      ((G1A : Matrix Bool Bool ℂ) ⊗ₖ (G1B : Matrix Bool Bool ℂ)))

end FowlerLSQC.Canonical


