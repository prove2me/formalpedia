-- Prove2me | Definitions.Def_PRUPermLayer_collisionOp
-- name    : PRUPermLayer_collisionOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:10.640846+00:00
-- url     : https://prove2.me/theorems/ae048799-c2cf-4e29-8ffa-355d953c833f
-- title:
--   Collision operator $A_\mu = \mathbb E_{C\sim\mu}(C\otimes C)^\dagger\pi_{\mathrm{eq}}(C\otimes C)$
-- statement:
--   For a distribution $\mu$ on $U(2)$, the **collision operator** is the two-qubit operator
--   $$
--   A_\mu = \mathop{\mathbb E}_{C\sim\mu} (C\otimes C)^\dagger\, \pi_{\mathrm{eq}}\, (C\otimes C).
--   $$
--   Its expectation in a two-qubit state is the probability that the two qubits give equal outcomes after the same random gate.
--
--   **Formalization Note** The expectation is taken entry by entry.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.6, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_PRUPermLayer_qubitUnitaryMeasurable
import Definitions.Def_PRUPermLayer_piEq
open MeasureTheory

namespace PRUPermLayer

/-- The collision operator `A_µ = E_{C∼µ} (C ⊗ C)† π_eq (C ⊗ C)` of a distribution `µ` on
`U(2)` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.6, p.11 (PDF p.13)).

**Formalization Note** The expectation is taken entrywise; `C ⊗ C` is
`Matrix.kroneckerMap (· * ·) C C` on `Bool × Bool`. -/
noncomputable def collisionOp (μ : Measure (Matrix.unitaryGroup Bool ℂ)) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q => ∫ C, (star (Matrix.kroneckerMap (· * ·) (C : Matrix Bool Bool ℂ)
      (C : Matrix Bool Bool ℂ)) * piEq *
    Matrix.kroneckerMap (· * ·) (C : Matrix Bool Bool ℂ) (C : Matrix Bool Bool ℂ) :
      Matrix (Bool × Bool) (Bool × Bool) ℂ) p q ∂μ

end PRUPermLayer


