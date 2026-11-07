-- Prove2me | Definitions.Def_PRUPermLayer_plusOp
-- name    : PRUPermLayer_plusOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:22.202226+00:00
-- url     : https://prove2.me/theorems/ba416deb-9a81-477e-a59a-c68c72acb2fb
-- title:
--   Plus operator $H_\mu = \mathbb E_{C\sim\mu} C^\dagger|+\rangle\langle+|C$
-- statement:
--   For a distribution $\mu$ on $U(2)$, the **plus operator** is
--   $$
--   H_\mu = \mathop{\mathbb E}_{C\sim\mu} C^\dagger\, |+\rangle\langle +|\, C, \qquad |+\rangle = (|0\rangle + |1\rangle)/\sqrt2 .
--   $$
--   Its expectation in a one-qubit state is the probability that the qubit is sent to $|+\rangle$ by the random gate.
--
--   **Formalization Note** $|+\rangle\langle+|$ is the matrix with all entries $1/2$; the expectation is taken entry by entry.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.6, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_PRUPermLayer_qubitUnitaryMeasurable
open MeasureTheory

namespace PRUPermLayer

/-- The plus operator `H_µ = E_{C∼µ} C† |+⟩⟨+| C` of a distribution `µ` on `U(2)`
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.6, p.11 (PDF p.13)), with `|+⟩ = (|0⟩ + |1⟩)/√2`.

**Formalization Note** `|+⟩⟨+|` is the matrix with all four entries `1/2`; the expectation is
taken entrywise. -/
noncomputable def plusOp (μ : Measure (Matrix.unitaryGroup Bool ℂ)) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => ∫ C, (star (C : Matrix Bool Bool ℂ) * Matrix.of (fun _ _ => (1 / 2 : ℂ)) *
    (C : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ) a b ∂μ

end PRUPermLayer


