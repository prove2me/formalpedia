-- Prove2me | Definitions.Def_PRUPermLayer_qubitUnitaryMeasurable
-- name    : PRUPermLayer_qubitUnitaryMeasurable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:34.397314+00:00
-- url     : https://prove2.me/theorems/ffddf8e1-b28c-437e-8945-75d27c1ec7c0
-- title:
--   Borel $\sigma$-algebra on the single-qubit unitary group $U(2)$
-- statement:
--   The single-qubit unitary group $U(2)$, the set of $2\times 2$ complex matrices $C$ with $CC^\dagger = I$, carries the Borel $\sigma$-algebra of its matrix topology. A **distribution on $U(2)$** (the law $\mu$ of a random single-qubit gate) is a probability measure for this $\sigma$-algebra.
--
--   The single-qubit distributions $\mu$ of the paper (the uniform Clifford law, and arbitrary $\mu$ in Lemma 4.1 and Proposition 4.3) are measures for this $\sigma$-algebra.
--
--   **Formalization Note** One-qubit operators are matrices indexed by $\{0,1\}$ (written `Bool`, with `false` $=|0\rangle$), as in the published gate layer. The module declares the Borel instance and records that it is Borel, mirroring the published instance on $U(d)$.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)

import Mathlib
open MeasureTheory

namespace PRUPermLayer

/-- The Borel σ-algebra on the single-qubit unitary group `U(2)`, written
`Matrix.unitaryGroup Bool ℂ` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11): "For a distribution µ on U(2)").
A distribution `µ` of a single-qubit gate is a probability measure for this σ-algebra.

**Formalization Note** A one-qubit operator is a `Bool`-indexed matrix (`false` is `|0⟩`), as in
the published `QAlgorithms` gate layer. The instance mirrors the published Borel instance
`QAlgorithms.Schur.unitaryMeasurable` on `Matrix.unitaryGroup (Fin d) ℂ`; the second instance
records that it is the Borel σ-algebra. -/
noncomputable instance qubitUnitaryMeasurable : MeasurableSpace (Matrix.unitaryGroup Bool ℂ) :=
  borel _

instance qubitUnitaryBorel : BorelSpace (Matrix.unitaryGroup Bool ℂ) := ⟨rfl⟩

end PRUPermLayer


