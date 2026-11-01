-- Prove2me | Definitions.Def_WildeQIT_Covering_matrixMeasurableSpace
-- name    : WildeQIT_Covering_matrixMeasurableSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:49.222821+00:00
-- url     : https://prove2.me/theorems/3f44358c-9b3a-4d76-b409-0e830f874afc
-- title:
--   Borel σ-algebra on complex matrices (operator-valued random variables)
-- statement:
--   An **operator-valued random variable** on a finite-dimensional Hilbert space $\mathcal H\cong\mathbb C^n$ is a measurable map into $\mathcal L(\mathcal H)$, the $n\times n$ complex matrices. The matrices carry the product of the Borel σ-algebras of their complex entries, which is the Borel σ-algebra of any norm on matrices. This σ-algebra is what makes independence and identical distribution of random operators meaningful.
--
--   **Formalization Note** A definition rather than a global instance; statements that need it declare it as a local instance.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §17.3, p. 508 (operator-valued random variables)

import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §17.3, p. 508
(operator-valued random variables).
-/

namespace WildeQIT.Covering

/-- **Measurable structure on operators** (Wilde, arXiv:1106.1445v8, §17.3, p. 508). An
operator-valued random variable is a measurable map into `L(H)`; operators on a
finite-dimensional `H` are matrices, and they carry the product of the Borel σ-algebras of their
complex entries.

**Formalization Note.** A `def`, not a global instance: statements that use it declare it as a
local instance. On `Matrix m n ℂ = m → n → ℂ` with finite `m, n` this is the Borel σ-algebra of
any norm on matrices. -/
@[instance_reducible]
noncomputable def matrixMeasurableSpace (m n : Type) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

end WildeQIT.Covering


