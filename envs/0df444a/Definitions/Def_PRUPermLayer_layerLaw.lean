-- Prove2me | Definitions.Def_PRUPermLayer_layerLaw
-- name    : PRUPermLayer_layerLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:20.788846+00:00
-- url     : https://prove2.me/theorems/2136f4a9-ba7e-4c65-9581-8ada5088f7bc
-- title:
--   Layer law $\mu^{\otimes n}$ of $n$ independent single-qubit gates
-- statement:
--   Let $\mu$ be a distribution on $U(2)$. The **layer law** $\mu^{\otimes n}$ is the distribution of $L = C_1 \otimes \cdots \otimes C_n$ when $C_1, \dots, C_n$ are independent with $C_i \sim \mu$: the image of the product measure $\mu \times \cdots \times \mu$ on $U(2)^n$ under $(C_1,\dots,C_n) \mapsto C_1 \otimes \cdots \otimes C_n$. It is a distribution on $U(N)$, $N = 2^n$.
--
--   **Formalization Note** The product measure requires $\mu$ to be $\sigma$-finite, which every probability measure is. The tensor-product map is continuous, so the image of a probability measure is a probability measure (checked in the mission's sanity file).
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_PRUPermLayer_qubitUnitaryMeasurable
import Definitions.Def_PRUPermLayer_layerUnitary
open MeasureTheory

namespace PRUPermLayer

/-- The law `µ^{⊗n}` of the layer `L = C₁ ⊗ ⋯ ⊗ Cₙ` with independent factors `Cᵢ ∼ µ`
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11): "For a distribution µ on U(2), the layer L = C1⊗· · ·⊗Cn has
independent factors Ci ∼ µ, and we write µ⊗n for its distribution"). It is the image of the
product measure `µ × ⋯ × µ` on `U(2)ⁿ` under `(C₁, …, Cₙ) ↦ C₁ ⊗ ⋯ ⊗ Cₙ`.

**Formalization Note** `µ` is a measure on `Matrix.unitaryGroup Bool ℂ` with the Borel σ-algebra
`qubitUnitaryMeasurable`; `SigmaFinite µ` is needed to form the product and holds for every
probability measure. The map is continuous, hence measurable, so the image of a probability
measure is a probability measure (checked in `Solutions/verification/PRUPermLayer_sanity.lean`). -/
noncomputable def layerLaw (μ : Measure (Matrix.unitaryGroup Bool ℂ)) [SigmaFinite μ] (n : ℕ) :
    Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :=
  Measure.map layerUnitary (Measure.pi fun _ : Fin n => μ)

end PRUPermLayer


