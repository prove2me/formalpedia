-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_IsStateOneDesign
-- name    : ShallowShadows_ShadowNorm_IsStateOneDesign
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:09.874211+00:00
-- url     : https://prove2.me/theorems/96b525a2-2ce1-457c-b664-e2b25fe7d545
-- title:
--   State one-design: $\mathbb E_{\sigma\sim\mathcal E}[\sigma] = \mathbb I/2^n$
-- statement:
--   A **state one-design** on $n$ qubits is an ensemble of states $\mathcal E$, a probability measure on the density operators, whose mean is the maximally mixed state:
--
--   $$
--   \mathbb E_{\sigma\sim\mathcal E}[\sigma] = \frac{\mathbb I}{2^n}.
--   $$
--
--   **Formalization Note** Density operators are positive semidefinite matrices of trace one (`WildeQIT.IsDensityOperator`), with the Borel $\sigma$-algebra of the entrywise topology (declared in this module). The mean is stated entrywise, $\int \sigma_{ab}\,d\mathcal E(\sigma) = 2^{-n}\delta_{ab}$; entries of density operators are bounded and continuous, so this is never satisfied vacuously, and the Dirac measure at $\mathbb I/2^n$ is a one-design (checked in a verification file).
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §VIII, p. 7 (before Eq. (18))

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

open ClassicalShadow.Linear MeasureTheory

namespace ShallowShadows.ShadowNorm

/-- The Borel σ-algebra on `n`-qubit operators (the entrywise topology of complex matrices). -/
noncomputable instance opMeasurableSpace (n : ℕ) : MeasurableSpace (Op n) := borel (Op n)

/-- The σ-algebra `opMeasurableSpace` is the Borel σ-algebra. -/
instance opBorelSpace (n : ℕ) : BorelSpace (Op n) := ⟨rfl⟩

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §VIII, p. 7 (before
Eq. (18)): a state one-design, "any ensemble of states `ℰ` such that `E_{σ∼ℰ}[σ] = 𝕀/2ⁿ`".

**Formalization Note.** An ensemble of states is a Borel probability measure on the set of
density operators (positive semidefinite, trace one; `WildeQIT.IsDensityOperator`), which covers
every finite ensemble. The mean condition is stated entrywise, `∫ σ_{ab} dℰ(σ) = 2^{-n} δ_{ab}`,
which is the matrix identity `E[σ] = 𝕀/2ⁿ` (matrices carry no global norm in Mathlib, so the
Bochner integral is taken coordinatewise). Every entry of a density operator has modulus at most
`1` and is a continuous function of `σ`, so each entry is integrable under any probability measure
and the condition is never satisfied vacuously; the Dirac measure at `𝕀/2ⁿ` satisfies it. The
module also declares the Borel `MeasurableSpace` instance on `Op n` used by this definition. -/
def IsStateOneDesign {n : ℕ} (𝓔 : Measure {σ : Op n // WildeQIT.IsDensityOperator σ}) : Prop :=
  IsProbabilityMeasure 𝓔 ∧
    ∀ a b : Bits n, ∫ σ, (σ.1 a b) ∂𝓔 = ((2 : ℂ) ^ n)⁻¹ * (1 : Op n) a b

end ShallowShadows.ShadowNorm


