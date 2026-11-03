-- Prove2me | Definitions.Def_HolevoEntropyGain_IsGeneratorValue
-- name    : HolevoEntropyGain_IsGeneratorValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:55.270109+00:00
-- url     : https://prove2.me/theorems/62439069-5e85-43be-9e19-a1f4117c62d3
-- title:
--   Canonical variable $R_j$ as the Stone generator of $t\mapsto W(te_j)$
-- statement:
--   For a Weyl system $W$ and a coordinate $j$, the canonical variable $R_j$ is the selfadjoint generator of the unitary group $t\mapsto W(te_j)$: $W(te_j) = \exp(itR_j)$. The relation $R_j\psi = \varphi$ means
--
--   $$
--   \frac{d}{dt}\Big|_{t=0} W(te_j)\psi = i\varphi .
--   $$
--
--   By Stone's theorem the domain $D(R_j)$ is exactly the set of $\psi$ for which this derivative exists.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, p.4 (W(z) = exp(iRz), R the row of canonical variables)

import Mathlib
import Definitions.Def_HolevoEntropyGain_WeylSystem

open QAlgorithms.RealRegisters (Hilbert)

namespace HolevoEntropyGain

/-- `Rⱼψ = φ`, for the canonical variable `Rⱼ`, the selfadjoint Stone generator of `t ↦ W(t eⱼ)`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, p.4, PDF p.4).

**Formalization Note** (R10) `W(z) = exp(iRz)` gives `d/dt W(t eⱼ)ψ = iRⱼψ` at `t = 0`, and by Stone's
theorem the domain of `Rⱼ` is exactly the set of `ψ` for which this derivative exists. -/
def IsGeneratorValue {I : Type} {s : ℕ} {Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ}
    (W : WeylSystem I Δ) (j : Fin (2 * s)) (ψ φ : Hilbert I) : Prop :=
  HasDerivAt (fun t : ℝ => W.operator (t • Pi.single j 1) ψ) (Complex.I • φ) 0

end HolevoEntropyGain


