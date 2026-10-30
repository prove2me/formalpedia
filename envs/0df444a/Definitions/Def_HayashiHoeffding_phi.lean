-- Prove2me | Definitions.Def_HayashiHoeffding_phi
-- name    : HayashiHoeffding_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:25.275357+00:00
-- url     : https://prove2.me/theorems/899fe68b-7c6a-4a77-80cd-8f2d6f2ed6c0
-- title:
--   $\phi(s|\rho\|\sigma) = \log \operatorname{Tr} \rho^{1-s}\sigma^s$
-- statement:
--   For density operators $\rho$, $\sigma$ on a complex Hilbert space and a real $s$,
--
--   $$\phi(s|\rho\|\sigma) := \log \operatorname{Tr} \rho^{1-s} \sigma^s ,$$
--
--   with values in $[-\infty, \infty)$: $\phi(s) = -\infty$ when $\operatorname{Tr} \rho^{1-s}\sigma^s = 0$ (for instance when $\rho$ and $\sigma$ have orthogonal supports). For $0 \le s \le 1$ the operator $\rho^{1-s}\sigma^s$ is trace class and its trace lies in $[0,1]$.
--
--   $\phi$ is the logarithm of the Petz quasi-entropy; it governs the exponents of Theorem 1.
--
--   **Formalization Note**
--   1. Powers are the published `qPow`: $A^s$ by continuous functional calculus for $s \ne 0$, and the support projection $\Pi_A$ at $s = 0$ (the limit of $A^s$ as $s \to 0^+$). So $\phi(0) = \log \operatorname{Tr} \rho \Pi_\sigma$ and $\phi(1) = \log \operatorname{Tr} \Pi_\rho \sigma$.
--   2. The trace is `basisOperatorTrace`; its real part is taken.
--   3. The logarithm is `elog`.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, "Formulation and main results", p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_QChernoff_Trace_Power
import Definitions.Def_HayashiHoeffding_elog

open QAlgorithms.Papers.Independent.Next46.P02

namespace HayashiHoeffding

universe u

/-- The function `φ(s|ρ‖σ) := log Tr ρ^{1−s} σ^s` of two density operators `ρ, σ` on a complex
Hilbert space, with values in the extended reals.

Hayashi, arXiv:quant-ph/0611013v2, "Formulation and main results", p.3:
"where φ(s|ρ‖σ) def= log Trρ^{1−s}σ^s".

**Formalization Note.**
1. Powers are `QChernoff.Trace.qPow`: `A^s` is the continuous functional calculus power for
   `s ≠ 0` and the support projection `Π_A` at `s = 0` (the paper does not define `A^0` for
   singular `A`; this is the reading under which `A^s → Π_A` as `s → 0⁺`). So `φ(0) = log Tr ρ Π_σ`.
2. The trace is `basisOperatorTrace`; for density operators and `0 ≤ s ≤ 1` the product
   `ρ^{1−s} σ^s` is trace class and its trace is real and nonnegative, so its real part is taken.
3. The logarithm is `elog`: `φ(s) = −∞` when `Tr ρ^{1−s} σ^s = 0` (e.g. orthogonal supports). -/
noncomputable def phi {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ σ : H →L[ℂ] H) (s : ℝ) : EReal :=
  elog (basisOperatorTrace (QChernoff.Trace.qPow ρ (1 - s) * QChernoff.Trace.qPow σ s)).re

end HayashiHoeffding


