-- Prove2me | Definitions.Def_HolevoEntropyGain_tracePairing
-- name    : HolevoEntropyGain_tracePairing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:24.129352+00:00
-- url     : https://prove2.me/theorems/ed96bb79-fcb0-4940-8cf1-28accce224c6
-- title:
--   Trace pairing $\operatorname{Tr} XA$ of a trace-class and a bounded operator
-- statement:
--   For a trace-class operator $X$ on $\ell^2(I)$, given by its matrix $(X_{ij})$ in the canonical basis $(e_i)$, and a bounded operator $A$,
--
--   $$
--   \operatorname{Tr} XA = \sum_i \sum_j X_{ij}\,\langle e_j, A e_i\rangle .
--   $$
--
--   Both series converge absolutely when $X$ is trace class and $I$ is countable. This is the pairing in which the paper writes characteristic functions $\operatorname{Tr}\rho W(z)$ and the extended expectations $\operatorname{Tr}\rho F$.
--
--   **Formalization Note** The definition is total; it is applied only to trace-class $X$.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2–3, pp.2, 4 (Tr ρF, Tr ρW(z))

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

namespace HolevoEntropyGain

/-- The trace `Tr X A` of a trace-class coefficient array `X` against a bounded operator `A`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2–3, pp.2, 4, PDF pp.2, 4).

**Formalization Note** `operatorCoeff A j i = ⟨e_j, A e_i⟩`, so the inner sum is `⟨e_i, XA e_i⟩`. For
`X` trace class and `I` countable both series converge absolutely, so no default value of `tsum`
intervenes. The pairing is only applied to trace-class `X`. -/
noncomputable def tracePairing {I : Type} (X : Matrix I I ℂ) (A : Hilbert I →L[ℂ] Hilbert I) : ℂ :=
  ∑' i, ∑' j, X i j * operatorCoeff A j i

end HolevoEntropyGain


