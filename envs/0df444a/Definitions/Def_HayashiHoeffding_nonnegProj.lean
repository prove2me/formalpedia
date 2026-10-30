-- Prove2me | Definitions.Def_HayashiHoeffding_nonnegProj
-- name    : HayashiHoeffding_nonnegProj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:30.69936+00:00
-- url     : https://prove2.me/theorems/1b248050-86f4-479b-aaa6-98c88687c770
-- title:
--   Spectral projection $\{C \ge 0\}$
-- statement:
--   For a self-adjoint bounded operator $C$ on a complex Hilbert space, $\{C \ge 0\}$ denotes the spectral projection of $C$ onto $[0, \infty)$; for a discrete spectral decomposition $C = \sum_i c_i E_i$ it is
--
--   $$\{C \ge 0\} = \sum_{c_i \ge 0} E_i = I - \{C < 0\} .$$
--
--   It contains the kernel of $C$.
--
--   **Formalization Note** Defined as `1 − supportProj C⁻`, so $\{C \ge 0\} + \{C < 0\} = I$ by construction.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, Lemma 1, p.3, and "Proof of Lemma 1", p.4

import Mathlib
import Definitions.Def_QChernoff_Trace_Power

namespace HayashiHoeffding

universe u

/-- The spectral projection `{C ≥ 0}` of a self-adjoint bounded operator `C`: the identity minus
the support projection of the negative part `C⁻`, i.e. the spectral projection `1_{[0,∞)}(C)`
(it includes the kernel of `C`).

Hayashi, arXiv:quant-ph/0611013v2, Lemma 1, p.3: "for any Hermite matrix C we denote the
projection Σ_{ci≥0} Ei ... by {C ≥ 0} ... with the spectral decomposition C = Σ_i ci Ei"; and
p.4: "I − {X^{1−s} − Y^{1−s} ≥ 0} = {X^{1−s} − Y^{1−s} < 0}".

**Formalization Note.** Written as `1 − QChernoff.Trace.supportProj C⁻` (no Borel functional
calculus in Mathlib); this is the paper's `Σ_{cᵢ≥0} Eᵢ` whenever the spectrum is discrete, and
`{C ≥ 0} + {C < 0} = I` holds by construction. Only used on self-adjoint `C`. -/
noncomputable def nonnegProj {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (C : H →L[ℂ] H) : H →L[ℂ] H :=
  1 - QChernoff.Trace.supportProj C⁻

end HayashiHoeffding


