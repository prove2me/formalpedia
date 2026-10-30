-- Prove2me | Definitions.Def_HayashiHoeffding_negProj
-- name    : HayashiHoeffding_negProj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:35.452879+00:00
-- url     : https://prove2.me/theorems/be442e0d-5b80-4a14-be46-56277a32e3ba
-- title:
--   Spectral projection $\{C < 0\}$
-- statement:
--   For a self-adjoint bounded operator $C$ on a complex Hilbert space, $\{C < 0\}$ denotes the spectral projection of $C$ onto $(-\infty, 0)$; for a discrete spectral decomposition $C = \sum_i c_i E_i$ it is
--
--   $$\{C < 0\} = \sum_{c_i < 0} E_i .$$
--
--   It is defined as the orthogonal projection onto the closure of the range of the negative part $C_- $ of $C$.
--
--   These projections define the likelihood-ratio-type tests $T_{n,s}$ of the paper.
--
--   **Formalization Note** Mathlib has no Borel functional calculus; `negProj C := supportProj C⁻` with `C⁻` the continuous-functional-calculus negative part and `supportProj` the published support projection. The closure of the range of $C_-$ is exactly the spectral subspace of $(-\infty,0)$ for every bounded self-adjoint $C$.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, Lemma 1, p.3

import Mathlib
import Definitions.Def_QChernoff_Trace_Power

namespace HayashiHoeffding

universe u

/-- The spectral projection `{C < 0}` of a self-adjoint bounded operator `C`: the support
projection (orthogonal projection onto the closure of the range) of the negative part `C⁻`,
which is the spectral projection `1_{(−∞,0)}(C)`.

Hayashi, arXiv:quant-ph/0611013v2, Lemma 1, p.3: "for any Hermite matrix C we denote the
projection Σ_{ci≥0} Ei (Σ_{ci<0} Ei) by {C ≥ 0} ({C < 0}) with the spectral decomposition
C = Σ_i ci Ei".

**Formalization Note.** Mathlib has no Borel functional calculus, so the spectral projection is
written as `QChernoff.Trace.supportProj C⁻` with `C⁻` the continuous-functional-calculus
negative part. For every bounded self-adjoint `C` the closure of the range of `C⁻` is exactly
the spectral subspace of `(−∞, 0)`, so this agrees with the paper's `Σ_{cᵢ<0} Eᵢ` whenever the
spectrum is discrete. Only used on self-adjoint `C`. -/
noncomputable def negProj {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (C : H →L[ℂ] H) : H →L[ℂ] H :=
  QChernoff.Trace.supportProj C⁻

end HayashiHoeffding


