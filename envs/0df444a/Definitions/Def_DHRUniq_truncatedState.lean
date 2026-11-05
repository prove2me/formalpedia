-- Prove2me | Definitions.Def_DHRUniq_truncatedState
-- name    : DHRUniq_truncatedState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:55.403773+00:00
-- url     : https://prove2.me/theorems/85951ee2-3c30-448b-afb0-5479616c6725
-- title:
--   Truncation $|\phi_n\rangle$ of a Schmidt decomposition
-- statement:
--   Given a Schmidt decomposition $\sum_i\sqrt{p_i}\,|e_i\rangle\otimes|f_i\rangle$ and an index set $\mathrm{TYP}$, with $p=\sum_{i\in\mathrm{TYP}}p_i$, the **truncated wavefunction** is
--
--   $$
--   |\phi_n\rangle=\frac1{\sqrt p}\sum_{i\in\mathrm{TYP}}\sqrt{p_i}\,|e_i\rangle\otimes|f_i\rangle .
--   $$
--
--   In the proof of the uniqueness theorem it is the typical part of $|\psi^{\otimes n}\rangle$.
--
--   **Formalization Note** The formula is used only when $p>0$.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §8, p. 18

import Mathlib

namespace DHRUniq

/-- **The truncation `|φ_n⟩ = p^{-1/2} ∑_{i ∈ TYP} √p_i |e_i⟩ ⊗ |f_i⟩`** of a Schmidt decomposition
to an index set `TYP`, with `p = ∑_{i ∈ TYP} p_i` (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §8, p. 18, the display after (34-c)).

**Formalization Note** When `p = 0`, `(Real.sqrt 0)⁻¹ = 0` and the vector is `0`; the mission uses
it only with `p ≥ 1 - ε > 0`. -/
noncomputable def truncatedState {ι a b : Type} (TYP : Finset ι) (p : ι → ℝ) (e : ι → a → ℂ)
    (f : ι → b → ℂ) : a × b → ℂ :=
  fun z => ((Real.sqrt (∑ i ∈ TYP, p i))⁻¹ : ℝ) *
    ∑ i ∈ TYP, (Real.sqrt (p i) : ℂ) * e i z.1 * f i z.2

end DHRUniq


