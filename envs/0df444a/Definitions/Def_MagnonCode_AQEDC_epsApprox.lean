-- Prove2me | Definitions.Def_MagnonCode_AQEDC_epsApprox
-- name    : MagnonCode_AQEDC_epsApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:32.166258+00:00
-- url     : https://prove2.me/theorems/c859ad76-9e54-4d2b-9985-a7e316bea4ed
-- title:
--   Eq. (3): the defect $\epsilon_{\mathrm{approx}}$
-- statement:
--   Let $\{\psi_\alpha\}_{\alpha\in[K]}$ be vectors and $\{R_j\}_{j\in[J]}$ operators. The approximate Knill-Laflamme defect is
--
--   $$
--   \epsilon_{\mathrm{approx}}:=\max_{\alpha,\beta\in[K]}\sum_{j\in[J]}\bigl|\langle\psi_\alpha|R_j|\psi_\beta\rangle-\delta_{\alpha,\beta}\langle\psi_1|R_j|\psi_1\rangle\bigr|^2.
--   $$
--
--   It measures how far the code is from the exact detection condition, summed over all Kraus operators.
--
--   **Formalization Note** The index set is any finite type, with a distinguished element in the role of the index $1$; this also makes it nonempty, so the maximum is a true maximum.
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Eq. (3), p. 11

import Mathlib

namespace MagnonCode.AQEDC

open scoped Matrix

/-- **Eq. (3)** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 11): the approximate Knill-Laflamme defect
`ε_approx = max_{α,β ∈ [K]} Σ_{j ∈ [J]} |⟨ψ_α|R_j|ψ_β⟩ − δ_{α,β}⟨ψ_1|R_j|ψ_1⟩|²`.

**Formalization Note** `K` is any finite index type and `α₀` plays the printed index `1`. The maximum
is `Finset.sup'` over the nonempty set `K × K`, so it is the true maximum. -/
noncomputable def epsApprox {X K J : Type*} [Fintype X] [Fintype K] [DecidableEq K] [Fintype J]
    (α₀ : K) (R : J → Matrix X X ℂ) (ψ : K → X → ℂ) : ℝ :=
  Finset.univ.sup' ⟨(α₀, α₀), Finset.mem_univ _⟩ fun a : K × K =>
    ∑ j, ‖star (ψ a.1) ⬝ᵥ R j *ᵥ ψ a.2 -
        (if a.1 = a.2 then star (ψ α₀) ⬝ᵥ R j *ᵥ ψ α₀ else 0)‖ ^ 2

end MagnonCode.AQEDC


