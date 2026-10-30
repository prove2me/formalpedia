-- Prove2me | Definitions.Def_FuchsVdGraaf_outcomeDist
-- name    : FuchsVdGraaf_outcomeDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:18.429025+00:00
-- url     : https://prove2.me/theorems/1b5351f2-a8e3-4b63-bcbb-9b66168974a2
-- title:
--   Outcome distribution $p(E)(x) = \mathrm{Tr}(\rho E_x)$ (eq. 10)
-- statement:
--   Applying a POVM $E = \langle E_1,\dots,E_m\rangle$ to a system in state $\rho$ produces outcome $x$ with probability
--
--   $$
--   p(E)(x) = \mathrm{Prob}[\text{result} = x \mid \text{state} = \rho] = \mathrm{Tr}(\rho E_x).
--   $$
--
--   For two states $\rho_0, \rho_1$ this gives the two distributions $p_0(E), p_1(E)$ on the outcome set, to which the classical distinguishability measures are applied.
--
--   **Formalization Note** The value is the real part of the trace; for a density matrix and a POVM the trace is real and nonnegative and the values sum to $1$.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, eq. (10), p.7; §4, p.9

import Mathlib

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, eq. (10), p.7 and §4, p.9: applying the
POVM `E = ⟨E₁, …, E_m⟩` to a system in state `ρ` gives the distribution
`p(E)(x) = Prob[result = x | state = ρ] = Tr(ρ E_x)`.

**Formalization Note.** The value is the real part of the trace; for a density matrix and
positive semidefinite `E_x` the trace is real and nonnegative. Outcomes are `Fin m`. -/
noncomputable def outcomeDist {n : Type} [Fintype n] {m : ℕ} (ρ : Matrix n n ℂ)
    (E : Fin m → Matrix n n ℂ) : Fin m → ℝ :=
  fun x => (Matrix.trace (ρ * E x)).re

end FuchsVdGraaf


