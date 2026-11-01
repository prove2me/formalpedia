-- Prove2me | Definitions.Def_BaconThesis_Supercoherence_IsGroundEnergy
-- name    : BaconThesis_Supercoherence_IsGroundEnergy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:43.677406+00:00
-- url     : https://prove2.me/theorems/eece3029-44bb-43aa-982d-3c6042b7d79f
-- title:
--   $E$ is the ground-state energy (lowest eigenvalue) of $H$
-- statement:
--   A real number $E$ is the **ground-state energy** of a square complex matrix $H$ if
--
--   1. $E$ is an eigenvalue of $H$: some nonzero vector $v$ has $Hv = Ev$;
--   2. every eigenvalue $\mu$ of $H$ satisfies $E \le \operatorname{Re}\mu$.
--
--   For a Hermitian $H$ all eigenvalues are real, so $E$ is the minimum of the spectrum. At most one $E$ has this property.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, p.169 (PDF p.186), and Definition 15.2.1, pp.170–171 (PDF pp.187–188)

import Mathlib
import Definitions.Def_BaconThesis_Supercoherence_groundSpace

open Matrix

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §15.2, p.169 (PDF p.186) and Definition 15.2.1, pp.170–171 (PDF pp.187–188):
`E` is the ground-state energy of `H`, i.e. the lowest eigenvalue: `E` is an eigenvalue of `H`
(its eigenspace is nonzero) and every eigenvalue `μ` of `H` satisfies `E ≤ Re μ`.

**Formalization Note.** For the Hermitian Hamiltonians of the chapter every eigenvalue is real,
so `E ≤ Re μ` is `E ≤ μ`. At most one `E` satisfies the predicate. -/
def IsGroundEnergy {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (E : ℝ) : Prop :=
  groundSpace H E ≠ ⊥ ∧
    ∀ (μ : ℂ) (v : ι → ℂ), v ≠ 0 → H *ᵥ v = μ • v → E ≤ μ.re

end BaconThesis.Supercoherence


