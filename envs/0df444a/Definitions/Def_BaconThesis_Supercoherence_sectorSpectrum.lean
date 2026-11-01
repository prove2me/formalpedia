-- Prove2me | Definitions.Def_BaconThesis_Supercoherence_sectorSpectrum
-- name    : BaconThesis_Supercoherence_sectorSpectrum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:14.273542+00:00
-- url     : https://prove2.me/theorems/235ba266-e41f-42a2-a1c8-985b90315d9a
-- title:
--   Eigenvalues of $H$ on the stabilizer sector $(S_1,S_2)=(s_1,s_2)$
-- statement:
--   For complex numbers $s_1, s_2$ (in the chapter, $s_1, s_2 \in \{+1,-1\}$), the set of eigenvalues of the Hamiltonian $H$ of (15.7) with an eigenvector in the joint eigenspace $\{S_1 = s_1, S_2 = s_2\}$ of the stabilizer generators:
--
--   $$\operatorname{spec}_{s_1,s_2}(H) = \{ \mu \in \mathbb C : \exists v \ne 0,\ S_1 v = s_1 v,\ S_2 v = s_2 v,\ H v = \mu v \}.$$
--
--   Since $H$ commutes with $S_1$ and $S_2$, this is the spectrum of $H$ restricted to that sector.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, eq. (15.9) and the sentence after it, p.169 (PDF p.186)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_S1
import Definitions.Def_BaconThesis_Supercoherence_S2
import Definitions.Def_BaconThesis_Supercoherence_codeHamiltonian

open QMaxCutSDP.Rounding Matrix

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, eq. (15.9) and the sentence after it, p.169 (PDF p.186): the eigenvalues of the
Hamiltonian `H` of (15.7) on the joint eigenspace of the stabilizer generators with eigenvalues
`S₁ = s₁`, `S₂ = s₂`: the set of `μ` for which some nonzero vector `v` has `S₁ v = s₁ v`,
`S₂ v = s₂ v` and `H v = μ v`.

**Formalization Note.** `s₁, s₂` are complex scalars; the chapter uses `s₁, s₂ ∈ {+1, −1}`. Since
`H` commutes with `S₁, S₂`, this is the spectrum of `H` restricted to that sector. -/
def sectorSpectrum (s1 s2 : ℂ) : Set ℂ :=
  {μ | ∃ v : (Fin 4 → Fin 2) → ℂ, v ≠ 0 ∧ S1 *ᵥ v = s1 • v ∧ S2 *ᵥ v = s2 • v ∧
    codeHamiltonian *ᵥ v = μ • v}

end BaconThesis.Supercoherence


