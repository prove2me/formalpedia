-- Prove2me | Definitions.Def_DHRUniq_psiPlus
-- name    : DHRUniq_psiPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:43.549512+00:00
-- url     : https://prove2.me/theorems/dea4b5d9-f54c-4775-aa16-37455d26ecb3
-- title:
--   The wavefunction $|\Psi_+(\mathbb C^d)\rangle$
-- statement:
--   On $\mathbb C^d\otimes\mathbb C^d$ with standard basis $(|i\rangle)_{i=1}^d$,
--
--   $$
--   |\Psi_+(\mathbb C^d)\rangle=\sum_{i=1}^d\frac1{\sqrt d}\,|i\rangle\otimes|i\rangle .
--   $$
--
--   This is the maximally entangled wavefunction of Definition 8; for $d=2$ its state $P_+(\mathbb C^2)$ is the Bell pair that fixes the unit of entanglement in (P1′).
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Definition 8, p. 7

import Mathlib

namespace DHRUniq

/-- **The wavefunction `|Ψ_+(ℂ^d)⟩ = ∑_{i=1}^d (1/√d) |ψ_i ⊗ ψ_i⟩`** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, Definition 8,
p. 7), on `ℂ^d ⊗ ℂ^d` with the standard basis as the chosen orthonormal basis.

**Formalization Note** `P_+(ℂ²)` of (P1′) is `pureState (psiPlus 2)`. -/
noncomputable def psiPlus (d : ℕ) : Fin d × Fin d → ℂ :=
  fun z => if z.1 = z.2 then ((Real.sqrt d)⁻¹ : ℝ) else 0

end DHRUniq


