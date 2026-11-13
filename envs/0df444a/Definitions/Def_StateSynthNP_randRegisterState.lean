-- Prove2me | Definitions.Def_StateSynthNP_randRegisterState
-- name    : StateSynthNP_randRegisterState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:47:42.688631+00:00
-- url     : https://prove2.me/theorems/27b86fff-36f2-4e5e-91a6-4484853faca6
-- title:
--   Hadamard transform $H^{\otimes m}$ and the random-register state
-- statement:
--   The Hadamard transform on $m$ qubits has entries $\langle s|H^{\otimes m}|r\rangle=(-1)^{s\cdot r}/\sqrt2^{\,m}$, where $s\cdot r$ is the number of positions where $s$ and $r$ are both $1$. For vectors $v_r$ indexed by $r\in\{0,1\}^m$, the random-register state is
--
--   $$
--   w=(H^{\otimes m}\otimes I)\Bigl(2^{-m/2}\sum_{r\in\{0,1\}^m}|r\rangle\otimes v_r\Bigr),
--   $$
--
--   the result of preparing $v_r$ in superposition over all random strings $r$ and then applying $H^{\otimes m}$ to the random register.
-- source:
--   A. Sen, State Synthesis with an NP oracle, arXiv:2611.02370 (held version, sha256 1705b965726e24478266bc8bdb695f0c6c6e06e172eff71c247272c116f264d0), proof of Lemma 2.2, p.5 ("prepare |ψ̂⟩ … in superposition over all choices of … random bits, and then cleanly uncompute them")

import Mathlib

set_option autoImplicit false

namespace StateSynthNP

/-- The Hadamard transform `H^{⊗m}` on `m` qubits:
`⟨s|H^{⊗m}|r⟩ = (−1)^{s·r} / √2^m`, with `s·r = #{j : s_j = r_j = 1}`. -/
noncomputable def hadamardTensor (m : ℕ) : Matrix (Fin m → Bool) (Fin m → Bool) ℂ :=
  fun s r => (-1 : ℂ) ^ (Finset.univ.filter fun j => s j && r j).card / ((Real.sqrt 2 : ℝ) : ℂ) ^ m

/-- The state obtained by preparing `v_r` in superposition over all `m`-bit random strings `r` and
then applying `H^{⊗m}` to the random register:
`(H^{⊗m} ⊗ I) (2^{−m/2} Σ_r |r⟩ ⊗ v_r)`, as a function of (random-register string, index).

Source: A. Sen, *State Synthesis with an NP oracle*, arXiv:2611.02370 (held version, sha256 1705b965…), proof of Lemma 2.2, p.5: "we can prepare |ψ̂⟩ (with the same global phase) in
superposition over all choices of poly(n, log(1/ε)) size random bits, and then cleanly uncompute
them at the end". -/
noncomputable def randRegisterState {ι : Type} (m : ℕ) (v : (Fin m → Bool) → ι → ℂ) :
    (Fin m → Bool) × ι → ℂ :=
  fun si => ∑ r, hadamardTensor m si.1 r * (((Real.sqrt 2 : ℝ) : ℂ) ^ m)⁻¹ * v r si.2

end StateSynthNP


