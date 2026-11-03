-- Prove2me | Definitions.Def_BaconThesis_Collective_collPlus
-- name    : BaconThesis_Collective_collPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:11.90766+00:00
-- url     : https://prove2.me/theorems/6d4fd969-4a79-40ae-ba37-a186d070aa09
-- title:
--   Collective raising operator $S_+^{[n]}$
-- statement:
--   With the book's convention $\sigma_+=\sigma_x+i\sigma_y$, the **collective raising operator** on $n$ qubits is
--   $$
--   S_+^{[n]}=\sum_{i=1}^n\tfrac12\,\sigma_+^{(i)}=S_x^{[n]}+iS_y^{[n]}.
--   $$
--   In the computational basis $\sigma_+=2|0\rangle\langle1|$, which raises $m=-\tfrac12$ to $m=+\tfrac12$.
--
--   It appears in the collective amplitude damping Hamiltonian $S_+S_-$ of (8.29) and (8.50).
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.30) with α = +, §8.4, p.113 (PDF p.130); σ± = σx ± iσy, (3.21), p.36 (PDF p.53) and (8.22)/(8.25), p.112 (PDF p.129)

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BaconThesis_Collective_onQubit

open scoped Matrix

namespace BaconThesis.Collective

/-- **The collective raising operator `S_+^[n]`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, (8.30)–(8.31), §8.4, p.113 (PDF p.130) with `α = +`, and (8.25), p.112 (PDF p.129):
`S_+ = Σ_i ½ σ_+^(i)` with `σ_+ = σ_x + iσ_y` (the book's convention, p.36 and p.112).

So `S_+^[n] = S_x^[n] + i S_y^[n]`.

**Formalization Note.** Qubits are indexed from `0`; `σ_+ = σ_x + iσ_y = 2|0⟩⟨1|` in the
computational basis (it raises `m = -1/2` to `m = +1/2`). -/
noncomputable def collPlus (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ∑ i : Fin n, (1 / 2 : ℂ) • onQubit i (BBPSSW.Distill.pauli .x + Complex.I • BBPSSW.Distill.pauli .y)

end BaconThesis.Collective


