-- Prove2me | Definitions.Def_BaconThesis_Collective_collS
-- name    : BaconThesis_Collective_collS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:02.881201+00:00
-- url     : https://prove2.me/theorems/fbf1485c-a19b-4520-b397-49a0350a0f6c
-- title:
--   Collective spin operators $S_\alpha^{[n]}=\sum_i \tfrac12\sigma_\alpha^{(i)}$
-- statement:
--   For $n$ qubits and $\alpha\in\{x,y,z\}$, the **collective operator**
--   $$
--   S_\alpha^{[n]}=\sum_{i=1}^{n}\tfrac12\,\sigma_\alpha^{(i)}
--   $$
--   is the sum over all qubits of half the Pauli operator $\sigma_\alpha$ acting on that qubit. These are the error operators of collective decoherence: weak collective decoherence has only $S_z$, strong collective decoherence all three $S_x,S_y,S_z$ (Definitions 8.4.1–8.4.2).
--
--   **Formalization Note** $\alpha$ ranges over the published axis labels `BBPSSW.Distill.Axis` and $\sigma_\alpha$ is the published `BBPSSW.Distill.pauli` (basis $0=|0\rangle$, $\sigma_z|0\rangle=|0\rangle$, so $|0\rangle$ has $m=+\tfrac12$ as on p.117). The ladder operators $S_\pm$ are separate definitions. For $n=0$ the sum is empty and $S_\alpha^{[0]}=0$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.30)–(8.31), §8.4, p.113 (PDF p.130)

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BaconThesis_Collective_onQubit

open scoped Matrix

namespace BaconThesis.Collective

/-- **The collective spin operators `S_x^[n], S_y^[n], S_z^[n]`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, (8.30)–(8.31), §8.4, p.113 (PDF p.130):
`S_α^[n] = Σ_{i=1}^n ½ σ_α^(i)`, the collective operator on `n` qubits.

`collS n α` is `Σ_i ½ σ_α^(i)` on `ℂ^(Fin n → Fin 2)` for `α ∈ {x, y, z}`.

**Formalization Note.** `α` ranges over the published `BBPSSW.Distill.Axis` (`.x`, `.y`, `.z`) and
`σ_α` is the published `BBPSSW.Distill.pauli` (basis `0` = `|0⟩`, `σ_z|0⟩ = |0⟩`); the ladder operators `S_±` (the book's
`α = +, −`) are `collPlus` and `collMinus`. Qubits are indexed from `0`. For `n = 0` the sum is
empty and `collS 0 α = 0` on the one-dimensional space. -/
noncomputable def collS (n : ℕ) (α : BBPSSW.Distill.Axis) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ∑ i : Fin n, (1 / 2 : ℂ) • onQubit i (BBPSSW.Distill.pauli α)

end BaconThesis.Collective


