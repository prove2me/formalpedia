-- Prove2me | Definitions.Def_BaconThesis_ExchangeUniv_ket3
-- name    : BaconThesis_ExchangeUniv_ket3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:11.009617+00:00
-- url     : https://prove2.me/theorems/d52bd48f-4d24-492f-865f-57c762b4d25c
-- title:
--   The three-qubit states $|J=\tfrac12,\lambda,\mu\rangle$ of (C.1)
-- statement:
--   On three qubits the four states of total spin $J=\tfrac12$ used in (C.1) are, for degeneracy label $\lambda\in\{0,1\}$ and $\mu\in\{0,1\}$,
--   $$
--   |\tfrac12,0,0\rangle=\tfrac1{\sqrt2}(|010\rangle-|100\rangle),\qquad |\tfrac12,0,1\rangle=\tfrac1{\sqrt2}(|011\rangle-|101\rangle),
--   $$
--   $$
--   |\tfrac12,1,0\rangle=\tfrac1{\sqrt6}(-2|001\rangle+|010\rangle+|100\rangle),\qquad |\tfrac12,1,1\rangle=\tfrac1{\sqrt6}(2|110\rangle-|101\rangle-|011\rangle).
--   $$
--   The label $\lambda$ is the DFS (degeneracy) index on which the exchanges act; $\mu$ is the irrep index on which they act trivially.
--
--   **Formalization Note** The ket $|b_1b_2b_3\rangle$ is the basis vector of the bit string with entries $b_1,b_2,b_3$ at qubits $0,1,2$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (C.1), pp.245–246 (PDF pp.262–263), from (8.46)

import Mathlib

open scoped Matrix

namespace BaconThesis.ExchangeUniv

/-- **The three-qubit basis states `|J = 1/2, λ, μ⟩` of (C.1).**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, (C.1), pp.245–246 (PDF pp.262–263), from (8.46): on three qubits,
* `|1/2, 0, 0⟩ = (|010⟩ − |100⟩)/√2`,  `|1/2, 0, 1⟩ = (|011⟩ − |101⟩)/√2`,
* `|1/2, 1, 0⟩ = (−2|001⟩ + |010⟩ + |100⟩)/√6`,  `|1/2, 1, 1⟩ = (2|110⟩ − |101⟩ − |011⟩)/√6`.

`ket3 λ μ` is the vector `|1/2, λ, μ⟩ ∈ ℂ^(Fin 3 → Fin 2)`; the ket `|b₁b₂b₃⟩` is the basis vector
of the bit string `x` with `x 0 = b₁`, `x 1 = b₂`, `x 2 = b₃`.

**Formalization Note.** Qubits `1, 2, 3` of the book are `0, 1, 2`. The basis kets are written as
indicator functions `fun x => if x = ![b₁, b₂, b₃] then 1 else 0`. -/
noncomputable def ket3 (lam mu : Fin 2) : (Fin 3 → Fin 2) → ℂ :=
  let e : (Fin 3 → Fin 2) → (Fin 3 → Fin 2) → ℂ := fun b x => if x = b then 1 else 0
  if lam = 0 then
    if mu = 0 then (1 / Real.sqrt 2 : ℂ) • (e ![0, 1, 0] - e ![1, 0, 0])
    else (1 / Real.sqrt 2 : ℂ) • (e ![0, 1, 1] - e ![1, 0, 1])
  else
    if mu = 0 then (1 / Real.sqrt 6 : ℂ) • (-(2 : ℂ) • e ![0, 0, 1] + e ![0, 1, 0] + e ![1, 0, 0])
    else (1 / Real.sqrt 6 : ℂ) • ((2 : ℂ) • e ![1, 1, 0] - e ![1, 0, 1] - e ![0, 1, 1])

end BaconThesis.ExchangeUniv


