-- Prove2me | Definitions.Def_BaconThesis_Control_coeffOp
-- name    : BaconThesis_Control_coeffOp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:15.315981+00:00
-- url     : https://prove2.me/theorems/4d1bdf2a-3069-4657-b9ba-69539d1e0611
-- title:
--   Apparatus operators $A_\alpha = \mathrm{Tr}_S[(F_\alpha\otimes I_A)H]$ of the expansion (3.3)
-- statement:
--   Let $H$ be an operator on $\mathcal H_S\otimes\mathcal H_A$ (system first, apparatus second) and $(F_\alpha)$ a family of system operators. The **apparatus operator** with index $\alpha$ is
--   $$
--   A_\alpha = \mathrm{Tr}_S\big[(F_\alpha\otimes I_A)\, H\big],
--   $$
--   where $\mathrm{Tr}_S$ is the partial trace over the system.
--
--   When $(F_\alpha)$ is a fixed basis (trace orthonormal and Hermitian), these are exactly the operators in the expansion
--   $$
--   H = \sum_\alpha F_\alpha\otimes A_\alpha
--   $$
--   of eq. (3.3), so the expansion is computed from $H$ rather than assumed. For Hermitian $H$ they are Hermitian, as the book notes.
--
--   **Formalization Note** The partial trace is the published `WildeQIT.partialTraceLeft`.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §3.2.1, eq. (3.3), p.32 (PDF p.49)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace

open scoped Kronecker

namespace BaconThesis.Control

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§3.2.1, eq. (3.3), p.32 (PDF p.49): the **apparatus operator** `A_α` in the expansion
`H = Σ_α F_α ⊗ A_α` of a system-apparatus Hamiltonian over a fixed basis `F` of the system
operators, computed from `H` as `A_α = Tr_S[(F_α ⊗ I_A) H]`.

**Formalization Note.** The joint space is `ℂ^s ⊗ ℂ^a` as `Matrix (s × a) (s × a) ℂ`, system
first, apparatus second (Mathlib's `⊗ₖ`), and `Tr_S` is the published `WildeQIT.partialTraceLeft`.
For a trace-orthonormal Hermitian basis `F` (`IsFixedBasis`) the `A_α` so defined are the unique
operators with `H = Σ_α F_α ⊗ A_α`, so the expansion (3.3) is not a hypothesis anywhere; for a
Hermitian `H` they are Hermitian, as the book notes. -/
def coeffOp {s a κ : Type} [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a]
    (H : Matrix (s × a) (s × a) ℂ) (F : κ → Matrix s s ℂ) (α : κ) : Matrix a a ℂ :=
  WildeQIT.partialTraceLeft ((F α ⊗ₖ (1 : Matrix a a ℂ)) * H)

end BaconThesis.Control


