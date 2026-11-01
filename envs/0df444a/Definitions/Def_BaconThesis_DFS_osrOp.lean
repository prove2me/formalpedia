-- Prove2me | Definitions.Def_BaconThesis_DFS_osrOp
-- name    : BaconThesis_DFS_osrOp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:45.526993+00:00
-- url     : https://prove2.me/theorems/fcae0afe-fc21-4294-8b7c-fd9084b91894
-- title:
--   The OSR operator $\langle\varphi|U(t)|\psi\rangle$ of a system–environment evolution
-- statement:
--   Let $H$ be an operator on $\mathcal H_S\otimes\mathcal H_E$ (finite dimensional) with evolution operator $U(t)=\exp[-iHt]$, and let $\varphi,\psi\in\mathcal H_E$ be environment vectors. The system operator
--   $$
--   \langle\varphi|U(t)|\psi\rangle=(I_S\otimes\langle\varphi|)\,U(t)\,(I_S\otimes|\psi\rangle),
--   \qquad
--   \big(\langle\varphi|U(t)|\psi\rangle\big)_{ab}=\sum_{k,l}\overline{\varphi_k}\;U(t)_{(a,k),(b,l)}\;\psi_l ,
--   $$
--   is the partial matrix element of $U(t)$ between $\varphi$ and $\psi$. The thesis's **OSR operators** are
--   $$
--   A_{i=(\mu,\nu)}(t)=\sqrt{p_\nu}\,\langle\mu|U(t)|\nu\rangle ,
--   $$
--   where $\rho_E(0)=\sum_\nu p_\nu|\nu\rangle\langle\nu|$ is the spectral decomposition of the environment's initial state and $\{|\mu\rangle\}$ is an orthonormal basis of the environment; this is the case $\varphi=|\mu\rangle$, $\psi=\sqrt{p_\nu}|\nu\rangle$.
--
--   **Formalization Note** The joint space is indexed by pairs, system first. The bra $\langle\varphi|$ conjugates the entries of $\varphi$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §2.2.1, eq. (2.11), p.16 (PDF p.33); eq. (5.6), p.70 (PDF p.87)

import Mathlib
import Definitions.Def_BaconThesis_DFS_evolOp

namespace BaconThesis.DFS

/-- **An OSR operator `⟨φ|U(t)|ψ⟩` of the joint evolution.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§2.2.1, eq. (2.11), p.16 (PDF p.33): `A_{i=(µ,ν)}(t) = √p_ν ⟨µ|U(t)|ν⟩`, and eq. (5.6), p.70
(PDF p.87).

For a joint Hamiltonian `H` on system ⊗ environment, a time `t` and environment vectors `φ`, `ψ`,
`osrOp H t φ ψ` is the system operator `(I ⊗ ⟨φ|) U(t) (I ⊗ |ψ⟩)`, with entries
`(osrOp H t φ ψ)_{ab} = ∑_{k,l} conj(φ_k) U(t)_{(a,k),(b,l)} ψ_l`.
The book's OSR operator `A_{(µ,ν)}(t)` is `osrOp H t |µ⟩ (√p_ν |ν⟩)`, where `ρ_E(0) = ∑_ν p_ν |ν⟩⟨ν|`
is the spectral decomposition of the environment state and `|µ⟩` is an orthonormal basis of the
environment.

**Formalization Note.** The joint space is indexed by `s × e`, system first; `U(t)` is
`evolOp H t = exp(−itH)`. The bra `⟨φ|` conjugates `φ`. -/
noncomputable def osrOp {s e : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]
    (H : Matrix (s × e) (s × e) ℂ) (t : ℝ) (φ ψ : e → ℂ) : Matrix s s ℂ :=
  Matrix.of fun a b => ∑ k, ∑ l, star (φ k) * evolOp H t (a, k) (b, l) * ψ l

end BaconThesis.DFS


