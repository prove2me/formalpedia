-- Prove2me | Definitions.Def_BaconThesis_DFS_evolOp
-- name    : BaconThesis_DFS_evolOp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:07.113421+00:00
-- url     : https://prove2.me/theorems/b96cd0a1-f4ba-4c78-b9a0-639d2299775e
-- title:
--   The joint evolution operator $U(t)=\exp[-iHt]$
-- statement:
--   Let $\mathcal H=\mathbb C^{\iota}$ be a finite-dimensional Hilbert space and let $H$ be an operator on $\mathcal H$ (in applications a Hamiltonian, i.e. Hermitian). For a real time $t$ the **evolution operator** is
--   $$
--   U(t)=\exp[-iHt]=\sum_{n=0}^{\infty}\frac{(-it)^n}{n!}H^n ,
--   $$
--   with $\hbar=1$. When $H$ is Hermitian, $U(t)$ is unitary.
--
--   In this mission $H$ is the joint Hamiltonian of a system and its environment, and $U(t)$ is the operator whose Taylor expansion (5.3) drives the proof that the OSR operators lie in the OSR algebra.
--
--   **Formalization Note** Operators are matrices `Matrix ι ι ℂ`; the exponential is Mathlib's `NormedSpace.exp` applied to $(-it)H$. Hermiticity of $H$ is not built into the definition; the statements that need $U(t)$ unitary assume it.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §2.2.1, p.16 (PDF p.33); eq. (5.3), p.69 (PDF p.86)

import Mathlib

namespace BaconThesis.DFS

/-- **The joint evolution operator `U(t) = exp[−iHt]`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§2.2.1, p.16 (PDF p.33), "U(t) = exp[−iHt]", and eq. (5.3), p.69 (PDF p.86), where the same
operator is expanded as a Taylor series.

For a square complex matrix `H` on a finite index type `ι` and a real time `t`,
`evolOp H t = exp((−i t) H)`.

**Formalization Note.** Hilbert spaces are `ι → ℂ` with `Fintype ι`, operators are
`Matrix ι ι ℂ`. The exponential is Mathlib's `NormedSpace.exp` (the power series
`∑ₙ Xⁿ/n!`, independent of any choice of norm). `ħ = 1` as in the book. Hermiticity of `H` is
not built in: the statements that need `U(t)` unitary assume `H.IsHermitian`. -/
noncomputable def evolOp {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (t : ℝ) :
    Matrix ι ι ℂ :=
  NormedSpace.exp ((-(t : ℂ) * Complex.I) • H)

end BaconThesis.DFS


