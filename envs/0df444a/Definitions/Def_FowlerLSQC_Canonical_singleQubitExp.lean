-- Prove2me | Definitions.Def_FowlerLSQC_Canonical_singleQubitExp
-- name    : FowlerLSQC_Canonical_singleQubitExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:53.215135+00:00
-- url     : https://prove2.me/theorems/44b32a70-bafd-464b-9280-3418b30fb8af
-- title:
--   Single-qubit exponential $e^{it\sigma}$
-- statement:
--   For a real number $t$ and a $2\times2$ complex matrix $\sigma$, this is the single-qubit gate
--   $$
--   e^{it\sigma}=\sum_{n\ge0}\frac{(it\sigma)^n}{n!}.
--   $$
--   The chapter uses it with $\sigma\in\{X,Y,Z\}$ and $t=\pm\pi/4$ to build the local gates $P_{12},P_{13},P_{23},M_{12},M_{13},M_{23}$ of (4.19)–(4.24), which permute and negate the parameters of a non-local gate.
--
--   **Formalization Note** The exponential is `NormedSpace.exp`; $e^{-i\pi/4\,\sigma}$ is `singleQubitExp σ (-(π/4))`.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §4.4, (4.19)–(4.24), p.52 (PDF p.70)

import Mathlib

namespace FowlerLSQC.Canonical

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §4.4,
(4.19)–(4.24), p.52 (PDF p.70): the single-qubit gate `e^{i t σ}` for a real `t` and a
2×2 matrix `σ`; the book uses `e^{iπ/4 Z}`, `e^{-iπ/4 Z}`, `e^{±iπ/4 Y}`, `e^{±iπ/4 X}`.

**Formalization Note.** The exponential is the matrix exponential `NormedSpace.exp`; the book's
`e^{-iπ/4 σ}` is `singleQubitExp σ (-(π/4))`. -/
noncomputable def singleQubitExp (σ : Matrix Bool Bool ℂ) (t : ℝ) : Matrix Bool Bool ℂ :=
  NormedSpace.exp (((t : ℂ) * Complex.I) • σ)

end FowlerLSQC.Canonical


