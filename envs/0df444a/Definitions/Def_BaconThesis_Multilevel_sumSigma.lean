-- Prove2me | Definitions.Def_BaconThesis_Multilevel_sumSigma
-- name    : BaconThesis_Multilevel_sumSigma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:36:42.541286+00:00
-- url     : https://prove2.me/theorems/9eb7ac52-eb42-4261-b84c-b9c0ba7b0c71
-- title:
--   Coupling generator $\sum_{i>j} c_{ij}\sigma_{ij}$ of an $N$-level atom
-- statement:
--   Consider an atom with $N$ levels $|1\rangle,\dots,|N\rangle$, an orthonormal basis of $\mathbb C^N$. For $i\neq j$ let
--
--   $$
--   \sigma_{ij} = |i\rangle\langle j| + |j\rangle\langle i| .
--   $$
--
--   Given complex coefficients $c_{ij}$ for $i>j$, this definition is the operator
--
--   $$
--   \sum_{i>j=1}^{N} c_{ij}\,\sigma_{ij}.
--   $$
--
--   For $c_{ij}=g_{ij}$, the level-dependent factor of the atom–field coupling (12.2), it is the first generator $\sum_{i>j} g_{ij}\sigma_{ij}$ of the OSR algebra of the thesis's Chapter 12; for $c_{ij}=g_{ij}^{*}$ it is the second generator $\sum_{i>j} g^{*}_{ij}\sigma_{ij}$. The decoherence-free condition (12.3) asks for joint eigenvectors of these two operators.
--
--   **Formalization Note** Levels are indexed by `Fin N` (0-based in Lean, 1-based in the thesis), and $|i\rangle\langle j|$ is the matrix unit `Matrix.single i j 1`. Only the coefficients with $j<i$ enter; the values of $c$ on $i\le j$ are ignored.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §12.1, eqs. (12.1)–(12.3), pp.155–156 (PDF pp.172–173)

import Mathlib

open scoped Matrix

namespace BaconThesis.Multilevel

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§12.1, eqs. (12.1)–(12.3), pp.155–156 (PDF pp.172–173): the system operator
`Σ_{i>j=1}^N c_ij σ_ij` of an `N`-level atom, where `σ_ij = |i⟩⟨j| + |j⟩⟨i|`. With `c = g` this is
the first generator `Σ_{i>j} g_ij σ_ij` of the OSR algebra of the atom–field coupling (12.2); with
`c = g*` (entrywise complex conjugate) it is the second generator `Σ_{i>j} g*_ij σ_ij`.

**Formalization Note.** The levels `|1⟩, …, |N⟩` are the standard basis vectors of `Fin N → ℂ`
(0-based in Lean, 1-based in the book); `|i⟩⟨j|` is `Matrix.single i j 1`. Only the coefficients
`c i j` with `j < i` enter the sum (the book's range `i > j`); the values of `c` on `i ≤ j` are
ignored. -/
def sumSigma {N : ℕ} (c : Fin N → Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ i, ∑ j, if j < i then c i j • (Matrix.single i j 1 + Matrix.single j i 1) else 0

end BaconThesis.Multilevel


