-- Prove2me | Definitions.Def_UnitalMIP_rhoMax
-- name    : UnitalMIP_rhoMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:35.908834+00:00
-- url     : https://prove2.me/theorems/48e5bf72-bc04-4d26-8eaf-f398c525a647
-- title:
--   Quantum maximal correlation $\rho_{\max}(\psi)$ and the normalized Schatten 2-norm
-- statement:
--   For $X\in M_d$ the **normalized Schatten 2-norm** is $\|X\|_2=\tau_d(X^\dagger X)^{1/2}$, so that $\|\mathbb 1\|_2=1$. For a bipartite state $\psi_{AB}\in M_{d_A}\otimes M_{d_B}$ with maximally mixed marginals, the **quantum maximal correlation** is
--
--   $$
--   \rho_{\max}(\psi_{AB})=\max\Bigl\{\,\bigl|\mathrm{Tr}\bigl[\psi_{AB}(X\otimes Y^\dagger)\bigr]\bigr| \;:\; X\in M_{d_A},\ Y\in M_{d_B},\ \tau_{d_A}(X)=\tau_{d_B}(Y)=0,\ \|X\|_2=\|Y\|_2=1\Bigr\}.
--   $$
--
--   It lies in $[0,1]$ and governs the dichotomy: $\rho_{\max}(\psi)<1$ and $\rho_{\max}(\psi)=1$ are the two regimes of the main theorem.
--
--   **Formalization Note** The maximum is written as the supremum (`sSup`) of the set of admissible values; for $d_A,d_B\ge 2$ the set is nonempty and bounded and the supremum is attained. The norms are the normalized ones of (7).
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), §2.1, (7), p.11; Definition 2.20, p.18

import Mathlib
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals

open scoped Matrix

namespace UnitalMIP

/-- The **normalized Schatten 2-norm** `‖X‖₂ := τ_d(X†X)^{1/2}` (arXiv:2609.39318, version of
2026-11-03, sha256 56ebc59e…, §2.1, (7) with `p = 2`, p.11; `|X|² = X†X`). It is normalized by the
dimension: `‖𝟙‖₂ = 1`.

**Formalization Note** `τ_d(X†X)` is a nonnegative real number; the definition takes the square
root of its real part. Block operators `W = ∑_a |a⟩ ⊗ W_a` are not given a norm of their own: the
statements of the mission use only `‖W†W − 𝟙‖₂` with `W†W = ∑_a W_a† W_a`, which is this norm of
an ordinary matrix. -/
noncomputable def nnorm2 {d : Type} [Fintype d] (X : Matrix d d ℂ) : ℝ :=
  Real.sqrt (ntr (Xᴴ * X)).re

/-- **Quantum maximal correlation** (arXiv:2609.39318, version of 2026-11-03, sha256 56ebc59e…,
Definition 2.20, p.18): for a bipartite state `ψ` on `ℂ^{dA} ⊗ ℂ^{dB}` with maximally mixed
marginals,
`ρmax(ψ) := max { |Tr[ψ (X ⊗ Y†)]| : τ_{dA}(X) = τ_{dB}(Y) = 0, ‖X‖₂ = ‖Y‖₂ = 1 }`.

**Formalization Note** The maximum is written as `sSup` of the set of admissible values. For
`dA, dB ≥ 2` the set is nonempty and bounded (the admissible `X`, `Y` form compact sets), so the
supremum is attained and equals the maximum; the norms are the normalized ones (7). The
definition is applied only to states with maximally mixed marginals, as in the source; it is
total, and on other inputs it is still the same supremum. -/
noncomputable def rhoMax {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB]
    [DecidableEq dB] (ψ : Matrix (dA × dB) (dA × dB) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ (X : Matrix dA dA ℂ) (Y : Matrix dB dB ℂ), ntr X = 0 ∧ ntr Y = 0 ∧
    nnorm2 X = 1 ∧ nnorm2 Y = 1 ∧ r = ‖Matrix.trace (ψ * Matrix.kronecker X Yᴴ)‖}

end UnitalMIP


