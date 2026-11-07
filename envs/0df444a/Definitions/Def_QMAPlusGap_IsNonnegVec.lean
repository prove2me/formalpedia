-- Prove2me | Definitions.Def_QMAPlusGap_IsNonnegVec
-- name    : QMAPlusGap_IsNonnegVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:19.659351+00:00
-- url     : https://prove2.me/theorems/05a36a0d-5876-4029-a013-af9490c5ea9e
-- title:
--   Nonnegative amplitudes $|\psi\rangle\ge0$
-- statement:
--   Fix a finite-dimensional Hilbert space $\mathcal H=\mathbb C^{\kappa}$ with its computational basis $\{|z\rangle\}_{z\in\kappa}$. A vector $|\psi\rangle=\sum_z\psi_z|z\rangle$ has **nonnegative amplitudes**, written $|\psi\rangle\ge0$, if
--   $$
--   \psi_z\in\mathbb R_{\ge0}\qquad\text{for every }z .
--   $$
--
--   Proofs in $\mathsf{QMA}^+$ are restricted to such vectors, and every soundness statement of the paper quantifies over them.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), §2, p.10

import Mathlib

set_option autoImplicit false

namespace QMAPlusGap

/-- **Nonnegative amplitudes** `|ψ⟩ ≥ 0`, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), §2, p.10: "A pure state `|ψ⟩ = Σ_z ψ_z|z⟩` has nonnegative
amplitudes if `ψ_z ∈ ℝ_{≥0}` for every computational-basis string `z`."

**Formalization Note** A vector of `H = ℂ^κ` is a function `κ → ℂ` (coordinates in the fixed computational
basis); every coordinate is real (imaginary part `0`) and nonnegative. -/
def IsNonnegVec {κ : Type} (ψ : κ → ℂ) : Prop :=
  ∀ z : κ, (ψ z).im = 0 ∧ 0 ≤ (ψ z).re

end QMAPlusGap


