-- Prove2me | Definitions.Def_QMAPlusGap_IsSphereProb
-- name    : QMAPlusGap_IsSphereProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:57.385879+00:00
-- url     : https://prove2.me/theorems/1bcdf407-f4c0-4a16-8e29-4cf9bfb80d18
-- title:
--   Probability measures on the unit sphere of $\mathbb C^\iota$
-- statement:
--   A **probability measure on the unit sphere** of $\mathcal H=\mathbb C^{\iota}$ is a Borel probability measure $\mu$ on $\mathbb C^{\iota}$ with
--   $$
--   \mu\{\psi:\ \|\psi\|=1\}=1 .
--   $$
--   The de Finetti statements approximate reduced states by mixtures $\int(|\psi\rangle\langle\psi|)^{\otimes\ell}\,d\mu(\psi)$ over such measures.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 10, p.17; Theorem 12, p.25; Theorem A.4, p.36

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_vnorm

set_option autoImplicit false

namespace QMAPlusGap

open MeasureTheory

/-- A **probability measure on the unit sphere of `H = ℂ^ι`**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…) (Lemma 10, p.17: "a probability measure on
unit vectors"; Theorem 12, p.25 and Theorem A.4, p.36: "a probability measure on the unit sphere of H").

**Formalization Note** `μ` is a probability measure on `ι → ℂ` (product Borel σ-algebra) that is concentrated
on the Euclidean unit sphere `{ψ | ArgmaxDeFinetti.vnorm ψ = 1}`. -/
def IsSphereProb {ι : Type} [Fintype ι] (μ : Measure (ι → ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ᵐ ψ ∂μ, ArgmaxDeFinetti.vnorm ψ = 1

end QMAPlusGap


