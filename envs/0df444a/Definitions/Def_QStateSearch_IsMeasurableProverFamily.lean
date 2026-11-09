-- Prove2me | Definitions.Def_QStateSearch_IsMeasurableProverFamily
-- name    : QStateSearch_IsMeasurableProverFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:20.511179+00:00
-- url     : https://prove2.me/theorems/8bfd16f2-2d91-4993-bab1-7a8ebf270c80
-- title:
--   Measurable family of provers $\psi\mapsto P_\psi$
-- statement:
--   A family $\psi\mapsto P_\psi$ of deterministic classical provers, indexed by $\psi\in\mathbb C^D$, is **measurable** if for every transcript $h$, message length $b$ and reply $z$ the set $\{\psi : P_\psi(h,b)=z\}$ is Borel. Then every compatible set $C(h)$ is Borel, hence Haar measurable.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 3, pp.10–11

import Mathlib
import Definitions.Def_QStateSearch_Prover

namespace QStateSearch

/-- A family `ψ ↦ P_ψ` of deterministic classical provers is measurable when, for every
transcript `h`, message length `b` and reply `z`, the set of hidden states whose prover replies
`z` after `h` is Borel.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 3, pp.10–11: "fix a measurable choice ψ ↦ P_ψ, for ψ ∈ CP^{D−1}, of deterministic
classical provers … Measurability of the choice ψ ↦ P_ψ makes every set C(h) Haar measurable."

**Formalization Note.** The family is indexed by vectors of `ℂ^D` (the Haar measure lives on
the unit sphere) rather than by points of `CP^{D−1}`. -/
def IsMeasurableProverFamily {D : ℕ} (P : EuclideanSpace ℂ (Fin D) → Prover) : Prop :=
  ∀ (h : List ℕ) (b : ℕ) (z : Fin (2 ^ b)), MeasurableSet {ψ | P ψ h b = z}

end QStateSearch


