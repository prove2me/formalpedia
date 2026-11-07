-- Prove2me | Definitions.Def_SetMultCost_projection
-- name    : SetMultCost_projection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:56.989927+00:00
-- url     : https://prove2.me/theorems/d7ab31d2-4cd8-4acb-93cf-07f839a82d85
-- title:
--   Projection by variable substitution
-- statement:
--   A **projection** sends each variable to a variable or to $0$ and extends to an $F$-algebra map of polynomial rings. It is **part-preserving** when each variable goes to a variable of its own part or to $0$.
--
--   The paper uses this for the last step of Corollary 2.7: a width-$n$ set-multilinear algebraic branching program computes a part-preserving projection of $\mathrm{IMM}_{n,d}$, and applying the substitution to a circuit yields a circuit for the projection.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Proof of Corollary 2.7, p.11

import Mathlib

namespace SetMultCost

/-- A **projection by variable substitution**: each variable goes to a variable (`some y`) or to
`0` (`none`). The last line of the proof of Corollary 2.7 (Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.11) calls it a "set-multilinear
restriction" of `IMM_{n,d}` and applies "this linear substitution to the circuit". -/
noncomputable def projection {σ τ : Type*} (F : Type*) [CommRing F] (ρ : σ → Option τ) :
    MvPolynomial σ F →ₐ[F] MvPolynomial τ F :=
  MvPolynomial.aeval fun x => match ρ x with
    | some y => MvPolynomial.X y
    | none => 0

/-- The substitution sends each variable to a variable of its own part or to `0`; so it preserves
set-multilinearity. -/
def IsPartPreserving {σ τ ι : Type*} (partσ : σ → ι) (partτ : τ → ι) (ρ : σ → Option τ) : Prop :=
  ∀ x y, ρ x = some y → partτ y = partσ x

end SetMultCost


