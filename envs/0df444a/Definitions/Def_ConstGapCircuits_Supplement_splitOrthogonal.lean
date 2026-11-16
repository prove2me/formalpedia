-- Prove2me | Definitions.Def_ConstGapCircuits_Supplement_splitOrthogonal
-- name    : ConstGapCircuits_Supplement_splitOrthogonal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:28:18.191461+00:00
-- url     : https://prove2.me/theorems/0b2eddcf-d4c8-4f55-b2a1-7b48737a2609
-- title:
--   Linear stabilizers and the split orthogonal group over the binary field
-- statement:
--   For a vector space $V$ over a field $K$ and a function $q:V\to K$, its linear stabilizer is the group of all $K$-linear bijections preserving $q$. On $V=\mathbb F_2^n\times\mathbb F_2^n$, define the quadratic form
--   $$
--   \phi(a,b)=\sum_{i=0}^{n-1}a_i b_i,\qquad
--   \mathrm O^+(2n;\mathbb F_2)=\{T\in\mathrm{GL}_{\mathbb F_2}(V):\phi(Tx)=\phi(x)\text{ for every }x\}.
--   $$
--   This is the automorphism group of the quadratic form itself, including in characteristic two. It supplies the target of the orthogonal Clifford quotient theorem independently of the quantum matrix model.
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), pp. 15–17, Proposition 2.36 and equation (2.38); PDF sha256 e8cf47b0382db220adaab4a2a08a778925d68118885ede05fe433e280cb5da26

import Mathlib

noncomputable section

namespace ConstGapCircuits.Supplement
open scoped BigOperators

/-- The group of linear bijections preserving a given function, used for the quadratic
form in (2.38). The object is defined independently of the Clifford model. -/
def linearStabilizer {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (q : V → K) : Subgroup (V ≃ₗ[K] V) where
  carrier := {T | ∀ x, q (T x) = q x}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro T U hT hU x
    exact (hT (U x)).trans (hU x)
  inv_mem' := by
    intro T hT x
    simpa using (hT (T.symm x)).symm

abbrev PhaseSpace (n : ℕ) := (Fin n → ZMod 2) × (Fin n → ZMod 2)

/-- The quadratic form itself, not its associated alternating bilinear form. -/
def splitQuadratic {n : ℕ} (x : PhaseSpace n) : ZMod 2 := ∑ i, x.1 i * x.2 i

/-- O^+(2n; F_2), all F_2-linear bijections preserving a·b. -/
abbrev SplitOrthogonal (n : ℕ) := ↥(linearStabilizer (splitQuadratic (n := n)))

end ConstGapCircuits.Supplement


