-- Prove2me | Definitions.Def_LowErrExt_IsAffineSource
-- name    : LowErrExt_IsAffineSource
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:23.720698+00:00
-- url     : https://prove2.me/theorems/595b3517-1b15-4419-9280-bd050b4cb91b
-- title:
--   Affine sources and somewhere-uniform (SU) affine sources
-- statement:
--   1. A source $\mathbf Z$ on a finite abelian group is **affine** if it is uniform on a coset (over $\mathbb F_2^n$: an affine subspace).
--   2. A source $\mathbf X=(\mathbf X_i)_{i}$ on $(\mathbb F_2^n)^t$ is **somewhere-uniform (SU) affine** if it is affine and some row $\mathbf X_i$ is uniform on $\mathbb F_2^n$.
--
--   **Formalization Note** Rows are indexed by any finite type (in Lemma 5.3, $[D]\times[D]$).
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), §1.1, p.5; Definition 3.31, p.28

import Mathlib
import Definitions.Def_LowErrExt_IsCoset

open scoped ENNReal

namespace LowErrExt

/-- **Affine source.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…), §1.1,
p.5: "An affine source is just a random variable X ∼ Fn2 that is uniform over some affine
subspace".

`IsAffineSource Z`: `Z` is uniform on a coset `V` of the (finite) abelian group `G`: `Z(z) = 1/|V|`
for `z ∈ V` and `0` otherwise.

**Formalization Note.** Over `𝔽₂ⁿ` (and `(𝔽₂ⁿ)ᵗ`) cosets are exactly affine subspaces. -/
def IsAffineSource {G : Type*} [AddCommGroup G] (Z : PMF G) : Prop :=
  ∃ V : Set G, IsCoset V ∧ ∀ z, Z z = V.indicator (fun _ => ((Nat.card V : ℝ≥0∞))⁻¹) z

/-- **Somewhere-uniform affine source.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 3.31, p.28: "A random variable X ∼ (Fn2)t is called a somewhere-uniform (SU) affine
source if it is an affine source and there exists some i ∈ [t] such that Xi is uniform."

**Formalization Note.** Rows are indexed by a finite type `κ` (in Lemma 5.3, `κ = [D] × [D]`). -/
def IsSUAffine {κ : Type*} {n : ℕ} (Z : PMF (κ → Fin n → ZMod 2)) : Prop :=
  IsAffineSource Z ∧ ∃ i : κ, Z.map (fun z => z i) = PMF.uniformOfFintype (Fin n → ZMod 2)

end LowErrExt


