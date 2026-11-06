-- Prove2me | Definitions.Def_HMBinPacking_LatticePolytope
-- name    : HMBinPacking_LatticePolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:08.474202+00:00
-- url     : https://prove2.me/theorems/df067ffe-8fba-4d48-87f8-8840d0baec25
-- title:
--   Lattice polytopes and the integer decomposition property
-- statement:
--   A **lattice polytope** in $\mathbb R^d$ is the convex hull of a finite nonempty subset of $\mathbb Z^d$. For a set $Q\subseteq\mathbb R^d$ and a real $n>0$, $nQ:=\{nx:x\in Q\}$.
--
--   A lattice polytope $Q\subseteq\mathbb R^d$ has the **integer decomposition property** if for every integer $n\ge1$, each
--   $$
--   z\in nQ\cap\mathbb Z^d
--   $$
--   can be expressed as a sum $z=p_1+\dots+p_n$ of $n$ points $p_1,\dots,p_n\in Q\cap\mathbb Z^d$ (repetitions allowed).
--
--   Lemma 2 gives this property for the polytopes $r+k\,\mathrm{conv}(V)$ with $k\ge d$; Lemma 4 uses it to split the integer point $z_r\in n_rP_r$ into $n_r$ bin configurations.
--
--   **Formalization Note** The paper defines the property for lattice polytopes, so `HasIDP Q` includes `IsLatticePolytope Q`. Dilation is the pointwise scalar multiple of a set.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, §2, p.4 (lattice polytope, nQ, integer decomposition property)

import Mathlib
import Definitions.Def_HMBinPacking_Casts
open scoped Pointwise

namespace HMBinPacking

/-- **Lattice polytope.**
Koana, Kumabe, arXiv:2609.16923v2, §2, p.4: "A lattice polytope in R^d is the convex hull of a
finite nonempty subset of Z^d."

**Formalization Note.** `R^d` is `Fin d → ℝ`; `Z^d` is `Fin d → ℤ`, cast with `zCast`. -/
def IsLatticePolytope {d : ℕ} (Q : Set (Fin d → ℝ)) : Prop :=
  ∃ V : Set (Fin d → ℤ), V.Finite ∧ V.Nonempty ∧ Q = convexHull ℝ (zCast '' V)

/-- **The integer decomposition property.**
Koana, Kumabe, arXiv:2609.16923v2, §2, p.4: "For a polytope Q ⊆ R^d and a real number n > 0, we
define nQ := {nx : x ∈ Q}. A lattice polytope Q ⊆ R^d has the integer decomposition property if, for
every integer n ≥ 1, each z ∈ nQ ∩ Z^d can be expressed as a sum of n points of Q ∩ Z^d."

**Formalization Note.** The paper defines the property for lattice polytopes, so `HasIDP Q` includes
`IsLatticePolytope Q`. `nQ` is the pointwise dilation `(n : ℝ) • Q`. A sum of `n` points is a family
`p : Fin n → ℤ^d` (repetitions allowed) with every `p j ∈ Q`. -/
def HasIDP {d : ℕ} (Q : Set (Fin d → ℝ)) : Prop :=
  IsLatticePolytope Q ∧
    ∀ n : ℕ, 1 ≤ n → ∀ z : Fin d → ℤ, zCast z ∈ (n : ℝ) • Q →
      ∃ p : Fin n → Fin d → ℤ, (∀ j, zCast (p j) ∈ Q) ∧ ∑ j, p j = z

end HMBinPacking


