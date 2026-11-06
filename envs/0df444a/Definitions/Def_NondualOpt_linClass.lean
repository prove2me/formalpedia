-- Prove2me | Definitions.Def_NondualOpt_linClass
-- name    : NondualOpt_linClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:41.739694+00:00
-- url     : https://prove2.me/theorems/8a450d25-6731-45e4-8932-f1fa51b265a6
-- title:
--   The linear pairing class $L_{X,H}$
-- statement:
--   The **linear pairing class** is
--   $$
--   L_{X,H}=\{H\ni g\mapsto\langle g,u\rangle:\ u\in X\},
--   $$
--   functions on $H$ indexed by feasible points $u\in X$: the roles of $X$ and $H$ are dualized. The paper's bounds are expressed through $\mathrm{sfat}_\alpha(L_{X,H})$.
--
--   **Formalization Note** The domain is $H$ itself, so shattered trees and covers range over $H$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (6), p.7

import Mathlib

namespace NondualOpt

/-- The linear pairing class `L_{X,H} = {H ∋ g ↦ ⟨g, u⟩ : u ∈ X}`: functions on `H`, indexed by
feasible points `u ∈ X`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (6), p.7.

**Formalization Note.** The domain is the subtype `H`, so trees for `sfat` and sequential covers
range over `H`, as in the paper. -/
def linClass {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F) : Set (H → ℝ) :=
  {h | ∃ u ∈ X, h = fun g : H => pair (g : F) u}

end NondualOpt


