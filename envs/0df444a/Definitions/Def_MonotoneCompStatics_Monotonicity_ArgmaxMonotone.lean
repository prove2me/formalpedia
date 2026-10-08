-- Prove2me | Definitions.Def_MonotoneCompStatics_Monotonicity_ArgmaxMonotone
-- name    : MonotoneCompStatics_Monotonicity_ArgmaxMonotone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:29.777715+00:00
-- url     : https://prove2.me/theorems/44c44365-ba69-491b-adfd-df5295a9e9a9
-- title:
--   Monotonicity of maximizers in parameter and constraint set
-- statement:
--   Let $X$ be a lattice, $T$ a partially ordered parameter set, and $f:X\times T\to\mathbb R$. Write $M(t,S)=\operatorname{argmax}_{x\in S}f(x,t)$. The maximizer correspondence is **monotone nondecreasing in $(t,S)$** when
--
--   $$t\le t',\quad S\le_s S'\quad\Longrightarrow\quad M(t,S)\le_s M(t',S')$$
--
--   for every $t,t'\in T$ and every pair of constraint sets $S,S'\subseteq X$. Here $A\le_s B$ is the strong set order: for $a\in A$ and $b\in B$, their meet belongs to $A$ and their join belongs to $B$.
--
--   **Formalization Note** This quantifies over all constraint sets, including empty sets, and makes no attainment assumption. Lean represents $f$ as a curried function and imports the published strong set order, which has the same empty-set convention as the paper.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), pp. 159, 162 (PDF 4, 7), strong set order and Theorem 4 proof

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_MonotoneCompStatics_Monotonicity_argmaxOn

namespace MonotoneCompStatics.Monotonicity

def ArgmaxMonotone {X T : Type*} [Lattice X] [PartialOrder T] (f : X → T → ℝ) : Prop :=
  ∀ ⦃t t' : T⦄ ⦃S S' : Set X⦄, t ≤ t' → Supermodularity.Lattices.InducedSetOrder S S' →
    Supermodularity.Lattices.InducedSetOrder (argmaxOn (fun x => f x t) S) (argmaxOn (fun x => f x t') S')

end MonotoneCompStatics.Monotonicity


