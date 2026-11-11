-- Prove2me | Definitions.Def_NCQuadLB_Circuit_B
-- name    : NCQuadLB_Circuit_B
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:28:59.190073+00:00
-- url     : https://prove2.me/theorems/7847db71-3c93-40b1-8ec3-cc94bb4a711a
-- title:
--   The spanning sets $\mathcal B_v\subseteq\mathbb F\langle X\rangle$ of a circuit
-- statement:
--   Let $\Psi$ be a fan-in 2 circuit over $\mathbb F\langle X,Y\rangle$. For every vertex $v$ define $\mathcal B_v\subseteq\mathbb F\langle X\rangle$ inductively:
--
--   1. leaves: $\mathcal B_\ell=\{1\}$;
--   2. sum gates: $\mathcal B_v=\bigcup_{u\in\mathrm{ch}(v)}\mathcal B_u$;
--   3. product gates $p=a\times b$: $$\mathcal B_p=\mathcal B_a\cup\{\hat a_X\cdot h\mid h\in\mathcal B_b\},$$ where $\hat a$ is the polynomial computed at the left child $a$.
--
--   These sets span the $X$-coefficients of the separated part of each gate's polynomial, and the lower bound counts them after projection to degree $d$.
--
--   **Formalization Note** $\hat a$ is the polynomial computed at $a$ itself, not the one carried by the scaled edge; edge scalars do not enter $\mathcal B$.
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), Definition 3.1, p.5

import Mathlib
import Definitions.Def_NCQuadLB_Circuit
import Definitions.Def_NCQuadLB_CoeffX

namespace NCQuadLB

namespace Circuit

variable {F : Type*} [Field F] {σ τ : Type*}

/-- The spanning sets `ℬ_v ⊆ F⟨X⟩` (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative
Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, Definition 3.1, p.5),
defined inductively over the vertices:
* leaves: `ℬ_ℓ = {1}`;
* sum gates: `ℬ_v = ⋃_{u ∈ ch(v)} ℬ_u`;
* product gates `p = a × b`: `ℬ_p = ℬ_a ∪ {â_X · h | h ∈ ℬ_b}`.

**Formalization Note** `â` is the polynomial computed at the left child `a` itself (`value a`), not
the polynomial carried by the scaled edge; `â_X` is `xPart`. The edge scalars do not enter `ℬ`. -/
noncomputable def B (C : Circuit F (σ ⊕ τ)) (k : Fin C.size) : Set (FreeAlgebra F (σ ⊕ τ)) :=
  match C.node k with
  | .const _ => {1}
  | .var _ => {1}
  | .add a b _ _ => C.B (C.child a) ∪ C.B (C.child b)
  | .mul a b _ _ => C.B (C.child a) ∪ (fun h => xPart (C.value (C.child a)) * h) '' C.B (C.child b)
termination_by k.val
decreasing_by all_goals simp only [child]; omega

end Circuit

end NCQuadLB


