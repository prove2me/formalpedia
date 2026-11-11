-- Prove2me | Definitions.Def_NCQuadLB_Circuit_Path
-- name    : NCQuadLB_Circuit_Path
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:29:08.189967+00:00
-- url     : https://prove2.me/theorems/9ceff2e8-15d1-4a5e-929a-5d5492d9da84
-- title:
--   Paths from a vertex to a leaf and their weights $w_\pi$
-- statement:
--   Let $\Psi$ be a fan-in 2 circuit over $\mathbb F\langle X,Y\rangle$. A **path from $v$ to a leaf** starts at $v$ and repeatedly follows one in-edge of the current gate to the corresponding child until it reaches a leaf. Its **weight** is
--
--   $$
--   w_\pi=\prod_{i=0}^m c_{v_i},\qquad c_{v_i}=\begin{cases}(\hat a_i)_X&\text{if }v_i=a_i\times b_i\text{ is a product gate and the path continues to }b_i,\\1&\text{otherwise,}\end{cases}
--   $$
--
--   the product taken in path order ($c_{v_0}$ leftmost), where $\hat a_i$ is the polynomial computed at the left child.
--
--   Lemma 3.3 identifies $\mathcal B_v$ with the set of these weights.
--
--   **Formalization Note** A path is a sequence of in-edge choices (first or second edge at a sum gate, left or right at a product gate), not of vertices: when both in-edges of a gate come from one vertex, the two choices are different paths.
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), Lemma 3.3, p.6

import Mathlib
import Definitions.Def_NCQuadLB_Circuit
import Definitions.Def_NCQuadLB_CoeffX

namespace NCQuadLB

namespace Circuit

variable {F : Type*} [Field F] {σ τ : Type*}

/-- A **path from vertex `k` to a leaf** (Shastri, Willumsgaard, *A Quadratic Lower Bound for
Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, Lemma 3.3,
p.6): starting at `k`, follow one in-edge of the current gate to one of its children, until a leaf is
reached.

**Formalization Note** A path is a sequence of in-edge choices, not of vertices: at a `+` gate it goes
to the first (`addLeft`) or the second (`addRight`) child, at a `×` gate to the left (`mulLeft`) or the
right (`mulRight`) child. When both in-edges of a gate come from the same vertex the two choices are
different paths. -/
inductive Path (C : Circuit F (σ ⊕ τ)) : Fin C.size → Type _
  /-- the path of length `0` at a leaf -/
  | leaf {k : Fin C.size} (h : (C.node k).isLeaf = true) : Path C k
  /-- through the first in-edge of a `+` gate -/
  | addLeft {k : Fin C.size} {a b : Fin k} {α β : F} (h : C.node k = .add a b α β)
      (π : Path C (C.child a)) : Path C k
  /-- through the second in-edge of a `+` gate -/
  | addRight {k : Fin C.size} {a b : Fin k} {α β : F} (h : C.node k = .add a b α β)
      (π : Path C (C.child b)) : Path C k
  /-- through the left in-edge of a `×` gate -/
  | mulLeft {k : Fin C.size} {a b : Fin k} {α β : F} (h : C.node k = .mul a b α β)
      (π : Path C (C.child a)) : Path C k
  /-- through the right in-edge of a `×` gate -/
  | mulRight {k : Fin C.size} {a b : Fin k} {α β : F} (h : C.node k = .mul a b α β)
      (π : Path C (C.child b)) : Path C k

/-- The weight `w_π = ∏_{i=0}^m c_{v_i}` of a path `π = (v_0, …, v_m)` (Lemma 3.3, p.6), the product
taken in path order (`c_{v_0}` leftmost), where `c_{v_i} = (â_i)_X` if `v_i = a_i × b_i` is a product
gate and the path continues to its right child `b_i`, and `c_{v_i} = 1` otherwise.

**Formalization Note** `â_i` is the polynomial computed at the left child `a_i` (`value`), and
`(â_i)_X` is `xPart`. -/
noncomputable def Path.weight {C : Circuit F (σ ⊕ τ)} :
    {k : Fin C.size} → Path C k → FreeAlgebra F (σ ⊕ τ)
  | _, .leaf _ => 1
  | _, .addLeft _ π => π.weight
  | _, .addRight _ π => π.weight
  | _, .mulLeft _ π => π.weight
  | _, .mulRight (a := a) _ π => xPart (C.value (C.child a)) * π.weight

end Circuit

end NCQuadLB


