-- Prove2me | Definitions.Def_CoDecompFO_Fib
-- name    : CoDecompFO_Fib
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:46:55.357281+00:00
-- url     : https://prove2.me/theorems/7151bfc1-d850-49d3-8bdf-e8e6f618fbe2
-- title:
--   The pullback of $\sigma$-structures
-- statement:
--   Given maps $g:A\to K$ and $h:B\to K$ from $\sigma$-structures $A,B$, the **pullback** $A\times_K B$ has point set
--   $$
--   \{(x,y)\in A\times B : g(x)=h(y)\},
--   $$
--   and a relation holds of a tuple of pairs exactly when it holds of the tuple of first coordinates in $A$ and of the tuple of second coordinates in $B$.
--
--   This is the operation by which co-decompositions build large structures from small ones.
--
--   **Formalization Note** $g$ and $h$ are plain maps, because the relations of the pullback do not refer to $K$. For the maps of a co-decomposition they are homomorphisms.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), ¶2.5, p.6

import Mathlib
import Definitions.Def_CoDecompFO_Sig

set_option autoImplicit false

namespace CoDecompFO

/-- The point set of the **pullback** (Bumpus et al., arXiv:2611.04658, held file sha256 d550d7af…,
¶2.5, p.6): "G ×_K H := {(x,y) ∈ G × H | g(x) = h(y)}". -/
@[ext] structure Fib {A B K : Type} (g : A → K) (h : B → K) : Type where
  /-- The first coordinate. -/
  fst : A
  /-- The second coordinate. -/
  snd : B
  /-- The two coordinates agree in `K`. -/
  eq : g fst = h snd

/-- The **pullback of σ-structures** (¶2.5, p.6): a relation holds of a tuple of pairs iff it holds
of the first coordinates and of the second coordinates.

**Formalization Note** `g` and `h` are plain maps. The relations do not refer to `K`, so no
structure on `K` and no homomorphism condition is needed to form the pullback. -/
instance Fib.structure (σ : Sig) {A B K : Type} [σ.lang.Structure A] [σ.lang.Structure B]
    (g : A → K) (h : B → K) : σ.lang.Structure (Fib g h) :=
  σ.structureOf (fun i args =>
    σ.holds i (fun j => (args j).fst) ∧ σ.holds i (fun j => (args j).snd))

end CoDecompFO


