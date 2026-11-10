-- Prove2me | Definitions.Def_MonoABPWidth_Hierarchy_simplicity
-- name    : MonoABPWidth_Hierarchy_simplicity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:16:24.8654+00:00
-- url     : https://prove2.me/theorems/368d82eb-4e37-49c0-a404-d4e3aafaeafb
-- title:
--   Relevance, pairwise nonproportionality, and simple mABPs
-- statement:
--   For a finite layered mABP $A$, write $f_{s\to v}$ and $f_{v\to t}$ for its prefix and suffix polynomials. Relevance requires both to be nonzero for every vertex. Pairwise nonproportionality requires, for distinct vertices $u,v$ in the same layer and every nonzero real $c$,
--   $$
--   f_{s\to u}\ne c f_{s\to v},\qquad f_{u\to t}\ne c f_{v\to t}.
--   $$
--   A program is simple when it is relevant, has this pairwise property, and each edge label is a constant or a multiple of one variable. This is pairwise nonproportionality separately for prefixes and suffixes; no joint linear independence is required. Zero-labelled potential edges satisfy the single-term condition and represent missing edges.
--
--   Simplicity is a conclusion of simplification and is never required of the input program in the main theorem.
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), §4.1, p.6, PDF7; Definition A.1, p.27, PDF28

import Definitions.Def_MonoABPWidth_Hierarchy_branchingProgram

namespace MonoABPWidth.Hierarchy

/-- Definition A.1(1), p.27: every vertex has nonzero prefix and suffix. -/
def MABP.Relevant {σ : Type} (A : MABP σ) : Prop :=
  ∀ (i : Fin (A.depth + 1)) (v : Fin (A.layerSize i)),
    A.prefix i v ≠ 0 ∧ A.suffix i v ≠ 0

/-- Definition A.1(2): pairwise nonproportionality, separately for prefixes and
suffixes in each layer. This does not require linear independence of the layer. -/
def MABP.Nonproportional {σ : Type} (A : MABP σ) : Prop :=
  ∀ (i : Fin (A.depth + 1)) (u v : Fin (A.layerSize i)), u ≠ v →
    ∀ c : ℝ, c ≠ 0 →
      A.prefix i u ≠ MvPolynomial.C c * A.prefix i v ∧
      A.suffix i u ≠ MvPolynomial.C c * A.suffix i v

/-- Definition A.1(3), for every potential edge, including zero labels. -/
def MABP.SingleTermEdges {σ : Type} (A : MABP σ) : Prop :=
  ∀ (e : Fin A.depth) (u : Fin (A.layerSize e.castSucc))
    (v : Fin (A.layerSize e.succ)), SingleTerm (A.label e u v).poly

/-- Definition A.1 in full; never an assumption of the main depth bound. -/
def MABP.Simple {σ : Type} (A : MABP σ) : Prop :=
  A.Relevant ∧ A.Nonproportional ∧ A.SingleTermEdges

end MonoABPWidth.Hierarchy


