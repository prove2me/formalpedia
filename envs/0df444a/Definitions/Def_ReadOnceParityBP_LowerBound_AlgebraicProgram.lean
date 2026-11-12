-- Prove2me | Definitions.Def_ReadOnceParityBP_LowerBound_AlgebraicProgram
-- name    : ReadOnceParityBP_LowerBound_AlgebraicProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:24:49.836206+00:00
-- url     : https://prove2.me/theorems/e76c6d13-0038-4e08-a9d2-496749b74938
-- title:
--   Syntactically multilinear ABPs and polynomial evaluation
-- statement:
--   An algebraic edge label is a field constant or an affine polynomial a+bXᵢ in one syntactically designated variable i. A syntactically multilinear algebraic branching program P is a finite acyclic multigraph in which each variable is designated on at most one edge of each source-to-target path. The polynomial it computes is
--
--   $$P_{\rm poly}=\sum_{p:s\leadsto t}\prod_{e\in p}\operatorname{label}(e).$$
--
--   The definition also provides IsMultilinear(f), meaning that every exponent in each supported monomial of f is at most one, and boolOf(f), the evaluation of a polynomial over F₂ on Boolean assignments. These are genuine formal polynomials, without the quotient relation Xᵢ²=Xᵢ. Affine labels include 1+Xᵢ, needed to encode negation. Syntactic labels with zero slope still designate their written variable; a constant can instead use the constant constructor. The model is parameterized by the coefficient type, with the paper's ABPs instantiated at F₂.
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Definition 2.1, pp.3–4, and §2.1 p.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_LabelledDAG

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Edge labels of an algebraic branching program over a field `F` (Definition 2.1): a
constant `c ∈ F`, or a linear function `a + b·x_i` in a single variable `x_i`. Arbitrary
linear forms in several variables are not labels. -/
inductive ALabel (ι F : Type) where
  | const (c : F)
  | lin (i : ι) (a b : F)

namespace ALabel

variable {ι F : Type}

/-- The variable a label is written in, if any (a syntactic notion). -/
def var? : ALabel ι F → Option ι
  | const _ => none
  | lin i _ _ => some i

/-- The polynomial a label denotes. -/
noncomputable def poly [CommSemiring F] : ALabel ι F → MvPolynomial ι F
  | const c => MvPolynomial.C c
  | lin i a b => MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X i

end ALabel

/-- Volk, Definition 2.1 (p. 3): a syntactically multilinear algebraic branching program (ABP)
with coefficients in `F` (the paper takes `F = 𝔽₂`). A finite directed acyclic multigraph
with source `s` and target `t`, each edge labelled by a constant or a linear function in a
single variable, such that on every `s → t` path every variable appears at most once. -/
structure SMABP (ι F : Type) extends LabelledDAG (ALabel ι F) where
  readOnce : ∀ p : List (Fin numE), IsWalk graph.tail graph.head p s t →
    (p.filterMap fun e => (label e).var?).Nodup

namespace SMABP

variable {ι F : Type} [CommSemiring F]

/-- The polynomial computed by the program: the sum over all `s → t` paths of the product of
the edge labels on the path (the set of paths is finite since the graph is acyclic). -/
noncomputable def poly (P : SMABP ι F) : MvPolynomial ι F :=
  ∑ᶠ (p : List (Fin P.numE)) (_ : IsWalk P.src P.tgt p P.s P.t),
    (p.map fun e => (P.label e).poly).prod

end SMABP

/-- A polynomial is multilinear if every variable has exponent at most `1` in every monomial. -/
def IsMultilinear {ι F : Type} [CommSemiring F] (f : MvPolynomial ι F) : Prop :=
  ∀ m ∈ f.support, ∀ i, m i ≤ 1

/-- Volk, §2.1 (p. 5): for `f ∈ 𝔽₂[x]`, the Boolean function `f_bool` that `f` represents,
obtained by evaluating `f` at points of `{0,1}^ι ⊆ 𝔽₂^ι`. -/
noncomputable def boolOf {ι : Type} (f : MvPolynomial ι (ZMod 2)) (a : ι → Bool) : Bool :=
  decide (MvPolynomial.eval (fun i => if a i then (1 : ZMod 2) else 0) f = 1)

end ReadOnceParityBP.LowerBound


