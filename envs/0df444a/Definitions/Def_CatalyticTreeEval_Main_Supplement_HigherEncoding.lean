-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_Supplement_HigherEncoding
-- name    : CatalyticTreeEval_Main_Supplement_HigherEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:32:17.035203+00:00
-- url     : https://prove2.me/theorems/9e00d4b8-c31c-4073-8121-fddc4e6b98e3
-- title:
--   Definition 2.2 — complete ordered variable-arity tree evaluation
-- statement:
--   For integers $r\ge2$, $\ell\ge1$ and $h\ge1$, a complete ordered $r$-ary tree of height $h$ has an arbitrary $\ell$-bit label at each leaf and an arbitrary function from $r$ labels to one label at each internal node. Its value is obtained by applying each gate to its children's values. The required output is the whole root label.
--
--   The serialization lists each gate's full truth table in lexicographic argument order, followed by its children in position order; leaves contribute their labels. Thus
--   $$\operatorname{value}(\operatorname{node}(f,T))=f\bigl((\operatorname{value}(T_i))_{i<r}\bigr).$$
--   Height and label length use the published binary headers; arity is provided in the framework header. At $r=2$, the embedding from the published binary tree has exactly the same payload and headers. Full truth tables remain input data, without an oracle that reads them at unit cost. This is the source model needed for the higher-arity companion theorem.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Definition 2.2, printed p. 5 (PDF p. 7); §4.5 input access, printed pp. 28–29 (PDF pp. 30–31)

import Definitions.Def_CatalyticTreeEval_Main_Encoding

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

/-- Ordered r-tuples in lexicographic order, first coordinate most significant. -/
def tuples (r l : ℕ) : List (Fin r → Label l) :=
  (List.finRange ((2 ^ l) ^ r)).map fun a i =>
    ⟨(a.val / (2 ^ l) ^ (r - 1 - i.val)) % (2 ^ l), Nat.mod_lt _ (by positivity)⟩

/-- The complete ordered r-ary tree; no promise is made about node functions. -/
inductive ArityTree (r l : ℕ) : ℕ → Type
  | leaf : Label l → ArityTree r l 0
  | node {h : ℕ} : ((Fin r → Label l) → Label l) →
      (Fin r → ArityTree r l h) → ArityTree r l (h + 1)

def ArityTree.value {r l h : ℕ} : ArityTree r l h → Label l
  | .leaf v => v
  | .node f children => f (fun i => (children i).value)

def arityTableCode {r l : ℕ} (f : (Fin r → Label l) → Label l) : List Bool :=
  (tuples r l).flatMap fun y => bits l (f y).val

def ArityTree.payload {r l h : ℕ} : ArityTree r l h → List Bool
  | .leaf v => bits l v.val
  | .node f children => arityTableCode f ++
      (List.finRange r).flatMap (fun i => (children i).payload)

/-- At r=2 the payload and h,l headers agree with the binary encoding.
The arity is supplied in the separate framework parameter header. -/
def ArityTree.encode {r l h : ℕ} (I : ArityTree r l h) : List Bool :=
  natCode h ++ natCode l ++ I.payload

/-- Explicit embedding for checking agreement with the published binary model. -/
def fromBinary {l h : ℕ} : Tree l h → ArityTree 2 l h
  | .leaf v => .leaf v
  | .node f a b => .node (fun x => f (x 0) (x 1))
      (fun i => if i = 0 then fromBinary a else fromBinary b)

end CatalyticTreeEval.Main.Supplement


