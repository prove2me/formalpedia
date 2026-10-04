-- Prove2me | Definitions.Def_ResourceScheduling_Graph_ReductionProgram
-- name    : ResourceScheduling_Graph_ReductionProgram
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T15:41:46.099995+00:00
-- url     : https://prove2.me/theorems/fc410ec4-d831-4e4c-b835-c8778cc21e7b
-- title:
--   ResourceScheduling Graph ReductionProgram
-- statement:
--   A fixed seventeen-register program for the original reduction: unary parsing, matrix validation, non-edge counting, and lexicographically ordered unary resource emission.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMBudget

set_option autoImplicit false
namespace ResourceScheduling.Graph

inductive GraphReg where
  | t | n | good | i | j | k | c0 | c1 | c2 | count | index | bitA | bitB | delta | aux | size | num
  deriving DecidableEq

def GraphReg.number : GraphReg → Fin 17
  | .t => 0 | .n => 1 | .good => 2 | .i => 3 | .j => 4 | .k => 5
  | .c0 => 6 | .c1 => 7 | .c2 => 8 | .count => 9 | .index => 10
  | .bitA => 11 | .bitB => 12 | .delta => 13 | .aux => 14 | .size => 15 | .num => 16

instance : Finite GraphReg := Finite.of_injective GraphReg.number (by
  intro a b h; cases a <;> cases b <;> simp [GraphReg.number] at h ⊢)
noncomputable instance : Fintype GraphReg := Fintype.ofFinite _

namespace GraphProgram
open GraphReg
abbrev Code := RAMCode GraphReg
def block : List Code → Code := List.foldr RAMCode.seq .skip
def one (r : GraphReg) : Code := block [.zero r, .inc r]
def forN (counter idx : GraphReg) (hc : n ≠ counter) (body : Code) : Code :=
  block [.copy n counter hc, .zero idx, .loop counter (.seq body (.inc idx))]

def read (a b dst : GraphReg) (h : b ≠ index) : Code :=
  block [.mul a n index (by decide), .add b index h, .bit index dst]

def ifNonEdge (p : Code) : Code :=
  block [.sub j i delta,
    .branch delta (block [read i j bitA (by decide), .branch bitA .skip p]) .skip]

def ifEq (a b : GraphReg) (p q : Code) : Code :=
  block [.sub a b delta, .branch delta q
    (block [.sub b a aux, .branch aux q p])]

def validateCell : Code := block [read i j bitA (by decide),
  .branch bitA (block [read j i bitB (by decide), .branch bitB .skip (.zero good)]) .skip]

def validateRow : Code := block [read i i bitA (by decide),
  .branch bitA (.zero good) .skip, forN c1 j (by decide) validateCell]

def validate : Code := forN c0 i (by decide) validateRow

def countEdges : Code := block [.zero count,
  forN c0 i (by decide) (forN c1 j (by decide) (ifNonEdge (.inc count)))]

def emitCell : Code := block [.zero num,
  ifEq k i (.inc num) (ifEq k j (.inc num) .skip), .emit num]

def emitRows : Code := forN c0 i (by decide)
  (forN c1 j (by decide) (ifNonEdge (forN c2 k (by decide) emitCell)))

def emit : Code := block [.zero num, .inc num, .inc num, .emit num,
  .zero num, .inc num, .emit num, .emit n, .emit count, emitRows, .emit t]

def prepare : Code := block [.parse t good (by decide), .copy t n (by decide),
  .add t n (by decide), .add t n (by decide), .mul n n size (by decide),
  .length aux, .sub aux size delta, .branch delta (.zero good) .skip,
  .sub size aux delta, .branch delta (.zero good) .skip]

def program : Code := block [prepare, validate, .branch good (block [countEdges, emit]) .skip]

end GraphProgram
end ResourceScheduling.Graph


