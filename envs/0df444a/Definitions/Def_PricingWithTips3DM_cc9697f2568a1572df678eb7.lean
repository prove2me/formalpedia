-- Prove2me | Definitions.Def_PricingWithTips3DM_cc9697f2568a1572df678eb7
-- name    : PricingWithTips3DM_cc9697f2568a1572df678eb7
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:19:11.077018+00:00
-- url     : https://prove2.me/theorems/883d30d6-ba75-4a75-9291-f1ee95cad1f5
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.Basic
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_87dc7ae0ede24fbf3bba7914
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# General CLIQUE encoding primitives

The instance and certificate grammars use disjoint leading markers and unary
natural numbers.  Every structural role has its own alphabet constructor.
-/

namespace CLRS
namespace Chapter34

/-- The unambiguous alphabet shared by general CLIQUE instances and their
certificates. -/
inductive CliqueSym
  | instanceMark
  | certificateMark
  | tick
  | fieldSep
  | edgeMark
  | vertexMark
  | pairSep
  | recordEnd
  deriving DecidableEq, Repr, Fintype

/-- Prepend a unary natural number to a fixed suffix. -/
def prependCliqueTicks : Nat → List CliqueSym → List CliqueSym
  | 0, suffix => suffix
  | count + 1, suffix => .tick :: prependCliqueTicks count suffix

/-- Unary-prefix construction commutes with extending its suffix. -/
theorem prependCliqueTicks_append (count : Nat) (suffix tail : List CliqueSym) :
    prependCliqueTicks count suffix ++ tail =
      prependCliqueTicks count (suffix ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prependCliqueTicks, ih]

/-- Encode one normalized edge record with unary endpoints. -/
def encodeCliqueEdge (edge : Nat × Nat) : List CliqueSym :=
  .edgeMark :: prependCliqueTicks edge.1
    (.pairSep :: prependCliqueTicks edge.2 [.recordEnd])

/-- Encode a graph-plus-{lit}`k` instance in the canonical instance grammar. -/
def encodeCliqueInstance (I : CliqueInstance) : List CliqueSym :=
  .instanceMark :: prependCliqueTicks I.vertexCount
    (.fieldSep :: prependCliqueTicks I.targetSize
      (.fieldSep :: I.edges.flatMap encodeCliqueEdge))

/-- Encode one selected vertex record. -/
def encodeCliqueVertex (vertex : Nat) : List CliqueSym :=
  .vertexMark :: prependCliqueTicks vertex [.recordEnd]

/-- Encode a list of selected vertices in the certificate grammar. -/
def encodeCliqueCertificate (vertices : List Nat) : List CliqueSym :=
  .certificateMark :: vertices.flatMap encodeCliqueVertex

/-- Prepending unary ticks adds exactly the represented natural number. -/
@[simp] theorem prependCliqueTicks_length (count : Nat) (suffix : List CliqueSym) :
    (prependCliqueTicks count suffix).length = count + suffix.length := by
  induction count with
  | zero => simp [prependCliqueTicks]
  | succ count ih =>
      simp only [prependCliqueTicks, List.length_cons, ih]
      omega

/-- The encoded length of one edge record. -/
@[simp] theorem encodeCliqueEdge_length (edge : Nat × Nat) :
    (encodeCliqueEdge edge).length = edge.1 + edge.2 + 3 := by
  simp [encodeCliqueEdge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The encoded length of one certificate vertex record. -/
@[simp] theorem encodeCliqueVertex_length (vertex : Nat) :
    (encodeCliqueVertex vertex).length = vertex + 2 := by
  simp [encodeCliqueVertex]

end Chapter34
end CLRS


