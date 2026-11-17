-- Prove2me | Definitions.Def_CoRSuccGap_Supplement_TermSize
-- name    : CoRSuccGap_Supplement_TermSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:37:57.955477+00:00
-- url     : https://prove2.me/theorems/ea58f1bd-ca75-403c-a544-36f73728ff77
-- title:
--   Total syntax-tree node count $|T|$ for CoR terms
-- statement:
--   The **total node count** $|T|$ of a CoR term counts every node in its syntax tree. Each input or constant leaf contributes one; complement and converse contribute one plus the size of their child; and union, intersection and composition contribute one plus the sizes of both children.
--
--   Repeated occurrences of an identical subterm remain distinct nodes. Thus this statistic is neither the number of composition occurrences nor the number of distinct gates in a circuit DAG. It is the resource bounded on both sides in Theorem 6.3.
-- source:
--   Uezato--Nakamura, arXiv:2609.26778 (held version, sha256 5ad6337d...), Section 2.3 p.16 (PDF 18), Theorem 6.3 p.34 (PDF 36)

import Definitions.Def_CoRSuccGap_Term

set_option autoImplicit false

namespace CoRSuccGap
namespace Supplement

/-!
# Total syntax-tree size of a CoR term

Uezato--Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the
Calculus of Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Section 2.3,
p.16 (PDF 18), and Theorem 6.3, p.34 (PDF 36).

Every leaf contributes one node, a unary constructor contributes one plus its subtree, and a
binary constructor contributes one plus both subtrees.  This is tree size: repeated subterms are
counted repeatedly and are not shared as circuit gates.
-/

namespace Term

variable {σ : Type*}

/-- Total number `|T|` of nodes in the syntax tree of a CoR term. -/
def numNodes : CoRSuccGap.Term σ → ℕ
  | .rel _ => 1
  | .zero => 1
  | .one => 1
  | .id => 1
  | .union T U => numNodes T + numNodes U + 1
  | .inter T U => numNodes T + numNodes U + 1
  | .compl T => numNodes T + 1
  | .conv T => numNodes T + 1
  | .comp T U => numNodes T + numNodes U + 1

end Term

end Supplement
end CoRSuccGap


