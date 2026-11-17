-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_IsBooleanTree
-- name    : QuantumLTF_Membership_Supplement_IsBooleanTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:34:12.791714+00:00
-- url     : https://prove2.me/theorems/ed160302-94c0-425a-b048-dbb1ad057e6a
-- title:
--   Membership-query tree with Boolean query points
-- statement:
--   A deterministic adaptive membership-query tree is **Boolean** if every point it queries, along answers in $\{\pm1\}$, lies in $\{-1,1\}^n$. Section 4 and Appendix A restrict membership queries to such points.
--
--   **Formalization Note** Children are followed only at the answers $\pm1$, as in the base `QueryTree.run` and `QueryTree.depth`.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §4, p. 39 (PDF p. 40); Theorem A.1, p. 86 (PDF p. 87)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_QueryTree

namespace QuantumLTF.Membership.Supplement

open QuantumLTF.Membership

/-- **A membership-query tree that queries only Boolean points.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §4, p. 39 (PDF p. 40): "We
further restrict the membership queries to `x ∈ {−1, 1}ⁿ`", and Theorem A.1, p. 86 (PDF p. 87). Every
point queried along the answers `±1` has all coordinates in `{−1, 1}`.

**Formalization Note.** Children are followed only at the answers `1` and `−1`, as in
`QueryTree.run` and `QueryTree.depth` for `±1`-valued functions. -/
def IsBooleanTree {n : ℕ} {α : Type} : QueryTree n α → Prop
  | .leaf _ => True
  | .query x next => (∀ i : Fin n, x i = 1 ∨ x i = -1) ∧
      IsBooleanTree (next 1) ∧ IsBooleanTree (next (-1))

end QuantumLTF.Membership.Supplement


