-- Prove2me | Definitions.Def_PlanarDFVSKernel_rho
-- name    : PlanarDFVSKernel_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:59.937308+00:00
-- url     : https://prove2.me/theorems/5eb38dee-def6-4b6d-945c-43cca08a41b5
-- title:
--   $\rho(J)$ and source shores
-- statement:
--   In a digraph $J$ one may add the reverse $v\to u$ of any arc $u\to v$, keeping the original arc. $\rho(J)$ is the minimum number of such additions that make $J$ strongly connected (finite when $J$ is weakly connected). A **source shore** is a nonempty proper vertex set with no entering arc.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §5.2, p.20 (PDF 21); §2.3, p.7 (PDF 8)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- `J` plus the reverses of the arcs in `A` is strongly connected (Sheng, Xiao, *A Polynomial
Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256
75cfca8f…), §5.2, p.20 (PDF 21)): "we may add the reverse v → u of any arc u → v of J, while
retaining the original arc." -/
def RevAugStrong {n m : ℕ} (J : Graph n m) (A : Finset (Fin m)) : Prop :=
  ∀ u v, Relation.ReflTransGen (fun a b => ∃ e, (J.tail e = a ∧ J.head e = b) ∨
    (e ∈ A ∧ J.head e = a ∧ J.tail e = b)) u v

/-- **`ρ(J)`** (ibid., p.20 (PDF 21)): "Let ρ(J) be the minimum number of such additions needed to
make J strongly connected." The infimum over arc sets `A` whose reverses make `J` strongly
connected of `|A|`.

**Formalization Note** Adding the reverse of the same arc twice adds nothing, so additions are a
set of arcs. For a weakly connected `J` the set of all arcs qualifies ("This minimum is finite"),
so the infimum is attained; for a `J` that is not weakly connected and has at least two vertices
no set qualifies and `sInf ∅ = 0` (not used: Lemma 5.3 assumes weak connectivity). -/
noncomputable def rho {n m : ℕ} (J : Graph n m) : ℕ :=
  sInf {r | ∃ A : Finset (Fin m), A.card = r ∧ RevAugStrong J A}

/-- **A source shore** (ibid., §2.3, p.7 (PDF 8), and p.20 (PDF 21)): "Recall that a source shore is
a nonempty proper vertex set with no entering arc." -/
def IsSourceShore {n m : ℕ} (J : Graph n m) (U : Set (Fin n)) : Prop :=
  U.Nonempty ∧ U ≠ Set.univ ∧ ∀ e, J.head e ∈ U → J.tail e ∈ U

end PlanarDFVSKernel


