-- Prove2me | Definitions.Def_HybridXorLift_ParallelHybridAlg_ampl
-- name    : HybridXorLift_ParallelHybridAlg_ampl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:54.334183+00:00
-- url     : https://prove2.me/theorems/cc6a35e6-6699-4cfa-874f-7570ecdf433a
-- title:
--   Transcript amplitude $c_h(x)$
-- statement:
--   At an internal history $h$ let $|\phi_h\rangle$ be the prepared state, $O_{h,x}$ the product of the $k(h)$ controlled phase queries and $V_h$ the final unitary. For a complete-basis outcome $y$ set
--   $$
--   a_{h,y}(x) = \langle y|\, V_h O_{h,x}\, |\phi_h\rangle, \qquad c_\varnothing(x) = 1, \qquad c_{hy}(x) = c_h(x)\, a_{h,y}(x).
--   $$
--   $c_h(x)$ is the **transcript amplitude** of $h$ on input $x$: the product of the outcome amplitudes along the path, which keeps the phases a parity-sensitive argument needs.
--
--   **Formalization Note** The product is accumulated from the root down (the amplitude of the first outcome times the transcript amplitude, in the subtree, of the rest of the path), which is the same product. A list that is not a history gets amplitude $0$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §3.1, Eq. (3.1), p.11 (PDF p.13)

import Definitions.Def_HybridXorLift_ParallelHybridAlg
import Definitions.Def_HybridXorLift_decodeStep
import Definitions.Def_HybridXorLift_ParallelSub_finalState

namespace HybridXorLift

/-- The transcript amplitude `c_h(x)` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §3.1, Eq. (3.1), p.11 (PDF p.13)):
`a_{h,y}(x) = ⟨y| V_h O_{h,x} |ϕ_h⟩`, `c_∅(x) = 1` and `c_{hy}(x) = c_h(x) a_{h,y}(x)`.

**Formalization Note** The product of the outcome amplitudes along the path is accumulated from
the root down (`c_{y h'} = a_{∅,y} · c'_{h'}` for the subtree at the child `y`), which is the
same product. A list that is not a history gets amplitude `0`. -/
noncomputable def ParallelHybridAlg.ampl {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} :
    ParallelHybridAlg ι α → (ι → Bool) → List (Step ι) → ℂ
  | _, _, [] => 1
  | .halt _, _, _ :: _ => 0
  | .round k w S next, x, u :: l =>
      match decodeStep k w u with
      | some y => inner ℂ (QAlgorithms.ket y) (S.finalState x) * (next y).ampl x l
      | none => 0

end HybridXorLift


