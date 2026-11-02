-- Prove2me | Definitions.Def_StackProgPortLift
-- name    : StackProgPortLift
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T20:33:15.790869+00:00
-- url     : https://prove2.me/theorems/57e73515-f3ed-4273-ab91-dc8cf6f0e5c6
-- title:
--   Computable lifting of finite stack programs to selected ports
-- statement:
--   A structured stack program operating on a set of local stack ports can be embedded into a larger collection of ports. The computable lift takes an injective local-to-global port map and an explicit inverse decoder: it applies each action to the selected ports and leaves other ports unchanged, while preserving the sequence, branch, and loop structure.
--
--   The module also provides mathematical projection and write-back operations for specifying the lifted execution. Exact execution preservation is a separate theorem. This shared implementation device supports the binary-encoding constructions in the complexity-theory missions.
-- source:
--   Supporting stack-machine construction for the formalization of Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. This port lift is an implementation device added to the formalization, not a claim made in the paper.

import Mathlib
import Definitions.Def_CookPvsNP_StackProgram

open CookPvsNP

namespace StackProgPortLift

/-- Project a larger stack store to the ports selected by an embedding. -/
def project {K L A : Type} (r : K ↪ L) (s : L → List A) : K → List A :=
  fun k ↦ s (r k)

/-- Replace exactly the embedded ports, leaving all other stack contents intact. -/
noncomputable def write {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) : L → List A := by
  classical
  exact fun l ↦ if h : ∃ k, r k = l then t (Classical.choose h) else s l

/-- Lift one action, projecting read heads and keeping every unselected port. -/
noncomputable def liftAct {K L A : Type} (r : K ↪ L)
    (f : (K → Option A) → K → StackAct A) : (L → Option A) → L → StackAct A := by
  classical
  exact fun h l ↦ if hex : ∃ k, r k = l then f (fun k ↦ h (r k)) (Classical.choose hex) else .keep

/-- Lift a structured stack program along an injective port map. -/
noncomputable def liftProg {K L A : Type} (r : K ↪ L) : StackProg K A → StackProg L A
  | .act f => .act (liftAct r f)
  | .seq p q => .seq (liftProg r p) (liftProg r q)
  | .branch test p q => .branch (fun h ↦ test (fun k ↦ h (r k))) (liftProg r p) (liftProg r q)
  | .loop test p => .loop (fun h ↦ test (fun k ↦ h (r k))) (liftProg r p)

/-- Computable action lift when an explicit port decoder is supplied. -/
def liftActC {K L A : Type} (r : K ↪ L) (decode : L → Option K)
    (f : (K → Option A) → K → StackAct A) : (L → Option A) → L → StackAct A :=
  fun h l ↦ match decode l with
    | none => .keep
    | some k => f (fun j ↦ h (r j)) k

/-- Computable program lift when an explicit port decoder is supplied. -/
def liftProgC {K L A : Type} (r : K ↪ L) (decode : L → Option K) :
    StackProg K A → StackProg L A
  | .act f => .act (liftActC r decode f)
  | .seq p q => .seq (liftProgC r decode p) (liftProgC r decode q)
  | .branch test p q => .branch (fun h ↦ test (fun k ↦ h (r k))) (liftProgC r decode p) (liftProgC r decode q)
  | .loop test p => .loop (fun h ↦ test (fun k ↦ h (r k))) (liftProgC r decode p)


end StackProgPortLift


