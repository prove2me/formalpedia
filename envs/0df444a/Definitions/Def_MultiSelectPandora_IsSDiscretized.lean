-- Prove2me | Definitions.Def_MultiSelectPandora_IsSDiscretized
-- name    : MultiSelectPandora_IsSDiscretized
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:23:23.218709+00:00
-- url     : https://prove2.me/theorems/4604594b-0dc4-4e1f-9e0c-702df9655ab2
-- title:
--   S-discretized policies
-- statement:
--   A policy is S-discretized when its decisions depend on the opened values only through $w_1,\dots,w_n$: two histories with the same actions, whose opened positions show the same $w$, get the same next action.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.20, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_DPPolicy
import Definitions.Def_MultiSelectPandora_wVal

namespace MultiSelectPandora

/-- **S-discretized policies.** Beyhaghi–Han–Luqman manuscript, Definition 3.20, p.14 (PDF p.15): "its decisions depend on the
opened values only through `w_1, …, w_n`".

**Formalization Note.** Two histories with the same actions, whose opened positions show the same `w`, get the same next
action. Out-of-range positions are compared as numbers; they never occur in play. -/
def IsSDiscretized (I : Inst) (k : ℕ) (ε : ℝ) (π : DPPolicy I.n) : Prop :=
  ∀ h h' : List (DPAct I.n × ℕ),
    List.Forall₂ (fun e e' => e.1 = e'.1 ∧
      match e.1 with
      | .openBox i => e.2 = e'.2 ∨ ∃ (hj : e.2 < I.s i) (hj' : e'.2 < I.s i),
          wVal I k ε i ⟨e.2, hj⟩ = wVal I k ε i ⟨e'.2, hj'⟩
      | _ => e.2 = e'.2) h h' →
    π h = π h'

end MultiSelectPandora


