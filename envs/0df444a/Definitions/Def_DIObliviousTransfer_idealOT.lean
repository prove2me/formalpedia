-- Prove2me | Definitions.Def_DIObliviousTransfer_idealOT
-- name    : DIObliviousTransfer_idealOT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:05:35.864988+00:00
-- url     : https://prove2.me/theorems/0a698e3a-cda5-4fd6-aa82-652a021d8c61
-- title:
--   Ideal one-bit oblivious transfer (Definition 7)
-- statement:
--   The sender Alice inputs $(S_0,S_1)\in\{0,1\}^2$ and the receiver Bob inputs $d\in\{0,1\}$. The outputs are $(\varnothing,S_d)$. The simulator may abort globally at any time before honest delivery, and then every honest party receives $\perp$. After valid inputs, the corrupt party's prescribed output is released to the simulator first, and the honest output is delivered on the simulator's go-ahead. With both parties honest the outputs are delivered at once.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Definition 7, p.19

import Mathlib
import Definitions.Def_DIObliviousTransfer_Protocol

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), Definition 7, p.19.

"For an ordered sender/receiver pair, ideal(OT) has `I_S = {0, 1}²`, `I_R = {0, 1}`,
`((S₀, S₁), d) ↦ (∅, S_d)`. `⊥` is not an input. The simulator may issue a global abort at any
time before honest delivery, including before corrupt input; then every honest party receives `⊥`
and the call terminates. After valid inputs, release the corrupt prescribed output to the
simulator first. For the honest-party set `H`, subsequently deliver `out_H = ⊥_H` if abort,
`(∅, S_d)|_H` otherwise."

**Formalization Note** (decision D10). Alice (party `true`) is the sender with input the two bits
`[S₀, S₁]`, Bob the receiver with input `[d]`. Outputs: Alice `∅` is `some []`, Bob `some [S_d]`,
`⊥` is `none`. Adversary message `[true]` is the global abort; the empty message delivers. With
both parties honest the outputs are delivered at once. Inputs that are not valid are ignored.
-/

/-- The state of ideal OT. -/
structure OTSt where
  H : Option Bool
  s : Option (Bool × Bool)
  d : Option Bool
  released : Bool
  done : Bool

/-- Release after both inputs: corrupt output to the simulator first, or direct delivery when
both parties are honest. -/
def OTSt.release (st : OTSt) : OTSt × List FOut :=
  match st.s, st.d, st.released with
  | some (s0, s1), some d, false =>
    match st.H with
    | none => ({ st with released := true, done := true },
        [.party true (some []), .party false (some [if d then s1 else s0])])
    | some true => ({ st with released := true }, [.adv [if d then s1 else s0]])
    | some false => ({ st with released := true }, [.adv []])
  | _, _, _ => (st, [])

/-- **Definition 7**, the ideal functionality for one-bit oblivious transfer. -/
def idealOT : Func where
  St := OTSt
  init := fun _ H => ⟨H, none, none, false, false⟩
  step := fun st e =>
    if st.done then (st, []) else
    match e with
    | .adv x =>
      if x = [true] then ({ st with done := true }, [.party true none, .party false none])
      else if x = [] ∧ st.released then
        match st.H, st.s, st.d with
        | some true, _, _ => ({ st with done := true }, [.party true (some [])])
        | some false, some (s0, s1), some d =>
            ({ st with done := true }, [.party false (some [if d then s1 else s0])])
        | _, _, _ => (st, [])
      else (st, [])
    | .party true x =>
      match x, st.s with
      | [s0, s1], none => OTSt.release { st with s := some (s0, s1) }
      | _, _ => (st, [])
    | .party false x =>
      match x, st.d with
      | [d], none => OTSt.release { st with d := some d }
      | _, _ => (st, [])
  validA := fun _ => {x | x.length = 2}
  validB := fun _ => {x | x.length = 1}

end DIObliviousTransfer


