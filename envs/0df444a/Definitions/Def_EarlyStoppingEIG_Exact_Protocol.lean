-- Prove2me | Definitions.Def_EarlyStoppingEIG_Exact_Protocol
-- name    : EarlyStoppingEIG_Exact_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:03.618592+00:00
-- url     : https://prove2.me/theorems/f4028ba6-d4ea-4ddf-8abe-3feb230237a0
-- title:
--   Binary broadcast sending and actual halt transitions (corrected at t=0)
-- statement:
--   An active sender signs its private input in round one. Every active party in rounds $2,\ldots,t+1$ signs its complete previous-round receipt list. A valid direct message is stored, and each own signed message is stored as its own receipt. Malformed packets are ignored; delivery order selects the first valid packet if a faulty channel sends several.
--
--   $$R=t+1\quad\text{or}\quad 2\le R<t+1\text{ and the local cover test accepts}.$$
--
--   At final stopping nonsenders use horizon $R$; early round-two stopping uses the direct sender bit (default zero); later early stopping uses horizon $R-1$. The sender outputs its private input. Stopping records an actual halt and disables future honest sends.
--
--   **Correction.** For $t=0$, all parties output and halt at the end of round one. The printed loop omits this case: $n=2,t=f=0$ with input 1 and reliable honest delivery never enters the output branch. For $t>0$ the printed rules are retained.
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), §3.2, pp.17–18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_Output
import Definitions.Def_EarlyStoppingEIG_Exact_Cover

namespace EarlyStoppingEIG.Exact

def directBit (P : Parameters) (v : LocalView P) : Bool :=
  match v.receipt 1 P.sender with
  | some (.sig _ _ (.atom 1)) => true
  | _ => false

/-- The only branch using the private input is the sender's branch. -/
noncomputable def stoppingBit (P : Parameters) (b : Bool) (i : Party P)
    (v : LocalView P) (r : ℕ) : Bool :=
  if i = P.sender then b else
  if P.t = 0 ∨ (r = 2 ∧ r < P.t + 1) then directBit P v else
  output P i v (if r = P.t + 1 then r else r - 1)

/-- ΠBB's end-of-round transition. The r=1,t=0 branch is the documented
correction; for t>0 these are exactly the printed stopping rules, pp.17–18. -/
noncomputable def closeLocal (P : Parameters) (b : Bool) (i : Party P)
    (r : ℕ) (v : LocalView P) : LocalView P := by
  classical
  exact if v.halt.isSome then v else
    if (r = 1 ∧ P.t = 0) ∨
      (2 ≤ r ∧ r ≤ P.t + 1 ∧ (r = P.t + 1 ∨ coverAccepts P i v r))
    then { v with halt := some (r, stoppingBit P b i v r) } else v

def RequiredToSend (P : Parameters) (i : Party P) (v : LocalView P) (r : ℕ) : Prop :=
  v.halt = none ∧ ((r = 1 ∧ i = P.sender) ∨ (2 ≤ r ∧ r ≤ P.t + 1))

def honestPayload (P : Parameters) (b : Bool) (i : Party P)
    (v : LocalView P) (r : ℕ) : Message P :=
  if r = 1 ∧ i = P.sender then bitPayload b else
  .tuple [.atom r, .tuple (List.ofFn (fun j : Party P => encodeReceipt (v.receipt (r - 1) j)))]

def honestSigned (P : Parameters) (b : Bool) (i : Party P)
    (v : LocalView P) (r nonce : ℕ) : Message P :=
  .sig i nonce (honestPayload P b i v r)

def recordOwn (P : Parameters) (i : Party P) (r : ℕ) (m : Message P)
    (v : LocalView P) : LocalView P :=
  { v with own := Function.update v.own r (some m)
           receipt := Function.update v.receipt r (Function.update (v.receipt r) i (some m)) }

/-- The first valid channel message for this author and round is stored.
Malformed wire terms do not create receipts or nested signed evidence.
Own signed messages are already present before delivery. -/
noncomputable def receive (P : Parameters) (j : Party P) (r : ℕ) (m : Message P)
    (v : LocalView P) : LocalView P := by
  classical
  exact if v.halt = none ∧ v.receipt r j = none ∧ WellFormed P r j m then
    { v with receipt := Function.update v.receipt r (Function.update (v.receipt r) j (some m)) }
    else v

end EarlyStoppingEIG.Exact


