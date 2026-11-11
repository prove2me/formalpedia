-- Prove2me | Definitions.Def_DecDynMatch_exec
-- name    : DecDynMatch_exec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:58:11.796403+00:00
-- url     : https://prove2.me/theorems/6861be48-d1f7-4d56-bc51-c4421b21adf1
-- title:
--   The execution of SC-DA on an instance and the realized matching $M_t$
-- statement:
--   Fix an instance and a replay rule $F$. The **execution** is the deterministic run of the protocol: each player $i$ starts in the initial state at its entry round $b_i$ and, in every round $t$ in which it is active, applies the round-start checks, proposes to $\textsf{SelectArm}$, and applies feedback. Each arm accepts its most preferred proposer among the active players proposing to it and rejects the others; no other information is exchanged. The accepted pairs form the **realized matching** $M_t$.
--
--   The definition provides the state $\textsf{pre}_t(i)$ before round $t$, the round-start state $\textsf{cur}_t(i)$, the proposal $\textsf{prop}_t(i)$, acceptance, $M_t$, and the state $\textsf{post}_t(i)$ after round $t$.
--
--   **Formalization Note** The run is defined by recursion on $t$ for all players at once; inactive players' states are computed but never affect active ones, because acceptance compares only active proposers and a player is reset at its entry round.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), §2.2, p.4; Algorithm 1, p.6; execution conventions, p.14

import Mathlib
import Definitions.Def_DecDynMatch_roundStart
import Definitions.Def_DecDynMatch_selectArm
import Definitions.Def_DecDynMatch_feedback

namespace DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- Player `i` is accepted in round `t` when the active players propose `x`: it is active, and
every other active player proposing to the same arm is less preferred by that arm (§2.2, p.4:
"Each arm accepts its most preferred current proposer"). -/
def acceptedBy (I : Instance K ι) (t : ℕ) (x : ι → Fin K) (i : ι) : Prop :=
  i ∈ active I t ∧ ∀ j ∈ active I t, j ≠ i → x j = x i → I.π (x i) j < I.π (x i) i

open Classical in
/-- One global round `t`: from the profile `pre` of states before round `t`, every player applies
the round-start checks, proposes, observes acceptance among the active proposers, and applies
feedback. Returns the profile of states after round `t`. -/
noncomputable def stepProfile (I : Instance K ι) (F : ℕ → ℕ) (t : ℕ) (pre : ι → LState K) :
    ι → LState K :=
  fun i =>
    let x : ι → Fin K := fun j => selectArm I j (roundStart (pre j))
    feedback I F (roundStart (pre i)) (x i) (decide (acceptedBy I t x i))

/-- **The execution of SC-DA with replay rule `F` on instance `I`.** J. Chen, M. Gao, Z. Zhang,
*Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), §2.2,
p.4 ("Upon entry at round bᵢ, player i initializes its local state according to the protocol …
Active players' local states are not affected by population changes"), and App. A, p.14 ("All
executions below follow Algorithm 1 from its prescribed initialization, with the replay update in
Equation (13)").

`pre F I t i` is player `i`'s state before round `t` (before the round-start checks): the initial
state `init I` in every round `t ≤ bᵢ`, and the state after round `t − 1` afterwards.

**Formalization Note.** States of inactive players are computed but never influence active ones:
acceptance only compares active proposers, and a player is reset to `init I` at its entry round
`bᵢ` (each player enters once; after `dᵢ` it is never active again). -/
noncomputable def pre (F : ℕ → ℕ) (I : Instance K ι) : ℕ → ι → LState K
  | 0 => fun _ => init I
  | t + 1 => fun i => if t + 1 ≤ I.b i then init I else stepProfile I F t (pre F I t) i

/-- Round-start state of player `i` in round `t` (after the round-start checks, before proposals;
p.14: "Round-start states in the proofs are taken after these checks and before proposals"). -/
noncomputable def cur (F : ℕ → ℕ) (I : Instance K ι) (t : ℕ) (i : ι) : LState K :=
  roundStart (pre F I t i)

/-- The arm player `i` proposes to in round `t`. -/
noncomputable def prop (F : ℕ → ℕ) (I : Instance K ι) (t : ℕ) (i : ι) : Fin K :=
  selectArm I i (cur F I t i)

/-- Player `i` is active and accepted in round `t`. -/
def Accepts (F : ℕ → ℕ) (I : Instance K ι) (t : ℕ) (i : ι) : Prop :=
  acceptedBy I t (prop F I t) i

open Classical in
/-- The realized matching `Mₜ` (§2.2, p.4: "The accepted player-arm pairs form the realized
matching Mₜ"): `M F I t i = some (prop F I t i)` if `i` is accepted in round `t`, else `none`. -/
noncomputable def M (F : ℕ → ℕ) (I : Instance K ι) (t : ℕ) : ι → Option (Fin K) :=
  fun i => if Accepts F I t i then some (prop F I t i) else none

/-- Player `i`'s state after round `t` (after feedback and `a ← a + 1`). -/
noncomputable def post (F : ℕ → ℕ) (I : Instance K ι) (t : ℕ) (i : ι) : LState K :=
  stepProfile I F t (pre F I t) i

end DecDynMatch


