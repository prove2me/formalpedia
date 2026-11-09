-- Prove2me | Definitions.Def_RelativisticZK205_ThreeCol_Verifier
-- name    : RelativisticZK205_ThreeCol_Verifier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:08:20.077946+00:00
-- url     : https://prove2.me/theorems/a6a7f369-1c69-4031-9b66-0c7282a4d6ae
-- title:
--   One-round verifier pairs as two-stage kernels, their joint output law, and No-Signalling verifiers
-- statement:
--   A pair of verifiers $(V'_1,V'_2\mid\widehat V')$ with auxiliary inputs $a_1,a_2$ first picks the two queries $q_1,q_2$ together with a private memory $s$ (everything they carry to the check phase, including outcomes of $\widehat V'$), with an arbitrary joint law $\mathrm{ask}(a_1,a_2)$. After receiving the replies $w_1,w_2$ they compute their outputs $(o_1,o_2)$ with an arbitrary joint law $\mathrm{finish}(a_1,a_2,s,q_1,q_2,w_1,w_2)$.
--
--   Given a two-party channel $R$ answering the queries, the **joint output distribution** is
--
--   $$
--   \mathrm{run}(V,R,a_1,a_2)=\Pr[(o_1,o_2)]\ \text{ for } (s,q_1,q_2)\sim\mathrm{ask}(a_1,a_2),\ (w_1,w_2)\sim R(q_1,q_2),\ (o_1,o_2)\sim\mathrm{finish}(\dots).
--   $$
--
--   A verifier pair is **No-Signalling** when, with the memory marginalised and the replies held fixed: the law of $q_1$ does not depend on $a_2$ and that of $q_2$ not on $a_1$; the law of $(q_1,o_1)$ does not depend on $(a_2,w_2)$ and that of $(q_2,o_2)$ not on $(a_1,w_1)$; and the law of $(q_1,q_2,o_1)$ does not depend on $w_2$ and that of $(q_1,q_2,o_2)$ not on $w_1$.
--
--   This is the verifier side of Definition 22 for the one-round protocol of §5.1, where in the check phase "$V'_i\mid\widehat V'$ computes whatever it wants" and the simulator outputs what $V'_i$ outputs.
--
--   **Formalization Note** `Verifier Aux State Q W O` has fields `ask` and `finish`; `run` binds `ask`, the channel and `finish`. The types `Aux`, `State`, `O` are arbitrary, so a verifier may copy its whole transcript into its output. Theorem 1 is stated for every verifier, No-Signalling or not; `IsNoSignalling` records the class the source names, and the honest verifiers satisfy it. Polynomial running time (Definition 22) is not modelled.
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), Definition 22, p.9; §5.1, p.10 (Steps 1–2 and the check phase)

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Channel

/-!
# One-round verifiers and their joint output distribution

Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, *Relativistic Zero
Knowledge*, STOC 2027 submission #205 (October 2026), Definition 22 (p.9) and §5.1 (pp.9–10:
Step 1, "pick", and the check phase, "computes whatever it wants").

A pair of verifiers `(V'₁, V'₂ | V̂')` with auxiliary inputs `a₁, a₂` first picks the two queries
together with private memory, then, after the replies `w₁, w₂` arrive, computes the two outputs.
Everything the verifiers carry from the pick phase to the check phase, including any outcome of
`V̂'` that is not part of the queries, is in the memory `State`.
-/

namespace RelativisticZK205.ThreeCol

/-- A one-round verifier pair as a two-stage kernel, with auxiliary-input type `Aux`, memory type
`State`, query type `Q`, reply type `W` and output type `O`.
* `ask a₁ a₂`: the joint law of `(memory, q₁, q₂)`; `q₁` goes to the first prover (or simulator),
  `q₂` to the second.
* `finish a₁ a₂ s q₁ q₂ w₁ w₂`: the joint law of the outputs `(o₁, o₂)` given everything. -/
structure Verifier (Aux State Q W O : Type) where
  /-- Commit phase, Step 1: pick the two queries (and memory). -/
  ask : Aux → Aux → PMF (State × Q × Q)
  /-- Check phase: compute the two outputs. -/
  finish : Aux → Aux → State → Q → Q → W → W → PMF (O × O)

namespace Verifier

variable {Aux State Q W O : Type}

/-- The joint output distribution of the verifiers `V` with auxiliary inputs `a₁, a₂` when the
replies come from the two-party channel `R`: pick `(s, q₁, q₂)`, obtain `(w₁, w₂) ∼ R(q₁, q₂)`, then
compute `(o₁, o₂)`. -/
noncomputable def run (V : Verifier Aux State Q W O) (R : Channel Q Q W W) (a₁ a₂ : Aux) :
    PMF (O × O) :=
  (V.ask a₁ a₂).bind fun sq =>
    (R sq.2.1 sq.2.2).bind fun w => V.finish a₁ a₂ sq.1 sq.2.1 sq.2.2 w.1 w.2

/-- The law of `(q₁, q₂, o₁, o₂)` when the replies are held fixed at `w₁, w₂`, with the memory
marginalised. -/
noncomputable def jointLaw (V : Verifier Aux State Q W O) (a₁ a₂ : Aux) (w₁ w₂ : W) :
    PMF (Q × Q × O × O) :=
  (V.ask a₁ a₂).bind fun sq =>
    (V.finish a₁ a₂ sq.1 sq.2.1 sq.2.2 w₁ w₂).map fun o => (sq.2.1, sq.2.2, o.1, o.2)

/-- No-Signalling verifiers (memory marginalised): neither verifier's view depends on the other
verifier's inputs.
1. The law of `q₁` does not depend on `a₂`, and that of `q₂` not on `a₁`.
2. The law of `(q₁, o₁)` does not depend on `(a₂, w₂)`, and that of `(q₂, o₂)` not on `(a₁, w₁)`.
3. The law of `(q₁, q₂, o₁)` does not depend on `w₂`, and that of `(q₁, q₂, o₂)` not on `w₁`. -/
def IsNoSignalling (V : Verifier Aux State Q W O) : Prop :=
  (∀ a₁ a₂ a₂', (V.ask a₁ a₂).map (fun sq => sq.2.1) = (V.ask a₁ a₂').map (fun sq => sq.2.1)) ∧
  (∀ a₁ a₁' a₂, (V.ask a₁ a₂).map (fun sq => sq.2.2) = (V.ask a₁' a₂).map (fun sq => sq.2.2)) ∧
  (∀ a₁ a₂ a₂' w₁ w₂ w₂',
    (V.jointLaw a₁ a₂ w₁ w₂).map (fun t => (t.1, t.2.2.1)) =
      (V.jointLaw a₁ a₂' w₁ w₂').map (fun t => (t.1, t.2.2.1))) ∧
  (∀ a₁ a₁' a₂ w₁ w₁' w₂,
    (V.jointLaw a₁ a₂ w₁ w₂).map (fun t => (t.2.1, t.2.2.2)) =
      (V.jointLaw a₁' a₂ w₁' w₂).map (fun t => (t.2.1, t.2.2.2))) ∧
  (∀ a₁ a₂ w₁ w₂ w₂',
    (V.jointLaw a₁ a₂ w₁ w₂).map (fun t => (t.1, t.2.1, t.2.2.1)) =
      (V.jointLaw a₁ a₂ w₁ w₂').map (fun t => (t.1, t.2.1, t.2.2.1))) ∧
  (∀ a₁ a₂ w₁ w₁' w₂,
    (V.jointLaw a₁ a₂ w₁ w₂).map (fun t => (t.1, t.2.1, t.2.2.2)) =
      (V.jointLaw a₁ a₂ w₁' w₂).map (fun t => (t.1, t.2.1, t.2.2.2)))

end Verifier

end RelativisticZK205.ThreeCol


