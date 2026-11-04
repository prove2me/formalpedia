-- Prove2me | Definitions.Def_QMCLeafB_final_reunion_m7
-- name    : QMCLeafB_final_reunion_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:05:58.896186+00:00
-- url     : https://prove2.me/theorems/695f22ed-f6f9-4245-abd0-f9b4d30982fb
-- title:
--   QMCLeafB final_reunion_m7
-- statement:
--   # leaf B phase 13 — brick `final-stroke` (swarm `smw17fqzz`, member m7, direction d4), the reunion
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_brick_init_verdict_m8
import Definitions.Def_QMCLeafB_round_program_m3
/-
# leaf B phase 13 — brick `final-stroke` (swarm `smw17fqzz`, member m7, direction d4), the reunion

This is the assembly file.  It is short on purpose: every piece below is somebody else's proved
theorem, and the only thing this file adds is that they are put in the *right* order.

What it consumes:

* `QMCLeafB.InitVerdict` (`Check_brick_init_verdict_m8`): the state `St`, `init`, `verdict`,
  `poly_init`, `poly_verdict`, `init_tape` and `verdict_iterate_eq_anyOk`;
* `QMCLeafB.FinalStroke` (`Check_final_stroke_m7`): `hspec_of_tape_free`, the `RunParams`/`RunParts`
  split, `runParamsOfK` (the numeric half of `RunData`, with the round count free above
  `budgetRounds`), and — the point of this file — the **orbit** form of the closing stroke,
  `endgame_orbit_of_parts` + `orbit_of_monomial_pow`.

Why the orbit form and not the shelf's `hsize`: `SimPoly.poly_loop_state` asks for forward invariance
of the *ball* `{(encSt x).length ≤ sizes.eval (encSt a).length}`, and no clip-and-snap round has that
property (m3's f55).  What the machine combinator actually uses is invariance along the reachable
orbit, which `boundedRun_loopBody_orbit` proves is all that is needed.  So the size hypothesis here is
the round's **growth class**:

    hmono : ∀ s j, (enc (round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k,     1 ≤ k

and `sizes` is discharged as `sizesOrbitPow C k = (2C+2)·(X+1)^k`.  `k ≥ 2` is what a clip-to-`mu` /
snap-to-`d` round needs (`mu`, `d` are state data, so the first application can lengthen the state
from `L` to `O(n²·L)`); `k = 1` is not enough, and that is why the size slot is stated with a power.

Residual after this file: `round` with `Automatic.Poly round` and its growth class, `fuel` with its
exact length `K*m`, `rmax`/`m`/`hhalve`, `K ≥ budgetRounds`, and `RunParts` per bracketed `(G,t)`.
No `sorry`, no `axiom`; audit at the end.
-/

set_option autoImplicit false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.FinalReunion

open QuantumMaxCutEnergy

/-- The request coding of the leaf, as in `Check_brick_verdict_sound` and `Check_final_stroke_m7`. -/
local instance instRequestCodingReunion :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **`d9f601e5` with the size slot in orbit form.**  `QMCLeafB.InitVerdict.endgame_of_my_loop`
(`Check_brick_init_verdict_m8`) with `hsize`/`hsize0` — the unsatisfiable ball form — replaced by the
round's monomial growth class `hmono`.  Everything else is unchanged, so this theorem replaces that
one as the endgame to fill in.

`C` and `k` are the round's size class and exponent; `k ≥ 1` and `k = 2` is the intended value. -/
theorem endgame_orbit
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G QMCLeafB.InitVerdict.dqV m ≤ K G)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (round : QMCLeafB.InitVerdict.St → QMCLeafB.InitVerdict.St)
    (hr : Automatic.Poly round)
    (C k : ℕ) (hk : 1 ≤ k)
    (hmono : ∀ (s : QMCLeafB.InitVerdict.St) (j : ℕ),
      (enc (round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitVerdict.init round QMCLeafB.InitVerdict.verdict
          (fun G' _ => K G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G QMCLeafB.InitVerdict.dqV
          (by norm_num [QMCLeafB.InitVerdict.dqV]) rmax hrmax m hm1 (K G) (hK G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_orbit_of_parts
    QMCLeafB.InitVerdict.init fuel round QMCLeafB.InitVerdict.verdict
    QMCLeafB.InitVerdict.poly_init hfuel hr QMCLeafB.InitVerdict.poly_verdict
    (QMCLeafB.FinalStroke.sizesOrbitPow C k)
    (fun a j hj => QMCLeafB.FinalStroke.orbit_of_monomial_pow round C k hk hmono a j hj)
    (fun G' _ => K G' * m)
    QMCLeafB.InitVerdict.init_tape hfuelLen
    (fun G t _ hlo hhi => (hd G t hlo hhi).toRunData)

/-- The same with the round's growth class written in the `1 ≤ k, C` shape a ledger proof produces:
`hmono` at `k = 2`, the value a clip-to-`mu`/snap-to-`d` round needs. -/
theorem endgame_orbit_sq
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G QMCLeafB.InitVerdict.dqV m ≤ K G)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (round : QMCLeafB.InitVerdict.St → QMCLeafB.InitVerdict.St)
    (hr : Automatic.Poly round)
    (C : ℕ)
    (hmono : ∀ (s : QMCLeafB.InitVerdict.St) (j : ℕ),
      (enc (round^[j] s)).length ≤ C * ((enc s).length + 1) ^ 2)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitVerdict.init round QMCLeafB.InitVerdict.verdict
          (fun G' _ => K G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G QMCLeafB.InitVerdict.dqV
          (by norm_num [QMCLeafB.InitVerdict.dqV]) rmax hrmax m hm1 (K G) (hK G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_orbit rmax hrmax m hm1 hhalve K hK fuel hfuel round hr C 2 (by norm_num) hmono
    hfuelLen hd

/-! ## The same endgame at m3's σ

`Check_round_program_m3` builds `round`, `verdict`, `poly_round` and `poly_verdict` at
`RoundProgram.RSt`, self-contained (the state carries the weight-matrix code `A`, the primal code
`X`, the threshold `t`, the box bound `mu`, the grid `d`, the ok flags `oks` and the current normal
`rec`).  The two σ's of the phase (`InitVerdict.St` and `RoundProgram.RSt`) are *not* the same type:
`St` has no field for `A`, `RSt` has none for `cs/ps/rhos`.  Both endgames are therefore stated, so
whichever σ wins only has to supply the pieces it lacks — at `RSt` that is `init` (build the row-major
`wMatrix` code `A` from the request; `X`, `mu`, `d` are the cheap arithmetic of `MOf`/`gridOf`) and
`RunParts`; at `St` it is `round` and `RunParts`.

`dq = 1` here for the same reason as `dqV`: `RSt.mu` is the box bound `2n² + 2dq²` of `initShapeOf`,
so `dq` is pinned by the state's own `mu`-register. -/
theorem endgame_RSt
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G 1 m ≤ K G)
    (init0 : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → QMCLeafB.RoundProgram.RSt)
    (hinit0 : Automatic.Poly init0)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (C k : ℕ) (hk : 1 ≤ k)
    (hmono : ∀ (s : QMCLeafB.RoundProgram.RSt) (j : ℕ),
      (enc (QMCLeafB.RoundProgram.round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict (fun G' _ => K G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G 1 (by norm_num) rmax hrmax m hm1 (K G) (hK G)
          (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_orbit_of_parts
    init0 fuel QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    hinit0 hfuel QMCLeafB.RoundProgram.poly_round QMCLeafB.RoundProgram.poly_verdict
    (QMCLeafB.FinalStroke.sizesOrbitPow C k)
    (fun a j hj => QMCLeafB.FinalStroke.orbit_of_monomial_pow QMCLeafB.RoundProgram.round C k hk
      hmono a j hj)
    (fun G' _ => K G' * m) hinitTape hfuelLen
    (fun G t _ hlo hhi => (hd G t hlo hhi).toRunData)

/-- **The endgame at `RSt` with a constant per-round size cost.**  The strongest size hypothesis the
concrete round can meet: one round costs at most `c` bits of the *joint* `(state, fuel)` encoding, so
`sizes = sizesAdd c = (c+1)·(X+1)` (see `FinalStroke.horbit_of_additive_step`).  With `oks` a
`List Bool` and the fuel one bit per round, the ideal cost is `c = 0`; `c = 3` is the value while the
record `rec` is not shrunk.

Note on why the hypothesis cannot be weakened to "for all `s`" at the *state* level: `mu` and `d` are
state data, so a state with a tiny `X` and a huge `mu` has its `n²` entries rewritten at height
`≈ height mu`, which is not an additive cost.  The per-round cost has to be asserted on the pair
`(state, fuel)` along the run, which is what `hstep` does, or the reachable set has to be carved out
by a height invariant. -/
theorem endgame_RSt_step
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G 1 m ≤ K G)
    (init0 : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → QMCLeafB.RoundProgram.RSt)
    (hinit0 : Automatic.Poly init0)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (c : ℕ)
    (hstep : ∀ (s : QMCLeafB.RoundProgram.RSt) (f : List Bool),
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundProgram.round s, f.tail)).length
        ≤ (QMCLeafB.SimPoly.encSt (s, f)).length + c)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict (fun G' _ => K G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G 1 (by norm_num) rmax hrmax m hm1 (K G) (hK G)
          (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_orbit_of_parts
    init0 fuel QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    hinit0 hfuel QMCLeafB.RoundProgram.poly_round QMCLeafB.RoundProgram.poly_verdict
    (QMCLeafB.FinalStroke.sizesAdd c)
    (QMCLeafB.FinalStroke.horbit_of_additive_step QMCLeafB.RoundProgram.round c hstep)
    (fun G' _ => K G' * m) hinitTape hfuelLen
    (fun G t _ hlo hhi => (hd G t hlo hhi).toRunData)

/-! ## Axiom audit -/

#print axioms QMCLeafB.FinalReunion.endgame_orbit
#print axioms QMCLeafB.FinalReunion.endgame_orbit_sq
#print axioms QMCLeafB.FinalReunion.endgame_RSt
#print axioms QMCLeafB.FinalReunion.endgame_RSt_step

end QMCLeafB.FinalReunion


