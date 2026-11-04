-- Prove2me | Definitions.Def_QMCLeafB_hspec_m4
-- name    : QMCLeafB_hspec_m4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:17:04.41277+00:00
-- url     : https://prove2.me/theorems/1fb20d6f-e3c3-49e7-b1d5-ab33852df655
-- title:
--   QMCLeafB hspec_m4
-- statement:
--   # leaf B phase 13 — brick `hspec` (swarm `smw17fqzz`, member m4, direction d7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_fuel
/-
# leaf B phase 13 — brick `hspec` (swarm `smw17fqzz`, member m4, direction d7)

The closing stroke

    QMCLeafB.VerdictSound.solution_of_loop_via_runData
      (init fuel round verdict hinit hfuel hr hv sizes hsize hsize0 o hspec hd)

has exactly one slot that *relates two different objects*: `hspec`, the equation

    ∀ p : (Input × List Bool) × ℚ,  verdict (round^[(fuel p).length] (init p)) = o p.1.1 p.2

between the **program-level run** (`init`, `round`, `verdict`, `fuel`, all of which see the whole
input pair `p = ((G, coins), t)`, random tape included) and the **tape-free bit** `o : Input → ℚ →
Bool`.  This file pins `o` and discharges `hspec`; it builds no state machine and no program of the
analysis — `σ` stays a variable, so the brick composes with whichever `σ` the driver members pin.

The content is small but it is *not* vacuous, because `hspec` fails for a run that reads the tape,
and because "the fuel's length is the round count" is a real constraint:

* §1 the decoded input `weightsOf G` (the parser's own output) and the `Poly` program that reads it
  off `(Input × List Bool) × ℚ`.  `QMCNumericRuntime.parseWeights` **stops after the announced
  number of weights**, so the parser drops the random tape — this is the whole source of
  tape-freeness below.
* §2 the general `hspec` theorem: from (a) the fuel length is a tape-free count `T0 G t` and (b) the
  program's initial state is the tape-free state `inits G t`, the equation holds by unfolding.
  Neither hypothesis is a proof obligation smuggled in: §3 proves both are `rfl` at the concrete
  shapes `init p = pack (weightsOf p.1.1) p.2`, `fuel = fuelTake k (countOf Tof)`.
* §3 the concrete tape-free run: `initOf`, `initP`, `countOf`, their `Poly` proofs from the shelf
  (`decodedInputProgram`, `Fuel.poly_fuelTake`), and the exact fuel length
  (`Fuel.fuelTake_length_of_le`).
* §3b **the general decoded input** `δ`: the driver's `init` is `pack ∘ decode` for a tape-free `Poly`
  decoder `decode : Input → ℚ → δ` (whatever it parses: order, weights, threshold).  `initD_poly`,
  `initD_tape_free`, `hspec_runBitD`, `solution_of_loop_via_iterateD`.
* §3c a decoder that carries the graph order as well (`(n, weights, t)`), since `Boundary.initShapeOf
  (n*n)` needs `n`: `decodedWithOrder` and `decodedWithOrder_poly`.
* §3d/§3e/§3f **the round count**: `countWithOrder` (one round on the degenerate orders),
  `roundCount C d G = 4 * (C (n+1)^d) * (n n)` (the integration's `K * m` at `m = 4 n²`), the order
  `G.n` as a `Poly` function of the input, and the fuel-length slots `hfuelLen_*` verbatim at
  `fuel := Fuel.fuelTake k T`.  Warning recorded there: a plain monomial `C (n+1)^d` is *not* under
  `L^(2^k)` at `n = 0` with an empty tape, so the count has to vanish or collapse there.
* §3g **overshooting fuel**: `hspec` does not need the exact count.  `anyOk` is stable under
  appending `false` rounds (`anyOk_congr_of_false`), so a fuel that is merely *long* works provided
  the run records `false` from `Tstar` on (`hspec_of_overshoot`, `hspec_of_stable_ok`).  This is what
  lets `Tstar` be `RunData`'s `K * m`, a `clog`-based number no `Poly` program can compute.
  Conversely §3g shows that *monotonicity of `anyOk` alone is not enough* — the missing hypothesis is
  "no new `ok` after `Tstar`", which is a real obligation on `round`.
* §3h/§3i/§3j **the round count the estimate needs**: `bitCost q = size (num q) + size (den q) + 1`
  is `Poly` in the decider's input (`poly_bitCostRq`), `Rq + 1 ≤ 2 ^ bitCost Rq`
  (`Rq_add_one_le_two_pow_bitCost`), `bitCost (Rq G) ≤ 48 L + 16` (`bitCost_Rq_le`), and the count
  `countK C d G = (C (n+1)^d (bitCost (Rq G) + 1)) * (4 n²)` — the `K * m` the run actually uses —
  is `Poly` (`poly_countK`) and under the fuel length (`hTle_countK`, `hfuelLen_countK`, from
  `C + d + 9 ≤ 2^k`).  A monomial in `n` alone is *never* enough here: `hbudget` needs
  `K ≳ n² log (1 + Rq)` and `log Rq` is unbounded at fixed `n`.
* §4 the **pinned `o`** — `runBitP` / `runBitD` — and `hspec` at that `o` (`hspec_runBit`,
  `hspec_runBit_take`), which is the slot verbatim; `runBitP_eq_doc` is the campaign doc's `o`.
* §5 the bit is computable: `poly_runBit`, the `Automatic.Poly` statement for the pinned `o`
  (`SimPoly.ho_of_loop`'s `ho` slot).  So the `o` of this file needs no separate program.
* §6 the closing stroke **with `o` and `hspec` filled in** — `solution_of_loop_via_iterate`,
  `solution_of_loop_via_iterateD`, `solution_of_loop_via_orderCount`: the remaining slots are the
  driver's (`σ`, `pack`/`decode`, `round`, `verdict`, `hr`, `hv`, `sizes`, `hsize`, `hsize0`, the
  count, `hd`).  No `o`, no `hspec`, no fuel.
* §7 axiom audit (43 audits on 2026-11-03, all `[propext, Classical.choice, Quot.sound]` or less).

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`.
-/

set_option autoImplicit false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.Hspec

open QuantumMaxCutEnergy

/-- The request coding of the leaf, spelt exactly as in `Check_brick_finish_line` /
`Check_sim_poly_m4` / `Check_fuel` (`⟨encodeRequest⟩`, not the generic `encodePair`): the closing
stroke is stated at this instance, so `hspec` here is `hspec` there. -/
local instance instRequestCodingHspec : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The decoded input: the graph's weight list, off the encoded request

`o : Input → ℚ → Bool` cannot see the tape, so every ingredient of the run that the verdict depends
on has to be a function of the *decoded* input.  The library's parser is exactly such a function:
it reads the unary order, then the `n(n-1)/2` weights, and stops — the tape never enters. -/

/-- The graph's weights as rationals, in endpoint order — the parser's own output
(`ℚ≥0 → ℚ` is the identity on the nose). -/
def weightsOf (G : QuantumMaxCutEnergy.Input) : List ℚ :=
  (QMCNumericRuntime.weightsList G).map (fun q : ℚ≥0 => (q : ℚ))

/-- **The parser drops the tape**: `parseWeights` of the request word is the graph's weight list,
for every tape.  (`Check_AssemblyGlue_m1` records the same fact; it is restated here so that this
brick depends only on `Definitions`, `Check_fuel` and `Check_brick_verdict_sound`.) -/
theorem weightsOf_parseWeights (G : QuantumMaxCutEnergy.Input) (coins : List Bool) :
    QMCNumericRuntime.parseWeights (QuantumMaxCutEnergy.encodeRequest (G, coins)) = weightsOf G :=
  QMCNumericRuntime.parseWeights_request G coins

/-- **The weight list is a `Poly` function of the decider's exact input.**  Domain coding is
`encodePair encodeRequest Ratio.encode`; `fst` projects the request word out and the campaign's
parser reads the weights off it. -/
noncomputable def weightsOfRequestProgram :
    PolyProgram (encodePair QuantumMaxCutEnergy.encodeRequest Ratio.encode) (encodeList Ratio.encode)
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => weightsOf p.1.1) :=
  (PolyProgram.fst QuantumMaxCutEnergy.encodeRequest Ratio.encode).comp
    QMCNumericRuntime.requestWeightsProgram

/-- `weightsOfRequestProgram` in `Automatic.Poly` form. -/
theorem weightsOfRequest_poly :
    Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => weightsOf p.1.1) :=
  ⟨weightsOfRequestProgram⟩

/-- **The decoded input of the whole run**: `(weights of G, t)`, as one `Poly` function of the
encoder's input.  Every tape-free quantity of this file factors through this pair. -/
noncomputable def decodedInputProgram :
    PolyProgram (encodePair QuantumMaxCutEnergy.encodeRequest Ratio.encode)
      (encodePair (encodeList Ratio.encode) Ratio.encode)
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => (weightsOf p.1.1, p.2)) :=
  weightsOfRequestProgram.fanout
    (PolyProgram.snd QuantumMaxCutEnergy.encodeRequest Ratio.encode)

/-- `decodedInputProgram` in `Automatic.Poly` form. -/
theorem decodedInput_poly :
    Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => (weightsOf p.1.1, p.2)) :=
  ⟨decodedInputProgram⟩

/-! ## 2.  The general `hspec` theorem

`hspec` compares the *program's* run, started at `init p` for `(fuel p).length` rounds, with the
*tape-free* bit.  The two are equal as soon as the length and the start agree, because `round` and
`verdict` are pure functions of the state `σ` and hence cannot see the tape either. -/

section General

variable {σ : Type}

/-- The tape-free run: `inits G t` is the state the program starts in at `(G, t)` once the tape is
forgotten, `T0 G t` the number of rounds it runs there. -/
def runBit (inits : QuantumMaxCutEnergy.Input → ℚ → σ) (round : σ → σ) (verdict : σ → Bool)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ) :
    QuantumMaxCutEnergy.Input → ℚ → Bool :=
  fun G t => verdict (round^[T0 G t] (inits G t))

/-- **`hspec`, in the general form.**  If the fuel length is the tape-free round count and the
program's initial state is the tape-free initial state, then the program's verdict is `runBit`.

Note what is *not* assumed: nothing about `round` or `verdict` (they are endofunctions of `σ`, so
they are automatically tape-free) and nothing about the tape.  The two hypotheses are discharged at
the concrete shapes in §3. -/
theorem hspec_of_tape_free {init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ}
    {inits : QuantumMaxCutEnergy.Input → ℚ → σ} (round : σ → σ) (verdict : σ → Bool)
    {fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool}
    {T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ}
    {T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ}
    (hinit : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), init p = inits p.1.1 p.2)
    (hT : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), T p = T0 p.1.1 p.2)
    (hlen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), (fuel p).length = T p) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (round^[(fuel p).length] (init p)) = runBit inits round verdict T0 p.1.1 p.2 := by
  intro p
  rw [hlen p, hT p, hinit p]
  rfl

end General

/-! ## 3.  The concrete tape-free run: `pack (weights G) t`

The driver's initial state will be built by parsing the graph (weights, order) and packing; the round
count is a `Poly` function of the same decoded input.  Both shapes are tape-free by construction, and
§3 proves the `Poly` and length facts they need. -/

section Concrete

variable {σ : Type}

/-- **The tape-free initial state of the run**, at the graph level: the packing function `pack` gets
the decoded weight list and the threshold. -/
def initOf (pack : List ℚ → ℚ → σ) (G : QuantumMaxCutEnergy.Input) (t : ℚ) : σ :=
  pack (weightsOf G) t

/-- The same at the program's own type, `((Input × List Bool) × ℚ)`. -/
def initP (pack : List ℚ → ℚ → σ) : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ :=
  fun p => pack (weightsOf p.1.1) p.2

/-- **The program's initial state is the tape-free one**: `hspec`'s `hinit` at this shape, `rfl`. -/
theorem initP_apply (pack : List ℚ → ℚ → σ)
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    initP pack p = initOf pack p.1.1 p.2 := rfl

/-- **The initial state does not depend on the random tape**: `hspec`'s tape-independence, `rfl` at
this shape.  (For contrast: had `init` been written on `p` by parsing `encodeRequest p.1`, the tape
would have entered — `init`'s `Poly`-ness alone does not give this.) -/
theorem initP_tape_free (pack : List ℚ → ℚ → σ) (G : QuantumMaxCutEnergy.Input)
    (coins coins' : List Bool) (t : ℚ) :
    initP pack ((G, coins), t) = initP pack ((G, coins'), t) := rfl

/-- **The initial state is a `Poly` program.**  One hypothesis, on the decoded shape
`List ℚ × ℚ → σ` — i.e. exactly what a packing routine on the parsed graph looks like. -/
theorem initP_poly [Coding σ] (pack : List ℚ → ℚ → σ)
    (hpack : Automatic.Poly (fun q : List ℚ × ℚ => pack q.1 q.2)) :
    Automatic.Poly (initP pack) :=
  ⟨decodedInputProgram.comp hpack.program⟩

/-- **The round count, tape-free**: `Tof` evaluated on the decoded input.  This is the function whose
value at `(G, t)` is both the number of rounds the loop runs (`hspec`) and the one `o` is defined
with. -/
def countOf (Tof : List ℚ → ℚ → ℕ) : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ :=
  fun p => Tof (weightsOf p.1.1) p.2

/-- `countOf` unfolded. -/
theorem countOf_apply (Tof : List ℚ → ℚ → ℕ)
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    countOf Tof p = Tof (weightsOf p.1.1) p.2 := rfl

/-- **The round count is a `Poly` program** as soon as it is one on the decoded input. -/
theorem poly_countOf (Tof : List ℚ → ℚ → ℕ)
    (hTof : Automatic.Poly (fun q : List ℚ × ℚ => Tof q.1 q.2)) :
    Automatic.Poly (countOf Tof) :=
  Automatic.Poly.comp
    (f := fun q : List ℚ × ℚ => Tof q.1 q.2)
    (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => (weightsOf p.1.1, p.2))
    hTof decodedInput_poly

/-- **The fuel has exactly the prescribed length.**  This is `Check_fuel`'s truncation lemma read at
`countOf`: once the round count is under the squaring bound at the input's own request word, the
truncated fuel has length exactly the count — so the loop of `ho_of_loop` runs the `T0` rounds `o`
was defined with. -/
theorem fuelTake_countOf_length (k : ℕ) (Tof : List ℚ → ℚ → ℕ)
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ))
    (h : countOf Tof p ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 ^ k) :
    (QMCLeafB.Fuel.fuelTake k (countOf Tof) p).length = Tof (weightsOf p.1.1) p.2 := by
  rw [QMCLeafB.Fuel.fuelTake_length_of_le k (countOf Tof) p h]
  rfl

end Concrete

/-! ## 3b.  The general decoded input

The driver's initial state is built by *parsing* the request: whatever it needs — the graph order for
`Boundary.initShapeOf (n*n)`, the weight list, the threshold — is a function of `(G, t)` alone, and a
`Poly` program computes it.  `δ` below is that decoded data; the two hypotheses of §3b are exactly
the driver's obligations and neither mentions the tape.  The concrete `weightsOf` case of §3 is the
instance `δ = List ℚ × ℚ`, `decode G t = (weightsOf G, t)`; §3c gives the instance that also carries
the order, which is what the packed code `initShapeOf (n*n)` needs. -/

/-- The initial state from a tape-free decoder `decode` and a packing `pack`. -/
def initD {σ δ : Type} (decode : QuantumMaxCutEnergy.Input → ℚ → δ) (pack : δ → σ) :
    ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ :=
  fun p => pack (decode p.1.1 p.2)

/-- `initD` unfolded. -/
theorem initD_apply {σ δ : Type} (decode : QuantumMaxCutEnergy.Input → ℚ → δ) (pack : δ → σ)
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    initD decode pack p = pack (decode p.1.1 p.2) := rfl

/-- **Tape-independence of the initial state, at a general decoder**: `rfl`, because `decode` is not
handed the tape.  This is the hypothesis `hspec` needs and `Automatic.Poly init` does *not* imply. -/
theorem initD_tape_free {σ δ : Type} (decode : QuantumMaxCutEnergy.Input → ℚ → δ) (pack : δ → σ)
    (G : QuantumMaxCutEnergy.Input) (coins coins' : List Bool) (t : ℚ) :
    initD decode pack ((G, coins), t) = initD decode pack ((G, coins'), t) := rfl

/-- **The initial state is a `Poly` program**: decoder ∘ packing, each `Poly`. -/
theorem initD_poly {σ δ : Type} [Coding σ] [Coding δ]
    (decode : QuantumMaxCutEnergy.Input → ℚ → δ) (pack : δ → σ)
    (hdecode : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => decode p.1.1 p.2))
    (hpack : Automatic.Poly pack) :
    Automatic.Poly (initD decode pack) :=
  Automatic.Poly.comp
    (f := pack) (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => decode p.1.1 p.2)
    hpack hdecode

/-- **The pinned verdict bit at a general decoded input.** -/
def runBitD {σ δ : Type} (decode : QuantumMaxCutEnergy.Input → ℚ → δ) (pack : δ → σ)
    (round : σ → σ) (verdict : σ → Bool) (Tof : δ → ℕ) :
    QuantumMaxCutEnergy.Input → ℚ → Bool :=
  fun G t => verdict (round^[Tof (decode G t)] (pack (decode G t)))

/-- `runBitD` unfolded. -/
theorem runBitD_apply {σ δ : Type} (decode : QuantumMaxCutEnergy.Input → ℚ → δ) (pack : δ → σ)
    (round : σ → σ) (verdict : σ → Bool) (Tof : δ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    runBitD decode pack round verdict Tof G t
      = verdict (round^[Tof (decode G t)] (pack (decode G t))) := rfl

/-- **`hspec` at the general pinned `o`.**  The program runs `(fuel p).length` rounds from
`initD decode pack p`; if that length is the tape-free count, the result is `runBitD`. -/
theorem hspec_runBitD {σ δ : Type} (decode : QuantumMaxCutEnergy.Input → ℚ → δ) (pack : δ → σ)
    (round : σ → σ) (verdict : σ → Bool) (Tof : δ → ℕ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hlen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = Tof (decode p.1.1 p.2)) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (round^[(fuel p).length] (initD decode pack p))
        = runBitD decode pack round verdict Tof p.1.1 p.2 := by
  intro p
  rw [hlen p]
  rfl

/-- **The closing stroke at a general decoded input.**  `o` and `hspec` are gone; the driver supplies
the decoder, the packing, the round, the verdict, the size accounting, the count and the run bundle
`hd` at the pinned `o`. -/
theorem solution_of_loop_via_iterateD {σ δ : Type} [Coding σ] [Coding δ]
    (decode : QuantumMaxCutEnergy.Input → ℚ → δ) (pack : δ → σ)
    (hdecode : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => decode p.1.1 p.2))
    (hpack : Automatic.Poly pack)
    (round : σ → σ) (verdict : σ → Bool)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (k : ℕ) (Tof : δ → ℕ)
    (hTof : Automatic.Poly Tof)
    (hTle : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fun p => Tof (decode p.1.1 p.2)) p
        ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → QMCLeafB.VerdictSound.RunData
        (runBitD decode pack round verdict Tof) G t) :
    QMCLeafB.FinishLine.SolutionStatement := by
  have hfuelpoly : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QMCLeafB.Fuel.fuelTake k (fun p => Tof (decode p.1.1 p.2)) p) :=
    QMCLeafB.Fuel.poly_fuelTake k _ (Automatic.Poly.comp hTof hdecode)
  have hlen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (QMCLeafB.Fuel.fuelTake k (fun p => Tof (decode p.1.1 p.2)) p).length
        = Tof (decode p.1.1 p.2) :=
    fun p => QMCLeafB.Fuel.fuelTake_length_of_le k _ p (hTle p)
  exact QMCLeafB.VerdictSound.solution_of_loop_via_runData (initD decode pack)
    (QMCLeafB.Fuel.fuelTake k (fun p => Tof (decode p.1.1 p.2))) round verdict
    (initD_poly decode pack hdecode hpack) hfuelpoly hr hv sizes hsize hsize0
    (runBitD decode pack round verdict Tof)
    (hspec_runBitD decode pack round verdict Tof _ hlen) hd

/-! ## 3c.  A concrete decoder that carries the graph order

`RunData.hwit`/`hcut` are stated at `Boundary.initShapeOf (n*n) (…)`, so the packed state needs the
order `n`, not just the weights.  The order is read off the request word by the campaign's own
`inputWidth`, and `inputWidth`/`parseWeights` are both `Poly` at the raw word coding — so the pair
`(n, weights)` is a `Poly` function of the request, and it is tape-free by the two `_request`
lemmas. -/

/-- The graph order, read off the raw request word.  (`packProgram` moves the word to the
list-of-bools encoding that `inputWidth_poly` is stated at.) -/
noncomputable def inputWidthWordProgram :
    PolyProgram id Nat.bits QMCNumericRuntime.inputWidth :=
  BooleanLists.packProgram.comp QMCNumericRuntime.inputWidth_poly.program

/-- The decoded input carrying the order: `((n, weights), t)`. -/
def decodedWithOrder (G : QuantumMaxCutEnergy.Input) (t : ℚ) : (ℕ × List ℚ) × ℚ :=
  ((G.n, weightsOf G), t)

/-- The decoder *as a program reads it*, before the two `_request` simplifications: the order and the
weights parsed straight off the encoded request word. -/
noncomputable def parsedWithOrderProgram :
    PolyProgram (encodePair QuantumMaxCutEnergy.encodeRequest Ratio.encode)
      (encodePair (encodePair Nat.bits (encodeList Ratio.encode)) Ratio.encode)
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        ((QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1),
          QMCNumericRuntime.parseWeights (QuantumMaxCutEnergy.encodeRequest p.1)), p.2)) :=
  let wordProg : PolyProgram id (encodePair Nat.bits (encodeList Ratio.encode))
      (fun xs : List Bool =>
        (QMCNumericRuntime.inputWidth xs, QMCNumericRuntime.parseWeights xs)) :=
    inputWidthWordProgram.fanout QMCNumericRuntime.rawWeightsProgram
  let reqProg : PolyProgram QuantumMaxCutEnergy.encodeRequest
      (encodePair Nat.bits (encodeList Ratio.encode))
      (fun r : QuantumMaxCutEnergy.Input × List Bool =>
        (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest r),
          QMCNumericRuntime.parseWeights (QuantumMaxCutEnergy.encodeRequest r))) :=
    wordProg.recode QuantumMaxCutEnergy.encodeRequest (fun _ => rfl) (fun _ => rfl)
  (PolyProgram.fst QuantumMaxCutEnergy.encodeRequest Ratio.encode).comp reqProg |>.fanout
    (PolyProgram.snd QuantumMaxCutEnergy.encodeRequest Ratio.encode)

/-- **The decoded input with the order is a `Poly` function.**  This is the `hdecode` of §3b at
`δ = (ℕ × List ℚ) × ℚ`, for a driver whose packing needs `n`. -/
theorem decodedWithOrder_poly :
    Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => decodedWithOrder p.1.1 p.2) := by
  have hparsed : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        ((QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1),
          QMCNumericRuntime.parseWeights (QuantumMaxCutEnergy.encodeRequest p.1)), p.2)) :=
    ⟨parsedWithOrderProgram⟩
  refine QMCLeafB.FinishLine.poly_of_pointwise hparsed ?_
  intro p
  rw [QMCNumericRuntime.inputWidth_request, weightsOf_parseWeights]
  rfl

/-- **The order is tape-free**: `n = inputWidth (encodeRequest (G, coins))` for every tape. -/
theorem decodedWithOrder_eq (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    decodedWithOrder G t
      = ((QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest (G, coins)),
          QMCNumericRuntime.parseWeights (QuantumMaxCutEnergy.encodeRequest (G, coins))), t) := by
  rw [QMCNumericRuntime.inputWidth_request, weightsOf_parseWeights]
  rfl

/-! ## 3d.  The canonical round count, and its squaring bound

`hspec` needs `(fuel p).length` to be *exactly* the tape-free count, i.e. the count must be under the
squaring bound `L^(2^k)` at the input's own request word (`Fuel.fuelTake_length_of_le`).  This is the
one place where the degenerate orders could bite: at `n ≤ 1` the request word is `[false] ++ tape`, so
with an empty tape the bound reads `count ≤ 1`.  The fix is to make the count collapse on those
inputs, which costs nothing — the analysis never runs there (`soundAt_of_le_one`).

§3d gives the canonical count `if n ≤ 1 then 1 else C (n+1)^d` on the decoded input that carries the
order, proves it `Poly`, and proves the squaring bound from `d + C ≤ 2^k`
(`Fuel.mul_pow_le_fuel_length` for `n ≥ 2`, the trivial `1 ≤ L^(2^k)` for `n ≤ 1`). -/

/-- `x ↦ x^d` is a `Poly` function of `ℕ`: `d` multiplications, no search. -/
theorem nat_pow_poly (d : ℕ) : Automatic.Poly (fun x : ℕ => x ^ d) := by
  induction d with
  | zero =>
      have h : (fun x : ℕ => x ^ 0) = fun _ => 1 := by funext x; simp
      rw [h]
      exact Automatic.Poly.const 1
  | succ e ih =>
      have h : (fun x : ℕ => x ^ (e + 1)) = fun x => x * x ^ e := by
        funext x
        rw [Nat.pow_succ']
      rw [h]
      exact Automatic.Poly.comp Automatic.Poly.nat_mul
        (Automatic.Poly.pair Automatic.Poly.identity ih)

/-- `x ↦ C (x+1)^d` is a `Poly` function of `ℕ`. -/
theorem nat_monomial_poly (C d : ℕ) :
    Automatic.Poly (fun x : ℕ => C * (x + 1) ^ d) := by
  have hinner : Automatic.Poly (fun x : ℕ => x + 1) :=
    Automatic.Poly.comp (f := fun y : ℕ × ℕ => y.1 + y.2) (g := fun x : ℕ => (x, 1))
      Automatic.Poly.nat_add
      (Automatic.Poly.pair Automatic.Poly.identity (Automatic.Poly.const 1))
  exact Automatic.Poly.comp (f := fun y : ℕ × ℕ => y.1 * y.2)
    (g := fun x : ℕ => (C, (x + 1) ^ d))
    Automatic.Poly.nat_mul
    (Automatic.Poly.pair (Automatic.Poly.const C)
      (Automatic.Poly.comp (f := fun x : ℕ => x ^ d) (g := fun x : ℕ => x + 1)
        (nat_pow_poly d) hinner))

/-- **The canonical round count** at a decoded input carrying the order: one round on the degenerate
orders, the monomial `C (n+1)^d` otherwise. -/
def countWithOrder (C d : ℕ) (x : (ℕ × List ℚ) × ℚ) : ℕ :=
  if x.1.1 ≤ 1 then 1 else C * (x.1.1 + 1) ^ d

/-- The order is a `Poly` function of the decoded input. -/
theorem poly_order : Automatic.Poly (fun x : (ℕ × List ℚ) × ℚ => x.1.1) :=
  Automatic.Poly.comp (f := (Prod.fst : ℕ × List ℚ → ℕ))
    (g := (Prod.fst : (ℕ × List ℚ) × ℚ → ℕ × List ℚ))
    Automatic.Poly.fst Automatic.Poly.fst

/-- **The canonical count is a `Poly` function** of the decoded input. -/
theorem poly_countWithOrder (C d : ℕ) :
    Automatic.Poly (fun x : (ℕ × List ℚ) × ℚ => countWithOrder C d x) := by
  have htest : Automatic.Poly (fun x : (ℕ × List ℚ) × ℚ => decide (x.1.1 ≤ 1)) :=
    Automatic.Poly.nat_le_comp poly_order (Automatic.Poly.const 1)
  have hmono : Automatic.Poly
      (fun x : (ℕ × List ℚ) × ℚ => C * (x.1.1 + 1) ^ d) :=
    Automatic.Poly.comp (f := fun m : ℕ => C * (m + 1) ^ d)
      (g := fun x : (ℕ × List ℚ) × ℚ => x.1.1)
      (nat_monomial_poly C d) poly_order
  exact Automatic.Poly.ite_prop htest (Automatic.Poly.const 1) hmono

/-- **The squaring bound at the canonical count.**  The degenerate orders are the reason for the
`if`; for `n ≥ 2` this is `Fuel.mul_pow_le_fuel_length` verbatim. -/
theorem hTle_countWithOrder (k C d : ℕ) (hkd : d + C ≤ 2 ^ k)
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    countWithOrder C d (decodedWithOrder p.1.1 p.2)
      ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 ^ k := by
  have hL1 : 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length := by
    rw [QMCNumericRuntime.request_encoding]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  by_cases hn : (p.1.1).n ≤ 1
  · have h1 : countWithOrder C d (decodedWithOrder p.1.1 p.2) = 1 := by
      simp [countWithOrder, decodedWithOrder, hn]
    rw [h1]
    exact Nat.succ_le_of_lt (pow_pos (by omega) _)
  · have hn2 : 2 ≤ (p.1.1).n := by omega
    have h2 : countWithOrder C d (decodedWithOrder p.1.1 p.2) = C * ((p.1.1).n + 1) ^ d := by
      simp [countWithOrder, decodedWithOrder, hn]
    rw [h2]
    have h := QMCLeafB.Fuel.mul_pow_le_fuel_length k C d p hkd hn2
    rwa [QMCLeafB.Fuel.fuel_length] at h

/-- **The closing stroke at the canonical count.**  Everything about `o`, `hspec`, the fuel and the
count is discharged: the driver supplies `σ`, the packing `pack : (ℕ × List ℚ) × ℚ → σ`, the round,
the verdict, the size accounting, the exponents `C d` with `d + C ≤ 2^k`, and the run bundle `hd` at
the pinned `o`. -/
theorem solution_of_loop_via_orderCount {σ : Type} [Coding σ]
    (pack : (ℕ × List ℚ) × ℚ → σ)
    (hpack : Automatic.Poly pack)
    (round : σ → σ) (verdict : σ → Bool)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (k C d : ℕ) (hkd : d + C ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → QMCLeafB.VerdictSound.RunData
        (runBitD decodedWithOrder pack round verdict (countWithOrder C d)) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_loop_via_iterateD decodedWithOrder pack decodedWithOrder_poly hpack round verdict
    hr hv sizes hsize hsize0 k (countWithOrder C d) (poly_countWithOrder C d)
    (hTle_countWithOrder k C d hkd) hd

/-! ## 3e.  The fuel-length slot in the shape the integration asks for

`FinalStroke.endgame_of_parts` (`Check_final_stroke_m7`) asks for

    hfuelLen : ∀ p, (fuel p).length = T0 p.1.1 p.2

with `T0 : Input → ℚ → ℕ` the run's round count.  §3e supplies that slot *closed*, for
`fuel := Fuel.fuelTake k (fun p => T0 p.1.1 p.2)`: the only obligation on `T0` is a bound.  Three
forms, weakest hypothesis first.

The clean one has no degenerate-order exception at all: `T0 G t ≤ (G.n + 1) ^ (2^k)`, because the
request word is at least `n+1` bits long (`succ_n_le_request_length`) and the fuel is `k` squarings of
it.  A plain monomial `C (n+1)^d` with `d + C ≤ 2^k` is *not* enough on its own: at `n = 0` the
request word is `[false] ++ tape`, so with an empty tape the bound would read `C ≤ 1`.  The real
count `K G * (4 n²)` is `0` at `n = 0`, which is why it escapes; §3e records the precise safe
condition (`T0 ≤ 1` on the degenerate orders). -/

/-- **The fuel length from a `(n+1)^(2^k)` bound.**  No exception for degenerate orders: the request
word starts with the unary order, so `n + 1 ≤ (encodeRequest (G, coins)).length` for every tape. -/
theorem hTle_of_succ_pow (k : ℕ) (Tof : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), Tof G t ≤ (G.n + 1) ^ 2 ^ k)
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    Tof p.1.1 p.2 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 ^ k :=
  (hT p.1.1 p.2).trans
    (Nat.pow_le_pow_left (QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2) _)

/-- **The fuel length from a monomial bound, with the degenerate orders handled separately.**  This is
the form for a count of the shape `K G * m G` with `K G * m G ≤ C (n+1)^d` for `n ≥ 2` and `≤ 1` at
`n ≤ 1`. -/
theorem hTle_of_monomial_of_small (k C d : ℕ) (hkd : d + C ≤ 2 ^ k)
    (Tof : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Tof G t ≤ C * (G.n + 1) ^ d)
    (hsmall : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), G.n ≤ 1 → Tof G t ≤ 1)
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    Tof p.1.1 p.2 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 ^ k := by
  refine hTle_of_succ_pow k Tof (fun G t => ?_) p
  by_cases hn : G.n ≤ 1
  · have h1 : Tof G t ≤ 1 := hsmall G t hn
    have h2 : 1 ≤ (G.n + 1) ^ 2 ^ k := Nat.one_le_pow (2 ^ k) (G.n + 1) (by omega)
    omega
  · have hn2 : 2 ≤ G.n := by omega
    have hn1 : 2 ≤ G.n + 1 := by omega
    have hC : C ≤ (G.n + 1) ^ C :=
      (le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left hn1 C)
    calc Tof G t ≤ C * (G.n + 1) ^ d := hT G t hn2
      _ ≤ (G.n + 1) ^ C * (G.n + 1) ^ d := Nat.mul_le_mul_right _ hC
      _ = (G.n + 1) ^ (C + d) := (Nat.pow_add _ _ _).symm
      _ ≤ (G.n + 1) ^ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)

/-- **`hfuelLen`: the exact-length slot of `endgame_of_parts`**, at `fuel := Fuel.fuelTake k T` and
`T0` of the shape §3e controls.  This is the slot verbatim, so the integration names it. -/
theorem hfuelLen_of_monomial_of_small (k C d : ℕ) (hkd : d + C ≤ 2 ^ k)
    (Tof : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Tof G t ≤ C * (G.n + 1) ^ d)
    (hsmall : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), G.n ≤ 1 → Tof G t ≤ 1) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (QMCLeafB.Fuel.fuelTake k (fun p => Tof p.1.1 p.2) p).length = Tof p.1.1 p.2 :=
  fun p => QMCLeafB.Fuel.fuelTake_length_of_le k _ p (hTle_of_monomial_of_small k C d hkd Tof hT hsmall p)

/-- **`hfuelLen` from the `(n+1)^(2^k)` bound** — the degenerate-free form. -/
theorem hfuelLen_of_succ_pow (k : ℕ) (Tof : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), Tof G t ≤ (G.n + 1) ^ 2 ^ k) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (QMCLeafB.Fuel.fuelTake k (fun p => Tof p.1.1 p.2) p).length = Tof p.1.1 p.2 :=
  fun p => QMCLeafB.Fuel.fuelTake_length_of_le k _ p (hTle_of_succ_pow k Tof hT p)

/-! ## 3f.  The order is `Poly`, and the canonical count `K·m = C (n+1)^d · 4 n²` closed

The run's round count that the integration can actually use is `T0 G t = K G * m G` with `K` above
the volume budget and `m = 4 n²` the halving time (`ClosingBracket.runData_hhalve_close` is stated at
`rmax = 0`, `m = 4 * (n*n)`).  §3f closes that count: the graph order is a `Poly` function of the
decider's input, the count `4 * (C (n+1)^d) * (n n)` is `Poly`, and it is under `(n+1)^(2^k)` as soon
as `4 + C + d ≤ 2^k` — hence its fuel has exactly that length (§3e). -/

/-- The order, read off the request word, as a program across the request coding. -/
noncomputable def orderOfRequestProgram :
    PolyProgram QuantumMaxCutEnergy.encodeRequest Nat.bits
      (fun r : QuantumMaxCutEnergy.Input × List Bool =>
        QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest r)) :=
  inputWidthWordProgram.recode QuantumMaxCutEnergy.encodeRequest (fun _ => rfl) (fun _ => rfl)

/-- **`G.n` is a `Poly` function of the decider's input** (`Input × List Bool`): the request word
starts with the unary order. -/
theorem orderOfInput_poly :
    Automatic.Poly (fun r : QuantumMaxCutEnergy.Input × List Bool => r.1.n) :=
  QMCLeafB.FinishLine.poly_of_pointwise ⟨orderOfRequestProgram⟩
    (fun r => by rw [QMCNumericRuntime.inputWidth_request])

/-- **`G.n` is a `Poly` function of `((Input × List Bool) × ℚ)`.** -/
theorem orderP_poly :
    Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => p.1.1.n) :=
  Automatic.Poly.comp (f := fun r : QuantumMaxCutEnergy.Input × List Bool => r.1.n)
    (g := (Prod.fst : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) →
      QuantumMaxCutEnergy.Input × List Bool))
    orderOfInput_poly Automatic.Poly.fst

/-- **The canonical round count** with `m = 4 n²`: `T0 G t = K G * m` at `K G = C (n+1)^d`.  (The
threshold `t` does not enter, which is what lets `o` be a function of `(G, t)` and the fuel a
function of `(G, tape)`.) -/
def roundCount (C d : ℕ) (G : QuantumMaxCutEnergy.Input) : ℕ :=
  4 * (C * (G.n + 1) ^ d) * (G.n * G.n)

/-- `x ↦ x * x` is `Poly`. -/
theorem nat_sq_poly : Automatic.Poly (fun n : ℕ => n * n) :=
  Automatic.Poly.comp (f := fun y : ℕ × ℕ => y.1 * y.2) (g := fun n : ℕ => (n, n))
    Automatic.Poly.nat_mul (Automatic.Poly.pair Automatic.Poly.identity Automatic.Poly.identity)

/-- **The canonical count is a `Poly` function.** -/
theorem poly_roundCount (C d : ℕ) :
    Automatic.Poly (fun n : ℕ => ((4 * C) * (n + 1) ^ d) * (n * n)) :=
  Automatic.Poly.comp (f := fun y : ℕ × ℕ => y.1 * y.2)
    (g := fun n : ℕ => ((4 * C) * (n + 1) ^ d, n * n))
    Automatic.Poly.nat_mul
    (Automatic.Poly.pair (nat_monomial_poly (4 * C) d) nat_sq_poly)

/-- **The count as a `Poly` function of the decider's input.** -/
theorem poly_roundCount_program (C d : ℕ) :
    Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      roundCount C d p.1.1) := by
  refine QMCLeafB.FinishLine.poly_of_pointwise
    (Automatic.Poly.comp (f := fun n : ℕ => ((4 * C) * (n + 1) ^ d) * (n * n))
      (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => p.1.1.n)
      (poly_roundCount C d) orderP_poly) ?_
  intro p
  simp only [roundCount]
  ring

/-- **The canonical count is under `(n+1)^(4+C+d)`.**  (At `n = 0` it is `0`; for `n ≥ 1` the four
factors `4`, `C`, `(n+1)^d`, `n·n` each sit under a power of `n+1`.) -/
theorem roundCount_le (C d : ℕ) (G : QuantumMaxCutEnergy.Input) :
    roundCount C d G ≤ (G.n + 1) ^ (4 + C + d) := by
  by_cases hn : G.n = 0
  · have h0 : G.n = 0 := hn
    simp only [roundCount, h0, Nat.mul_zero]
    exact Nat.zero_le _
  · have hn1 : 1 ≤ G.n := by omega
    have hn2 : 2 ≤ G.n + 1 := by omega
    have h4 : 4 ≤ (G.n + 1) ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ (G.n + 1) ^ 2 := Nat.pow_le_pow_left hn2 2
    have hC : C ≤ (G.n + 1) ^ C :=
      (le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left hn2 C)
    have hsq : G.n * G.n ≤ (G.n + 1) ^ 2 := by
      have h : (G.n + 1) ^ 2 = G.n * G.n + (2 * G.n + 1) := by ring
      rw [h]
      omega
    have hd : (G.n + 1) ^ d ≤ (G.n + 1) ^ d := le_rfl
    calc roundCount C d G = 4 * C * (G.n + 1) ^ d * (G.n * G.n) := by
          simp only [roundCount]; ring
      _ ≤ (G.n + 1) ^ 2 * (G.n + 1) ^ C * (G.n + 1) ^ d * (G.n + 1) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h4 hC) hd) hsq
      _ = (G.n + 1) ^ (4 + C + d) := by
          rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
          congr 1
          omega

/-- **The canonical count is under `(n+1)^(2^k)`** as soon as `4 + C + d ≤ 2^k`. -/
theorem roundCount_le_succ_pow (k C d : ℕ) (hkd : 4 + C + d ≤ 2 ^ k)
    (G : QuantumMaxCutEnergy.Input) :
    roundCount C d G ≤ (G.n + 1) ^ 2 ^ k :=
  (roundCount_le C d G).trans (Nat.pow_le_pow_right (by omega) hkd)

/-- **`hfuelLen` at the canonical count** — the slot of `FinalStroke.endgame_of_parts` verbatim, for
`T0 := fun G _ => roundCount C d G` and `fuel := Fuel.fuelTake k (fun p => roundCount C d p.1.1)`. -/
theorem hfuelLen_roundCount (k C d : ℕ) (hkd : 4 + C + d ≤ 2 ^ k) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (QMCLeafB.Fuel.fuelTake k (fun p => roundCount C d p.1.1) p).length
        = roundCount C d p.1.1 :=
  fun p => QMCLeafB.Fuel.fuelTake_length_of_le k (fun p => roundCount C d p.1.1) p
    (hTle_of_succ_pow k (fun G _ => roundCount C d G)
      (fun G _ => roundCount_le_succ_pow k C d hkd G) p)

/-! ## 3g.  Overshooting fuel: `hspec` does **not** need the exact round count

§3e/§3f make the fuel length *equal* the round count, which forces the count to be a `Poly` function.
That is a strong requirement, and it is not necessary.  The run's verdict is `SimLoop.anyOk` of the
recorded `ok` bits (`InitVerdict` §2b, `SimLoop.anyOk`), which is *stable* once no further round
reports `ok`: extra rounds that record `false` cannot change it.  So the fuel may be any `Poly` list
that is merely **long enough**:

    Tstar G t ≤ (fuel p).length   and   every round `k ≥ Tstar G t` records `false`
      ⟹  verdict after `(fuel p).length` rounds = verdict after `Tstar G t` rounds.

`Tstar` need not be `Poly` at all (`RunData`'s `K * m` is a `clog`-based budget, which no `Poly`
program can compute) — it is only the number `o` is defined with.  The fuel can then be the
*untruncated* `Fuel.fuel k`, whose length `L^(2^k)` is tape-dependent, which is now harmless. -/

/-- `anyOk` is stable under appending rounds that all report `false`. -/
theorem anyOk_congr_of_false (ok : ℕ → Bool) {T T' : ℕ} (hT : T ≤ T')
    (hfalse : ∀ k, T ≤ k → k < T' → ok k = false) :
    QMCLeafB.SimLoop.anyOk ok T' = QMCLeafB.SimLoop.anyOk ok T := by
  apply Bool.eq_iff_iff.mpr
  rw [QMCLeafB.SimLoop.anyOk_eq_true_iff, QMCLeafB.SimLoop.anyOk_eq_true_iff]
  constructor
  · rintro ⟨k, hk, hok⟩
    refine ⟨k, ?_, hok⟩
    by_contra hkT
    have hk' : T ≤ k := by omega
    rw [hfalse k hk' hk] at hok
    exact Bool.noConfusion hok
  · rintro ⟨k, hk, hok⟩
    exact ⟨k, by omega, hok⟩

/-- **`hspec` from an overshooting fuel and a stable run.**  `Tstar` is the count `o` is defined
with; the fuel only has to reach it, and the run must record `false` from `Tstar` on. -/
theorem hspec_of_overshoot {σ : Type} [Coding σ]
    (inits : QuantumMaxCutEnergy.Input → ℚ → σ)
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool) (Tstar : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), init p = inits p.1.1 p.2)
    (hTle : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), Tstar p.1.1 p.2 ≤ (fuel p).length)
    (hstab : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (T : ℕ), Tstar G t ≤ T →
      verdict (round^[T] (inits G t)) = verdict (round^[Tstar G t] (inits G t))) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (round^[(fuel p).length] (init p))
        = runBit inits round verdict Tstar p.1.1 p.2 := by
  intro p
  rw [hinitTape p]
  exact hstab p.1.1 p.2 (fuel p).length (hTle p)

/-- **`hspec` from an overshooting fuel, with the stability supplied by the run's `ok` record.**
This is the form for the `InitVerdict` state machine: `okOf s` is the bit round `s` records,
`hreadout` is `InitVerdict`'s readout (`verdict` after `T` rounds is `anyOk` of the bits), and
`hfalse` says the run stops reporting `ok` after `Tstar`. -/
theorem hspec_of_stable_ok {σ : Type} [Coding σ]
    (inits : QuantumMaxCutEnergy.Input → ℚ → σ)
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool) (okOf : σ → Bool)
    (Tstar : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), init p = inits p.1.1 p.2)
    (hreadout : ∀ (s : σ) (T : ℕ),
      verdict (round^[T] s) = QMCLeafB.SimLoop.anyOk (fun k => okOf (round^[k] s)) T)
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ),
      Tstar G t ≤ k → okOf (round^[k] (inits G t)) = false)
    (hTle : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), Tstar p.1.1 p.2 ≤ (fuel p).length) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (round^[(fuel p).length] (init p))
        = runBit inits round verdict Tstar p.1.1 p.2 := by
  refine hspec_of_overshoot inits init fuel round verdict Tstar hinitTape hTle (fun G t T hT => ?_)
  rw [hreadout (inits G t) T, hreadout (inits G t) (Tstar G t)]
  refine anyOk_congr_of_false (ok := fun k => okOf (round^[k] (inits G t))) hT (fun k hk _ => ?_)
  exact hfalse G t k hk

/-- **The fuel length from a monomial in the request word's length.**  With an overshooting fuel the
count need not be `Poly`, but it must still be under `L^(2^k)` (the length of `Fuel.fuel k`).  A
monomial `C (L+1)^d` is, as soon as `C + 2d ≤ 2^k`; the degenerate input `L = 1` (the empty graph
with an empty tape) is the one case to check by hand. -/
theorem hTle_fuel_of_length_monomial (k C d : ℕ) (hkd : C + 2 * d ≤ 2 ^ k)
    (Tstar : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ)
    (hT : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      Tstar p ≤ C * ((QuantumMaxCutEnergy.encodeRequest p.1).length + 1) ^ d)
    (hsmall : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (QuantumMaxCutEnergy.encodeRequest p.1).length = 1 → Tstar p ≤ 1)
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    Tstar p ≤ (QMCLeafB.Fuel.fuel k p).length := by
  have hL1 : 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length := by
    rw [QMCNumericRuntime.request_encoding]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  rw [QMCLeafB.Fuel.fuel_length]
  rcases Nat.lt_or_ge (QuantumMaxCutEnergy.encodeRequest p.1).length 2 with h2 | h2
  · have hLeq : (QuantumMaxCutEnergy.encodeRequest p.1).length = 1 := by omega
    refine (hsmall p hLeq).trans ?_
    rw [hLeq, Nat.one_pow]
  · -- `L ≥ 2`: `C ≤ L^C`, `(L+1)^d ≤ L^(2d)`
    have hC : C ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ C := by
      rcases Nat.eq_zero_or_pos C with h0 | h0
      · rw [h0]
        exact Nat.zero_le _
      · exact (le_of_lt Nat.lt_two_pow_self).trans
          (Nat.pow_le_pow_left (by omega : 2 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length) C)
    have hbase : (QuantumMaxCutEnergy.encodeRequest p.1).length + 1
        ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length
          * (QuantumMaxCutEnergy.encodeRequest p.1).length := by nlinarith
    have hd : ((QuantumMaxCutEnergy.encodeRequest p.1).length + 1) ^ d
        ≤ ((QuantumMaxCutEnergy.encodeRequest p.1).length
            * (QuantumMaxCutEnergy.encodeRequest p.1).length) ^ d :=
      Nat.pow_le_pow_left hbase d
    calc Tstar p
        ≤ C * ((QuantumMaxCutEnergy.encodeRequest p.1).length + 1) ^ d := hT p
      _ ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ C
            * ((QuantumMaxCutEnergy.encodeRequest p.1).length
              * (QuantumMaxCutEnergy.encodeRequest p.1).length) ^ d :=
          Nat.mul_le_mul hC hd
      _ = (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (C + 2 * d) := by
          rw [Nat.mul_pow]
          ring_nf
      _ ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 ^ k :=
          Nat.pow_le_pow_right (by omega) hkd

/-! ## 3h.  A `Poly`-computable count that grows with the *values* of the weights

A count written as a monomial in the order `n` is too small: `RunData.hbudget` needs
`volPot · (1/2)^K < δ^{n²}` at `δ = dq/(8(cAq+1))`, so `K ≳ n² log(1/(1+Rq))` — and `log Rq` is
unbounded at fixed `n` (a weight can have a million-bit numerator).  What the `Nat.clog` estimate
needs is a `Poly`-computable quantity comparable to `n² · log(1+Rq)`: the **bit cost** of `Rq`,

    bitCost q = Nat.size q.num.natAbs + Nat.size q.den + 1,

the number of input bits that describe the rational.  §3h proves it is a `Poly` function of the
decider's input (`Rq` is, by `Check_brick_rq_program.Rq_poly_req`) and the inequalities the estimate
consumes: `Rq G + 1 ≤ 2 ^ bitCost (Rq G)` and `(Rq G + 1)^e ≤ 2 ^ (bitCost (Rq G) * e)`.

The estimate `budgetRounds ≤ C (n+1)^d · bitCost (Rq G)` is *not* here: it is the `Nat.clog`/`Real.log`
step, which the round-count brick (`Check_roundcount_m2`) owns. -/

/-- **The bit cost of a rational**: numerator bits + denominator bits + 1.  The `+ 1` makes it
strictly positive, so it can be used as a factor of a round count. -/
def bitCost (q : ℚ) : ℕ := Nat.size q.num.natAbs + Nat.size q.den + 1

/-- `q ↦ (q.num, q.den)` is `Poly` (the ratio encoding is the pair of the two components). -/
theorem poly_ratParts : Automatic.Poly (fun q : ℚ => (q.num, q.den)) :=
  ⟨PolyProgram.ratNum.fanout PolyProgram.ratDen⟩

/-- **The bit cost is a `Poly` function of the rational.** -/
theorem poly_bitCost : Automatic.Poly (fun q : ℚ => bitCost q) := by
  have hnum : Automatic.Poly (fun q : ℚ => Nat.size q.num.natAbs) :=
    Automatic.Poly.comp (f := (Nat.size : ℕ → ℕ)) (g := fun q : ℚ => q.num.natAbs)
      (Automatic.Poly.of_program PolyProgram.natSize)
      (Automatic.Poly.comp (f := (Int.natAbs : ℤ → ℕ)) (g := fun q : ℚ => q.num)
        (Automatic.Poly.of_program PolyProgram.intAbs)
        (Automatic.Poly.of_program PolyProgram.ratNum))
  have hden : Automatic.Poly (fun q : ℚ => Nat.size q.den) :=
    Automatic.Poly.comp (f := (Nat.size : ℕ → ℕ)) (g := fun q : ℚ => q.den)
      (Automatic.Poly.of_program PolyProgram.natSize)
      (Automatic.Poly.of_program PolyProgram.ratDen)
  have hsum : Automatic.Poly (fun q : ℚ => Nat.size q.num.natAbs + Nat.size q.den + 1) := by
    have h2 : Automatic.Poly
        (fun q : ℚ => (Nat.size q.num.natAbs + Nat.size q.den, 1)) :=
      Automatic.Poly.pair
        (Automatic.Poly.comp (f := fun y : ℕ × ℕ => y.1 + y.2)
          (g := fun q : ℚ => (Nat.size q.num.natAbs, Nat.size q.den))
          Automatic.Poly.nat_add (Automatic.Poly.pair hnum hden))
        (Automatic.Poly.const 1)
    exact Automatic.Poly.comp (f := fun y : ℕ × ℕ => y.1 + y.2)
      (g := fun q : ℚ => (Nat.size q.num.natAbs + Nat.size q.den, 1))
      Automatic.Poly.nat_add h2
  exact hsum

/-- **The bit cost of `Rq` is a `Poly` function of the decider's input.**  (`Rq` itself is one:
`Check_brick_rq_program.Rq_poly_req`.) -/
theorem poly_bitCostRq :
    Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      bitCost (QMCLeafB.EngineRuntime.Rq p.1.1)) := by
  have hRq : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        QMCLeafB.EngineRuntime.Rq p.1.1) :=
    Automatic.Poly.comp
      (f := fun a : QuantumMaxCutEnergy.Input × List Bool => QMCLeafB.EngineRuntime.Rq a.1)
      (g := (Prod.fst : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) →
        QuantumMaxCutEnergy.Input × List Bool))
      QMCLeafB.BrickRQ.Rq_poly_req Automatic.Poly.fst
  exact Automatic.Poly.comp (f := bitCost)
    (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QMCLeafB.EngineRuntime.Rq p.1.1)
    poly_bitCost hRq

/-- **`Rq + 1 ≤ 2 ^ bitCost Rq`**: the value of the total weight is under `2` to its own bit cost.
This is the step that turns `log (1 + Rq)` into an exponent a `Poly` program can compute. -/
theorem rat_add_one_le_two_pow_bitCost (q : ℚ) (hq0 : (0 : ℚ) ≤ q) :
    q + 1 ≤ (2 : ℚ) ^ bitCost q := by
  have hden1 : (1 : ℚ) ≤ (q.den : ℚ) := by
    have := q.den_pos
    exact_mod_cast this
  have hden0 : (0 : ℚ) < (q.den : ℚ) := by
    have := q.den_pos
    exact_mod_cast this
  have hq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
  have hnum0 : (0 : ℚ) ≤ (q.num : ℚ) := by
    have hq0' : (0 : ℚ) ≤ (q.num : ℚ) / (q.den : ℚ) := by rw [← hq]; exact hq0
    rcases (div_nonneg_iff.mp hq0') with ⟨h, -⟩ | ⟨h, hd'⟩
    · exact h
    · exfalso; linarith
  have hnatAbs : (q.num : ℚ) ≤ (q.num.natAbs : ℚ) := by
    have h : q.num ≤ ((q.num.natAbs : ℤ)) := Int.le_natAbs
    have h2 : ((q.num : ℤ) : ℚ) ≤ (((q.num.natAbs : ℤ)) : ℚ) := by exact_mod_cast h
    simpa using h2
  have hle : q ≤ (q.num.natAbs : ℚ) := by
    calc q = (q.num : ℚ) / (q.den : ℚ) := hq
      _ ≤ (q.num : ℚ) := by
          rw [div_le_iff₀ hden0]
          nlinarith
      _ ≤ (q.num.natAbs : ℚ) := hnatAbs
  have hsize : q.num.natAbs + 1 ≤ 2 ^ Nat.size q.num.natAbs :=
    Nat.succ_le_of_lt (Nat.lt_size_self _)
  calc q + 1 ≤ (q.num.natAbs : ℚ) + 1 := by linarith
    _ = ((q.num.natAbs + 1 : ℕ) : ℚ) := by push_cast; ring
    _ ≤ ((2 ^ Nat.size q.num.natAbs : ℕ) : ℚ) := by exact_mod_cast hsize
    _ ≤ ((2 ^ bitCost q : ℕ) : ℚ) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by
          simp only [bitCost]
          omega)
    _ = (2 : ℚ) ^ bitCost q := by push_cast; ring

/-- **`Rq + 1 ≤ 2 ^ bitCost Rq`** at the graph's total weight (the case used by the count). -/
theorem Rq_add_one_le_two_pow_bitCost (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.EngineRuntime.Rq G + 1
      ≤ (2 : ℚ) ^ bitCost (QMCLeafB.EngineRuntime.Rq G) :=
  rat_add_one_le_two_pow_bitCost _ (QMCLeafB.EngineRuntime.Rq_nonneg G)

/-- **The power form**: `(Rq + 1)^e` is under `2 ^ (bitCost Rq * e)`. -/
theorem Rq_add_one_pow_le_two_pow (G : QuantumMaxCutEnergy.Input) (e : ℕ) :
    (QMCLeafB.EngineRuntime.Rq G + 1) ^ e
      ≤ (2 : ℚ) ^ (bitCost (QMCLeafB.EngineRuntime.Rq G) * e) := by
  calc (QMCLeafB.EngineRuntime.Rq G + 1) ^ e
      ≤ ((2 : ℚ) ^ bitCost (QMCLeafB.EngineRuntime.Rq G)) ^ e :=
        pow_le_pow_left₀ (by linarith [QMCLeafB.EngineRuntime.Rq_nonneg G])
          (Rq_add_one_le_two_pow_bitCost G) e
    _ = (2 : ℚ) ^ (bitCost (QMCLeafB.EngineRuntime.Rq G) * e) := by
        rw [← pow_mul]

/-! ## 3i.  `bitCost (Rq G)` is linear in the input length

The count of §3h is only usable if it is under the fuel length `L^(2^k)`, `L` the request word's
length.  `bitCost` counts the *bits of the total weight's numerator and denominator*, and a sum of
`n(n-1)/2` weights can have a denominator as long as the product of all denominators — so the bound
is not `bitCost ≤ L` but `bitCost ≤ C·L`, which is more than enough.  §3i proves it from the
library's own `HasHeight` accounting (`Ratio.height_length`, `HasHeight.foldAdd`,
`Ratio.length_height`):

    bitCost (Rq G) ≤ 24 * (encodeInput G).length + 16.

The constant is irrelevant (the fuel gives `L^(2^k)` with `2^k ≥ 6`); what matters is that the bound
is *linear*, so `C (n+1)^d (bitCost (Rq G) + 1) ≤ L^(2^k)` for any fixed exponents. -/

/-- `encodeWeights` is the flatMap of the two `encodeNumber`s. -/
theorem encodeWeights_eq (ws : List ℚ≥0) :
    QMCNumericRuntime.encodeWeights ws
      = ws.flatMap (fun q => QuantumMaxCutEnergy.encodeNumber q.num ++
          QuantumMaxCutEnergy.encodeNumber q.den) := rfl

/-- `encodeNumber`'s length: two copies of the bit length plus the separator. -/
theorem encodeNumber_length (m : ℕ) :
    (QuantumMaxCutEnergy.encodeNumber m).length = 2 * Nat.size m + 1 := by
  have hbits : (Computability.encodeNat m).length = Nat.size m := by
    rw [QMCNumericRuntime.encodeNat_eq_bits, Nat.size_eq_bits_len]
  simp only [QuantumMaxCutEnergy.encodeNumber, hbits, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- `Ratio.encode`'s length in terms of `Nat.size`. -/
theorem encode_ratio_length (q : ℚ) :
    (Ratio.encode q).length = 7 + 2 * Nat.size q.num.natAbs + Nat.size q.den := by
  rw [Ratio.encode_length]
  simp only [Nat.size_eq_bits_len]

/-- **One weight costs at most twice its input bits.**  The input writes `num` and `den` as
`encodeNumber`s; the ratio encoding is `7 + 2·size num + size den`. -/
theorem encode_ratio_le (q : ℚ≥0) :
    (Ratio.encode (q : ℚ)).length
      ≤ 2 * ((QuantumMaxCutEnergy.encodeNumber q.num).length
        + (QuantumMaxCutEnergy.encodeNumber q.den).length) := by
  have hnum : ((q : ℚ).num.natAbs) = q.num := rfl
  have hden : ((q : ℚ).den) = q.den := rfl
  have hb : 1 ≤ Nat.size q.den := by
    have h : 0 < q.den := q.den_pos
    have := Nat.size_pos.mpr h
    omega
  rw [encode_ratio_length, hnum, hden, encodeNumber_length, encodeNumber_length]
  omega

/-- **The weight list's `Ratio.encode` word is at most `6×` its input block.** -/
theorem encodeList_flatMap_le (ws : List ℚ≥0) :
    (encodeList Ratio.encode (ws.map (fun q : ℚ≥0 => (q : ℚ)))).length
      ≤ 6 * (ws.flatMap (fun q => QuantumMaxCutEnergy.encodeNumber q.num ++
          QuantumMaxCutEnergy.encodeNumber q.den)).length + 2 * ws.length := by
  induction ws with
  | nil => simp only [List.map_nil, List.length_nil, EncodedList.nil, List.flatMap_nil, Nat.le_refl]
  | cons q ws ih =>
      have hq := encode_ratio_le q
      have h4 : 2 ≤ (QuantumMaxCutEnergy.encodeNumber q.num).length
          + (QuantumMaxCutEnergy.encodeNumber q.den).length := by
        have h1 := encodeNumber_length q.num
        have h2 := encodeNumber_length q.den
        omega
      have hde : (QuantumMaxCutEnergy.encodeNumber q.num
          ++ QuantumMaxCutEnergy.encodeNumber q.den).length
          = (QuantumMaxCutEnergy.encodeNumber q.num).length
            + (QuantumMaxCutEnergy.encodeNumber q.den).length := List.length_append
      rw [List.map_cons, EncodedList.cons_length, List.flatMap_cons, List.length_append,
        List.length_cons]
      omega

/-- `encodeList_weights_le` in `encodeWeights` form. -/
theorem encodeList_weights_le (ws : List ℚ≥0) :
    (encodeList Ratio.encode (ws.map (fun q : ℚ≥0 => (q : ℚ)))).length
      ≤ 6 * (QMCNumericRuntime.encodeWeights ws).length + 2 * ws.length := by
  rw [encodeWeights_eq]
  exact encodeList_flatMap_le ws

/-- The weights block sits inside the graph encoding. -/
theorem encodeWeights_le_encodeInput (G : QuantumMaxCutEnergy.Input) :
    (QMCNumericRuntime.encodeWeights (QMCNumericRuntime.weightsList G)).length
      ≤ (QuantumMaxCutEnergy.encodeInput G).length := by
  have hew : (QMCNumericRuntime.encodeWeights (QMCNumericRuntime.weightsList G)).length
      = ((QMCNumericRuntime.weightsList G).flatMap (fun q =>
          QuantumMaxCutEnergy.encodeNumber q.num
            ++ QuantumMaxCutEnergy.encodeNumber q.den)).length := by rw [encodeWeights_eq]
  rw [hew, QMCNumericRuntime.encoding_weightsList]
  have h : (List.replicate G.n true ++ [false] ++
      (QMCNumericRuntime.weightsList G).flatMap (fun q =>
        QuantumMaxCutEnergy.encodeNumber q.num ++ QuantumMaxCutEnergy.encodeNumber q.den)).length
      = G.n + 1 + ((QMCNumericRuntime.weightsList G).flatMap (fun q =>
        QuantumMaxCutEnergy.encodeNumber q.num
          ++ QuantumMaxCutEnergy.encodeNumber q.den)).length := by
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  rw [h]
  omega

/-- Each weight costs at least one bit of the graph encoding. -/
theorem weightsList_length_le_encodeInput (G : QuantumMaxCutEnergy.Input) :
    (QMCNumericRuntime.weightsList G).length ≤ (QuantumMaxCutEnergy.encodeInput G).length := by
  have hflat : (QMCNumericRuntime.weightsList G).length
      ≤ (QMCNumericRuntime.encodeWeights (QMCNumericRuntime.weightsList G)).length := by
    rw [encodeWeights_eq, List.length_flatMap]
    have hone : (QMCNumericRuntime.weightsList G).length
        = ((QMCNumericRuntime.weightsList G).map (fun _ => 1)).sum := by simp
    rw [hone]
    apply List.sum_le_sum
    intro q _
    rw [List.length_append]
    have h3 := encodeNumber_length q.num
    have h4 := encodeNumber_length q.den
    omega
  have h2 := encodeWeights_le_encodeInput G
  omega

/-- `bitCost` is under the word length of the ratio encoding. -/
theorem bitCost_le_encode (q : ℚ) : bitCost q ≤ (Ratio.encode q).length := by
  rw [encode_ratio_length]
  simp only [bitCost]
  omega

/-- **A weight list's rational sum has height at most its `Ratio.encode` word length** — the
library's fold accounting (`HasHeight.foldAdd`). -/
theorem HasHeight_map_sum (ws : List ℚ≥0) :
    HasHeight ((ws.map (fun q : ℚ≥0 => (q : ℚ))).sum)
      ((encodeList Ratio.encode (ws.map (fun q : ℚ≥0 => (q : ℚ)))).length) := by
  have h := HasHeight.foldAdd (ws.map (fun q : ℚ≥0 => (q : ℚ))) 0 0 (HasHeight.zero 0)
  rw [OAI.MetricKMedian.Binary.ListAlgorithms.foldAdd] at h
  simpa using h

/-- **The height of `2 · Σ weights`**: the factor `2` costs two bits. -/
theorem HasHeight_two_mul_map_sum (ws : List ℚ≥0) :
    HasHeight (2 * (ws.map (fun q : ℚ≥0 => (q : ℚ))).sum)
      ((encodeList Ratio.encode (ws.map (fun q : ℚ≥0 => (q : ℚ)))).length + 2) := by
  have h2 : HasHeight (2 : ℚ) 2 := by
    constructor <;> norm_num [HasHeight]
  have hmul := h2.mul (HasHeight_map_sum ws)
  exact hmul.mono (by omega)

/-- **`bitCost (2 Σ weights)` is linear in the input block.** -/
theorem bitCost_two_mul_map_sum_le (ws : List ℚ≥0) :
    bitCost (2 * (ws.map (fun q : ℚ≥0 => (q : ℚ))).sum)
      ≤ 24 * (QMCNumericRuntime.encodeWeights ws).length + 24 * ws.length + 16 := by
  have hh := HasHeight_two_mul_map_sum ws
  have henc := Ratio.length_height hh
  have hbit := bitCost_le_encode (2 * (ws.map (fun q : ℚ≥0 => (q : ℚ))).sum)
  have hL := encodeList_weights_le ws
  linarith

/-- **`bitCost (Rq G)` is linear in the graph's encoded length.** -/
theorem bitCost_Rq_le (G : QuantumMaxCutEnergy.Input) :
    bitCost (QMCLeafB.EngineRuntime.Rq G)
      ≤ 48 * (QuantumMaxCutEnergy.encodeInput G).length + 16 := by
  rw [QMCLeafB.BrickRQ.Rq_eq_two_weightsList]
  have h := bitCost_two_mul_map_sum_le (QMCNumericRuntime.weightsList G)
  have hW := encodeWeights_le_encodeInput G
  have hK := weightsList_length_le_encodeInput G
  linarith

/-! ## 3j.  The count `C (n+1)^d (bitCost (Rq G) + 1)`, and its squaring bound

This is the count the `Nat.clog` estimate should aim at (the `budgetRounds ≤ K` step): it is `Poly`
(§3h), it grows with `log (1 + Rq)` as `hbudget` requires, and §3j proves it is under the fuel's
`L^(2^k)` — the last thing the fuel slots of §3e/§3f need.  The degenerate orders `n ≤ 1` get one
round, and there the request word is at least one bit long. -/

/-- **The bit-cost round count**: one round on the degenerate orders, `C (n+1)^d (bitCost Rq + 1)`
otherwise.  Constant-free in the threshold, as `o` and the fuel require. -/
noncomputable def countWithBitCost (C d : ℕ) (G : QuantumMaxCutEnergy.Input) : ℕ :=
  if G.n ≤ 1 then 1 else C * (G.n + 1) ^ d * (bitCost (QMCLeafB.EngineRuntime.Rq G) + 1)

/-- The `Rq`-part of the bit-cost count is `Poly`. -/
theorem poly_bitCostRq_succ :
    Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1) :=
  Automatic.Poly.comp (f := fun m : ℕ => m + 1)
    (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      bitCost (QMCLeafB.EngineRuntime.Rq p.1.1))
    (Automatic.Poly.comp (f := fun y : ℕ × ℕ => y.1 + y.2) (g := fun m : ℕ => (m, 1))
      Automatic.Poly.nat_add (Automatic.Poly.pair Automatic.Poly.identity (Automatic.Poly.const 1)))
    poly_bitCostRq

/-- **The bit-cost count is a `Poly` function of the decider's input.** -/
theorem poly_countWithBitCost (C d : ℕ) :
    Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      countWithBitCost C d p.1.1) := by
  have htest : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => decide (p.1.1.n ≤ 1)) :=
    Automatic.Poly.nat_le_comp orderP_poly (Automatic.Poly.const 1)
  have hmono : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        C * (p.1.1.n + 1) ^ d * (bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1)) :=
    Automatic.Poly.comp (f := fun y : ℕ × ℕ => y.1 * y.2)
      (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        (C * (p.1.1.n + 1) ^ d, bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1))
      Automatic.Poly.nat_mul
      (Automatic.Poly.pair
        (Automatic.Poly.comp (f := fun n : ℕ => C * (n + 1) ^ d)
          (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => p.1.1.n)
          (nat_monomial_poly C d) orderP_poly)
        poly_bitCostRq_succ)
  exact Automatic.Poly.ite_prop htest (Automatic.Poly.const 1) hmono

/-- `48 L + 17 ≤ L^5` for `L ≥ 3`: the slack that absorbs the linear `bitCost` bound. -/
theorem bitCost_slack (L : ℕ) (hL : 3 ≤ L) : 48 * L + 17 ≤ L ^ 5 := by
  have h65 : 65 ≤ L ^ 4 := by
    calc 65 ≤ 81 := by norm_num
      _ = 3 ^ 4 := by norm_num
      _ ≤ L ^ 4 := Nat.pow_le_pow_left hL 4
  have h1 : 48 * L + 17 ≤ 65 * L := by omega
  have h2 : 65 * L ≤ L ^ 4 * L := Nat.mul_le_mul_right L h65
  have h3 : L ^ 4 * L = L ^ 5 := by rw [← Nat.pow_succ]
  omega

/-- **The bit-cost count is under the squaring bound.**  `C + d + 5 ≤ 2^k` is the only exponent
condition; the degenerate orders give `count = 1`. -/
theorem hTle_countWithBitCost_exp (K C d : ℕ) (hK : C + d + 5 ≤ K)
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    countWithBitCost C d p.1.1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ K := by
  have hL1 : 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length := by
    rw [QMCNumericRuntime.request_encoding]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  have hsplit : (QuantumMaxCutEnergy.encodeInput p.1.1).length
      ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length := by
    simp only [QuantumMaxCutEnergy.encodeRequest, List.length_append]
    exact Nat.le_add_right _ _
  by_cases hn : (p.1.1).n ≤ 1
  · rw [countWithBitCost, if_pos hn]
    exact Nat.succ_le_of_lt (pow_pos (by omega) _)
  · have hn2 : 2 ≤ (p.1.1).n := by omega
    have hL3 : 3 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length := by
      have he : (p.1.1).n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
        QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
      omega
    have hbit := bitCost_Rq_le p.1.1
    have hbit' : bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1
        ≤ 48 * (QuantumMaxCutEnergy.encodeRequest p.1).length + 17 := by
      have := hsplit
      omega
    have hfac := bitCost_slack (QuantumMaxCutEnergy.encodeRequest p.1).length hL3
    rw [countWithBitCost, if_neg hn]
    have hC : C ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ C := by
      rcases Nat.eq_zero_or_pos C with h0 | h0
      · rw [h0]; exact Nat.zero_le _
      · exact (le_of_lt Nat.lt_two_pow_self).trans
          (Nat.pow_le_pow_left (by omega) C)
    have hn1 : (p.1.1).n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
      QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
    have hpow : ((p.1.1).n + 1) ^ d ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ d :=
      Nat.pow_le_pow_left hn1 d
    calc C * ((p.1.1).n + 1) ^ d * (bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1)
        ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ C
            * (QuantumMaxCutEnergy.encodeRequest p.1).length ^ d
            * (48 * (QuantumMaxCutEnergy.encodeRequest p.1).length + 17) := by
          refine Nat.mul_le_mul (Nat.mul_le_mul hC hpow) hbit'
      _ ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ C
            * (QuantumMaxCutEnergy.encodeRequest p.1).length ^ d
            * (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 5 := by
          refine Nat.mul_le_mul le_rfl hfac
      _ = (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (C + d + 5) := by
          rw [← Nat.pow_add, ← Nat.pow_add]
      _ ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ K :=
          Nat.pow_le_pow_right (by omega) hK

/-- **The bit-cost count is under `L^(2^k)`.** -/
theorem hTle_countWithBitCost (k C d : ℕ) (hkd : C + d + 5 ≤ 2 ^ k)
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    countWithBitCost C d p.1.1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 ^ k :=
  hTle_countWithBitCost_exp (2 ^ k) C d hkd p

/-- **`hfuelLen` at the bit-cost count** — the slot of `FinalStroke.endgame_of_parts` verbatim. -/
theorem hfuelLen_countWithBitCost (k C d : ℕ) (hkd : C + d + 5 ≤ 2 ^ k) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (QMCLeafB.Fuel.fuelTake k (fun p => countWithBitCost C d p.1.1) p).length
        = countWithBitCost C d p.1.1 :=
  fun p => QMCLeafB.Fuel.fuelTake_length_of_le k (fun p => countWithBitCost C d p.1.1) p
    (hTle_countWithBitCost k C d hkd p)

/-- **`hfuelLen` at the bit-cost count, in `Input → ℚ → ℕ` form** (the `T0` slot). -/
theorem hfuelLen_countWithBitCost_input (k C d : ℕ) (hkd : C + d + 5 ≤ 2 ^ k) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (QMCLeafB.Fuel.fuelTake k (fun p => countWithBitCost C d p.1.1) p).length
        = (fun (G : QuantumMaxCutEnergy.Input) (_ : ℚ) => countWithBitCost C d G) p.1.1 p.2 :=
  hfuelLen_countWithBitCost k C d hkd

/-- **The same count in `K * m` form**, `m = 4 n²` the halving time of
`ClosingBracket.runData_hhalve_close`.  `RunData`'s round count is `K * m`, so this is the shape the
`hd` bundle and the `Nat.clog` estimate have to agree on. -/
noncomputable def countK (C d : ℕ) (G : QuantumMaxCutEnergy.Input) : ℕ :=
  (if G.n ≤ 1 then 1 else C * (G.n + 1) ^ d * (bitCost (QMCLeafB.EngineRuntime.Rq G) + 1))
    * (4 * (G.n * G.n))

/-- **The `K * m` count is a `Poly` function of the decider's input.** -/
theorem poly_countK (C d : ℕ) :
    Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => countK C d p.1.1) := by
  have hnat : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (countWithBitCost C d p.1.1, 4 * (p.1.1.n * p.1.1.n))) :=
    Automatic.Poly.pair (poly_countWithBitCost C d)
      (Automatic.Poly.comp (f := fun n : ℕ => 4 * (n * n))
        (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => p.1.1.n)
        (Automatic.Poly.comp (f := fun y : ℕ × ℕ => y.1 * y.2) (g := fun n : ℕ => (4, n * n))
          Automatic.Poly.nat_mul
          (Automatic.Poly.pair (Automatic.Poly.const 4) nat_sq_poly))
        orderP_poly)
  exact Automatic.Poly.comp (f := fun y : ℕ × ℕ => y.1 * y.2)
    (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (countWithBitCost C d p.1.1, 4 * (p.1.1.n * p.1.1.n)))
    Automatic.Poly.nat_mul hnat

/-- **The `K * m` count is under the squaring bound** (`C + d + 7 ≤ 2^k` suffices). -/
theorem hTle_countK (k C d : ℕ) (hkd : C + d + 9 ≤ 2 ^ k)
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    countK C d p.1.1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 ^ k := by
  have hpK : 2 ≤ 2 ^ k := by omega
  have hn1 : (p.1.1).n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
    QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
  by_cases hn : (p.1.1).n ≤ 1
  · have hval : countK C d p.1.1 = 1 * (4 * ((p.1.1).n * (p.1.1).n)) := by
      simp only [countK, if_pos hn]
    rw [hval]
    have h01 : (p.1.1).n = 0 ∨ (p.1.1).n = 1 := by omega
    rcases h01 with h0 | h0
    · rw [h0]
      simp only [Nat.mul_zero]
      exact Nat.zero_le _
    · rw [h0]
      norm_num only [Nat.mul_one, Nat.one_mul]
      have hL2 : 2 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length := by omega
      have h4 : 4 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 :=
              Nat.pow_le_pow_left hL2 2
      exact h4.trans (Nat.pow_le_pow_right (by omega) hpK)
  · have hn2 : 2 ≤ (p.1.1).n := by omega
    have hL3 : 3 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length := by omega
    have hbase : countWithBitCost C d p.1.1
        ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k - 4) :=
      hTle_countWithBitCost_exp (2 ^ k - 4) C d (by omega) p
    have hm2 : 4 * ((p.1.1).n * (p.1.1).n)
        ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 4 := by
      have hsq : (p.1.1).n * (p.1.1).n ≤ ((p.1.1).n + 1) * ((p.1.1).n + 1) :=
        Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
      have h2 : ((p.1.1).n + 1) * ((p.1.1).n + 1)
          ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length
            * (QuantumMaxCutEnergy.encodeRequest p.1).length := Nat.mul_le_mul hn1 hn1
      have h3 : 4 * ((p.1.1).n * (p.1.1).n)
          ≤ 4 * ((QuantumMaxCutEnergy.encodeRequest p.1).length
            * (QuantumMaxCutEnergy.encodeRequest p.1).length) :=
        Nat.mul_le_mul le_rfl (hsq.trans h2)
      have h44 : 4 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 :=
              Nat.pow_le_pow_left (by omega) 2
      have h4 : 4 * ((QuantumMaxCutEnergy.encodeRequest p.1).length
            * (QuantumMaxCutEnergy.encodeRequest p.1).length)
          ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 4 := by
        calc 4 * ((QuantumMaxCutEnergy.encodeRequest p.1).length
              * (QuantumMaxCutEnergy.encodeRequest p.1).length)
            = 4 * (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 := by ring
          _ ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2
                * (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 :=
              Nat.mul_le_mul h44 le_rfl
          _ = (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 4 := by ring
      exact h3.trans h4
    have hif : countK C d p.1.1
        = countWithBitCost C d p.1.1 * (4 * ((p.1.1).n * (p.1.1).n)) := by
      unfold countK countWithBitCost
      rw [if_neg hn]
    calc countK C d p.1.1
        = countWithBitCost C d p.1.1 * (4 * ((p.1.1).n * (p.1.1).n)) := hif
      _ ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k - 4)
            * (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 4 := Nat.mul_le_mul hbase hm2
      _ = (QuantumMaxCutEnergy.encodeRequest p.1).length ^ ((2 ^ k - 4) + 4) := by
          rw [Nat.pow_add]
      _ = (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 ^ k := by
          rw [show 2 ^ k - 4 + 4 = 2 ^ k by omega]

/-- **`hfuelLen` at the `K * m` count** — the slot of `FinalStroke.endgame_of_parts` verbatim, at the
round count the run itself uses. -/
theorem hfuelLen_countK (k C d : ℕ) (hkd : C + d + 9 ≤ 2 ^ k) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (QMCLeafB.Fuel.fuelTake k (fun p => countK C d p.1.1) p).length = countK C d p.1.1 :=
  fun p => QMCLeafB.Fuel.fuelTake_length_of_le k (fun p => countK C d p.1.1) p
    (hTle_countK k C d hkd p)

/-! ## 4.  The pinned `o`, and `hspec` verbatim

`o` is *defined* here — this is the definition the driver members should share: the verdict of the
tape-free run at the tape-free start, run for the tape-free count.  §4 shows the stroke's `hspec`
slot holds for it. -/

section Pinned

variable {σ : Type}

/-- **The verdict bit.**  `o G t` is what the run does from the tape-free start `pack (weights G) t`
after `Tof (weights G) t` rounds.  This is the campaign doc's `o G t := verdict (round^[T0 G t]
(init ((G, []), t)))`, with `init ((G, []), t)` replaced by its tape-free description (the two agree
by `initP_apply`). -/
def runBitP (pack : List ℚ → ℚ → σ) (round : σ → σ) (verdict : σ → Bool)
    (Tof : List ℚ → ℚ → ℕ) : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  fun G t => verdict (round^[Tof (weightsOf G) t] (pack (weightsOf G) t))

/-- `runBitP` is `runBit` at the decoded count: the two spellings of §2 and §4 agree definitionally,
so `hspec_of_tape_free` applies to it without a case. -/
theorem runBitP_eq_runBit (pack : List ℚ → ℚ → σ) (round : σ → σ) (verdict : σ → Bool)
    (Tof : List ℚ → ℚ → ℕ) :
    runBitP pack round verdict Tof
      = runBit (initOf pack) round verdict (fun (G : QuantumMaxCutEnergy.Input) (t : ℚ) =>
          Tof (weightsOf G) t) := rfl

/-- **`runBitP` is the campaign doc's definition verbatim**: the verdict after `T0` rounds from the
program's own initial state at the empty tape.  So a reader who writes `o` the doc's way gets this
file's `hspec` with no adapter. -/
theorem runBitP_eq_doc (pack : List ℚ → ℚ → σ) (round : σ → σ) (verdict : σ → Bool)
    (Tof : List ℚ → ℚ → ℕ) :
    runBitP pack round verdict Tof
      = fun (G : QuantumMaxCutEnergy.Input) (t : ℚ) =>
          verdict (Nat.iterate round (Tof (weightsOf G) t) (initP pack ((G, []), t))) := rfl

/-- `runBitP` unfolded: the form to compute with. -/
theorem runBitP_apply (pack : List ℚ → ℚ → σ) (round : σ → σ) (verdict : σ → Bool)
    (Tof : List ℚ → ℚ → ℕ) (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    runBitP pack round verdict Tof G t
      = verdict (round^[Tof (weightsOf G) t] (pack (weightsOf G) t)) :=
  rfl

/-- **`hspec` at the pinned `o`, from the fuel length alone.**  The `hinit` and `hT` hypotheses of
`hspec_of_tape_free` are `rfl` at this shape, so what is left is the exact-length fact of §3. -/
theorem hspec_runBit (pack : List ℚ → ℚ → σ) (round : σ → σ) (verdict : σ → Bool)
    (Tof : List ℚ → ℚ → ℕ) (k : ℕ)
    (hlen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (QMCLeafB.Fuel.fuelTake k (countOf Tof) p).length = Tof (weightsOf p.1.1) p.2) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (round^[(QMCLeafB.Fuel.fuelTake k (countOf Tof) p).length] (initP pack p))
        = runBitP pack round verdict Tof p.1.1 p.2 := by
  intro p
  rw [hlen p]
  rfl

/-- **`hspec` at the pinned `o`, from the squaring bound.**  The only hypothesis is the one
`Check_fuel` asks for: the round count is under `L^(2^k)` at the input's request word, `L` its
length.  (Discharge it from `Fuel.mul_pow_le_fuel_length` by bounding `Tof` by a monomial `C (n+1)^d`
with `d + C ≤ 2^k`; a longer tape only makes the request word longer, hence the bound easier.) -/
theorem hspec_runBit_take (pack : List ℚ → ℚ → σ) (round : σ → σ) (verdict : σ → Bool)
    (Tof : List ℚ → ℚ → ℕ) (k : ℕ)
    (hTle : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      countOf Tof p ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 ^ k) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (round^[(QMCLeafB.Fuel.fuelTake k (countOf Tof) p).length] (initP pack p))
        = runBitP pack round verdict Tof p.1.1 p.2 :=
  hspec_runBit pack round verdict Tof k (fun p => fuelTake_countOf_length k Tof p (hTle p))

end Pinned

/-! ## 5.  The bit is computable: `Poly (fun p => o p.1.1 p.2)`

`o` is defined through a `Nat.iterate`, which a `Poly` program cannot state directly; the loop
combinator computes it.  This is `SimPoly.ho_of_loop`'s `ho` slot at the pinned `o`, i.e. the
"`o` needs no separate program" half of the brick. -/

section Bit

variable {σ : Type} [Coding σ]

/-- **The pinned `o` is a `Poly` function.**  All the loop-side slots (`init`, `fuel`, `round`,
`verdict`, the size accounting) plus the exact fuel length. -/
theorem poly_runBit (pack : List ℚ → ℚ → σ)
    (hpack : Automatic.Poly (fun q : List ℚ × ℚ => pack q.1 q.2))
    (round : σ → σ) (verdict : σ → Bool)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (k : ℕ) (Tof : List ℚ → ℚ → ℕ)
    (hTof : Automatic.Poly (fun q : List ℚ × ℚ => Tof q.1 q.2))
    (hTle : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      countOf Tof p ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 ^ k) :
    Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        runBitP pack round verdict Tof p.1.1 p.2) :=
  QMCLeafB.SimPoly.ho_of_loop (initP pack) (QMCLeafB.Fuel.fuelTake k (countOf Tof)) round verdict
    (initP_poly pack hpack) (QMCLeafB.Fuel.poly_fuelTake k (countOf Tof) (poly_countOf Tof hTof))
    hr hv sizes hsize hsize0 (runBitP pack round verdict Tof)
    (hspec_runBit_take pack round verdict Tof k hTle)

end Bit

/-! ## 6.  The closing stroke with `o` and `hspec` filled in

What is left for the integration: the driver (`σ`, `pack`, `round`, `verdict`, `hr`, `hv`), the size
accounting (`sizes`, `hsize`, `hsize0`), the round count (`k`, `Tof`, `hTof`, `hTle`) and the run
bundle `hd` — read at the pinned `o` of §4.  Nothing else. -/

section Stroke

variable {σ : Type} [Coding σ]

/-- **`d9f601e5` from the driver and a run bundle at the pinned `o`.**  `solution_of_loop_via_runData`
with `init := initP pack`, `fuel := fuelTake k (countOf Tof)`, `o := runBitP pack round verdict Tof`
and `hspec` discharged by §4. -/
theorem solution_of_loop_via_iterate (pack : List ℚ → ℚ → σ)
    (hpack : Automatic.Poly (fun q : List ℚ × ℚ => pack q.1 q.2))
    (round : σ → σ) (verdict : σ → Bool)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (k : ℕ) (Tof : List ℚ → ℚ → ℕ)
    (hTof : Automatic.Poly (fun q : List ℚ × ℚ => Tof q.1 q.2))
    (hTle : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      countOf Tof p ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → QMCLeafB.VerdictSound.RunData
        (runBitP pack round verdict Tof) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.VerdictSound.solution_of_loop_via_runData (initP pack)
    (QMCLeafB.Fuel.fuelTake k (countOf Tof)) round verdict
    (initP_poly pack hpack) (QMCLeafB.Fuel.poly_fuelTake k (countOf Tof) (poly_countOf Tof hTof))
    hr hv sizes hsize hsize0 (runBitP pack round verdict Tof)
    (hspec_runBit_take pack round verdict Tof k hTle) hd

end Stroke

/-! ## 7.  Axiom audit -/

#print axioms QMCLeafB.Hspec.weightsOf_parseWeights
#print axioms QMCLeafB.Hspec.weightsOfRequest_poly
#print axioms QMCLeafB.Hspec.decodedInput_poly
#print axioms QMCLeafB.Hspec.hspec_of_tape_free
#print axioms QMCLeafB.Hspec.initP_apply
#print axioms QMCLeafB.Hspec.initP_tape_free
#print axioms QMCLeafB.Hspec.initP_poly
#print axioms QMCLeafB.Hspec.poly_countOf
#print axioms QMCLeafB.Hspec.fuelTake_countOf_length
#print axioms QMCLeafB.Hspec.runBitP_apply
#print axioms QMCLeafB.Hspec.hspec_runBit
#print axioms QMCLeafB.Hspec.hspec_runBit_take
#print axioms QMCLeafB.Hspec.poly_runBit
#print axioms QMCLeafB.Hspec.solution_of_loop_via_iterate
#print axioms QMCLeafB.Hspec.countOf_apply
#print axioms QMCLeafB.Hspec.initD_apply
#print axioms QMCLeafB.Hspec.initD_tape_free
#print axioms QMCLeafB.Hspec.initD_poly
#print axioms QMCLeafB.Hspec.runBitD_apply
#print axioms QMCLeafB.Hspec.hspec_runBitD
#print axioms QMCLeafB.Hspec.solution_of_loop_via_iterateD
#print axioms QMCLeafB.Hspec.decodedWithOrder_eq
#print axioms QMCLeafB.Hspec.decodedWithOrder_poly
#print axioms QMCLeafB.Hspec.nat_pow_poly
#print axioms QMCLeafB.Hspec.nat_monomial_poly
#print axioms QMCLeafB.Hspec.poly_order
#print axioms QMCLeafB.Hspec.poly_countWithOrder
#print axioms QMCLeafB.Hspec.hTle_countWithOrder
#print axioms QMCLeafB.Hspec.solution_of_loop_via_orderCount
#print axioms QMCLeafB.Hspec.runBitP_eq_runBit
#print axioms QMCLeafB.Hspec.runBitP_eq_doc
#print axioms QMCLeafB.Hspec.hTle_of_succ_pow
#print axioms QMCLeafB.Hspec.hTle_of_monomial_of_small
#print axioms QMCLeafB.Hspec.hfuelLen_of_monomial_of_small
#print axioms QMCLeafB.Hspec.hfuelLen_of_succ_pow
#print axioms QMCLeafB.Hspec.orderOfInput_poly
#print axioms QMCLeafB.Hspec.orderP_poly
#print axioms QMCLeafB.Hspec.nat_sq_poly
#print axioms QMCLeafB.Hspec.poly_roundCount
#print axioms QMCLeafB.Hspec.poly_roundCount_program
#print axioms QMCLeafB.Hspec.roundCount_le
#print axioms QMCLeafB.Hspec.roundCount_le_succ_pow
#print axioms QMCLeafB.Hspec.hfuelLen_roundCount
#print axioms QMCLeafB.Hspec.anyOk_congr_of_false
#print axioms QMCLeafB.Hspec.hspec_of_overshoot
#print axioms QMCLeafB.Hspec.hspec_of_stable_ok
#print axioms QMCLeafB.Hspec.hTle_fuel_of_length_monomial
#print axioms QMCLeafB.Hspec.poly_ratParts
#print axioms QMCLeafB.Hspec.poly_bitCost
#print axioms QMCLeafB.Hspec.poly_bitCostRq
#print axioms QMCLeafB.Hspec.rat_add_one_le_two_pow_bitCost
#print axioms QMCLeafB.Hspec.Rq_add_one_le_two_pow_bitCost
#print axioms QMCLeafB.Hspec.Rq_add_one_pow_le_two_pow
#print axioms QMCLeafB.Hspec.encodeNumber_length
#print axioms QMCLeafB.Hspec.encode_ratio_length
#print axioms QMCLeafB.Hspec.encode_ratio_le
#print axioms QMCLeafB.Hspec.encodeList_weights_le
#print axioms QMCLeafB.Hspec.encodeWeights_le_encodeInput
#print axioms QMCLeafB.Hspec.weightsList_length_le_encodeInput
#print axioms QMCLeafB.Hspec.HasHeight_map_sum
#print axioms QMCLeafB.Hspec.HasHeight_two_mul_map_sum
#print axioms QMCLeafB.Hspec.bitCost_two_mul_map_sum_le
#print axioms QMCLeafB.Hspec.bitCost_Rq_le
#print axioms QMCLeafB.Hspec.poly_bitCostRq_succ
#print axioms QMCLeafB.Hspec.poly_countWithBitCost
#print axioms QMCLeafB.Hspec.bitCost_slack
#print axioms QMCLeafB.Hspec.hTle_countWithBitCost
#print axioms QMCLeafB.Hspec.hfuelLen_countWithBitCost
#print axioms QMCLeafB.Hspec.hfuelLen_countWithBitCost_input
#print axioms QMCLeafB.Hspec.poly_countK
#print axioms QMCLeafB.Hspec.hTle_countWithBitCost_exp
#print axioms QMCLeafB.Hspec.hTle_countK
#print axioms QMCLeafB.Hspec.hfuelLen_countK

/-! The two closing forms, for the coordinator: each is `SolutionStatement` from a driver and a run
bundle at the pinned `o`. -/

#check @QMCLeafB.Hspec.solution_of_loop_via_iterateD
#check @QMCLeafB.Hspec.solution_of_loop_via_orderCount
#check @QMCLeafB.Hspec.hspec_runBitD

end QMCLeafB.Hspec


