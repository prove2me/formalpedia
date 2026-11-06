-- Prove2me | Definitions.Def_QMCLeafB_fal36
-- name    : QMCLeafB_fal36
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:17:22.466777+00:00
-- url     : https://prove2.me/theorems/a8e50106-cd82-4742-a86b-d0f26cf4f3b5
-- title:
--   QMCLeafB fal36
-- statement:
--   # `Check_fal36_m4` — phase 36, member m4, direction `falsify36`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_asm35
import Definitions.Def_QMCLeafB_crux_m1
/-
# `Check_fal36_m4` — phase 36, member m4, direction `falsify36`

**The question.**  Phase-36's step 1 says: at an ALL-CUT point the run's own transcript is a
record, because with a membership-equivalent ok test `RunParts.hcut` is *exactly* "the centre is a
non-member, so the oracle's cut is genuine" — i.e. `RelaxOracle.relaxMem_or_cut`'s content.  This
file decides that claim.

## The answers

* **`hcut` itself is NOT a rationality condition, and the sqrt-2 obstruction does not reach it.**
  `hcut` names the engine's own accumulated centre `Cat k` in real coordinates and states one real
  inequality per round against it; it never asks for a rational representation.  Receipt:
  `hcut_trace_of_above` — the *trace normal* gives `hcut` with `del = 0` at an ARBITRARY real
  accumulated centre as soon as the centre's trace beats the body's level.  So
  `hctr_one_forces_square` / `not_hctr_initShape_two` is irrelevant to `hcut`.

* **But the bridge from the shelf's oracle to `hcut` is NOT definitional, and that is where the
  sqrt-2 obstruction lives.**  The shelf's cut is a `RelaxCut` at a *rational* centre `cX`, and its
  separation reads `-margin <= n . (z - flat(cX))`.  `hcut` reads `-del <= n . (z - Cat k)`.
  The two differ by the **signed translation price**

      enc = n . (flat(cX) - Cat k),

  and the shelf's own bridge (`Check_relax_oracle_m4` §5.5) consumes exactly the
  identification `Cat k = flat(cX k)` that cannot hold (`not_hctr_initShape_two`).  The exact
  repair is the **enclosure form**: `del k >= margin - enc` (`hcut_of_relaxCut_price`), whose price
  is additive in `del` and whose *dimensionless* value `(margin - enc)/sqrt(sigma)` is invariant
  under rescaling the normal (`price_scale_invariant`) — so no normalisation escapes it.

* **Consequence for the leaf (`EnclosureSlot`).**  The residual can be stated in the oracle's OWN
  output language — a `RelaxCut` family at rational centres plus the price inequality — and it
  implies `ShallowSlot`; so `HokSlot + EnclosureSlot` already yields the verbatim sentence
  (`solution_via_enclosure`).  This is step 1 done honestly: the record IS the run's transcript,
  but only after the transcript is re-anchored at the engine's own centre.

* **Where step 1 does not deliver step 3 (`no_record_at_ball_of_false_bit`,
  `oracleRecSlot_needs_bit_true`).**  At a body carrying the campaign ball the record class is EMPTY
  for EVERY bit reading `false` there.  So `-BodyRec` is not an all-cut-run obstruction that
  *forces* a bit: it excludes the bit's false reading and nothing else.  Which bit the program
  computes is a property of the program, and the passage `-BodyRec => bit true` needs the PROGRAM's
  own `hcut` at every round — i.e. exactly the price above.  Machine-checked consequence: the honest
  step-1 slot (`OracleRecSlot`) is *inconsistent* with a bit-`false` reading at a ball-bearing
  bracket point, so it cannot be the premise that derives the bit's truth there.

* **Record level (§6), which is what phase 36 actually needs.**  `bodyRec_of_oracleCuts` builds the
  all-false record at an ARBITRARY transcript with free depth `rho <= rmax` — i.e. it produces
  `ThinRec34M4.BodyRec`, the class phase 36 names `SelfRec` — from the oracle's `RelaxCut` family at
  rational centres plus the ledger and the price.  `solution_via_oracleRec` then closes the verbatim
  sentence from `HokSlot + OracleRecSlot`.  (The `§5` `ShallowCut`/`EnclosureSlot` form is the
  `rmax`-saturated special case and is strictly stronger; it is kept because the shelf's assembler
  consumes that shape.)

Discipline: `set_option autoImplicit false` (below); the file is proof-term and tactic only, with
every `#print axioms` line exactly `[propext, Classical.choice, Quot.sound]` (checked at build).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace QMCLeafB.Fal36M4

open QMCLeafB.EngineIterates

/-! ## 1.  `hcut` is a support inequality

`RunParts.hcut` (verbatim, `Check_final_stroke_m7`) is

    forall k, k < K*m -> ok k = false -> forall z, z in relaxBall -> -(del k) <= c_k . (z - Cat k).

Splitting the pairing shows it is neither a rationality condition nor a normalisation condition: it
says that the cut hyperplane, moved to the engine's own accumulated centre `Cat k`, supports the
relaxation with slack `del k`.  The *only* free number at round `k` is the slack. -/

/-- **`hcut` as a support inequality.**  The half-space `{z | c_k . z <= c_k . Cat k + del k}`
contains the whole relaxation. -/
theorem hcut_iff_support {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (cd : ℕ → CutData (G.n * G.n))
    (del : ℕ → ℚ) (T : ℕ) :
    (∀ k, k < T → ∀ z, z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P →
        -(((del k : ℚ)) : ℝ) ≤
          cutCR cd k ⬝ᵥ (z - Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k))
      ↔ (∀ k, k < T → ∀ z, z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P →
          cutCR cd k ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
            - cutCR cd k ⬝ᵥ z ≤ ((del k : ℚ) : ℝ)) := by
  constructor <;> intro H k hk z hz
  · have h := H k hk z hz
    rw [dotProduct_sub] at h
    linarith
  · have h := H k hk z hz
    rw [dotProduct_sub]
    linarith

#print axioms QMCLeafB.Fal36M4.hcut_iff_support

/-- **Monotonicity in the recorded slack** — the field is a one-sided budget. -/
theorem hcut_mono {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {cd : ℕ → CutData (G.n * G.n)}
    {del del' : ℕ → ℚ} {T : ℕ}
    (h : ∀ k, k < T → ∀ z, z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P →
      -(((del k : ℚ)) : ℝ) ≤
        cutCR cd k ⬝ᵥ (z - Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k))
    (hle : ∀ k, del k ≤ del' k) :
    ∀ k, k < T → ∀ z, z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P →
      -(((del' k : ℚ)) : ℝ) ≤
        cutCR cd k ⬝ᵥ (z - Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) := by
  intro k hk z hz
  have h1 := h k hk z hz
  have h2 : ((del k : ℚ) : ℝ) ≤ ((del' k : ℚ) : ℝ) := by exact_mod_cast hle k
  linarith

#print axioms QMCLeafB.Fal36M4.hcut_mono

/-! ## 2.  The sqrt-2 obstruction does not reach `hcut`

The shelf's static-separator route dies on `hctr_one_forces_square`: the engine's accumulated
centre is irrational from `k = 1` (`not_hctr_initShape_two`), so it can never be the flattening of
a rational matrix.  That is a statement about *representing* the centre, not about `hcut`, which
only pairs the centre with a normal.  The receipt is the trace normal, which separates the
relaxation from ANY real centre above the body's level, irrational or not. -/

/-- The flat cast of `flatQ` is the flattening of the cast (banked `Check_crux_m1` §1). -/
theorem flat_castMat_flatQ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat A)
      = fun k => ((QMCLeafB.RelaxOracle.flatQ A k : ℚ) : ℝ) :=
  QMCLeafB.CruxM1.flat_castMat_eq n A

#print axioms QMCLeafB.Fal36M4.flat_castMat_flatQ

/-- A negated normal negates the pairing. -/
theorem neg_dot {N : ℕ} (x z : Fin N → ℝ) :
    (fun k => -x k) ⬝ᵥ z = -(x ⬝ᵥ z) := by
  rw [dotProduct, dotProduct, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

#print axioms QMCLeafB.Fal36M4.neg_dot

/-- **The trace normal separates the relaxation from any real centre above the level.**  The
normal is the negative trace direction (the `traceHighCutOf` branch of the oracle); no rationality,
no symmetric representative, and no norm bound on the body is used except through `relaxBodyLE`'s
own trace clause. -/
theorem trace_separates {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ M : ℝ}
    {a : Fin (n * n) → ℝ}
    (ha : u + δ / 2
      ≤ (fun k => ((QMCLeafB.RelaxOracle.flatQ A k : ℚ) : ℝ)) ⬝ᵥ a) :
    ∀ z, z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) u δ M →
      0 ≤ (fun k => -(((QMCLeafB.RelaxOracle.flatQ A k : ℚ)) : ℝ)) ⬝ᵥ (z - a) := by
  intro z hz
  have htr : QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat A)
      (QMCLeafB.Boundary.unflat z) ≤ u + δ / 2 := hz.1.2.2
  have hdot : (fun k => ((QMCLeafB.RelaxOracle.flatQ A k : ℚ) : ℝ)) ⬝ᵥ z
      = QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat A)
          (QMCLeafB.Boundary.unflat z) := by
    rw [QMCLeafB.RelaxOracle.frob_eq_flat_dot, dotProduct]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [flat_castMat_flatQ, QMCLeafB.Boundary.flat_unflat]
  have hYX : (fun k => ((QMCLeafB.RelaxOracle.flatQ A k : ℚ) : ℝ)) ⬝ᵥ z
      ≤ (fun k => ((QMCLeafB.RelaxOracle.flatQ A k : ℚ) : ℝ)) ⬝ᵥ a :=
    le_trans hdot.le (le_trans htr ha)
  rw [dotProduct_sub, neg_dot (fun k => ((QMCLeafB.RelaxOracle.flatQ A k : ℚ) : ℝ)), neg_dot]
  linarith

#print axioms QMCLeafB.Fal36M4.trace_separates

/-- **`hcut` at the engine's own (irrational) accumulated centres.**  With the trace normal
recorded at every round, `RunParts.hcut` holds with slack `del = 0` at the accumulated centres as
soon as each of them sits above the body's level — the centres are never rationalised. -/
theorem hcut_trace_of_above {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (cd : ℕ → CutData (G.n * G.n))
    (T : ℕ)
    (hnorm : ∀ k, k < T →
      (cd k).c = fun i => -(QMCLeafB.RelaxOracle.flatQ (QMCLeafB.Finalization.wMatrixQ G) i))
    (ha : ∀ k, k < T →
      ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          + ((P.dq : ℚ) : ℝ) / 2
        ≤ (fun i => ((QMCLeafB.RelaxOracle.flatQ (QMCLeafB.Finalization.wMatrixQ G) i
              : ℚ) : ℝ)) ⬝ᵥ
            Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) :
    ∀ k, k < T → ∀ z, z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P →
      -(0 : ℝ) ≤
        cutCR cd k ⬝ᵥ (z - Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) := by
  intro k hk z hz
  have hz' : z ∈ QMCLeafB.Boundary.relaxBall
      (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G))
      ((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) ((P.dq : ℚ) : ℝ)
      (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ) := by
    rw [QMCLeafB.HemptyR_M3.castMat_wMatrixQ]
    have hu : (((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
        = (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
      push_cast
      ring
    rw [hu]
    exact hz
  have hu2 : (((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
      = (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
    push_cast
    ring
  have ha' : (((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
        + ((P.dq : ℚ) : ℝ) / 2
      ≤ (fun i => ((QMCLeafB.RelaxOracle.flatQ (QMCLeafB.Finalization.wMatrixQ G) i
            : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k := by
    rw [hu2]
    exact ha k hk
  have hsep := trace_separates (A := QMCLeafB.Finalization.wMatrixQ G)
    (u := ((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)) (δ := ((P.dq : ℚ) : ℝ))
    (M := (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ))
    (a := Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) ha' z hz'
  have hc : cutCR cd k
      = fun i => -(((QMCLeafB.RelaxOracle.flatQ (QMCLeafB.Finalization.wMatrixQ G) i
          : ℚ) : ℝ)) := by
    funext i
    simp only [cutCR, hnorm k hk]
    push_cast
    ring
  rw [hc]
  linarith

#print axioms QMCLeafB.Fal36M4.hcut_trace_of_above

/-! ## 3.  The exact price of the bridge: `hctr` cannot hold, the enclosure can

`RelaxOracle.relaxMem_or_cut` gives, at a rational centre `cX`, either a member or a cut
`C : RelaxCut A cX u δ` with `-C.margin <= n . (z - flat cX)` for the whole relaxation.  `hcut`
needs the same inequality at `Cat k`.  The difference is one dot product. -/

/-- **The price, and the repair.**  If the signed translation
`enc = n . (flat(cX) - Cat k)` satisfies `margin - enc <= del`, then the oracle's cut at its own
rational centre is a valid `hcut` at the engine's accumulated centre with slack `del`. -/
theorem hcut_of_relaxCut_price {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (C : QMCLeafB.RelaxOracle.RelaxCut A cX u δ) (a : Fin (n * n) → ℝ) {del : ℚ}
    (hprice : ((C.margin : ℚ) : ℝ)
        - (fun i => ((QMCLeafB.RelaxOracle.flatQ C.normal i : ℚ) : ℝ)) ⬝ᵥ
            (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX) - a)
      ≤ ((del : ℚ) : ℝ)) :
    ∀ z, z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) u δ M →
      -(((del : ℚ)) : ℝ) ≤
        (fun i => ((QMCLeafB.RelaxOracle.flatQ C.normal i : ℚ) : ℝ)) ⬝ᵥ (z - a) := by
  intro z hz
  have h := C.separates_ball M z hz
  have hsplit := QMCLeafB.CruxM1.dotProduct_sub_split
    (fun i => ((QMCLeafB.RelaxOracle.flatQ C.normal i : ℚ) : ℝ)) z
    (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX)) a
  rw [hsplit]
  linarith

#print axioms QMCLeafB.Fal36M4.hcut_of_relaxCut_price

/-- **The price is free when the accumulated centre is on the body's side.**  With `enc >= 0` the
round's own margin is a legal slack: `hcut` at `del = margin`, no extra budget. -/
theorem hcut_of_relaxCut_price_nonneg {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    {M : ℝ} (C : QMCLeafB.RelaxOracle.RelaxCut A cX u δ) (a : Fin (n * n) → ℝ)
    (henc : 0 ≤ (fun i => ((QMCLeafB.RelaxOracle.flatQ C.normal i : ℚ) : ℝ)) ⬝ᵥ
      (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX) - a)) :
    ∀ z, z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) u δ M →
      -(((C.margin : ℚ)) : ℝ) ≤
        (fun i => ((QMCLeafB.RelaxOracle.flatQ C.normal i : ℚ) : ℝ)) ⬝ᵥ (z - a) := by
  refine hcut_of_relaxCut_price C a ?_
  have hm : (0 : ℚ) < C.margin := C.margin_pos
  have hmR : (0 : ℝ) < ((C.margin : ℚ) : ℝ) := by exact_mod_cast hm
  linarith

#print axioms QMCLeafB.Fal36M4.hcut_of_relaxCut_price_nonneg

/-- **The price is not removable: it vanishes for every normal exactly when the recorded centre IS
the engine's centre.**  So no choice of normals lets a rational `cX` stand in for `Cat k`, and
`not_hctr_initShape_two` therefore says the shelf's identification is unavailable already at
`k = 1`. -/
theorem price_zero_iff_centre_eq {N : ℕ} (a b : Fin N → ℝ) :
    (∀ c : Fin N → ℝ, c ⬝ᵥ (b - a) = 0) ↔ b = a := by
  constructor
  · intro h
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp (h (b - a)))
  · rintro rfl c
    simp

#print axioms QMCLeafB.Fal36M4.price_zero_iff_centre_eq

/-- **No normalisation escapes the price.**  Rescaling the recorded normal by `lam != 0` scales the
margin, the price and `sigma` by `lam`, `lam` and `lam^2`, so the ledger `del^2 <= rho^2 sigma`
sees only the dimensionless quantity `(margin - enc)/sqrt(sigma)`.  An infeasible round cannot be
made feasible by re-choosing the normal's magnitude. -/
theorem price_scale_invariant {m e ρ σ lam : ℚ} (hlam : lam ≠ 0) :
    (lam * m - lam * e) ^ 2 ≤ ρ ^ 2 * (lam ^ 2 * σ) ↔ (m - e) ^ 2 ≤ ρ ^ 2 * σ := by
  have h2 : (0 : ℚ) < lam ^ 2 := by positivity
  have h1 : (lam * m - lam * e) ^ 2 = lam ^ 2 * (m - e) ^ 2 := by ring
  have h3 : ρ ^ 2 * (lam ^ 2 * σ) = lam ^ 2 * (ρ ^ 2 * σ) := by ring
  rw [h1, h3]
  exact mul_le_mul_iff_of_pos_left h2

#print axioms QMCLeafB.Fal36M4.price_scale_invariant


/-- **The price is unavoidable at `k = 1`.**  For EVERY rational presentation of the engine's own
accumulated centre — every `cX ∈ ℚ^{2×2}` — some normal pays a nonzero price.  So the identification
`hctr` is not merely inconvenient, it is unattainable, and the bridge from the shelf's rational-cut
oracle to `hcut` must carry the translation term. -/
theorem price_nonzero_at_one :
    ∀ cX : Matrix (Fin 2) (Fin 2) ℚ, ∃ c : Fin 4 → ℝ,
      c ⬝ᵥ (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX)
        - QMCLeafB.EngineIterates.Cat 4 (0 : Fin 4 → ℝ) (QMCLeafB.CruxM1.coordCd 2) 1) ≠ 0 := by
  intro cX
  by_contra h
  push Not at h
  exact QMCLeafB.CruxM1.not_hctr_initShape_two
    ⟨cX, ((price_zero_iff_centre_eq
      (QMCLeafB.EngineIterates.Cat 4 (0 : Fin 4 → ℝ) (QMCLeafB.CruxM1.coordCd 2) 1)
      (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX))).mp h).symm⟩

#print axioms QMCLeafB.Fal36M4.price_nonzero_at_one

/-! ## 4.  Step 1 as a theorem: the record IS the transcript's own datum

At a bit-`false` point the program disappears from `RunParts` (`hverdict` becomes `ok = false`
everywhere) and the record is exactly the transcript's datum.  So step 1's content is a property of
the transcript, not of the bit. -/

/-- **Step 1, exactly.**  At a bit-`false` point, a record exists iff the transcript carries the
shallow-cut datum — no reference to the program at all. -/
theorem step1_content {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (h : o G t = false) :
    Nonempty (QMCLeafB.FinalStroke.RunParts o G t P)
      ↔ QMCLeafB.ThinRec34M4.RecordDatum G t P :=
  (QMCLeafB.ThinRec34M4.runParts_false_iff_bodyRec h).trans
    QMCLeafB.ThinRec34M4.bodyRec_iff_recordDatum

#print axioms QMCLeafB.Fal36M4.step1_content

/-- **Step 1 does not deliver step 3.**  At a body carrying the campaign ball the record class is
empty at EVERY bit reading `false` there.  Hence `¬BodyRec` is not an obstruction to all-cut *runs*:
it is an obstruction to the bit's false reading, and which bit the program computes is decided by
the program — its own `hcut` must hold at every round for the implication to bite, i.e. exactly the
price `§3` prices. -/
theorem no_record_at_ball_of_false_bit {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t P) :
    o G t = false → ¬ Nonempty (QMCLeafB.FinalStroke.RunParts o G t P) := by
  intro hbit hrec
  exact QMCLeafB.ThinRec34M4.not_bodyRec_of_ball hn hball
    ((QMCLeafB.ThinRec34M4.runParts_false_iff_bodyRec hbit).mp hrec)

#print axioms QMCLeafB.Fal36M4.no_record_at_ball_of_false_bit

/-! ## 5.  The wiring: the residual in the oracle's own language

`EnclosureSlot` is `ShallowSlot` re-expressed through the shelf's `RelaxOracle` output: a family of
rational cuts at rational centres, a depth stream inside `rmax·sqrt(sigma)`, and — the one new
clause — the price inequality `margin − enc <= del` at the engine's own accumulated centre.  By
`hcut_of_relaxCut_price` it implies `ShallowSlot`, so `HokSlot + EnclosureSlot` closes the verbatim
leaf by the banked `Asm35M4.solution_via_shallowCut`.  The point of the form is that every clause is
produced by the program's own oracle; none of them asks the engine's centre to be rational. -/

/-- The signed price of presenting the oracle's rational centre `cX k` instead of the engine's own
accumulated centre `Cat k`. -/
noncomputable def price {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k : ℕ, QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq)
    (hn : 2 ≤ G.n) (hc : ∀ k : ℕ, QMCLeafB.RelaxOracle.flatQ (C k).normal ≠ 0) (k : ℕ) : ℝ :=
  ((C k).margin : ℝ)
    - (fun i => ((QMCLeafB.RelaxOracle.flatQ (C k).normal i : ℚ) : ℝ)) ⬝ᵥ
        (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
          - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.ThinRec34M4.NormalCut G P hn
                (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal) hc) k)

/-- **The enclosure slot** — the residual at the oracle's own interface. -/
def EnclosureSlot : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    Asm35M4.o33 G t = false →
    ∃ (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
      (C : ∀ k : ℕ, QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.EngineRuntime.Rq G / 40000) (Asm35M4.P33 G).dq)
      (hc : ∀ k : ℕ, QMCLeafB.RelaxOracle.flatQ (C k).normal ≠ 0)
      (del : ℕ → ℚ),
      (∀ k, k < (Asm35M4.P33 G).K * (Asm35M4.P33 G).m → 0 ≤ del k)
      ∧ (∀ k, (del k) ^ 2 ≤ (Asm35M4.P33 G).rmax ^ 2
          * QMCLeafB.EngineIterates.sigmaQ
              (fun i => QMCLeafB.RelaxOracle.flatQ (C k).normal i)
              ((QMCLeafB.ThinRec34M4.NormalCut G (Asm35M4.P33 G) hn
                (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal) hc k).p))
      ∧ (∀ k, k < (Asm35M4.P33 G).K * (Asm35M4.P33 G).m →
          price (Asm35M4.P33 G) cX C hn hc k ≤ ((del k : ℚ) : ℝ))

/-- **`EnclosureSlot` gives `ShallowCut`.**  The witness is the transcript carried by the oracle's
own normals, and `hcut` comes from `hcut_of_relaxCut_price` at the engine's accumulated centres. -/
theorem shallowCut_of_enclosure {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {hn : 2 ≤ G.n}
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k : ℕ, QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) (Asm35M4.P33 G).dq)
    (hc : ∀ k : ℕ, QMCLeafB.RelaxOracle.flatQ (C k).normal ≠ 0)
    (del : ℕ → ℚ)
    (hdel0 : ∀ k, k < (Asm35M4.P33 G).K * (Asm35M4.P33 G).m → 0 ≤ del k)
    (hchk : ∀ k, (del k) ^ 2 ≤ (Asm35M4.P33 G).rmax ^ 2
      * QMCLeafB.EngineIterates.sigmaQ
          (fun i => QMCLeafB.RelaxOracle.flatQ (C k).normal i)
          ((QMCLeafB.ThinRec34M4.NormalCut G (Asm35M4.P33 G) hn
            (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal) hc k).p))
    (hprice : ∀ k, k < (Asm35M4.P33 G).K * (Asm35M4.P33 G).m →
      price (Asm35M4.P33 G) cX C hn hc k ≤ ((del k : ℚ) : ℝ)) :
    QMCLeafB.ThinRec34M4.ShallowCut G t (Asm35M4.P33 G) hn := by
  refine ⟨fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal, hc, del, hdel0, hchk, ?_⟩
  intro k hk z hz
  have hz' : z ∈ QMCLeafB.Boundary.relaxBall
      (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G))
      (((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
      (((Asm35M4.P33 G).dq : ℚ) : ℝ)
      (((2 * (G.n : ℚ) ^ 2 + 2 * (Asm35M4.P33 G).dq ^ 2 : ℚ)) : ℝ) := by
    rw [QMCLeafB.HemptyR_M3.castMat_wMatrixQ]
    have hu : (((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
        = (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
      push_cast
      ring
    rw [hu]
    exact hz
  have hpcut := hcut_of_relaxCut_price (C := C k)
    (a := QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
      (QMCLeafB.ThinRec34M4.NormalCut G (Asm35M4.P33 G) hn
        (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal) hc) k)
    (del := del k) (hprice k hk) z hz'
  have hcR : QMCLeafB.EngineIterates.cutCR
      (QMCLeafB.ThinRec34M4.NormalCut G (Asm35M4.P33 G) hn
        (fun k => QMCLeafB.RelaxOracle.flatQ (C k).normal) hc) k
      = fun i => ((QMCLeafB.RelaxOracle.flatQ (C k).normal i : ℚ) : ℝ) := rfl
  rw [hcR]
  rw [dotProduct_sub] at hpcut
  linarith

#print axioms QMCLeafB.Fal36M4.shallowCut_of_enclosure

/-- **Slot level.** -/
theorem shallowSlot_of_enclosureSlot (H : EnclosureSlot) : Asm35M4.ShallowSlot := by
  intro G t hn h1 h2 hbit
  obtain ⟨cX, C, hc, del, hdel0, hchk, hprice⟩ := H G t hn h1 h2 hbit
  exact shallowCut_of_enclosure cX C hc del hdel0 hchk hprice

#print axioms QMCLeafB.Fal36M4.shallowSlot_of_enclosureSlot

/-- **The leaf from `{HokSlot} + {EnclosureSlot}`** — the verbatim `d9f601e5` sentence, with the
record horn supplied through the oracle's own output language. -/
theorem solution_via_enclosure (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : Asm35M4.HokSlot) (He : EnclosureSlot) :
    QMCLeafB.FinishLine.SolutionStatement :=
  Asm35M4.solution_via_shallowCut k hk hok (shallowSlot_of_enclosureSlot He)

#print axioms QMCLeafB.Fal36M4.solution_via_enclosure


/-! ## 6.  Record level: `BodyRec` from the oracle's own cuts

§5 works through `ShallowCut`, whose transcript is the `rmax`-saturated `NormalCut`.  The leaf's
actual residual is finer — `ThinRec34M4.BodyRec`, an all-false `RunParts` at an ARBITRARY transcript
with free depth `rho <= rmax` — and phase 36's `SelfRec` is exactly that class.  So the bridge is
stated once more at record level: the oracle's rational cuts plus the price supply `BodyRec`, hence
phase 36's `SelfRec`, hence the verbatim leaf. -/

/-- The signed price of presenting a rational centre `cX` instead of the real point `a`. -/
noncomputable def priceAt {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (C : QMCLeafB.RelaxOracle.RelaxCut A cX u δ) (a : Fin (n * n) → ℝ) : ℝ :=
  ((C.margin : ℚ) : ℝ)
    - (fun i => ((QMCLeafB.RelaxOracle.flatQ C.normal i : ℚ) : ℝ)) ⬝ᵥ
        (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX) - a)

/-- **`hcut` at any transcript's accumulated centre, priced.**  This is `hcut_of_relaxCut_price`
with the price named. -/
theorem hcut_of_priceAt {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (C : QMCLeafB.RelaxOracle.RelaxCut A cX u δ) (a : Fin (n * n) → ℝ) {del : ℚ}
    (hprice : priceAt C a ≤ ((del : ℚ) : ℝ)) :
    ∀ z, z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) u δ M →
      -(((del : ℚ)) : ℝ) ≤
        (fun i => ((QMCLeafB.RelaxOracle.flatQ C.normal i : ℚ) : ℝ)) ⬝ᵥ (z - a) :=
  hcut_of_relaxCut_price C a hprice

#print axioms QMCLeafB.Fal36M4.priceAt
#print axioms QMCLeafB.Fal36M4.hcut_of_priceAt

/-- **THE RECORD FROM THE ORACLE'S OWN CUTS.**  At any interior bracket point, a transcript with
the engine's witness relation whose normals are the `RelaxOracle`'s cut normals at rational centres,
whose depths obey the record's own ledger `del^2 <= rho^2 sigma` with `rho <= rmax`, and whose price
`margin - enc` fits in `del` at the ENGINE's accumulated centre, IS an all-false record.  The
conclusion is `BodyRec` — the exact class phase 36 calls `SelfRec`. -/
theorem bodyRec_of_oracleCuts {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k : ℕ, QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq)
    (cd : ℕ → CutData (G.n * G.n)) (del : ℕ → ℚ)
    (hnorm : ∀ k, (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k).normal)
    (hwit : ∀ k, k < P.K * P.m →
      (Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k).mulVec (cd k).p = (cd k).c)
    (hrho : ∀ k, k < P.K * P.m → 0 ≤ (cd k).rho)
    (hcne : ∀ k, k < P.K * P.m → (cd k).c ≠ 0)
    (hdel0 : ∀ k, k < P.K * P.m → 0 ≤ del k)
    (hcheck : ∀ k, k < P.K * P.m →
      (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hle : ∀ k, k < P.K * P.m → (cd k).rho ≤ P.rmax)
    (hprice : ∀ k, k < P.K * P.m →
      priceAt (C k) (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) ≤ ((del k : ℚ) : ℝ)) :
    QMCLeafB.ThinRec34M4.BodyRec G t P :=
  ⟨QMCLeafB.CruxM1.allFalseParts (o := QMCLeafB.ThinRec34M4.falseBit) (P := P) rfl cd del
    hwit hrho hcne hdel0 hcheck hle
    (fun k hk z hz => by
      have hz' : z ∈ QMCLeafB.Boundary.relaxBall
          (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G))
          (((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ((P.dq : ℚ) : ℝ)
          (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ) := by
        rw [QMCLeafB.HemptyR_M3.castMat_wMatrixQ]
        have hu : (((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
            = (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
          push_cast
          ring
        rw [hu]
        exact hz
      have hp := hcut_of_priceAt (C := C k)
        (a := Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) (del := del k)
        (hprice k hk) z hz'
      have hcR : cutCR cd k
          = fun i => ((QMCLeafB.RelaxOracle.flatQ (C k).normal i : ℚ) : ℝ) := by
        funext i
        simp only [cutCR, hnorm k]
      rw [hcR]
      exact hp)⟩

#print axioms QMCLeafB.Fal36M4.bodyRec_of_oracleCuts

/-- **The record-level residual, at the oracle's own interface.** -/
def OracleRecSlot : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (_hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ¬ QMCLeafB.ThinRec34M4.BodyEmpty G t (Asm35M4.P33 G) →
    Asm35M4.o33 G t = false →
    ∃ (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
      (C : ∀ k : ℕ, QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.EngineRuntime.Rq G / 40000) (Asm35M4.P33 G).dq)
      (cd : ℕ → CutData (G.n * G.n)) (del : ℕ → ℚ),
      (∀ k, (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k).normal)
      ∧ (∀ k, k < (Asm35M4.P33 G).K * (Asm35M4.P33 G).m →
          (Aat (G.n * G.n)
            (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
              (2 * (G.n : ℚ) ^ 2 + 2 * (Asm35M4.P33 G).dq ^ 2)) cd k).mulVec
            (cd k).p = (cd k).c)
      ∧ (∀ k, k < (Asm35M4.P33 G).K * (Asm35M4.P33 G).m → 0 ≤ (cd k).rho)
      ∧ (∀ k, k < (Asm35M4.P33 G).K * (Asm35M4.P33 G).m → (cd k).c ≠ 0)
      ∧ (∀ k, k < (Asm35M4.P33 G).K * (Asm35M4.P33 G).m → 0 ≤ del k)
      ∧ (∀ k, k < (Asm35M4.P33 G).K * (Asm35M4.P33 G).m →
          (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
      ∧ (∀ k, k < (Asm35M4.P33 G).K * (Asm35M4.P33 G).m → (cd k).rho ≤ (Asm35M4.P33 G).rmax)
      ∧ (∀ k, k < (Asm35M4.P33 G).K * (Asm35M4.P33 G).m →
          priceAt (C k) (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k)
            ≤ ((del k : ℚ) : ℝ))

/-- **`OracleRecSlot` gives `BodyRec` / `SelfRec` at the campaign program.** -/
theorem bodyRec_of_oracleRecSlot (H : OracleRecSlot)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (_hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hne : ¬ QMCLeafB.ThinRec34M4.BodyEmpty G t (Asm35M4.P33 G))
    (hb : Asm35M4.o33 G t = false) :
    QMCLeafB.ThinRec34M4.BodyRec G t (Asm35M4.P33 G) := by
  unfold OracleRecSlot at H
  obtain ⟨cX, C, cd, del, hnorm, hwit, hrho, hcne, hdel0, hcheck, hle, hprice⟩ :=
    H G t _hn hlo hlt hne hb
  exact bodyRec_of_oracleCuts (P := Asm35M4.P33 G) cX C cd del hnorm
    hwit hrho hcne hdel0 hcheck hle hprice

#print axioms QMCLeafB.Fal36M4.bodyRec_of_oracleRecSlot

/-- **`OracleRecSlot` gives the leaf's `hfalse` slot**, in exactly the shape
`Pbit33.Hd33_of_relaxMem` consumes. -/
noncomputable def hfalseSlot_of_oracleRecSlot (H : OracleRecSlot) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = false →
      QMCLeafB.FinalStroke.RunParts QMCLeafB.Pbit33.o33 G t (QMCLeafB.Pbit33.P33 G) := by
  intro G t hn hlo hlt hb
  by_cases he : QMCLeafB.ThinRec34M4.BodyEmpty G t (Asm35M4.P33 G)
  · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t (Asm35M4.P33 G) hn hb he
  · exact Classical.choice
      ((QMCLeafB.ThinRec34M4.runParts_false_iff_bodyRec (P := Asm35M4.P33 G) hb).2
        (bodyRec_of_oracleRecSlot H hn hlo hlt he hb))

#print axioms QMCLeafB.Fal36M4.hfalseSlot_of_oracleRecSlot

/-- **THE LEAF FROM `{HokSlot} + {OracleRecSlot}`** — the verbatim `d9f601e5` sentence. -/
theorem solution_via_oracleRec (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : Asm35M4.HokSlot) (H : OracleRecSlot) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Pbit33.solution33 k hk
    (QMCLeafB.Pbit33.Hd33_of_relaxMem hok (hfalseSlot_of_oracleRecSlot H))

#print axioms QMCLeafB.Fal36M4.solution_via_oracleRec


/-- A ball inside the run's relaxation exhibits a point of the relaxed body, so the body is not
empty. -/
theorem not_bodyEmpty_of_ball {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r
      ⊆ QMCLeafB.BallM2.runBall G t P) :
    ¬ QMCLeafB.ThinRec34M4.BodyEmpty G t P := by
  intro he
  have hmem : QMCLeafB.AnswerProducer.flat X₀ ∈ QMCLeafB.BallM2.runBall G t P := by
    apply hball
    show ∑ i : Fin (G.n * G.n),
      (QMCLeafB.AnswerProducer.flat X₀ i - QMCLeafB.AnswerProducer.flat X₀ i) ^ 2 ≤ r ^ 2
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero]
    positivity
  exact he (QMCLeafB.Boundary.unflat (QMCLeafB.AnswerProducer.flat X₀)) hmem.1

#print axioms QMCLeafB.Fal36M4.not_bodyEmpty_of_ball

/-- The campaign ball radius at the phase-33 family, as a real number. -/
noncomputable def ballR (G : QuantumMaxCutEnergy.Input) : ℝ :=
  (((Asm35M4.P33 G).dq : ℝ)) / (8 * ((((Asm35M4.P33 G).cAq : ℝ)) + 1))

/-- **THE SHARP FORM OF (4).**  `OracleRecSlot` is the honest reading of step 1 (the oracle's own
cuts, priced at the engine's centre).  It is INCONSISTENT with a bit-`false` reading at any bracket
point whose body carries the campaign ball: the slot would produce `BodyRec`, which
`not_bodyRec_of_ball` forbids.  So step 1 cannot be used to *derive* the bit's truth there — the
slot fails exactly where step 3 needs it, and the passage to `CompleteSlot` is not a consequence of
`-BodyRec` but an extra program obligation. -/
theorem oracleRecSlot_needs_bit_true {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {hn : 2 ≤ G.n} {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (H : OracleRecSlot)
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) (ballR G)
      ⊆ QMCLeafB.BallM2.runBall G t (Asm35M4.P33 G))
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hb : Asm35M4.o33 G t = false) : False :=
  QMCLeafB.ThinRec34M4.not_bodyRec_of_ball hn hball
    (bodyRec_of_oracleRecSlot H hn hlo hlt
      (not_bodyEmpty_of_ball (P := Asm35M4.P33 G) hball) hb)

#print axioms QMCLeafB.Fal36M4.ballR
#print axioms QMCLeafB.Fal36M4.oracleRecSlot_needs_bit_true

end QMCLeafB.Fal36M4


