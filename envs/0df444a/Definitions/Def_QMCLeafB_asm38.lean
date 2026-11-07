-- Prove2me | Definitions.Def_QMCLeafB_asm38
-- name    : QMCLeafB_asm38
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:08:14.911757+00:00
-- url     : https://prove2.me/theorems/f2c68f5f-2f2a-4463-aa70-52567757ed30
-- title:
--   QMCLeafB asm38
-- statement:
--   # `Check_asm38_m6` — phase 38, member m6, direction `assembly38`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thinrec34
import Definitions.Def_QMCLeafB_asm36
/-
# `Check_asm38_m6` — phase 38, member m6, direction `assembly38`

**Leaf B (`d9f601e5`) and the phase-38 inequality.**  This file DECIDES the phase-38 obligation —
"the ellipsoid centre stays within `rmax` of the body in the current `A_k`-norm at every round" —
and assembles the leaf from its rmax-COLLAR form, which is strictly weaker than the campaign's
banked supporting-cut slot.

## What is taken as given (consumed, not re-derived)

* `ThinRec34M4.BodyRec` / `ShallowCut` / `bodyRec_of_shallowCut` / `relaxBallP`
  (`Check_thinrec34_m4`): the all-cut record class and the shallow-cut datum;
* `Asm36M8.SelfRec` / `solution_of_selfRec` / `solution_of_selfRec_statement` / `selfRec_of_nonempty`
  (`Check_asm36_m8`): the verbatim leaf from `{HokSlot, SelfRec}`;
* `Asm35M4.ShallowSlot` / `SupportSlot` / `sigmaQ_NormalCut_pos` (`Check_asm35_m4`): the campaign's
  slots — `SupportSlot` is the `del ≡ 0` (supporting-cut, centre OUTSIDE the body) form;
* `Giv37M7.no_price_of_deep_rmax` (`Check_giv37_m7`, NOT imported): the sharp failure mode, a body
  point beating `rmax·√σ` kills the round for every normal, centre and presentation.  §4b records its
  trajectory-level shadow here (`not_runParts_of_deepPoint`), so this file is deliberately free of
  the phase-37 cone and co-loads with the phase-37 *Check* files.

## What this file establishes

§1 **The inequality, exactly.**  `suppAt` is the support value `sup_{z∈body} c_k ⧝ (Cat_k − z)` of
the run at round `k`; `BoundAt` is the phase-38 sentence at that round, `Bound` at every round.

§2 **Sup-bookkeeping.**  `relaxBallP` carries a norm bound, so `suppAt` is a genuine supremum
(`bddAbove_suppAt` unconditional, `le_suppAt` unconditional, `suppAt_le_of_pointwise` for the
pointwise-to-sup step including the empty body).

§3 **VERDICT: TRUE — and with the exact constant.**  For every legal all-cut run (every
`RunParts falseBit G t P`: no collar, no fatness, no programme data, no emptiness hypothesis) the
bound holds at every round below the horizon (`bound_of_runParts`), and it holds with the SHARP
constant `ρ_k·√σ_k` (`boundAt_sharp`, `bound_sharp`): the ledger `del² ≤ ρ²σ` (`del_le_rho_sqrt`)
composed with the cut contract `−del ≤ c ⧝ (z − Cat)` gives
`suppAt ≤ ρ_k·√σ_k ≤ rmax·√σ_k`.  So the inequality is *implied* by the run's own depth ledger:
its exact constant is the run's depth, not `rmax`.  What the leaf still owes is the EXISTENCE of a
run, not the inequality.

§4 **The round equivalence.**  At one round, "support value ≤ recorded margin" is literally the
record's `hcut` (`suppAt_le_iff_cutSlot`) — m7's presentation identity at the leaf's own
`relaxBallP` and its own accumulated centre.

§5 **The rationalisation.**  `ShallowCut` records a RATIONAL margin with `del² ≤ rmax²σ`; the
phase-38 inequality is real-valued.  `exists_rat_margin` produces a rational margin whenever
`suppAt < rmax·√σ` (or `suppAt ≤ 0`), using density of `ℚ` in `ℝ` and `√σ`-monotonicity;
`shallowCut_of_suppStrict` therefore turns the real-valued collar bound into the record's rational
ledger.  The one caveat, stated not elided: the exact-tangency case `suppAt = rmax·√σ` with `√σ`
irrational has NO rational margin, so the collar slot is stated with a strict inequality (or
`suppAt ≤ 0`, which covers the supporting-cut case with no positivity needed).

§6 **The collar slot and the assembly.**  `CollarBoundSlot` is the phase-38 inequality at the
campaign programme in the run's own coordinates.  `shallowSlot_of_collarBound` reduces it to the
banked `ShallowSlot`; `collarBound_of_support` shows the banked `SupportSlot` implies it, so the
collar route is a genuine WEAKENING of the campaign's current route;
`solution_via_collarBound` / `solution_via_collarBound_statement` conclude the verbatim `d9f601e5`
sentence, the second in the platform's own type (the statement lock);
`solution_via_support38` re-derives the banked supporting-cut route through the same machinery.

Discipline: `set_option autoImplicit false`; no `sorry`, no `admit`, no `axiom`, no `native_decide`,
no `unsafe`; every `#print axioms` below is exactly `[propext, Classical.choice, Quot.sound]`.

## Logical form (why this is not in tension with the accepted phase-38 refutations)

The verdict is about RUNS, which is the form the leaf's obligation has: `SelfRec` asks for an all-cut
record at a bit-false point, and the inequality is exactly that record's cut slot
(`suppAt_le_iff_cutSlot`).  It is complementary to — not contradicted by — the free-standing reading
refuted by m2/d6 (`Check_eq38_m2`: containment alone gives `≤ √σ`, a factor `4n²` short, and an
`A_k`-ball of radius `> rmax` about `Cat_k` kills every all-cut record) and by m8/d4
(`Check_op38_m8`: the round is unrecordable iff the body's interior swallows the closed `A`-ball of
radius rmax about `Cat_k`).  In this file's vocabulary: at such a body no `B : RunParts falseBit G t P`
exists, so `Bound` holds only vacuously — which is what `not_runParts_of_deepPoint` says at the
trajectory level.  The inequality can never be *violated* by a record (§3) and can be *unsatisfiable*
at fat bodies (m2/m8); the leaf's residue is therefore the shape/satisfiability question, and
`CollarBoundSlot` is where it lives.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators
open Matrix

namespace QMCLeafB.Asm38M6

open QuantumMaxCutEnergy

/-! ## 1.  The phase-38 inequality, exactly -/

/-- The body of the record at `(G,t,P)` in flat coordinates — `ThinRec34M4.relaxBallP`. -/
abbrev body (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Set (Fin (G.n * G.n) → ℝ) :=
  QMCLeafB.ThinRec34M4.relaxBallP G t P

/-- The relaxation's norm bound `M = 2n² + 2dq²`, as a real number. -/
abbrev Mball (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) : ℝ :=
  ((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ) : ℝ)

/-- The flat cut normal at round `k`. -/
abbrev nrm {G : QuantumMaxCutEnergy.Input}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (k : ℕ) : Fin (G.n * G.n) → ℝ :=
  QMCLeafB.EngineIterates.cutCR cd k

/-- The accumulated point at round `k` — the ellipsoid centre `Cat_k`. -/
abbrev ctr {G : QuantumMaxCutEnergy.Input}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (k : ℕ) : Fin (G.n * G.n) → ℝ :=
  QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k

/-- `√σ_k`, the `A_k`-norm of the cut normal, as a real number. -/
abbrev ssqrt {G : QuantumMaxCutEnergy.Input}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (k : ℕ) : ℝ :=
  Real.sqrt (((QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p : ℚ) : ℝ))

/-- The support value at round `k`: `sup_{z∈body} c_k ⧝ (Cat_k − z)`, the left-hand side of the
phase-38 inequality.  It is `sSup` of the image of the body under the cut's own normal. -/
def suppAt (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (k : ℕ) : ℝ :=
  sSup ((fun z : Fin (G.n * G.n) → ℝ => nrm cd k ⬝ᵥ (ctr cd k - z)) '' body G t P)

/-- **The phase-38 inequality at round `k`**: `sup_{z∈body} c_k ⧝ (Cat_k − z) ≤ rmax·√σ_k` — the
ellipsoid centre `Cat_k` lies within `rmax` of the body in the `A_k`-norm, in the cut's direction. -/
def BoundAt (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (k : ℕ) : Prop :=
  suppAt G t P cd k ≤ (P.rmax : ℝ) * ssqrt cd k

/-- **The phase-38 inequality for a whole run**: it holds at every round below the horizon. -/
def Bound (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) : Prop :=
  ∀ k, k < P.K * P.m → BoundAt G t P cd k

/-! ## 2.  Sup-bookkeeping

`relaxBallP` carries the norm bound `∑ zᵢ² ≤ M`, so the support image is bounded above by the crude
constant `∑ᵢ |cᵢ|(|Catᵢ| + √M)`: `suppAt` is a genuine supremum, `le_suppAt` holds
unconditionally, and a pointwise bound upgrades to the supremum. -/

/-- **The support image is bounded above** — unconditionally, from the relaxation's norm bound. -/
theorem bddAbove_suppAt (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (k : ℕ) :
    BddAbove ((fun z : Fin (G.n * G.n) → ℝ => nrm cd k ⬝ᵥ (ctr cd k - z)) '' body G t P) := by
  refine ⟨∑ i, |nrm cd k i| * (|ctr cd k i| + Real.sqrt (Mball G P)), ?_⟩
  rintro v ⟨z, hz, rfl⟩
  have hzb : ∀ i, |z i| ≤ Real.sqrt (Mball G P) := by
    intro i
    have h1 : z i ^ 2 ≤ (∑ j, z j ^ 2) :=
      Finset.single_le_sum (f := fun j => z j ^ 2) (fun j _ => sq_nonneg (z j))
        (Finset.mem_univ i)
    have hsq : (|z i|) ^ 2 ≤ Mball G P := by
      rw [sq_abs]
      exact le_trans h1 hz.2
    calc |z i| = Real.sqrt ((|z i|) ^ 2) := (Real.sqrt_sq (abs_nonneg _)).symm
      _ ≤ Real.sqrt (Mball G P) := Real.sqrt_le_sqrt hsq
  have hterm : ∀ i, nrm cd k i * (ctr cd k i - z i)
      ≤ |nrm cd k i| * (|ctr cd k i| + Real.sqrt (Mball G P)) := by
    intro i
    have h4 : |ctr cd k i - z i| ≤ |ctr cd k i| + Real.sqrt (Mball G P) := by
      have h3 : |ctr cd k i - z i| ≤ |ctr cd k i| + |z i| := abs_sub _ _
      have := hzb i; linarith
    have habs : nrm cd k i * (ctr cd k i - z i) ≤ |nrm cd k i| * |ctr cd k i - z i| := by
      calc nrm cd k i * (ctr cd k i - z i) ≤ |nrm cd k i * (ctr cd k i - z i)| := le_abs_self _
        _ = |nrm cd k i| * |ctr cd k i - z i| := abs_mul _ _
    have h5 := mul_le_mul_of_nonneg_left h4 (abs_nonneg (nrm cd k i))
    linarith
  calc nrm cd k ⬝ᵥ (ctr cd k - z)
      = ∑ i, nrm cd k i * (ctr cd k i - z i) := rfl
    _ ≤ ∑ i, |nrm cd k i| * (|ctr cd k i| + Real.sqrt (Mball G P)) :=
        Finset.sum_le_sum (fun i _ => hterm i)

#print axioms QMCLeafB.Asm38M6.bddAbove_suppAt

/-- **A body point is at most the support value.** -/
theorem le_suppAt (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (k : ℕ)
    {z : Fin (G.n * G.n) → ℝ} (hz : z ∈ body G t P) :
    nrm cd k ⬝ᵥ (ctr cd k - z) ≤ suppAt G t P cd k :=
  le_csSup (bddAbove_suppAt G t P cd k) (Set.mem_image_of_mem _ hz)

#print axioms QMCLeafB.Asm38M6.le_suppAt

/-- **A pointwise bound bounds the support value** (empty body: `sSup ∅ = 0 ≤ B`). -/
theorem suppAt_le_of_pointwise (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (k : ℕ) {B : ℝ}
    (h : ∀ z ∈ body G t P, nrm cd k ⬝ᵥ (ctr cd k - z) ≤ B) (hB : 0 ≤ B) :
    suppAt G t P cd k ≤ B := by
  rcases (body G t P).eq_empty_or_nonempty with hemp | hne
  · rw [suppAt, hemp, Set.image_empty, Real.sSup_empty]
    exact hB
  · exact csSup_le (hne.image _) (by rintro v ⟨z, hz, rfl⟩; exact h z hz)

#print axioms QMCLeafB.Asm38M6.suppAt_le_of_pointwise

/-! ## 2b.  The empty body: the collar is free there

`BodyEmpty` speaks about matrices; the flat relaxation `relaxBallP` is its preimage under `unflat`,
so an empty body makes the support value `sSup ∅ = 0` — the `suppAt ≤ 0` branch of the collar slot is
then automatic for EVERY normal stream.  This is why the slot below carries no emptiness
hypothesis. -/

/-- **An empty recorded body is the empty set in flat coordinates.** -/
theorem body_eq_empty_of_bodyEmpty {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (hemp : QMCLeafB.ThinRec34M4.BodyEmpty G t P) : body G t P = ∅ := by
  ext z
  constructor
  · intro hz
    exact hemp (QMCLeafB.Boundary.unflat z) hz.1
  · intro hz
    exact absurd hz (Set.notMem_empty z)

#print axioms QMCLeafB.Asm38M6.body_eq_empty_of_bodyEmpty

/-- **The support value vanishes at an empty body.** -/
theorem suppAt_eq_zero_of_bodyEmpty {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (hemp : QMCLeafB.ThinRec34M4.BodyEmpty G t P)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (k : ℕ) :
    suppAt G t P cd k = 0 := by
  rw [suppAt, body_eq_empty_of_bodyEmpty hemp, Set.image_empty, Real.sSup_empty]

#print axioms QMCLeafB.Asm38M6.suppAt_eq_zero_of_bodyEmpty

/-- **At an empty body the collar round is free for every stream**: the `suppAt ≤ 0` branch always
holds, so `CollarBoundSlot` owes nothing there. -/
theorem collarRound_of_bodyEmpty {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (hemp : QMCLeafB.ThinRec34M4.BodyEmpty G t P)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (k : ℕ) :
    suppAt G t P cd k < (P.rmax : ℝ) * ssqrt cd k ∨ suppAt G t P cd k ≤ 0 :=
  Or.inr (le_of_eq (suppAt_eq_zero_of_bodyEmpty hemp cd k))

#print axioms QMCLeafB.Asm38M6.collarRound_of_bodyEmpty

/-! ## 3.  VERDICT: the inequality holds on every legal run, with the exact constant `ρ_k·√σ_k` -/

/-- **The recorded margin never exceeds `ρ·√σ`** — the sharp form of `del_le_rmax_sqrt`, with no
positivity hypothesis on `σ` (`σ < 0` forces `del = 0` and `√σ = 0`). -/
theorem del_le_rho_sqrt {n : ℕ} {c p : Fin n → ℚ} {ρ del : ℚ}
    (hρ : 0 ≤ ρ) (hdel0 : 0 ≤ del)
    (hchk : del ^ 2 ≤ ρ ^ 2 * QMCLeafB.EngineIterates.sigmaQ c p) :
    (del : ℝ) ≤ (ρ : ℝ) * Real.sqrt (((QMCLeafB.EngineIterates.sigmaQ c p : ℚ) : ℝ)) := by
  by_cases hσ : (0 : ℚ) ≤ QMCLeafB.EngineIterates.sigmaQ c p
  · exact QMCLeafB.EngineIterates.margin_le_of_sq_check hdel0 hρ hσ hchk
  · have hσ' : ((QMCLeafB.EngineIterates.sigmaQ c p : ℚ) : ℝ) ≤ 0 := by
      have hlt : QMCLeafB.EngineIterates.sigmaQ c p < 0 := lt_of_not_ge hσ
      exact_mod_cast hlt.le
    have h1 : del ^ 2 ≤ 0 := by
      have h2 : (0 : ℚ) ≤ ρ ^ 2 := sq_nonneg ρ
      nlinarith
    have h2 : del = 0 := by nlinarith [sq_nonneg del]
    rw [h2, Real.sqrt_eq_zero'.2 hσ']
    simp

#print axioms QMCLeafB.Asm38M6.del_le_rho_sqrt

/-- **The recorded `ok` flag of an all-false record is `false` at every round below the horizon.** -/
theorem ok_false_of_falseBit {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts QMCLeafB.ThinRec34M4.falseBit G t P)
    {k : ℕ} (hk : k < P.K * P.m) : B.ok k = false :=
  (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).1 B.hverdict.symm k hk

#print axioms QMCLeafB.Asm38M6.ok_false_of_falseBit

/-- **The sharp bound at one round of a legal all-cut run**: the support value is at most
`ρ_k·√σ_k` — the run's own depth, not `rmax`. -/
theorem boundAt_sharp {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts QMCLeafB.ThinRec34M4.falseBit G t P)
    {k : ℕ} (hk : k < P.K * P.m) :
    suppAt G t P B.cd k ≤ ((B.cd k).rho : ℝ) * ssqrt B.cd k := by
  have hok := ok_false_of_falseBit B hk
  have hcut := B.hcut k hk hok
  have hchk := B.hcheck k hk hok
  have hdel0 := B.hdel0 k hk hok
  have hrho := B.hrho k hk hok
  have hdel : ((B.del k : ℚ) : ℝ) ≤ ((B.cd k).rho : ℝ) * ssqrt B.cd k :=
    del_le_rho_sqrt hrho hdel0 hchk
  refine suppAt_le_of_pointwise G t P B.cd k (fun z hz => ?_)
    (mul_nonneg (by exact_mod_cast hrho) (Real.sqrt_nonneg _))
  have h := hcut z hz
  rw [dotProduct_sub] at h ⊢
  linarith

#print axioms QMCLeafB.Asm38M6.boundAt_sharp

/-- **The phase-38 inequality at one round of any legal all-cut run** — no hypotheses beyond the
record. -/
theorem boundAt_of_runParts {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts QMCLeafB.ThinRec34M4.falseBit G t P)
    {k : ℕ} (hk : k < P.K * P.m) : BoundAt G t P B.cd k := by
  refine le_trans (boundAt_sharp B hk) (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  exact_mod_cast B.hle k hk (ok_false_of_falseBit B hk)

#print axioms QMCLeafB.Asm38M6.boundAt_of_runParts

/-- **VERDICT (TRUE, unconditional at the run level).**  Every legal all-cut run keeps its
accumulated centre within `rmax` of the body in the current `A_k`-norm, at every round below the
horizon. -/
theorem bound_of_runParts {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts QMCLeafB.ThinRec34M4.falseBit G t P) :
    Bound G t P B.cd :=
  fun k hk => boundAt_of_runParts B hk

#print axioms QMCLeafB.Asm38M6.bound_of_runParts

/-- The same verdict with the sharp constant: `suppAt ≤ ρ_k·√σ_k` at every round. -/
theorem bound_sharp {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts QMCLeafB.ThinRec34M4.falseBit G t P) :
    ∀ k, k < P.K * P.m → suppAt G t P B.cd k ≤ ((B.cd k).rho : ℝ) * ssqrt B.cd k :=
  fun k hk => boundAt_sharp B hk

#print axioms QMCLeafB.Asm38M6.bound_sharp

/-- **The campaign's shallow ceiling is exactly `rmaxOf (n·n) = 1/(4n²)`.** -/
theorem rmax_P33 (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.Pbit33.P33 G).rmax = 1 / (4 * (G.n : ℚ) ^ 2) := by
  have h : (QMCLeafB.Pbit33.P33 G).rmax
      = 1 / (4 * ((G.n * G.n : ℕ) : ℚ)) := rfl
  rw [h]
  push_cast
  ring

#print axioms QMCLeafB.Asm38M6.rmax_P33

/-- **THE VERDICT AT THE PROBLEM'S OWN CONSTANT.**  On every legal all-cut run at the campaign
parameters, `sup_{z∈body} c_k ⧝ (Cat_k − z) ≤ (1/(4n²))·√σ_k` at every round below the horizon: the
ellipsoid centre stays within `rmax = rmaxOf (n·n) = 1/(4n²)` of the body in the current `A_k`-norm.
No hypothesis beyond the run. -/
theorem bound_campaign_constant {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (B : QMCLeafB.FinalStroke.RunParts QMCLeafB.ThinRec34M4.falseBit G t
      (QMCLeafB.Pbit33.P33 G))
    {k : ℕ} (hk : k < (QMCLeafB.Pbit33.P33 G).K * (QMCLeafB.Pbit33.P33 G).m) :
    suppAt G t (QMCLeafB.Pbit33.P33 G) B.cd k
      ≤ ((1 / (4 * (G.n : ℚ) ^ 2) : ℚ) : ℝ) * ssqrt B.cd k := by
  have hleQ : (B.cd k).rho ≤ 1 / (4 * (G.n : ℚ) ^ 2) := by
    have h := B.hle k hk (ok_false_of_falseBit B hk)
    rwa [rmax_P33] at h
  have hle : ((B.cd k).rho : ℝ) ≤ ((1 / (4 * (G.n : ℚ) ^ 2) : ℚ) : ℝ) := by
    exact_mod_cast hleQ
  exact le_trans (bound_sharp B k hk) (mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _))

#print axioms QMCLeafB.Asm38M6.bound_campaign_constant

/-- **The verdict transported to the leaf's own slot.**  `SelfRec` is inhabited only through a
record, so it forces the phase-38 inequality on that record's trajectory: the inequality is never the
obstruction — producing the run is. -/
theorem exists_bound_of_bodyRec {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.ThinRec34M4.BodyRec G t P) :
    ∃ cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n), Bound G t P cd :=
  let ⟨B⟩ := H
  ⟨B.cd, bound_of_runParts B⟩

#print axioms QMCLeafB.Asm38M6.exists_bound_of_bodyRec

/-- **Non-vacuity of the verdict.**  At an empty body there IS an all-cut record
(`RefutedM3.runParts_of_emptyBody` through `ThinRec34M4.bodyRec_of_emptyBody`), hence a trajectory
that satisfies the phase-38 inequality.  So §3 is not a vacuous implication — the campaign's
recurring vacuity defect does not apply to the verdict. -/
theorem exists_bound_nonvacuous {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (hemp : QMCLeafB.ThinRec34M4.BodyEmpty G t P) :
    ∃ cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n), Bound G t P cd :=
  exists_bound_of_bodyRec (QMCLeafB.ThinRec34M4.bodyRec_of_emptyBody hn hemp)

#print axioms QMCLeafB.Asm38M6.exists_bound_nonvacuous

/-! ## 4.  The round equivalence: "support value ≤ margin" IS the record's `hcut` -/

/-- **`hcut` ⟺ the support bound at the recorded margin.**  m7's presentation identity, at the
leaf's own `relaxBallP` and its own accumulated centre: the two statements are the same proposition. -/
theorem suppAt_le_iff_cutSlot {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (k : ℕ) {del : ℚ}
    (hdel0 : 0 ≤ del) :
    suppAt G t P cd k ≤ (del : ℝ)
      ↔ ∀ z ∈ body G t P, nrm cd k ⬝ᵥ (ctr cd k - z) ≤ (del : ℝ) := by
  constructor
  · intro h z hz
    exact le_trans (le_suppAt G t P cd k hz) h
  · intro h
    exact suppAt_le_of_pointwise G t P cd k h (by exact_mod_cast hdel0)

#print axioms QMCLeafB.Asm38M6.suppAt_le_iff_cutSlot

/-! ## 4b.  The sharp failure mode, at the leaf's own trajectory

m7's `no_price_of_deep_rmax` (`Check_giv37_m7`) says a body point beating `rmax·√σ` kills the round
for every centre, normal and presentation.  At the leaf's own vocabulary the same is a one-liner from
§3: a stream with a deep round is the transcript of NO record.  Together with §3 this is the
two-sided reading of the inequality: it holds on every run, and it is exactly what a run has to
deliver, so a violation is never an inequality failure but a non-existence property. -/

/-- **A deep body point kills the round for the whole stream.** -/
theorem not_runParts_of_deepPoint {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)} {k : ℕ} (hk : k < P.K * P.m)
    {z : Fin (G.n * G.n) → ℝ} (hz : z ∈ body G t P)
    (hdeep : (P.rmax : ℝ) * ssqrt cd k < nrm cd k ⬝ᵥ (ctr cd k - z)) :
    ¬ ∃ B : QMCLeafB.FinalStroke.RunParts QMCLeafB.ThinRec34M4.falseBit G t P, B.cd = cd := by
  rintro ⟨B, rfl⟩
  have hb : suppAt G t P B.cd k ≤ (P.rmax : ℝ) * ssqrt B.cd k := boundAt_of_runParts B hk
  have hp := le_suppAt G t P B.cd k hz
  linarith

#print axioms QMCLeafB.Asm38M6.not_runParts_of_deepPoint

/-! ## 5.  The rationalisation: a strict support bound gives the record's RATIONAL margin

`ShallowCut` asks for a rational `del` with `del² ≤ rmax²·σ`.  Given `S < rmax·√σ` with `σ ≥ 0` and
`rmax ≥ 0`, a rational lies strictly between them and its square stays below `rmax²·σ`; if `S ≤ 0`
then `del = 0` already works.  So the real-valued collar bound IS recordable — except at exact
tangency with an irrational `√σ`, which is why the collar slot below is stated strictly. -/

/-- **A rational margin exists under a strict support bound** (`S ≤ 0` also suffices). -/
theorem exists_rat_margin {σ rmax : ℚ} {S : ℝ} (hσ : 0 ≤ σ) (hrmax : 0 ≤ rmax)
    (h : S < (rmax : ℝ) * Real.sqrt ((σ : ℚ) : ℝ) ∨ S ≤ 0) :
    ∃ del : ℚ, 0 ≤ del ∧ del ^ 2 ≤ rmax ^ 2 * σ ∧ S ≤ (del : ℝ) := by
  have hnn : (0 : ℚ) ≤ rmax ^ 2 * σ := mul_nonneg (sq_nonneg _) hσ
  rcases h with hlt | hle0
  · by_cases hS : S ≤ 0
    · exact ⟨0, le_rfl, by simpa using hnn, by simpa using hS⟩
    · push Not at hS
      obtain ⟨d, hd1, hd2⟩ := exists_rat_btwn hlt
      have hd0 : (0 : ℚ) ≤ d := by
        have h0d : (0 : ℝ) < (d : ℝ) := lt_trans hS hd1
        exact_mod_cast h0d.le
      refine ⟨d, hd0, ?_, le_of_lt hd1⟩
      have hsq : ((d : ℝ)) ^ 2 < ((rmax : ℝ) * Real.sqrt ((σ : ℚ) : ℝ)) ^ 2 := by
        nlinarith [lt_trans hS hd1]
      rw [mul_pow, Real.sq_sqrt (by exact_mod_cast hσ)] at hsq
      have hgoal : ((d : ℚ) : ℝ) ^ 2 ≤ ((rmax : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ) :=
        le_of_lt hsq
      exact_mod_cast hgoal
  · exact ⟨0, le_rfl, by simpa using hnn, by simpa using hle0⟩

#print axioms QMCLeafB.Asm38M6.exists_rat_margin

/-- **The real-valued collar bound gives the record's rational shallow-cut datum.**  `hbound` is the
phase-38 inequality at every round of the canonical `runCut` trajectory, in its strict form (or with
`suppAt ≤ 0`, which is the supporting-cut regime). -/
theorem shallowCut_of_suppStrict {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (hbound : ∀ k, k < P.K * P.m →
      suppAt G t P (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k
          < (P.rmax : ℝ) * ssqrt (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k
        ∨ suppAt G t P (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k ≤ 0) :
    QMCLeafB.ThinRec34M4.ShallowCut G t P hn := by
  classical
  have hex : ∀ k, k < P.K * P.m → ∃ d : ℚ, 0 ≤ d ∧ d ^ 2 ≤ P.rmax ^ 2 *
      QMCLeafB.EngineIterates.sigmaQ (c k)
        ((QMCLeafB.ThinRec34M4.NormalCut G P hn c hc k).p) ∧
      suppAt G t P (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k ≤ (d : ℝ) := by
    intro k hk
    have hσ : (0 : ℚ) ≤ QMCLeafB.EngineIterates.sigmaQ (c k)
        ((QMCLeafB.ThinRec34M4.NormalCut G P hn c hc k).p) :=
      le_of_lt (Asm35M4.sigmaQ_NormalCut_pos (P := P) hn c hc k)
    rcases hbound k hk with hlt | hle
    · exact exists_rat_margin hσ P.hrmax (Or.inl hlt)
    · exact exists_rat_margin hσ P.hrmax (Or.inr hle)
  refine ⟨c, hc, fun k => if h : k < P.K * P.m then Classical.choose (hex k h) else 0,
    ?_, ?_, ?_⟩
  · intro k hk
    simp only [dif_pos hk]
    exact (Classical.choose_spec (hex k hk)).1
  · intro k
    by_cases hk : k < P.K * P.m
    · simp only [dif_pos hk]
      exact (Classical.choose_spec (hex k hk)).2.1
    · simp only [dif_neg hk]
      have hσ : (0 : ℚ) ≤ QMCLeafB.EngineIterates.sigmaQ (c k)
          ((QMCLeafB.ThinRec34M4.NormalCut G P hn c hc k).p) :=
        le_of_lt (Asm35M4.sigmaQ_NormalCut_pos (P := P) hn c hc k)
      nlinarith [sq_nonneg P.rmax]
  · intro k hk z hz
    have hd : suppAt G t P (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k
        ≤ ((if h : k < P.K * P.m then Classical.choose (hex k h) else 0 : ℚ) : ℝ) := by
      simp only [dif_pos hk]
      exact (Classical.choose_spec (hex k hk)).2.2
    have h1 : nrm (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k
        ⬝ᵥ (ctr (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k - z)
        ≤ ((if h : k < P.K * P.m then Classical.choose (hex k h) else 0 : ℚ) : ℝ) :=
      le_trans (le_suppAt G t P (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k hz) hd
    rw [dotProduct_sub] at h1
    exact h1

#print axioms QMCLeafB.Asm38M6.shallowCut_of_suppStrict

/-! ## 6.  The collar slot at the campaign programme, and the assembly -/

/-- **THE COLLAR SLOT — the phase-38 inequality at the campaign programme.**  At every bit-`false`
interior bracket point there is a nonzero rational normal stream whose accumulated centres stay
within the `rmax`-collar of the relaxation at every round below the horizon: the support value is
strictly below `rmax·√σ_k`, or at most `0` (the supporting-cut regime).  No emptiness, fatness or
collar hypothesis: where the body is empty the slot is free (`Asm35M4.shallowCut_of_emptyBody`). -/
def CollarBoundSlot : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)) →
    QMCLeafB.Pbit33.o33 G t = false →
    ∃ (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0),
      ∀ k, k < (QMCLeafB.Pbit33.P33 G).K * (QMCLeafB.Pbit33.P33 G).m →
        suppAt G t (QMCLeafB.Pbit33.P33 G)
            (QMCLeafB.ThinRec34M4.NormalCut G (QMCLeafB.Pbit33.P33 G) hn c hc) k
            < ((QMCLeafB.Pbit33.P33 G).rmax : ℝ)
              * ssqrt (QMCLeafB.ThinRec34M4.NormalCut G (QMCLeafB.Pbit33.P33 G) hn c hc) k
        ∨ suppAt G t (QMCLeafB.Pbit33.P33 G)
            (QMCLeafB.ThinRec34M4.NormalCut G (QMCLeafB.Pbit33.P33 G) hn c hc) k ≤ 0

#print axioms QMCLeafB.Asm38M6.CollarBoundSlot

/-- **The collar slot gives the campaign's `ShallowSlot`** — via the rationalisation of §5. -/
theorem shallowSlot_of_collarBound (H : CollarBoundSlot) : Asm35M4.ShallowSlot := by
  intro G t hn hlo hlt hb
  obtain ⟨c, hc, hbound⟩ := H G t hn hlo hlt hb
  exact shallowCut_of_suppStrict c hc hbound

#print axioms QMCLeafB.Asm38M6.shallowSlot_of_collarBound

/-- **The banked supporting-cut slot implies the collar slot** — so the phase-38 route is a genuine
WEAKENING: it allows the accumulated centre to sit inside the body by up to `rmax`. -/
theorem collarBound_of_support (H : Asm35M4.SupportSlot) : CollarBoundSlot := by
  intro G t hn hlo hlt hb
  obtain ⟨c, hc, hsupp⟩ := H G t hn hlo hlt hb
  refine ⟨c, hc, fun k hk => Or.inr ?_⟩
  refine suppAt_le_of_pointwise G t (QMCLeafB.Pbit33.P33 G)
    (QMCLeafB.ThinRec34M4.NormalCut G (QMCLeafB.Pbit33.P33 G) hn c hc) k (fun z hz => ?_) le_rfl
  have h := hsupp k hk z hz
  rw [dotProduct_sub] at h ⊢
  linarith

#print axioms QMCLeafB.Asm38M6.collarBound_of_support

/-- **The collar slot gives `SelfRec`** — through the banked `selfRec_of_nonempty` and the record
class of `ThinRec34M4`. -/
theorem selfRec_of_collarBound (H : CollarBoundSlot) : QMCLeafB.Asm36M8.SelfRec :=
  QMCLeafB.Asm36M8.selfRec_of_nonempty (fun G t hn hlo hlt hb _ =>
    QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn
      (shallowSlot_of_collarBound H G t hn hlo hlt hb))

#print axioms QMCLeafB.Asm38M6.selfRec_of_collarBound

/-! ### 6b.  The phase-38 inequality as a slot at the campaign programme

`BoundSlot` is the phase-38 sentence itself at the campaign programme, with the trajectory
existential: at every bit-`false` interior bracket point there IS a run of the engine whose
accumulated centres stay within `rmax` of the body at every round.  `boundSlot_of_selfRec` derives it
from the leaf's own residual slot, and `boundSlot_of_collarBound` from the collar slot — so the
inequality is not an extra hypothesis anywhere in the assembly. -/

/-- **THE PHASE-38 INEQUALITY, AS A SLOT** at the campaign programme. -/
def BoundSlot : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)) →
    QMCLeafB.Pbit33.o33 G t = false →
    ∃ cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n),
      Bound G t (QMCLeafB.Pbit33.P33 G) cd

#print axioms QMCLeafB.Asm38M6.BoundSlot

/-- **The leaf's own residual slot forces the phase-38 inequality.**  `SelfRec` is inhabited only
through an all-cut record, and every record satisfies the inequality (§3): so `SelfRec ⟹ BoundSlot`,
with no extra work and no extra hypothesis. -/
theorem boundSlot_of_selfRec (H : QMCLeafB.Asm36M8.SelfRec) : BoundSlot :=
  fun G t hn hlo hlt hb => exists_bound_of_bodyRec (H G t hn hlo hlt hb)

#print axioms QMCLeafB.Asm38M6.boundSlot_of_selfRec

/-- **The collar slot forces the phase-38 inequality** — on the very trajectory it exhibits. -/
theorem boundSlot_of_collarBound (H : CollarBoundSlot) : BoundSlot := by
  intro G t hn hlo hlt hb
  obtain ⟨c, hc, hbound⟩ := H G t hn hlo hlt hb
  refine ⟨QMCLeafB.ThinRec34M4.NormalCut G (QMCLeafB.Pbit33.P33 G) hn c hc, fun k hk => ?_⟩
  rcases hbound k hk with hlt | hle
  · exact le_of_lt hlt
  · exact le_trans hle (mul_nonneg (by exact_mod_cast (QMCLeafB.Pbit33.P33 G).hrmax)
      (Real.sqrt_nonneg _))

#print axioms QMCLeafB.Asm38M6.boundSlot_of_collarBound

/-- **THE LEAF FROM THE COLLAR BOUND.**  The verbatim `d9f601e5` sentence at the campaign programme
from the upper slot and the phase-38 collar inequality — the exact one-hypothesis form. -/
theorem solution_via_collarBound (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : Asm35M4.HokSlot) (H : CollarBoundSlot) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Asm36M8.solution_of_selfRec k hk hok (selfRec_of_collarBound H)

#print axioms QMCLeafB.Asm38M6.solution_via_collarBound

/-- The same in the platform's own type (the `d9f601e5` sentence, written out) — the statement
lock. -/
theorem solution_via_collarBound_statement (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : Asm35M4.HokSlot) (H : CollarBoundSlot) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.Asm36M8.solution_of_selfRec_statement k hk hok (selfRec_of_collarBound H)

#print axioms QMCLeafB.Asm38M6.solution_via_collarBound_statement

/-- **Cross-check of the banked route.**  The campaign's supporting-cut slot implies the collar
slot, so `solution_via_collarBound` recovers the banked `Asm35M4.solution_via_support`: the two
routes agree, and the collar route is the weaker hypothesis. -/
theorem solution_via_support38 (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : Asm35M4.HokSlot) (H : Asm35M4.SupportSlot) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_via_collarBound k hk hok (collarBound_of_support H)

#print axioms QMCLeafB.Asm38M6.solution_via_support38

/-! ## 7.  The statement lock

The platform's `d9f601e5` sentence is `FinishLine.SolutionStatement`, and the type of
`solution_via_collarBound_statement` is that sentence written out.  `statement_lock` is the machine
check that the two are the same proposition: the sentence closed here is the sentence served. -/

/-- **THE STATEMENT LOCK.** -/
theorem statement_lock :
    QMCLeafB.FinishLine.SolutionStatement ↔
      ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
        Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
          QuantumMaxCutEnergy.encodeValue
          (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
        ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
          ModernConvex.Relaxations.IsMaxcutSDPValue
            (Matrix.of fun i j : Fin G.n =>
              if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
              else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
          (L G : ℝ) ≤ S ∧
          S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  Iff.rfl

#print axioms QMCLeafB.Asm38M6.statement_lock

end QMCLeafB.Asm38M6


