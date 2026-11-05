-- Prove2me | Definitions.Def_QMCLeafB_fal28
-- name    : QMCLeafB_fal28
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:43:00.526658+00:00
-- url     : https://prove2.me/theorems/eb037f45-5c5a-4562-a3e9-98f2a9ab7d5b
-- title:
--   QMCLeafB fal28
-- statement:
--   # `Check_fal28_m5` — phase 28, direction `falsify28` (m5)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_traj_m3
/-
# `Check_fal28_m5` — phase 28, direction `falsify28` (m5)

Adversarial audit of the P* / `TestRun` programme before the construction is built out.
Three attacks were registered.  Verdicts, all machine-checked below.

## Attack (i) — does a non-member centre always give a separating direction?

**NO KILL.**  `RelaxOracle.relaxMem_or_cut` is the exact dichotomy over rational centres:
`RelaxMem A cX u δ ∨ Nonempty (RelaxCut A cX u δ)`, and the `RelaxCut` side carries
`margin_pos : 0 < margin` against the *whole real* relaxation.  So the case the attack looked
for — "the centre violates only the psd margin and no direction separates the body" — cannot
occur: the three violated slots give the normals `v vᵀ`, `±e_i e_iᵀ`, `-A`, each with a strictly
positive margin.  Restated as `cut_of_not_relaxMem` / `cut_separates_whole_body` in §1.

## Attack (iii) — is the visit theorem's `htest` a hidden gap?

**THE PREMISE IS FALSE, and that is the finding.**  `TestRun` carries *no coherence condition
between its centres `cX` and the run*: the structure is literally `toParts`, `cX`, `htest`
(`TrajM3.TestRun`), and nothing says `cX k` is round `k`'s state.  Consequently the centre
sequence is a *relabelling*: given the run's own `ok` stream, one fixed member and one fixed
non-member serve as the centres, round by round (`testRun_of_centres`), because `htest` is an
iff whose two sides are decided by the `ok` bit.  The sharp form is `testRun_iff`:

> `TestRun o G t P` is inhabited **iff** every round that reports `ok` has *some* rational member
> (and a non-member exists, which it always does, `nonmember_zero`).

So the cost is `RunParts o G t P` + one rational member per `ok` round — and the banked
non-vacuity witness `TrajM3.sliver_testRun` already uses a constant centre, the same fact in
miniature.  Therefore:

* no *exact/certified membership test* has to live inside P*'s round function for the sake of
  `htest` — including at `n ≥ 3`, where `Check_ctest_m8` §3 shows the snapped descent answers
  `true` at the campaign's canonical (tight) member.  That receipt does **not** block the family;
  it only means P* cannot *stop* on the strength of the descent's boolean;
* the content of the reduction is entirely `RunParts` (the cut stream: `hwit`, `hcheck`, `hle`,
  `hcut`, `hdel0`) plus the one implication `campaignBit G t = true → ∃ a rational member` — the
  density / ok-branch repair (`hcert_of_relaxMem`-class material), and the true home of the
  certified-grid work.

## Attack (ii) — are `RunParts`' numeric slots satisfiable at the frozen constants?

**NO KILL, but the slot is not where the risk is.**  `RunParams`' fields (`dq`, `cAq`, `rmax`,
`K`, `m`, `hAsum`, `hhalve`, `hbudget`) mention neither `o` nor `t`: they are `paramsKbc2`'s,
and were discharged there.  The threshold-dependent content is `RunParts`, which the two lanes
cover (`ok ≡ true` at a member-bearing body, `hcert` via `hcert_of_relaxMem`; `ok ≡ false` at a
body with no member, where `hcut` is vacuous).  What the attack should have asked, and what
`testRun_iff` now isolates, is the single implication of §4.

## What the audit delivers (the constructive fallout)

§4b–§5b close the *assembly* side of phase 28 outright:

* `testRun_iff` :
  `(∃ T : TestRun o G t P, T.toParts = B) ↔ ((∃ k, B.ok k = true) → ∃ Q, RelaxMem … Q)`;
* `testRunFamilyOfSoundFlags` : the whole family `∀ G t, TestRun campaignBit G t (paramsKbc2 G)`
  from the `RunParts` family + the `∃`-form *soundness* of the flags + one non-member per point
  (`nonmember_exists` supplies it at every `n > 0` and every `dq` — no `dq < 4` bound);
* **`target_of_runPartsFamily : QMCLeafB.Audit25M8.Target`** — the verbatim `d9f601e5` sentence
  (`Audit25M8.statement_lock`), from exactly those inputs.

So the named residual of phase 28 is **not** "P*'s round function must implement the membership
test".  It is:

1. `RunParts campaignBit G t (paramsKbc2 G)` at every `(G,t)` — the cut-stream ledger
   (`hwit`, `hcheck`, `hle`, `hcut`, `hdel0`);
2. the **soundness** half of the ok flag: "some round reported `ok` ⟹ a rational member exists"
   (`sound_flags_of_test` is the per-round form, which is exactly what
   `LdltCertM5.pivPsdMargin_of_tolerance` gives).

Completeness of the test (member ⟹ ok) is *not* needed anywhere, nor the grid, nor the tolerance;
and `RunParts.hcert`'s witness is decoupled from the queried centre, so an ok round is certified
by *any* exact unit-diagonal PSD point inside the leaf's level.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
axiom receipts at the end (expected `[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Fal28M5

open QuantumMaxCutEnergy

/-! ## 1.  Attack (i): the violated slot always separates — no kill

The banked totality theorem, restated in the direction the construction consumes: a centre that
is *not* a member is separated from the whole real relaxation by a rational cut of strictly
positive margin.  So the "psd-margin-only violation with no separating direction" case the
attack looked for does not exist, and P*'s cut lane never gets stuck. -/

/-- **No non-member without a genuine cut.**  `RelaxOracle.relaxMem_or_cut`'s contrapositive
read-out, with the margin's strict positivity exposed. -/
theorem cut_of_not_relaxMem {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} (hδ : 0 < δ)
    (h : ¬ QMCLeafB.RelaxOracle.RelaxMem A cX u δ) :
    ∃ C : QMCLeafB.RelaxOracle.RelaxCut A cX u δ, 0 < C.margin := by
  rcases QMCLeafB.RelaxOracle.relaxMem_or_cut A cX u δ hδ with hM | hC
  · exact absurd hM h
  · obtain ⟨C⟩ := hC
    exact ⟨C, C.margin_pos⟩

/-- The cut's margin is nonnegative against **every** real point of the relaxation — the form
`RunParts.hcut` asks for, with zero `del`-slack. -/
theorem cut_separates_whole_body {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (C : QMCLeafB.RelaxOracle.RelaxCut A cX u δ) :
    ∀ X : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
        ((δ : ℚ) : ℝ) X →
      0 ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat C.normal)
        (X - QMCLeafB.SepOracle.castMat cX) + ((C.margin : ℚ) : ℝ) := by
  intro X hX
  have h := C.separates X hX
  linarith

/-! ## 2.  Attack (iii): the centres are a relabelling — `htest` constrains nothing

`TestRun`'s `cX` is free.  Given *any* run record, one member and one non-member settle
`htest` at every round simultaneously. -/

variable {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
variable {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}

/-- **THE RELABELLING LEMMA.**  A `RunParts` plus one rational member and one rational
non-member *is* a `TestRun`: round `k`'s centre is declared to be the member exactly when
`ok k` holds, and the non-member otherwise.  No coherence with the run's own states is
available — and none is needed. -/
theorem testRun_of_centres (B : QMCLeafB.FinalStroke.RunParts o G t P)
    {Qm Qn : Matrix (Fin G.n) (Fin G.n) ℚ}
    (hQm : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Qm
      (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hQn : ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Qn
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    Nonempty (QMCLeafB.TrajM3.TestRun o G t P) := by
  refine ⟨{ toParts := B
            cX := fun k => if B.ok k = true then Qm else Qn
            htest := ?_ }⟩
  intro k
  by_cases hk : B.ok k = true
  · simp only [if_pos hk]
    exact ⟨fun _ => hQm, fun _ => hk⟩
  · simp only [if_neg hk]
    exact ⟨fun hc => absurd hc hk, fun hm => absurd hm hQn⟩

/-! ## 3.  A rational non-member always exists (so `htest`'s negative side is free) -/

/-- **The zero matrix is never a member** as soon as `δ < 4` and `n > 0`: its diagonal misses
`1` by more than `δ/4`.  At the campaign's `dq ≤ 1/380000` the side condition is trivial. -/
theorem nonmember_zero {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hδ : δ < 4) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem A (0 : Matrix (Fin n) (Fin n) ℚ) u δ := by
  intro h
  have h1 := h.diag_near ⟨0, hn⟩
  have h0 : (0 : Matrix (Fin n) (Fin n) ℚ) ⟨0, hn⟩ ⟨0, hn⟩ = 0 := rfl
  rw [h0] at h1
  rw [show |(0 : ℚ) - 1| = 1 by norm_num] at h1
  linarith

/-- **At `δ ≤ 0` no matrix is a member** (`RelaxMem.δ_pos` fails), so the non-member is free at the
degenerate inputs too (`n = 0`, `Rq = 0`).  Together with `nonmember_zero` this covers both cases
of the campaign's `dq`. -/
theorem nonmember_of_nonpos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} (hδ : δ ≤ 0) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem A (0 : Matrix (Fin n) (Fin n) ℚ) u δ :=
  fun h => absurd h.δ_pos (not_lt.mpr hδ)

/-- **A rescaled identity is never a member**, for *any* `δ > 0`: its diagonal is `1 + δ`, which
misses `1` by `δ > δ/4`.  No size bound on `δ` — this is the version that survives the degenerate
inputs where `δ` is large. -/
theorem nonmember_scale_one {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hδ : 0 < δ) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem A ((1 + δ) • (1 : Matrix (Fin n) (Fin n) ℚ)) u δ := by
  intro h
  have h1 := h.diag_near ⟨0, hn⟩
  have hval : ((1 + δ) • (1 : Matrix (Fin n) (Fin n) ℚ)) ⟨0, hn⟩ ⟨0, hn⟩ = 1 + δ := by
    simp [Matrix.smul_apply]
  rw [hval] at h1
  rw [show |1 + δ - 1| = δ by
    rw [show (1 : ℚ) + δ - 1 = δ by ring, abs_of_pos hδ]] at h1
  linarith

/-- **A non-member exists at every `n > 0`, for every tolerance `δ`** — the two cases are
`δ ≤ 0` (nothing is a member) and `δ > 0` (`nonmember_scale_one`).  This is the discharge of the
`hQn` hypothesis of §5b away from `n = 0`. -/
theorem nonmember_exists {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℚ} (u δ : ℚ) :
    ∃ Q : Matrix (Fin n) (Fin n) ℚ, ¬ QMCLeafB.RelaxOracle.RelaxMem A Q u δ := by
  by_cases h : δ ≤ 0
  · exact ⟨0, nonmember_of_nonpos h⟩
  · push Not at h
    exact ⟨(1 + δ) • (1 : Matrix (Fin n) (Fin n) ℚ), nonmember_scale_one hn h⟩

/-! ## 4.  What the family costs: one member per `ok` round, and nothing else

The phase-28 requirement lists "`htest : ok k ↔ RelaxMem (wMatrixQ G) (cX k) (t−ε) dq`" as the
definitional test P*'s round function must implement.  It is cheaper than that. -/

/-- **THE CHARACTERIZATION.**  A `TestRun` *on a given record* exists **iff** every round that
reports `ok` has some rational member available at `(G,t)`.  Nothing else is asked: the centres
are chosen, not read off the run. -/
theorem testRun_iff (B : QMCLeafB.FinalStroke.RunParts o G t P)
    {Qn : Matrix (Fin G.n) (Fin G.n) ℚ}
    (hQn : ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Qn
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    (∃ T : QMCLeafB.TrajM3.TestRun o G t P, T.toParts = B)
      ↔ ((∃ k, B.ok k = true) →
          ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
            QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
              (t - QMCLeafB.RundataCert.eps G) P.dq) := by
  constructor
  · rintro ⟨T, hTB⟩ ⟨k, hk⟩
    refine ⟨T.cX k, (T.htest k).mp ?_⟩
    rw [hTB]
    exact hk
  · intro h
    by_cases hex : ∃ k, B.ok k = true
    · obtain ⟨Qm, hQm⟩ := h hex
      refine ⟨{ toParts := B, cX := fun k => if B.ok k = true then Qm else Qn, htest := ?_ }, rfl⟩
      intro k
      by_cases hk : B.ok k = true
      · simp only [if_pos hk]
        exact ⟨fun _ => hQm, fun _ => hk⟩
      · simp only [if_neg hk]
        exact ⟨fun hc => absurd hc hk, fun hm => absurd hm hQn⟩
    · refine ⟨{ toParts := B, cX := fun _ => Qn, htest := ?_ }, rfl⟩
      intro k
      exact ⟨fun hok => absurd ⟨k, hok⟩ hex, fun hm => absurd hm hQn⟩

/-- **`TestRun` from `RunParts` and one member.**  The campaign's form of `testRun_iff`: at
`n > 0` and `dq < 4` a non-member is free, so one member settles the whole slot. -/
theorem testRun_of_runParts_of_member (B : QMCLeafB.FinalStroke.RunParts o G t P)
    (hn : 0 < G.n) (hδ : P.dq < 4)
    (hmem : ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq) :
    Nonempty (QMCLeafB.TrajM3.TestRun o G t P) := by
  obtain ⟨Qm, hQm⟩ := hmem
  exact testRun_of_centres B hQm (nonmember_zero hn hδ)

/-- **The one direction the family really owes**: a `true` bit names a rational member. -/
theorem member_of_bit_true (T : QMCLeafB.TrajM3.TestRun o G t P) (h : o G t = true) :
    ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq := by
  obtain ⟨k, _hk, hM⟩ := T.exists_member_of_bit_true h
  exact ⟨T.cX k, hM⟩

/-- **The false-bit lane needs nothing at all**: if the record's flags above the horizon are
`false` (a free choice of the constructor), a single non-member settles `htest` outright. -/
theorem testRun_of_allFalseAbove (B : QMCLeafB.FinalStroke.RunParts o G t P)
    (habove : ∀ k, B.ok k = false)
    {Qn : Matrix (Fin G.n) (Fin G.n) ℚ}
    (hQn : ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Qn
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    Nonempty (QMCLeafB.TrajM3.TestRun o G t P) := by
  refine ⟨{ toParts := B, cX := fun _ => Qn, htest := ?_ }⟩
  intro k
  constructor
  · intro hok
    rw [habove k] at hok
    exact Bool.noConfusion hok
  · intro hm
    exact absurd hm hQn

/-! ## 5.  The consequence: the phase-28 family is `RunParts` + the bit's member implication

Note what is *absent* from the statement below: no certified membership test, no grid, no
tolerance, no coherence between `cX` and the program's state. -/

/-- **The phase-28 `TestRun` family from the record family and the bit's member implication.** -/
theorem testRunFamily_of_runParts
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.FinalStroke.RunParts (QMCLeafB.Audit2M5.campaignBit) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G))
    (habove : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), (B G t).ok k = false)
    (hn : ∀ G : QuantumMaxCutEnergy.Input, 0 < G.n)
    (hδ : ∀ G : QuantumMaxCutEnergy.Input, (QMCLeafB.UnionShallow.paramsKbc2 G).dq < 4)
    (hmem : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = true →
      ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq) :
    Nonempty (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.TrajM3.TestRun (QMCLeafB.Audit2M5.campaignBit) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) := by
  refine ⟨fun G t => ?_⟩
  by_cases hb : QMCLeafB.Audit2M5.campaignBit G t = true
  · exact (testRun_of_runParts_of_member (B G t) (hn G) (hδ G) (hmem G t hb)).some
  · exact (testRun_of_allFalseAbove (B G t) (fun k => habove G t k)
      (nonmember_zero (hn G) (hδ G))).some

/-! ## 4b.  Only *soundness* of the ok test is needed — completeness is not

This is the audit's substantive consequence.  The phase-28 plan worried about making P*'s ok flag
*decide* membership (an exact PSD decision, which `Check_ctest_m8` §3 shows the snapped descent
cannot do at the campaign's tight member).  `testRun_iff` says the family needs only the
one-way implication "some round reported `ok` ⟹ a member exists there", i.e. the **soundness**
half of the test — which is exactly what `pivPsdMargin_of_tolerance` supplies.  An ok flag that
is *too weak* (never fires at a member) costs accuracy at that point but never blocks the family;
an ok flag that fires at a non-member would. -/

/-- **Sound flags give the family.**  The residual in its weakest usable form: per point, the
`∃`-form soundness of the record's flags.  (The per-round form is `sound_flags_of_test` below.) -/
noncomputable def testRunFamilyOfSoundFlags
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.FinalStroke.RunParts (QMCLeafB.Audit2M5.campaignBit) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G))
    (hQn : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      ∃ Qn : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Qn
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hsound : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∃ k, (B G t).ok k = true) →
      ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.TrajM3.TestRun (QMCLeafB.Audit2M5.campaignBit) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  fun G t =>
    ((testRun_iff (B G t) ((hQn G t).choose_spec)).mpr (hsound G t)).choose

/-- **The per-round form**: a test that is sound *at its own centre* supplies the `∃`-form.  This
is the shape P*'s round function has to deliver, and it is one direction only. -/
theorem sound_flags_of_test
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.FinalStroke.RunParts (QMCLeafB.Audit2M5.campaignBit) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G))
    (cXt : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ),
      Matrix (Fin G.n) (Fin G.n) ℚ)
    (hsound : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), (B G t).ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXt G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∃ k, (B G t).ok k = true) →
      ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq := by
  intro G t hk
  obtain ⟨k, hok⟩ := hk
  exact ⟨cXt G t k, hsound G t k hok⟩

/-! ## 5b.  THE ASSEMBLY: `RunParts` + sound flags already give the verbatim leaf

Composing §4b with the banked stroke `TrajM3.solution_of_testRunFamily` (which is
`Audit25M8.solution_of_package : Package → Target`).  Nothing else is assumed. -/

/-- **The verbatim `d9f601e5` sentence from the record family and flag soundness.**  This is the
phase-28 residual in closed form: `RunParts campaignBit paramsKbc2` at every `(G,t)`, plus the
soundness one-liner. -/
theorem target_of_runPartsFamily
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.FinalStroke.RunParts (QMCLeafB.Audit2M5.campaignBit) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G))
    (hQn : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      ∃ Qn : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Qn
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hsound : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∃ k, (B G t).ok k = true) →
      ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq) :
    QMCLeafB.Audit25M8.Target :=
  QMCLeafB.TrajM3.solution_of_testRunFamily
    (testRunFamilyOfSoundFlags B hQn hsound)

end QMCLeafB.Fal28M5

/-! ## 6.  Axiom receipts -/

#print axioms QMCLeafB.Fal28M5.cut_of_not_relaxMem
#print axioms QMCLeafB.Fal28M5.cut_separates_whole_body
#print axioms QMCLeafB.Fal28M5.testRun_of_centres
#print axioms QMCLeafB.Fal28M5.nonmember_zero
#print axioms QMCLeafB.Fal28M5.nonmember_of_nonpos
#print axioms QMCLeafB.Fal28M5.nonmember_scale_one
#print axioms QMCLeafB.Fal28M5.nonmember_exists
#print axioms QMCLeafB.Fal28M5.testRun_iff
#print axioms QMCLeafB.Fal28M5.testRun_of_runParts_of_member
#print axioms QMCLeafB.Fal28M5.member_of_bit_true
#print axioms QMCLeafB.Fal28M5.testRun_of_allFalseAbove
#print axioms QMCLeafB.Fal28M5.testRunFamily_of_runParts
#print axioms QMCLeafB.Fal28M5.testRunFamilyOfSoundFlags
#print axioms QMCLeafB.Fal28M5.sound_flags_of_test
#print axioms QMCLeafB.Fal28M5.target_of_runPartsFamily


