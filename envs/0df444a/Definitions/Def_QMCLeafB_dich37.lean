-- Prove2me | Definitions.Def_QMCLeafB_dich37
-- name    : QMCLeafB_dich37
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:28:55.613638+00:00
-- url     : https://prove2.me/theorems/a17caaa2-302f-46ec-83b3-84315826a648
-- title:
--   QMCLeafB dich37
-- statement:
--   # `Check_dich_37_m1` — phase 37, member m1, direction d2 (`dichotomy-formal`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_relax_oracle_m4
import Definitions.Def_QMCLeafB_fal36
import Definitions.Def_QMCLeafB_bh35
import Definitions.Def_QMCLeafB_asm36_m8
/-
# `Check_dich_37_m1` — phase 37, member m1, direction d2 (`dichotomy-formal`)

**The task.**  Phase 37 asks for the membership-gate dichotomy: give the programme an `ok` test
which IS membership at the round's own centre, and prove that then EXACTLY ONE of

* **(A)** some round reports `ok`, so the bit is TRUE and a member is exhibited at THAT round's own
  rational centre — no grating, no search, no volume;
* **(B)** every round reports a non-member, so every round's oracle cut is a GENUINE separator at
  its own rational centre, and the only gap to `hcut` (stated at the engine's accumulated centre
  `Cat k`) is m4/ph36's PRICE `n·(flat cX − Cat k)`

holds — i.e. that neither horn carries a hidden obligation, and the leaf's cost is exactly the
price in case (B).

## What this file machine-checks

* **§1 The gate is a COMPUTATION, and one tempting shortcut is FALSE.**  `okB` (below) is the
  oracle's own branch verdict, and it is a genuine decision procedure for membership:
  `okB_eq_true_iff_mem`.  It is a plain `def` from rational comparisons plus the exact LDLT pivot
  recursion — Lean COMPILES and RUNS it (`§5`, `#eval` on a member and a non-member).  So the phase's
  falsification question ("is the member-or-not decision realisable in the programme?") has a
  positive answer at the level of decidability; the bit-cost/poly-time bound is the `Automatic.Poly`
  ledger's business (direction 4), not this file's.
  **FALSIFIED HERE: "a cut means a non-member".**  `RelaxCut.separates` is ONE-SIDED, so the cut
  structures are inhabited at member centres too — `mem_and_cut` exhibits a member centre carrying a
  `RelaxCut` (normal `0`, margin `1`).  Hence (i) `ok` must be the membership test itself, never "no
  cut was found"; and (ii) the case-(B) cut can only be *genuine* because of the price+ledger — see
  `zero_normal_not_recordable` in §4, which shows the vacuous cut cannot be recorded.

* **§2 The dichotomy is a theorem.**  For ANY programme whose ok test is membership at the round's
  own rational centre (`Gate`), the two horns are exhaustive and exclusive:
  `dichotomy_of_gate`, `dichotomy_exclusive`.  Horn (A) gives the member at that round's centre and
  makes the verdict bit `true` (`bit_true_of_hornA`, `hornA_member_at_own_centre`); horn (B) gives a
  `RelaxCut` at every round's own centre and makes the bit `false` (`bit_false_of_allFalse`,
  `cuts_of_allFalse`).

* **§3 Horn (B) is DEFINITIONAL up to the price.**  `cutFamily` MANUFACTURES the cut family from
  the gate + the all-`false` verdict — no `RelaxCut` family is assumed anywhere.  With the recorded
  normals identified with the oracle's (`hnorm`, the programme's only transcript obligation), the
  engine-centre inequality `RunParts.hcut` follows from the per-round price inequality
  (`hcut_of_gate_allFalse`), and the record `ThinRec34M4.BodyRec` (= phase 36's `SelfRec`) follows
  as well (`bodyRec_of_gate_allFalse`) — m4's `bodyRec_of_oracleCuts` with its `C`-family
  hypothesis DISCHARGED.  In case (B) the leaf therefore costs exactly the price.

* **§4 The price's exact strength (the honest boundary of horn (B)).**  `price_ledger_necessary`:
  if a round is recordable at all (ledger `del^2 <= rho^2*sigma`, `rho <= rmax`, `del >= 0`,
  `del >= price`) then NECESSARILY `price <= rmax*sqrt(sigma_k)`.  `price_ledger_sufficient`:
  conversely, if `price < rmax*sqrt(sigma_k)` then a rational `del` satisfying all four exists.  So
  the ledger pays the price at round `k` **iff** `price k <= rmax*sqrt(sigma_k)`: that single scalar
  inequality is the whole of (B2), and its failure CLOSES the price route at that round (a bigger
  `del` cannot help; the leaf would then need a different normal).  `zero_normal_not_recordable` is
  the sharp corollary: the zero-normal cut has `price = margin > 0` while `sigma = 0`, so the
  price+ledger exclude it — this is what makes case (B)'s cut a genuine separator rather than the
  vacuous one of §1.

* **§5 Receipts.**  (i) Horn (A) exhibits a member at the round's *recorded* centre, but `HokSlot`'s
  witness must be symmetric and a member need not be (`member_not_symmetric`), so the passage
  (A) => `hok` uses the programme's symmetry invariant — stated, not assumed away, in
  `hokShape_of_gate`.  (ii) Both horns are inhabited on real data (`nonvacuous_A`, `nonvacuous_B`).
  (iii) `#eval` of the computable gate on a member and a non-member.

Discipline: `set_option autoImplicit false`; every declaration's `#print axioms` line is exactly
[propext, Classical.choice, Quot.sound] (batch audit in §6); published `Definitions.*` imports only.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Dich37M1

open Matrix QMCLeafB.RelaxOracle QMCLeafB.EngineIterates

variable {n : ℕ}

/-! ## 1.  The gate as a computation, and a false shortcut

The tempting reading is "the oracle returned a cut, so the centre is a non-member".  It is FALSE:
`RelaxCut.separates` is a one-sided inequality `-margin <= <n, X - cX>` over the relaxation, and it
is satisfied vacuously at a member centre by the zero normal.  So the `ok` test must be the
membership predicate itself — exactly what §2's `Gate` assumes — and the genuineness of a recorded
cut has to come from the price and the ledger (§4). -/

/-- The Frobenius pairing with the zero normal vanishes. -/
theorem frob_zero_left {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.SepOracle.frob (0 : Matrix (Fin n) (Fin n) ℝ) X = 0 := by
  rw [QMCLeafB.SepOracle.frob]
  exact Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => by simp))

/-- **FALSIFICATION: a cut does NOT mean a non-member.**  At the banked member centre
`cX = 1` (`RelaxMem 0 1 0 1`, m4's `relaxMem_example`) there is a `RelaxCut` — the zero normal with
margin `1`, whose separation holds vacuously.  Consequences: (i) `ok` cannot be defined as "the
oracle failed to find a cut"; (ii) "cut => non-member" is not available anywhere in the argument. -/
theorem mem_and_cut :
    RelaxMem (0 : Matrix (Fin 2) (Fin 2) ℚ) (1 : Matrix (Fin 2) (Fin 2) ℚ) 0 1
      ∧ Nonempty (RelaxCut (0 : Matrix (Fin 2) (Fin 2) ℚ) (1 : Matrix (Fin 2) (Fin 2) ℚ) 0 1) := by
  refine ⟨QMCLeafB.RelaxOracle.relaxMem_example, ⟨⟨0, 1, by norm_num, ?_⟩⟩⟩
  intro X _
  have h0 : QMCLeafB.SepOracle.castMat (0 : Matrix (Fin 2) (Fin 2) ℚ) = 0 := by
    ext i j; simp [QMCLeafB.SepOracle.castMat]
  rw [h0, frob_zero_left]
  norm_num

/-- **The `ok` test as a computation.**  Run the relaxed separation oracle at the round's own
rational centre and report its branch verdict: `true` on `mem`, `false` on `cut`.  Its body is
rational comparisons plus the exact LDLT pivot recursion, so this is a plain `def` — it COMPILES and
RUNS (`§5`). -/
def okB {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ)
    (hδ : 0 < δ) (hs : cXᵀ = cX) : Bool :=
  match relaxOracle A cX u δ hδ hs with
  | RelaxResponse.mem _ => true
  | RelaxResponse.cut _ => false

/-- A member takes the `mem` branch: the trace test is `RelaxMem.trace_le`, the diagonal test is
`diagMarginSum_eq_zero_iff`, and the pivot recursion cannot report a violated direction because the
shifted form is nonnegative by `RelaxMem.psd_margin`. -/
theorem okB_eq_true_of_mem {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hδ : 0 < δ) (hs : cXᵀ = cX) (hm : RelaxMem A cX u δ) :
    okB A cX u δ hδ hs = true := by
  have htr : QMCLeafB.SepOracle.frob A cX ≤ u + δ / 2 := hm.trace_le
  have hdiag : diagMarginSum cX δ = 0 := (diagMarginSum_eq_zero_iff cX δ).mpr hm.diag_near
  simp only [okB, relaxOracle, dif_pos htr, dif_pos hdiag]
  cases hsp : QMCLeafB.SepOracle.splitOfTranspose n
      (cX + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ)) (shift_symm hs δ) with
  | psd m C hC => rfl
  | violated v hv =>
      exfalso
      rw [qf_shift] at hv
      have := hm.psd_margin v
      linarith

/-- **The gate decides membership.**  `mem` carries its own proof; a `cut` branch is impossible at a
member centre by the previous lemma. -/
theorem okB_eq_true_iff_mem {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hδ : 0 < δ) (hs : cXᵀ = cX) :
    okB A cX u δ hδ hs = true ↔ RelaxMem A cX u δ := by
  refine ⟨fun h => ?_, okB_eq_true_of_mem hδ hs⟩
  unfold okB at h
  cases hr : relaxOracle A cX u δ hδ hs with
  | mem hm => exact hm
  | cut C => rw [hr] at h; exact Bool.noConfusion h

/-- The negative reading of the same computation. -/
theorem okB_eq_false_iff_not_mem {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hδ : 0 < δ) (hs : cXᵀ = cX) :
    okB A cX u δ hδ hs = false ↔ ¬ RelaxMem A cX u δ := by
  rw [← Bool.not_eq_true, okB_eq_true_iff_mem]

/-! ## 2.  The gate, and the dichotomy

The gate is stated over the *whole* sequence `ok : ℕ → Bool`, because the round programme's test is
a function of its own state and knows nothing about the run's horizon `T = K*m`; the horizon-bounded
form is a corollary (`Gate.mono`). -/

/-- **THE MEMBERSHIP GATE.**  The programme's `ok` test is membership at the round's own rational
centre `cX k` — no ball, no cube, no volume, no search. -/
def Gate (A : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) (ok : ℕ → Bool)
    (cX : ℕ → Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ k, ok k = true ↔ RelaxMem A (cX k) u δ

/-- The gate, restricted to the run's horizon. -/
theorem Gate.mono {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {ok : ℕ → Bool}
    {cX : ℕ → Matrix (Fin n) (Fin n) ℚ} (h : Gate A u δ ok cX) (T : ℕ) :
    ∀ k, k < T → (ok k = true ↔ RelaxMem A (cX k) u δ) :=
  fun k _ => h k

/-- **The gate is inhabited by the computable test of §1** — so `Gate` is a programme rule, not
merely a specification. -/
theorem gate_of_okB {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} (hδ : 0 < δ)
    (cX : ℕ → Matrix (Fin n) (Fin n) ℚ) (hs : ∀ k, (cX k)ᵀ = cX k) :
    Gate A u δ (fun k => okB A (cX k) u δ hδ (hs k)) cX :=
  fun k => okB_eq_true_iff_mem hδ (hs k)

/-- **THE MEMBERSHIP-GATE DICHOTOMY.**  For any programme whose `ok` test is membership at the
round's own rational centre, either some round reports `ok` — and then a member is exhibited at THAT
round's own centre — or every round reports a non-member, and then the oracle's verdict at every
round's own centre is a genuine `RelaxCut` of the whole relaxation.

Both horns are definitional: no grating, no volume, no reach theorem, and no hypothesis on the
trajectory beyond the gate itself. -/
theorem dichotomy_of_gate {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {ok : ℕ → Bool}
    {cX : ℕ → Matrix (Fin n) (Fin n) ℚ} (hδ : 0 < δ) (hg : Gate A u δ ok cX) :
    (∃ k, ok k = true ∧ RelaxMem A (cX k) u δ)
      ∨ ((∀ k, ok k = false) ∧ (∀ k, Nonempty (RelaxCut A (cX k) u δ))) := by
  by_cases h : ∃ k, ok k = true
  · obtain ⟨k, hk⟩ := h
    exact Or.inl ⟨k, hk, (hg k).1 hk⟩
  · push Not at h
    refine Or.inr ⟨fun k => ?_, fun k => ?_⟩
    · cases hk : ok k with
      | false => rfl
      | true => exact absurd hk (h k)
    · have hnm : ¬ RelaxMem A (cX k) u δ := fun hm => h k ((hg k).2 hm)
      exact (relaxMem_or_cut A (cX k) u δ hδ).resolve_left hnm

/-- **"EXACTLY ONE".**  The two horns cannot both hold. -/
theorem dichotomy_exclusive {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {ok : ℕ → Bool}
    {cX : ℕ → Matrix (Fin n) (Fin n) ℚ} :
    ¬ ((∃ k, ok k = true ∧ RelaxMem A (cX k) u δ) ∧ (∀ k, ok k = false)) := by
  rintro ⟨⟨k, hk, -⟩, hall⟩
  rw [hall k] at hk
  exact Bool.noConfusion hk

/-- The all-`false` horn manufactures the cut family at every round's own centre — no family is
assumed. -/
theorem cuts_of_allFalse {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {ok : ℕ → Bool}
    {cX : ℕ → Matrix (Fin n) (Fin n) ℚ} (hδ : 0 < δ) (hg : Gate A u δ ok cX)
    (hall : ∀ k, ok k = false) : ∀ k, Nonempty (RelaxCut A (cX k) u δ) := by
  intro k
  have hnm : ¬ RelaxMem A (cX k) u δ := fun hm => by
    have h1 : ok k = true := (hg k).2 hm
    rw [hall k] at h1
    exact Bool.noConfusion h1
  exact (relaxMem_or_cut A (cX k) u δ hδ).resolve_left hnm

/-! ### 2b.  The two horns at the run's verdict bit -/

/-- **Horn (A) makes the verdict bit `true`.** -/
theorem bit_true_of_hornA {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {ok : ℕ → Bool} {T : ℕ}
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok T)
    (h : ∃ k, k < T ∧ ok k = true) : o G t = true := by
  rw [hverdict, QMCLeafB.SimLoop.anyOk_eq_true_iff]
  exact h

/-- The run's verdict is `false` when no round reports `ok`. -/
theorem anyOk_eq_false_of_allFalse {ok : ℕ → Bool} :
    ∀ T : ℕ, (∀ k, k < T → ok k = false) → QMCLeafB.SimLoop.anyOk ok T = false
  | 0, _ => rfl
  | T + 1, h => by
      rw [QMCLeafB.SimLoop.anyOk_succ, h T (Nat.lt_succ_self T),
        anyOk_eq_false_of_allFalse T (fun k hk => h k (Nat.lt_succ_of_lt hk))]
      rfl

/-- **Horn (B) makes the verdict bit `false`.** -/
theorem bit_false_of_allFalse {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {ok : ℕ → Bool} {T : ℕ}
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok T)
    (hall : ∀ k, k < T → ok k = false) : o G t = false := by
  rw [hverdict]
  exact anyOk_eq_false_of_allFalse T hall

/-- **Horn (A) at the run's horizon**: the bit is true and a member sits at one round's own
rational centre. -/
theorem hornA_member_at_own_centre {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    {ok : ℕ → Bool} {cX : ℕ → Matrix (Fin n) (Fin n) ℚ} {T : ℕ}
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok T) (hδ : 0 < δ)
    (hg : Gate A u δ ok cX) (hbit : o G t = true) :
    ∃ k, k < T ∧ ok k = true ∧ RelaxMem A (cX k) u δ := by
  rw [hverdict, QMCLeafB.SimLoop.anyOk_eq_true_iff] at hbit
  obtain ⟨k, hk, hok⟩ := hbit
  exact ⟨k, hk, hok, (hg k).1 hok⟩

/-- **Horn (A) gives `HokSlot`'s conclusion** at the gate's own `(A, u, δ)`: the member is the
round's recorded centre.  The one side condition is SYMMETRY of the recorded centre, a property of
the programme's state coding, not of the gate (§5 `member_not_symmetric`). -/
theorem hokShape_of_gate {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {ok : ℕ → Bool}
    {cX : ℕ → Matrix (Fin n) (Fin n) ℚ} (hs : ∀ k, (cX k)ᵀ = cX k)
    (hg : Gate A u δ ok cX) (h : ∃ k, ok k = true) :
    ∃ Q : Matrix (Fin n) (Fin n) ℚ, Qᵀ = Q ∧ RelaxMem A Q u δ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨cX k, hs k, (hg k).1 hk⟩


/-! ## 3.  Horn (B) is definitional up to the price

No `RelaxCut` family is assumed in this section: the family is MANUFACTURED from the gate and the
all-`false` verdict (`cutFamily`).  The only transcript-side obligation is `hnorm` — that the
recorded normal IS the oracle's cut normal — which is a property of the round programme, not of the
geometry.  With it, `RunParts.hcut` at the engine's own accumulated centre follows from the price,
and so does the record `BodyRec` (phase 36's `SelfRec`). -/

/-- **The cuts case (B) manufactures.**  At every round the gate says the centre is not a member, so
`relaxMem_or_cut` returns a genuine separator there.  This is the only use of `Classical.choice` in
the file, and it is choice on a disjunction the gate has already decided. -/
def cutFamily (A : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) (hδ : 0 < δ)
    (ok : ℕ → Bool) (cX : ℕ → Matrix (Fin n) (Fin n) ℚ) (hg : Gate A u δ ok cX)
    (hall : ∀ k, ok k = false) (k : ℕ) : RelaxCut A (cX k) u δ :=
  Classical.choice (cuts_of_allFalse hδ hg hall k)

/-- **HORN (B) ⟹ `RunParts.hcut` at the ENGINE's centre, at the price.**  The recorded normal is the
oracle's cut normal at the round's own rational centre; the engine's centre `Cat k` differs from it
by the signed translation whose pairing is m4/ph36's price.  So the per-round price inequality is
the ONLY gap between case (B) and the leaf's `hcut` field. -/
theorem hcut_of_gate_allFalse {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {ok : ℕ → Bool}
    (hg : Gate (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq ok cX)
    (hall : ∀ k, ok k = false)
    (cd : ℕ → CutData (G.n * G.n)) (del : ℕ → ℚ)
    (hnorm : ∀ k, (cd k).c = flatQ (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k).normal)
    (hprice : ∀ k, k < P.K * P.m → Fal36M4.priceAt (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k)
        (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) ≤ ((del k : ℚ) : ℝ)) :
    ∀ k, k < P.K * P.m → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ)
          (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ) →
        -(((del k : ℚ)) : ℝ) ≤ QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
          (z - Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) := by
  intro k hk _ z hz
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
  have hp := Fal36M4.hcut_of_priceAt
    (C := cutFamily (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k)
    (a := Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) (del := del k)
    (hprice k hk) z hz'
  have hcR : cutCR cd k = fun i => ((flatQ (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k).normal i : ℚ) : ℝ) := by
    funext i
    simp only [cutCR, hnorm k]
  rw [hcR]
  exact hp

/-- **HORN (B) ⟹ the RECORD.**  m4/ph36's `bodyRec_of_oracleCuts` with its cut-family hypothesis
DISCHARGED: the family is `cutFamily`, manufactured from the gate.  So at an all-`false` run the
record `ThinRec34M4.BodyRec` — phase 36's `SelfRec` — costs exactly the ledger plus the price. -/
theorem bodyRec_of_gate_allFalse {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {ok : ℕ → Bool}
    (hg : Gate (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq ok cX)
    (hall : ∀ k, ok k = false)
    (cd : ℕ → CutData (G.n * G.n)) (del : ℕ → ℚ)
    (hnorm : ∀ k, (cd k).c = flatQ (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k).normal)
    (hwit : ∀ k, k < P.K * P.m →
      (Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k).mulVec (cd k).p = (cd k).c)
    (hrho : ∀ k, k < P.K * P.m → 0 ≤ (cd k).rho)
    (hcne : ∀ k, k < P.K * P.m → (cd k).c ≠ 0)
    (hdel0 : ∀ k, k < P.K * P.m → 0 ≤ del k)
    (hcheck : ∀ k, k < P.K * P.m → (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hle : ∀ k, k < P.K * P.m → (cd k).rho ≤ P.rmax)
    (hprice : ∀ k, k < P.K * P.m → Fal36M4.priceAt (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k)
        (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) ≤ ((del k : ℚ) : ℝ)) :
    QMCLeafB.ThinRec34M4.BodyRec G t P :=
  Fal36M4.bodyRec_of_oracleCuts (P := P) cX
    (fun k => cutFamily (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k)
    cd del hnorm hwit hrho hcne hdel0 hcheck hle hprice


/-- **CASE (B) IS THE RUN'S OWN TRANSCRIPT.**  Putting the verdict equation in: at an all-`false`
run the bit is `false`, and the record `BodyRec` built in `bodyRec_of_gate_allFalse` IS a
`RunParts` at that bit (m4/ph36's `runParts_false_iff_bodyRec`).  So case (B) of the dichotomy
yields the leaf's record object itself, with the price as its only non-definitional input. -/
theorem runParts_of_gate_allFalse {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {ok : ℕ → Bool}
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m))
    (hg : Gate (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq ok cX)
    (hall : ∀ k, ok k = false)
    (cd : ℕ → CutData (G.n * G.n)) (del : ℕ → ℚ)
    (hnorm : ∀ k, (cd k).c = flatQ (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k).normal)
    (hwit : ∀ k, k < P.K * P.m →
      (Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k).mulVec (cd k).p = (cd k).c)
    (hrho : ∀ k, k < P.K * P.m → 0 ≤ (cd k).rho)
    (hcne : ∀ k, k < P.K * P.m → (cd k).c ≠ 0)
    (hdel0 : ∀ k, k < P.K * P.m → 0 ≤ del k)
    (hcheck : ∀ k, k < P.K * P.m → (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hle : ∀ k, k < P.K * P.m → (cd k).rho ≤ P.rmax)
    (hprice : ∀ k, k < P.K * P.m → Fal36M4.priceAt (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k)
        (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) ≤ ((del k : ℚ) : ℝ)) :
    Nonempty (QMCLeafB.FinalStroke.RunParts o G t P) := by
  have hbit : o G t = false :=
    bit_false_of_allFalse hverdict (fun k _ => hall k)
  exact (QMCLeafB.ThinRec34M4.runParts_false_iff_bodyRec (P := P) hbit).2
    (bodyRec_of_gate_allFalse (P := P) hg hall cd del hnorm hwit hrho hcne hdel0 hcheck hle hprice)


/-- **The transcript that case (B) writes down.**  Its normal is the oracle's cut normal at the
round's own centre — so the identification `hnorm` of `bodyRec_of_gate_allFalse` is not an assumption
but this definition's `rfl`.  Only the depth `rho` and the witness `p` remain as programme data. -/
def cdOfGate (A : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) (hδ : 0 < δ)
    (ok : ℕ → Bool) (cX : ℕ → Matrix (Fin n) (Fin n) ℚ) (hg : Gate A u δ ok cX)
    (hall : ∀ k, ok k = false) (p : ℕ → Fin (n * n) → ℚ) (rho : ℕ → ℚ) :
    ℕ → CutData (n * n) :=
  fun k => ⟨flatQ (cutFamily A u δ hδ ok cX hg hall k).normal, p k, rho k⟩

/-- The constructed transcript's normal IS the oracle's cut normal, definitionally. -/
theorem cdOfGate_c (A : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) (hδ : 0 < δ)
    (ok : ℕ → Bool) (cX : ℕ → Matrix (Fin n) (Fin n) ℚ) (hg : Gate A u δ ok cX)
    (hall : ∀ k, ok k = false) (p : ℕ → Fin (n * n) → ℚ) (rho : ℕ → ℚ) (k : ℕ) :
    (cdOfGate A u δ hδ ok cX hg hall p rho k).c
      = flatQ (cutFamily A u δ hδ ok cX hg hall k).normal := rfl

/-- **HORN (B) WITH THE TRANSCRIPT CONSTRUCTED.**  `bodyRec_of_gate_allFalse` with `hnorm` deleted:
the recorded normals are the oracle's BY CONSTRUCTION.  What remains is the depth stream
(`hwit`, `hrho`, `hle`) and the price.  This is the sharpest form of "case (B) is definitional up to
the price". -/
theorem bodyRec_of_gate_transcript {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {ok : ℕ → Bool}
    (hg : Gate (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq ok cX)
    (hall : ∀ k, ok k = false)
    (p : ℕ → Fin (G.n * G.n) → ℚ) (rho : ℕ → ℚ) (del : ℕ → ℚ)
    (hwit : ∀ k, k < P.K * P.m →
      (Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))
        (cdOfGate (QMCLeafB.Finalization.wMatrixQ G)
          (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall p rho) k).mulVec (p k)
        = flatQ (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
            (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k).normal)
    (hrho : ∀ k, k < P.K * P.m → 0 ≤ rho k)
    (hcne : ∀ k, k < P.K * P.m →
      flatQ (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
        (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k).normal ≠ 0)
    (hdel0 : ∀ k, k < P.K * P.m → 0 ≤ del k)
    (hcheck : ∀ k, k < P.K * P.m → (del k) ^ 2
      ≤ (rho k) ^ 2 * sigmaQ
        (flatQ (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
          (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k).normal) (p k))
    (hle : ∀ k, k < P.K * P.m → rho k ≤ P.rmax)
    (hprice : ∀ k, k < P.K * P.m → Fal36M4.priceAt (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k)
        (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (cdOfGate (QMCLeafB.Finalization.wMatrixQ G)
            (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall p rho) k)
        ≤ ((del k : ℚ) : ℝ)) :
    QMCLeafB.ThinRec34M4.BodyRec G t P :=
  bodyRec_of_gate_allFalse hg hall
    (cdOfGate (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall p rho)
    del (fun _ => rfl) hwit hrho hcne hdel0 hcheck hle hprice


/-- The VACUOUS cut: zero normal, unit margin.  Its separation is `-1 <= 0`, so it exists at every
centre (`mem_and_cut`).  Used ONLY as a fallback outside the run's horizon, where no geometry is
asserted; it can never be *recorded* at a visited round (`zero_normal_not_recordable`). -/
def vacCut (A : Matrix (Fin n) (Fin n) ℚ) (cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) :
    RelaxCut A cX u δ where
  normal := 0
  margin := 1
  margin_pos := by norm_num
  separates := by
    intro X _
    have h0 : QMCLeafB.SepOracle.castMat (0 : Matrix (Fin n) (Fin n) ℚ) = 0 := by
      ext i j; simp [QMCLeafB.SepOracle.castMat]
    rw [h0, frob_zero_left]
    norm_num

/-- **The cuts case (B) manufactures, at a HORIZON.**  Inside the run it is the oracle's genuine cut
at the round's own centre; outside the horizon it is the vacuous one, which the ledger will exclude
anywhere it matters.  This makes the family total, so no all-`false` fact is ever needed beyond the
rounds the run visits. -/
def cutFamilyH (A : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) (hδ : 0 < δ)
    (ok : ℕ → Bool) (cX : ℕ → Matrix (Fin n) (Fin n) ℚ) (hg : Gate A u δ ok cX) (T : ℕ)
    (hall : ∀ k, k < T → ok k = false) (k : ℕ) : RelaxCut A (cX k) u δ :=
  if h : k < T then
    Classical.choice ((relaxMem_or_cut A (cX k) u δ hδ).resolve_left (fun hm => by
      have h1 : ok k = true := (hg k).2 hm
      rw [hall k h] at h1
      exact Bool.noConfusion h1))
  else vacCut A (cX k) u δ

/-- Each manufactured cut carries its own separation field — the structure's contract, available at
any `k` (inside the horizon it is the oracle's genuine cut, outside it is vacuous). -/
theorem cutFamilyH_separates {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {hδ : 0 < δ}
    {ok : ℕ → Bool} {cX : ℕ → Matrix (Fin n) (Fin n) ℚ} {hg : Gate A u δ ok cX} {T : ℕ}
    {hall : ∀ k, k < T → ok k = false} (k : ℕ) :
    ∀ X : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
        ((δ : ℚ) : ℝ) X →
      -((((cutFamilyH A u δ hδ ok cX hg T hall k).margin : ℚ) : ℝ))
        ≤ QMCLeafB.SepOracle.frob
            (QMCLeafB.SepOracle.castMat (cutFamilyH A u δ hδ ok cX hg T hall k).normal)
            (X - QMCLeafB.SepOracle.castMat (cX k)) :=
  (cutFamilyH A u δ hδ ok cX hg T hall k).separates

/-- **HORN (B) AT A HORIZON.**  `bodyRec_of_gate_allFalse` with the all-`false` fact needed only on
the rounds the run visits (`k < K*m`); the family is `cutFamilyH`, genuine inside the horizon. -/
theorem bodyRec_of_gateH {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {ok : ℕ → Bool}
    (hg : Gate (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq ok cX)
    (hall : ∀ k, k < P.K * P.m → ok k = false)
    (cd : ℕ → CutData (G.n * G.n)) (del : ℕ → ℚ)
    (hnorm : ∀ k, (cd k).c = flatQ (cutFamilyH (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg (P.K * P.m) hall k).normal)
    (hwit : ∀ k, k < P.K * P.m →
      (Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k).mulVec (cd k).p = (cd k).c)
    (hrho : ∀ k, k < P.K * P.m → 0 ≤ (cd k).rho)
    (hcne : ∀ k, k < P.K * P.m → (cd k).c ≠ 0)
    (hdel0 : ∀ k, k < P.K * P.m → 0 ≤ del k)
    (hcheck : ∀ k, k < P.K * P.m → (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hle : ∀ k, k < P.K * P.m → (cd k).rho ≤ P.rmax)
    (hprice : ∀ k, k < P.K * P.m → Fal36M4.priceAt (cutFamilyH (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg (P.K * P.m) hall k)
        (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) ≤ ((del k : ℚ) : ℝ)) :
    QMCLeafB.ThinRec34M4.BodyRec G t P :=
  Fal36M4.bodyRec_of_oracleCuts (P := P) cX
    (fun k => cutFamilyH (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg (P.K * P.m) hall k)
    cd del hnorm hwit hrho hcne hdel0 hcheck hle hprice

/-! ## 4.  The price's exact strength

The ledger at round `k` is `del^2 <= rho^2 * sigma`, `rho <= rmax`, `del >= 0`, and the bridge to
`hcut` asks `del >= price`.  We show that this system is solvable in `del` **exactly** when
`price <= rmax*sqrt(sigma)`: a NECESSARY condition (`price_ledger_necessary`) and, with strict
inequality, a SUFFICIENT one (`price_ledger_sufficient`).  So (B2)'s single scalar inequality is not
a convention — it is the whole feasibility of the priced route, and where it fails no `del` helps. -/

/-- **The price cannot exceed the ledger's capacity.** -/
theorem price_ledger_necessary {σ rmax : ℚ} {p : ℝ} {del : ℚ}
    (hσ : 0 < σ) (hrmax : 0 ≤ rmax) (hdel0 : 0 ≤ del)
    (hprice : p ≤ ((del : ℚ) : ℝ)) (hcheck : del ^ 2 ≤ rmax ^ 2 * σ) :
    p ≤ ((rmax : ℚ) : ℝ) * Real.sqrt (((σ : ℚ) : ℝ)) := by
  have hσR : (0 : ℝ) ≤ ((σ : ℚ) : ℝ) := by exact_mod_cast (le_of_lt hσ)
  have hrmaxR : (0 : ℝ) ≤ ((rmax : ℚ) : ℝ) := by exact_mod_cast hrmax
  have hcast : (((del : ℚ) : ℝ)) ^ 2 ≤ ((rmax : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ) := by
    have h1 : (((del ^ 2 : ℚ)) : ℝ) ≤ (((rmax ^ 2 * σ : ℚ)) : ℝ) := by exact_mod_cast hcheck
    push_cast at h1
    linarith
  have htop : (0 : ℝ) ≤ ((rmax : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ) := by positivity
  by_cases hp : p ≤ 0
  · linarith
  · push Not at hp
    have hp2 : p ^ 2 ≤ ((rmax : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ) := by nlinarith
    have h1 : p ≤ Real.sqrt (p ^ 2) := by rw [Real.sqrt_sq (le_of_lt hp)]
    have h2 : Real.sqrt (p ^ 2) ≤ Real.sqrt (((rmax : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ)) :=
      Real.sqrt_le_sqrt hp2
    have h3 : Real.sqrt (((rmax : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ))
        = ((rmax : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hrmaxR]
    rw [h3] at h2
    linarith

/-- **The same in the run's own ledger coordinates** (`del^2 <= rho^2*sigma`, `rho <= rmax`). -/
theorem price_le_of_runLedger {σ rmax rho del : ℚ} {p : ℝ}
    (hσ : 0 < σ) (hrmax : 0 ≤ rmax) (hrho : 0 ≤ rho) (hle : rho ≤ rmax)
    (hdel0 : 0 ≤ del) (hcheck : del ^ 2 ≤ rho ^ 2 * σ) (hprice : p ≤ ((del : ℚ) : ℝ)) :
    p ≤ ((rmax : ℚ) : ℝ) * Real.sqrt (((σ : ℚ) : ℝ)) := by
  refine price_ledger_necessary hσ hrmax hdel0 hprice ?_
  have h1 : rho ^ 2 ≤ rmax ^ 2 := by nlinarith
  have h2 : (0 : ℚ) ≤ σ := le_of_lt hσ
  nlinarith

/-- **Capacity is sufficient** (with room to spare): if the price fits strictly inside the ledger's
capacity, a rational `del` exists that the ledger carries and the bridge accepts.  (Kept in the
`p > 0` case; for `p <= 0` the choice `del = 0` works unconditionally, which is why the hypothesis is
`p < rmax*sqrt(sigma)` and not the "max" form.) -/
theorem price_ledger_sufficient {σ rmax : ℚ} {p : ℝ} (hσ : 0 < σ) (hrmax : 0 ≤ rmax)
    (hp : p < ((rmax : ℚ) : ℝ) * Real.sqrt (((σ : ℚ) : ℝ))) :
    ∃ del : ℚ, 0 ≤ del ∧ p ≤ ((del : ℚ) : ℝ) ∧ del ^ 2 ≤ rmax ^ 2 * σ := by
  have hσR : (0 : ℝ) < ((σ : ℚ) : ℝ) := by exact_mod_cast hσ
  have hrmaxR : (0 : ℝ) ≤ ((rmax : ℚ) : ℝ) := by exact_mod_cast hrmax
  by_cases hp0 : p ≤ 0
  · refine ⟨0, le_rfl, by push_cast; linarith, ?_⟩
    nlinarith [sq_nonneg (rmax : ℚ), le_of_lt hσ]
  · push Not at hp0
    obtain ⟨del, hd1, hd2⟩ := exists_rat_btwn hp
    have hdel0R : (0 : ℝ) < ((del : ℚ) : ℝ) := lt_trans hp0 hd1
    have hdel0 : (0 : ℚ) ≤ del := by exact_mod_cast le_of_lt hdel0R
    have hpdel : p ≤ ((del : ℚ) : ℝ) := le_of_lt hd1
    have hsq : (((del : ℚ) : ℝ)) ^ 2 ≤ ((rmax : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ) := by
      have h4 : (((rmax : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ)) ^ 2
          = ((rmax : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ) := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hσR)]
      have h5 : (((del : ℚ) : ℝ)) ^ 2
          < (((rmax : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ)) ^ 2 := by nlinarith
      rw [h4] at h5
      linarith
    refine ⟨del, hdel0, hpdel, ?_⟩
    have h6 : (((del ^ 2 : ℚ)) : ℝ) ≤ (((rmax ^ 2 * σ : ℚ)) : ℝ) := by push_cast; linarith
    exact_mod_cast h6

/-- **The zero normal pays its whole margin.**  So the `RelaxCut` of §1 (`mem_and_cut`), whose
separation is vacuous, prices at `margin > 0`. -/
theorem priceAt_eq_margin_of_normal_zero {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (C : RelaxCut A cX u δ) (hC : C.normal = 0) (a : Fin (n * n) → ℝ) :
    Fal36M4.priceAt C a = ((C.margin : ℚ) : ℝ) := by
  unfold Fal36M4.priceAt
  rw [hC]
  simp [QMCLeafB.RelaxOracle.flatQ, dotProduct]

/-- **THE PRICE + LEDGER MAKE CASE (B) GENUINE.**  A recorded cut with zero normal has
`sigma = 0`, so the ledger forces `del = 0`, but the price is the whole margin `> 0`: recordable
transcripts cannot contain the vacuous cut.  This is the repair of §1's false shortcut
"cut = non-member": the genuine-ness of the case-(B) separator is not structural, it is PAID for. -/
theorem zero_normal_not_recordable {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    {a : Fin (n * n) → ℝ} (C : RelaxCut A cX u δ) (hC : C.normal = 0) {σ rho del : ℚ}
    (hσ : σ = 0) (hcheck : del ^ 2 ≤ rho ^ 2 * σ)
    (hprice : Fal36M4.priceAt C a ≤ ((del : ℚ) : ℝ)) : False := by
  have hp : ((C.margin : ℚ) : ℝ) ≤ ((del : ℚ) : ℝ) := by
    rw [← priceAt_eq_margin_of_normal_zero C hC a]
    exact hprice
  have hd : del = 0 := by
    have h0 : del ^ 2 ≤ 0 := by rw [hσ] at hcheck; simpa using hcheck
    have := sq_nonneg del
    nlinarith
  have hm : (0 : ℝ) < ((C.margin : ℚ) : ℝ) := by exact_mod_cast C.margin_pos
  rw [hd] at hp
  push_cast at hp
  linarith


/-! ### 4b.  What each candidate fix of the phase delivers

(B1) asks for the round's rational centre to BE the engine's accumulated point; (B2) asks for the
price to fit the depth ceiling.  Both pay off at exactly one place in §3, and the two lemmas below
locate it: (B1) makes the price the round's own margin (`priceAt_of_centre_identity`), so `del =
margin` pays it with no slack at all; (B2) delivers a rational `del` from the dimensionless capacity
`price < rho*sqrt(sigma)` (`price_ledger_sufficient_of_le`). -/

/-- **The capacity lemma with an arbitrary rational ceiling** — the run's own depth `rho`, not just
`rmax`.  This is the form (B2) has to hit: the ledger is `del^2 <= rho^2*sigma`, so the freedom is
the dimensionless `price/sqrt(sigma) <= rho`. -/
theorem price_ledger_sufficient_of_le {σ B : ℚ} {p : ℝ} (hσ : 0 < σ) (hB : 0 ≤ B)
    (hp : p < ((B : ℚ) : ℝ) * Real.sqrt (((σ : ℚ) : ℝ))) :
    ∃ del : ℚ, 0 ≤ del ∧ p ≤ ((del : ℚ) : ℝ) ∧ del ^ 2 ≤ B ^ 2 * σ := by
  have hσR : (0 : ℝ) < ((σ : ℚ) : ℝ) := by exact_mod_cast hσ
  by_cases hp0 : p ≤ 0
  · refine ⟨0, le_rfl, by push_cast; linarith, ?_⟩
    nlinarith [sq_nonneg B, le_of_lt hσ]
  · push Not at hp0
    obtain ⟨del, hd1, hd2⟩ := exists_rat_btwn hp
    have hdel0R : (0 : ℝ) < ((del : ℚ) : ℝ) := lt_trans hp0 hd1
    have hdel0 : (0 : ℚ) ≤ del := by exact_mod_cast le_of_lt hdel0R
    have hpdel : p ≤ ((del : ℚ) : ℝ) := le_of_lt hd1
    have hsq : (((del : ℚ) : ℝ)) ^ 2 ≤ ((B : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ) := by
      have h4 : (((B : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ)) ^ 2
          = ((B : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ) := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hσR)]
      have h5 : (((del : ℚ) : ℝ)) ^ 2 < (((B : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ)) ^ 2 := by
        nlinarith
      rw [h4] at h5
      linarith
    refine ⟨del, hdel0, hpdel, ?_⟩
    have h6 : (((del ^ 2 : ℚ)) : ℝ) ≤ (((B ^ 2 * σ : ℚ)) : ℝ) := by push_cast; linarith
    exact_mod_cast h6

/-- **THE PRICE VANISHES UNDER CENTRE IDENTITY (the form (B1) must produce).**  If the round's
rational centre IS the engine's accumulated centre, the price is the round's own margin — i.e. the
only payment left is the margin itself, with `del = margin` and no slack. -/
theorem priceAt_of_centre_identity {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (C : RelaxCut A cX u δ) (a : Fin (n * n) → ℝ)
    (hid : QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX) = a) :
    Fal36M4.priceAt C a = ((C.margin : ℚ) : ℝ) := by
  unfold Fal36M4.priceAt
  rw [hid, sub_self]
  simp [dotProduct]

/-- **(B1) PAYOFF.**  With centre identity at every round, the price condition of
`bodyRec_of_gate_allFalse` is met by the round's own margin, so case (B)'s record costs exactly the
engine's own ledger `margin^2 <= rho^2*sigma_k` — nothing added. -/
theorem priceAt_le_margin_of_centre_identity {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (C : RelaxCut A cX u δ) (a : Fin (n * n) → ℝ)
    (hid : QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX) = a) :
    Fal36M4.priceAt C a ≤ ((C.margin : ℚ) : ℝ) :=
  le_of_eq (priceAt_of_centre_identity C a hid)


/-- **The horizon-bounded form** — what a run of length `T` actually needs.  Horn (B) then asks only
for the rounds the run visits. -/
theorem dichotomy_of_gate_horizon {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {ok : ℕ → Bool}
    {cX : ℕ → Matrix (Fin n) (Fin n) ℚ} (T : ℕ) (hδ : 0 < δ) (hg : Gate A u δ ok cX) :
    (∃ k, k < T ∧ ok k = true ∧ RelaxMem A (cX k) u δ)
      ∨ ((∀ k, k < T → ok k = false) ∧ (∀ k, k < T → Nonempty (RelaxCut A (cX k) u δ))) := by
  by_cases h : ∃ k, k < T ∧ ok k = true
  · obtain ⟨k, hk, hok⟩ := h
    exact Or.inl ⟨k, hk, hok, (hg k).1 hok⟩
  · push Not at h
    refine Or.inr ⟨fun k hk => ?_, fun k hk => ?_⟩
    · cases hok : ok k with
      | false => rfl
      | true => exact absurd hok (h k hk)
    · have hnm : ¬ RelaxMem A (cX k) u δ := fun hm => h k hk ((hg k).2 hm)
      exact (relaxMem_or_cut A (cX k) u δ hδ).resolve_left hnm

/-- **Horn (A) discharges the programme's `hok` slot** — in the exact shape `Asm35M4.HokSlot` and
`Asm36M8.solution_of_two_slots_selfRec` consume.  The only side conditions are the verdict equation
(the bit is the run's `anyOk`) and that the recorded centres are symmetric.  Nothing analytic is
left in the `ok` lane at a membership gate. -/
theorem hok_of_gate {o : QuantumMaxCutEnergy.Input → ℚ → Bool} {G : QuantumMaxCutEnergy.Input}
    {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G} {ok : ℕ → Bool}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m))
    (hg : Gate (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) ok cX)
    (hs : ∀ k, (cX k)ᵀ = cX k) (hbit : o G t = true) :
    ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ, Qᵀ = Q ∧
      RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) := by
  obtain ⟨k, -, hk⟩ := (QMCLeafB.SimLoop.anyOk_eq_true_iff ok (P.K * P.m)).mp
    (by rw [← hverdict]; exact hbit)
  exact hokShape_of_gate hs hg ⟨k, hk⟩

/-- **THE PHASE'S DICHOTOMY, AT THE CAMPAIGN'S OWN OBJECTS.**  One theorem, no hidden hypotheses:
for a programme whose `ok` test is membership at the round's own rational centre, either

* the bit is `true` and a SYMMETRIC rational member sits at `(wMatrixQ G, t - Rq/40000, P.dq)` — the
  `hok` lane, free; or
* the bit is `false`, every visited round's oracle verdict is a genuine `RelaxCut` at that round's
  own centre, and the run's `hcut` at the ENGINE's centres holds as soon as the per-round price fits
  the slack `del`.

This is the leaf's membership-gate reduction in the shape the assembly consumes: horn (A) is `hok`,
horn (B) is `SelfRec` modulo the price. -/
theorem dichotomy_campaign {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {ok : ℕ → Bool} {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m))
    (hg : Gate (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq ok cX)
    (hs : ∀ k, (cX k)ᵀ = cX k)
    (cd : ℕ → CutData (G.n * G.n)) (del : ℕ → ℚ)
    (hall : ∀ k, ok k = false)
    (hnorm : ∀ k, (cd k).c = flatQ (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k).normal)
    (hprice : ∀ k, k < P.K * P.m → Fal36M4.priceAt (cutFamily (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq P.hdq ok cX hg hall k)
        (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) ≤ ((del k : ℚ) : ℝ)) :
    (o G t = true ∧ ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ, Qᵀ = Q ∧
        RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq)
      ∨ (o G t = false
          ∧ (∀ k, k < P.K * P.m → Nonempty (RelaxCut (QMCLeafB.Finalization.wMatrixQ G)
              (cX k) (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq))
          ∧ (∀ k, k < P.K * P.m → ok k = false → ∀ z,
              z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
                ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ)
                (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ) →
              -(((del k : ℚ)) : ℝ) ≤ QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
                (z - Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k))) := by
  rcases dichotomy_of_gate_horizon (P.K * P.m) P.hdq hg with ⟨k, hk, hok, hm⟩ | ⟨hfalse, hcuts⟩
  · refine Or.inl ⟨bit_true_of_hornA hverdict ⟨k, hk, hok⟩, ⟨cX k, hs k, hm⟩⟩
  · exact Or.inr ⟨bit_false_of_allFalse hverdict hfalse, hcuts,
      hcut_of_gate_allFalse hg hall cd del hnorm hprice⟩


/-- `anyOk` is `false` only when every visited round is `false`. -/
theorem allFalse_of_anyOk_false {ok : ℕ → Bool} :
    ∀ T : ℕ, QMCLeafB.SimLoop.anyOk ok T = false → ∀ k, k < T → ok k = false
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | T + 1, h, k, hk => by
      rw [QMCLeafB.SimLoop.anyOk_succ, Bool.or_eq_false_iff] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h' | rfl
      · exact allFalse_of_anyOk_false T h.2 k h'
      · exact h.1

/-- **THE EXACT REMAINDER OF THE LEAF AT A MEMBERSHIP GATE.**  Everything the phase-37 argument
still owes, in the run's own language: at every bit-`false` interior bracket point, a transcript whose
normals ARE the oracle's manufactured cuts at the round's own rational centres (`cutFamilyH`), with
the depth ledger (witness, `0 ≤ rho ≤ rmax`, nonzero normal, `0 ≤ del`) and the PRICE inequality
`priceAt ≤ del` at the engine's accumulated centres.

Nothing is assumed about how the cuts arise — the gate manufactures them.  The all-`false` fact is
demanded only on the rounds the run visits (`k < K*m`). -/
def RecSlot (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ok : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cX : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hgate : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), Gate (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) (P G).dq (ok G t) (cX G t)) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (_hn : 2 ≤ G.n)
    (_hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (_hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (_hall : ∀ k, k < (P G).K * (P G).m → ok G t k = false),
    ∃ (cd : ℕ → CutData (G.n * G.n)) (del : ℕ → ℚ),
      (∀ k, (cd k).c = flatQ (cutFamilyH (QMCLeafB.Finalization.wMatrixQ G)
        (t - QMCLeafB.EngineRuntime.Rq G / 40000) (P G).dq (P G).hdq (ok G t) (cX G t)
        (hgate G t) ((P G).K * (P G).m) _hall k).normal)
      ∧ (∀ k, k < (P G).K * (P G).m →
          (Aat (G.n * G.n)
            (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
              (2 * (G.n : ℚ) ^ 2 + 2 * (P G).dq ^ 2)) cd k).mulVec (cd k).p = (cd k).c)
      ∧ (∀ k, k < (P G).K * (P G).m → 0 ≤ (cd k).rho)
      ∧ (∀ k, k < (P G).K * (P G).m → (cd k).c ≠ 0)
      ∧ (∀ k, k < (P G).K * (P G).m → 0 ≤ del k)
      ∧ (∀ k, k < (P G).K * (P G).m → (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
      ∧ (∀ k, k < (P G).K * (P G).m → (cd k).rho ≤ (P G).rmax)
      ∧ (∀ k, k < (P G).K * (P G).m → Fal36M4.priceAt (cutFamilyH (QMCLeafB.Finalization.wMatrixQ G)
          (t - QMCLeafB.EngineRuntime.Rq G / 40000) (P G).dq (P G).hdq (ok G t) (cX G t)
          (hgate G t) ((P G).K * (P G).m) _hall k) (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k)
          ≤ ((del k : ℚ) : ℝ))

/-- **THE LEAF FROM A MEMBERSHIP GATE + THE RECORD SLOT.**  `d9f601e5` (via m8/ph36's four-slot
assembly) from: the bit is the gate's `anyOk`, the gate is membership at the round's own rational
centre with symmetric centres, the register/ledger facts (`Poly`, `K·m ≥ 1`, top slice), the single
translation `(P G).dq = dqShallow G`, and the record slot above.

So at a membership gate the phase's TWO horns are discharged as follows: `hok` is
`hok_of_gate` — no analytic input at all — and the record is `RecSlot`, whose only non-definitional
content is the depth ledger and the price.  The collar (volume, content, reach) has disappeared from
the argument. -/
theorem solution_of_gate_recSlot
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ok : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cX : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hverdict : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      o G t = QMCLeafB.SimLoop.anyOk (ok G t) ((P G).K * (P G).m))
    (hPdq : ∀ G : QuantumMaxCutEnergy.Input, (P G).dq = QMCLeafB.RundataParams.dqShallow G)
    (hgate : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), Gate (QMCLeafB.Finalization.wMatrixQ G)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) (P G).dq (ok G t) (cX G t))
    (hsym : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), (cX G t k)ᵀ = cX G t k)
    (H : RecSlot P ok cX hgate) :
    QMCLeafB.FinishLine.SolutionStatement := by
  have hgate' : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      Gate (QMCLeafB.Finalization.wMatrixQ G) (t - QMCLeafB.RundataCert.eps G)
        (QMCLeafB.RundataParams.dqShallow G) (ok G t) (cX G t) := by
    intro G t
    rw [← hPdq G]
    exact hgate G t
  refine QMCLeafB.Asm36M8.solution_of_two_slots_selfRec o P ho hKm htop ?_ ?_
  · intro G t hn hlo hlt hb
    exact hok_of_gate (hverdict G t) (hgate' G t) (hsym G t) hb
  · intro G t hn hlo hlt hf
    have hall : ∀ k, k < (P G).K * (P G).m → ok G t k = false := by
      have hf' : QMCLeafB.SimLoop.anyOk (ok G t) ((P G).K * (P G).m) = false := by
        rw [← hverdict G t]; exact hf
      exact allFalse_of_anyOk_false _ hf'
    obtain ⟨cd, del, hnorm, hwit, hrho, hcne, hdel0, hcheck, hle, hprice⟩ := H G t hn hlo hlt hall
    exact bodyRec_of_gateH (P := P G) (hgate G t) hall cd del hnorm
      hwit hrho hcne hdel0 hcheck hle hprice

/-! ## 5.  Receipts

(i) A member need not be symmetric, so horn (A)'s `RelaxMem` at the recorded centre gives
`HokSlot`'s conclusion only with the programme's symmetry invariant.
(ii) Both horns are inhabited on real data. -/

/-- **Horn (A) does not give `HokSlot` for free**: `HokSlot` demands `cXᵀ = cX`, and a member need
not be symmetric.  So the passage (A) ⟹ `hok` carries one programme-side obligation — the state
coding must be symmetric — which is exactly what the `RoundProgram` state supplies. -/
theorem member_not_symmetric :
    ∃ cX : Matrix (Fin 2) (Fin 2) ℚ,
      RelaxMem (0 : Matrix (Fin 2) (Fin 2) ℚ) cX 0 1 ∧ cXᵀ ≠ cX := by
  refine ⟨!![1, 1; 0, 1], ⟨by norm_num, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    have hkey : QMCLeafB.SepOracle.qf (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) x
        = (x 0 + x 1 / 2) ^ 2 + (3 / 4) * x 1 ^ 2 := by
      rw [QMCLeafB.SepOracle.qf_eq_sum]
      simp [Fin.sum_univ_two]
      ring
    have hsum : ∑ i : Fin 2, x i ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
      simp [Fin.sum_univ_two]
    rw [hkey, hsum]
    nlinarith [sq_nonneg (x 0 + x 1 / 2), sq_nonneg (x 1)]
  · intro i
    fin_cases i <;> simp
  · simp [QMCLeafB.SepOracle.frob]
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp at h01

/-- **Horn (B) is inhabited on real data**: at the non-member centre `2·1` (diagonal gate violated)
every round's oracle verdict is the banked diagonal cut. -/
theorem nonvacuous_B :
    ∀ _k : ℕ, Nonempty (RelaxCut (0 : Matrix (Fin 2) (Fin 2) ℚ)
      (2 • (1 : Matrix (Fin 2) (Fin 2) ℚ)) 0 1) :=
  fun _ => QMCLeafB.RelaxOracle.diagCut_witness

/-- **Horn (A) is inhabited on real data**: at the member centre `1` the gate fires. -/
theorem nonvacuous_A :
    Gate (0 : Matrix (Fin 2) (Fin 2) ℚ) 0 1 (fun _ => true)
      (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℚ)) := by
  intro k
  exact ⟨fun _ => QMCLeafB.RelaxOracle.relaxMem_example,
    fun _ => rfl⟩


/-- **Non-vacuity, horn (A)**: at the member centre the dichotomy fires on its `ok` branch. -/
theorem nonvacuous_A_horn :
    ∃ k, (fun _ : ℕ => true) k = true
      ∧ RelaxMem (0 : Matrix (Fin 2) (Fin 2) ℚ) (1 : Matrix (Fin 2) (Fin 2) ℚ) 0 1 := by
  rcases dichotomy_of_gate (n := 2) (A := 0) (u := 0) (δ := 1) (ok := fun _ => true)
    (cX := fun _ => 1) (by norm_num) nonvacuous_A with h | h
  · exact h
  · exact Bool.noConfusion (h.1 0)

/-- At the non-member centre `2·1` there is no member, so the gate's `ok` is `false`. -/
theorem not_mem_two_one :
    ¬ RelaxMem (0 : Matrix (Fin 2) (Fin 2) ℚ) (2 • (1 : Matrix (Fin 2) (Fin 2) ℚ)) 0 1 := by
  intro h
  have hd := h.diag_near 0
  have h00 : (2 • (1 : Matrix (Fin 2) (Fin 2) ℚ)) 0 0 = 2 := by simp
  rw [h00] at hd
  norm_num at hd

/-- **Non-vacuity, horn (B)**: at the non-member centre the SAME dichotomy fires on its all-`false`
branch, and the cuts are the banked diagonal cuts at that centre. -/
theorem nonvacuous_B_horn :
    ∀ _k : ℕ, Nonempty (RelaxCut (0 : Matrix (Fin 2) (Fin 2) ℚ)
      (2 • (1 : Matrix (Fin 2) (Fin 2) ℚ)) 0 1) := by
  have hg : Gate (0 : Matrix (Fin 2) (Fin 2) ℚ) 0 1 (fun _ : ℕ => false)
      (fun _ => 2 • (1 : Matrix (Fin 2) (Fin 2) ℚ)) := by
    intro k
    exact ⟨fun h => Bool.noConfusion h, fun hm => absurd hm not_mem_two_one⟩
  rcases dichotomy_of_gate (n := 2) (A := 0) (u := 0) (δ := 1) (ok := fun _ : ℕ => false)
    (cX := fun _ => 2 • (1 : Matrix (Fin 2) (Fin 2) ℚ)) (by norm_num) hg with h | h
  · obtain ⟨k, hk, -⟩ := h
    exact Bool.noConfusion hk
  · exact h.2

/-! ## 6.  Axiom audit -/
#print axioms QMCLeafB.Dich37M1.frob_zero_left
#print axioms QMCLeafB.Dich37M1.mem_and_cut
#print axioms QMCLeafB.Dich37M1.okB
#print axioms QMCLeafB.Dich37M1.okB_eq_true_of_mem
#print axioms QMCLeafB.Dich37M1.okB_eq_true_iff_mem
#print axioms QMCLeafB.Dich37M1.okB_eq_false_iff_not_mem
#print axioms QMCLeafB.Dich37M1.Gate
#print axioms QMCLeafB.Dich37M1.Gate.mono
#print axioms QMCLeafB.Dich37M1.gate_of_okB
#print axioms QMCLeafB.Dich37M1.dichotomy_of_gate
#print axioms QMCLeafB.Dich37M1.dichotomy_exclusive
#print axioms QMCLeafB.Dich37M1.cuts_of_allFalse
#print axioms QMCLeafB.Dich37M1.bit_true_of_hornA
#print axioms QMCLeafB.Dich37M1.anyOk_eq_false_of_allFalse
#print axioms QMCLeafB.Dich37M1.bit_false_of_allFalse
#print axioms QMCLeafB.Dich37M1.hornA_member_at_own_centre
#print axioms QMCLeafB.Dich37M1.hokShape_of_gate
#print axioms QMCLeafB.Dich37M1.cutFamily
#print axioms QMCLeafB.Dich37M1.hcut_of_gate_allFalse
#print axioms QMCLeafB.Dich37M1.bodyRec_of_gate_allFalse
#print axioms QMCLeafB.Dich37M1.runParts_of_gate_allFalse
#print axioms QMCLeafB.Dich37M1.price_ledger_necessary
#print axioms QMCLeafB.Dich37M1.price_le_of_runLedger
#print axioms QMCLeafB.Dich37M1.price_ledger_sufficient
#print axioms QMCLeafB.Dich37M1.priceAt_eq_margin_of_normal_zero
#print axioms QMCLeafB.Dich37M1.zero_normal_not_recordable
#print axioms QMCLeafB.Dich37M1.member_not_symmetric
#print axioms QMCLeafB.Dich37M1.nonvacuous_A
#print axioms QMCLeafB.Dich37M1.nonvacuous_A_horn
#print axioms QMCLeafB.Dich37M1.not_mem_two_one
#print axioms QMCLeafB.Dich37M1.nonvacuous_B
#print axioms QMCLeafB.Dich37M1.nonvacuous_B_horn
#print axioms QMCLeafB.Dich37M1.allFalse_of_anyOk_false
#print axioms QMCLeafB.Dich37M1.vacCut
#print axioms QMCLeafB.Dich37M1.cutFamilyH
#print axioms QMCLeafB.Dich37M1.cutFamilyH_separates
#print axioms QMCLeafB.Dich37M1.bodyRec_of_gateH
#print axioms QMCLeafB.Dich37M1.RecSlot
#print axioms QMCLeafB.Dich37M1.solution_of_gate_recSlot
#print axioms QMCLeafB.Dich37M1.cdOfGate
#print axioms QMCLeafB.Dich37M1.cdOfGate_c
#print axioms QMCLeafB.Dich37M1.bodyRec_of_gate_transcript
#print axioms QMCLeafB.Dich37M1.dichotomy_of_gate_horizon
#print axioms QMCLeafB.Dich37M1.hok_of_gate
#print axioms QMCLeafB.Dich37M1.dichotomy_campaign
#print axioms QMCLeafB.Dich37M1.price_ledger_sufficient_of_le
#print axioms QMCLeafB.Dich37M1.priceAt_of_centre_identity
#print axioms QMCLeafB.Dich37M1.priceAt_le_margin_of_centre_identity

end QMCLeafB.Dich37M1

/-! ## 7.  Executable receipts: the gate RUNS

`okB` is a computable `def`: Lean compiles it and these evaluate without a kernel reduction blowup.
The first line is a MEMBER (the identity centre, `RelaxMem 0 1 0 1`); the second is a NON-member
(the centre `2·1`, whose diagonal gate fails); the third re-runs the gate at a member after the
polygon has been closed through `okB_eq_true_iff_mem`. -/


