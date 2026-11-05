-- Prove2me | Definitions.Def_QMCLeafB_relaxapi
-- name    : QMCLeafB_relaxapi
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:58:28.650712+00:00
-- url     : https://prove2.me/theorems/643ab3eb-cbd0-42f8-8041-7e11407b3b92
-- title:
--   QMCLeafB relaxapi
-- statement:
--   # leaf B phase 30 — the relax-api toolbox (swarm `smw239r00`, member m3, direction d4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_relax_oracle_m4
import Definitions.Def_QMCLeafB_ldltcert2_m5
import Definitions.Def_QMCLeafB_hemptyR
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_unionShallow
/-
# leaf B phase 30 — the relax-api toolbox (swarm `smw239r00`, member m3, direction d4)

Engine-independent, machine-checked glue for the campaign's last construction phase.  Nothing here
adds a program slot, a ledger, or a verdict lane; the file is the *toolbox* the program / `hd` /
`htop` lanes cite instead of reproving.

## What is proved

* §1 **Level/slack transport, both shapes, with the directions pinned.**
  `relaxBodyLE` and `RelaxMem` are monotone *upward* in both the level `u` and the tolerance `δ`
  (`relaxMem_mono_δ`, `relaxMem_mono_joint`); `RelaxCut` transports *downward* in both
  (`relaxCut_transfer` — a cut certified on a looser relaxation separates every tighter one).
  The psd clause alone is monotone upward in `δ` as well (`psd_clause_mono`), and that is the
  *only* slack direction that works: **both** attempted tightenings are refuted here, the psd one
  (`psd_clause_tighten_false`, centre `−(3/4)·1`) and the diagonal one
  (`relaxMem_mono_δ_false`, centre `(19/16)·1`).  Consequence, load-bearing for the repaired round:
  a psd certificate produced at tolerance `ν` serves the loop's clause at every `δ ≥ ν`, so a test
  at `dq/2` *does* serve the bundle at `dq` — but never the other way round.
  `relaxMem_of_psd_clause` assembles the whole bundle from a psd clause plus the two cheap slots.
* §2 **The certified psd test, consumed.**  `PivPsdMargin` (the coded-state clause of
  `ContractM7`, at grid `d ≥ 2N²/δ`) is transported onto a plain rational matrix
  (`psd_clause_of_pivPsdMargin`), instantiated at the descent's own exchange rate
  (`psd_clause_of_tolerance`), and composed with §1 at the campaign's numbers
  (`relaxMem_at_campaign_of_test`: test at `ν = dq/2`, grid `4n²/dq`, bundle at `dq`), and finally
  with the shelf's rounding bridge (`hcert_of_certified_test`: the coded test plus the two cheap
  slots produce `RunParts.hcert`'s genuine unit-diagonal PSD point at `t + Rq/40000`).
* §3 **The top slice's witness, unconditionally.**  On `t ≥ −δ/2` the identity is a `RelaxMem`
  member at the *level* `t` (`relaxMem_one`), and on the leaf's top slice `t ≥ −Rq/40000` it is the
  unit-diagonal PSD point `RunParts.hcert` asks for (`hcert_top_slice`).  This is the witness side
  of `htop`, independent of the trajectory: at every `G` (even `Rq = 0`).
* §4 **The cut side's nonvanishing, branch by branch.**  `RunParts.hcne` (`(cd k).c ≠ 0`) is the
  field the trivial record fails, so each oracle branch is checked at the exact place it is produced:
  the psd branch needs `v ≠ 0` (`psdCut_normal_ne_zero`, with `psdCut_margin_pos`); the diagonal
  branch never vanishes **at a positive tolerance** (`diagCut_normal_ne_zero`, and `0 < δ` is shown
  to be necessary); the computable summed-diagonal branch never vanishes when its margin is positive
  (`diagSumCut_normal_ne_zero`); the trace branch's normal is literally `−A`
  (`traceHighCut_normal_eq`) and is nonzero exactly on a nonempty relaxation
  (`traceHighCut_normal_ne_zero_of_nonempty`).  The *low*-side trace cut is flagged: `A = 0` is
  consistent with a nonempty body there and its normal vanishes.
* §5 **Level alignment at the campaign's interface.**  `RunParts` reads both certificates at the
  engine's `(t − eps G, dq G)` while the round tests at its own level; the two valid fill-ins are
  recorded — cuts at any level `≥ t − eps G` fill `hcut` (`hcut_of_cuts_at_level`, with the `roundT`
  instance `hcut_of_cuts_top_level` at `t + eps G`), members at any level `≤ t − eps G` fill `hcert`
  (`hcert_of_relaxMem_at_level`).  The opposite moves are refuted: `relaxMem_level_not_down` is the
  level warning (a member at the `roundT` level `t + eps G` does *not* serve the engine's bundle),
  and the engine's own ok test is calibrated so that no transport is needed on its route
  (`levelOf = t − eps + dq/2` is exactly the trace bound).  §5.1 is the one-call endpoint for the
  program lane: `relaxMem_at_campaign_of_grid` and `hcert_of_campaign_grid` take the descent's own
  data (box-run certificate, `pivAns = false`, grid `4n² ≤ dq·stD`) and return the loop's `ok`
  bundle, resp. `RunParts.hcert`'s genuine unit-diagonal PSD point at `t + Rq/40000`.

## What is NOT here

No centre stream / trajectory construction (that is the crux lane), no `hwit` preimage, no
`del`/`rho` bookkeeping, no ledger, no `Poly`.  The file is a pure geometric/arithmetic toolbox.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` receipts at the end (expected `[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.RelaxApiM3

open QMCLeafB.SepOracle
open QMCLeafB.BallFloor (relaxBodyLE)
open QMCLeafB.RelaxOracle

/-! ## 1.  Level / slack transport -/

/-- `relaxBodyLE` is monotone in the level `u` (the objective conjunct is the only one that reads
`u`).  Local copy: the same statement lives in `HBodyM6`, whose module pulls the audit cone in. -/
theorem relaxBodyLE_mono_u {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {δ : ℝ} {u₁ u₂ : ℝ}
    (h : u₁ ≤ u₂) {X : Matrix (Fin n) (Fin n) ℝ} (hX : relaxBodyLE A u₁ δ X) :
    relaxBodyLE A u₂ δ X := by
  obtain ⟨hpsd, hdiag, htr⟩ := hX
  exact ⟨hpsd, hdiag, le_trans htr (by linarith)⟩

/-- `relaxBodyLE` is monotone in the tolerance `δ`: the psd margin loosens, the diagonal band
widens, and the trace bound rises. -/
theorem relaxBodyLE_mono_δ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u : ℝ} {δ₁ δ₂ : ℝ}
    (h : δ₁ ≤ δ₂) {X : Matrix (Fin n) (Fin n) ℝ} (hX : relaxBodyLE A u δ₁ X) :
    relaxBodyLE A u δ₂ X := by
  obtain ⟨hpsd, hdiag, htr⟩ := hX
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hS : (0 : ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    nlinarith [hpsd x, hS]
  · intro i
    have := hdiag i
    nlinarith [this]
  · linarith

/-- Joint monotonicity: the relaxation only grows when both the level and the tolerance rise. -/
theorem relaxBodyLE_mono_joint {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u₁ u₂ δ₁ δ₂ : ℝ}
    (hu : u₁ ≤ u₂) (hδ : δ₁ ≤ δ₂) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : relaxBodyLE A u₁ δ₁ X) : relaxBodyLE A u₂ δ₂ X :=
  relaxBodyLE_mono_u hu (relaxBodyLE_mono_δ hδ hX)

/-- **`RelaxMem` is monotone in the tolerance** (upward), the psd and diagonal clauses being the
ones that move. -/
theorem relaxMem_mono_δ {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ₁ δ₂ : ℚ}
    (h : δ₁ ≤ δ₂) (hM : RelaxMem A cX u δ₁) : RelaxMem A cX u δ₂ := by
  obtain ⟨hδ, hpsd, hdiag, htr⟩ := hM
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · intro x
    have hS : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    nlinarith [hpsd x, hS]
  · intro i
    have := hdiag i
    nlinarith [this]
  · linarith

/-- Local copy of the level-monotonicity of `RelaxMem` (`HBodyM6.relaxMem_mono`, restated so this
module does not have to import the audit cone). -/
theorem relaxMem_mono_u_local {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ} {u₁ u₂ : ℚ}
    (h : u₁ ≤ u₂) (hM : RelaxMem A cX u₁ δ) : RelaxMem A cX u₂ δ := by
  obtain ⟨hδ, hpsd, hdiag, htr⟩ := hM
  exact ⟨hδ, hpsd, hdiag, le_trans htr (by linarith)⟩

/-- **Joint monotonicity of `RelaxMem`**: level up, tolerance up. -/
theorem relaxMem_mono_joint {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u₁ u₂ δ₁ δ₂ : ℚ}
    (hu : u₁ ≤ u₂) (hδ : δ₁ ≤ δ₂) (hM : RelaxMem A cX u₁ δ₁) : RelaxMem A cX u₂ δ₂ :=
  relaxMem_mono_δ hδ (relaxMem_mono_u_local hu hM)

/-- **The psd clause is monotone upward in the tolerance** (and only upward): a `−ν/2` margin
certificate serves every `δ ≥ ν`.  This is what lets a test at `dq/2` serve the bundle at `dq`. -/
theorem psd_clause_mono {n : ℕ} {cX : Matrix (Fin n) (Fin n) ℚ} {ν δ : ℚ}
    (h : ∀ x : Fin n → ℚ, -(ν / 2) * (∑ i, x i ^ 2) ≤ qf cX x) (hνδ : ν ≤ δ) :
    ∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ qf cX x := by
  intro x
  have hS : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hmono : (ν / 2) * (∑ i, x i ^ 2) ≤ (δ / 2) * (∑ i, x i ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hS
  have h1 := h x
  linarith

/-- **The bundle from a psd clause plus the two cheap slots.**  This is the assembly the repaired
round performs: the certified test supplies `hpsd` at its own (smaller) tolerance, the diagonal and
trace tests are the cheap rational slots, and the loop's `RelaxMem` at `δ` follows. -/
theorem relaxMem_of_psd_clause {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u ν δ : ℚ}
    (hδ : 0 < δ) (hνδ : ν ≤ δ)
    (hpsd : ∀ x : Fin n → ℚ, -(ν / 2) * (∑ i, x i ^ 2) ≤ qf cX x)
    (hdiag : ∀ i, |cX i i - 1| ≤ δ / 4) (htrace : frob A cX ≤ u + δ / 2) :
    RelaxMem A cX u δ :=
  ⟨hδ, psd_clause_mono hpsd hνδ, hdiag, htrace⟩

/-- **`RelaxCut` transports to a smaller body.**  A cut certified at the relaxation `(u₁, δ₁)`
separates the relaxation at every `(u₀, δ₀)` with `u₀ ≤ u₁`, `δ₀ ≤ δ₁` — the normal and the margin
are unchanged, only the quantified body shrinks.  (Nothing here is specific to the oracle's three
branches: it is the `RelaxCut` analogue of `relaxMem_mono_joint`.)  A `def`, since `RelaxCut` carries
data. -/
def relaxCut_transfer {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u₁ δ₁ u₀ δ₀ : ℚ}
    (C : RelaxCut A cX u₁ δ₁) (hu : u₀ ≤ u₁) (hδ : δ₀ ≤ δ₁) :
    RelaxCut A cX u₀ δ₀ where
  normal := C.normal
  margin := C.margin
  margin_pos := C.margin_pos
  separates := by
    intro X hX
    have huR : ((u₀ : ℚ) : ℝ) ≤ ((u₁ : ℚ) : ℝ) := by exact_mod_cast hu
    have hδR : ((δ₀ : ℚ) : ℝ) ≤ ((δ₁ : ℚ) : ℝ) := by exact_mod_cast hδ
    exact C.separates X (relaxBodyLE_mono_joint huR hδR hX)

/-! ### 1.1  The two refuted tightenings

Both "shrink the slack" moves fail, and each fails for its own clause.  They are recorded because
the campaign's arithmetic repeatedly wants to move a certificate between the levels
`t − ε`, `t + ε`, `t − ε + dq/2` and between the tolerances `dq`, `dq/2`, `3dq/4`. -/

/-- **The psd clause does not tighten.**  `cX = −(1/3)·1` has `qf = −(1/3)‖x‖²`, which satisfies the
`−δ/2` margin at `δ = 1` (`−1/2 ≤ −1/3`) and violates it at `δ = 1/2` (`−1/4 ≤ −1/3` is false). -/
theorem psd_clause_tighten_false :
    (∀ x : Fin 2 → ℚ, -((1 : ℚ) / 2) * (∑ i, x i ^ 2)
        ≤ qf ((-(1 / 3 : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) x)
      ∧ ¬ (∀ x : Fin 2 → ℚ, -(((1 : ℚ) / 2) / 2) * (∑ i, x i ^ 2)
        ≤ qf ((-(1 / 3 : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) x) := by
  have hq : ∀ x : Fin 2 → ℚ,
      qf ((-(1 / 3 : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) x = (-(1 / 3)) * (∑ i, x i ^ 2) := by
    intro x
    rw [qf_smulQ, qf_one]
  constructor
  · intro x
    rw [hq x]
    have hS : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    nlinarith
  · intro h
    have h1 := h (fun _ => 1)
    rw [hq (fun _ => 1)] at h1
    norm_num at h1

/-- **`RelaxMem` does not transport downward in the tolerance either** — now the diagonal clause
is the obstruction (the psd one is free here: `(19/16)·1` is positive).  `|19/16 − 1| = 3/16` sits
inside `δ/4 = 1/4` but outside `(1/2)/4 = 1/8`. -/
theorem relaxMem_mono_δ_false :
    RelaxMem (0 : Matrix (Fin 2) (Fin 2) ℚ) ((19 / 16 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ))
        0 1
      ∧ ¬ RelaxMem (0 : Matrix (Fin 2) (Fin 2) ℚ) ((19 / 16 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ))
        0 (1 / 2) := by
  have hii : ∀ i : Fin 2, ((19 / 16 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) i i = 19 / 16 := by
    intro i
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  have hq : ∀ x : Fin 2 → ℚ,
      qf ((19 / 16 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) x = (19 / 16) * (∑ i, x i ^ 2) := by
    intro x
    rw [qf_smulQ, qf_one]
  constructor
  · refine ⟨by norm_num, ?_, ?_, ?_⟩
    · intro x
      rw [hq x]
      have hS : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      nlinarith
    · intro i
      rw [hii i]
      norm_num
    · have h0 : frob (0 : Matrix (Fin 2) (Fin 2) ℚ)
          ((19 / 16 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) = 0 := by simp [frob]
      rw [h0]
      norm_num
  · rintro ⟨-, -, hdiag, -⟩
    have h0 := hdiag 0
    rw [hii 0] at h0
    norm_num at h0

/-! ## 2.  The certified psd test, consumed -/

/-- **The coded clause on a plain matrix.**  `ContractM7.PivPsdMargin s δ` is stated over
`MatQ.toMatrix (stN s) (stX s)`; this is the same clause at a stated dimension `n` with
`stN s = n` — the shape `RelaxMem.psd_margin` speaks. -/
theorem psd_clause_of_pivPsdMargin {n : ℕ} (s : QMCLeafB.RoundProgram.RSt) {δ : ℚ}
    (hn : QMCLeafB.RoundProgram.stN s = n)
    (h : QMCLeafB.ContractM7.PivPsdMargin s δ) :
    ∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2)
      ≤ qf (MatQ.toMatrix n (QMCLeafB.RoundProgram.stX s)) x := by
  intro x
  subst hn
  exact h x

/-- **The certified test at the grid's tolerance, on a plain matrix.**  `pivPsdMargin_of_tolerance`
(`2N²/d` exchange rate) plus the shape bridge: whenever the snapped descent answers `false` at a
state whose grid dominates `2N²/ν`, the matrix its code names has a `−ν/2` psd margin — decided by
rational comparisons only. -/
theorem psd_clause_of_tolerance (s : QMCLeafB.RoundProgram.RSt) {ν : ℚ}
    (hlen : QMCLeafB.RoundProgram.stN s ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hD : 0 < QMCLeafB.RoundProgram.stD s)
    (hsym : ∀ i j : Fin (QMCLeafB.RoundProgram.stN s),
      QMCLeafB.PivExact.matOf (QMCLeafB.RoundProgram.stN s) (QMCLeafB.RoundProgram.stX s) i j
        = QMCLeafB.PivExact.matOf (QMCLeafB.RoundProgram.stN s)
            (QMCLeafB.RoundProgram.stX s) j i)
    (hbox : QMCLeafB.LdltCertM5.BoxRun (QMCLeafB.RoundProgram.stMu s)
      (QMCLeafB.RoundProgram.stN s)
      ((QMCLeafB.RoundProgram.stMu s, QMCLeafB.RoundProgram.stD s),
        QMCLeafB.RoundProgram.toRows (QMCLeafB.RoundProgram.stN s, QMCLeafB.RoundProgram.stX s),
        ([] : _)))
    (hpiv : (QMCLeafB.RoundProgram.pivAns s).1 = false) (hν : 0 < ν)
    (hgrid : 2 * (QMCLeafB.RoundProgram.stN s : ℚ) * (QMCLeafB.RoundProgram.stN s : ℚ)
      ≤ ν * (QMCLeafB.RoundProgram.stD s : ℚ)) :
    ∀ x : Fin (QMCLeafB.RoundProgram.stN s) → ℚ,
      -(ν / 2) * (∑ i, x i ^ 2)
        ≤ qf (MatQ.toMatrix (QMCLeafB.RoundProgram.stN s) (QMCLeafB.RoundProgram.stX s)) x :=
  psd_clause_of_pivPsdMargin s rfl
    (QMCLeafB.LdltCertM5.pivPsdMargin_of_tolerance s hlen hD hsym hbox hpiv hν hgrid)

/-- **The loop's `ok` bundle at the campaign's own numbers, from the coded test at `dq/2`.**
The test runs at half the loop's tolerance (grid `4n²/dq` — `psd_clause_of_tolerance` with
`ν = dq/2`), §1's upward transport lifts its margin to `dq`, and the two cheap rational slots close
the bundle.  This is the `RelaxMem` that `RundataCert.hcert_of_relaxMem` then consumes. -/
theorem relaxMem_at_campaign_of_test (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (s : QMCLeafB.RoundProgram.RSt)
    (hn : QMCLeafB.RoundProgram.stN s = G.n)
    (htest : QMCLeafB.ContractM7.PivPsdMargin s (QMCLeafB.RundataCert.dq G / 2))
    (hdq : 0 < QMCLeafB.RundataCert.dq G)
    (hdiag : ∀ i, |MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s) i i - 1|
      ≤ QMCLeafB.RundataCert.dq G / 4)
    (htrace : frob (QMCLeafB.Finalization.wMatrixQ G)
        (MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s))
        ≤ (t - QMCLeafB.RundataCert.eps G) + QMCLeafB.RundataCert.dq G / 2) :
    RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
      (MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s))
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataCert.dq G) :=
  relaxMem_of_psd_clause hdq (by linarith)
    (psd_clause_of_pivPsdMargin s hn htest) hdiag htrace

/-- **`RunParts.hcert` from the coded test.**  The whole `ok`-slot chain at the campaign's numbers:
the certified psd test at `dq/2` plus the diagonal and trace slots produce a **genuine**
unit-diagonal PSD point with `tr (wMatrix G · X) ≤ t + Rq/40000` — the shape `RunParts.hcert`
consumes at every `ok` round. -/
theorem hcert_of_certified_test (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (s : QMCLeafB.RoundProgram.RSt)
    (hn : QMCLeafB.RoundProgram.stN s = G.n)
    (htest : QMCLeafB.ContractM7.PivPsdMargin s (QMCLeafB.RundataCert.dq G / 2))
    (hn1 : 1 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdq : 0 < QMCLeafB.RundataCert.dq G)
    (hCsym : (MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s))ᵀ
      = MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s))
    (hdiag : ∀ i, |MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s) i i - 1|
      ≤ QMCLeafB.RundataCert.dq G / 4)
    (htrace : frob (QMCLeafB.Finalization.wMatrixQ G)
        (MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s))
        ≤ (t - QMCLeafB.RundataCert.eps G) + QMCLeafB.RundataCert.dq G / 2) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
  have hM := relaxMem_at_campaign_of_test G t s hn htest hdq hdiag htrace
  have h := QMCLeafB.RundataCert.hcert_of_relaxMem G t
    (MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s)) hn1 hRq hM hCsym
  simpa only [QMCLeafB.RundataCert.eps] using h

/-! ## 3.  The top slice's witness: the identity -/

/-- The identity is a unit-diagonal PSD point. -/
theorem isUnitDiagPSD_one {n : ℕ} :
    QMCLeafB.AnswerProducer.IsUnitDiagPSD (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨Matrix.PosSemidef.one, fun i => by simp⟩

/-- **The weight matrix's pairing with the identity vanishes** — it is the trace of the weight
matrix, which has zero diagonal. -/
theorem trace_wMatrix_one (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.wMatrix G * (1 : Matrix (Fin G.n) (Fin G.n) ℝ)).trace = 0 := by
  rw [Matrix.mul_one, Matrix.trace]
  exact Finset.sum_eq_zero fun i _ => QMCLeafB.wMatrix_apply_of_eq

/-- **The identity is a `RelaxMem` member at level `t`** as soon as `−δ/2 ≤ t`.  Its objective is
`0` (zero diagonal), its diagonal is exactly `1`, and its quadratic form is positive. -/
theorem relaxMem_one (G : QuantumMaxCutEnergy.Input) {t δ : ℚ} (hδ : 0 < δ)
    (ht : -(δ / 2) ≤ t) :
    RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (1 : Matrix (Fin G.n) (Fin G.n) ℚ) t δ := by
  refine ⟨hδ, ?_, ?_, ?_⟩
  · intro x
    have h1 : qf (1 : Matrix (Fin G.n) (Fin G.n) ℚ) x = ∑ i, x i ^ 2 := qf_one x
    rw [h1]
    have hS : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    nlinarith
  · intro i
    have hii : (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i i = 1 := by simp
    rw [hii, sub_self, abs_zero]
    linarith
  · have h0 : frob (QMCLeafB.Finalization.wMatrixQ G)
        (1 : Matrix (Fin G.n) (Fin G.n) ℚ) = 0 := by
      rw [frob]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases h : j = i
      · subst h; rw [QMCLeafB.Finalization.wMatrixQ_apply_of_eq]; simp
      · simp [Matrix.one_apply_ne (Ne.symm h)]
    rw [h0]
    linarith

/-- **The identity is a member at the `roundT` level `t + εw` on the whole top slice — for every
positive tolerance.**  This is the strongest form of the `htop` witness: on `t ≥ −Rq/40000` the
level `t + Rq/40000` is nonnegative, so the trace clause `0 ≤ (t + εw) + δ/2` costs nothing and no
relation between `δ` and `εw` is needed. -/
theorem relaxMem_one_top_level (G : QuantumMaxCutEnergy.Input) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (ht : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) :
    RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
      (t + QMCLeafB.EngineRuntime.Rq G / 40000) δ := by
  have hnnR : (0 : ℝ) ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
    linarith
  have hnn : (0 : ℚ) ≤ t + QMCLeafB.EngineRuntime.Rq G / 40000 := by
    have h1 : (0 : ℝ) ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by linarith
    have h2 : (((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
        = (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
      push_cast
      ring
    have h3 : ((0 : ℚ) : ℝ)
        ≤ (((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
      rw [h2]
      simpa using h1
    exact_mod_cast h3
  refine relaxMem_one G hδ ?_
  linarith

/-- **`RunParts.hcert`'s conclusion on the top slice, unconditionally**: the identity is a genuine
unit-diagonal PSD point whose objective is `0 ≤ t + Rq/40000`.  No hypothesis on `G` at all. -/
theorem hcert_top_slice (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (ht : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
  refine ⟨1, isUnitDiagPSD_one, ?_⟩
  rw [trace_wMatrix_one]
  linarith

/-! ## 4.  The cut side's nonvanishing -/

/-- **A psd-branch cut's normal is nonzero** when the violated direction is: `v vᵀ ≠ 0`.  This is
the `RunParts.hcne` shape (`(cd k).c ≠ 0`) that the trivial record fails, at the exact place the
oracle produces it. -/
theorem psdCut_normal_ne_zero {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    {v : Fin n → ℚ} (hv : v ≠ 0)
    (h : qf cX v < -(δ / 2) * (∑ i, v i ^ 2)) :
    (psdCutOf (A := A) (cX := cX) (u := u) (δ := δ) h).normal ≠ 0 := by
  intro h0
  have h1 : vecMulVec v v = 0 := h0
  apply hv
  funext j
  have h' := congrFun (congrFun h1 j) j
  simp only [Matrix.vecMulVec_apply, Matrix.zero_apply] at h'
  exact (mul_eq_zero.mp h').elim id id

/-- `signOf` of a nonzero rational is nonzero (local copy of `HBodyM6.signOf_ne_zero`, which lives
behind the audit cone). -/
theorem signOf_ne_zero' {q : ℚ} (hq : q ≠ 0) : signOf q ≠ 0 := by
  intro h
  have h1 : signOf q * q = |q| := signOf_mul_self q
  rw [h, zero_mul] at h1
  exact hq (abs_eq_zero.mp h1.symm)

/-- **The diagonal branch's normal never vanishes** — at a positive tolerance.  The branch
hypothesis `δ/4 < |cX_ii − 1|` with `0 < δ` forces `|cX_ii − 1| > 0`, hence
`signOf (1 − cX_ii) ≠ 0`, and `signOf · • e_i e_iᵀ` is then nonzero at `(i, i)`.

Note the `0 < δ` hypothesis is *necessary*: at `δ < 0` a centre with `cX_ii = 1` satisfies the branch
hypothesis while its normal vanishes (the trivial record again).  In the campaign `δ = dq > 0`
always, so the branch is recordable there. -/
theorem diagCut_normal_ne_zero {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} (i : Fin n)
    (hδ : 0 < δ) (h : δ / 4 < |cX i i - 1|) :
    (diagCutOf (A := A) (cX := cX) (u := u) (δ := δ) i h).normal ≠ 0 := by
  intro h0
  have hne : cX i i - 1 ≠ 0 := by
    intro h1
    rw [h1, abs_zero] at h
    linarith
  have hs : signOf (1 - cX i i) ≠ 0 :=
    @signOf_ne_zero' (1 - cX i i) (by intro h1; exact hne (by linarith))
  have h' : signOf (1 - cX i i) • vecMulVec (delta i) (delta i)
      = (0 : Matrix (Fin n) (Fin n) ℚ) := h0
  have h2 : signOf (1 - cX i i) = 0 := by
    have h3 := congrFun (congrFun h' i) i
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, Matrix.zero_apply] at h3
    have hdel : QMCLeafB.SepOracle.delta i i = (1 : ℚ) := by
      simp only [QMCLeafB.SepOracle.delta]
      simp
    rw [hdel] at h3
    simpa using h3
  exact hs h2

/-- **The summed diagonal branch's normal never vanishes when its margin is positive.**  A positive
`diagMarginSum` means some coordinate carries a nonzero `signOf`, hence a nonzero diagonal entry.

`hcne` receipt: the computable diagonal cut (the choice-free branch) is always recordable. -/
theorem diagSumCut_normal_ne_zero {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hδ : 0 < δ) (h : 0 < diagMarginSum cX δ) :
    (diagSumCut (A := A) (cX := cX) (u := u) (δ := δ) h).normal ≠ 0 := by
  intro h0
  have h' : diagonal (diagNormalSum cX δ) = (0 : Matrix (Fin n) (Fin n) ℚ) := h0
  obtain ⟨i, hi⟩ : ∃ i, δ / 4 < |cX i i - 1| := by
    by_contra hc
    push_neg at hc
    have hz : diagMarginSum cX δ = 0 :=
      (diagMarginSum_eq_zero_iff cX δ).mpr hc
    linarith
  have hni : diagNormalSum cX δ i ≠ 0 := by
    simp only [diagNormalSum, if_pos hi]
    apply signOf_ne_zero'
    intro h1
    apply (show cX i i - 1 ≠ 0 by intro h2; rw [h2, abs_zero] at hi; linarith)
    linarith
  have h2 := congrFun (congrFun h' i) i
  simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply] at h2
  exact hni h2

/-- **The trace branch's normal is `−A`.**  It is nonzero exactly when `A ≠ 0` — this is the one
branch whose `hcne` receipt needs a hypothesis. -/
theorem traceHighCut_normal_eq {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (h : u + δ / 2 < frob A cX) :
    (traceHighCutOf (A := A) (cX := cX) (u := u) (δ := δ) h).normal = -A := rfl

/-- **The high-side trace cut's normal is nonzero on a nonempty relaxation.**  `A = 0` would force
`0 ≤ u + δ/2 < 0` at every member, so a nonempty body rules it out.

`hcne` receipt: at a *nonempty* relaxation the high-side trace cut is recordable.  (The
recordability of the *low*-side cut — `traceLowCutOf`, used only by `relaxOk_or_cut` — is a
different matter: there `A = 0` is consistent with a nonempty body and the normal vanishes.) -/
theorem traceHighCut_normal_ne_zero_of_nonempty {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ}
    {u δ : ℚ} (h : u + δ / 2 < frob A cX)
    (hne : ∃ X : Matrix (Fin n) (Fin n) ℝ,
      relaxBodyLE (castMat A) ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) X) :
    (traceHighCutOf (A := A) (cX := cX) (u := u) (δ := δ) h).normal ≠ 0 := by
  rw [traceHighCut_normal_eq]
  intro h0
  have hA : A = 0 := neg_eq_zero.mp h0
  subst hA
  obtain ⟨X, -, -, htr⟩ := hne
  have hz : QMCLeafB.BallFloor.frob
      (QMCLeafB.SepOracle.castMat (0 : Matrix (Fin n) (Fin n) ℚ)) X = 0 := by
    simp [QMCLeafB.BallFloor.frob, QMCLeafB.SepOracle.castMat_apply]
  rw [hz] at htr
  have hR : ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 < 0 := by
    have h1 : (((u + δ / 2 : ℚ)) : ℝ)
        < ((frob (0 : Matrix (Fin n) (Fin n) ℚ) cX : ℚ) : ℝ) := by exact_mod_cast h
    have h2 : frob (0 : Matrix (Fin n) (Fin n) ℚ) cX = 0 := by simp [frob]
    rw [h2] at h1
    rw [show (((u + δ / 2 : ℚ)) : ℝ) = ((u : ℚ) : ℝ) + ((δ : ℚ) : ℝ) / 2 by
      push_cast; ring] at h1
    linarith
  linarith

/-- **The recorded margin is positive** (the domain of `RunParts.hdel0` plus `hcheck`). -/
theorem psdCut_margin_pos {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    {v : Fin n → ℚ} (h : qf cX v < -(δ / 2) * (∑ i, v i ^ 2)) :
    0 < (psdCutOf (A := A) (cX := cX) (u := u) (δ := δ) h).margin :=
  (psdCutOf (A := A) (cX := cX) (u := u) (δ := δ) h).margin_pos

/-! ## 5.  Level alignment at the campaign's interface

`RunParts` reads both certificates at the **engine's** level `u₀ = t − eps G` and tolerance `dq G`,
while the repaired round tests at its own level (m7's `roundT` design: `t + εw`; a lower-body design:
`t − eps + dq/2`).  Both are *above* `u₀`, so §1's two transport directions give the fill-ins: cuts
transport down, `RelaxMem` transports down.  Nothing else in the shape changes. -/

/-- **`RunParts.hcut` from cuts certified at any level above the engine's.**  A cut that separates
the relaxation at `(u₁, dq G)` with `t − eps G ≤ u₁` separates the engine's own relaxation at
`(t − eps G, dq G)` — §1's `relaxCut_transfer` — and `RundataCert.hcut_of_relaxCuts` then supplies
the slot verbatim. -/
theorem hcut_of_cuts_at_level (G : QuantumMaxCutEnergy.Input) (t : ℚ) {u₁ : ℚ}
    (hu : t - QMCLeafB.RundataCert.eps G ≤ u₁) {M : ℝ} (T : ℕ) (ok : ℕ → Bool)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (mg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k) u₁
        (QMCLeafB.RundataCert.dq G))
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hmg : ∀ k (hok : ok k = false), mg k = (C k hok).margin)
    (hctr : ∀ k, QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
      = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) :
    ∀ k, k < T → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
          ((t : ℝ) - ((QMCLeafB.RundataCert.eps G : ℚ) : ℝ))
          ((QMCLeafB.RundataCert.dq G : ℚ) : ℝ) M →
        -(((mg k : ℚ)) : ℝ)
          ≤ QMCLeafB.EngineIterates.cutCR cd k
              ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
                (0 : Fin (G.n * G.n) → ℝ) cd k) :=
  QMCLeafB.RundataCert.hcut_of_relaxCuts G t T ok cd mg cX
    (fun k hok => relaxCut_transfer (C k hok) hu le_rfl) hnorm hmg hctr

/-- The instance the `roundT` design uses: cuts certified at the leaf's own upper level `t + eps G`
fill `RunParts.hcut` at the engine's `t − eps G`. -/
theorem hcut_of_cuts_top_level (G : QuantumMaxCutEnergy.Input) (t : ℚ) {M : ℝ} (T : ℕ)
    (ok : ℕ → Bool) (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (mg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t + QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataCert.dq G))
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hmg : ∀ k (hok : ok k = false), mg k = (C k hok).margin)
    (hctr : ∀ k, QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
      = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) :
    ∀ k, k < T → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
          ((t : ℝ) - ((QMCLeafB.RundataCert.eps G : ℚ) : ℝ))
          ((QMCLeafB.RundataCert.dq G : ℚ) : ℝ) M →
        -(((mg k : ℚ)) : ℝ)
          ≤ QMCLeafB.EngineIterates.cutCR cd k
              ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
                (0 : Fin (G.n * G.n) → ℝ) cd k) :=
  hcut_of_cuts_at_level G t
    (by linarith [QMCLeafB.RundataCert.eps_nonneg G]) T ok cd mg cX C hnorm hmg hctr

/-- **`RunParts.hcert` from a member certified at any level at or below the engine's.**
This is the *valid* direction, and it is the opposite of the cut's: membership is *upward* closed in
the level (`relaxMem_mono`), so a member at `u₁ ≤ t − eps G` serves the engine's bundle at
`t − eps G`, while a member at a *higher* level does not (its trace clause is the weaker one).  Note
that the repaired round does not even need this: its own test level is `t − eps G + dq G/2`, which is
*exactly* `RelaxMem`'s trace bound at `(t − eps G, dq G)`, so an `ok` answer supplies the clause
directly (`relaxMem_of_psd_clause`). -/
theorem hcert_of_relaxMem_at_level (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (cX : Matrix (Fin G.n) (Fin G.n) ℚ) {u₁ : ℚ}
    (hu : u₁ ≤ t - QMCLeafB.RundataCert.eps G)
    (hn1 : 1 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX u₁
      (QMCLeafB.RundataCert.dq G))
    (hCsym : cXᵀ = cX) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
  have h0 := QMCLeafB.RundataCert.hcert_of_relaxMem G t cX hn1 hRq
    (relaxMem_mono_u_local hu h) hCsym
  simpa only [QMCLeafB.RundataCert.eps] using h0

/-- **Warn-off: a member at the `roundT` level `t + eps G` does NOT serve the engine's `hcert`.**
The trace clause of `RelaxMem` at the higher level is the weaker one; the `ok` bundle must be read at
`t − eps G` itself (`OkLower.relaxMem_of_oracleV_ok` does exactly that, its test level being
`t − eps G + dq G/2`).  Concretely at `A = 1`, `cX = 2·1`, `δ = 4`: the level `5` bundle holds
(`4 ≤ 5 + 2`) and the level `0` bundle fails (`4 ≤ 0 + 2` is false). -/
theorem relaxMem_level_not_down :
    RelaxMem (1 : Matrix (Fin 2) (Fin 2) ℚ) ((2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) 5 4
      ∧ ¬ RelaxMem (1 : Matrix (Fin 2) (Fin 2) ℚ) ((2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) 0 4 := by
  have hii : ∀ i : Fin 2, ((2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) i i = 2 := by
    intro i
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  have hq : ∀ x : Fin 2 → ℚ,
      qf ((2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) x = 2 * (∑ i, x i ^ 2) := by
    intro x
    rw [qf_smulQ, qf_one]
  have hfr : frob (1 : Matrix (Fin 2) (Fin 2) ℚ) ((2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) = 4 := by
    rw [frob]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_mul, one_mul,
      Fin.sum_univ_two, Fin.isValue, Matrix.one_apply_eq, Matrix.one_apply_ne]
    norm_num
  constructor
  · refine ⟨by norm_num, ?_, ?_, ?_⟩
    · intro x
      rw [hq x]
      nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (x i))]
    · intro i
      rw [hii i]
      norm_num
    · rw [hfr]; norm_num
  · rintro ⟨-, -, -, htr⟩
    rw [hfr] at htr
    norm_num at htr

/-! ### 5.1  The ok slot in one call, from the round's own grid

`relaxMem_at_campaign_of_test` takes the coded clause as a hypothesis.  For the program lane the
data are the descent's: the state's grid `stD`, its box-run certificate, the verdict
`(pivAns s).1 = false`, and the condition `4n² ≤ dq·stD` (i.e. the test ran at `dq/2`).  The two
lemmas below do the whole derivation, so a round's `ok` branch is one application. -/

/-- **`RelaxMem` at the campaign's numbers from the descent's own grid.** -/
theorem relaxMem_at_campaign_of_grid (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (s : QMCLeafB.RoundProgram.RSt)
    (hn : QMCLeafB.RoundProgram.stN s = G.n)
    (hlen : QMCLeafB.RoundProgram.stN s ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hD : 0 < QMCLeafB.RoundProgram.stD s)
    (hsym : ∀ i j : Fin (QMCLeafB.RoundProgram.stN s),
      QMCLeafB.PivExact.matOf (QMCLeafB.RoundProgram.stN s) (QMCLeafB.RoundProgram.stX s) i j
        = QMCLeafB.PivExact.matOf (QMCLeafB.RoundProgram.stN s)
            (QMCLeafB.RoundProgram.stX s) j i)
    (hbox : QMCLeafB.LdltCertM5.BoxRun (QMCLeafB.RoundProgram.stMu s)
      (QMCLeafB.RoundProgram.stN s)
      ((QMCLeafB.RoundProgram.stMu s, QMCLeafB.RoundProgram.stD s),
        QMCLeafB.RoundProgram.toRows (QMCLeafB.RoundProgram.stN s, QMCLeafB.RoundProgram.stX s),
        ([] : _)))
    (hpiv : (QMCLeafB.RoundProgram.pivAns s).1 = false)
    (hdq : 0 < QMCLeafB.RundataCert.dq G)
    (hgrid : 4 * (G.n : ℚ) * (G.n : ℚ) ≤ QMCLeafB.RundataCert.dq G
      * (QMCLeafB.RoundProgram.stD s : ℚ))
    (hdiag : ∀ i, |MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s) i i - 1|
      ≤ QMCLeafB.RundataCert.dq G / 4)
    (htrace : frob (QMCLeafB.Finalization.wMatrixQ G)
        (MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s))
        ≤ (t - QMCLeafB.RundataCert.eps G) + QMCLeafB.RundataCert.dq G / 2) :
    RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
      (MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s))
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataCert.dq G) := by
  refine relaxMem_at_campaign_of_test G t s hn ?_ hdq hdiag htrace
  have hν : 0 < QMCLeafB.RundataCert.dq G / 2 := by linarith
  have hgrid' : 2 * (QMCLeafB.RoundProgram.stN s : ℚ) * (QMCLeafB.RoundProgram.stN s : ℚ)
      ≤ (QMCLeafB.RundataCert.dq G / 2) * (QMCLeafB.RoundProgram.stD s : ℚ) := by
    rw [hn]
    linarith
  exact QMCLeafB.LdltCertM5.pivPsdMargin_of_tolerance s hlen hD hsym hbox hpiv hν hgrid'

/-- **`RunParts.hcert` in one call, from the descent's own grid.**  The complete `ok`-slot chain at
the campaign's numbers: the certified test at `dq/2` (grid `4n²/dq`) plus the cheap diagonal and
trace slots plus symmetry produce the genuine unit-diagonal PSD point with
`tr (wMatrix G · X) ≤ t + Rq/40000`. -/
theorem hcert_of_campaign_grid (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (s : QMCLeafB.RoundProgram.RSt)
    (hn : QMCLeafB.RoundProgram.stN s = G.n)
    (hlen : QMCLeafB.RoundProgram.stN s ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hD : 0 < QMCLeafB.RoundProgram.stD s)
    (hsym : ∀ i j : Fin (QMCLeafB.RoundProgram.stN s),
      QMCLeafB.PivExact.matOf (QMCLeafB.RoundProgram.stN s) (QMCLeafB.RoundProgram.stX s) i j
        = QMCLeafB.PivExact.matOf (QMCLeafB.RoundProgram.stN s)
            (QMCLeafB.RoundProgram.stX s) j i)
    (hbox : QMCLeafB.LdltCertM5.BoxRun (QMCLeafB.RoundProgram.stMu s)
      (QMCLeafB.RoundProgram.stN s)
      ((QMCLeafB.RoundProgram.stMu s, QMCLeafB.RoundProgram.stD s),
        QMCLeafB.RoundProgram.toRows (QMCLeafB.RoundProgram.stN s, QMCLeafB.RoundProgram.stX s),
        ([] : _)))
    (hpiv : (QMCLeafB.RoundProgram.pivAns s).1 = false)
    (hn1 : 1 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdq : 0 < QMCLeafB.RundataCert.dq G)
    (hgrid : 4 * (G.n : ℚ) * (G.n : ℚ) ≤ QMCLeafB.RundataCert.dq G
      * (QMCLeafB.RoundProgram.stD s : ℚ))
    (hCsym : (MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s))ᵀ
      = MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s))
    (hdiag : ∀ i, |MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s) i i - 1|
      ≤ QMCLeafB.RundataCert.dq G / 4)
    (htrace : frob (QMCLeafB.Finalization.wMatrixQ G)
        (MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s))
        ≤ (t - QMCLeafB.RundataCert.eps G) + QMCLeafB.RundataCert.dq G / 2) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
  have hM := relaxMem_at_campaign_of_grid G t s hn hlen hD hsym hbox hpiv hdq hgrid hdiag htrace
  have h := QMCLeafB.RundataCert.hcert_of_relaxMem G t
    (MatQ.toMatrix G.n (QMCLeafB.RoundProgram.stX s)) hn1 hRq hM hCsym
  simpa only [QMCLeafB.RundataCert.eps] using h

end QMCLeafB.RelaxApiM3

/-! ## Axiom audit -/
#print axioms QMCLeafB.RelaxApiM3.relaxBodyLE_mono_u
#print axioms QMCLeafB.RelaxApiM3.relaxBodyLE_mono_δ
#print axioms QMCLeafB.RelaxApiM3.relaxBodyLE_mono_joint
#print axioms QMCLeafB.RelaxApiM3.relaxMem_mono_δ
#print axioms QMCLeafB.RelaxApiM3.relaxMem_mono_u_local
#print axioms QMCLeafB.RelaxApiM3.relaxMem_mono_joint
#print axioms QMCLeafB.RelaxApiM3.psd_clause_mono
#print axioms QMCLeafB.RelaxApiM3.relaxMem_of_psd_clause
#print axioms QMCLeafB.RelaxApiM3.relaxCut_transfer
#print axioms QMCLeafB.RelaxApiM3.psd_clause_tighten_false
#print axioms QMCLeafB.RelaxApiM3.relaxMem_mono_δ_false
#print axioms QMCLeafB.RelaxApiM3.psd_clause_of_pivPsdMargin
#print axioms QMCLeafB.RelaxApiM3.psd_clause_of_tolerance
#print axioms QMCLeafB.RelaxApiM3.relaxMem_at_campaign_of_test
#print axioms QMCLeafB.RelaxApiM3.hcert_of_certified_test
#print axioms QMCLeafB.RelaxApiM3.isUnitDiagPSD_one
#print axioms QMCLeafB.RelaxApiM3.trace_wMatrix_one
#print axioms QMCLeafB.RelaxApiM3.relaxMem_one
#print axioms QMCLeafB.RelaxApiM3.relaxMem_one_top_level
#print axioms QMCLeafB.RelaxApiM3.hcert_top_slice
#print axioms QMCLeafB.RelaxApiM3.psdCut_normal_ne_zero
#print axioms QMCLeafB.RelaxApiM3.psdCut_margin_pos
#print axioms QMCLeafB.RelaxApiM3.diagCut_normal_ne_zero
#print axioms QMCLeafB.RelaxApiM3.diagSumCut_normal_ne_zero
#print axioms QMCLeafB.RelaxApiM3.traceHighCut_normal_eq
#print axioms QMCLeafB.RelaxApiM3.traceHighCut_normal_ne_zero_of_nonempty
#print axioms QMCLeafB.RelaxApiM3.hcut_of_cuts_at_level
#print axioms QMCLeafB.RelaxApiM3.hcut_of_cuts_top_level
#print axioms QMCLeafB.RelaxApiM3.relaxMem_at_campaign_of_grid
#print axioms QMCLeafB.RelaxApiM3.hcert_of_campaign_grid
#print axioms QMCLeafB.RelaxApiM3.hcert_of_relaxMem_at_level
#print axioms QMCLeafB.RelaxApiM3.relaxMem_level_not_down


