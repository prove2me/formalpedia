-- Prove2me | Definitions.Def_QMCLeafB_pinchLower_m2
-- name    : QMCLeafB_pinchLower_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:53:53.385477+00:00
-- url     : https://prove2.me/theorems/dec7a223-d837-4b3e-a3f3-7c7984b35f2a
-- title:
--   QMCLeafB pinchLower_m2
-- statement:
--   # leaf B phase 18 — brick `pinch-lower` (swarm `smw1i2drp`, member m2, direction d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_drift_m3
import Definitions.Def_QMCLeafB_obstruction_m1
/-
# leaf B phase 18 — brick `pinch-lower` (swarm `smw1i2drp`, member m2, direction d3)

**The pinch-consistent centre reshape for the `hd` residual (`run-records`, item 1).**

`AuditM1`'s obstruction (machine-checked, `Check_obstruction_m1.lean`) is that the two conditions the
record conduit puts on the *same* centre — the identity-band `hdiagc`, `cXᵢᵢ ≤ 1 − dq/4`
(`RunPartsStream.hbody_of_diag`), and the `ok`-round `RelaxMem.diag_near`, `|cXᵢᵢ − 1| ≤ dq/4` — meet
only at `cXᵢᵢ = 1 − dq/4` exactly (`AuditM1.pinch_entry`), a value the program's dyadic grid does not
represent.  So the record centre cannot be the program's state; it must be the **lowered** point

    cX k := (1 − dq/4) • Q k ,

where `Q k` is the matrix the oracle actually queries (the state's own `stX`, reshaped), and the
`1 − dq/4` factor is the unique uniform scale that keeps `diag_near` (`AuditM1.scale_forces_boundary`).

This file performs the reshape once and for all, so that the run's records may be produced at `Q`
(where the program's own verdicts live: `RoundProgram.oracleR`/`OkLower.oracleV`) and consumed at
`cX` (where the conduit's conditions live):

* `lowerCentre` / `relaxCut_lower_centre` (§2): a cut at `Q` with normal `n` and margin `m` is a cut
  at `s•Q` with the **same** normal and margin whenever `0 ≤ ⟨n, Q⟩` — exact computation:
  `⟨n, X − sQ⟩ = ⟨n, X − Q⟩ + (1−s)⟨n,Q⟩` and `1 − s = dq/4 ≥ 0`.  (The run supplies the side
  condition: the diagonal cut's normal is `sign(1 − Qᵢᵢ)·eᵢeᵢᵀ` and the state's diagonal is below
  `1`, hence `⟨n,Q⟩ = Qᵢᵢ > 0`; a PSD cut is handled by *recomputing* its margin at `Q` instead —
  the caller's `hCq` may carry any margin, so `hpair` is the only thing asked of it.)
* `relaxMem_lower_centre` (§3): a `RelaxMem` at a unit-diagonal `Q` transports to the lowered centre
  by `AuditM1.relaxMem_boundary_smul`, at the exact price of the threshold shift
  `(1 − dq/4)(u' + dq/2) ≤ u + dq/2` — the single hinge of the `ok` branch.
* `runParts_lowered` (§4): **the whole residual list of `DriftExact.runParts_at_interior_exact`** at
  `cX := (1 − dq/4) • Q`, discharged from the same list at `Q`:

  - `C` at cut rounds ← `hCq` + the nonnegative pairing,
  - `hmem` at ok rounds ← `hmemq` + the threshold shift,
  - `hCsym` ← symmetry of `Q` (entrywise snap preserves it),
  - `hTrc` ← the *state trace* condition `∑ᵢ Qᵢᵢ ≤ n` (one number per round, not `n` entries):
    `∑ᵢ ((1 − dq/4)•Q)ᵢᵢ = (1 − dq/4)·∑ᵢ Qᵢᵢ ≤ n(1 − dq/4)`,
  - `hdriftc`/`hdriftd` ← the same condition at `Q` **plus the lowering cost** `(dq/4)·⟨c_k, flat Q_k⟩`
    (resp. `(dq/4)·tr Q_k`), which is exactly the difference `flat Q_k − flat cX_k`
    (`drift_shift`).  At `dq = dqShallow ≈ ε/(9Rq)` this is an `O(dq)` charge against the
    `marg_k/2` budget — the quantitative reason the pinch repair is cheap,
  - `hlam0/1/2`, `hcn`, `hcne`, `hcEq` are untouched by the lowering (`cX` does not occur in them).

So the residual of item 1 becomes: *per-round oracle records, state trace and drift at the program's
own centre `Q`*.  The pinch bookkeeping is removed from the residual.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audit at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.PinchLower

open QuantumMaxCutEnergy

/-! ## 1.  `frob` in its second argument, and the `flat` scaling law -/

/-- `frob` is additive in its second argument. -/
theorem frob_sub_right {n : ℕ} (C X Y : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.SepOracle.frob C (X - Y)
      = QMCLeafB.SepOracle.frob C X - QMCLeafB.SepOracle.frob C Y := by
  simp [QMCLeafB.SepOracle.frob, Finset.sum_sub_distrib, mul_sub]

/-- `frob` is homogeneous in its second argument. -/
theorem frob_smul_right {n : ℕ} (c : ℝ) (C X : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.SepOracle.frob C (c • X) = c * QMCLeafB.SepOracle.frob C X := by
  rw [QMCLeafB.SepOracle.frob, QMCLeafB.SepOracle.frob, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  ring

/-- The row-major flattening is homogeneous. -/
theorem flat_smul {n : ℕ} (c : ℝ) (Y : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.AnswerProducer.flat (c • Y) = c • QMCLeafB.AnswerProducer.flat Y := by
  funext k
  simp [QMCLeafB.AnswerProducer.flat, Matrix.smul_apply, smul_eq_mul]

/-- **The flattening of a rational scalar multiple** — the identity that turns the lowering into a
`(dq/4)`-charge in flat coordinates. -/
theorem flat_castMat_smul {n : ℕ} (s : ℚ) (Q : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (s • Q))
      = ((s : ℚ) : ℝ) • QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q) := by
  rw [QMCLeafB.RelaxOracle.castMat_smul, flat_smul]

/-- `(1 − dq/4) • v = v − (dq/4) • v` in real coordinates. -/
theorem smul_one_sub {N : ℕ} (dq : ℚ) (v : Fin N → ℝ) :
    (((1 - dq / 4 : ℚ)) : ℝ) • v = v - (((dq : ℚ) : ℝ) / 4) • v := by
  rw [show (((1 - dq / 4 : ℚ)) : ℝ) = 1 - ((dq : ℚ) : ℝ) / 4 by push_cast; ring]
  rw [sub_smul, one_smul]

/-- **The drift shift identity**: lowering the centre by `q` adds exactly `q·⟨c,v⟩` to the pairing
`⟨c, X − v⟩`.  This is the exact `hstatec`-free cost of the pinch repair. -/
theorem drift_shift {N : ℕ} (c X v : Fin N → ℝ) (q : ℝ) :
    c ⬝ᵥ (X - (v - q • v)) = c ⬝ᵥ (X - v) + q * (c ⬝ᵥ v) := by
  have h : X - (v - q • v) = (X - v) + q • v := by abel
  rw [h, dotProduct_add, dotProduct_smul, smul_eq_mul]

/-- A symmetric rational matrix stays symmetric under a uniform rescaling. -/
theorem transpose_smul_of_symm {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} (h : Qᵀ = Q) (s : ℚ) :
    (s • Q)ᵀ = s • Q := by
  rw [Matrix.transpose_smul, h]

/-- The trace of a uniform rescaling. -/
theorem trace_smul {n : ℕ} (s : ℚ) (Q : Matrix (Fin n) (Fin n) ℚ) :
    ∑ i, (s • Q) i i = s * ∑ i, Q i i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Matrix.smul_apply, smul_eq_mul]

/-! ## 2.  `RelaxCut` at the lowered centre

The cut was found at the program's own centre `Q`; the relaxed body is a *fixed* set (its centre is
not `Q`), so the only thing that changes under the lowering is the affine offset `⟨n, X − cX⟩`.  With
`⟨n,Q⟩ ≥ 0` the offset moves in the safe direction and the margin survives unchanged. -/

/-- **A cut at `Q` is a cut at `s • Q`** (same normal, same margin) when `s ≤ 1` and the normal pairs
nonnegatively with `Q`. -/
def lowerCentre {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (C : QMCLeafB.RelaxOracle.RelaxCut A Q u dq) {s : ℚ} (hs1 : s ≤ 1)
    (hpair : 0 ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat C.normal)
      (QMCLeafB.SepOracle.castMat Q)) :
    QMCLeafB.RelaxOracle.RelaxCut A (s • Q) u dq := by
  refine ⟨C.normal, C.margin, C.margin_pos, ?_⟩
  intro X hX
  have h1 := C.separates X hX
  have hcast : QMCLeafB.SepOracle.castMat (s • Q)
      = ((s : ℚ) : ℝ) • QMCLeafB.SepOracle.castMat Q :=
    QMCLeafB.RelaxOracle.castMat_smul s Q
  have hsplit : X - QMCLeafB.SepOracle.castMat (s • Q)
      = (X - QMCLeafB.SepOracle.castMat Q)
        + (1 - ((s : ℚ) : ℝ)) • QMCLeafB.SepOracle.castMat Q := by
    rw [hcast, sub_smul, one_smul]
    abel
  have hs0 : (0 : ℝ) ≤ 1 - ((s : ℚ) : ℝ) := by
    have hle : ((s : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hs1
    linarith
  rw [hsplit, QMCLeafB.SepOracle.frob_add, frob_smul_right]
  have h2 : 0 ≤ (1 - ((s : ℚ) : ℝ)) * QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat C.normal) (QMCLeafB.SepOracle.castMat Q) :=
    mul_nonneg hs0 hpair
  linarith

/-- The Proposition-valued form of `lowerCentre` (the axiom-audit target: the construction itself is
data, so its cone is read off a Prop restatement). -/
theorem relaxCut_lower_centre {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (C : QMCLeafB.RelaxOracle.RelaxCut A Q u dq) {s : ℚ} (hs1 : s ≤ 1)
    (hpair : 0 ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat C.normal)
      (QMCLeafB.SepOracle.castMat Q)) :
    ∃ C' : QMCLeafB.RelaxOracle.RelaxCut A (s • Q) u dq,
      C'.normal = C.normal ∧ C'.margin = C.margin :=
  ⟨lowerCentre C hs1 hpair, rfl, rfl⟩

/-- **The rational `frob` is the real `frob` of the casts** — what makes a margin shift expressible
in `ℚ` while the separation is proved in `ℝ`. -/
theorem castMat_frob {n : ℕ} (C Q : Matrix (Fin n) (Fin n) ℚ) :
    ((QMCLeafB.SepOracle.frob C Q : ℚ) : ℝ)
      = QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat C)
          (QMCLeafB.SepOracle.castMat Q) := by
  simp only [QMCLeafB.SepOracle.frob, QMCLeafB.SepOracle.castMat_apply]
  push_cast
  rfl

#print axioms QMCLeafB.PinchLower.castMat_frob

/-- **The complete cut transport** (no pairing hypothesis): the same normal at the lowered centre,
with the margin `m − (1 − s)·⟨n,Q⟩` (`⟨n,Q⟩ = frob n Q`, the *linear* pairing, not the quadratic form).
`lowerCentre` is the case `⟨n,Q⟩ ≥ 0`, where the shift is a *gain* and the margin can be kept; this
form covers the PSD branch (`n = vvᵀ`, `qf Q v = ⟨n,Q⟩ < 0`, so the shift is a *cost*).  Together the
two give: *any* `RelaxCut` at `Q` yields one at `s • Q`. -/
def lowerCentreShift {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (C : QMCLeafB.RelaxOracle.RelaxCut A Q u dq) {s : ℚ}
    (hpos : 0 < C.margin - (1 - s) * QMCLeafB.SepOracle.frob C.normal Q) :
    QMCLeafB.RelaxOracle.RelaxCut A (s • Q) u dq := by
  refine ⟨C.normal, C.margin - (1 - s) * QMCLeafB.SepOracle.frob C.normal Q, hpos, ?_⟩
  intro X hX
  have h1 := C.separates X hX
  have hcast : QMCLeafB.SepOracle.castMat (s • Q)
      = ((s : ℚ) : ℝ) • QMCLeafB.SepOracle.castMat Q :=
    QMCLeafB.RelaxOracle.castMat_smul s Q
  have hsplit : X - QMCLeafB.SepOracle.castMat (s • Q)
      = (X - QMCLeafB.SepOracle.castMat Q)
        + (1 - ((s : ℚ) : ℝ)) • QMCLeafB.SepOracle.castMat Q := by
    rw [hcast, sub_smul, one_smul]
    abel
  rw [hsplit, QMCLeafB.SepOracle.frob_add, frob_smul_right, ← castMat_frob]
  push_cast
  linarith

/-- The Proposition-valued form of `lowerCentreShift` (audit target). -/
theorem lowerCentreShift_spec {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (C : QMCLeafB.RelaxOracle.RelaxCut A Q u dq) {s : ℚ}
    (hpos : 0 < C.margin - (1 - s) * QMCLeafB.SepOracle.frob C.normal Q) :
    ∃ C' : QMCLeafB.RelaxOracle.RelaxCut A (s • Q) u dq,
      C'.normal = C.normal
        ∧ C'.margin = C.margin - (1 - s) * QMCLeafB.SepOracle.frob C.normal Q :=
  ⟨lowerCentreShift C hpos, rfl, rfl⟩

#print axioms QMCLeafB.PinchLower.lowerCentreShift_spec

/-! ## 3.  `RelaxMem` at the lowered centre

`ok` is the *lower* body (`frob ≤ u + δ/2`) at the state's own (unit) diagonal; the lowering keeps
`diag_near` exactly on the band boundary and pays only the threshold shift. -/

theorem relaxMem_lower_centre {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u u' dq : ℚ}
    (hmem : QMCLeafB.RelaxOracle.RelaxMem A Q u' dq) (hdq : 0 < dq) (h4 : dq ≤ 4)
    (hQ : ∀ i, Q i i = 1) (hu : (1 - dq / 4) * (u' + dq / 2) ≤ u + dq / 2) :
    QMCLeafB.RelaxOracle.RelaxMem A ((1 - dq / 4) • Q) u dq :=
  QMCLeafB.AuditM1.relaxMem_boundary_smul hmem hdq h4 (fun i => by rw [hQ i]) hu

#print axioms QMCLeafB.PinchLower.frob_sub_right
#print axioms QMCLeafB.PinchLower.frob_smul_right
#print axioms QMCLeafB.PinchLower.flat_smul
#print axioms QMCLeafB.PinchLower.flat_castMat_smul
#print axioms QMCLeafB.PinchLower.smul_one_sub
#print axioms QMCLeafB.PinchLower.drift_shift
#print axioms QMCLeafB.PinchLower.transpose_smul_of_symm
#print axioms QMCLeafB.PinchLower.trace_smul
#print axioms QMCLeafB.PinchLower.relaxCut_lower_centre
#print axioms QMCLeafB.PinchLower.relaxMem_lower_centre

/-! ## 3b.  The run supplies the pairing: the diagonal cut's normal pairs with the state

The `dvR ≠ 0` branch of `RoundProgram.oracleR` answers with the diagonal normal
`sign(1 − Qᵢᵢ)·eᵢeᵢᵀ`; on a state with `0 ≤ Qᵢᵢ ≤ 1` that normal pairs nonnegatively with `Q`, so
`lowerCentre` keeps its margin.  (For the PSD branch use `lowerCentreShift`.) -/

theorem hpair_diagNormal {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} (i : Fin n)
    (h0 : 0 ≤ Q i i) (h1 : Q i i ≤ 1) :
    0 ≤ QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (QMCLeafB.RelaxOracle.diagNormal Q i))
      (QMCLeafB.SepOracle.castMat Q) := by
  rw [QMCLeafB.RelaxOracle.frob_diagNormal,
    show (QMCLeafB.SepOracle.castMat Q) i i = Q i i from by simp [QMCLeafB.SepOracle.castMat]]
  rcases lt_or_eq_of_le h1 with hlt | heq
  · have hpos : 0 < 1 - Q i i := by linarith
    have hs : QMCLeafB.SepOracle.signOf (1 - Q i i) = 1 := by
      simp [QMCLeafB.SepOracle.signOf, hpos]
    rw [hs]
    push_cast
    have h0' : (0 : ℝ) ≤ ((Q i i : ℚ) : ℝ) := by exact_mod_cast h0
    linarith
  · have hs : QMCLeafB.SepOracle.signOf (1 - Q i i) = 0 := by
      simp [QMCLeafB.SepOracle.signOf, heq]
    rw [hs]
    simp

#print axioms QMCLeafB.PinchLower.hpair_diagNormal

/-! ## 3c.  The two scalar conditions, in their weakest form

The trace slot only needs `∑ᵢ Qᵢᵢ ≤ n`, i.e. an *entrywise* bound `Qᵢᵢ ≤ 1` (the run's diagonal
invariant: the GLS scaling and the rank-one subtraction keep every diagonal entry below `1`).  The
`ok`-round threshold shift `(1 − dq/4)(u' + dq/2) ≤ u + dq/2` is, at `u' = u`, exactly
`0 ≤ u + dq/2`; along the campaign's `wMatrix ≥ 0`, a state in the lower body has `frob A Q ≥ 0`, so
this is the state's own feasibility read-out and not a new condition. -/

theorem htrace_of_entry {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} (h : ∀ i, Q i i ≤ 1) :
    ∑ i, Q i i ≤ (n : ℚ) := by
  have h1 : ∑ i, Q i i ≤ ∑ _i : Fin n, (1 : ℚ) := Finset.sum_le_sum (fun i _ => h i)
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h1

theorem threshold_shift_of_nonneg {u dq : ℚ} (hdq : 0 ≤ dq) (hu : 0 ≤ u + dq / 2) :
    (1 - dq / 4) * (u + dq / 2) ≤ u + dq / 2 :=
  mul_le_of_le_one_left hu (by linarith)

#print axioms QMCLeafB.PinchLower.htrace_of_entry
#print axioms QMCLeafB.PinchLower.threshold_shift_of_nonneg

/-! ## 4.  The record list at the lowered centre

Everything the conduit `DriftExact.runParts_at_interior_exact` asks for at `cX := (1 − dq/4) • Q`,
produced from the same list at the program's own centre `Q`. -/

theorem runParts_lowered
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ) (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (u' : ℕ → ℚ)
    (hQsym : ∀ k, (Q k)ᵀ = Q k)
    (htraceQ : ∀ k, ∑ i, (Q k) i i ≤ (G.n : ℚ))
    (hCq : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (Q k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hpair : ∀ k (hok : ok k = false),
      0 ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat (hCq k hok).normal)
        (QMCLeafB.SepOracle.castMat (Q k)))
    (hmargq : ∀ k (hok : ok k = false), marg k = (hCq k hok).margin)
    (hunidiag : ∀ k, ok k = true → ∀ i, Q k i i = 1)
    (hmemq : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (Q k) (u' k)
        (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (huq : ∀ k, ok k = true →
      (1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
          * (u' k + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2)
        ≤ (t - QMCLeafB.RundataCert.eps G) + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (hCq k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn
              cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
            ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn cn hcne (c k) k|
        + 9 * marg k ^ 2
            / (4 * (((QMCLeafB.UnionShallow.paramsKbc2 G)).rmax) ^ 2) + 1
      ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hdriftcQ : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k)))
        + (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4
          * ((fun i => ((c k i : ℚ) : ℝ))
              ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftdQ : ∀ k, ok k = false →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G ((QMCLeafB.UnionShallow.paramsKbc2 G)) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k)))
        + (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4
          * (QMCLeafB.RunPartsStream.dOne G.n
              ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m)) :
    Nonempty (QMCLeafB.FinalStroke.RunParts o G t
      (QMCLeafB.UnionShallow.paramsKbc2 G)) := by
  have hdq : 0 < (QMCLeafB.UnionShallow.paramsKbc2 G).dq :=
    QMCLeafB.RundataParams.dqShallow_pos G
  have h4 : (QMCLeafB.UnionShallow.paramsKbc2 G).dq ≤ 4 := by
    have h1 : (QMCLeafB.UnionShallow.paramsKbc2 G).dq ≤ 1 :=
      QMCLeafB.UnionShallow.dqShallow_le_one G (ne_of_gt hRq)
    linarith
  have hs1 : (1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) ≤ 1 := by linarith
  have hs0 : (0 : ℚ) ≤ 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4 := by linarith
  refine Nonempty.intro ?_
  refine QMCLeafB.DriftExact.runParts_at_interior_exact o G t hn hRq ok marg
    (fun k => (1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) • Q k) lam c cn ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hverdict
  · -- `C`: the cut at the lowered centre
    intro k hok
    exact lowerCentre (hCq k hok) hs1 (hpair k hok)
  · -- `hmarg`: the margin is untouched by the lowering
    intro k hok
    exact hmargq k hok
  · -- `hmem`: the ok round at the lowered centre
    intro k hk hok
    exact relaxMem_lower_centre (hmemq k hk hok) hdq h4 (hunidiag k hok) (huq k hok)
  · -- `hCsym`
    intro k
    exact transpose_smul_of_symm (hQsym k) _
  · exact hcEq
  · exact hcn
  · exact hcne
  · exact hlam0
  · exact hlam1
  · exact hlam2
  · -- `hTrc`: the state-trace condition `∑ᵢ Qᵢᵢ ≤ n`
    intro k
    rw [trace_smul]
    have h1 := mul_le_mul_of_nonneg_left (htraceQ k) hs0
    have h2 : (G.n : ℚ) * (1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
        = (1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) * (G.n : ℚ) := by ring
    rw [h2]
    exact h1
  · -- `hdriftc`: the base drift plus the explicit lowering cost
    intro k hok
    have hv : QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat
        ((1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) • Q k))
        = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k))
          - (((((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4)
              • QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k))) := by
      rw [flat_castMat_smul, smul_one_sub]
    rw [hv, drift_shift]
    have := hdriftcQ k hok
    linarith
  · -- `hdriftd`: same, with the identity direction
    intro k hok
    have hv : QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat
        ((1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) • Q k))
        = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k))
          - (((((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4)
              • QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k))) := by
      rw [flat_castMat_smul, smul_one_sub]
    rw [hv, drift_shift]
    have := hdriftdQ k hok
    linarith

#print axioms QMCLeafB.PinchLower.runParts_lowered


