-- Prove2me | Definitions.Def_QMCLeafB_InterfaceAudit_m2
-- name    : QMCLeafB_InterfaceAudit_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:12:24.2658+00:00
-- url     : https://prove2.me/theorems/fff6f6bd-8efd-4502-bcf3-9a3dc9c88aba
-- title:
--   QMCLeafB InterfaceAudit_m2
-- statement:
--   # Leaf-B phase 3 — interface audit and the rational-value last mile (member m2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QMCLeafB_Core
import Definitions.Def_QMCLeafB_RoundingOut
import Definitions.Def_QMCLeafB_certpsd
import Definitions.Def_QMCLeafB_finalization
/-
# Leaf-B phase 3 — interface audit and the rational-value last mile (member m2)

This file does **not** re-prove any of the five bricks.  It does three things.

## 1. Cross-library compatibility (proved, `rfl`-level)

The rational PSD test exists in three copies — `CastBridge.qf`, `RoundingOut.qf`,
`CertPSD.qf` — introduced by three different bricks.  They are *definitionally the same
expression*, so a hypothesis stated for one is accepted by the other two.  The lemmas below
make that transfer explicit, so `brick-sep-oracle` (which speaks `CertPSD`/margins),
`brick-finalization` (which speaks `RoundingOut`) and `brick-engine-iterates` (which speaks
`CastBridge`/`IntegrationProbe`) can be composed without rewriting any statement.

## 2. The rational weight matrix and the `ℚ≥0` lower value

The leaf statement's matrix is an inline `Matrix.of` over `↑(G.weights e)`; `QMCLeafB.wMatrix`
is *verbatim* that expression over `ℝ`.  The engine, however, produces **rational** data, and
the leaf's `L : Input → ℚ≥0` must be a nonnegative *rational*.  So we need the rational copy
`wMatrixQ`, its cast identity `castM (wMatrixQ G) = wMatrix G`, the rational double-sum
identity `∑∑ wMatrixQ = 2 ∑ w`, and the rational lower value `ratLowerValue` with
`0 ≤ ratLowerValue` and `↑(ratLowerValue) = lowerValue (castM A) (castM X)`.

## 3. The last mile to the leaf statement

`rat_sandwich_lowerValue`  : rational primal/dual data + rational gap ⟹ the sandwich for the
                             *rational* lower value (the exact shape the leaf needs).
`leafB_value_bounds_rat`   : the graph-level form, with the slack `∑ w / 10000`.
`target_of_engine`         : **exactly the type of `agm_classical_sdp_lower_value_tm2`**
                             (same conclusion, same slack), under precisely the two remaining
                             obligations: the rational iterate data with its gap bound, and one
                             `PolyProgram` computing the resulting rational value.  The TM2
                             obligation is discharged here (`PolyProgram.stock` + `nnratOutput`),
                             so nothing about `TM2ComputableInPolyTime` is left to the bricks.

Nothing here introduces `sorry`, `axiom` or `native_decide`; the axiom audit is at the end.
-/

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary

namespace QMCLeafB.AuditM2

variable {n : ℕ}

/-! ## 1.  The three rational PSD tests agree -/

/-- `RoundingOut.qf` and `CertPSD.qf` are the same function (same definition body). -/
theorem qf_roundingOut_eq_certPSD (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    RoundingOut.qf M x = CertPSD.qf M x := rfl

/-- `RoundingOut.qf` and `CastBridge.qf` are the same function. -/
theorem qf_roundingOut_eq_castBridge (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    RoundingOut.qf M x = CastBridge.qf M x := rfl

/-- The `RoundingOut` rational test is the `CertPSD` one. -/
theorem roundRatPSD_iff_certPSD (X : Matrix (Fin n) (Fin n) ℚ) :
    RoundingOut.RatPSD X ↔ ∀ x : Fin n → ℚ, 0 ≤ CertPSD.qf X x :=
  Iff.intro (fun h x => h x) (fun h x => h x)

/-- The `RoundingOut` rational test is the `CastBridge` one. -/
theorem roundRatPSD_iff_castBridge (X : Matrix (Fin n) (Fin n) ℚ) :
    RoundingOut.RatPSD X ↔ ∀ x : Fin n → ℚ, 0 ≤ CastBridge.qf X x :=
  Iff.intro (fun h x => h x) (fun h x => h x)

/-- **Executable certification of the engine's output.**  From the abstract rational test used by
`RoundingOut`/`CastBridge` a `GramCert` passing the executable `CertPSD` check exists
(`premise_iff_exists_cert`).  This is the step `brick-finalization` needs to hand a checked
certificate to the program layer. -/
theorem exists_cert_of_roundRatPSD (X : Matrix (Fin n) (Fin n) ℚ) (hX : Xᵀ = X)
    (h : RoundingOut.RatPSD X) :
    ∃ (m : ℕ) (C : CertPSD.GramCert n m), C.check X = true :=
  (CertPSD.premise_iff_exists_cert X hX).mp (fun x => h x)

/-! ## 2.  The rational weight matrix — one definition, re-exported

`brick-finalization` (member m4, `Solutions/Check_finalization.lean`, accepted) already defines the
rational weight matrix, its cast bridge, its structural facts and its total weight.  We *do not*
redefine them: the lemmas below are the same statements restated under this namespace so that this
file's endgame consumes the accepted definition and any drift is a compile error. -/

/-- The rational weight matrix of the accepted finalization brick. -/
noncomputable abbrev wMatrixQ (G : QuantumMaxCutEnergy.Input) : Matrix (Fin G.n) (Fin G.n) ℚ :=
  Finalization.wMatrixQ G

/-- The cast of the rational weight matrix is the leaf's real weight matrix. -/
theorem castM_wMatrixQ (G : QuantumMaxCutEnergy.Input) :
    CastBridge.castM (wMatrixQ G) = wMatrix G :=
  Finalization.wMatrix_castM G

/-- The rational weight matrix is entrywise nonnegative. -/
theorem wMatrixQ_nonneg (G : QuantumMaxCutEnergy.Input) (i j : Fin G.n) :
    0 ≤ wMatrixQ G i j :=
  (Finalization.isQMCWeight_wMatrixQ G).nonneg i j

/-- The total weight of the rational weight matrix is twice the edge weight, over `ℚ`. -/
theorem sum_wMatrixQ (G : QuantumMaxCutEnergy.Input) :
    (∑ i, ∑ j, wMatrixQ G i j) = 2 * ∑ e, (G.weights e : ℚ) :=
  Finalization.Vq_wMatrixQ G

/-! ## 3.  The rational lower value -/

/-- The lower value attached to a rational primal/dual pair, computed over `ℚ`. -/
def ratLowerValue (A X : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  ((∑ i, ∑ j, A i j) - (A * X).trace) / 4

/-- The rational lower value casts to the real `lowerValue` of the cast pair. -/
theorem ratLowerValue_cast (A X : Matrix (Fin n) (Fin n) ℚ) :
    ((ratLowerValue A X : ℚ) : ℝ) = lowerValue (CastBridge.castM A) (CastBridge.castM X) := by
  simp only [ratLowerValue, lowerValue, V]
  exact CastBridge.cast_lowerValue A X

/-- A rational unit-diagonal PSD primal point has entries in `[-1, 1]`. -/
theorem abs_entry_le_one {X : Matrix (Fin n) (Fin n) ℚ} (hX : Xᵀ = X)
    (hXp : RoundingOut.RatPSD X) (hdiag : ∀ i, X i i = 1) (i j : Fin n) : |X i j| ≤ 1 := by
  have h2 := RoundingOut.two_mul_abs_entry_le_diag_add hX hXp i j
  rw [hdiag i, hdiag j] at h2
  linarith

/-- **Nonnegativity of the rational lower value** on entrywise nonnegative data.  This is the
`ℚ≥0` obligation of the leaf's `L : Input → ℚ≥0`, discharged over `ℚ` (the merged
`QMCLeafB.lowerValue_nonneg` is the real, `PosSemidef` version). -/
theorem ratLowerValue_nonneg (A X : Matrix (Fin n) (Fin n) ℚ) (hA : ∀ i j, 0 ≤ A i j)
    (hX : Xᵀ = X) (hXp : RoundingOut.RatPSD X) (hdiag : ∀ i, X i i = 1) :
    0 ≤ ratLowerValue A X := by
  have hsym : ∀ i j, X j i = X i j := fun i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hX i) j
  have htrace : (A * X).trace = ∑ i, ∑ j, A i j * X i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsym]
  have hle : (A * X).trace ≤ ∑ i, ∑ j, A i j := by
    rw [htrace]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hx : X i j ≤ 1 := (abs_le.mp (abs_entry_le_one hX hXp hdiag i j)).2
    calc A i j * X i j ≤ A i j * 1 := by
          exact mul_le_mul_of_nonneg_left hx (hA i j)
      _ = A i j := mul_one _
  rw [ratLowerValue]
  linarith

/-! ## 4.  The sandwich for the rational lower value -/

/-- **The leaf's per-graph numerical endgame, stated for the *rational* lower value.**  Given
rational primal/dual data certified by the rational tests and the rational gap bound
`∑ y + tr (A X) ≤ (∑ᵢ∑ⱼ Aᵢⱼ)/5000`, the rational lower value is nonnegative, and its cast is
sandwiched by the SDP value with slack `(∑ᵢ∑ⱼ Aᵢⱼ)/20000`. -/
theorem rat_sandwich_lowerValue (A X : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ) (S : ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hXsym : Xᵀ = X)
    (hXtest : ∀ x : Fin n → ℚ, 0 ≤ CastBridge.qf X x) (hXdiag : ∀ i, X i i = 1)
    (hysym : (diagonal y + A)ᵀ = diagonal y + A)
    (hytest : ∀ x : Fin n → ℚ, 0 ≤ CastBridge.qf (diagonal y + A) x)
    (hgap : (∑ i, y i) + (A * X).trace ≤ (∑ i, ∑ j, A i j) / 5000)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (CastBridge.castM A) S) :
    0 ≤ ratLowerValue A X ∧
      ((ratLowerValue A X : ℚ) : ℝ) ≤ S ∧
      S - ((ratLowerValue A X : ℚ) : ℝ) ≤ (∑ i, ∑ j, A i j) / 20000 := by
  have hXp : RoundingOut.RatPSD X := fun x => hXtest x
  have hnn := ratLowerValue_nonneg A X hA hXsym hXp hXdiag
  have hcast := ratLowerValue_cast A X
  obtain ⟨h1, h2⟩ :=
    IntegrationProbe.rat_sandwich A X y S hXsym hXtest hXdiag hysym hytest hgap hS
  refine ⟨hnn, ?_, ?_⟩
  · rw [hcast]; exact h1
  · rw [hcast]
    rw [IntegrationProbe.V_castM A] at h2
    refine h2.trans (le_of_eq ?_)
    push_cast
    ring

/-! ## 5.  The graph-level form with the leaf's constant -/

/-- **The leaf's value bound with a rational (`ℚ≥0`-able) lower value.**  Per graph: the SDP
value `S` exists, is above the rational lower value attached to the engine's rational output,
and is within `∑ w / 10000` of it. -/
theorem leafB_value_bounds_rat
    (X : (G : QuantumMaxCutEnergy.Input) → Matrix (Fin G.n) (Fin G.n) ℚ)
    (y : (G : QuantumMaxCutEnergy.Input) → Fin G.n → ℚ)
    (hXsym : ∀ G, (X G)ᵀ = X G)
    (hXtest : ∀ (G : QuantumMaxCutEnergy.Input) (x : Fin G.n → ℚ),
      0 ≤ CastBridge.qf (X G) x)
    (hXdiag : ∀ (G : QuantumMaxCutEnergy.Input) (i : Fin G.n), X G i i = 1)
    (hysym : ∀ G, (diagonal (y G) + wMatrixQ G)ᵀ = diagonal (y G) + wMatrixQ G)
    (hytest : ∀ (G : QuantumMaxCutEnergy.Input) (x : Fin G.n → ℚ),
      0 ≤ CastBridge.qf (diagonal (y G) + wMatrixQ G) x)
    (hgap : ∀ G, (∑ i, y G i) + (wMatrixQ G * X G).trace
      ≤ (∑ i, ∑ j, wMatrixQ G i j) / 5000) :
    ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue (wMatrix G) S ∧
      0 ≤ ratLowerValue (wMatrixQ G) (X G) ∧
      ((ratLowerValue (wMatrixQ G) (X G) : ℚ) : ℝ) ≤ S ∧
      S - ((ratLowerValue (wMatrixQ G) (X G) : ℚ) : ℝ)
        ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  intro G
  obtain ⟨S, hS⟩ := QMCLeafBExistence.exists_isMaxcutSDPValue (wMatrix G)
  have hS' : ModernConvex.Relaxations.IsMaxcutSDPValue
      (CastBridge.castM (wMatrixQ G)) S := by
    rw [castM_wMatrixQ]; exact hS
  obtain ⟨hnn, hlow, hup⟩ :=
    rat_sandwich_lowerValue (wMatrixQ G) (X G) (y G) S
      (fun i j => wMatrixQ_nonneg G i j) (hXsym G) (hXtest G) (hXdiag G)
      (hysym G) (hytest G) (hgap G) hS'
  refine ⟨S, hS, hnn, hlow, ?_⟩
  refine hup.trans (le_of_eq ?_)
  have hsum := sum_wMatrixQ G
  rw [hsum]
  push_cast
  ring

/-! ## 6.  The last mile: `PolyProgram` ⟹ `TM2ComputableInPolyTime` -/

/-- A `PolyProgram` computing a nonnegative rational function (in the `ℚ≥0` output type, with the
rational encoding `Ratio.encode`) yields the TM2 statement in the leaf's shape.  This is the
substrate's `nnratOutput` recipe (`QMCNumericRuntime.floorProgram`) packaged once, so that no brick
has to redo the output-adapter step. -/
theorem tm2_of_nnratPolyProgram {f : QuantumMaxCutEnergy.Input → ℚ≥0}
    (P : PolyProgram QuantumMaxCutEnergy.encodeRequest (fun q : ℚ≥0 => Ratio.encode (q : ℚ))
      (fun request : QuantumMaxCutEnergy.Input × List Bool => f request.1)) :
    Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
      QuantumMaxCutEnergy.encodeValue
      (fun request : QuantumMaxCutEnergy.Input × List Bool => f request.1)) :=
  ⟨(P.comp QMCNumericRuntime.nnratOutput).stock⟩

/-! ## 7.  `agm_classical_sdp_lower_value_tm2`, reduced to the engine's two outputs -/

/-- **The leaf theorem `d9f601e5`, modulo exactly two engine obligations.**  The conclusion is
the leaf statement verbatim (same slack `∑ w / 10000`, same inline weight matrix, same
`TM2ComputableInPolyTime` requirement).  The hypotheses are:

* `X`, `y` — the rational iterate's terminal primal point and its recorded dual average, with the
  four rational feasibility tests, the unit diagonal, and the rational gap bound
  `∑ y + tr (A X) ≤ (∑ᵢ∑ⱼ Aᵢⱼ)/5000`  —  the output of `brick-engine-iterates` /
  `brick-sep-oracle` / `brick-finalization`;
* `PL` — a `PolyProgram` computing the resulting rational lower value
  (the value, not the certificate: this is the only computational content left).

The TM2 obligation itself is discharged here by `tm2_of_polyProgram`; the numerical endgame by
`leafB_value_bounds_rat` (`rat_sandwich` + `V_wMatrix`); `IsMaxcutSDPValue` by
`exists_isMaxcutSDPValue`. -/
theorem target_of_engine
    (X : (G : QuantumMaxCutEnergy.Input) → Matrix (Fin G.n) (Fin G.n) ℚ)
    (y : (G : QuantumMaxCutEnergy.Input) → Fin G.n → ℚ)
    (PL : PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool =>
        (ratLowerValue (wMatrixQ request.1) (X request.1) : ℚ)))
    (hXsym : ∀ G, (X G)ᵀ = X G)
    (hXtest : ∀ (G : QuantumMaxCutEnergy.Input) (x : Fin G.n → ℚ),
      0 ≤ CastBridge.qf (X G) x)
    (hXdiag : ∀ (G : QuantumMaxCutEnergy.Input) (i : Fin G.n), X G i i = 1)
    (hysym : ∀ G, (diagonal (y G) + wMatrixQ G)ᵀ = diagonal (y G) + wMatrixQ G)
    (hytest : ∀ (G : QuantumMaxCutEnergy.Input) (x : Fin G.n → ℚ),
      0 ≤ CastBridge.qf (diagonal (y G) + wMatrixQ G) x)
    (hgap : ∀ G, (∑ i, y G i) + (wMatrixQ G * X G).trace
      ≤ (∑ i, ∑ j, wMatrixQ G i j) / 5000) :
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
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  have hbounds := leafB_value_bounds_rat X y hXsym hXtest hXdiag hysym hytest hgap
  let L : QuantumMaxCutEnergy.Input → ℚ≥0 :=
    fun G => ⟨ratLowerValue (wMatrixQ G) (X G), (hbounds G).choose_spec.2.1⟩
  have hL : ∀ G, (L G : ℝ) = ((ratLowerValue (wMatrixQ G) (X G) : ℚ) : ℝ) := fun G => rfl
  have hprog : Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
      QuantumMaxCutEnergy.encodeValue
      (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) := by
    refine tm2_of_nnratPolyProgram (f := L) ?_
    exact PL.recode id (fun _ => rfl) (fun _ => rfl)
  refine ⟨L, hprog, fun G => ?_⟩
  obtain ⟨S, hS, _hnn, hlow, hup⟩ := hbounds G
  exact ⟨S, hS, by rw [hL G]; exact hlow, by rw [hL G]; exact hup⟩


/-! ## 8.  Two compositions the finalization brick needs, so it does not redo them -/

/-- **The budget regime, packaged.**  `RoundingOut.exists_displayPair` asks for a budget
`∑ w g + roundCost A ν ≤ V/5000`; the QMC regime supplies it from `∑ w g ≤ V/10000` and
`ν ≤ 1/30000` (`RoundingOut.budget_closes`).  This lemma does the composition once, so
`brick-finalization` can state its obligations in the regime's own terms
(nonnegative zero-diagonal weight data, histogram budget `V/10000`, tolerance `1/30000`). -/
theorem exists_displayPair_of_regime {T : ℕ} {A X : Matrix (Fin n) (Fin n) ℚ}
    {w : Fin T → ℚ} {y : Fin T → Fin n → ℚ} {g : Fin T → ℚ} {ν : ℚ}
    (hAnonneg : ∀ i j, 0 ≤ A i j) (hAz : ∀ i, A i i = 0)
    (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 30000)
    (hAsym : Aᵀ = A) (hXsym : Xᵀ = X) (hXp : RoundingOut.RatPSD X)
    (hdiag : ∀ i, |X i i - 1| ≤ ν)
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hypTest : ∀ t x, 0 ≤ RoundingOut.qf (diagonal (y t) + A) x)
    (hbudget : ∀ t, (∑ i, y t i) + (A * X).trace ≤ g t)
    (hg : (∑ t, w t * g t) ≤ (∑ i, ∑ j, A i j) / 10000) :
    Nonempty (RoundingOut.DisplayPair A) :=
  RoundingOut.exists_displayPair hν0 hAsym hXsym hXp hdiag hw0 hw1 hypTest hbudget
    (RoundingOut.budget_closes hAnonneg hAz hν0 hν hg)

/-- **From a certified display pair to the leaf's value bound, with no further hypotheses.**  This
is the composition `DisplayPair → ratLowerValue → sandwich → ∑ w / 10000` that
`brick-finalization`/`brick-solution-assembly` would otherwise have to build: given a display pair
for the rational weight matrix of every graph, the rational lower value of its primal point is
nonnegative and sandwiched by the SDP value with the leaf's exact slack. -/
theorem value_bounds_of_displayPair
    (D : (G : QuantumMaxCutEnergy.Input) → RoundingOut.DisplayPair (wMatrixQ G)) :
    ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue (wMatrix G) S ∧
      0 ≤ ratLowerValue (wMatrixQ G) (D G).X ∧
      ((ratLowerValue (wMatrixQ G) (D G).X : ℚ) : ℝ) ≤ S ∧
      S - ((ratLowerValue (wMatrixQ G) (D G).X : ℚ) : ℝ)
        ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  refine leafB_value_bounds_rat (fun G => (D G).X) (fun G => (D G).y)
    (fun G => (D G).Xsym) (fun G x => (D G).Xtest x) (fun G i => (D G).Xdiag i)
    (fun G => (D G).ysym) (fun G x => (D G).ytest x) ?_
  intro G
  exact (D G).gap

/-- **The leaf statement from a certified display pair plus one program.**  This is the interface
`brick-finalization` (m4, accepted) delivers to — its `finalize`/`finalize_sandwich_wMatrix` produce
`RoundingOut.DisplayPair (wMatrixQ G)` from the engine's terminal report — and the only remaining
computational input is a `PolyProgram` for the rational lower value of the produced primal point.
The TM2 obligation, the `ℚ≥0` packaging and the `∑ w / 10000` slack are all discharged here. -/
theorem target_of_displayPair_program
    (D : (G : QuantumMaxCutEnergy.Input) → RoundingOut.DisplayPair (wMatrixQ G))
    (PL : PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool =>
        (ratLowerValue (wMatrixQ request.1) (D request.1).X : ℚ))) :
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
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  have hbounds := value_bounds_of_displayPair D
  let L : QuantumMaxCutEnergy.Input → ℚ≥0 :=
    fun G => ⟨ratLowerValue (wMatrixQ G) (D G).X, (hbounds G).choose_spec.2.1⟩
  have hL : ∀ G, (L G : ℝ) = ((ratLowerValue (wMatrixQ G) (D G).X : ℚ) : ℝ) := fun G => rfl
  have hprog : Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
      QuantumMaxCutEnergy.encodeValue
      (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) := by
    refine tm2_of_nnratPolyProgram (f := L) ?_
    exact PL.recode id (fun _ => rfl) (fun _ => rfl)
  refine ⟨L, hprog, fun G => ?_⟩
  obtain ⟨S, hS, _hnn, hlow, hup⟩ := hbounds G
  exact ⟨S, hS, by rw [hL G]; exact hlow, by rw [hL G]; exact hup⟩

/-- **The canonical reduction of `d9f601e5`.**  The leaf theorem is *exactly* the conjunction of
two things, and nothing else:

* a uniform per-graph value bound for a rational function `Lv : Input → ℚ≥0`
  (`(Lv G : ℝ) ≤ S` and `S - (Lv G : ℝ) ≤ ∑ w / 10000` at any `S` with `IsMaxcutSDPValue (wMatrix G) S`),
  which `QMCLeafB.ThresholdDriver.leafB_threshold_driver_wMatrix` (member m7, accepted) produces
  from thirteen engine answers, and `leafB_value_bounds_rat` produces from the display pair;
* **one** `PolyProgram` computing `Lv`, i.e. the engine's computability.

The TM2 obligation, the `ℚ≥0` packaging and the slack constant are discharged here, so this lemma is
the assembly step: whoever lands the program lands the leaf. -/
theorem target_of_value_program
    (Lv : QuantumMaxCutEnergy.Input → ℚ≥0)
    (PL : PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool => (Lv request.1 : ℚ)))
    (hb : ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue (wMatrix G) S ∧
      (Lv G : ℝ) ≤ S ∧ S - (Lv G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000) :
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
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  refine ⟨Lv, ?_, hb⟩
  refine tm2_of_nnratPolyProgram (f := Lv) ?_
  exact PL.recode id (fun _ => rfl) (fun _ => rfl)

/-! ## 9.  Axiom audit -/

#print axioms QMCLeafB.AuditM2.roundRatPSD_iff_certPSD
#print axioms QMCLeafB.AuditM2.exists_cert_of_roundRatPSD
#print axioms QMCLeafB.AuditM2.castM_wMatrixQ
#print axioms QMCLeafB.AuditM2.sum_wMatrixQ
#print axioms QMCLeafB.AuditM2.ratLowerValue_cast
#print axioms QMCLeafB.AuditM2.ratLowerValue_nonneg
#print axioms QMCLeafB.AuditM2.rat_sandwich_lowerValue
#print axioms QMCLeafB.AuditM2.leafB_value_bounds_rat
#print axioms QMCLeafB.AuditM2.tm2_of_nnratPolyProgram
#print axioms QMCLeafB.AuditM2.target_of_engine
#print axioms QMCLeafB.AuditM2.target_of_displayPair_program
#print axioms QMCLeafB.AuditM2.target_of_value_program
#print axioms QMCLeafB.AuditM2.exists_displayPair_of_regime
#print axioms QMCLeafB.AuditM2.value_bounds_of_displayPair
#print axioms QMCLeafB.IntegrationProbe.rat_sandwich
#print axioms QMCLeafB.leafB_sandwich
#print axioms QMCLeafB.RoundingOut.exists_displayPair
#print axioms QMCLeafB.RoundingOut.budget_closes
#print axioms QMCLeafB.CertPSD.premise_iff_exists_cert
#print axioms QMCLeafB.CastBridge.cast_lowerValue
#print axioms QMCLeafBExistence.exists_isMaxcutSDPValue

end QMCLeafB.AuditM2


