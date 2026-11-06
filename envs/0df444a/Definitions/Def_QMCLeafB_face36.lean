-- Prove2me | Definitions.Def_QMCLeafB_face36
-- name    : QMCLeafB_face36
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:15:38.251798+00:00
-- url     : https://prove2.me/theorems/e3271e42-337a-4bb6-bbe5-612d1bd288ce
-- title:
--   QMCLeafB face36
-- statement:
--   # `Check_face36_m2` — phase 36, member m2, direction d4 (`face-record`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thinrec34
import Definitions.Def_QMCLeafB_dreg
import Definitions.Def_QMCLeafB_bh35
/-
# `Check_face36_m2` — phase 36, member m2, direction d4 (`face-record`)

**The question.**  `hfalse` at a bit-`false` point is exactly the program-free record class
`BodyRec G t P = Nonempty (RunParts (fun _ _ => false) G t P)` (m4/ph34
`runParts_false_iff_bodyRec`), and three independent machine-checked refutations kill it on every
body with content: m1/ph35's radius-free ball/horizon theorem, m3/ph35's exact cube threshold,
m8/ph35's parallelotope.  What survives is the measure-zero face `Δ = 0` of the band, where the body
is a segment.  This file decides that face — positively — and pins the exact domain of the record
horn.

**The answer: the face is a genuine record class, and it costs no arithmetic.**

* §1–§3 **`bodyRec_of_level`, the general theorem.**  If the run's relaxation
  `relaxBall (wMatrix G) (t - Rq/40000) P.dq M` is contained in a **rational level set**
  `{z | v ⬝ z = b}` (`v : Fin (n*n) → ℚ`, `v ≠ 0`, `b : ℝ`), then the all-false record EXISTS — with
  no hypothesis on content, dimension, thinness, the horizon or the program.  Construction: the
  **adaptive** normal `c_k = +v` if `v ⬝ Cat k ≤ b`, else `-v`.  Since `v ⬝ z = b` on the whole
  relaxation, both are supporting normals there, so `hcut` holds at EVERY round with `del ≡ 0`;
  `hcheck` is then `0 ≤ ρ²σ_k` and `σ_k = c_k ⬝ A_k⁻¹ c_k > 0` because every iterate is `PosQ`, so
  the depth ledger never enters.  The sign must be read off the *current* centre, so
  `runCut`/`NormalCut` cannot be used (their normal stream is fixed before the centre is known): §2
  carries the joint recursion `faceSt : ℕ → {A // castM A PosDef} × centre` (positivity threaded by
  `stepShape_posDef`) and identifies it with the engine's own `Aat`/`Cat` by structural induction —
  the record IS the run, with no re-presentation of the centre.

* §4 **the face at the campaign's exemplar.**  At `(G₁, tStar)` the level `u + dq/2` is exactly the
  objective floor `-(2 + 3dq/2)`, so every point of the REAL relaxed body (`relaxBodyLE`, which is
  what `hcut` quantifies over) has `X₀₁ + X₁₀ = -(2 + 3dq/2)` and `X₀₀ + X₁₁ = 2 + dq/2` with
  `Xᵢᵢ ≤ 1 + dq/4`: the body is exactly the segment `{Xᵢᵢ = 1 + dq/4, X₀₁ + X₁₀ = -(2 + 3dq/2)}`
  (m5/ph35's `diag_eq_top_zero` over `ℚ`, here over `ℝ`).  Hence `BodyRec G₁ tStar P` for ANY
  `RunParams` with `dq = 1/380000` (`bodyRec_face`), in particular for `P₁ = paramsKbc2 G₁`.

* **What this gives the assembler.**  `face_runParts`: at the face, `RunParts o G₁ tStar P` exists for
  EVERY bit `o` that reads `false` there — the leaf's `hfalse` slot is discharged at the face with no
  program hypothesis, no `ReachTop` and no arithmetic.  `face_summary` records the three facts the
  assembler needs at once (the point is inside the leaf's bracket, the body is NONEMPTY, and the
  record exists).  `bodyRec_domain` states the general domain: `{relaxation ⊆ a rational level set}`.

* §5 **the face is closed from BOTH sides.**  For the released/pinched gate the bit AT the face is
  `false` (m5/ph35 `dreg_pinched_ok_false`), so the leaf's `hfalse` is owed there and §4 supplies it
  (`face_pinched_ok_false`).  With the repaired membership-equivalent gate the face is inhabited by a
  rational member with a constant reaching orbit (`face_topGate`, `face_reachTop`), so the bit may
  read `true` there and the upper side supplies the same slot.  Either way the face needs no
  `ReachTop` and no program edit; it is the one point class where the leaf's residual is EMPTY.

* **Consistency with the three refutations.**  `face_no_ball` proves that the face's relaxation
  contains NO ball of positive radius, so m1/ph35's `not_shallowCut_of_ball_horizon` hypothesis is
  unsatisfiable there (and a segment carries no cube/parallelotope either).  Off the face the level
  rises by `Δ` and the body acquires width, so the three refutations apply and the record horn is
  dead there: the *only* remaining lanes off the face are the certified-gate repair + visit
  completeness (the bit horn).

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
no `Automatic.Poly` content here; axioms audited at the end of the file.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Face36M2

open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates

abbrev falseBit : QuantumMaxCutEnergy.Input → ℚ → Bool := fun _ _ => false

/-- The all-false record class at `(G,t)`. -/
def BodyRec (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  Nonempty (QMCLeafB.FinalStroke.RunParts falseBit G t P)

/-- The relaxation the record's `hcut` quantifies over, at `P`'s tolerance. -/
def relaxBallP (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Set (Fin (G.n * G.n) → ℝ) :=
  QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
    ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ)
    (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ)

theorem two_le_mul_self {n : ℕ} (hn : 2 ≤ n) : 2 ≤ n * n := by
  have h := Nat.mul_le_mul hn hn
  omega

/-! ## 1.  The adaptive normal: `±v` across a rational level -/

/-- The real cast of a rational direction. -/
def vR {N : ℕ} (v : Fin N → ℚ) : Fin N → ℝ := fun i => ((v i : ℚ) : ℝ)

theorem vR_neg {N : ℕ} (v : Fin N → ℚ) : vR (-v) = -vR v := by
  funext i
  simp [vR]

theorem vR_ne_zero {N : ℕ} {v : Fin N → ℚ} (hv : v ≠ 0) : vR v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi : ((v i : ℚ) : ℝ) = 0 := by
    have h' := congrFun h i
    simpa [vR] using h'
  exact_mod_cast hi

/-- The adaptive choice: cut with `+v` from the low side of the level `b`, with `-v` otherwise.
Both are supporting normals whenever the whole relaxation has `v`-value exactly `b`. -/
def pickN {N : ℕ} (v : Fin N → ℚ) (b : ℝ) (a : Fin N → ℝ) : Fin N → ℚ := by
  classical
  exact if vR v ⬝ᵥ a ≤ b then v else -v

theorem pickN_ne_zero {N : ℕ} {v : Fin N → ℚ} (hv : v ≠ 0) (b : ℝ) (a : Fin N → ℝ) :
    pickN v b a ≠ 0 := by
  unfold pickN
  split_ifs with h
  · exact hv
  · exact neg_ne_zero.mpr hv

/-- **The supporting inequality of the adaptive choice.** -/
theorem pickN_spec {N : ℕ} {v : Fin N → ℚ} {b : ℝ} {a z : Fin N → ℝ}
    (hz : vR v ⬝ᵥ z = b) :
    vR (pickN v b a) ⬝ᵥ a ≤ vR (pickN v b a) ⬝ᵥ z := by
  unfold pickN
  split_ifs with h
  · rw [hz]
    exact h
  · have hlt : b < vR v ⬝ᵥ a := not_le.mp h
    have h1 : vR (-v) ⬝ᵥ a = -(vR v ⬝ᵥ a) := by
      rw [vR_neg, neg_dotProduct]
    have h2 : vR (-v) ⬝ᵥ z = -(vR v ⬝ᵥ z) := by
      rw [vR_neg, neg_dotProduct]
    rw [h1, h2, hz]
    linarith

/-! ## 2.  The engine chain at the adaptive stream -/

/-- The joint recursion: shape and centre, the normal chosen from the current centre. -/
noncomputable def faceSt (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ) :
    ℕ → { A : Matrix (Fin (G.n * G.n)) (Fin (G.n * G.n)) ℚ //
          (QMCLeafB.EngineIterates.castM A).PosDef } × (Fin (G.n * G.n) → ℝ)
  | 0 => (⟨QMCLeafB.RunPartsDilate.A0P G P, QMCLeafB.RunPartsDilate.A0P_posDef G P⟩,
          fun _ => 0)
  | (k + 1) =>
      let prev := faceSt G P hn v hv b k
      let c := pickN v b prev.2
      let p := QMCLeafB.RunPartsShallow.witOf
        (QMCLeafB.EngineIterates.posQ_of_cast prev.1.2) c
      (⟨QMCLeafB.EngineIterates.rStep (G.n * G.n) prev.1.1 c p P.rmax, by
          rw [QMCLeafB.EngineIterates.rStep_cast]
          refine QMCLeafB.EngineIterates.stepShape_posDef (two_le_mul_self hn) prev.1.2 ?_ ?_ ?_
          · exact vR_ne_zero (pickN_ne_zero hv b prev.2)
          · rw [QMCLeafB.EngineIterates.cast_mulVec,
              QMCLeafB.RunPartsShallow.witOf_spec]
          · exact_mod_cast P.hrmax⟩,
        QMCLeafB.EngineIterates.stepCentre (G.n * G.n) prev.2 (vR c) (vR p)
          ((P.rmax : ℚ) : ℝ))

/-- The recorded cut stream of the adaptive normals. -/
noncomputable def faceCd (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ) :
    ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
  fun k =>
    let prev := faceSt G P hn v hv b k
    let c := pickN v b prev.2
    ⟨c, QMCLeafB.RunPartsShallow.witOf
        (QMCLeafB.EngineIterates.posQ_of_cast prev.1.2) c, P.rmax⟩

theorem Aat_faceCd (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ) (k : ℕ) :
    QMCLeafB.EngineIterates.Aat (G.n * G.n) (QMCLeafB.RunPartsDilate.A0P G P)
        (faceCd G P hn v hv b) k
      = (faceSt G P hn v hv b k).1.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [QMCLeafB.EngineIterates.Aat_unfold, ih]
      rfl

theorem Cat_faceCd (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ) (k : ℕ) :
    QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
        (faceCd G P hn v hv b) k
      = (faceSt G P hn v hv b k).2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [QMCLeafB.EngineIterates.Cat_unfold, ih]
      rfl

theorem face_hwit (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ) (k : ℕ) :
    QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) (faceCd G P hn v hv b) k
        *ᵥ ((faceCd G P hn v hv b k).p)
      = (faceCd G P hn v hv b k).c := by
  have h1 := Aat_faceCd G P hn v hv b k
  have h2 : QMCLeafB.RunPartsDilate.A0P G P
      = QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2) := rfl
  rw [← h2, h1]
  exact QMCLeafB.RunPartsShallow.witOf_spec
    (QMCLeafB.EngineIterates.posQ_of_cast (faceSt G P hn v hv b k).1.2)
    (pickN v b (faceSt G P hn v hv b k).2)

theorem face_sigma_pos (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ) (k : ℕ) :
    0 < QMCLeafB.EngineIterates.sigmaQ (faceCd G P hn v hv b k).c
      (faceCd G P hn v hv b k).p := by
  have hposq : QMCLeafB.EngineIterates.PosQ
      (faceSt G P hn v hv b k).1.1 :=
    QMCLeafB.EngineIterates.posQ_of_cast (faceSt G P hn v hv b k).1.2
  have hA : (faceSt G P hn v hv b k).1.1 *ᵥ (faceCd G P hn v hv b k).p
      = (faceCd G P hn v hv b k).c :=
    QMCLeafB.RunPartsShallow.witOf_spec hposq _
  have hne : (faceCd G P hn v hv b k).c ≠ 0 :=
    pickN_ne_zero hv b (faceSt G P hn v hv b k).2
  have hpne : (faceCd G P hn v hv b k).p ≠ 0 := by
    intro hp
    apply hne
    rw [← hA, hp, Matrix.mulVec_zero]
  have hq : QMCLeafB.EngineIterates.qf (faceSt G P hn v hv b k).1.1
        (faceCd G P hn v hv b k).p
      = QMCLeafB.EngineIterates.sigmaQ (faceCd G P hn v hv b k).c
          (faceCd G P hn v hv b k).p := by
    show (faceCd G P hn v hv b k).p
        ⬝ᵥ ((faceSt G P hn v hv b k).1.1 *ᵥ (faceCd G P hn v hv b k).p)
      = (faceCd G P hn v hv b k).c ⬝ᵥ (faceCd G P hn v hv b k).p
    rw [hA, dotProduct_comm]
  rw [← hq]
  exact hposq.2 _ hpne

theorem face_hcut (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ) (t : ℚ)
    (hface : ∀ z ∈ relaxBallP G t P, vR v ⬝ᵥ z = b) (k : ℕ) :
    ∀ z, z ∈ relaxBallP G t P →
      0 ≤ QMCLeafB.EngineIterates.cutCR (faceCd G P hn v hv b) k
            ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
                  (0 : Fin (G.n * G.n) → ℝ) (faceCd G P hn v hv b) k) := by
  intro z hz
  have hspec := pickN_spec (v := v) (b := b)
    (a := (faceSt G P hn v hv b k).2) (z := z) (hface z hz)
  rw [Cat_faceCd, dotProduct_sub]
  show 0 ≤ vR (pickN v b (faceSt G P hn v hv b k).2) ⬝ᵥ z
    - vR (pickN v b (faceSt G P hn v hv b k).2) ⬝ᵥ (faceSt G P hn v hv b k).2
  linarith

/-- **THE FACE RECORD.**  If the whole relaxation lies in a rational level set
`{z | v ⬝ z = b}` with `v ≠ 0`, the all-false record exists. -/
theorem bodyRec_of_level {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ)
    (hface : ∀ z ∈ relaxBallP G t P, vR v ⬝ᵥ z = b) :
    BodyRec G t P := by
  have hbc : ∀ T : ℕ, QMCLeafB.SimLoop.anyOk (fun _ : ℕ => false) T = false := by
    intro T
    induction T with
    | zero => rfl
    | succ T ih => rw [QMCLeafB.SimLoop.anyOk_succ, ih]; rfl
  refine ⟨{ ok := fun _ => false
            cd := faceCd G P hn v hv b
            del := fun _ => 0
            hcert := ?_
            hwit := ?_
            hrho := ?_
            hcne := ?_
            hdel0 := ?_
            hcheck := ?_
            hle := ?_
            hcut := ?_
            hverdict := ?_ }⟩
  · intro k _ hok
    exact absurd hok (by simp)
  · intro k _ _
    exact face_hwit G P hn v hv b k
  · intro k _ _
    show (0 : ℚ) ≤ P.rmax
    exact P.hrmax
  · intro k _ _
    exact pickN_ne_zero hv b (faceSt G P hn v hv b k).2
  · intro k _ _
    exact le_refl 0
  · intro k _ _
    have hσ := (face_sigma_pos G P hn v hv b k).le
    have h1 : (0 : ℚ) ≤ P.rmax ^ 2 := sq_nonneg _
    have h2 : (0 : ℚ) ≤ P.rmax ^ 2 * QMCLeafB.EngineIterates.sigmaQ
        (faceCd G P hn v hv b k).c (faceCd G P hn v hv b k).p := mul_nonneg h1 hσ
    have hrho : (faceCd G P hn v hv b k).rho = P.rmax := rfl
    rw [hrho]
    simpa using h2
  · intro k _ _
    show P.rmax ≤ P.rmax
    exact le_refl _
  · intro k _ _ z hz
    have h := face_hcut (t := t) G P hn v hv b hface k z hz
    simpa using h
  · show falseBit G t = QMCLeafB.SimLoop.anyOk (fun _ => false) (P.K * P.m)
    exact (hbc (P.K * P.m)).symm


/-! ## 4.  The measure-zero face of the band, at the campaign's own exemplar

At `G₁` and threshold `tStar` the level `u + dq/2` is exactly the objective floor
`−(2 + 3dq/2)`, so the relaxed body collapses onto the segment
`{X₀₀ = X₁₁ = 1 + dq/4, X₀₁ + X₁₀ = −(2 + 3dq/2)}`: it is contained in the rational level set
`{X₀₀ = 1 + dq/4}`.  §3 then produces the record with zero margins. -/

open QMCLeafB.DregM6 in
/-- The objective pairing at the exemplar, in entries. -/
theorem frob_G1 (X : Matrix (Fin 2) (Fin 2) ℝ) :
    QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) X = X 0 1 + X 1 0 := by
  simp only [QMCLeafB.BallFloor.frob, Fin.sum_univ_two,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_00, QMCLeafB.AnchorFactsM2.wMatrix_G₁_01,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_10, QMCLeafB.AnchorFactsM2.wMatrix_G₁_11]
  ring

/-- **The face is pinned.**  Whenever the level is at the objective floor `−(2 + 2d)`, every
relaxed body point has its `(0,0)` diagonal exactly at the top edge `1 + d/4`. -/
theorem face_mem_G1 {X : Matrix (Fin 2) (Fin 2) ℝ} {u d : ℝ}
    (hu : u = -(2 + 2 * d))
    (hX : QMCLeafB.BallFloor.relaxBodyLE
      (QMCLeafB.wMatrix QMCLeafB.DregM6.G₁) u d X) :
    X 0 0 = 1 + d / 4 := by
  have hX' := hX
  obtain ⟨hpsd, hdiag, htr⟩ := hX'
  have hqf := hpsd (fun _ : Fin 2 => (1 : ℝ))
  have hsq : (∑ i : Fin 2, ((1 : ℝ)) ^ 2) = 2 := by norm_num
  have hqf' : QMCLeafB.BallFloor.qfR X (fun _ : Fin 2 => (1 : ℝ))
      = X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
    rw [QMCLeafB.BallFloor.qfR_eq_sum]
    simp only [Fin.sum_univ_two]
    ring
  rw [hsq, hqf'] at hqf
  have hfloor := QMCLeafB.DregM6.frob_floor
    (u := u) (d := d) hX
  rw [frob_G1] at hfloor htr
  have hd0 := (abs_le.mp (hdiag 0)).2
  have hd1 := (abs_le.mp (hdiag 1)).2
  rw [hu] at htr
  have e0 : X 0 0 = 1 + d / 4 := by linarith
  exact e0

/-- The rational normal picking out the `(0,0)` flat coordinate. -/
def e00 : Fin (2 * 2) → ℚ := fun k => if k = finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)) then 1 else 0

theorem e00_ne : e00 ≠ 0 := by
  intro h
  have h' := congrFun h (finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)))
  simp [e00] at h'

theorem dot_e00 (z : Fin (2 * 2) → ℝ) :
    vR e00 ⬝ᵥ z = QMCLeafB.Boundary.unflat z 0 0 := by
  show vR e00 ⬝ᵥ z = z (finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)))
  rw [dotProduct, Finset.sum_eq_single (finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)))]
  · simp [vR, e00]
  · intro b _ hb
    have h1 : e00 b = 0 := by
      simp only [e00]
      rw [if_neg hb]
    simp [vR, h1]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- **The face's level identity** at ANY `RunParams` with the campaign's tolerance. -/
theorem face_level_G1 (P : QMCLeafB.FinalStroke.RunParams QMCLeafB.DregM6.G₁)
    (hPdq : P.dq = 1 / 380000)
    (z : Fin (QMCLeafB.DregM6.G₁.n * QMCLeafB.DregM6.G₁.n) → ℝ)
    (hz : z ∈ relaxBallP QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar P) :
    vR e00 ⬝ᵥ z = 1 + (1 / 380000 : ℝ) / 4 := by
  have hd : ((P.dq : ℚ) : ℝ) = 1 / 380000 := by rw [hPdq]; norm_num
  have hu : ((QMCLeafB.DregM6.tStar : ℚ) : ℝ)
      - (((QMCLeafB.EngineRuntime.Rq QMCLeafB.DregM6.G₁ / 40000 : ℚ)) : ℝ)
      = -(2 + 2 * (1 / 380000 : ℝ)) := by
    have h := QMCLeafB.DregM6.thresh_eq 0
    simpa using h
  have hbody := hz.1
  rw [hu, hd] at hbody
  have h00 := face_mem_G1 (u := -(2 + 2 * (1 / 380000 : ℝ)))
    (d := 1 / 380000) rfl hbody
  rw [dot_e00, h00]

/-- **THE FACE RECORD at the campaign's exemplar**, at any parameter set of the campaign's
tolerance. -/
theorem bodyRec_face (P : QMCLeafB.FinalStroke.RunParams QMCLeafB.DregM6.G₁)
    (hPdq : P.dq = 1 / 380000) :
    BodyRec QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar P :=
  bodyRec_of_level (hn := by norm_num [QMCLeafB.DregM6.G₁])
    e00 e00_ne (1 + (1 / 380000 : ℝ) / 4) (face_level_G1 P hPdq)

/-- The face record at the campaign's own parameter family `P₁ = paramsKbc2 G₁`. -/
theorem bodyRec_face_G1 :
    BodyRec QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar QMCLeafB.DregM6.P₁ :=
  bodyRec_face _ QMCLeafB.DregM6.dq_eq

/-- **The face point is inside the leaf's own interior bracket** — so the record is owed exactly
where the leaf's `hfalse` is read. -/
theorem face_interior :
    (-(QMCLeafB.EngineRuntime.Rq QMCLeafB.DregM6.G₁) : ℚ) ≤ QMCLeafB.DregM6.tStar
      ∧ QMCLeafB.DregM6.tStar < -(QMCLeafB.EngineRuntime.Rq QMCLeafB.DregM6.G₁) / 40000 := by
  constructor
  · rw [QMCLeafB.DregM6.Rq_eq]
    unfold QMCLeafB.DregM6.tStar
    norm_num
  · rw [QMCLeafB.DregM6.Rq_eq]
    unfold QMCLeafB.DregM6.tStar
    norm_num

/-- **What the face record gives the assembler.**  At the face the leaf's `hfalse` slot is
discharged for EVERY bit that reads `false` there: the record is program-free
(`runParts_false_iff_bodyRec`). -/
theorem face_runParts (P : QMCLeafB.FinalStroke.RunParams QMCLeafB.DregM6.G₁)
    (hPdq : P.dq = 1 / 380000)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (h : o QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar = false) :
    Nonempty (QMCLeafB.FinalStroke.RunParts o QMCLeafB.DregM6.G₁
      QMCLeafB.DregM6.tStar P) :=
  (QMCLeafB.ThinRec34M4.runParts_false_iff_bodyRec h).2 (bodyRec_face P hPdq)

/-- **The face record in `hfalse`'s own shape**: the `RunParts` value, not just its existence. -/
noncomputable def hfalse_at_face (P : QMCLeafB.FinalStroke.RunParams QMCLeafB.DregM6.G₁)
    (hPdq : P.dq = 1 / 380000)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (h : o QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar = false) :
    QMCLeafB.FinalStroke.RunParts o QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar P :=
  Classical.choice (face_runParts P hPdq o h)

/-! ### 5.  The face is closed from both sides

The record of §4 is not an optional extra: for the released/pinched-gate programme the bit AT the
face is `false` (m5/ph35 `dreg_pinched_ok_false`, itself the composite of `pinchMem_of_releasedGate`
and `dreg_no_pinchMem`), so the leaf's `hfalse` slot is owed there and the record supplies it.  With
the repaired, membership-equivalent gate the face can equally well read `true` — a rational member
exists and a constant orbit reaches it (`dreg_topGate_inhabited`, `dreg_reachTop_const`) — and then
`hok` supplies the other side.  Either way the face needs no `ReachTop` and no program edit. -/

/-- **At the face a pinched-sound `ok` register reads `false` at every round.** -/
theorem face_pinched_ok_false {flag : ℕ → Bool}
    (hsound : ∀ k, flag k = true →
      QMCLeafB.BH35M5.PinchMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁)
        ((QMCLeafB.DregM6.tStar + 0) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
        QMCLeafB.DregM6.P₁.dq) (T : ℕ) :
    QMCLeafB.SimLoop.anyOk flag T = false := by
  have h0 : (0 : ℚ) < QMCLeafB.BH35M5.d0 := by norm_num [QMCLeafB.BH35M5.d0]
  have h := QMCLeafB.BH35M5.dreg_pinched_ok_false (Δ := 0) h0 hsound T
  simpa using h

/-- **The repaired, membership-equivalent gate is inhabited at the face.** -/
theorem face_topGate :
    QMCLeafB.BH35M5.TopGate (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁)
      ((QMCLeafB.DregM6.tStar + 0) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq (QMCLeafB.BH35M5.XQ 0) := by
  have h := QMCLeafB.BH35M5.dreg_topGate_inhabited (Δ := 0) (by norm_num) (by norm_num)
  simpa using h

/-- **A constant orbit reaches it** — so at the face the repaired programme reads `true` at every
horizon `T > 0`, with no landing theorem. -/
theorem face_reachTop {T : ℕ} (hT : 0 < T) :
    QMCLeafB.BH35M5.ReachTop (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁)
      ((QMCLeafB.DregM6.tStar + 0) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq (fun _ => QMCLeafB.BH35M5.XQ 0) T := by
  have h := QMCLeafB.BH35M5.dreg_reachTop_const (Δ := 0) (by norm_num) (by norm_num) hT
  simpa using h

/-- **And where the face record is available at all**: exactly when the relaxation is contained in
a rational level set.  Off the face the level rises and the body acquires width — the three banked
refutations (`not_shallowCut_of_ball_horizon`, the cube threshold, the parallelotope) then deny the
record, so this is the whole domain of the record horn that survives at the campaign's own numbers. -/
theorem bodyRec_domain {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ)
    (hface : ∀ z ∈ relaxBallP G t P, vR v ⬝ᵥ z = b) :
    BodyRec G t P :=
  bodyRec_of_level hn v hv b hface

/-- The two banked emptiness predicates agree definitionally. -/
theorem bodyEmpty_iff {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} :
    QMCLeafB.ThriceM3.BodyEmpty G t P ↔ QMCLeafB.ThinRec34M4.BodyEmpty G t P := Iff.rfl

/-- **The face's body is NONEMPTY** — so the record there is not free through the empty-body route
(`RefutedM3.runParts_of_emptyBody`); the face is a genuine nonempty-thin record. -/
theorem face_body_nonempty :
    ¬ QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar QMCLeafB.DregM6.P₁ := by
  have h := QMCLeafB.DregM6.not_bodyEmpty (0 : ℚ) (by norm_num) (by norm_num)
  have h0 : QMCLeafB.DregM6.tStar + (0 : ℚ) = QMCLeafB.DregM6.tStar := by ring
  rwa [h0] at h

/-- **THE FACE, IN ONE STATEMENT.**  The face point is inside the leaf's interior bracket, its
relaxed body is nonempty, and the all-false record exists there — so the leaf's `hfalse` at the face
is discharged with no program hypothesis, no reach theorem and no arithmetic. -/
theorem face_summary :
    (-(QMCLeafB.EngineRuntime.Rq QMCLeafB.DregM6.G₁) : ℚ) ≤ QMCLeafB.DregM6.tStar
      ∧ QMCLeafB.DregM6.tStar < -(QMCLeafB.EngineRuntime.Rq QMCLeafB.DregM6.G₁) / 40000
      ∧ ¬ QMCLeafB.ThinRec34M4.BodyEmpty QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar
          QMCLeafB.DregM6.P₁
      ∧ BodyRec QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar QMCLeafB.DregM6.P₁ :=
  ⟨face_interior.1, face_interior.2, (bodyEmpty_iff.not).mpr face_body_nonempty, bodyRec_face_G1⟩

/-- **No ball fits in the face's relaxation.**  m1/ph35's radius-free theorem
(`not_shallowCut_of_ball_horizon`) needs `eucBallF u r ⊆ relaxBall` with `r > 0`; at the face that
hypothesis is UNSATISFIABLE, which is exactly why the record survives: the relaxation is contained
in the hyperplane `{X₀₀ = 1 + dq/4}`, so no ball of positive radius can sit inside it. -/
theorem face_no_ball :
    ¬ ∃ (u : Fin (QMCLeafB.DregM6.G₁.n * QMCLeafB.DregM6.G₁.n) → ℝ) (r : ℝ), 0 < r ∧
        QMCLeafB.Boundary.eucBallF u r ⊆
          relaxBallP QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar QMCLeafB.DregM6.P₁ := by
  rintro ⟨u, r, hr, hsub⟩
  have hb := face_level_G1 QMCLeafB.DregM6.P₁ QMCLeafB.DregM6.dq_eq
  have hmem : u ∈ relaxBallP QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar QMCLeafB.DregM6.P₁ := by
    refine hsub ?_
    show (∑ i, (u i - u i) ^ 2) ≤ r ^ 2
    simpa using (sq_nonneg r)
  have huu := hb u hmem
  set e : Fin (QMCLeafB.DregM6.G₁.n * QMCLeafB.DregM6.G₁.n) :=
    finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)) with he
  set z : Fin (QMCLeafB.DregM6.G₁.n * QMCLeafB.DregM6.G₁.n) → ℝ :=
    fun i => if i = e then u e + r / 2 else u i with hz
  have hze : z e = u e + r / 2 := by
    rw [hz]; simp
  have hzball : z ∈ QMCLeafB.Boundary.eucBallF u r := by
    show (∑ i, (z i - u i) ^ 2) ≤ r ^ 2
    rw [Finset.sum_eq_single e]
    · rw [hze]; nlinarith
    · intro b _ hbne
      have hb' : z b = u b := by rw [hz]; simp [hbne]
      rw [hb', sub_self]; ring
    · intro hcon
      exact absurd (Finset.mem_univ e) hcon
  have hzz := hb z (hsub hzball)
  rw [dot_e00] at huu hzz
  have hze' : QMCLeafB.Boundary.unflat z 0 0 = z e := rfl
  have hue : QMCLeafB.Boundary.unflat u 0 0 = u e := rfl
  rw [hze', hze] at hzz
  rw [hue] at huu
  linarith

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.Face36M2.two_le_mul_self
#print axioms QMCLeafB.Face36M2.vR_neg
#print axioms QMCLeafB.Face36M2.vR_ne_zero
#print axioms QMCLeafB.Face36M2.pickN_ne_zero
#print axioms QMCLeafB.Face36M2.pickN_spec
#print axioms QMCLeafB.Face36M2.Aat_faceCd
#print axioms QMCLeafB.Face36M2.Cat_faceCd
#print axioms QMCLeafB.Face36M2.face_hwit
#print axioms QMCLeafB.Face36M2.face_sigma_pos
#print axioms QMCLeafB.Face36M2.face_hcut
#print axioms QMCLeafB.Face36M2.bodyRec_of_level
#print axioms QMCLeafB.Face36M2.frob_G1
#print axioms QMCLeafB.Face36M2.face_mem_G1
#print axioms QMCLeafB.Face36M2.e00_ne
#print axioms QMCLeafB.Face36M2.dot_e00
#print axioms QMCLeafB.Face36M2.face_level_G1
#print axioms QMCLeafB.Face36M2.bodyRec_face
#print axioms QMCLeafB.Face36M2.bodyRec_face_G1
#print axioms QMCLeafB.Face36M2.face_interior
#print axioms QMCLeafB.Face36M2.face_runParts
#print axioms QMCLeafB.Face36M2.hfalse_at_face
#print axioms QMCLeafB.Face36M2.bodyRec_domain
#print axioms QMCLeafB.Face36M2.bodyEmpty_iff
#print axioms QMCLeafB.Face36M2.face_body_nonempty
#print axioms QMCLeafB.Face36M2.face_summary
#print axioms QMCLeafB.Face36M2.face_no_ball
#print axioms QMCLeafB.Face36M2.face_pinched_ok_false
#print axioms QMCLeafB.Face36M2.face_topGate
#print axioms QMCLeafB.Face36M2.face_reachTop

end QMCLeafB.Face36M2


