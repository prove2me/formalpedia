-- Prove2me | Definitions.Def_QMCLeafB_gq38
-- name    : QMCLeafB_gq38
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:36:47.698026+00:00
-- url     : https://prove2.me/theorems/6782f36d-4a70-4c06-bd82-065e1de040a9
-- title:
--   QMCLeafB gq38
-- statement:
--   # `Check_gq38_m7` — phase 38, member m7, direction `gap-quantitative`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_face36
import Definitions.Def_QMCLeafB_sc35
import Definitions.Def_QMCLeafB_cov36
/-
# `Check_gq38_m7` — phase 38, member m7, direction `gap-quantitative`

**The obligation.**  `SelfRec` / `ShallowCut` at the collar is ONE inequality per round: the
accumulated centre `Cat k` must be within `rmax·√σ_k` of the body in the `c_k` direction.  The
campaign's reading after phases 36/37 is that the record horn is DEAD off the face `Δ = 0` and that
the only remaining lane is the bit horn.  This file decides the quantitative question that reading
turns on — and answers it NEGATIVELY for the reading, POSITIVELY for the record.

## The answer

* **§1–§2 `bodyRec_of_slab`: the record class is a SLAB class, not a face class.**  m2/ph36's
  `bodyRec_of_level` needs the relaxation in a rational LEVEL set (`v ⬝ z = b`), which kills the
  margin (`del ≡ 0`).  The same adaptive construction works on a SLAB of half-width `h`: with the
  normal `±v` read off the current centre, the cut margin is `h` at EVERY round, because the sign
  that puts the centre on the right side of `b` always exists.  The record's only remaining cost is
  the LEDGER `h² ≤ rmax²·σ_k`, and the banked σ-floor (`Sc35M7.sigma_ge`:
  `σ_k ≥ M₀·((n+ρ)/(n+1))^{2k}` along ANY stream at fixed depth `ρ`) turns that into ONE explicit
  arithmetic condition:

      h²  ≤  rmax² · M₀ · ((n + rmax)/(n + 1))^{2·(K·m − 1)}.

  A horizon-thin body therefore carries a record — with no appeal to the bit, to content, to balls
  or to a landing theorem.

* **§3 the collar instantiation.**  At `(G₁, tStar + Δ)` the relaxed body obeys
  `X₀₀ ∈ [1 + δ/4 − Δ, 1 + δ/4]` (the frob ceiling rises by exactly `Δ`; the peak identity
  `X₀₀ + X₁₁ = 2 + δ/2` becomes `≥ 2 + δ/2 − Δ`), i.e. it is a SLAB of half-width `Δ/2`.  §2 then
  gives `BodyRec G₁ (tStar + Δ) P₁` for `Δ = (1/2)^{P₁.K·P₁.m}`, hence at a point which is in the
  leaf's interior bracket, off the face, with a NONEMPTY body, and where every banked content
  obstruction (m1's ball/horizon, m3's cube, m8's parallelotope) is silent.  **So the record horn is
  ALIVE on the collar**: the phase-36/37 "record dead off the face" reading is false as stated.

* **§4 the ONE-ROUND CRITERION, obstruction half** (`deep_core_blocks`, machine-checked): if the
  closed `r`-ball of the shape metric about the centre lies in the body and `ρ < r`, then EVERY
  normal is beaten, strictly, by a body point.  So a round's obstruction is exactly the
  bounded-distance condition "the centre is `ρ`-deep in the body", and the shallow ledger is a
  statement about the centre's POSITION, not about depths or presentations.
  (`not_bodyRec_of_core_zero` is the engine-level consequence, and it needs NO horizon: a body that
  contains the `rmax`-ball about the ORIGIN admits no record at all, because round zero's centre is
  the origin.)

## What is not settled

* the DUAL of §4 (the existence half: `ρ`-ball not in the body ⟹ some strictly separating normal) —
  it is the Hahn–Banach/Cauchy–Schwarz direction and is not formalised here, though the argument is
  three lines;
* the intermediate collar: slab half-width `h` above the horizon threshold but below every content
  obstruction.  The threshold is explicit (`h² ≤ rmax²·M₀·δ'^{2(K·m−1)}`), so that window is now a
  numerical question, not a qualitative one.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
every `#print axioms` is exactly `[propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Gq38M7

open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates
open QMCLeafB.Face36M2

theorem two_le_mul_self {n : ℕ} (hn : 2 ≤ n) : 2 ≤ n * n := by
  have h := Nat.mul_le_mul hn hn
  omega

/-! ## 0.  A rational unit direction and its cast -/

theorem vR_dot {N : ℕ} (v w : Fin N → ℚ) :
    vR v ⬝ᵥ vR w = (((v ⬝ᵥ w : ℚ)) : ℝ) := by
  simp only [vR, dotProduct, Rat.cast_sum, Rat.cast_mul]

theorem vR_dot_self {N : ℕ} {v : Fin N → ℚ} (hunit : v ⬝ᵥ v = 1) :
    vR v ⬝ᵥ vR v = 1 := by
  rw [vR_dot, hunit]
  norm_num

theorem neg_vR_dot_self {N : ℕ} {v : Fin N → ℚ} (hunit : v ⬝ᵥ v = 1) :
    vR (-v) ⬝ᵥ vR (-v) = 1 := by
  rw [vR_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  exact vR_dot_self hunit

/-! ## 1.  The adaptive normal on a SLAB: the margin is the half-width -/

/-- **The supporting inequality on a slab.**  If the whole body lies in `[b − h, b + h]` in the
`v`-direction, the adaptive normal `pickN v b a` satisfies the `hcut` inequality with margin `h`,
for every centre `a`. -/
theorem pickN_spec_slab {N : ℕ} {v : Fin N → ℚ} {b h : ℝ} {a z : Fin N → ℝ}
    (hlo : b - h ≤ vR v ⬝ᵥ z) (hhi : vR v ⬝ᵥ z ≤ b + h) :
    vR (pickN v b a) ⬝ᵥ a - vR (pickN v b a) ⬝ᵥ z ≤ h := by
  unfold pickN
  split_ifs with hle
  · have : vR v ⬝ᵥ a - vR v ⬝ᵥ z ≤ b - (b - h) := by linarith
    linarith
  · have h1 : vR (-v) ⬝ᵥ a = -(vR v ⬝ᵥ a) := by
      rw [vR_neg, neg_dotProduct]
    have h2 : vR (-v) ⬝ᵥ z = -(vR v ⬝ᵥ z) := by
      rw [vR_neg, neg_dotProduct]
    rw [h1, h2]
    linarith

#print axioms QMCLeafB.Gq38M7.pickN_spec_slab

/-! ## 2.  THE SLAB RECORD

The construction is m2/ph36's adaptive chain (`faceSt`/`faceCd`) verbatim; the changes are the
margin `del ≡ hq` (instead of `0`) and the ledger, discharged by the banked σ-floor
`Sc35M7.sigma_ge`. -/

/-- **The σ-floor along the adaptive chain**, in the exact form the ledger consumes. -/
theorem slab_sigma_floor {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (hunit : v ⬝ᵥ v = 1) (b : ℝ) (k : ℕ) :
    ((QMCLeafB.RundataArith.capOf G P.dq : ℚ) : ℝ)
        * (((((G.n * G.n : ℕ) : ℝ) + ((P.rmax : ℚ) : ℝ)) / (((G.n * G.n : ℕ) : ℝ) + 1))
            ^ (2 * k))
      ≤ QMCLeafB.EngineIterates.sigmaR
          (QMCLeafB.EngineIterates.cutCR (faceCd G P hn v hv b) k)
          (QMCLeafB.EngineIterates.cutPR (faceCd G P hn v hv b) k) := by
  have hN : 2 ≤ G.n * G.n := two_le_mul_self hn
  have hA0 : (QMCLeafB.EngineIterates.castM (QMCLeafB.RunPartsDilate.A0P G P)).PosDef :=
    QMCLeafB.RunPartsDilate.A0P_posDef G P
  have hM0 : 0 < QMCLeafB.RundataArith.capOf G P.dq :=
    QMCLeafB.RundataArith.capOf_pos G P.dq P.hdq
  have hbase : ∀ w : Fin (G.n * G.n) → ℝ,
      w ⬝ᵥ (QMCLeafB.EngineIterates.castM (QMCLeafB.RunPartsDilate.A0P G P) *ᵥ w)
        = (((QMCLeafB.RundataArith.capOf G P.dq : ℚ)) : ℝ)⁻¹ * (w ⬝ᵥ w) := by
    intro w
    have h := QMCLeafB.Sc35M7.base_qf (n := G.n * G.n) (QMCLeafB.RundataArith.capOf G P.dq) w
    have hA0P : QMCLeafB.RunPartsDilate.A0P G P
        = QMCLeafB.Boundary.initShapeOf (G.n * G.n) (QMCLeafB.RundataArith.capOf G P.dq) := rfl
    rw [hA0P]
    exact h
  have hcsq : ∀ k, QMCLeafB.EngineIterates.cutCR (faceCd G P hn v hv b) k
      ⬝ᵥ QMCLeafB.EngineIterates.cutCR (faceCd G P hn v hv b) k = 1 := by
    intro k
    have hcast : QMCLeafB.EngineIterates.cutCR (faceCd G P hn v hv b) k
        = vR (pickN v b (faceSt G P hn v hv b k).2) := rfl
    rw [hcast]
    unfold pickN
    split_ifs with hle
    · exact vR_dot_self hunit
    · exact neg_vR_dot_self hunit
  have hwit : ∀ k, QMCLeafB.EngineIterates.Aat (G.n * G.n) (QMCLeafB.RunPartsDilate.A0P G P)
      (faceCd G P hn v hv b) k *ᵥ ((faceCd G P hn v hv b k).p)
        = (faceCd G P hn v hv b k).c := by
    intro k
    have h1 := face_hwit G P hn v hv b k
    have h2 : QMCLeafB.RunPartsDilate.A0P G P
        = QMCLeafB.Boundary.initShapeOf (G.n * G.n)
            (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2) := rfl
    rw [h2]
    exact h1
  exact QMCLeafB.Sc35M7.sigma_ge (n := G.n * G.n) hN hA0 hwit
    (fun k => by show (0 : ℚ) ≤ P.rmax; exact P.hrmax)
    (fun k => pickN_ne_zero hv b (faceSt G P hn v hv b k).2)
    (M0 := QMCLeafB.RundataArith.capOf G P.dq) (ρ := P.rmax) (fun k => rfl) hM0 hbase k
    (hcsq k)

#print axioms QMCLeafB.Gq38M7.slab_sigma_floor

/-- **THE SLAB RECORD.**  If the whole relaxation lies in a slab `b − h ≤ v ⬝ z ≤ b + h` of half-width
`h ≥ 0` about a rational unit normal `v`, and the half-width fits the horizon's σ-floor (`hledger`),
then the all-false record EXISTS — at every threshold, every horizon, every program. -/
theorem bodyRec_of_slab {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (hunit : v ⬝ᵥ v = 1)
    (b : ℝ) (hq : ℚ) (h0 : 0 ≤ hq)
    (hslab : ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P,
      b - ((hq : ℚ) : ℝ) ≤ vR v ⬝ᵥ z ∧ vR v ⬝ᵥ z ≤ b + ((hq : ℚ) : ℝ))
    (hledger : ∀ k, k < P.K * P.m →
      hq ^ 2 ≤ P.rmax ^ 2 * (QMCLeafB.RundataArith.capOf G P.dq
        * ((((G.n * G.n : ℕ) : ℚ) + P.rmax) / (((G.n * G.n : ℕ) : ℚ) + 1)) ^ (2 * k))) :
    QMCLeafB.ThinRec34M4.BodyRec G t P := by
  have hbc : ∀ T : ℕ, QMCLeafB.SimLoop.anyOk (fun _ : ℕ => false) T = false := by
    intro T
    induction T with
    | zero => rfl
    | succ T ih => rw [QMCLeafB.SimLoop.anyOk_succ, ih]; rfl
  refine ⟨{ ok := fun _ => false
            cd := faceCd G P hn v hv b
            del := fun _ => hq
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
    exact h0
  · intro k hk _
    have hfloor := slab_sigma_floor P hn v hv hunit b k
    have hcastσ : ((QMCLeafB.EngineIterates.sigmaQ (faceCd G P hn v hv b k).c
        (faceCd G P hn v hv b k).p : ℚ) : ℝ)
        = QMCLeafB.EngineIterates.sigmaR
            (QMCLeafB.EngineIterates.cutCR (faceCd G P hn v hv b) k)
            (QMCLeafB.EngineIterates.cutPR (faceCd G P hn v hv b) k) :=
      QMCLeafB.EngineIterates.cast_sigmaQ _ _
    have hstep : ((hq : ℚ) : ℝ) ^ 2 ≤ ((P.rmax : ℚ) : ℝ) ^ 2
        * (((QMCLeafB.RundataArith.capOf G P.dq : ℚ) : ℝ)
          * (((((G.n * G.n : ℕ) : ℝ) + ((P.rmax : ℚ) : ℝ))
              / (((G.n * G.n : ℕ) : ℝ) + 1)) ^ (2 * k))) := by
      have hb := hledger k hk
      have hcast : (((hq ^ 2 : ℚ)) : ℝ) ≤ (((P.rmax ^ 2 * (QMCLeafB.RundataArith.capOf G P.dq
            * ((((G.n * G.n : ℕ) : ℚ) + P.rmax) / (((G.n * G.n : ℕ) : ℚ) + 1)) ^ (2 * k)) : ℚ)) : ℝ) := by
        exact_mod_cast hb
      push_cast at hcast
      simpa using hcast
    have hreal : ((hq : ℚ) : ℝ) ^ 2 ≤ ((P.rmax : ℚ) : ℝ) ^ 2
        * QMCLeafB.EngineIterates.sigmaR
            (QMCLeafB.EngineIterates.cutCR (faceCd G P hn v hv b) k)
            (QMCLeafB.EngineIterates.cutPR (faceCd G P hn v hv b) k) :=
      le_trans hstep (mul_le_mul_of_nonneg_left hfloor (sq_nonneg _))
    have hgoalR : (((hq ^ 2 : ℚ)) : ℝ)
        ≤ (((P.rmax ^ 2 * QMCLeafB.EngineIterates.sigmaQ (faceCd G P hn v hv b k).c
              (faceCd G P hn v hv b k).p : ℚ)) : ℝ) := by
      have hL : (((hq ^ 2 : ℚ)) : ℝ) = ((hq : ℚ) : ℝ) ^ 2 := by push_cast; ring
      have hR : (((P.rmax ^ 2 * QMCLeafB.EngineIterates.sigmaQ (faceCd G P hn v hv b k).c
              (faceCd G P hn v hv b k).p : ℚ)) : ℝ)
          = ((P.rmax : ℚ) : ℝ) ^ 2 * QMCLeafB.EngineIterates.sigmaR
              (QMCLeafB.EngineIterates.cutCR (faceCd G P hn v hv b) k)
              (QMCLeafB.EngineIterates.cutPR (faceCd G P hn v hv b) k) := by
        rw [← hcastσ]
        push_cast
        ring
      rw [hL, hR]
      exact hreal
    rw [show (faceCd G P hn v hv b k).rho = P.rmax from rfl]
    exact_mod_cast hgoalR
  · intro k _ _
    show P.rmax ≤ P.rmax
    exact le_refl _
  · intro k _ _ z hz
    have hs := hslab z hz
    have hspec := pickN_spec_slab (v := v) (b := b) (h := ((hq : ℚ) : ℝ))
      (a := (faceSt G P hn v hv b k).2) (z := z) hs.1 hs.2
    rw [Cat_faceCd, dotProduct_sub]
    show -(((hq : ℚ) : ℝ)) ≤ vR (pickN v b (faceSt G P hn v hv b k).2) ⬝ᵥ z
      - vR (pickN v b (faceSt G P hn v hv b k).2) ⬝ᵥ (faceSt G P hn v hv b k).2
    linarith
  · have h1 : QMCLeafB.ThinRec34M4.falseBit G t = false := rfl
    have h2 : QMCLeafB.SimLoop.anyOk (fun _ => false) (P.K * P.m) = false := hbc _
    rw [h1, h2]

#print axioms QMCLeafB.Gq38M7.bodyRec_of_slab

/-! ## 3.  The collar body at `G₁` is a SLAB

The face identity `X₀₀ + X₁₁ = 2 + δ/2` at `Δ = 0` becomes `X₀₀ + X₁₁ ≥ 2 + δ/2 − Δ` when the
objective ceiling rises by `Δ`; with `Xᵢᵢ ≤ 1 + δ/4` this pins `X₀₀` to the two-sided window
`[1 + δ/4 − Δ, 1 + δ/4]`, i.e. a slab of half-width `Δ/2`. -/

open QMCLeafB.DregM6 in
/-- **The slab bound at the exemplar.**  Every point of the relaxed body at `tStar + Δ` has its
`(0,0)` diagonal in `[1 + δ/4 − Δ, 1 + δ/4]`. -/
theorem slab_G1 (Δ : ℚ) (hΔ : 0 ≤ Δ)
    {z : Fin (DregM6.G₁.n * DregM6.G₁.n) → ℝ}
    (hz : z ∈ QMCLeafB.ThinRec34M4.relaxBallP DregM6.G₁ (DregM6.tStar + Δ) DregM6.P₁) :
    1 + (1 / 380000 : ℝ) / 4 - (Δ : ℝ) ≤ QMCLeafB.Boundary.unflat z 0 0
      ∧ QMCLeafB.Boundary.unflat z 0 0 ≤ 1 + (1 / 380000 : ℝ) / 4 := by
  have hd : ((DregM6.P₁.dq : ℚ) : ℝ) = 1 / 380000 := QMCLeafB.Cov36M7.dq_r
  have hu : (((DregM6.tStar + Δ : ℚ)) : ℝ)
      - (((QMCLeafB.EngineRuntime.Rq DregM6.G₁ / 40000 : ℚ)) : ℝ)
      = -(2 + 2 * (1 / 380000 : ℝ)) + (Δ : ℝ) :=
  QMCLeafB.DregM6.thresh_eq Δ
  have hbody := hz.1
  rw [hu, hd] at hbody
  obtain ⟨hpsd, hdiag, htr⟩ := hbody
  have hqf := hpsd (fun _ : Fin 2 => (1 : ℝ))
  have hsq : (∑ i : Fin 2, ((1 : ℝ)) ^ 2) = 2 := by norm_num
  have hqf' : QMCLeafB.BallFloor.qfR (QMCLeafB.Boundary.unflat z) (fun _ : Fin 2 => (1 : ℝ))
      = QMCLeafB.Boundary.unflat z 0 0 + QMCLeafB.Boundary.unflat z 0 1
        + QMCLeafB.Boundary.unflat z 1 0 + QMCLeafB.Boundary.unflat z 1 1 := by
    rw [QMCLeafB.BallFloor.qfR_eq_sum]
    simp only [Fin.sum_univ_two]
    ring
  rw [hsq, hqf'] at hqf
  have hfr : QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix DregM6.G₁) (QMCLeafB.Boundary.unflat z)
      = QMCLeafB.Boundary.unflat z 0 1 + QMCLeafB.Boundary.unflat z 1 0 := by
    simp only [QMCLeafB.BallFloor.frob, Fin.sum_univ_two,
      QMCLeafB.AnchorFactsM2.wMatrix_G₁_00, QMCLeafB.AnchorFactsM2.wMatrix_G₁_01,
      QMCLeafB.AnchorFactsM2.wMatrix_G₁_10, QMCLeafB.AnchorFactsM2.wMatrix_G₁_11]
    ring
  rw [hfr] at htr
  have hd0 : QMCLeafB.Boundary.unflat z 0 0 ≤ 1 + (1 / 380000 : ℝ) / 4 := by
    have := (abs_le.mp (hdiag 0)).2
    linarith
  have hd1 : QMCLeafB.Boundary.unflat z 1 1 ≤ 1 + (1 / 380000 : ℝ) / 4 := by
    have := (abs_le.mp (hdiag 1)).2
    linarith
  constructor
  · linarith
  · exact hd0

#print axioms QMCLeafB.Gq38M7.slab_G1

/-! ## 3b.  The explicit threshold and its ledger

`Δ := (1/2)^(6·K·m + 2875392)`, half-width `h = Δ/2 = (1/2)^(K·m·6 + 2875393)`.  The exponent is
chosen so that the ledger follows from `(13/16)^{2k} ≥ (1/2)^{2k}` and nothing else, and so that
`Δ^8 ≤ 2^{-23003136}` holds with NO exact value of `K·m` beyond `1 ≤ K·m`. -/

/-- The collar point's objective slack exponent. -/
def N38 : ℕ := 6 * (DregM6.P₁.K * DregM6.P₁.m) + 2875392

/-- **The explicit collar slack.** -/
def Delta38 : ℚ := (1 / 2) ^ N38

/-- The recorded margin: exactly `Delta38 / 2`. -/
def hq38 : ℚ := (1 / 2) ^ (N38 + 1)

theorem hq38_eq_half : hq38 * 2 = Delta38 := by
  unfold hq38 Delta38
  rw [pow_succ]
  ring

theorem hq38_nonneg : 0 ≤ hq38 := by
  unfold hq38
  positivity

theorem hq38_pos : 0 < hq38 := by
  unfold hq38
  positivity

theorem Delta38_pos : 0 < Delta38 := by
  unfold Delta38
  positivity

theorem Delta38_nonneg : 0 ≤ Delta38 := Delta38_pos.le

theorem Delta38_ne_zero : Delta38 ≠ 0 := Delta38_pos.ne'

/-- The slack is far below any threshold the campaign uses. -/
theorem Delta38_le_inv : Delta38 ≤ (1 / 2 : ℚ) ^ 24 := by
  unfold Delta38
  refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
  unfold N38
  have h := QMCLeafB.UnionShallow.one_le_Kbc2_mul DregM6.G₁
  generalize DregM6.P₁.K * DregM6.P₁.m = TT at h ⊢
  omega

theorem P1_rmax : DregM6.P₁.rmax = 1 / 16 := by
  have h : DregM6.P₁.rmax = QMCLeafB.RundataHalving.rmaxOf (DregM6.G₁.n * DregM6.G₁.n) := rfl
  rw [h, QMCLeafB.Cov36M7.n_G₁]
  unfold QMCLeafB.RundataHalving.rmaxOf
  norm_num

theorem NN_eq : (((DregM6.G₁.n * DregM6.G₁.n : ℕ) : ℚ)) = 4 := by
  rw [QMCLeafB.Cov36M7.n_G₁]
  norm_num

theorem delta_ratio : ((((DregM6.G₁.n * DregM6.G₁.n : ℕ) : ℚ) + DregM6.P₁.rmax)
      / (((DregM6.G₁.n * DregM6.G₁.n : ℕ) : ℚ) + 1)) = 13 / 16 := by
  rw [NN_eq, P1_rmax]
  norm_num

theorem cap_ge_eight : (8 : ℚ) ≤ QMCLeafB.RundataArith.capOf DregM6.G₁ DregM6.P₁.dq := by
  unfold QMCLeafB.RundataArith.capOf
  have hn : DregM6.G₁.n = 2 := QMCLeafB.Cov36M7.n_G₁
  rw [hn]
  push_cast
  nlinarith [sq_nonneg DregM6.P₁.dq]

theorem T_pos : 1 ≤ DregM6.P₁.K * DregM6.P₁.m :=
  QMCLeafB.UnionShallow.one_le_Kbc2_mul DregM6.G₁

/-- **The horizon ledger at the explicit slack.** -/
theorem Delta38_ledger :
    ∀ k, k < DregM6.P₁.K * DregM6.P₁.m →
      hq38 ^ 2 ≤ DregM6.P₁.rmax ^ 2
        * (QMCLeafB.RundataArith.capOf DregM6.G₁ DregM6.P₁.dq
          * ((((DregM6.G₁.n * DregM6.G₁.n : ℕ) : ℚ) + DregM6.P₁.rmax)
              / (((DregM6.G₁.n * DregM6.G₁.n : ℕ) : ℚ) + 1)) ^ (2 * k)) := by
  intro k hk
  set T : ℕ := DregM6.P₁.K * DregM6.P₁.m with hT
  have hT1 : 1 ≤ T := by rw [hT]; exact T_pos
  -- 1.  `hq38 ^ 2 = (1/2)^(2 * N38 + 2)`
  have hsq : hq38 ^ 2 = (1 / 2 : ℚ) ^ (2 * N38 + 2) := by
    unfold hq38
    rw [← pow_mul, show (N38 + 1) * 2 = 2 * N38 + 2 by omega]
  -- 2.  the exponent is far beyond `2T + 5`
  have hexp : 2 * T + 5 ≤ 2 * (6 * T + 2875392) + 2 := by omega
  have hstep1 : (1 / 2 : ℚ) ^ (2 * N38 + 2) ≤ (1 / 2 : ℚ) ^ (2 * T + 5) := by
    have : 2 * N38 + 2 = 2 * (6 * T + 2875392) + 2 := by unfold N38; rw [← hT]
    rw [this]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  -- 3.  `(1/2)^(2T+5) = (1/32) * (1/2)^(2T)`
  have hstep2 : (1 / 2 : ℚ) ^ (2 * T + 5) = (1 / 32) * (1 / 2 : ℚ) ^ (2 * T) := by
    rw [pow_add]
    norm_num
    ring
  -- 4.  `(1/2)^(2T) ≤ (13/16)^(2T) ≤ (13/16)^(2k)`
  have hstep3 : (1 / 32 : ℚ) * (1 / 2) ^ (2 * T) ≤ (1 / 32) * (13 / 16 : ℚ) ^ (2 * k) := by
    have h1 : (1 / 2 : ℚ) ^ (2 * T) ≤ (13 / 16 : ℚ) ^ (2 * T) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h2 : (13 / 16 : ℚ) ^ (2 * T) ≤ (13 / 16) ^ (2 * k) := by
      refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
      omega
    exact mul_le_mul_of_nonneg_left (le_trans h1 h2) (by norm_num)
  -- 5.  `(1/32) ≤ rmax² · capOf`
  have hstep4 : (1 / 32 : ℚ) ≤ DregM6.P₁.rmax ^ 2
      * QMCLeafB.RundataArith.capOf DregM6.G₁ DregM6.P₁.dq := by
    rw [P1_rmax]
    calc (1 / 32 : ℚ) = (1 / 16) ^ 2 * 8 := by norm_num
      _ ≤ (1 / 16) ^ 2 * QMCLeafB.RundataArith.capOf DregM6.G₁ DregM6.P₁.dq :=
          mul_le_mul_of_nonneg_left cap_ge_eight (by norm_num)
  calc hq38 ^ 2 = (1 / 2 : ℚ) ^ (2 * N38 + 2) := hsq
    _ ≤ (1 / 2 : ℚ) ^ (2 * T + 5) := hstep1
    _ = (1 / 32) * (1 / 2 : ℚ) ^ (2 * T) := hstep2
    _ ≤ (1 / 32) * (13 / 16 : ℚ) ^ (2 * k) := hstep3
    _ ≤ (DregM6.P₁.rmax ^ 2 * QMCLeafB.RundataArith.capOf DregM6.G₁ DregM6.P₁.dq)
          * (13 / 16 : ℚ) ^ (2 * k) := by
        exact mul_le_mul_of_nonneg_right hstep4 (by positivity)
    _ = DregM6.P₁.rmax ^ 2
        * (QMCLeafB.RundataArith.capOf DregM6.G₁ DregM6.P₁.dq
          * ((((DregM6.G₁.n * DregM6.G₁.n : ℕ) : ℚ) + DregM6.P₁.rmax)
              / (((DregM6.G₁.n * DregM6.G₁.n : ℕ) : ℚ) + 1)) ^ (2 * k)) := by
        rw [delta_ratio]
        ring

#print axioms QMCLeafB.Gq38M7.Delta38_ledger

/-! ## 3c.  THE COLLAR RECORD: a genuine band point where the record EXISTS -/

theorem e00_unit : Face36M2.e00 ⬝ᵥ Face36M2.e00 = 1 := by
  unfold QMCLeafB.Face36M2.e00
  rw [dotProduct, Finset.sum_eq_single (finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)))]
  · norm_num
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **THE COLLAR RECORD.**  At the band point `(G₁, tStar + Δ)` with
`Δ = (1/2)^(6·K·m + 2875392)` the all-false record EXISTS, unconditionally.  This is a point with a
NONEMPTY body (`not_bodyEmpty`), inside the leaf's interior bracket, OFF the measure-zero face, and
below EVERY banked content obstruction (a ball witness needs `1 < pConst·r^8` with `r ≤ Δ`). -/
theorem bodyRec_collar :
    QMCLeafB.ThinRec34M4.BodyRec DregM6.G₁ (DregM6.tStar + Delta38) DregM6.P₁ := by
  have hΔnn : (0:ℝ) ≤ ((Delta38 : ℚ) : ℝ) := by
    exact_mod_cast QMCLeafB.Gq38M7.hq38_nonneg.trans (by
      rw [← hq38_eq_half]; nlinarith [hq38_pos])
  have hcast2 : ((hq38 : ℚ) : ℝ) * 2 = ((Delta38 : ℚ) : ℝ) := by
    have := hq38_eq_half
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) this
  refine bodyRec_of_slab (G := DregM6.G₁) (t := DregM6.tStar + Delta38) (P := DregM6.P₁)
    QMCLeafB.Cov36M7.two_le_n Face36M2.e00 Face36M2.e00_ne e00_unit
    (1 + (1 / 380000 : ℝ) / 4 - ((hq38 : ℚ) : ℝ)) hq38 hq38_nonneg ?_ Delta38_ledger
  intro z hz
  have hs := slab_G1 Delta38 (Delta38_pos.le) hz
  have hdot : vR Face36M2.e00 ⬝ᵥ z = QMCLeafB.Boundary.unflat z 0 0 :=
    QMCLeafB.Face36M2.dot_e00 z
  rw [hdot]
  constructor
  · have : ((Delta38 : ℚ) : ℝ) = 2 * ((hq38 : ℚ) : ℝ) := by linarith [hcast2]
    linarith [hs.1]
  · linarith [hs.2]

#print axioms QMCLeafB.Gq38M7.bodyRec_collar

/-- The collar slack is strictly below the campaign's own band tolerance. -/
theorem Delta38_lt_d0 : Delta38 < QMCLeafB.Cov36M7.d0 := by
  have h1 : Delta38 ≤ 1 / 16777216 := by
    have h := Delta38_le_inv
    have h2 : (1 / 2 : ℚ) ^ 24 = 1 / 16777216 := by norm_num
    rwa [h2] at h
  have h3 : (1 / 16777216 : ℚ) < QMCLeafB.Cov36M7.d0 := by
    rw [QMCLeafB.Cov36M7.d0]
    norm_num
  exact lt_of_le_of_lt h1 h3

/-- **The collar point is inside the leaf's interior bracket.** -/
theorem collar_bracket :
    -QMCLeafB.EngineRuntime.Rq DregM6.G₁ ≤ DregM6.tStar + Delta38
      ∧ DregM6.tStar + Delta38 ≤ 0 :=
  QMCLeafB.Cov36M7.band_in_bracket Delta38_pos Delta38_lt_d0

/-- **The collar body is nonempty** (the record is owed at a point the campaign cannot delete). -/
theorem collar_nonempty :
    ¬ QMCLeafB.ThriceM3.BodyEmpty DregM6.G₁ (DregM6.tStar + Delta38) DregM6.P₁ := by
  have h1 : Delta38 ≤ 1 / 16777216 := by
    have h := Delta38_le_inv
    have h2 : (1 / 2 : ℚ) ^ 24 = 1 / 16777216 := by norm_num
    rwa [h2] at h
  have hR : ((Delta38 : ℚ) : ℝ) ≤ (1 / 16777216 : ℝ) := by
    have h := Rat.cast_le (K := ℝ).mpr h1
    simpa using h
  have hΔ0R : (0 : ℝ) ≤ ((Delta38 : ℚ) : ℝ) := by
    have h := Rat.cast_nonneg (K := ℝ).mpr Delta38_nonneg
    simpa using h
  refine QMCLeafB.DregM6.not_bodyEmpty Delta38 hΔ0R ?_
  linarith

/-- **The content obstructions are SILENT at the collar point**: `pConst·Δ^8 ≤ 1`, so m1/ph35's
criterion `1 < pConst·r^8` has no witness (`r ≤ Δ` by `ball_radius_le_slack`). -/
theorem collar_silent : QMCLeafB.Cov36M7.pConst * ((Delta38 : ℚ) : ℝ) ^ 8 ≤ 1 := by
  have hpc : QMCLeafB.Cov36M7.pConst ≤ (2 : ℝ) ^ 23003136 := QMCLeafB.Cov36M7.pConst_le
  have hpos : (0:ℝ) < QMCLeafB.Cov36M7.pConst := QMCLeafB.Cov36M7.pConst_pos
  -- Δ^8 ≤ (1/2)^23003136
  have hΔ8 : ((Delta38 : ℚ) : ℝ) ^ 8 ≤ (1 / 2 : ℝ) ^ 23003136 := by
    have hD : ((Delta38 : ℚ) : ℝ) = (1 / 2 : ℝ) ^ N38 := by
      unfold Delta38
      push_cast
      norm_num
    rw [hD, ← pow_mul]
    refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
    unfold N38
    have h := T_pos
    omega
  have hmul : (2 : ℝ) ^ 23003136 * (1 / 2 : ℝ) ^ 23003136 = 1 := by
    rw [← mul_pow]
    norm_num
  calc QMCLeafB.Cov36M7.pConst * ((Delta38 : ℚ) : ℝ) ^ 8
      ≤ (2 : ℝ) ^ 23003136 * (1 / 2 : ℝ) ^ 23003136 := by
        exact mul_le_mul hpc hΔ8 (by positivity) (by positivity)
    _ = 1 := hmul

#print axioms QMCLeafB.Gq38M7.collar_silent

/-- **THE DECIDED VERDICT ON THE COLLAR.**  There is a rational `Δ > 0`, below the campaign's band
tolerance, with the point `(G₁, tStar + Δ)` inside the leaf's interior bracket, its relaxed body
NONEMPTY, `Δ ≠ 0` (off the measure-zero face), and `pConst·Δ^8 ≤ 1` (so no ball/cube/parallelotope
obstruction can fire) — and the all-false record EXISTS there.  So the record horn is NOT dead off the
face, and `SelfRec` holds at this band point without any bit-horn hypothesis. -/
theorem collar_summary :
    ∃ Δ : ℚ, 0 < Δ ∧ Δ < QMCLeafB.Cov36M7.d0 ∧ Δ ≠ 0
      ∧ (-QMCLeafB.EngineRuntime.Rq DregM6.G₁ ≤ DregM6.tStar + Δ
          ∧ DregM6.tStar + Δ ≤ 0)
      ∧ ¬ QMCLeafB.ThriceM3.BodyEmpty DregM6.G₁ (DregM6.tStar + Δ) DregM6.P₁
      ∧ QMCLeafB.Cov36M7.pConst * ((Δ : ℚ) : ℝ) ^ 8 ≤ 1
      ∧ QMCLeafB.ThinRec34M4.BodyRec DregM6.G₁ (DregM6.tStar + Δ) DregM6.P₁ :=
  ⟨Delta38, Delta38_pos, Delta38_lt_d0, Delta38_pos.ne',
    collar_bracket, collar_nonempty, collar_silent, bodyRec_collar⟩

#print axioms QMCLeafB.Gq38M7.collar_summary

/-- **The leaf's `hfalse` slot at the collar point, DISCHARGED for every bit.**  If the program's bit
reads `false` at `(G₁, tStar + Δ38)` — which the campaign's own reading says it must, since the body
is ball-free — then the run transcript exists there, with no bit-horn hypothesis. -/
theorem collar_hfalse (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hbit : o DregM6.G₁ (DregM6.tStar + Delta38) = false) :
    Nonempty (QMCLeafB.FinalStroke.RunParts o DregM6.G₁ (DregM6.tStar + Delta38) DregM6.P₁) :=
  (QMCLeafB.ThinRec34M4.runParts_false_iff_bodyRec hbit).2 bodyRec_collar

#print axioms QMCLeafB.Gq38M7.collar_hfalse

/-! ## 4.  THE ONE-ROUND CRITERION: the obligation is a bounded-distance condition

The campaign's `ShallowCut` reads `c·(Cat k − z) ≤ del k` with `del k² ≤ rmax²σ_k`.  This section
records what that inequality MEANS geometrically: if the closed `r`-ball of the shape metric around
the centre is inside the body for some `r > ρ`, then NO normal can separate the centre from the body
at depth `ρ` — every `c` is beaten strictly by a body point.  So the round's obstruction is exactly
the *bounded-distance* condition "the centre is not `ρ`-deep in the body", and the shallow ledger is
a statement about the centre's POSITION, not about depths or presentations. -/

/-- **THE DEEP-CORE OBSTRUCTION (strict form).**  If the closed ball of shape-radius `r` about `a`
lies in `B` and `ρ < r`, then for EVERY nonzero `c` some body point beats `ρ·√(cᵀA⁻¹c)` strictly:
no cut at depth `ρ` can have `a` as its accumulated centre. -/
theorem deep_core_blocks {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {a : Fin n → ℝ} {B : Set (Fin n → ℝ)} {ρ r : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ < r)
    (hball : ∀ z, (z - a) ⬝ᵥ (A *ᵥ (z - a)) ≤ r ^ 2 → z ∈ B)
    {c : Fin n → ℝ} (hc : c ≠ 0) :
    ∃ z ∈ B, ρ * Real.sqrt (c ⬝ᵥ (A⁻¹ *ᵥ c)) < c ⬝ᵥ (a - z) := by
  classical
  set p : Fin n → ℝ := A⁻¹ *ᵥ c with hp
  have hAA : A * A⁻¹ = 1 := by
    rw [Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hA)]
  have hAp : A *ᵥ p = c := by
    rw [hp, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hsym : Aᵀ = A := by
    have h := hA.isHermitian.eq
    simpa using h
  have hσpos : 0 < c ⬝ᵥ p := by
    have hpc : c ⬝ᵥ p = p ⬝ᵥ (A *ᵥ p) := by
      rw [dotProduct_comm c p, hAp]
    rw [hpc]
    refine hA.dotProduct_mulVec_pos (x := p) ?_
    intro hp0
    apply hc
    rw [← hAp, hp0]
    exact Matrix.mulVec_zero A
  set σ : ℝ := c ⬝ᵥ p with hσdef
  set u : Fin n → ℝ := (Real.sqrt σ)⁻¹ • p with hudef
  have hσσ : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt hσpos.le
  have hσne : Real.sqrt σ ≠ 0 := by positivity
  -- `u` is a unit vector of the shape metric
  have huA : u ⬝ᵥ (A *ᵥ u) = 1 := by
    have h1 : u ⬝ᵥ (A *ᵥ u) = (Real.sqrt σ)⁻¹ * (Real.sqrt σ)⁻¹ * (p ⬝ᵥ (A *ᵥ p)) := by
      rw [hudef, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [h1]
    have hpa : p ⬝ᵥ (A *ᵥ p) = Real.sqrt σ * Real.sqrt σ :=
      (show p ⬝ᵥ (A *ᵥ p) = σ from by rw [hAp]; exact dotProduct_comm p c).trans hσσ.symm
    rw [hpa]
    calc (Real.sqrt σ)⁻¹ * (Real.sqrt σ)⁻¹ * (Real.sqrt σ * Real.sqrt σ)
        = ((Real.sqrt σ)⁻¹ * Real.sqrt σ) * ((Real.sqrt σ)⁻¹ * Real.sqrt σ) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hσne]; ring
  -- the witnessed body point
  have hmem : (a - r • u) ∈ B := by
    refine hball (a - r • u) ?_
    have hsub : (a - r • u) - a = -(r • u) := by abel
    rw [hsub]
    have hneg : (-(r • u)) ⬝ᵥ (A *ᵥ (-(r • u))) = (u ⬝ᵥ (A *ᵥ u)) * r ^ 2 := by
      have h1 : (-(r • u)) ⬝ᵥ (A *ᵥ (-(r • u))) = (r • u) ⬝ᵥ (A *ᵥ (r • u)) := by
        rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
      have h2 : (r • u) ⬝ᵥ (A *ᵥ (r • u)) = r * r * (u ⬝ᵥ (A *ᵥ u)) := by
        rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        ring
      rw [h1, h2]
      ring
    rw [hneg, huA]
    norm_num
  refine ⟨a - r • u, hmem, ?_⟩
  have hsub : a - (a - r • u) = r • u := by abel
  rw [hsub, dotProduct_smul, smul_eq_mul]
  have hcu : c ⬝ᵥ u = Real.sqrt σ := by
    rw [hudef, dotProduct_smul, smul_eq_mul]
    have h1 : c ⬝ᵥ p = Real.sqrt σ * Real.sqrt σ :=
      (show c ⬝ᵥ p = σ from rfl).trans hσσ.symm
    rw [h1]
    calc (Real.sqrt σ)⁻¹ * (Real.sqrt σ * Real.sqrt σ)
        = (Real.sqrt σ)⁻¹ * Real.sqrt σ * Real.sqrt σ := by ring
      _ = 1 * Real.sqrt σ := by rw [inv_mul_cancel₀ hσne]
      _ = Real.sqrt σ := one_mul _
  rw [hcu]
  have hpos : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσpos
  nlinarith

#print axioms QMCLeafB.Gq38M7.deep_core_blocks

/-- **THE HORIZON-FREE REFUTATION.**  If the relaxation contains the closed `A₀`-ball of radius `r`
about the ORIGIN with `r > rmax`, then no all-false record exists — for any horizon, any depths, any
normals.  Unlike every banked ball/cube/parallelotope obstruction, this one needs NO horizon
inequality: it fires at round ZERO, where the accumulated centre is exactly the origin.  So the
record's exact domain excludes every body that is `rmax`-fat at `0`. -/
theorem not_bodyRec_of_core_zero {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (hKm : 0 < P.K * P.m)
    {r : ℝ} (hr : (P.rmax : ℝ) < r)
    (hball : ∀ z : Fin (G.n * G.n) → ℝ,
      (z - 0) ⬝ᵥ ((QMCLeafB.EngineIterates.castM (QMCLeafB.RunPartsDilate.A0P G P)) *ᵥ (z - 0))
        ≤ r ^ 2 → z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P) :
    ¬ QMCLeafB.ThinRec34M4.BodyRec G t P := by
  classical
  rintro ⟨B⟩
  have hany : QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m) = false := B.hverdict.symm
  have hok0 : B.ok 0 = false :=
    (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).1 hany 0 hKm
  have hA0 : (QMCLeafB.EngineIterates.castM (QMCLeafB.RunPartsDilate.A0P G P)).PosDef :=
    QMCLeafB.RunPartsDilate.A0P_posDef G P
  have hwit0 : QMCLeafB.EngineIterates.Aat (G.n * G.n) (QMCLeafB.RunPartsDilate.A0P G P) B.cd 0
      *ᵥ (B.cd 0).p = (B.cd 0).c := by
    have h1 := B.hwit 0 hKm hok0
    have h2 : QMCLeafB.RunPartsDilate.A0P G P
        = QMCLeafB.Boundary.initShapeOf (G.n * G.n)
            (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2) := rfl
    rw [h2]
    exact h1
  have hσne : (B.cd 0).c ≠ 0 := B.hcne 0 hKm hok0
  have hcast : QMCLeafB.EngineIterates.cutCR B.cd 0 ⬝ᵥ
      ((QMCLeafB.EngineIterates.castM (QMCLeafB.RunPartsDilate.A0P G P))⁻¹ *ᵥ
        QMCLeafB.EngineIterates.cutCR B.cd 0)
      = QMCLeafB.EngineIterates.sigmaQ (B.cd 0).c (B.cd 0).p := by
    have hinv : (QMCLeafB.EngineIterates.castM (QMCLeafB.RunPartsDilate.A0P G P))⁻¹ *ᵥ
        QMCLeafB.EngineIterates.cutCR B.cd 0 = QMCLeafB.EngineIterates.cutPR B.cd 0 := by
      have hcst : QMCLeafB.EngineIterates.castM (QMCLeafB.RunPartsDilate.A0P G P) *ᵥ
          QMCLeafB.EngineIterates.cutPR B.cd 0 = QMCLeafB.EngineIterates.cutCR B.cd 0 := by
        have h0 : QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat (G.n * G.n)
            (QMCLeafB.RunPartsDilate.A0P G P) B.cd 0) *ᵥ
            QMCLeafB.EngineIterates.cutPR B.cd 0 = QMCLeafB.EngineIterates.cutCR B.cd 0 := by
          rw [QMCLeafB.EngineIterates.cast_mulVec]
          exact congrArg (fun v : Fin (G.n * G.n) → ℚ => fun i => ((v i : ℚ) : ℝ)) hwit0
        have hAat0 : QMCLeafB.EngineIterates.Aat (G.n * G.n)
            (QMCLeafB.RunPartsDilate.A0P G P) B.cd 0 = QMCLeafB.RunPartsDilate.A0P G P := rfl
        rw [hAat0] at h0
        exact h0
      exact QMCLeafB.EngineIterates.inv_mulVec_eq_of_mulVec_eq hA0 hcst
    rw [hinv]
    exact (QMCLeafB.EngineIterates.cast_sigmaQ (B.cd 0).c (B.cd 0).p).symm
  obtain ⟨z, hz, hbeat⟩ := deep_core_blocks (A := QMCLeafB.EngineIterates.castM
      (QMCLeafB.RunPartsDilate.A0P G P)) hA0 (a := 0) (B := QMCLeafB.ThinRec34M4.relaxBallP G t P)
    (ρ := ((P.rmax : ℚ) : ℝ)) (r := r) (by exact_mod_cast P.hrmax) hr hball
    (c := QMCLeafB.EngineIterates.cutCR B.cd 0) (QMCLeafB.EngineIterates.cast_normal_ne hσne)
  have hencl := QMCLeafB.ThinRec34M4.encl_of_bodyRec (t := t) (P := P) B 0 hKm z hz
  rw [hcast] at hbeat
  -- `Cat 0 = 0`, so the enclosure is `-(c·z) ≤ rmax·√σ`
  have hC0 : QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd 0 = 0 := rfl
  rw [hC0] at hencl
  rw [dotProduct_zero] at hencl
  have hsub : QMCLeafB.EngineIterates.cutCR B.cd 0 ⬝ᵥ (0 - z)
      = -(QMCLeafB.EngineIterates.cutCR B.cd 0 ⬝ᵥ z) := by
    rw [zero_sub, dotProduct_neg]
  rw [hsub] at hbeat
  linarith

#print axioms QMCLeafB.Gq38M7.not_bodyRec_of_core_zero


