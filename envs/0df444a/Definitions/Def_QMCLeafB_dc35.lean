-- Prove2me | Definitions.Def_QMCLeafB_dc35
-- name    : QMCLeafB_dc35
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:47:19.098213+00:00
-- url     : https://prove2.me/theorems/f26abae4-5127-4005-9abd-def70fb62a31
-- title:
--   QMCLeafB dc35
-- statement:
--   # `Check_dc35_m1` — depth-decomposition: the ledger is the ONLY obstruction
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thinrec34
/-
# `Check_dc35_m1` — depth-decomposition: the ledger is the ONLY obstruction

Phase 35, member m1, direction d1 (`depth-decomposition`).  The obligation is
`QMCLeafB.ThinRec34M4.ShallowCut G t P hn` (m4/ph34-d5): a nonzero rational normal stream `c` and
rational margins `del` with

  `del k ≥ max_{z in relaxBall} c_k · (Cat_k - z)`   and   `(del k)^2 ≤ rmax^2 · σ_k`

where `σ_k = c_k ⬝ᵥ p_k`, `p_k` the engine's own witness of `A_k p_k = c_k`, at the CEILING
depth `ρ ≡ rmax` (`ShallowCut`'s transcript is `RunPartsDilate.runCut`).

This file pins the exact quantity and proves which part of it the engine controls.

## The decomposition (all machine-checked below)

Write `Q_k(z) := (z - Cat_k) ⬝ᵥ (A_k *ᵥ (z - Cat_k))` for the `A_k`-squared-radius of `z` about
the accumulated centre, and `R_k := sup {Q_k(z) : z ∈ relaxBall}`.

* §1 `depth_le_radius` — **the two-line Cauchy-Schwarz bound**: for ANY nonzero normal `c_k`,
  `c_k · (Cat_k - z) ≤ sqrt(Q_k z) * sqrt(σ_k)`.  Hence if `R_k ≤ d^2` with `d` rational,
  `d < rmax`, the round is closed with a *rational* margin (the ledger `del^2 ≤ rmax^2 σ` is an
  open condition, so the strict factor is what makes the rational ledger exist; §2 makes this
  exact).  **So `del := √σ` always separates: the ledger is the only obstruction.**
* §2 `exists_rat_ledger` — the rational ledger closes exactly on the open interval: given
  `d√σ < rmax√σ` there is a rational `del` with `d√σ ≤ del` and `del^2 ≤ rmax^2 σ`.
* §3 `shallowCut_of_radius` — the assembly: a normal stream plus a strict rational radius bound
  `R_k ≤ (dr k)^2 < rmax^2` at every round below the horizon PROVES `ShallowCut`.
* §4 `depth_self` — **which part the engine controls**: with the normal taken through a POINT of
  the relaxation, `p_k = Cat_k - z`, the depth is `√σ_k` exactly, i.e. `√(Q_k z)` — the
  ellipsoid radius of that point.  So the cut-at-a-violated-point choice pins the depth at the
  ellipsoid radius (which is `1` at a boundary point of the ellipsoid), and the ONLY freedom is
  the choice of DIRECTIONS, in which the depth ranges down to the relaxation's `A_k`-inradius.
* §5 `separated_round_free` — the opposite extreme: if the relaxation lies entirely on the far
  side of a hyperplane through `Cat_k`, the round costs `del = 0`.  (This is why the ellipsoid's
  own "first" round is free and why a FIXED direction dies — §7 quantifies the death.)
* §6 `contains_all_ellipsoids` — NECESSARY: `ShallowCut` forces the relaxation into EVERY
  ellipsoid of the ceiling chain (`body_containment` at `ρ ≡ rmax`, since `del ≤ rmax√σ ≤ √σ`).
  Consequence `not_shallowCut_of_ball`: at a campaign-ball-bearing body no shallow-cut stream
  exists.  The confinement m4 stated for the record transfers verbatim to the obligation.
* §7 `fixed_direction_dies` — the exact arithmetic of a constant normal stream: with the engine's
  own recursion the two quantities satisfy `h_{k+1} = h_k + γ_k λ_k`, `λ_{k+1} = λ_k (1 - γ_k)`,
  so `h_k + λ_k` is INVARIANT and `λ_k → 0`; a fixed direction therefore satisfies
  `c · Cat_k ≤ ℓ` only for a bounded number of rounds, with the explicit bound
  `K ≤ log(λ_0/(λ_0 + h_0 - ℓ)) / log (1 - γmax)`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every theorem (expected `[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.DC35M1

open QMCLeafB.EngineIterates
open QMCLeafB.ThinRec34M4 (ShallowCut NormalCut relaxBallP BodyRec)

/-! ## 1.  The depth of a cut, and the Cauchy–Schwarz bound

The depth of the round-`k` record in direction `c` at the accumulated centre `Cat_k` is
`(c ⬝ᵥ (Cat_k - z)) / √σ_k`, maximised over `z` in the relaxation.  The bound below says it is at
most the `A_k`-radius of `z` about `Cat_k` — so it is the RADIUS, not the depth, that the ledger
compares against `rmax`. -/

/-- **The two-line Cauchy–Schwarz bound.**  For a positive-definite `A`, a nonzero normal `c` with
witness `p` (`A p = c`), and any `u` whose `A`-squared-radius is at most `d²`:

  `c ⬝ᵥ u ≤ d · √σ`,   `σ = c ⬝ᵥ p = c ⬝ᵥ A⁻¹ c`.

`u` is `Cat_k - z` in the application.  No positivity of `d` is needed for the inequality itself;
`hd` only orders the product. -/
theorem depth_le_radius {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p u : Fin N → ℝ} (hAp : A *ᵥ p = c) (hc : c ≠ 0)
    {d : ℝ} (hd : 0 ≤ d) (hQ : u ⬝ᵥ (A *ᵥ u) ≤ d ^ 2) :
    c ⬝ᵥ u ≤ d * sqrtSigmaR c p := by
  have hσ : 0 < sigmaR c p := sigmaR_pos hA hAp hc
  have hσle : 0 ≤ sigmaR c p := hσ.le
  have hr : 0 ≤ sqrtSigmaR c p := Real.sqrt_nonneg _
  have hrr : sqrtSigmaR c p * sqrtSigmaR c p = sigmaR c p :=
    sqrtSigmaR_mul_self hA hAp hc
  have hcs := cauchy_sigmaR hA hAp hc u
  have hcs' : (c ⬝ᵥ u) ^ 2 ≤ sigmaR c p * (d ^ 2) := by
    have h1 : sigmaR c p * (u ⬝ᵥ (A *ᵥ u)) ≤ sigmaR c p * d ^ 2 :=
      mul_le_mul_of_nonneg_left hQ hσle
    linarith
  have hsq : (c ⬝ᵥ u) ^ 2 ≤ (d * sqrtSigmaR c p) ^ 2 := by
    have hrr2 : sqrtSigmaR c p ^ 2 = sigmaR c p := by rw [pow_two]; exact hrr
    rw [mul_pow, hrr2]; linarith
  have htarget : 0 ≤ d * sqrtSigmaR c p := mul_nonneg hd hr
  have hkey : |c ⬝ᵥ u| ≤ d * sqrtSigmaR c p := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt ((c ⬝ᵥ u) ^ 2) ≤ Real.sqrt ((d * sqrtSigmaR c p) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = d * sqrtSigmaR c p := Real.sqrt_sq htarget
  exact le_trans (le_abs_self _) hkey

#print axioms QMCLeafB.DC35M1.depth_le_radius

/-! ## 2.  The rational ledger closes on the strict factor

`del` is a RATIONAL margin: the engine's check `del² ≤ rmax²σ` is an exact rational comparison.
So a real bound of the shape `sup ≤ rmax·√σ` does not immediately produce a legal margin: we need
the strict inequality `sup < rmax·√σ` (and then rational density).  The strict factor is the
honest price of rationality, and it is the only reason any hypothesis below says `<` rather
than `≤`. -/

/-- **The rational ledger.**  If `σ > 0` and `d < rmax` (both rational, `0 ≤ d`, `0 ≤ rmax`), then
there is a rational `del` with `d·√σ ≤ del` and `del² ≤ rmax²·σ`. -/
theorem exists_rat_ledger {σ rmax d : ℚ} (hσ : 0 < σ) (hd0 : 0 ≤ d) (hd : d < rmax)
    (hrmax : 0 ≤ rmax) :
    ∃ del : ℚ, 0 ≤ del ∧ (d : ℝ) * Real.sqrt (σ : ℝ) ≤ (del : ℝ)
      ∧ (del : ℝ) ≤ (rmax : ℝ) * Real.sqrt (σ : ℝ)
      ∧ del ^ 2 ≤ rmax ^ 2 * σ := by
  have hσR : (0 : ℝ) < (σ : ℝ) := by exact_mod_cast hσ
  have hr : 0 < Real.sqrt (σ : ℝ) := Real.sqrt_pos.2 hσR
  have hrmaxR : (0 : ℝ) ≤ (rmax : ℝ) := by exact_mod_cast hrmax
  have hdR : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd0
  have hlt : (d : ℝ) * Real.sqrt (σ : ℝ) < (rmax : ℝ) * Real.sqrt (σ : ℝ) :=
    mul_lt_mul_of_pos_right (by exact_mod_cast hd) hr
  obtain ⟨del, h1, h2⟩ := exists_rat_btwn hlt
  have hdel0 : 0 ≤ del := by
    have : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt (σ : ℝ) := mul_nonneg hdR hr.le
    have h1' : (0 : ℝ) < (del : ℝ) := lt_of_le_of_lt this h1
    exact_mod_cast h1'.le
  refine ⟨del, hdel0, h1.le, h2.le, ?_⟩
  -- square the real inequality
  have hdelR : (0 : ℝ) ≤ (del : ℝ) := by exact_mod_cast hdel0
  have hsq : ((del : ℚ) : ℝ) ^ 2 ≤ ((rmax : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ) := by
    have h2' : (del : ℝ) ≤ (rmax : ℝ) * Real.sqrt (σ : ℝ) := h2.le
    have hsq2 : ((rmax : ℝ) * Real.sqrt (σ : ℝ)) ^ 2 = (rmax : ℝ) ^ 2 * (σ : ℝ) := by
      rw [mul_pow, Real.sq_sqrt hσR.le]
    nlinarith [sq_nonneg ((del : ℝ) - 0)]
  exact_mod_cast hsq

#print axioms QMCLeafB.DC35M1.exists_rat_ledger

/-! ## 3.  The ceiling chain, and the assembly of `ShallowCut` from a radius bound

`ShallowCut`'s transcript is fixed: `runCut` at `ρ ≡ rmax`, i.e. the shape chain generated by the
normal stream at the *ceiling* depth.  We name that chain's shape and centre and record its two
engine facts (positivity, and the witness relation from `runCut_wit`). -/

/-- The shape matrix of the CEILING chain at round `k` — the transcript `ShallowCut` names. -/
noncomputable def ceilShape (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    Matrix (Fin (G.n * G.n)) (Fin (G.n * G.n)) ℚ :=
  QMCLeafB.EngineIterates.Aat (G.n * G.n)
    (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
      (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) (NormalCut G P hn c hc) k

/-- The accumulated centre of the CEILING chain at round `k`. -/
noncomputable def ceilCentre (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    Fin (G.n * G.n) → ℝ :=
  QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
    (NormalCut G P hn c hc) k

/-- The initial shape of the chain is positive definite. -/
theorem initShape_posDef (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) :
    (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
      (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).PosDef :=
  QMCLeafB.Boundary.initShapeOf_cast_posDef
    (QMCLeafB.RundataArith.capOf_pos G P.dq P.hdq)

/-- The witness relation of the ceiling chain, in `initShapeOf` form. -/
theorem ceilShape_wit (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) :
    ∀ k, ceilShape G P hn c hc k *ᵥ (NormalCut G P hn c hc k).p
      = (NormalCut G P hn c hc k).c := by
  intro k
  have h := QMCLeafB.RunPartsDilate.runCut_wit G P hn c hc k
  show QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))
      (QMCLeafB.RunPartsDilate.runCut G P hn c hc) k
      *ᵥ (QMCLeafB.RunPartsDilate.runCut G P hn c hc k).p
    = (QMCLeafB.RunPartsDilate.runCut G P hn c hc k).c
  rw [← QMCLeafB.ThinRec34M4.initShape_eq G P]
  exact h

#print axioms QMCLeafB.DC35M1.ceilShape_wit

/-- Every shape of the ceiling chain is positive definite. -/
theorem ceilShape_posDef (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    (QMCLeafB.EngineIterates.castM (ceilShape G P hn c hc k)).PosDef := by
  have hN : 2 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  refine QMCLeafB.EngineIterates.Aat_cast_posDef hN (initShape_posDef G P)
    (ceilShape_wit G P hn c hc) (fun k => ?_) (fun k => hc k) k
  show (0 : ℚ) ≤ P.rmax
  exact P.hrmax

#print axioms QMCLeafB.DC35M1.ceilShape_posDef

/-- The cast witness of the ceiling chain: `A_k p_k = c_k` over `ℝ`. -/
theorem ceilShape_cast_wit (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    QMCLeafB.EngineIterates.castM (ceilShape G P hn c hc k)
        *ᵥ (fun i => ((NormalCut G P hn c hc k).p i : ℝ))
      = fun i => ((NormalCut G P hn c hc k).c i : ℝ) :=
  QMCLeafB.EngineIterates.cast_witness (ceilShape_wit G P hn c hc) k

#print axioms QMCLeafB.DC35M1.ceilShape_cast_wit

/-- The ceiling chain's `σ` at round `k` is positive (real form). -/
theorem sigmaR_ceil_pos (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    0 < QMCLeafB.EngineIterates.sigmaR
      (QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k)
      (QMCLeafB.EngineIterates.cutPR (NormalCut G P hn c hc) k) := by
  have h1 : (NormalCut G P hn c hc k).c ≠ 0 := hc k
  exact QMCLeafB.EngineIterates.sigmaR_pos (ceilShape_posDef G P hn c hc k)
    (ceilShape_cast_wit G P hn c hc k) (QMCLeafB.EngineIterates.cast_normal_ne h1)

#print axioms QMCLeafB.DC35M1.sigmaR_ceil_pos

/-- The ceiling chain's `σ` at round `k` is positive (rational form — the ledger's side). -/
theorem sigmaQ_ceil_pos (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    0 < QMCLeafB.EngineIterates.sigmaQ (c k) ((NormalCut G P hn c hc k).p) := by
  refine QMCLeafB.EngineIterates.sigmaQ_pos_of_cast ?_
  show 0 < QMCLeafB.EngineIterates.sigmaR (fun i => ((c k) i : ℝ))
    (fun i => (((NormalCut G P hn c hc k).p) i : ℝ))
  exact sigmaR_ceil_pos G P hn c hc k

#print axioms QMCLeafB.DC35M1.sigmaQ_ceil_pos

/-- **The assembly.**  A nonzero rational normal stream whose ceiling chain carries the relaxation
inside the STRICT `d_k`-ellipsoid about its own centre, with `d_k < rmax` rational, PROVES
`ShallowCut`.  The rational margin at each round is `exists_rat_ledger`'s. -/
theorem shallowCut_of_radius (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (dr : ℕ → ℚ) (hdr0 : ∀ k, 0 ≤ dr k) (hdlt : ∀ k, dr k < P.rmax)
    (hR : ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
      (ceilCentre G P hn c hc k - z)
          ⬝ᵥ (QMCLeafB.EngineIterates.castM (ceilShape G P hn c hc k)
              *ᵥ (ceilCentre G P hn c hc k - z)) ≤ ((dr k : ℚ) : ℝ) ^ 2) :
    ShallowCut G t P hn := by
  classical
  have hσpos : ∀ k, 0 < QMCLeafB.EngineIterates.sigmaQ (c k)
      ((NormalCut G P hn c hc k).p) := fun k => sigmaQ_ceil_pos G P hn c hc k
  have hex : ∀ k, ∃ del : ℚ, 0 ≤ del
      ∧ ((dr k : ℚ) : ℝ) * Real.sqrt (((QMCLeafB.EngineIterates.sigmaQ
            (c k) ((NormalCut G P hn c hc k).p) : ℚ)) : ℝ) ≤ (del : ℝ)
      ∧ del ^ 2 ≤ P.rmax ^ 2 * QMCLeafB.EngineIterates.sigmaQ (c k)
          ((NormalCut G P hn c hc k).p) := by
    intro k
    obtain ⟨d, hd0, h1, -, h2⟩ := exists_rat_ledger (hσpos k) (hdr0 k) (hdlt k) P.hrmax
    exact ⟨d, hd0, h1, h2⟩
  choose del hdel0 hdlb hdchk using hex
  refine ⟨c, hc, del, fun k _ => hdel0 k, fun k => hdchk k, ?_⟩
  intro k hk z hz
  have hdepth := depth_le_radius (ceilShape_posDef G P hn c hc k)
    (ceilShape_cast_wit G P hn c hc k)
    (QMCLeafB.EngineIterates.cast_normal_ne (hc k))
    (by exact_mod_cast hdr0 k) (hR k hk z hz)
  have hsqrt : QMCLeafB.EngineIterates.sqrtSigmaR
      (QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k)
      (QMCLeafB.EngineIterates.cutPR (NormalCut G P hn c hc) k)
      = Real.sqrt (((QMCLeafB.EngineIterates.sigmaQ (c k)
          ((NormalCut G P hn c hc k).p) : ℚ)) : ℝ) :=
    congrArg Real.sqrt (QMCLeafB.EngineIterates.cast_sigmaQ (c k)
      ((NormalCut G P hn c hc k).p)).symm
  rw [hsqrt] at hdepth
  show QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k
        ⬝ᵥ ceilCentre G P hn c hc k
      - QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k ⬝ᵥ z
      ≤ ((del k : ℚ) : ℝ)
  rw [← dotProduct_sub]
  exact le_trans hdepth (hdlb k)

#print axioms QMCLeafB.DC35M1.shallowCut_of_radius

/-! ## 4.  Which part the engine controls: the depth in the "cut-through-a-point" direction

`ShallowCut` leaves the NORMAL free.  The engine's own natural choice — the normal `A_k (Cat_k - z)`
through a relaxation point `z` (equivalently the witness `p_k = Cat_k - z`) — is the WORST choice:
its depth is exactly `√σ_k = √((Cat_k - z) ᵀ A_k (Cat_k - z))`, the `A_k`-radius of that point.
At a boundary point of the ellipsoid that is `1`, while the ledger demands `≤ rmax < 1`.  So the
direction choice is not cosmetic: the cut-at-a-violated-point direction pins the depth at the
ellipsoid radius, and the only way the ledger can be met is a direction in which the relaxation is
THINNER than the ellipsoid by the factor `rmax`. -/

/-- `σ` of the "cut through a point" normal: with `c = A p`, `σ = p ⬝ᵥ (A p)`, the `A`-quadratic
form of the witness (`= ‖p‖²_A`). -/
theorem sigmaQ_self {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (p : Fin N → ℚ) :
    QMCLeafB.EngineIterates.sigmaQ (A *ᵥ p) p = QMCLeafB.EngineIterates.qf A p := by
  rw [QMCLeafB.EngineIterates.sigmaQ, QMCLeafB.EngineIterates.qf]
  exact dotProduct_comm _ _

#print axioms QMCLeafB.DC35M1.sigmaQ_self

/-- **The worst direction pins the depth at the ellipsoid radius.**  Cutting in the direction
`c = A u` (i.e. `p = u`), the recorded depth `c ⬝ᵥ u / √σ` is exactly `√σ = √(u ᵀ A u)`. -/
theorem depth_self {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) {u : Fin N → ℝ}
    (hu : u ≠ 0) :
    ((A *ᵥ u) ⬝ᵥ u) / sqrtSigmaR (A *ᵥ u) u = sqrtSigmaR (A *ᵥ u) u := by
  have hq : 0 < u ⬝ᵥ (A *ᵥ u) := hA.dotProduct_mulVec_pos hu
  have hpos : 0 < (A *ᵥ u) ⬝ᵥ u := by rw [dotProduct_comm]; exact hq
  have hsq : sqrtSigmaR (A *ᵥ u) u * sqrtSigmaR (A *ᵥ u) u = (A *ᵥ u) ⬝ᵥ u := by
    rw [← pow_two, sqrtSigmaR]
    exact Real.sq_sqrt hpos.le
  have hr : 0 < sqrtSigmaR (A *ᵥ u) u := Real.sqrt_pos.2 hpos
  rw [div_eq_iff (ne_of_gt hr)]
  linarith [hsq]

#print axioms QMCLeafB.DC35M1.depth_self

/-- **The pin.**  If in addition the point sits on the ELLIPSOID's boundary (`u ᵀ A u = 1`), the
depth is exactly `1`, so no rational margin with `del < 1` records that direction; and a fortiori
no margin allowed by the ledger `del ≤ rmax·√σ` with `rmax < 1`. -/
theorem depth_self_of_boundary {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {u : Fin N → ℝ} (hu : u ≠ 0) (h1 : u ⬝ᵥ (A *ᵥ u) = 1) :
    ((A *ᵥ u) ⬝ᵥ u) / sqrtSigmaR (A *ᵥ u) u = 1 := by
  rw [depth_self hA hu]
  have hq : 0 < u ⬝ᵥ (A *ᵥ u) := hA.dotProduct_mulVec_pos hu
  have hpos : 0 < (A *ᵥ u) ⬝ᵥ u := by rw [dotProduct_comm]; exact hq
  have hsq : sqrtSigmaR (A *ᵥ u) u * sqrtSigmaR (A *ᵥ u) u = 1 := by
    have h2 : sqrtSigmaR (A *ᵥ u) u ^ 2 = (A *ᵥ u) ⬝ᵥ u := by
      rw [sqrtSigmaR]; exact Real.sq_sqrt hpos.le
    have h3 : (A *ᵥ u) ⬝ᵥ u = 1 := by
      rw [dotProduct_comm]; exact h1
    rw [← pow_two]; exact h2.trans h3
  have hr : 0 < sqrtSigmaR (A *ᵥ u) u := Real.sqrt_pos.2 hpos
  nlinarith [hsq, hr]

#print axioms QMCLeafB.DC35M1.depth_self_of_boundary

/-! ## 5.  The other extreme: a separated round is FREE (`del = 0`)

If the relaxation lies entirely on the far side of a hyperplane through `Cat_k`, the round costs
NOTHING: `del = 0` satisfies the ledger (`0² ≤ rmax²σ` for free) and the separation.  The round-`k`
criterion `min_c depth_k(c) ≤ rmax` is therefore `≤ 0` (free) exactly when `Cat_k` can be separated
from the relaxation, and positive only when `Cat_k` has entered the relaxation's convex hull. -/

/-- **A separated round costs `del = 0`.**  `hsep` says the relaxation is above the hyperplane
through `a` in direction `c`; then the round's separation holds with margin `0`, and the ledger at
`del = 0` is automatic. -/
theorem separated_round_free {N : ℕ} (c : Fin N → ℚ) {a : Fin N → ℝ}
    {B : Set (Fin N → ℝ)} (hsep : ∀ z ∈ B, (fun i => (c i : ℝ)) ⬝ᵥ a
      ≤ (fun i => (c i : ℝ)) ⬝ᵥ z)
    (σ rmax : ℚ) (hσ : 0 ≤ σ) (hrmax : 0 ≤ rmax) :
    ((0 : ℚ)) ^ 2 ≤ rmax ^ 2 * σ
      ∧ ∀ z ∈ B, (fun i => (c i : ℝ)) ⬝ᵥ a - (fun i => (c i : ℝ)) ⬝ᵥ z ≤ ((0 : ℚ) : ℝ) := by
  refine ⟨by simpa using mul_nonneg (by positivity) hσ, ?_⟩
  intro z hz
  have h := hsep z hz
  have h0 : ((0 : ℚ) : ℝ) = 0 := by norm_num
  rw [h0]
  linarith

#print axioms QMCLeafB.DC35M1.separated_round_free

/-- The `(i,j)` coordinate functional on the flat code. -/
def coord (n : ℕ) (i j : Fin n) : Fin (n * n) → ℚ :=
  fun k => if k = finProdFinEquiv (i, j) then 1 else 0

theorem coord_ne_zero {n : ℕ} (i j : Fin n) : coord n i j ≠ 0 := by
  intro h
  have h1 : coord n i j (finProdFinEquiv (i, j))
      = (0 : Fin (n * n) → ℚ) (finProdFinEquiv (i, j)) := by
    rw [h]
  simp [coord] at h1

#print axioms QMCLeafB.DC35M1.coord_ne_zero

theorem coord_dot {n : ℕ} (i j : Fin n) (z : Fin (n * n) → ℝ) :
    (fun k => ((coord n i j k : ℚ) : ℝ)) ⬝ᵥ z
      = QMCLeafB.Boundary.unflat z i j := by
  rw [QMCLeafB.Boundary.unflat]
  simp only [dotProduct]
  rw [Finset.sum_eq_single (finProdFinEquiv (i, j))]
  · simp [coord]
  · intro b _ hb
    simp [coord, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

#print axioms QMCLeafB.DC35M1.coord_dot

/-- **Round 0 is FREE, and the reason is the diagonal pinning.**  At `Cat 0 = 0` the coordinate
functional of any diagonal entry separates the accumulated centre from the whole relaxation,
because `relaxBodyLE` pins the diagonal to `1 ± dq/4` with `dq ≤ 4`.  So the ledger at `rmax < 1`
does not die at round 0 — it dies only if the trajectory cannot keep re-separating (see §7). -/
theorem round_zero_separates (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) (hdq : P.dq ≤ 4) :
    ∃ c : Fin (G.n * G.n) → ℚ, c ≠ 0
      ∧ ∀ z ∈ relaxBallP G t P,
          (fun i => (c i : ℝ)) ⬝ᵥ (0 : Fin (G.n * G.n) → ℝ)
            ≤ (fun i => (c i : ℝ)) ⬝ᵥ z := by
  haveI hne : NeZero G.n := ⟨by omega⟩
  refine ⟨coord G.n 0 0, coord_ne_zero 0 0, ?_⟩
  intro z hz
  have hz1 : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
      ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ)
      (QMCLeafB.Boundary.unflat z) := hz.1
  have hdiag := hz1.2.1 0
  have hL : (fun i => ((coord G.n 0 0 i : ℚ) : ℝ)) ⬝ᵥ (0 : Fin (G.n * G.n) → ℝ) = 0 := by
    simp
  have hzval : (fun i => ((coord G.n 0 0 i : ℚ) : ℝ)) ⬝ᵥ z
      = QMCLeafB.Boundary.unflat z 0 0 := coord_dot 0 0 z
  rw [hL, hzval]
  have hdqR : ((P.dq : ℚ) : ℝ) ≤ 4 := by exact_mod_cast hdq
  have hle := (abs_le.mp hdiag).1
  linarith

#print axioms QMCLeafB.DC35M1.round_zero_separates

/-! ## 6.  NECESSARY: a shallow-cut stream puts the relaxation in EVERY ellipsoid

`ShallowCut`'s ledger gives `del k ≤ rmax·√σ_k ≤ √σ_k` (as `rmax ≤ 1` in the campaign), which is
exactly the hypothesis of the engine's containment invariant at ceiling depth `ρ ≡ rmax`.  So the
obligation forces `relaxBall ⊆ Ell (A_k) (Cat_k)` at every round below the horizon — the *same*
consequence m4's `BodyRec` has.  In particular no shallow-cut stream exists at a campaign-ball
body (the ball floor contradicts the determinant accounting), which is the confinement m4 stated,
now at the level of the obligation itself. -/

/-- **`ShallowCut` forces containment.**  The ceiling chain carries the whole relaxation in every
one of its ellipsoids, below the horizon.  (`ρ ≡ rmax` and `del ≤ rmax·√σ ≤ √σ` since `rmax ≤ 1`,
so each recorded cut is a VALID cut of the relaxation — the very hypothesis of the engine's
containment invariant.) -/
theorem containment_of_shallow (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) (hrmax1 : P.rmax ≤ 1)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (del : ℕ → ℚ)
    (hdel0 : ∀ k, k < P.K * P.m → 0 ≤ del k)
    (hdel : ∀ k, (del k) ^ 2 ≤ P.rmax ^ 2
      * QMCLeafB.EngineIterates.sigmaQ (c k) ((NormalCut G P hn c hc k).p))
    (hshallow : ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
      QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k
          ⬝ᵥ ceilCentre G P hn c hc k
        - QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k ⬝ᵥ z
        ≤ ((del k : ℚ) : ℝ)) :
    ∀ k, k ≤ P.K * P.m → ∀ z ∈ relaxBallP G t P,
      QMCLeafB.EngineIterates.Ell (QMCLeafB.EngineIterates.castM (ceilShape G P hn c hc k))
        (ceilCentre G P hn c hc k) z := by
  have hN : 2 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  have hcover : ∀ z : Fin (G.n * G.n) → ℝ, z ∈ relaxBallP G t P →
      QMCLeafB.EngineIterates.Ell
        (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))) (0 : Fin (G.n * G.n) → ℝ) z := by
    intro z hz
    exact QMCLeafB.Boundary.ell_initShapeOf
      (QMCLeafB.RundataArith.capOf_pos G P.dq P.hdq) (QMCLeafB.Boundary.relaxBall_norm hz)
  intro k
  induction k with
  | zero =>
      intro _ z hz
      exact hcover z hz
  | succ k ih =>
      intro hk z hz
      have hkN : k < P.K * P.m := by omega
      have hprev := ih (by omega) z hz
      have hA := ceilShape_posDef G P hn c hc k
      have hwit := ceilShape_cast_wit G P hn c hc k
      have hcne : QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k ≠ 0 := by
        have h1 : (NormalCut G P hn c hc k).c ≠ 0 := hc k
        exact QMCLeafB.EngineIterates.cast_normal_ne h1
      have hdelb : ((del k : ℚ) : ℝ) ≤ (P.rmax : ℝ)
          * sqrtSigmaR (QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k)
              (QMCLeafB.EngineIterates.cutPR (NormalCut G P hn c hc) k) := by
        have h := QMCLeafB.EngineIterates.margin_le_of_sq_check (hdel0 k hkN) P.hrmax
          (le_of_lt (sigmaQ_ceil_pos G P hn c hc k)) (hdel k)
        have hsqrt := congrArg Real.sqrt (QMCLeafB.EngineIterates.cast_sigmaQ (c k)
          ((NormalCut G P hn c hc k).p))
        rw [hsqrt] at h
        exact h
      have hshape : QMCLeafB.EngineIterates.castM (ceilShape G P hn c hc (k + 1))
          = QMCLeafB.EngineIterates.stepShape (G.n * G.n)
              (QMCLeafB.EngineIterates.castM (ceilShape G P hn c hc k))
              (QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k)
              (QMCLeafB.EngineIterates.cutPR (NormalCut G P hn c hc) k) (P.rmax : ℝ) := by
        show QMCLeafB.EngineIterates.castM
          (QMCLeafB.EngineIterates.rStep (G.n * G.n) (ceilShape G P hn c hc k)
            (NormalCut G P hn c hc k).c (NormalCut G P hn c hc k).p P.rmax) = _
        exact QMCLeafB.EngineIterates.rStep_cast _ _ _ _
      rw [hshape]
      have hstep := QMCLeafB.EngineIterates.step_containment hN hA hcne hwit
        (ceilCentre G P hn c hc k) (ρ := (P.rmax : ℝ)) (by exact_mod_cast P.hrmax)
      refine hstep ⟨hprev, ?_⟩
      show -((P.rmax : ℝ) * sqrtSigmaR (QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k)
            (QMCLeafB.EngineIterates.cutPR (NormalCut G P hn c hc) k))
          ≤ QMCLeafB.EngineIterates.cutCR (NormalCut G P hn c hc) k
              ⬝ᵥ (z - ceilCentre G P hn c hc k)
      have hcut := hshallow k hkN z hz
      rw [dotProduct_sub]
      linarith

#print axioms QMCLeafB.DC35M1.containment_of_shallow

/-- **The confinement, transferred to the obligation.**  At a body carrying the campaign ball no
shallow-cut stream exists: `ShallowCut ⟹ BodyRec` (m4) and the ball floor kills every all-false
record.  So the obligation lives exactly on the ball-free stratum — as m4's confinement said for
the record, now for `ShallowCut` itself. -/
theorem not_shallowCut_of_ball (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t P) :
    ¬ ShallowCut G t P hn :=
  fun H => QMCLeafB.ThinRec34M4.not_bodyRec_of_ball hn hball
    (QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn H)

#print axioms QMCLeafB.DC35M1.not_shallowCut_of_ball

/-! ## 7.  Why a FIXED direction dies: the exact invariance

The engine's own recursion, read along a fixed direction `c`, gives two scalar recurrences:
`h_{k+1} = h_k + γ_k λ_k` (the centre rises toward the relaxation) and
`λ_{k+1} = λ_k (1 - γ_k)` (the ellipsoid's `c`-extent contracts), with `h_k = c ⬝ᵥ Cat_k`,
`λ_k = √σ_k`, `γ_k = (1-ρ_k)/(N+1)`.  Then `h_k + λ_k` is INVARIANT and `λ_k → 0`.  So a fixed
direction can satisfy `c ⬝ᵥ Cat_k ≤ ℓ` only while `λ_k ≥ λ₀ + h₀ - ℓ`; since `λ_k` decays
geometrically this bounds the number of rounds.  This is the exact reason every constant-normal
stream on the record dies (and it is why the direction must be re-chosen at every round). -/

/-- **The invariant of a fixed direction.**  The two recurrences force `h k + λ k = h 0 + λ 0`. -/
theorem fixed_dir_invariant {γ h lam : ℕ → ℝ}
    (hh : ∀ k, h (k + 1) = h k + γ k * lam k)
    (hl : ∀ k, lam (k + 1) = lam k * (1 - γ k)) :
    ∀ k, h k + lam k = h 0 + lam 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [hh k, hl k]
      linear_combination ih

#print axioms QMCLeafB.DC35M1.fixed_dir_invariant

/-- **A fixed direction dies.**  With `γ k ∈ [0,1]` bounded BELOW by `γmin > 0` (which the engine
supplies: `γ_k = (1-ρ_k)/(N+1) ≥ (1-rmax)/(N+1)`), `λ 0 > 0`, and `h` staying below
`ℓ < λ 0 + h 0`, the recurrences cannot hold at every round. -/
theorem fixed_direction_dies {γ h lam : ℕ → ℝ} {γmin ℓ : ℝ}
    (hγ0 : ∀ k, 0 ≤ γ k) (hγ1 : ∀ k, γ k ≤ 1) (hγmin : ∀ k, γmin ≤ γ k)
    (hγmin0 : 0 < γmin)
    (hh : ∀ k, h (k + 1) = h k + γ k * lam k)
    (hl : ∀ k, lam (k + 1) = lam k * (1 - γ k))
    (hl0 : 0 < lam 0)
    (hbdd : ∀ k, h k ≤ ℓ) (hℓ : ℓ < lam 0 + h 0) :
    False := by
  have hnonneg : ∀ k, 0 ≤ 1 - γ k := fun k => by linarith [hγ1 k]
  have hmono : ∀ k, 1 - γ k ≤ 1 - γmin := fun k => by linarith [hγmin k]
  have hgm0 : 0 ≤ 1 - γmin := by linarith [hγmin 0, hγ1 0]
  have hgm1 : 1 - γmin < 1 := by linarith
  have hupper : ∀ k, lam k ≤ lam 0 * (1 - γmin) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep : lam (k + 1) = lam k * (1 - γ k) := hl k
        rw [hstep]
        have hpos : (0 : ℝ) ≤ lam 0 * (1 - γmin) ^ k :=
          mul_nonneg hl0.le (pow_nonneg hgm0 k)
        have h1 : lam k * (1 - γ k) ≤ lam 0 * (1 - γmin) ^ k * (1 - γ k) :=
          mul_le_mul_of_nonneg_right ih (hnonneg k)
        have h2 : lam 0 * (1 - γmin) ^ k * (1 - γ k)
            ≤ lam 0 * (1 - γmin) ^ (k + 1) := by
          calc lam 0 * (1 - γmin) ^ k * (1 - γ k)
              ≤ lam 0 * (1 - γmin) ^ k * (1 - γmin) :=
                mul_le_mul_of_nonneg_left (hmono k) hpos
            _ = lam 0 * (1 - γmin) ^ (k + 1) := by rw [pow_succ]; ring
        linarith
  have hinv : ∀ k, h k + lam k = h 0 + lam 0 := fixed_dir_invariant hh hl
  have hlower : (0 : ℝ) < lam 0 + h 0 - ℓ := by linarith
  have htend : Filter.Tendsto (fun k : ℕ => (1 - γmin) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hgm0 hgm1
  have htend2 : Filter.Tendsto (fun k : ℕ => lam 0 * (1 - γmin) ^ k) Filter.atTop (nhds 0) := by
    have h := htend.const_mul (lam 0)
    simpa using h
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      lam 0 * (1 - γmin) ^ k < lam 0 + h 0 - ℓ :=
    htend2.eventually (isOpen_Iio.mem_nhds hlower)
  obtain ⟨K, hK⟩ := Filter.Eventually.exists hev
  have h1 : lam 0 + h 0 - ℓ ≤ lam K := by
    have h2 := hinv K
    have h3 := hbdd K
    linarith
  have h4 := hupper K
  linarith

#print axioms QMCLeafB.DC35M1.fixed_direction_dies

/-! ## 8.  The refutation criterion: ANY ball in the relaxation kills a long enough horizon

§6 says `ShallowCut` puts the whole relaxation in the LAST ellipsoid of the ceiling chain.  The
ball floor (`BallFloor.pow_two_mul_det_le_one_of_ball_subset_Ell`, radius-agnostic) then forces
`r^(2N)·det A_{K·m} ≤ 1`, while the engine's determinant telescopes to
`det A_0 · rho0R(N, rmax)^(K·m)`.  So **a ball of ANY positive radius in the relaxation refutes
`ShallowCut` as soon as the horizon beats `r^(-2N)`**:

    det A_0 · rho0R^K·m · r^(2N) > 1   ⟹   ¬ ShallowCut.

This is strictly stronger than `BallM2.no_runParts_of_ball`, which is the same statement at the
campaign's own radius `dq/(8(cA+1))` and the campaign's own halving count: the radius here is a
FREE parameter, so a body that is ball-free at the campaign radius but carries a SMALLER ball (a
thin slab with any positive width, or a free skew/antisymmetric direction) is refuted at a
correspondingly longer horizon.  It is the criterion to test at the thin band. -/

/-- **Horizon criterion.**  If the relaxation carries a Euclidean ball of radius `r > 0` (in flat
coordinates) and the horizon `K·m` beats the determinant floor, then no shallow-cut stream exists.
-/
theorem not_shallowCut_of_ball_horizon (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) (hrmax1 : P.rmax ≤ 1)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin (G.n * G.n) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀) ∈ relaxBallP G t P)
    (hK : 1 < (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).det
      * (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((P.rmax : ℚ) : ℝ)) ^ (P.K * P.m)
      * r ^ (2 * (G.n * G.n))) :
    ¬ ShallowCut G t P hn := by
  rintro ⟨c, hc, del, hdel0, hdel, hshallow⟩
  have hN : 2 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  -- containment at the final round
  have hcont := containment_of_shallow G t P hn hrmax1 c hc del hdel0 hdel hshallow
  -- the ball sits in the last ellipsoid
  have hball' : ∀ y : Fin (G.n * G.n) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀ - ceilCentre G P hn c hc (P.K * P.m))
          ⬝ᵥ (QMCLeafB.EngineIterates.castM (ceilShape G P hn c hc (P.K * P.m))
              *ᵥ (y + QMCLeafB.AnswerProducer.flat X₀
                  - ceilCentre G P hn c hc (P.K * P.m))) ≤ 1 := by
    intro y hy
    exact hcont (P.K * P.m) (le_refl _) (y + QMCLeafB.AnswerProducer.flat X₀) (hball y hy)
  have hfloor := QMCLeafB.BallFloor.pow_two_mul_det_le_one_of_ball_subset_Ell
    (ceilShape_posDef G P hn c hc (P.K * P.m)) hr hball'
  -- the engine's determinant telescopes
  have hdet := QMCLeafB.EngineIterates.Aat_det_ge (n := G.n * G.n) hN
    (initShape_posDef G P) (ceilShape_wit G P hn c hc)
    (fun k => P.hrmax) (fun k => hc k) P.hrmax (fun k => le_refl _) (P.K * P.m)
  have hdetpos : (0 : ℝ) < (QMCLeafB.EngineIterates.castM
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).det := (initShape_posDef G P).det_pos
  have hr2 : (0 : ℝ) < r ^ (2 * (G.n * G.n)) := by positivity
  have hmono : (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).det
        * (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((P.rmax : ℚ) : ℝ)) ^ (P.K * P.m)
        * r ^ (2 * (G.n * G.n))
      ≤ (QMCLeafB.EngineIterates.castM (ceilShape G P hn c hc (P.K * P.m))).det
        * r ^ (2 * (G.n * G.n)) := by
    have h2 : (0 : ℝ) ≤ r ^ (2 * (G.n * G.n)) := hr2.le
    exact mul_le_mul_of_nonneg_right hdet h2
  have h1 : (QMCLeafB.EngineIterates.castM (ceilShape G P hn c hc (P.K * P.m))).det
      * r ^ (2 * (G.n * G.n)) ≤ 1 := by
    rw [mul_comm ((QMCLeafB.EngineIterates.castM
      (ceilShape G P hn c hc (P.K * P.m))).det) (r ^ (2 * (G.n * G.n)))]
    exact hfloor
  have hchain : (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).det
        * (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((P.rmax : ℚ) : ℝ)) ^ (P.K * P.m)
        * r ^ (2 * (G.n * G.n)) ≤ 1 := le_trans hmono h1
  exact absurd hK (not_lt.mpr hchain)

#print axioms QMCLeafB.DC35M1.not_shallowCut_of_ball_horizon

end QMCLeafB.DC35M1


