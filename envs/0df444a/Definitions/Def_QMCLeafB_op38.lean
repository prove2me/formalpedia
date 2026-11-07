-- Prove2me | Definitions.Def_QMCLeafB_op38
-- name    : QMCLeafB_op38
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:45:38.202568+00:00
-- url     : https://prove2.me/theorems/00c7ea71-e4ff-4626-b625-8749206d92ea
-- title:
--   QMCLeafB op38
-- statement:
--   # `Check_op38_m8` — phase 38, member m8, direction `other-programme`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_EngineIterates
import Definitions.Def_QMCLeafB_boundary_m2
import Definitions.Def_QMCLeafB_final_stroke_m7
/-
# `Check_op38_m8` — phase 38, member m8, direction `other-programme`

## The decision

**The leaf's one inequality is decided exactly, and it is not a bounded-distance statement.**
With `A` the current shape, `a` the accumulated centre (`Cat k`), `c = A p` the cut normal and
`σ = c ⬝ᵥ p = ‖c‖²_{A⁻¹}` (`sigmaQ` in the engine's exact form), the per-round obligation

    sup_{z ∈ body} c ⬝ᵥ (a − z) ≤ r √σ                                          (`Shallow A a K r`)

is **equivalent** to a single geometric condition (§10, `criterion_iff`):

    `Shallow A a K r`  ⟺  some point of the closed `A`-ball of radius `r` about `a` lies outside the
                            body's interior.

So the round is unrecordable **iff the body swallows that ball** — an `A`-ball / interior condition,
with no distance, steering or trajectory content.  The two halves are proved separately:

* §10 `not_shallow_of_ball_interior`: if the closed `A`-ball of radius `r` sits in `int K`, no normal
  works (nudge the extremal point `a − (r/√σ)p` slightly along `−p`; openness keeps it in the body and
  it strictly beats `r√σ`).
* §9/§10 `shallow_of_escape` / `shallow_of_interior_escape`: a point of the complement (or of the
  boundary) within `A`-distance `r` gives an explicit normal — the opposite of a separating
  functional — with margin `r`, via the `A`-Cauchy–Schwarz `qf_cauchy`
  `(c ⬝ᵥ v)² ≤ (c ⬝ᵥ p)(v ⬝ᵥ A v)`.
* §3 `not_shallow_of_ball` is the cruder strict version (`r' > r`) that needs no interior.

Consequences, all machine-checked:

* §5 `not_shallow_ellipsoid` / `verdict_two_dim`: the *current ellipsoid itself* (an admissible body by
  `body_containment`) is unrecordable at its own centre for every `r < 1` — in particular at `n = 2`,
  `r = rmax = 1/16`.  So no cut sequence satisfies the phase-37 sentence "the ellipsoid centre stays
  within `rmax` of the body in the `A_k`-norm": that sentence is strictly stronger than the record.
* §6 `slab_shallow_every_centre` (thin slab, EVERY centre) and `far_body_shallow` (a body at distance
  10 from the origin, `rmax = 1/16`): the same margin is available arbitrarily far away.  Only being
  *deep inside* the body is forbidden.
* §7 `runParts_shallow_zero`: the leaf's own `RunParts` at `k = 0` **is** `Shallow` with margin
  `P.rmax` (the fields `hwit/hcut/hcheck/hle` and nothing else), so
  `no_runParts_of_ball_rmax`: a body carrying the `A₀`-ball of radius `> P.rmax` at the initial centre
  admits NO all-cut record at all — for every program bit and every cut sequence.
* §8 `collar_silent_two`: the campaign's collar inradius bound `dq/24` is far below the `A₀`-ball's
  radius `√(8+2dq²)/16`, so the obstruction is SILENT on the whole collar: round 0 is free there.

## What this means for the leaf

`SelfRec` needs, per round, only that the body does not swallow the `A_k`-ball of radius `rmax` about
`Cat k`.  On the collar (Euclidean inradius `≤ dq/24`, hence `≤ 3·10⁻¹⁶⁰⁶³⁹` on m7's surviving slab)
that ball cannot be swallowed while the current ellipsoid stays long compared with the body's thin
direction, and `shallow_of_thin` then exhibits the normal with `del = 0` whenever `Cat k ∉ K`.  The
open content is therefore the *shape* recursion (does `A_k` stay long enough for `K · m` rounds?), not
any distance/steering trade-off.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
every `#print axioms` below is exactly `[propext, Classical.choice, Quot.sound]`.
Imports: `Mathlib` + published `Definitions.Def_QMCLeafB_{EngineIterates, boundary_m2,
final_stroke_m7}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

open Matrix

noncomputable section

namespace QMCLeafB.Crit38M8

open QMCLeafB.EngineIterates

variable {n : ℕ}

/-! ## 1.  σ > 0 from the engine's own witness relation -/

theorem sigma_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {c p : Fin n → ℝ} (hAp : A *ᵥ p = c) (hc : c ≠ 0) : 0 < c ⬝ᵥ p := by
  have hp : p ≠ 0 := by
    intro h
    apply hc
    rw [← hAp, h, Matrix.mulVec_zero]
  rw [← hAp, dotProduct_comm]
  exact posDef_apply_pos hA hp

/-- A nonzero normal has a nonzero witness. -/
theorem witness_ne {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {c p : Fin n → ℝ} (hAp : A *ᵥ p = c) (hc : c ≠ 0) : p ≠ 0 := by
  intro h
  apply hc
  rw [← hAp, h, Matrix.mulVec_zero]

/-- The normal is nonzero when the witness is. -/
theorem normal_ne {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {p : Fin n → ℝ} (hp : p ≠ 0) : A *ᵥ p ≠ 0 := by
  intro h
  have h0 : p ⬝ᵥ (A *ᵥ p) = 0 := by rw [h, dotProduct_zero]
  exact absurd h0 (ne_of_gt (posDef_apply_pos hA hp))

#print axioms QMCLeafB.Crit38M8.sigma_pos

#print axioms QMCLeafB.Crit38M8.witness_ne

#print axioms QMCLeafB.Crit38M8.normal_ne

/-! ## 2.  The obligation, in the engine's `(c, p)` witness form -/

/-- **The one inequality of leaf B, per round.**  `c = A p` is the cut normal, `σ = c ⬝ᵥ p` is
`‖c‖²_{A⁻¹}` in the engine's exact form (`sigmaQ`), and the body `K` must lie within `r √σ` of the
accumulated centre `a` on the far side of the normal: `sup_{z ∈ K} c ⬝ᵥ (a - z) ≤ r √σ`. -/
def Shallow (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (K : Set (Fin n → ℝ)) (r : ℝ) : Prop :=
  ∃ c p : Fin n → ℝ, A *ᵥ p = c ∧ c ≠ 0 ∧ ∀ z ∈ K, c ⬝ᵥ (a - z) ≤ r * Real.sqrt (c ⬝ᵥ p)

/-! ## 3.  THE FAILURE MODE — a ball of `A`-radius `> r` at the centre kills EVERY normal -/

theorem not_shallow_of_ball {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {K : Set (Fin n → ℝ)} {a : Fin n → ℝ} {r ρ : ℝ} (hρ : 0 ≤ ρ) (hlt : ρ < r)
    (hball : ∀ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ r ^ 2 → a + v ∈ K) :
    ¬ Shallow A a K ρ := by
  rintro ⟨c, p, hAp, hc, hsh⟩
  have hσ : 0 < c ⬝ᵥ p := sigma_pos hA hAp hc
  have hp : p ≠ 0 := witness_ne hA hAp hc
  set s : ℝ := Real.sqrt (c ⬝ᵥ p) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr hσ
  have hs2 : s * s = c ⬝ᵥ p := by rw [hsdef]; exact Real.mul_self_sqrt hσ.le
  set k : ℝ := -(r / s) with hkdef
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hkey : k * (k * (s * s)) = r ^ 2 := by
    rw [hkdef]; field_simp
  have hkey2 : -(k * (s * s)) = r * s := by
    rw [hkdef]; field_simp
  have hmem : a + k • p ∈ K := by
    apply hball
    have hmv : A *ᵥ (k • p) = k • c := by rw [Matrix.mulVec_smul, hAp]
    have h1 : (k • p) ⬝ᵥ (A *ᵥ (k • p)) = k * (k * (c ⬝ᵥ p)) := by
      rw [hmv, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm p c]
    rw [h1, ← hs2, hkey]
  have hval : c ⬝ᵥ (a - (a + k • p)) = r * s := by
    have hsub : a - (a + k • p) = -(k • p) := by abel
    rw [hsub, dotProduct_neg, dotProduct_smul, smul_eq_mul, ← hs2, hkey2]
  have hfin := hsh _ hmem
  rw [hval, hsdef] at hfin
  nlinarith [hfin, hspos, hρ, hlt]

#print axioms QMCLeafB.Crit38M8.not_shallow_of_ball

/-! ## 4.  THE FREE CASE — a body thin in one `A`-direction can be recorded at EVERY centre -/

theorem shallow_of_thin {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {K : Set (Fin n → ℝ)} (a : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r)
    {p : Fin n → ℝ} (hp : p ≠ 0)
    (hthin : ∀ z₁ ∈ K, ∀ z₂ ∈ K,
      (A *ᵥ p) ⬝ᵥ (z₁ - z₂) ≤ 2 * r * Real.sqrt (p ⬝ᵥ (A *ᵥ p))) :
    Shallow A a K r := by
  set c : Fin n → ℝ := A *ᵥ p with hcdef
  have hcne : c ≠ 0 := normal_ne hA hp
  have hsig : c ⬝ᵥ p = p ⬝ᵥ (A *ᵥ p) := by rw [hcdef, dotProduct_comm]
  have hσpos : 0 < c ⬝ᵥ p := by
    rw [hsig]; exact posDef_apply_pos hA hp
  set s : ℝ := Real.sqrt (c ⬝ᵥ p) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr hσpos
  have hsp : Real.sqrt (p ⬝ᵥ (A *ᵥ p)) = s := by rw [← hsig, hsdef]
  by_cases hcase : ∀ z ∈ K, c ⬝ᵥ (a - z) ≤ r * s
  · refine ⟨c, p, hcdef.symm ▸ rfl, hcne, ?_⟩
    intro z hz
    rw [← hsdef]
    exact hcase z hz
  · push Not at hcase
    obtain ⟨z₁, hz₁, hgt⟩ := hcase
    have hspq : Real.sqrt (p ⬝ᵥ (A *ᵥ p)) = s := hsp
    refine ⟨-c, -p, ?_, ?_, ?_⟩
    · rw [Matrix.mulVec_neg, ← hcdef]
    · simpa using hcne
    · intro z hz
      have e1 : (-c) ⬝ᵥ (a - z) = c ⬝ᵥ (z - a) := by
        rw [neg_dotProduct, ← dotProduct_neg]
        congr 1
        abel
      have e2 : z - a = (z - z₁) + (z₁ - a) := by abel
      have hsplit : (-c) ⬝ᵥ (a - z) = c ⬝ᵥ (z - z₁) + c ⬝ᵥ (z₁ - a) := by
        rw [e1, e2, dotProduct_add]
      rw [hsplit]
      have ht : c ⬝ᵥ (z - z₁) ≤ 2 * r * s := by
        have := hthin z hz z₁ hz₁
        rw [hspq] at this
        linarith
      have hz1 : c ⬝ᵥ (z₁ - a) < -(r * s) := by
        have h1 : c ⬝ᵥ (z₁ - a) = -(c ⬝ᵥ (a - z₁)) := by
          rw [show z₁ - a = -(a - z₁) from by abel, dotProduct_neg]
        rw [h1]; linarith
      have hrhs : r * Real.sqrt ((-c) ⬝ᵥ (-p)) = r * s := by
        have hcc : (-c) ⬝ᵥ (-p) = c ⬝ᵥ p := by
          simp only [dotProduct_neg, neg_dotProduct, neg_neg]
        rw [hcc, hsdef]
      rw [hrhs]
      linarith

#print axioms QMCLeafB.Crit38M8.shallow_of_thin

/-! ## 5.  THE VERDICT — the current ellipsoid is never recordable at its own centre -/

/-- **The unit `A`-ball about `a` (i.e. the engine's own ellipsoid) kills every normal at its own
centre** as soon as `r < 1`.  Since `body_containment` allows the body to *be* the ellipsoid, this is
a legal instance of the leaf's obligation: the inequality is FALSE there, for every cut sequence and
every choice of normal. -/
theorem not_shallow_ellipsoid {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (a : Fin n → ℝ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : ¬ Shallow A a (Ell A a) r := by
  refine not_shallow_of_ball hA hr0 hr1 ?_
  intro v hv
  have hsub : a + v - a = v := by abel
  simp only [Ell, Set.mem_ofPred_eq, hsub]
  simpa using hv

#print axioms QMCLeafB.Crit38M8.not_shallow_ellipsoid

/-- `rmax = 1/(4·(n·n)) ≤ 1/4 < 1` at `n = 2`, so the campaign radius is inside the hypothesis. -/
theorem rmax_two_dim_lt_one : (1 / 16 : ℝ) < 1 := by norm_num

/-- **THE DECIDED INSTANCE (n = 2, `rmax = 1/16`).**  At the unit disc, every normal and every cut
sequence fails the leaf's inequality at round 0.  `1/16 = rmaxOf (2·2)`. -/
theorem verdict_two_dim :
    ¬ Shallow (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Fin 2 → ℝ) (Ell (1 : Matrix (Fin 2) (Fin 2) ℝ) 0)
      (1 / 16) :=
  not_shallow_ellipsoid (Matrix.PosDef.one) 0 (by norm_num) (by norm_num)

#print axioms QMCLeafB.Crit38M8.verdict_two_dim

/-! ## 6.  THE FREE REGIME — thin bodies are recordable at EVERY centre -/

/-- The thin slab `|z 1| ≤ 1/100` in `Fin 2`. -/
def slab : Set (Fin 2 → ℝ) := {z | |z 1| ≤ 1 / 100}

/-- **A body thin in ONE direction is recordable at EVERY centre, with margin `r = rmax`.**  No
distance hypothesis: the centre may be anywhere, inside or outside.  This is the regime the collar
sits in while the current ellipsoid stays long compared with the body's thin direction. -/
theorem slab_shallow_every_centre (a : Fin 2 → ℝ) :
    Shallow (1 : Matrix (Fin 2) (Fin 2) ℝ) a slab (1 / 16) := by
  have hA : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef := Matrix.PosDef.one
  have hp : (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
  refine shallow_of_thin hA a (by norm_num) hp ?_
  intro z₁ h₁ z₂ h₂
  simp only [slab, Set.mem_ofPred_eq, Matrix.one_mulVec] at *
  have h1 : z₁ 1 - z₂ 1 ≤ 1 / 100 + 1 / 100 := by
    have ha := abs_le.mp h₁
    have hb := abs_le.mp h₂
    linarith [ha.1, ha.2, hb.1, hb.2]
  have hdot : (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) ⬝ᵥ (z₁ - z₂) = z₁ 1 - z₂ 1 := by
    simp [dotProduct, Pi.sub_apply]
  have hpp : (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) ⬝ᵥ (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) = 1 := by
    simp [dotProduct]
  rw [hdot, hpp, Real.sqrt_one]
  linarith

#print axioms QMCLeafB.Crit38M8.slab_shallow_every_centre

/-- A body FAR from the centre (`z 0 ∈ [10, 10 + 1/100]`, `|z 1| ≤ 1`) is recordable at the
origin with `rmax` margin — the centre is at distance `10`, far beyond `rmax`.  So the obligation is
NOT a bounded-distance statement. -/
theorem far_body_shallow :
    Shallow (1 : Matrix (Fin 2) (Fin 2) ℝ) 0
      {z : Fin 2 → ℝ | 10 ≤ z 0 ∧ z 0 ≤ 10 + 1 / 100 ∧ |z 1| ≤ 1} (1 / 16) := by
  refine ⟨Pi.single 0 (1 : ℝ), Pi.single 0 (1 : ℝ), ?_, ?_, ?_⟩
  · show (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ Pi.single 0 (1 : ℝ) = Pi.single 0 (1 : ℝ)
    rw [Matrix.one_mulVec]
  · intro h
    have := congrFun h 0
    simp at this
  · intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    have hdot : (Pi.single 0 (1 : ℝ) : Fin 2 → ℝ) ⬝ᵥ
        ((0 : Fin 2 → ℝ) - z) = -z 0 := by
      simp [dotProduct, Pi.sub_apply]
    have hpp : (Pi.single 0 (1 : ℝ) : Fin 2 → ℝ) ⬝ᵥ (Pi.single 0 (1 : ℝ) : Fin 2 → ℝ) = 1 := by
      simp [dotProduct]
    rw [hdot, hpp, Real.sqrt_one]
    linarith

#print axioms QMCLeafB.Crit38M8.far_body_shallow

/-! ## 7.  THE RECORD-LEVEL VERDICT — the leaf's own `RunParts` forces the obligation at round 0 -/

/-- **`RunParts` ⟹ `Shallow` at round 0.**  The record's `hwit`/`hcut`/`hcheck`/`hle` at `k = 0` are
*exactly* the shallow-cut obligation at the accumulated centre `Cat 0 = 0` with margin `P.rmax`:
`del 0 ≥ sup_{z ∈ relaxBall} c₀ ⬝ᵥ (0 − z)` and `del 0 ≤ rho 0 √σ₀ ≤ rmax √σ₀`.  Nothing else in
the record is used. -/
theorem runParts_shallow_zero {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) (hkm : 0 < P.K * P.m)
    (hok0 : B.ok 0 = false) :
    Shallow (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)))
      (0 : Fin (G.n * G.n) → ℝ)
      (QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (P.dq : ℝ)
        ((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ) : ℝ))
      (P.rmax : ℝ) := by
  refine ⟨fun i => ((B.cd 0).c i : ℝ), fun i => ((B.cd 0).p i : ℝ), ?_, ?_, ?_⟩
  · have hw := B.hwit 0 hkm hok0
    have hcast := QMCLeafB.EngineIterates.cast_mulVec
      (QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))
        B.cd 0) (B.cd 0).p
    have hA0 : QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd 0
        = QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2) := rfl
    rw [hA0] at hcast hw
    rw [hw] at hcast
    exact hcast
  · intro h
    have hcne := B.hcne 0 hkm hok0
    apply hcne
    funext i
    have hi := congrFun h i
    simpa using hi
  · intro z hz
    have hcut := B.hcut 0 hkm hok0 z hz
    have hdel : (0 : ℝ) ≤ ((B.del 0 : ℚ) : ℝ) := by exact_mod_cast B.hdel0 0 hkm hok0
    have hrho : (0 : ℝ) ≤ (((B.cd 0).rho : ℚ) : ℝ) := by exact_mod_cast B.hrho 0 hkm hok0
    have hcheck : ((B.del 0 : ℚ) : ℝ) ^ 2
        ≤ (((B.cd 0).rho : ℚ) : ℝ) ^ 2
          * ((QMCLeafB.EngineIterates.sigmaQ (B.cd 0).c (B.cd 0).p : ℚ) : ℝ) := by
      exact_mod_cast B.hcheck 0 hkm hok0
    have hle : (((B.cd 0).rho : ℚ) : ℝ) ≤ (P.rmax : ℝ) := by
      exact_mod_cast B.hle 0 hkm hok0
    have hσ : ((QMCLeafB.EngineIterates.sigmaQ (B.cd 0).c (B.cd 0).p : ℚ) : ℝ)
        = (fun i => ((B.cd 0).c i : ℝ)) ⬝ᵥ (fun i => ((B.cd 0).p i : ℝ)) := by
      rw [QMCLeafB.EngineIterates.cast_sigmaQ]; rfl
    have hstep : ((B.del 0 : ℚ) : ℝ)
        ≤ ((B.cd 0).rho : ℝ) * Real.sqrt
            ((QMCLeafB.EngineIterates.sigmaQ (B.cd 0).c (B.cd 0).p : ℚ) : ℝ) := by
      calc ((B.del 0 : ℚ) : ℝ) = Real.sqrt (((B.del 0 : ℚ) : ℝ) ^ 2) :=
            (Real.sqrt_sq hdel).symm
        _ ≤ Real.sqrt ((((B.cd 0).rho : ℚ) : ℝ) ^ 2
              * ((QMCLeafB.EngineIterates.sigmaQ (B.cd 0).c (B.cd 0).p : ℚ) : ℝ)) :=
            Real.sqrt_le_sqrt hcheck
        _ = ((B.cd 0).rho : ℝ) * Real.sqrt
              ((QMCLeafB.EngineIterates.sigmaQ (B.cd 0).c (B.cd 0).p : ℚ) : ℝ) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hrho]
    have hfin : ((B.del 0 : ℚ) : ℝ) ≤ (P.rmax : ℝ) * Real.sqrt
        ((QMCLeafB.EngineIterates.sigmaQ (B.cd 0).c (B.cd 0).p : ℚ) : ℝ) :=
      hstep.trans (mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _))
    have hneg : (fun i => ((B.cd 0).c i : ℝ)) ⬝ᵥ
        ((0 : Fin (G.n * G.n) → ℝ) - z)
        = -((fun i => ((B.cd 0).c i : ℝ)) ⬝ᵥ z) := by
      rw [show (0 : Fin (G.n * G.n) → ℝ) - z = -z from by abel, dotProduct_neg]
    rw [hσ] at hfin
    rw [hneg]
    -- `hcut : -del ≤ c ⬝ᵥ z`
    have hz' : ((fun i => ((B.cd 0).c i : ℝ)) ⬝ᵥ z)
        = (QMCLeafB.EngineIterates.cutCR B.cd 0) ⬝ᵥ
            (z - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd 0) := by
      rw [show QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd 0
          = 0 from rfl]
      rw [show z - (0 : Fin (G.n * G.n) → ℝ) = z from by abel]
    rw [hz']
    linarith [hcut, hfin]

#print axioms QMCLeafB.Crit38M8.runParts_shallow_zero


/-- **THE LEAF-LEVEL FAILURE MODE.**  If the run's relaxation carries the initial ellipsoid's
`A₀`-ball of radius `r > P.rmax` about the initial centre `0`, then NO all-cut record exists at that
input — for every program bit and every cut sequence.  (`body_containment` permits the body to be a
ball, so this is an admissible instance.) -/
theorem no_runParts_of_ball_rmax {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {r : ℝ} (hr : (P.rmax : ℝ) < r)
    (hball : ∀ v : Fin (G.n * G.n) → ℝ,
      v ⬝ᵥ ((QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))) *ᵥ v) ≤ r ^ 2 →
      (0 : Fin (G.n * G.n) → ℝ) + v ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (P.dq : ℝ)
        ((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ) : ℝ)) :
    ∀ (B : QMCLeafB.FinalStroke.RunParts o G t P), 0 < P.K * P.m → B.ok 0 = false → False := by
  intro B hkm hok0
  have hM : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 := by
    have := P.hdq; positivity
  have hA : (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
      (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).PosDef :=
    QMCLeafB.Boundary.initShapeOf_cast_posDef hM
  have hρ : (0 : ℝ) ≤ (P.rmax : ℝ) := by exact_mod_cast P.hrmax
  exact not_shallow_of_ball hA hρ hr hball (runParts_shallow_zero B hkm hok0)

/-- **COLLAR SILENCE (n = 2).**  The campaign's collar body has Euclidean inradius `≤ dq/24`
(`Cov36M7.ball_radius_le_slack`), while the `A₀`-ball of radius `rmax = 1/16` at the initial centre is
a Euclidean ball of radius `√(8 + 2dq²)/16`.  For every `0 < dq ≤ 1` the collar's bound is far below
it, so the round-0 obstruction `no_runParts_of_ball_rmax` is **SILENT on the whole collar**: the
obligation is satisfiable at round 0 there for every cut sequence's first normal. -/
theorem collar_silent_two {dq : ℝ} (hdq0 : 0 < dq) (hdq1 : dq ≤ 1) :
    dq / 24 < (1 / 16) * Real.sqrt (8 + 2 * dq ^ 2) := by
  have hmono : Real.sqrt 8 ≤ Real.sqrt (8 + 2 * dq ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg dq]
  have hs8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
  have h2 : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  have h1 : dq / 24 ≤ 1 / 24 := by linarith
  nlinarith [hmono, hs8, h2, h1]

#print axioms QMCLeafB.Crit38M8.collar_silent_two

#print axioms QMCLeafB.Crit38M8.no_runParts_of_ball_rmax


/-! ## 9.  THE COMPLEMENTARY HALF — a point of the complement within `A`-distance `r` suffices -/

theorem qf_expand {A : Matrix (Fin n) (Fin n) ℝ} (t : ℝ) (v p : Fin n → ℝ) :
    (v - t • p) ⬝ᵥ (A *ᵥ (v - t • p))
      = v ⬝ᵥ (A *ᵥ v) - t * (v ⬝ᵥ (A *ᵥ p)) - t * (p ⬝ᵥ (A *ᵥ v))
        + t * (t * (p ⬝ᵥ (A *ᵥ p))) := by
  have hmv : A *ᵥ (v - t • p) = A *ᵥ v - t • (A *ᵥ p) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [hmv, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- **Cauchy–Schwarz in the `A`-form.** -/
theorem qf_cauchy {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {c p : Fin n → ℝ} (hAp : A *ᵥ p = c) (v : Fin n → ℝ) :
    (c ⬝ᵥ v) ^ 2 ≤ (c ⬝ᵥ p) * (v ⬝ᵥ (A *ᵥ v)) := by
  have hsym : Aᵀ = A := by
    have h := hA.isHermitian.eq
    simpa using h
  have hpAv : p ⬝ᵥ (A *ᵥ v) = c ⬝ᵥ v := by
    have h1 := dotProduct_transpose_mulVec (A := A) (x := v) (y := p)
    rw [hsym] at h1
    rw [← h1, hAp, dotProduct_comm v c]
  have hnonneg : ∀ t : ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v) - 2 * t * (c ⬝ᵥ v) + t ^ 2 * (c ⬝ᵥ p) := by
    intro t
    have h := qf_expand (A := A) t v p
    rw [hpAv, hAp, dotProduct_comm v c, dotProduct_comm p c] at h
    have hq : 0 ≤ (v - t • p) ⬝ᵥ (A *ᵥ (v - t • p)) := by
      by_cases h0 : v - t • p = 0
      · simp [h0]
      · exact (hA.dotProduct_mulVec_pos h0).le
    rw [h] at hq
    nlinarith [hq]
  by_cases hc : c = 0
  · rw [hc]; simp
  · have hσ : 0 < c ⬝ᵥ p := by
      rw [← hAp, dotProduct_comm]
      refine hA.dotProduct_mulVec_pos ?_
      intro h
      rw [h, Matrix.mulVec_zero] at hAp
      exact hc hAp.symm
    have hkey := hnonneg ((c ⬝ᵥ p)⁻¹ * (c ⬝ᵥ v))
    have hsne : c ⬝ᵥ p ≠ 0 := ne_of_gt hσ
    have hid : (c ⬝ᵥ p)⁻¹ * (c ⬝ᵥ v) * ((c ⬝ᵥ p)⁻¹ * (c ⬝ᵥ v)) * (c ⬝ᵥ p)
        = (c ⬝ᵥ p)⁻¹ * (c ⬝ᵥ v) ^ 2 := by
      field_simp
    have h2 : 0 ≤ (c ⬝ᵥ p) * (v ⬝ᵥ (A *ᵥ v) - 2 * ((c ⬝ᵥ p)⁻¹ * (c ⬝ᵥ v)) * (c ⬝ᵥ v)
        + ((c ⬝ᵥ p)⁻¹ * (c ⬝ᵥ v)) ^ 2 * (c ⬝ᵥ p)) := mul_nonneg hσ.le hkey
    have h3 : (c ⬝ᵥ p) * (v ⬝ᵥ (A *ᵥ v) - 2 * ((c ⬝ᵥ p)⁻¹ * (c ⬝ᵥ v)) * (c ⬝ᵥ v)
        + ((c ⬝ᵥ p)⁻¹ * (c ⬝ᵥ v)) ^ 2 * (c ⬝ᵥ p))
        = (c ⬝ᵥ p) * (v ⬝ᵥ (A *ᵥ v)) - (c ⬝ᵥ v) ^ 2 := by
      field_simp
      ring
    rw [h3] at h2
    linarith [h2]


/-- **THE ESCAPE SUFFICIENCY.**  If the body `K` has a point outside it within `A`-distance `r` of the
centre `a`, then the round is recordable with margin `r` — with the explicit normal `-c` of a
separating functional.  Together with `not_shallow_of_ball` this pins the obligation to the `A`-ball of
radius exactly `r` around the centre. -/
theorem shallow_of_escape {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {K : Set (Fin n → ℝ)} (hKc : Convex ℝ K) (hKcl : IsClosed K) (hne : K.Nonempty)
    (a : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) {v : Fin n → ℝ}
    (hv : v ⬝ᵥ (A *ᵥ v) ≤ r ^ 2) (hout : a + v ∉ K) :
    Shallow A a K r := by
  obtain ⟨f, u, hlt, hlt2⟩ := geometric_hahn_banach_closed_point hKc hKcl hout
  set c : Fin n → ℝ := fun i => f (Pi.single i (1 : ℝ)) with hc
  have hf_eq : ∀ x : Fin n → ℝ, f x = c ⬝ᵥ x := by
    intro x
    have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ]
    conv_lhs => rw [hx]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct, hc]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨z₀, hz₀⟩ := hne
  have hcne : c ≠ 0 := by
    intro h
    have h1 := hlt z₀ hz₀
    rw [hf_eq, h] at h1
    simp at h1
    have h2 : (0 : ℝ) < u := by linarith
    have h3 : f (a + v) = 0 := by rw [hf_eq, h]; simp
    linarith
  have hsym : Aᵀ = A := by
    have h := hA.isHermitian.eq
    simpa using h
  set p : Fin n → ℝ := A⁻¹ *ᵥ c with hp
  have hAp : A *ᵥ p = c := by
    rw [hp, Matrix.mulVec_mulVec, QMCLeafB.EngineIterates.mul_inv_of_posDef hA,
      Matrix.one_mulVec]
  have hσpos : 0 < c ⬝ᵥ p := by
    rw [← hAp, dotProduct_comm]
    refine QMCLeafB.EngineIterates.posDef_apply_pos hA ?_
    intro h
    rw [h, Matrix.mulVec_zero] at hAp
    exact hcne hAp.symm
  have hcs : (c ⬝ᵥ v) ^ 2 ≤ (c ⬝ᵥ p) * (v ⬝ᵥ (A *ᵥ v)) := qf_cauchy hA hAp v
  have hbound : c ⬝ᵥ v ≤ r * Real.sqrt (c ⬝ᵥ p) := by
    have h1 : (c ⬝ᵥ v) ^ 2 ≤ (c ⬝ᵥ p) * r ^ 2 := by
      have h2 : (c ⬝ᵥ p) * (v ⬝ᵥ (A *ᵥ v)) ≤ (c ⬝ᵥ p) * r ^ 2 :=
        mul_le_mul_of_nonneg_left hv hσpos.le
      linarith [hcs, h2]
    have h3 : Real.sqrt ((c ⬝ᵥ v) ^ 2) ≤ Real.sqrt ((c ⬝ᵥ p) * r ^ 2) :=
      Real.sqrt_le_sqrt h1
    have h5 : Real.sqrt ((c ⬝ᵥ p) * r ^ 2) = Real.sqrt (c ⬝ᵥ p) * r := by
      rw [Real.sqrt_mul hσpos.le, Real.sqrt_sq hr]
    have h6 : Real.sqrt ((c ⬝ᵥ v) ^ 2) = |c ⬝ᵥ v| := Real.sqrt_sq_eq_abs (c ⬝ᵥ v)
    rw [h6, h5] at h3
    have h4 : |c ⬝ᵥ v| ≤ r * Real.sqrt (c ⬝ᵥ p) := by
      rw [mul_comm]; exact h3
    linarith [le_abs_self (c ⬝ᵥ v), h4]
  refine ⟨-c, -p, ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_neg, hAp]
  · simpa using hcne
  · intro z hz
    have h1 : f z < u := hlt z hz
    have h2 : u < f (a + v) := hlt2
    have hfz : f (a - z) = f a - f z := by
      have : a - z = a + -z := by abel
      rw [this, map_add, map_neg]
      ring
    have hfa : f (a + v) = f a + f v := map_add f a v
    have hkey : c ⬝ᵥ (a - z) > -(f v) := by
      rw [← hf_eq, hfz]
      linarith [h1, hfa, h2]
    have hfv : f v = c ⬝ᵥ v := hf_eq v
    have hneg : (-c) ⬝ᵥ (a - z) = -(c ⬝ᵥ (a - z)) := neg_dotProduct c (a - z)
    have hcc : (-c) ⬝ᵥ (-p) = c ⬝ᵥ p := by
      simp only [dotProduct_neg, neg_dotProduct, neg_neg]
    rw [hneg, hcc]
    have h2' : c ⬝ᵥ (a - z) > -(c ⬝ᵥ v) := by rw [← hfv]; exact hkey
    linarith [h2', hbound]



#print axioms QMCLeafB.Crit38M8.qf_cauchy

#print axioms QMCLeafB.Crit38M8.shallow_of_escape

/-- **THE CRITERION, packaged.**  For a closed convex body, the round's obligation at margin `r`:
* HOLDS whenever some point of the complement is within `A`-distance `r` of the centre;
* FAILS for every normal whenever the closed `A`-ball of radius `r' > r` sits inside the body.
The two hypotheses are the two sides of the `A`-ball of radius `r` about the centre, so the
obligation is pinned to that ball: the record forbids the centre being *deep inside* the body in the
current metric, and nothing else. -/
theorem criterion {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {K : Set (Fin n → ℝ)} (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKne : K.Nonempty)
    (a : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ((∃ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ r ^ 2 ∧ a + v ∉ K) → Shallow A a K r)
    ∧ (∀ r' : ℝ, r < r' → (∀ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ r' ^ 2 → a + v ∈ K) →
        ¬ Shallow A a K r) :=
  ⟨fun ⟨v, hv, hout⟩ => shallow_of_escape hA hKc hKcl hKne a hr hv hout,
   fun r' hr' hball => not_shallow_of_ball hA hr hr' hball⟩

#print axioms QMCLeafB.Crit38M8.criterion


/-! ## 10.  THE EXACT CRITERION — the closed `A`-ball of radius `r` against the body's interior -/

/-- **NECESSITY, sharpened to the interior.**  If the *closed* `A`-ball of radius `r` about `a` sits in
the INTERIOR of the body, no normal records the round at margin `r`.  The proof only uses the openness
of the interior at the extremal body point `a − (r/√σ)p`: nudging slightly further along `−p` keeps the
point in the body and strictly beats `r√σ`. -/
theorem not_shallow_of_ball_interior {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {K : Set (Fin n → ℝ)} {a : Fin n → ℝ} {r : ℝ}
    (hball : ∀ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ r ^ 2 → a + v ∈ interior K) :
    ¬ Shallow A a K r := by
  rintro ⟨c, p, hAp, hc, hsh⟩
  have hσ : 0 < c ⬝ᵥ p := sigma_pos hA hAp hc
  have hp : p ≠ 0 := witness_ne hA hAp hc
  set s : ℝ := Real.sqrt (c ⬝ᵥ p) with hs
  have hs2 : s * s = c ⬝ᵥ p := by rw [hs]; exact Real.mul_self_sqrt hσ.le
  have hspos : 0 < s := Real.sqrt_pos.mpr hσ
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hnorm : (-(r / s) • p) ⬝ᵥ (A *ᵥ (-(r / s) • p)) = r ^ 2 := by
    have hmv : A *ᵥ (-(r / s) • p) = (-(r / s)) • c := by
      rw [Matrix.mulVec_smul, hAp]
    have h1 : (-(r / s) • p) ⬝ᵥ (A *ᵥ (-(r / s) • p))
        = (-(r / s)) * ((-(r / s)) * (p ⬝ᵥ c)) := by
      rw [hmv, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [h1, dotProduct_comm p c, ← hs2]
    field_simp
  have hz0 : a + (-(r / s) • p) ∈ interior K := hball _ hnorm.le
  obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.mp isOpen_interior _ hz0
  have hpn : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  set t : ℝ := ε / (2 * ‖p‖) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have htε : ‖t • p‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht]
    have h2 : ε / (2 * ‖p‖) * ‖p‖ = ε / 2 := by field_simp
    rw [h2]; linarith
  have hz1 : a + (-(r / s) • p - t • p) ∈ interior K := by
    apply hεb
    rw [Metric.mem_ball, dist_eq_norm]
    have he : (a + (-(r / s) • p - t • p)) - (a + (-(r / s) • p)) = -(t • p) := by abel
    rw [he, norm_neg]; exact htε
  have hval : c ⬝ᵥ (a - (a + (-(r / s) • p - t • p))) = r * s + t * (c ⬝ᵥ p) := by
    have hsub : a - (a + (-(r / s) • p - t • p)) = -((-(r / s) • p - t • p)) := by abel
    rw [hsub, dotProduct_neg, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, ← hs2]
    field_simp
    ring
  have hkey := hsh _ (interior_subset hz1)
  rw [hval] at hkey
  have hts : 0 < t * (c ⬝ᵥ p) := mul_pos htpos hσ
  have hlt : r * s < r * s + t * (c ⬝ᵥ p) := by linarith
  exact absurd hkey (not_le.mpr hlt)

#print axioms QMCLeafB.Crit38M8.not_shallow_of_ball_interior


/-- **THE SUFFICIENCY, sharpened to the boundary.**  If a point of the closed `A`-ball of radius `r`
about `a` is outside the body's interior, the round IS recordable with margin `r`: separate that point
from the body by its supporting hyperplane (`geometric_hahn_banach_of_nonempty_interior_point`) and take
the opposite normal, exactly as in `shallow_of_escape`. -/
theorem shallow_of_interior_escape {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {K : Set (Fin n → ℝ)} (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
    (a : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) {v : Fin n → ℝ}
    (hv : v ⬝ᵥ (A *ᵥ v) ≤ r ^ 2) (hout : a + v ∉ interior K) :
    Shallow A a K r := by
  obtain ⟨f, hfne, hle⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point (A := K) hKc hout hKint
  set c : Fin n → ℝ := fun i => f (Pi.single i (1 : ℝ)) with hc
  have hf_eq : ∀ x : Fin n → ℝ, f x = c ⬝ᵥ x := by
    intro x
    have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ]
    conv_lhs => rw [hx]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct, hc]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hcne : c ≠ 0 := by
    intro h
    apply hfne
    ext x
    rw [hf_eq x, h]
    simp
  set p : Fin n → ℝ := A⁻¹ *ᵥ c with hp
  have hAp : A *ᵥ p = c := by
    rw [hp, Matrix.mulVec_mulVec, QMCLeafB.EngineIterates.mul_inv_of_posDef hA,
      Matrix.one_mulVec]
  have hσpos : 0 < c ⬝ᵥ p := by
    rw [← hAp, dotProduct_comm]
    refine QMCLeafB.EngineIterates.posDef_apply_pos hA ?_
    intro h
    rw [h, Matrix.mulVec_zero] at hAp
    exact hcne hAp.symm
  have hcs : (c ⬝ᵥ v) ^ 2 ≤ (c ⬝ᵥ p) * (v ⬝ᵥ (A *ᵥ v)) := qf_cauchy hA hAp v
  have hbound : c ⬝ᵥ v ≤ r * Real.sqrt (c ⬝ᵥ p) := by
    have h1 : (c ⬝ᵥ v) ^ 2 ≤ (c ⬝ᵥ p) * r ^ 2 := by
      have h2 : (c ⬝ᵥ p) * (v ⬝ᵥ (A *ᵥ v)) ≤ (c ⬝ᵥ p) * r ^ 2 :=
        mul_le_mul_of_nonneg_left hv hσpos.le
      linarith [hcs, h2]
    have h3 : Real.sqrt ((c ⬝ᵥ v) ^ 2) ≤ Real.sqrt ((c ⬝ᵥ p) * r ^ 2) :=
      Real.sqrt_le_sqrt h1
    have h5 : Real.sqrt ((c ⬝ᵥ p) * r ^ 2) = Real.sqrt (c ⬝ᵥ p) * r := by
      rw [Real.sqrt_mul hσpos.le, Real.sqrt_sq hr]
    have h6 : Real.sqrt ((c ⬝ᵥ v) ^ 2) = |c ⬝ᵥ v| := Real.sqrt_sq_eq_abs (c ⬝ᵥ v)
    rw [h6, h5] at h3
    have h4 : |c ⬝ᵥ v| ≤ r * Real.sqrt (c ⬝ᵥ p) := by
      rw [mul_comm]; exact h3
    linarith [le_abs_self (c ⬝ᵥ v), h4]
  refine ⟨-c, -p, ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_neg, hAp]
  · simpa using hcne
  · intro z hz
    have h1 : f z ≤ f (a + v) := hle z hz
    have hfz : f (a - z) = f a - f z := by
      have hh : a - z = a + -z := by abel
      rw [hh, map_add, map_neg]; ring
    have hfa : f (a + v) = f a + f v := map_add f a v
    have hkey : c ⬝ᵥ (a - z) ≥ -(f v) := by
      rw [← hf_eq, hfz]
      linarith [h1, hfa]
    have hfv : f v = c ⬝ᵥ v := hf_eq v
    have hneg : (-c) ⬝ᵥ (a - z) = -(c ⬝ᵥ (a - z)) := neg_dotProduct c (a - z)
    have hcc : (-c) ⬝ᵥ (-p) = c ⬝ᵥ p := by
      simp only [dotProduct_neg, neg_dotProduct, neg_neg]
    rw [hneg, hcc]
    have h2' : -(c ⬝ᵥ (a - z)) ≤ c ⬝ᵥ v := by rw [← hfv]; linarith
    linarith [h2', hbound]

#print axioms QMCLeafB.Crit38M8.shallow_of_interior_escape

/-- **THE EXACT CRITERION.**  For a convex body with nonempty interior and centre `a`, the round is
recordable with margin `r` **iff** some point of the closed `A`-ball of radius `r` about `a` lies
outside the body's interior.  Equivalently: the obligation fails exactly when the body swallows that
ball.  No distance, no steering, no trajectory. -/
theorem criterion_iff {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {K : Set (Fin n → ℝ)} (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
    (a : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Shallow A a K r ↔ ∃ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ r ^ 2 ∧ a + v ∉ interior K := by
  constructor
  · intro hsh
    by_contra hcon
    push Not at hcon
    exact not_shallow_of_ball_interior hA hcon hsh
  · rintro ⟨v, hv, hout⟩
    exact shallow_of_interior_escape hA hKc hKint a hr hv hout

#print axioms QMCLeafB.Crit38M8.criterion_iff

end QMCLeafB.Crit38M8


