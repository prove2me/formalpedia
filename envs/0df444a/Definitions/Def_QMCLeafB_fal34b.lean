-- Prove2me | Definitions.Def_QMCLeafB_fal34b
-- name    : QMCLeafB_fal34b
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:51:47.235409+00:00
-- url     : https://prove2.me/theorems/c8c9468a-e4e6-45e5-8fcd-bedf2b76053c
-- title:
--   QMCLeafB fal34b
-- statement:
--   # leaf B phase 34 — `fal34b` (swarm `smw3g7eoq`, member m6, direction d4) — PUBLISHED CONE
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_sound31
import Definitions.Def_QMCLeafB_centre_adm_m1
import Definitions.Def_QMCLeafB_pinch_m1
import Definitions.Def_QMCLeafB_stateDiag
import Definitions.Def_QMCLeafB_htop_oklower_m7
/-
# leaf B phase 34 — `fal34b` (swarm `smw3g7eoq`, member m6, direction d4) — PUBLISHED CONE

The co-loadable twin of `Check_fal34_m6`: same three results, but importing only published
`Definitions.Def_QMCLeafB_*` bundles (so it loads next to the `pbit33` programme cone and next to
`Def_QMCLeafB_asm_m8` / `_topSlice` / `_asm2`, which `Check_fal34_m6`'s cone CANNOT — that one brings
`Solutions.Check_asm_m8`'s `AsmM8.MemberAt` and collides with `Definitions.Def_QMCLeafB_asm_m8`).
Everything is self-contained here: `dsum` and the canonical witness `famQ` are re-stated locally, so
no `Solutions.Check_*` import is needed.

## What it delivers

For a `RelaxMem` body at tolerance `δ` on the campaign's level and the program's own pinch
(`CentreAdm.diagPinch`, diagonal overwritten to `1 − δ/4`):

1. **`relaxMem_diagPinch_of_diagGate`** — a PER-COORDINATE diagonal bound `∀ i, |Qᵢᵢ − 1| ≤ δ/4`
   plus PSD plus the level makes the pinch a member.  (Weakens `CentreAdm.relaxMem_diagPinch`'s
   unit-diagonal hypothesis to exactly what a released `ok` test can deliver.)
2. **`not_relaxMem_diagPinch_advQ` / `tau_le_quarter_of_pinch_sound`** — the tolerance `δ/4` is FORCED
   for the per-coordinate gate: at `τ > δ/4` the PSD rank-one state `advQ τ = (1+τ)·J` passes
   `∀ i, |Qᵢᵢ − 1| ≤ τ` yet its pinch is a member of NO body (margin clause fails at `(1,−1)`).
3. **`quarter_gate_rejects_famQ` vs `sumGate_half_is_the_release_two`** — THE CORRECTION.  The
   campaign's canonical body witness `famQ n d b = d·1 + b·J` (`d + b = 1 + δ/4`) has every diagonal
   deviation exactly `δ/4`, hence `dsum = n·δ/4`; so a SUM gate at `δ/4` REJECTS it (for `n ≥ 2`),
   while a sum gate at `δ/2` accepts every member AND is pinch-sound at `n = 2`
   (`pinch_sound_at_half_two`).  Hence at `n = 2` — the stratum of `G₀`, `G₁` and the dreg band — the
   `dvR` release must be `dvR ≤ dqOf/2`, not `dvR ≤ dqOf/4`.
4. **`noStrictBelow_of_bit_false_record`** — a record at a bit-false point forbids any real
   unit-diagonal PSD point strictly below `t − Rq/40000` (published
   `Sound31.bit_true_of_strict_below` in contrapositive form): `hfalse`'s domain is contained in the
   strictly-thin stratum `NoStrictBelow`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every declaration.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Fal34B

open QuantumMaxCutEnergy

/-! ## §0  The sum statistic and the canonical witness, locally -/

/-- The program's `ok` register in matrix form: the SUM of the diagonal deviations.  (This is `dvR`'s
formula on the state's own row-major code; `Check_fal34_m6` carries the formal bridge.) -/
def dsum {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) : ℚ := ∑ i, |X i i - 1|

/-- Each deviation is at most the sum. -/
theorem le_dsum {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) : |X i i - 1| ≤ dsum X :=
  Finset.single_le_sum (f := fun j : Fin n => |X j j - 1|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)

#print axioms le_dsum

/-- All deviations equal `t` forces `dsum = n·t`. -/
theorem dsum_of_all_eq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) {t : ℚ}
    (h : ∀ i, |X i i - 1| = t) : dsum X = (n : ℚ) * t := by
  unfold dsum
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

#print axioms dsum_of_all_eq

/-- The campaign's canonical body witness: `d·1 + b·J` (all diagonal `d + b`, all off-diagonal `b`). -/
def famQ (n : ℕ) (d b : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  d • (1 : Matrix (Fin n) (Fin n) ℚ) + b • (Matrix.of fun _ _ => (1 : ℚ))

theorem famQ_apply_self {n : ℕ} (d b : ℚ) (i : Fin n) : famQ n d b i i = d + b := by
  simp [famQ]

#print axioms famQ_apply_self

/-- The witness's `dsum` when its diagonal is `1 + δ/4`: exactly `n·δ/4`. -/
theorem dsum_famQ {n : ℕ} {δ : ℚ} (hδ : 0 < δ) (d b : ℚ) (hdb : d + b = 1 + δ / 4) :
    dsum (famQ n d b) = (n : ℚ) * (δ / 4) :=
  dsum_of_all_eq _ (fun i => by
    rw [famQ_apply_self, hdb, show 1 + δ / 4 - 1 = δ / 4 by ring, abs_of_nonneg (by linarith)])

#print axioms dsum_famQ

/-! ## §1  The gate's sufficient form and its forced tolerance -/

/-- **`RelaxMem` at the pinch from a per-coordinate diagonal bound.** -/
theorem relaxMem_diagPinch_of_diagGate {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hdq : 0 < dq) (hdq4 : dq ≤ 4) (hA : ∀ i, A i i = 0)
    (hdiag : ∀ i, |Q i i - 1| ≤ dq / 4)
    (hpsd : ∀ x : Fin n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x)
    (htrace : QMCLeafB.SepOracle.frob A Q ≤ u + dq / 2) :
    QMCLeafB.RelaxOracle.RelaxMem A (QMCLeafB.CentreAdm.diagPinch Q dq) u dq where
  δ_pos := hdq
  psd_margin := by
    intro x
    have hcoef : ∀ i, -(dq / 2) ≤ 1 - dq / 4 - Q i i := by
      intro i
      have h := (abs_le.1 (hdiag i)).2
      linarith
    have hsum : ∑ i, (-(dq / 2)) * x i ^ 2 ≤ ∑ i, (1 - dq / 4 - Q i i) * x i ^ 2 :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hcoef i) (sq_nonneg (x i)))
    have hleft : ∑ i, (-(dq / 2)) * x i ^ 2 = -(dq / 2) * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
    rw [QMCLeafB.CentreAdm.qf_diagPinch]
    rw [hleft] at hsum
    have hp := hpsd x
    linarith
  diag_near := QMCLeafB.CentreAdm.abs_diagPinch Q hdq hdq4
  trace_le := by
    rw [QMCLeafB.CentreAdm.frob_diagPinch hA]
    exact htrace

#print axioms relaxMem_diagPinch_of_diagGate

/-- The SUM bound implies the per-coordinate bound, so a `dvR ≤ dq/4` gate base pinches into a member.
**This is `hok`'s consumer side at the brief's gate** — no `dvR = 0` hypothesis anywhere. -/
theorem relaxMem_diagPinch_of_dsumGate {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hdq : 0 < dq) (hdq4 : dq ≤ 4) (hA : ∀ i, A i i = 0)
    (hsum : dsum Q ≤ dq / 4)
    (hpsd : ∀ x : Fin n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x)
    (htrace : QMCLeafB.SepOracle.frob A Q ≤ u + dq / 2) :
    QMCLeafB.RelaxOracle.RelaxMem A (QMCLeafB.CentreAdm.diagPinch Q dq) u dq :=
  relaxMem_diagPinch_of_diagGate hdq hdq4 hA
    (fun i => le_trans (le_dsum Q i) hsum) hpsd htrace

#print axioms relaxMem_diagPinch_of_dsumGate

/-- The rank-one adversary: every entry `1 + τ`. -/
def advQ (τ : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := fun _ _ => 1 + τ

/-- The test direction `(1, −1)`. -/
def xadv : Fin 2 → ℚ := ![1, -1]

theorem advQ_qf (τ : ℚ) (x : Fin 2 → ℚ) :
    QMCLeafB.SepOracle.qf (advQ τ) x = (1 + τ) * (x 0 + x 1) ^ 2 := by
  change QMCLeafB.SepOracle.qf (fun _ _ : Fin 2 => (1 + τ)) x = (1 + τ) * (x 0 + x 1) ^ 2
  simp [QMCLeafB.SepOracle.qf, Matrix.mulVec]
  ring

#print axioms advQ_qf

theorem advQ_psd {τ : ℚ} (hτ : 0 ≤ τ) :
    ∀ x : Fin 2 → ℚ, 0 ≤ QMCLeafB.SepOracle.qf (advQ τ) x := by
  intro x
  rw [advQ_qf]
  have h : (0 : ℚ) ≤ (x 0 + x 1) ^ 2 := sq_nonneg _
  nlinarith

#print axioms advQ_psd

theorem advQ_dev (τ : ℚ) (i : Fin 2) : advQ τ i i - 1 = τ := by
  simp [advQ]

#print axioms advQ_dev

theorem xadv_sq_sum : ∑ i : Fin 2, xadv i ^ 2 = 2 := by
  simp [Fin.sum_univ_two, xadv]
  norm_num

#print axioms xadv_sq_sum

/-- **The adversary above `δ/4`**: a PSD state passing the per-coordinate gate whose pinch is a member
of NO body. -/
theorem not_relaxMem_diagPinch_advQ {dq τ : ℚ} (hτ : dq / 4 < τ)
    (A : Matrix (Fin 2) (Fin 2) ℚ) (u : ℚ) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem A (QMCLeafB.CentreAdm.diagPinch (advQ τ) dq) u dq := by
  intro h
  have hx := h.psd_margin xadv
  rw [QMCLeafB.CentreAdm.qf_diagPinch] at hx
  have hq : QMCLeafB.SepOracle.qf (advQ τ) xadv = 0 := by
    rw [advQ_qf]
    simp [xadv]
  have hcoef : ∀ i : Fin 2, (1 - dq / 4 - advQ τ i i) = -(dq / 4) - τ := by
    intro i
    simp [advQ]
    ring
  have hlin : ∑ i : Fin 2, (1 - dq / 4 - advQ τ i i) * xadv i ^ 2 = -(dq / 2) - 2 * τ := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [hcoef i])]
    rw [← Finset.mul_sum, xadv_sq_sum]
    ring
  rw [hq, xadv_sq_sum, hlin] at hx
  linarith

#print axioms not_relaxMem_diagPinch_advQ

/-- **The per-coordinate tolerance cannot be widened past `δ/4`.** -/
theorem tau_le_quarter_of_pinch_sound {dq τ : ℚ} (hdq : 0 < dq) (hτ0 : 0 ≤ τ)
    (hsound : ∀ (Q : Matrix (Fin 2) (Fin 2) ℚ), (∀ x : Fin 2 → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x) →
      (∀ i, |Q i i - 1| ≤ τ) →
      ∀ (A : Matrix (Fin 2) (Fin 2) ℚ) (u : ℚ), (∀ i, A i i = 0) →
        QMCLeafB.SepOracle.frob A Q ≤ u + dq / 2 →
        QMCLeafB.RelaxOracle.RelaxMem A (QMCLeafB.CentreAdm.diagPinch Q dq) u dq) :
    τ ≤ dq / 4 := by
  by_contra hcon
  rw [not_le] at hcon
  have hdev : ∀ i, |advQ τ i i - 1| ≤ τ := fun i => by
    rw [advQ_dev]
    exact le_of_eq (abs_of_nonneg hτ0)
  have hmem := hsound (advQ τ) (advQ_psd hτ0) hdev 0 0 (fun i => rfl) (by
    simp [QMCLeafB.SepOracle.frob]
    linarith)
  exact not_relaxMem_diagPinch_advQ hcon 0 0 hmem

#print axioms tau_le_quarter_of_pinch_sound

/-! ## §2  The defect: the two gates disagree exactly on the campaign's own witness -/

/-- Every member's deviations are at most `δ/4`, so its `dsum` is at most `n·δ/4`. -/
theorem dsum_le_of_relaxMem {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (h : QMCLeafB.RelaxOracle.RelaxMem A cX u δ) : dsum cX ≤ (n : ℚ) * (δ / 4) :=
  Finset.sum_le_sum (fun i _ => h.diag_near i) |>.trans_eq (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])

#print axioms dsum_le_of_relaxMem

/-- **A sum gate at `δ/4` REJECTS the campaign's canonical witness** (`n ≥ 2`). -/
theorem quarter_gate_rejects_famQ {n : ℕ} (hn : 2 ≤ n) {δ : ℚ} (hδ : 0 < δ) (d b : ℚ)
    (hdb : d + b = 1 + δ / 4) : ¬ (dsum (famQ n d b) ≤ δ / 4) := by
  rw [dsum_famQ hδ d b hdb]
  have hn' : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  intro hle
  nlinarith

#print axioms quarter_gate_rejects_famQ

/-- **The per-coordinate gate ACCEPTS the same witness.** -/
theorem coordGate_accepts_famQ {n : ℕ} {δ : ℚ} (hδ : 0 ≤ δ) (d b : ℚ)
    (hdb : d + b = 1 + δ / 4) (i : Fin n) : |famQ n d b i i - 1| ≤ δ / 4 := by
  rw [famQ_apply_self, hdb]
  rw [show 1 + δ / 4 - 1 = δ / 4 by ring, abs_of_nonneg (by linarith)]

#print axioms coordGate_accepts_famQ

/-! ## §3  The corrected sum tolerance at `n = 2`: `δ/2` is sound AND covering -/

def ones2 : Fin 2 → ℚ := ![1, 1]
def pm2 : Fin 2 → ℚ := ![1, -1]

theorem qf_at_ones (Q : Matrix (Fin 2) (Fin 2) ℚ) :
    QMCLeafB.SepOracle.qf Q ones2 = Q 0 0 + Q 0 1 + Q 1 0 + Q 1 1 := by
  simp [QMCLeafB.SepOracle.qf, ones2]
  ring

#print axioms qf_at_ones

theorem qf_at_pm (Q : Matrix (Fin 2) (Fin 2) ℚ) :
    QMCLeafB.SepOracle.qf Q pm2 = Q 0 0 - Q 0 1 - Q 1 0 + Q 1 1 := by
  simp [QMCLeafB.SepOracle.qf, pm2]
  ring

#print axioms qf_at_pm

theorem qf_pinch_exp (δ : ℚ) (Q : Matrix (Fin 2) (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    QMCLeafB.SepOracle.qf (QMCLeafB.CentreAdm.diagPinch Q δ) x
      = (1 - δ / 4) * (x 0 ^ 2 + x 1 ^ 2) + (Q 0 1 + Q 1 0) * (x 0 * x 1) := by
  change QMCLeafB.SepOracle.qf (fun i j : Fin 2 => if i = j then 1 - δ / 4 else Q i j) x
      = (1 - δ / 4) * (x 0 ^ 2 + x 1 ^ 2) + (Q 0 1 + Q 1 0) * (x 0 * x 1)
  simp [QMCLeafB.SepOracle.qf, Matrix.mulVec]
  ring

#print axioms qf_pinch_exp

/-- **The margin clause at half tolerance (`n = 2`).**  PSD + `dsum ≤ δ/2` pinches into a matrix with
minimum eigenvalue at least `−δ/2`. -/
theorem pinch_sound_at_half_two {δ : ℚ} {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hpsd : ∀ x : Fin 2 → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x)
    (hsum : dsum Q ≤ δ / 2) (x : Fin 2 → ℚ) :
    -(δ / 2) * ∑ i, x i ^ 2 ≤ QMCLeafB.SepOracle.qf (QMCLeafB.CentreAdm.diagPinch Q δ) x := by
  have h1 : 0 ≤ Q 0 0 + Q 0 1 + Q 1 0 + Q 1 1 := by
    have := hpsd ones2; rwa [qf_at_ones] at this
  have h2 : 0 ≤ Q 0 0 - Q 0 1 - Q 1 0 + Q 1 1 := by
    have := hpsd pm2; rwa [qf_at_pm] at this
  have hcross : |Q 0 1 + Q 1 0| ≤ Q 0 0 + Q 1 1 := by
    rw [abs_le]; constructor <;> linarith
  have hd : dsum Q = |Q 0 0 - 1| + |Q 1 1 - 1| := by
    rw [dsum, Fin.sum_univ_two]
  have hdiag : Q 0 0 + Q 1 1 ≤ 2 + δ / 2 := by
    have a := le_abs_self (Q 0 0 - 1)
    have b := le_abs_self (Q 1 1 - 1)
    rw [hd] at hsum
    linarith
  have ham : 2 * |x 0 * x 1| ≤ x 0 ^ 2 + x 1 ^ 2 := by
    have ha : |x 0 * x 1| = |x 0| * |x 1| := abs_mul _ _
    have h1' := sq_nonneg (x 0 - x 1)
    have h2' := sq_nonneg (x 0 + x 1)
    have h3 := sq_abs (x 0)
    have h4 := sq_abs (x 1)
    have h5 := abs_nonneg (x 0)
    have h6 := abs_nonneg (x 1)
    nlinarith [abs_nonneg (x 0 * x 1)]
  have hxsq : ∑ i : Fin 2, x i ^ 2 = x 0 ^ 2 + x 1 ^ 2 := Fin.sum_univ_two _
  have hkey : (Q 0 1 + Q 1 0) * (x 0 * x 1) ≥ -(Q 0 0 + Q 1 1) * |x 0 * x 1| := by
    have h1' : -(Q 0 0 + Q 1 1) * |x 0 * x 1| ≤ -|Q 0 1 + Q 1 0| * |x 0 * x 1| := by
      nlinarith [abs_nonneg (x 0 * x 1), abs_nonneg (Q 0 1 + Q 1 0)]
    have h2' : -|Q 0 1 + Q 1 0| * |x 0 * x 1| ≤ (Q 0 1 + Q 1 0) * (x 0 * x 1) := by
      have h := neg_abs_le ((Q 0 1 + Q 1 0) * (x 0 * x 1))
      rw [abs_mul] at h
      linarith
    linarith
  rw [qf_pinch_exp, hxsq]
  nlinarith [hdiag, ham, hkey, sq_nonneg (x 0), sq_nonneg (x 1)]

#print axioms pinch_sound_at_half_two

/-- **`hok`'s consumer side at the CORRECTED sum gate**: `dvR ≤ dq/2` on a PSD base at `n = 2` yields
a `RelaxMem` member at the pinch. -/
theorem relaxMem_diagPinch_of_dsumGate_half_two {A Q : Matrix (Fin 2) (Fin 2) ℚ} {u δ : ℚ}
    (hδ : 0 < δ) (hδ4 : δ ≤ 4) (hA : ∀ i, A i i = 0)
    (hsum : dsum Q ≤ δ / 2)
    (hpsd : ∀ x : Fin 2 → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x)
    (htrace : QMCLeafB.SepOracle.frob A Q ≤ u + δ / 2) :
    QMCLeafB.RelaxOracle.RelaxMem A (QMCLeafB.CentreAdm.diagPinch Q δ) u δ where
  δ_pos := hδ
  psd_margin := pinch_sound_at_half_two hpsd hsum
  diag_near := QMCLeafB.CentreAdm.abs_diagPinch Q hδ hδ4
  trace_le := by
    rw [QMCLeafB.CentreAdm.frob_diagPinch hA]
    exact htrace

#print axioms relaxMem_diagPinch_of_dsumGate_half_two

/-- **THE RELEASE AT `n = 2`, both directions**: the sum gate at `δ/2` is pinch-SOUND and accepts
every member (COMPLETE).  So at `n = 2` the `dvR` release needs `dqOf/2`, not `dqOf/4`. -/
theorem sumGate_half_is_the_release_two :
    (∀ (A Q : Matrix (Fin 2) (Fin 2) ℚ) (u δ : ℚ), 0 < δ → δ ≤ 4 → (∀ i, A i i = 0) →
      dsum Q ≤ δ / 2 → (∀ x : Fin 2 → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x) →
      QMCLeafB.SepOracle.frob A Q ≤ u + δ / 2 →
      QMCLeafB.RelaxOracle.RelaxMem A (QMCLeafB.CentreAdm.diagPinch Q δ) u δ) ∧
    (∀ (A cX : Matrix (Fin 2) (Fin 2) ℚ) (u δ : ℚ),
      QMCLeafB.RelaxOracle.RelaxMem A cX u δ → dsum cX ≤ δ / 2) :=
  ⟨fun _ _ _ _ hδ hδ4 hA hsum hpsd htrace =>
      relaxMem_diagPinch_of_dsumGate_half_two hδ hδ4 hA hsum hpsd htrace,
   fun _ _ _ _ h => by
     have h' := dsum_le_of_relaxMem (n := 2) h
     linarith⟩

#print axioms sumGate_half_is_the_release_two

/-! ## §3b  `hok`'s consumer side at the RELEASED gate, on the engine state -/

/-- `(List.range n).map g).sum` as a `Fin n`-sum. -/
theorem dsum_range {n : ℕ} (g : ℕ → ℚ) : ((List.range n).map g).sum = ∑ i : Fin n, g i := by
  rw [Fin.sum_univ_eq_sum_range (fun k => g k)]
  induction n with
  | zero => simp
  | succ m ih => simp [List.range_succ, ih, Finset.sum_range_succ]

#print axioms dsum_range

/-- **`dvR` IS `dsum`** on the state's own row-major code. -/
theorem dvR_eq_dsum (s : QMCLeafB.RoundProgram.RSt)
    (hlen : QMCLeafB.RoundProgram.stN s ≤ (QMCLeafB.RoundProgram.stX s).length) :
    QMCLeafB.RoundProgram.dvR s
      = dsum (QMCLeafB.StateDiag.stMat (QMCLeafB.RoundProgram.stN s)
          (QMCLeafB.RoundProgram.stX s)) := by
  have h1 : QMCLeafB.RoundProgram.dvR s
      = ((List.range (QMCLeafB.RoundProgram.stN s)).map
          (fun i => |QMCLeafB.RoundProgram.entV (QMCLeafB.RoundProgram.stN s,
            QMCLeafB.RoundProgram.stX s) i i - 1|)).sum := by
    unfold QMCLeafB.RoundProgram.dvR QMCLeafB.RoundProgram.diagSumV
    rw [QMCLeafB.StateDiag.idxs_of_le hlen]
    rw [show (fun i => QMCLeafB.RoundProgram.absq
        (QMCLeafB.RoundProgram.entV (QMCLeafB.RoundProgram.stN s,
          QMCLeafB.RoundProgram.stX s) i i - 1))
        = (fun i => |QMCLeafB.RoundProgram.entV (QMCLeafB.RoundProgram.stN s,
          QMCLeafB.RoundProgram.stX s) i i - 1|) from by
      funext i; exact QMCLeafB.RoundProgram.absq_eq _]
  rw [h1, dsum_range (fun i => |QMCLeafB.RoundProgram.entV (QMCLeafB.RoundProgram.stN s,
      QMCLeafB.RoundProgram.stX s) i i - 1|), dsum]
  rfl

#print axioms dvR_eq_dsum

/-- **`hok`'s CONSUMER SIDE AT THE RELEASED GATE.**  At any engine state whose sum register reads
`dvR s ≤ dq/4`, whose stored matrix is PSD, and whose trace test sits at the level
(`fvR s ≤ levelOf s`), the program's own pinch IS a symmetric rational member at
`(stT s − epsOf s, dq)`.

No `dvR = 0`, no `okV` flag, no pivot answer, no certified PSD margin: this replaces
`VerdictBridge.relaxMem_diagPinch_of_okV` for a program whose `ok` test is the released sum gate.  Its
two hypotheses `hpsd`/`hfv` are exactly what an `ok`-branch descent supplies (`PivExact.psd_of_false`
and the round's own level test). -/
theorem relaxMem_diagPinch_of_releasedGate {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    {s : QMCLeafB.RoundProgram.RSt} {u dq : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = n)
    (hlenA : n ≤ (QMCLeafB.RoundProgram.stA s).length)
    (hlenX : n ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hA : QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stA s) = A)
    (hAdiag : ∀ i, A i i = 0)
    (hsym : ∀ i j, QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s) i j
      = QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s) j i)
    (hgate : QMCLeafB.RoundProgram.dvR s ≤ dq / 4)
    (hpsd : ∀ x : Fin n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf
      (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) x)
    (hdqpos : 0 < dq) (hdq4 : dq ≤ 4)
    (hT : QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s = u)
    (hdq : QMCLeafB.OkLower.dqOf s = dq)
    (hfv : QMCLeafB.RoundProgram.fvR s ≤ QMCLeafB.OkLower.levelOf s) :
    ∃ cX : Matrix (Fin n) (Fin n) ℚ, cXᵀ = cX ∧ QMCLeafB.RelaxOracle.RelaxMem A cX u dq := by
  have hdv : QMCLeafB.RoundProgram.dvR s
      = dsum (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) := by
    rw [dvR_eq_dsum s (by rw [hN]; exact hlenX), hN]
  have hsum : dsum (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) ≤ dq / 4 := by
    rw [← hdv]
    exact hgate
  have htrace : QMCLeafB.SepOracle.frob A
      (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) ≤ u + dq / 2 := by
    have hf : QMCLeafB.RoundProgram.fvR s
        = QMCLeafB.SepOracle.frob (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stA s))
            (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) :=
      QMCLeafB.StateDiag.fvR_eq_frob hN hlenA hlenX
    have hl : QMCLeafB.OkLower.levelOf s
        = QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s + QMCLeafB.OkLower.dqOf s / 2 := rfl
    rw [hf, hA, hl, hT, hdq] at hfv
    linarith
  have hmem := relaxMem_diagPinch_of_dsumGate hdqpos hdq4 hAdiag hsum hpsd htrace
  refine ⟨QMCLeafB.CentreAdm.diagPinch
    (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) dq, ?_, hmem⟩
  ext i j
  rw [Matrix.transpose_apply]
  exact QMCLeafB.CentreAdm.diagPinch_symm hsym dq j i

#print axioms relaxMem_diagPinch_of_releasedGate

/-- **`hok`'s consumer side at the CORRECTED gate (`n = 2`, `dvR ≤ dq/2`).**  Same content as
`relaxMem_diagPinch_of_releasedGate`, at the tolerance that is also complete
(`sumGate_half_is_the_release_two`).  A program rebuilt with `dvR ≤ dqOf/2` at `n = 2` gets its whole
`hok` slot from this one call. -/
theorem relaxMem_diagPinch_of_releasedGate_half_two {A : Matrix (Fin 2) (Fin 2) ℚ}
    {s : QMCLeafB.RoundProgram.RSt} {u dq : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = 2)
    (hlenA : 2 ≤ (QMCLeafB.RoundProgram.stA s).length)
    (hlenX : 2 ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hA : QMCLeafB.StateDiag.stMat 2 (QMCLeafB.RoundProgram.stA s) = A)
    (hAdiag : ∀ i, A i i = 0)
    (hsym : ∀ i j, QMCLeafB.StateDiag.stMat 2 (QMCLeafB.RoundProgram.stX s) i j
      = QMCLeafB.StateDiag.stMat 2 (QMCLeafB.RoundProgram.stX s) j i)
    (hgate : QMCLeafB.RoundProgram.dvR s ≤ dq / 2)
    (hpsd : ∀ x : Fin 2 → ℚ, 0 ≤ QMCLeafB.SepOracle.qf
      (QMCLeafB.StateDiag.stMat 2 (QMCLeafB.RoundProgram.stX s)) x)
    (hdqpos : 0 < dq) (hdq4 : dq ≤ 4)
    (hT : QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s = u)
    (hdq : QMCLeafB.OkLower.dqOf s = dq)
    (hfv : QMCLeafB.RoundProgram.fvR s ≤ QMCLeafB.OkLower.levelOf s) :
    ∃ cX : Matrix (Fin 2) (Fin 2) ℚ, cXᵀ = cX ∧ QMCLeafB.RelaxOracle.RelaxMem A cX u dq := by
  have hdv : QMCLeafB.RoundProgram.dvR s
      = dsum (QMCLeafB.StateDiag.stMat 2 (QMCLeafB.RoundProgram.stX s)) := by
    rw [dvR_eq_dsum s (by rw [hN]; exact hlenX), hN]
  have hsum : dsum (QMCLeafB.StateDiag.stMat 2 (QMCLeafB.RoundProgram.stX s)) ≤ dq / 2 := by
    rw [← hdv]
    exact hgate
  have htrace : QMCLeafB.SepOracle.frob A
      (QMCLeafB.StateDiag.stMat 2 (QMCLeafB.RoundProgram.stX s)) ≤ u + dq / 2 := by
    have hf : QMCLeafB.RoundProgram.fvR s
        = QMCLeafB.SepOracle.frob (QMCLeafB.StateDiag.stMat 2 (QMCLeafB.RoundProgram.stA s))
            (QMCLeafB.StateDiag.stMat 2 (QMCLeafB.RoundProgram.stX s)) :=
      QMCLeafB.StateDiag.fvR_eq_frob hN hlenA hlenX
    have hl : QMCLeafB.OkLower.levelOf s
        = QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s + QMCLeafB.OkLower.dqOf s / 2 := rfl
    rw [hf, hA, hl, hT, hdq] at hfv
    linarith
  have hmem := relaxMem_diagPinch_of_dsumGate_half_two hdqpos hdq4 hAdiag hsum hpsd htrace
  refine ⟨QMCLeafB.CentreAdm.diagPinch
    (QMCLeafB.StateDiag.stMat 2 (QMCLeafB.RoundProgram.stX s)) dq, ?_, hmem⟩
  ext i j
  rw [Matrix.transpose_apply]
  exact QMCLeafB.CentreAdm.diagPinch_symm hsym dq j i

#print axioms relaxMem_diagPinch_of_releasedGate_half_two

/-! ## §4  The `hfalse` side: no record at a bit-false strict-below point -/

/-- **NO RECORD at a bit-false strict-below point** — `Sound31.bit_true_of_strict_below` in
contrapositive form. -/
theorem not_runParts_of_bit_false_strictBelow {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hfalse : o G t = false)
    (hstrict : ∃ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z ∧
        (QMCLeafB.wMatrix G * Z).trace
          < (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    QMCLeafB.FinalStroke.RunParts o G t P → False := by
  intro B
  have h := QMCLeafB.Sound31.bit_true_of_strict_below P hn B hstrict
  rw [hfalse] at h
  exact Bool.false_ne_true h

#print axioms not_runParts_of_bit_false_strictBelow

/-- **The strictly-thin stratum**, named. -/
def NoStrictBelow (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  ∀ Z : Matrix (Fin G.n) (Fin G.n) ℝ, QMCLeafB.AnswerProducer.IsUnitDiagPSD Z →
    (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
      ≤ (QMCLeafB.wMatrix G * Z).trace

/-- **`hfalse`'s domain is contained in the strictly-thin stratum.** -/
theorem noStrictBelow_of_bit_false_record {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hfalse : o G t = false)
    (B : QMCLeafB.FinalStroke.RunParts o G t P) : NoStrictBelow G t := by
  intro Z hZ
  by_contra hcon
  rw [not_le] at hcon
  exact not_runParts_of_bit_false_strictBelow P hn hfalse ⟨Z, hZ, hcon⟩ B

#print axioms noStrictBelow_of_bit_false_record

/-- **The program-design constraint**: a record at a strict-below point forces the bit TRUE. -/
theorem bit_true_required_at_strictBelow {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (hstrict : ∃ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z ∧
        (QMCLeafB.wMatrix G * Z).trace
          < (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (B : QMCLeafB.FinalStroke.RunParts o G t P) : o G t = true :=
  QMCLeafB.Sound31.bit_true_of_strict_below P hn B hstrict

#print axioms bit_true_required_at_strictBelow

end QMCLeafB.Fal34B


