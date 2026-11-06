-- Prove2me | Definitions.Def_QMCLeafB_round33_m4
-- name    : QMCLeafB_round33_m4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:40:55.413113+00:00
-- url     : https://prove2.me/theorems/875faf6f-37c7-4965-a5f2-5b2d9ded44a0
-- title:
--   QMCLeafB round33_m4
-- statement:
--   # `Check_round33_m4` — phase 33, member m4: (A) is banked, case (iii) dissolves, and two receipts
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_fal30
import Definitions.Def_QMCLeafB_sol_inst31
/-
# `Check_round33_m4` — phase 33, member m4: (A) is banked, case (iii) dissolves, and two receipts

The phase-33 charter states the leaf's last object as a `Automatic.Poly` bit `o` plus a `RunParts`
family at `o`, with three record cases, the third being

> relaxed body nonempty but no exact unit-diagonal PSD witness at `t + eps`

and proposes to absorb it with a **rounding lemma** (A):

    RelaxMem (wMatrixQ G) Q (t - eps) dqShallow  ⟹
      ∃ X real, IsUnitDiagPSD X ∧  (wMatrix G * X).trace ≤ t + eps.

**(A) is already in this workspace, three times over.**  This file

* §1 restates (A) as one named theorem in the charter's own shape (`round_member`), on top of
  `QMCLeafB.Fal30.hcert_from_relaxMem` (phase 30) — which itself composes
  `QMCLeafB.RelaxOracle.relaxMem_witness` (phase 10) with the banked `paramsKbc2_budget`;
* §2 composes it with `Inst31SubM3.runParts_of_member` to get the *whole record* at an `ok` point
  (`runParts_of_relaxMem`): case (iii) is not a case.  The family's residual is exactly two slots —
  `ok`-soundness of the bit (which (A) converts into the record) and the `false` records, where
  `EmptyBody` is banked (`RefutedM3.runParts_of_emptyBody`) and only the ball-free thin band
  (`CruxM1.allFalseParts`) is genuinely open;
* §3 is the falsification receipt the charter asked for: the proposed construction
  `X = D((1-θ)Q + θI)D` with `θ = dq/2` **does not have unit diagonal** — its diagonal entry is
  `1 + θ(1-Q_ii)/Q_ii`.  It is not a rounding of `Q` at all.  The construction that does work is
  `X = D(Q + (δ/2)·1)D` with `D = diag (Q_ii + δ/2)^{-1/2}`, whose diagonal is
  `(Q_ii+δ/2)/(Q_ii+δ/2) = 1`; that is what `relaxMem_witness` implements rationally as `roundDiag`;
* §4 is the trace accounting, independently of `paramsKbc2_budget`: for zero-diagonal `A`,
  `roundCost A ν ≤ (15/4)·ν·∑|A|`, so at `ν = 3δ/4` the cost is at most `5 eps/16` against a budget
  `2 eps - δ/2 ≥ 3 eps/2` — a factor `4.8` of slack.  **No refutation of (A) is available**: the
  budget `2 eps - dq/2` is not tight at any input, and the sharpest `n = 2` instance is checked
  below with exact numerals.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
every theorem axiom-audited.  Import cone: published `Definitions/` only (`unionShallow`, `audit25`,
`refuted_m3`), so it does not load `Check_EngineIterates` and stays out of the `Check_asm2_m8`
collision class.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Round33M4

open QuantumMaxCutEnergy

/-! ## 1.  Lemma (A) in the charter's exact shape -/

/-- **LEMMA (A), banked.**  A symmetric rational relaxed member of the ball relaxation at level
`t - eps G` and tolerance `dqShallow G` yields a genuine unit-diagonal PSD *real* point of value at
most `t + eps G`.

Side conditions are the campaign's own: `2 ≤ n` (the `n ≤ 1` stratum is settled by
`VerdictSound.soundAt_of_le_one`, which reads no record) and `0 < Rq G` (the campaign bracket forces
it: `Inst31SubM3.Rq_pos_of_interior`). -/
theorem round_member (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (cX : Matrix (Fin G.n) (Fin G.n) ℚ) (hCsym : cXᵀ = cX)
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) :=
  QMCLeafB.Fal30.hcert_from_relaxMem G t cX hn hRq hCsym h

#print axioms QMCLeafB.Round33M4.round_member

/-- **The existential form**: (A) at the level at which the program's `ok` flag speaks
(`∃` symmetric rational centre).  This is verbatim `Inst31SubM3.MemberAt`. -/
theorem round_member' (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hmem : ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    Inst31SubM3.MemberAt G t := by
  obtain ⟨cX, hCsym, h⟩ := hmem
  obtain ⟨X, hX, htr⟩ := round_member G t hn hRq cX hCsym h
  exact ⟨X, hX, htr⟩

#print axioms QMCLeafB.Round33M4.round_member'

/-! ## 2.  Case (iii) dissolves: a relaxed member already gives the whole record

`Inst31SubM3.runParts_of_member` builds `RunParts` from `MemberAt` — all-`ok` stream, every cut slot
vacuous, `hcert` the single point — and needs only the bit to read `true`.  Composing with §1: **at
every point where the program's `ok` test fires, the family's record exists, and its `hcert` is the
rounded member.**  So the program's `ok` test may be the cheap rational `RelaxMem`-at-the-snapped-
centre test: no exact-PSD test, no `hok`, no `Hpsd`, no grid enlargement. -/
noncomputable def runParts_of_relaxMem {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hbit : o G t = true)
    (hmem : ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  Inst31SubM3.runParts_of_member (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.UnionShallow.one_le_Kbc2_mul G) hbit (round_member' G t hn hRq hmem)

#print axioms QMCLeafB.Round33M4.runParts_of_relaxMem

/-- **The family is owed only off the rational member set.**  Three slots, each explicit:

* `hmem` — `ok`-soundness of the bit: it reads `true` only where a symmetric rational `RelaxMem`
  exists at the campaign's `(t - eps, dqShallow)`.  This is what a *cheap* program test certifies;
* `hdeg` — the degenerate `Rq = 0` corner (outside the interior bracket; `hcert` is unsatisfiable
  there whenever `t < 0`, so no `ok` round can be reported and the record must come from below);
* `hfalse` — the record at every `false` bit, i.e. exactly the `EmptyBody` (banked) plus thin-band
  (`CruxM1.allFalseParts`) obligation.

No emptiness, no thin-body and no `hcomplete` analysis appears in the `true` branch: that is the
content of (A). -/
noncomputable def runParts_family_of_slots {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (hmem : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      0 < QMCLeafB.EngineRuntime.Rq G → o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hdeg : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      ¬ (0 < QMCLeafB.EngineRuntime.Rq G) → o G t = true →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G))
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → o G t = false →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G))
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  by_cases hb : o G t = true
  · by_cases hRq : 0 < QMCLeafB.EngineRuntime.Rq G
    · exact runParts_of_relaxMem G t hn hRq hb (hmem G t hn hRq hb)
    · exact hdeg G t hn hRq hb
  · exact hfalse G t hn (by
      cases h : o G t with
      | false => rfl
      | true => exact absurd h hb)

#print axioms QMCLeafB.Round33M4.runParts_family_of_slots

/-! ## 3.  Receipt: the charter's `θ`-recipe is not a unit-diagonal construction

The charter proposes `X = D((1-θ)Q + θI)D` with `D = diag (1/√dᵢ)`, `dᵢ = Qᵢᵢ`, and `θ ≈ dq/2`,
claiming the diagonals of `(1-θ)Q + θI` are `1`.  They are `(1-θ)Qᵢᵢ + θ = Qᵢᵢ + θ(1 - Qᵢᵢ)`; after
the congruence the diagonal entry is

    Xᵢᵢ = ((1-θ)Qᵢᵢ + θ)/Qᵢᵢ = 1 + θ(1 - Qᵢᵢ)/Qᵢᵢ,

which is `1` only at `Qᵢᵢ = 1` — exactly the case the relaxation does not give.  So the recipe fails
the `IsUnitDiagPSD` requirement outright (the `D`-scaling is what *creates* the error). -/
theorem theta_recipe_diag (q θ : ℚ) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hθ : θ ≠ 0) :
    ((1 - θ) * q + θ) / q ≠ 1 := by
  intro h
  have h' : ((1 - θ) * q + θ) = q := by
    field_simp at h
    linarith [h]
  have : θ * (1 - q) = 0 := by linarith
  rcases mul_eq_zero.mp this with h2 | h2
  · exact hθ h2
  · exact hq1 (by linarith)

#print axioms QMCLeafB.Round33M4.theta_recipe_diag

/-- The same at the charter's own numbers, `dq = 1/4`, `Qᵢᵢ = 1 + dq/4 = 17/16`, `θ = dq/2 = 1/8`:
the diagonal is `135/136`, not `1`. -/
theorem theta_recipe_concrete :
    ((1 - (1 : ℚ) / 8) * (1 + 1 / 16) + 1 / 8) / (1 + 1 / 16) = 135 / 136 := by
  norm_num

#print axioms QMCLeafB.Round33M4.theta_recipe_concrete

theorem theta_recipe_concrete_ne_one :
    ((1 - (1 : ℚ) / 8) * (1 + 1 / 16) + 1 / 8) / (1 + 1 / 16) ≠ 1 := by
  norm_num

#print axioms QMCLeafB.Round33M4.theta_recipe_concrete_ne_one

/-- **The construction that does work.**  Shifting before scaling — `X = D(Q + (δ/2)·1)D` with
`Dᵢᵢ = (Qᵢᵢ + δ/2)^{-1/2}` — has diagonal entry exactly `1` *and* is PSD, because
`Q + (δ/2)·1 ⪰ 0` is exactly `RelaxMem.psd_margin`.  (`relaxMem_witness` realises this rationally:
`roundDiag` uses `sc X i = 2/(1 + Xᵢᵢ)` plus a compensating diagonal shift, avoiding square roots.) -/
theorem shift_recipe_diag (q c : ℚ) (hc : q + c ≠ 0) : (q + c) / (q + c) = 1 :=
  div_self hc

#print axioms QMCLeafB.Round33M4.shift_recipe_diag

/-! ## 4.  Receipt: the trace accounting, independently of `paramsKbc2_budget`

`roundCost A ν = (1+ν)(2ν+ν²)·∑|A| + ν²·∑|Aᵢᵢ|`.  For zero-diagonal `A` (the campaign's
`wMatrixQ G`) and `ν ≤ 1/2` the leading factor collapses to `ν(1+ν)(2+ν) ≤ (15/4)ν`, so one rounding
pass costs at most `(15/4)·ν·∑|A|` — with `ν = 3δ/4` and `∑|A| = Rq` that is `(45/16)·δ·Rq`. -/
theorem roundCost_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (ν : ℚ)
    (hA0 : ∀ i, A i i = 0) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1 / 2) :
    QMCLeafB.RoundingOut.roundCost A ν
      ≤ (15 / 4) * ν * (∑ i, ∑ j, |A i j|) := by
  unfold QMCLeafB.RoundingOut.roundCost
  have hdiag : (∑ i, |A i i|) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hA0 i, abs_zero]
  rw [hdiag]
  have hsum : (0 : ℚ) ≤ ∑ i, ∑ j, |A i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hfac : (1 + ν) * (2 * ν + ν ^ 2) = ν * ((1 + ν) * (2 + ν)) := by ring
  rw [hfac, mul_zero, add_zero]
  have hb : (1 + ν) * (2 + ν) ≤ 15 / 4 := by nlinarith
  have hν2 : (0 : ℚ) ≤ ν * ((1 + ν) * (2 + ν)) := by nlinarith
  calc ν * ((1 + ν) * (2 + ν)) * (∑ i, ∑ j, |A i j|)
      = (ν * (∑ i, ∑ j, |A i j|)) * ((1 + ν) * (2 + ν)) := by ring
    _ ≤ (ν * (∑ i, ∑ j, |A i j|)) * (15 / 4) := by
        apply mul_le_mul_of_nonneg_left hb
        exact mul_nonneg hν0 hsum
    _ = (15 / 4) * ν * (∑ i, ∑ j, |A i j|) := by ring

#print axioms QMCLeafB.Round33M4.roundCost_le

/-- **The campaign's budget, re-derived.**  With `δ·Rq ≤ eps/9` (which is
`dqShallow G · Rq G ≤ eps G / 9`, from `δ = eps/(9·Rq+1)`) and `δ ≤ eps`, one rounding pass costs at
most `5 eps/16` while the available slack is `2 eps - δ/2 ≥ 3 eps/2`: a factor `4.8` of margin.

This is checked at the sharpest `n = 2` input below with exact numerals
(`Rq = 2`, `eps = 1/20000`, `δ = 1/380000`); the derivation is the general one. -/
theorem budget_general {δ eps Rq : ℚ} (hδ : 0 ≤ δ) (heps : 0 < eps)
    (hδRq : δ * Rq ≤ eps / 9) (hδeps : δ ≤ eps) :
    (15 / 4) * (3 * δ / 4) * Rq ≤ 2 * eps - δ / 2 := by
  have h1 : (15 / 4) * (3 * δ / 4) * Rq = (45 / 16) * (δ * Rq) := by ring
  rw [h1]
  have h2 : (45 / 16) * (δ * Rq) ≤ (45 / 16) * (eps / 9) := by
    apply mul_le_mul_of_nonneg_left hδRq
    norm_num
  have h3 : (45 / 16) * (eps / 9) = 5 * eps / 16 := by ring
  rw [h3] at h2
  linarith

#print axioms QMCLeafB.Round33M4.budget_general

/-- **The sharpest `n = 2` instance, exact.**  Single edge of weight `1`: `Rq = 2`,
`eps = Rq/40000 = 1/20000`, `δ = dqShallow = eps/(9·Rq+1) = 1/380000`.  The rounding cost bound is
`(45/16)·δ·Rq = 45/3040000 ≈ 1.48·10⁻⁵`, the budget is `2eps - δ/2 = 1/10000 - 1/760000 ≈ 9.87·10⁻⁵`:
the budget is `10/3` times the bound, so the extreme psd-margin/diagonal-margin point does **not**
round over.  (The true worst-case cost there is `3δ/2 ≈ 3.9·10⁻⁶`, six times smaller still.) -/
theorem budget_sharp_two :
    (15 / 4) * (3 * (1 / 380000 : ℚ) / 4) * 2 ≤ 2 * (1 / 20000) - (1 / 380000) / 2 := by
  norm_num

#print axioms QMCLeafB.Round33M4.budget_sharp_two

theorem budget_sharp_two_ratio :
    (15 / 4) * (3 * (1 / 380000 : ℚ) / 4) * 2 = 45 / 3040000 := by
  norm_num

#print axioms QMCLeafB.Round33M4.budget_sharp_two_ratio

end QMCLeafB.Round33M4


