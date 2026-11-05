-- Prove2me | Definitions.Def_QMCLeafB_thriceG1
-- name    : QMCLeafB_thriceG1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:32:59.793193+00:00
-- url     : https://prove2.me/theorems/39d14b77-4373-4f48-a2cc-759c635a775a
-- title:
--   QMCLeafB thriceG1
-- statement:
--   # `Check_thriceG1_m3` — the third stratum is INHABITED at the exemplar
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thrice
/-
# `Check_thriceG1_m3` — the third stratum is INHABITED at the exemplar

`Check_thrice_m3` splits the interior by the program's bit, and the residual is the third stratum:
nonempty **real** body, bit `false`.  `Check_audit2_m5` §5 names `(G₁, t₁)` as the exemplar, but the
library's nonemptiness fact there (`Check_emptybody_m5.body_nonempty_G₁`) is a **rational** member
`RelaxMem (wMatrixQ G₁) Q₁ …`, not an inhabitant of the *real* body
`BallFloor.relaxBodyLE (wMatrix G₁) …` that the stratum predicate is stated over.  The split would
be decorative if the real body were empty at the exemplar: then `runParts_of_split`'s empty branch
would already handle the point.

This file closes that gap by exhibiting an explicit real matrix

    Xw = !![1, -(1 + 3/3040000); -(1 + 3/3040000), 1]

and checking the three `relaxBodyLE` slots by exact arithmetic (`δ = dq = 1/380000`,
`u = t₁ − Rq/40000 = −2 − 1/304000`):

* PSD margin: `qfR Xw x + (δ/2)(x₀²+x₁²) = (x₀−x₁)² + (1/3040000)(3(x₀−x₁)² + x₀² + x₁²) ≥ 0`;
* diagonal: `|1 − 1| = 0 ≤ δ/4`;
* objective: `frob (wMatrix G₁) Xw = 2·(−(1 + 3/3040000)) = −2 − 3/1520000 = u + δ/2` (tight).

Hence `¬ BodyEmpty G₁ t₁` and, with `Check_thrice_m3.not_pinchFeasible_G₁` (no pinched member) and
`Check_thrice_m3.bit_false_of_not_pinchFeasible`, the exemplar is a genuine **third-stratum** point
for the program's own bit: nonempty real body, `false` bit, no pinched member anywhere.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` per declaration.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.ThriceG1_M3

open QuantumMaxCutEnergy

/-- The sliver instance (`Check_emptybody_m5`'s `G₁`). -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.EmptyBodyM5.G₁

/-- The sliver threshold. -/
abbrev t₁ : ℚ := -(2 : ℚ) + 71 / 1520000

/-- The campaign tolerance at `G₁`. -/
abbrev dq : ℚ := (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq

/-- **The explicit real witness** at the exemplar: unit diagonal, off-diagonal `-(1 + 3/3040000)`
(the rational witness `Q₁`'s own off-diagonal, cast to `ℝ`). -/
noncomputable def Xw : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -(1 + 3 / 3040000); -(1 + 3 / 3040000), 1]

theorem qf_Xw (x : Fin 2 → ℝ) :
    QMCLeafB.BallFloor.qfR Xw x
      = x 0 ^ 2 + 2 * (-(1 + 3 / 3040000)) * (x 0 * x 1) + x 1 ^ 2 := by
  simp [QMCLeafB.BallFloor.qfR, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Xw]
  ring

#print axioms QMCLeafB.ThriceG1_M3.qf_Xw

theorem frob_Xw :
    QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) Xw = -(2 + 3 / 1520000) := by
  simp [QMCLeafB.BallFloor.frob, Fin.sum_univ_two, QMCLeafB.wMatrix, Xw, G₁]
  norm_num

#print axioms QMCLeafB.ThriceG1_M3.frob_Xw

theorem dq_eq : dq = 1 / 380000 := QMCLeafB.EmptyBodyM5.dq₁_eq

#print axioms QMCLeafB.ThriceG1_M3.dq_eq

/-- **The witness lies in the real relaxed body at `(G₁, t₁)`** — the three slots of
`BallFloor.relaxBodyLE`, each by exact arithmetic. -/
theorem relaxBodyLE_G₁_Xw :
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
      ((t₁ : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)) ((dq : ℚ) : ℝ) Xw := by
  have hRq : QMCLeafB.EngineRuntime.Rq G₁ = 2 := QMCLeafB.EmptyBodyM5.Rq_G₁
  have hdqv : ((dq : ℚ) : ℝ) = 1 / 380000 := by
    rw [dq_eq]; norm_num
  have huv : (t₁ : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)
      = -(2 + 5 / 1520000) := by
    rw [hRq]
    simp only [t₁]
    push_cast
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hsum : (∑ i : Fin 2, x i ^ 2) = x 0 ^ 2 + x 1 ^ 2 := by
      simp [Fin.sum_univ_two]
    rw [qf_Xw x, hdqv, hsum]
    have hsos : (0 : ℝ) ≤ (x 0 - x 1) ^ 2
        + (1 / 3040000) * (3 * (x 0 - x 1) ^ 2 + x 0 ^ 2 + x 1 ^ 2) := by
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0), sq_nonneg (x 1)]
    nlinarith [hsos]
  · intro i
    have h4 : (0 : ℝ) ≤ ((dq : ℚ) : ℝ) / 4 := by
      rw [hdqv]; norm_num
    have hii : Xw i i = 1 := by
      fin_cases i <;> simp [Xw]
    rw [hii, sub_self, abs_zero]
    exact h4
  · rw [frob_Xw, huv, hdqv]
    norm_num

#print axioms QMCLeafB.ThriceG1_M3.relaxBodyLE_G₁_Xw

/-- **The real body at the exemplar is NONEMPTY** — the stratum predicate's first conjunct,
machine-checked at the definition (not the rational surrogate). -/
theorem not_bodyEmpty_G₁ : ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ t₁
    (QMCLeafB.UnionShallow.paramsKbc2 G₁) :=
  fun h => h Xw relaxBodyLE_G₁_Xw

#print axioms QMCLeafB.ThriceG1_M3.not_bodyEmpty_G₁

/-- **The exemplar is a third-stratum point for every `false`-reading bit.**  Nonempty real body
(above) and no pinched member (`Check_thrice_m3.not_pinchFeasible_G₁`) are both unconditional here,
so stratum 3 is not vacuous and the ok lane's `PinchFeasible` — hence `CoreDataG`'s `hmem` — is
impossible there. -/
theorem third_stratum_inhabited :
    ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ t₁ (QMCLeafB.UnionShallow.paramsKbc2 G₁)
      ∧ ¬ QMCLeafB.ThriceM3.PinchFeasible G₁ t₁ (QMCLeafB.UnionShallow.paramsKbc2 G₁) :=
  ⟨not_bodyEmpty_G₁, QMCLeafB.ThriceM3.not_pinchFeasible_G₁⟩

#print axioms QMCLeafB.ThriceG1_M3.third_stratum_inhabited



/-! ## 3b.  `ResidSplit` does not avoid the exemplar

Now that the real body at `(G₁, t₁)` is known to be nonempty, the audit's split
(`Check_audit2_m5.ResidSplit`) is seen to **demand `CoreDataG` at the exemplar**.  There the verdict
equation forces every round below the horizon to be a `cut` round (`false_bit_all_cut`) — the
whole-window drift pair — and no pinched matrix is a member (`not_pinchFeasible_G₁`), so the demand
is unreachable.  This is why the phase-23 residual has to be keyed by the *bit* and stated at
`RunParts` (`ThriceM3.ThirdStratum`), and why a `ResidSplit` production should not be attempted. -/

/-- **Any `ResidSplit` producer owes the conduit at `(G₁, t₁)`.** -/
def residSplit_demands_at_G₁ {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (H : QMCLeafB.Audit2M5.ResidSplit o QMCLeafB.UnionShallow.paramsKbc2)
    (hn : 2 ≤ G₁.n) :
    QMCLeafB.EndgameM2.CoreDataG o G₁ t₁ (QMCLeafB.UnionShallow.paramsKbc2 G₁) hn :=
  H G₁ t₁ hn QMCLeafB.EmptyBodyM5.t₁_mem_bracket.1
    QMCLeafB.EmptyBodyM5.t₁_mem_bracket.2 not_bodyEmpty_G₁

#print axioms QMCLeafB.ThriceG1_M3.residSplit_demands_at_G₁

/-! ## 4.  The threshold direction is monotone — in the direction that hurts

`relaxBodyLE`'s threshold `u` occurs only in the *upper* objective bound `frob A X ≤ u + δ/2`, so
raising `t` only enlarges the body.  Hence emptiness transports **downward** in `t`, and the
nonempty stratum at `G₁` is a whole interval `[t₁, −Rq/40000)`, not a point.  (This is also why a
monotonicity argument cannot transport `RunParts` from an empty body *up* to `t₁`: `RunParts`'
`hbody`/separation slots are hardest exactly where the body is largest.) -/

/-- The relaxed body is monotone in the threshold. -/
theorem bodyLE_mono {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u u' δ : ℝ} (hu : u ≤ u')
    {X : Matrix (Fin n) (Fin n) ℝ} (h : QMCLeafB.BallFloor.relaxBodyLE A u δ X) :
    QMCLeafB.BallFloor.relaxBodyLE A u' δ X :=
  ⟨h.1, h.2.1, le_trans h.2.2 (by linarith)⟩

#print axioms QMCLeafB.ThriceG1_M3.bodyLE_mono

/-- **Emptiness is downward closed in the threshold.** -/
theorem bodyEmpty_of_le {G : QuantumMaxCutEnergy.Input} {t t' : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (htt : t ≤ t')
    (h : QMCLeafB.ThriceM3.BodyEmpty G t' P) : QMCLeafB.ThriceM3.BodyEmpty G t P := by
  intro X hX
  have hle : (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
      ≤ (t' : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
    have hcast : (t : ℝ) ≤ (t' : ℝ) := by exact_mod_cast htt
    linarith
  exact h X (bodyLE_mono hle hX)

#print axioms QMCLeafB.ThriceG1_M3.bodyEmpty_of_le

/-- **The third stratum at `G₁` is an interval**: every threshold at or above `t₁` (inside the
bracket) carries a nonempty real body.  So the residual is not a single bad point. -/
theorem not_bodyEmpty_of_le {t : ℚ} (htt : t₁ ≤ t) :
    ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ t (QMCLeafB.UnionShallow.paramsKbc2 G₁) :=
  fun h => not_bodyEmpty_G₁ (bodyEmpty_of_le htt h)

#print axioms QMCLeafB.ThriceG1_M3.not_bodyEmpty_of_le

/-! ## 5.  Adapters: the zip needs only `hon` and the third stratum -/

/-- `OkSupply` (one frozen member at every `true`-bit point) gives the true-bit strand. -/
def trueBitCore_of_okSupply {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.OkProd_M8.OkSupply o Pfam) :
    QMCLeafB.ThriceM3.TrueBitCore o Pfam :=
  fun G t hn hlo hhi hT => QMCLeafB.OkProd_M8.coreDataG_of_okPoint (H G t hn hlo hhi hT) hT

#print axioms QMCLeafB.ThriceG1_M3.trueBitCore_of_okSupply

/-- The campaign's own `hon` slot (`Check_verdbridge_m4.flag_true_of_okV` at the lower-body round)
gives the true-bit strand; nothing analytic is added. -/
def trueBitCore_of_honSupply {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.OkProd_M8.HonSupply o Pfam) :
    QMCLeafB.ThriceM3.TrueBitCore o Pfam :=
  trueBitCore_of_okSupply (QMCLeafB.OkProd_M8.okSupply_of_hon H)

#print axioms QMCLeafB.ThriceG1_M3.trueBitCore_of_honSupply

/-- **`hon` + the third stratum = the triple residual.** -/
noncomputable def tripleSupply_of_hon {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (Hhon : QMCLeafB.OkProd_M8.HonSupply o Pfam)
    (Hthird : QMCLeafB.ThriceM3.ThirdStratum o Pfam) :
    QMCLeafB.ThriceM3.TripleSupply o Pfam where
  trueBit := trueBitCore_of_honSupply Hhon
  third := Hthird

#print axioms QMCLeafB.ThriceG1_M3.tripleSupply_of_hon

/-- **The verbatim `d9f601e5` sentence from `hon` + the third stratum** — the shortest
consumable form of the whole leaf: campaign data (`rb`, `cXp`, `hbit`, `hokp`, `hdia`,
`hemptyR`), the `hon` slot, and `ThirdStratum`. -/
theorem solution_of_hon_and_third
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hdia : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) (i : Fin G.n),
      cXp G t k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (Hhon : QMCLeafB.OkProd_M8.HonSupply QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2)
    (Hthird : QMCLeafB.ThriceM3.ThirdStratum QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) :
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
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.ThriceM3.solution_of_triple rb cXp hbit hokp hdia hemptyR
    (tripleSupply_of_hon Hhon Hthird)

#print axioms QMCLeafB.ThriceG1_M3.solution_of_hon_and_third

end QMCLeafB.ThriceG1_M3


