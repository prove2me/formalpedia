-- Prove2me | Definitions.Def_QMCLeafB_emptybody
-- name    : QMCLeafB_emptybody
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:34:00.172802+00:00
-- url     : https://prove2.me/theorems/bbbc9c04-76a8-4af9-b722-4cf3bed86132
-- title:
--   QMCLeafB emptybody
-- statement:
--   # leaf B phase 21 — REFUTATION, machine-checked: `CoreDataF` / `ResidFinite` is UNSATISFIABLE
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_records_m2
/-
# leaf B phase 21 — REFUTATION, machine-checked: `CoreDataF` / `ResidFinite` is UNSATISFIABLE
  at a refuted empty-body point   (swarm `smw1m5nkm`, member m5, direction d1 `falsify-hcutfin`)

## What is checked here

`RecordsM2.solution_of_finite` (phase 20) derives the leaf's verbatim sentence from

  `ResidFinite (loopBit init0 round verdict Tbc2) UnionShallow.paramsKbc2`,

i.e. from one `CoreDataF o G t (paramsKbc2 G) hn` at **every** interior `(G, t)`.  This file shows
that hypothesis is **unsatisfiable**, so `solution_of_finite` is true but vacuous and cannot be the
leaf's closing stroke.

The counterexample is the phase-19/20 relaying input `G₀` (two vertices, the single edge of weight
`1/2`; `Rq G₀ = 1`, `dqShallow G₀ = 1/400000`, `ε G₀ = 1/40000`) at an **interior refuted**
threshold.  Two facts, in this order:

* §1  **the objective floor of a `RelaxMem` member**: for `A = wMatrixQ G₀` (zero diagonal,
  off-diagonal `1/2`) every rational `Q` with the three `RelaxMem` slots at tolerance `δ` satisfies
  `⟪A, Q⟫ = (Q₀₁ + Q₁₀)/2 ≥ -(1 + 3δ/4)`.  The proof is the two diagonal slots (`diag_near`
  upper bounds `Q₀₀, Q₁₁ ≤ 1 + δ/4`) plus one `psd_margin` test at `x = (1,1)`:
  `-δ ≤ Q₀₀ + Q₀₁ + Q₁₀ + Q₁₁`.  No symmetry, no eigenvalue, no square root.
* §2  **the body is empty on a whole interval**: `trace_le` asks `⟪A, Q⟫ ≤ t - ε + δ/2`, and at
  `δ = 1/400000`, `ε = 1/40000` the two bounds are incompatible for every
  `t < -(1599965/1600000) = -0.999978125`, an interval of interior thresholds that is not empty
  (`-1 ≤ t < -ε` is much wider).  At `t₀ = -99999/100000` the floor is `-1600003/1600000` and the
  ceiling is `-800011/800000`, i.e. the floor exceeds the ceiling by `19/1600000 > 0`.
* §3  consequently `flagOf … k = false` for **every** round `k` and **every** state family `X`
  (`flagOf` is the canonical member test), so `CoreDataF.hcutfin` — which says
  `flagOf … k = false → k < K·m` — reads `K·m < K·m` at `k = K·m`.
* §4  hence `¬ Nonempty (CoreDataF o G₀ t₀ (paramsKbc2 G₀) hn)` for **every** verdict bit `o`, and
  `¬ Nonempty (ResidFinite o paramsKbc2)` for **every** `o`.  In particular the hypothesis of
  `solution_of_finite` is empty.
* §5  the honest diagnosis: the *only* field of `CoreDataF` that fails at this point is `hcutfin`
  (the `∀k`-flavoured horizon condition); on the empty body `hverdict` is forced to `false` (so the
  horizon-bounded restatement loses nothing here), and the two drift slots are genuine obligations
  only below the horizon `K·m`.  That is the shape `SimLoop.simulate_refuted_sound`'s `K·m` window
  actually needs.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.EmptyBodyM5

open QuantumMaxCutEnergy

/-! ## 0.  The counterexample's parameters -/

/-- The refuting input: two vertices, one edge of weight `1/2` (phase 19/20's `G₀`; `abbrev`, so
`Fin G₀.n` is reducibly `Fin 2`). -/
abbrev G₀ : QuantumMaxCutEnergy.Input := QMCLeafB.ResidRefute.G₀

/-- The campaign's parameters at `G₀` (the family `solution_of_finite` uses). -/
abbrev P₀ : QMCLeafB.FinalStroke.RunParams G₀ := QMCLeafB.UnionShallow.paramsKbc2 G₀

/-- The campaign's oracle tolerance at `G₀`. -/
abbrev dq₀ : ℚ := P₀.dq

/-- The refuted interior threshold used for the headline statement. -/
abbrev t₀ : ℚ := -(99999 / 100000)

/-- The leaf's additive slack at `G₀`. -/
theorem eps_G₀ : QMCLeafB.RundataCert.eps G₀ = 1 / 40000 := by
  unfold QMCLeafB.RundataCert.eps
  norm_num [QMCLeafB.ResidRefute.Rq_G₀]

/-- **`dqShallow G₀ = 1/400000`** — the campaign tolerance at the refuting input (the same
computation as `ClosingStrokeM6.dqShallow_G₀`, re-established here so that this file depends on
`Check_records_m2` only). -/
theorem dq₀_eq : dq₀ = 1 / 400000 := by
  unfold dq₀ P₀
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  unfold QMCLeafB.RundataParams.dqShallow QMCLeafB.RundataParams.dqShallowCore
  rw [if_neg (by rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num)]
  unfold QMCLeafB.RundataCert.eps
  rw [QMCLeafB.ResidRefute.Rq_G₀]
  norm_num

/-- The six entries of the weight matrix of `G₀` (the four that matter; the matrix is symmetric with
zero diagonal). -/
theorem wMatrixQ_G₀_00 :
    QMCLeafB.Finalization.wMatrixQ G₀ (0 : Fin 2) (0 : Fin 2) = 0 :=
  QMCLeafB.Finalization.wMatrixQ_apply_of_eq

theorem wMatrixQ_G₀_01 :
    QMCLeafB.Finalization.wMatrixQ G₀ (0 : Fin 2) (1 : Fin 2) = 1 / 2 := by
  unfold QMCLeafB.Finalization.wMatrixQ
  norm_num [QMCLeafB.ResidRefute.G₀]

theorem wMatrixQ_G₀_10 :
    QMCLeafB.Finalization.wMatrixQ G₀ (1 : Fin 2) (0 : Fin 2) = 1 / 2 := by
  unfold QMCLeafB.Finalization.wMatrixQ
  norm_num [QMCLeafB.ResidRefute.G₀]

theorem wMatrixQ_G₀_11 :
    QMCLeafB.Finalization.wMatrixQ G₀ (1 : Fin 2) (1 : Fin 2) = 0 :=
  QMCLeafB.Finalization.wMatrixQ_apply_of_eq

/-! ## 1.  The objective floor of a member at a `2 × 2` input with `A = !![0, 1/2; 1/2, 0]`

The relaxation's three numeric slots, used once each:

* `diag_near e₀` and `diag_near e₁` — upper bounds on the diagonal;
* `psd_margin (1,1)` — `-(δ/2)·2 ≤ Q₀₀ + Q₀₁ + Q₁₀ + Q₁₁`, the only PSD input needed.

Together: `Q₀₁ + Q₁₀ ≥ -δ - Q₀₀ - Q₁₁ ≥ -δ - 2(1 + δ/4) = -2(1 + 3δ/4)`, and `⟪A, Q⟫` is exactly the
half of that sum.  Note there is **no** symmetry hypothesis on `Q` in `RelaxMem`, and none is used
here. -/

theorem frob_ge_of_relaxMem {u δ : ℚ} {A Q : Matrix (Fin 2) (Fin 2) ℚ}
    (h00 : A 0 0 = 0) (h01 : A 0 1 = 1 / 2) (h10 : A 1 0 = 1 / 2) (h11 : A 1 1 = 0)
    (hM : QMCLeafB.RelaxOracle.RelaxMem A Q u δ) :
    -(1 + 3 * δ / 4) ≤ QMCLeafB.SepOracle.frob A Q := by
  have hdiag0 : Q 0 0 ≤ 1 + δ / 4 := by
    have h := (abs_le.mp (hM.diag_near 0)).2
    linarith
  have hdiag1 : Q 1 1 ≤ 1 + δ / 4 := by
    have h := (abs_le.mp (hM.diag_near 1)).2
    linarith
  have hpsd := hM.psd_margin (fun _ : Fin 2 => (1 : ℚ))
  have hsq : (∑ i : Fin 2, ((1 : ℚ)) ^ 2) = 2 := by norm_num
  have hqf : QMCLeafB.SepOracle.qf Q (fun _ : Fin 2 => (1 : ℚ))
      = Q 0 0 + Q 0 1 + Q 1 0 + Q 1 1 := by
    rw [QMCLeafB.SepOracle.qf_eq_sum]
    simp [Fin.sum_univ_two]
    ring
  rw [hsq, hqf] at hpsd
  have hfrob : QMCLeafB.SepOracle.frob A Q = 1 / 2 * Q 0 1 + 1 / 2 * Q 1 0 := by
    simp [QMCLeafB.SepOracle.frob, Fin.sum_univ_two, h00, h01, h10, h11]
  rw [hfrob]
  linarith

#print axioms QMCLeafB.EmptyBodyM5.frob_ge_of_relaxMem

/-- The floor at `G₀`'s own weight matrix and the campaign's tolerance. -/
theorem frob_ge_G₀ {u : ℚ} {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hM : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₀) Q u dq₀) :
    -(1 + 3 * dq₀ / 4) ≤ QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G₀) Q :=
  frob_ge_of_relaxMem wMatrixQ_G₀_00 wMatrixQ_G₀_01 wMatrixQ_G₀_10 wMatrixQ_G₀_11 hM

#print axioms QMCLeafB.EmptyBodyM5.frob_ge_G₀

/-! ## 2.  The relaxed body at `(G₀, t)` is empty for every `t < -1599965/1600000`

`trace_le` requires `⟪A, Q⟫ ≤ (t - ε) + δ/2`; §1 requires `⟪A, Q⟫ ≥ -(1 + 3δ/4)`.  At
`δ = 1/400000`, `ε = 1/40000` the first of these is the stronger requirement exactly when
`t < ε - 1 - 5δ/4 = 1/40000 - 1 - 5/1600000 = -1599965/1600000 = -0.999978125`. -/

theorem not_relaxMem_G₀_of_lt {t : ℚ} (ht : t < -(1599965 / 1600000))
    (Q : Matrix (Fin 2) (Fin 2) ℚ) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₀) Q
        (t - QMCLeafB.RundataCert.eps G₀) dq₀ := by
  intro hM
  have hge := frob_ge_G₀ hM
  have hle := hM.trace_le
  rw [dq₀_eq] at hge hle
  rw [eps_G₀] at hle
  linarith

#print axioms QMCLeafB.EmptyBodyM5.not_relaxMem_G₀_of_lt

/-- **The body is empty at `t₀ = -99999/100000`.** -/
theorem not_relaxMem_G₀ (Q : Matrix (Fin 2) (Fin 2) ℚ) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₀) Q
        (t₀ - QMCLeafB.RundataCert.eps G₀) dq₀ :=
  not_relaxMem_G₀_of_lt (by unfold t₀; norm_num) Q

#print axioms QMCLeafB.EmptyBodyM5.not_relaxMem_G₀

/-- **The receipt**: at `t₀` the objective floor of a member exceeds the ceiling `trace_le` demands
by `19/1600000` (the exact gap; `1.1875·10⁻⁵`). -/
theorem the_gap : -(1 + 3 * dq₀ / 4) - (t₀ - QMCLeafB.RundataCert.eps G₀ + dq₀ / 2)
    = 19 / 1600000 := by
  rw [dq₀_eq, eps_G₀]
  unfold t₀
  norm_num

#print axioms QMCLeafB.EmptyBodyM5.the_gap

/-! ## 3.  An empty body makes *every* canonical flag `false`

`FlagsM5.flagOf` decides the `ok` bit by `RelaxMem` of the queried centre; with no member anywhere,
no centre family can raise a `true` flag.  This is the total form of the phase-19 observation
(`FlagsM5.flagOf_all_false`), specialised to the run's own pinched centres `cXst`. -/

theorem flagOf_false_of_emptyBody {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (hempty : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) P.dq)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    QMCLeafB.FlagsM5.flagOf G t P cX k = false :=
  QMCLeafB.FlagsM5.flagOf_false_of_not_mem G t P cX k (hempty (cX k))

#print axioms QMCLeafB.EmptyBodyM5.flagOf_false_of_emptyBody

/-- **An empty body refutes `CoreDataF`** — for every verdict bit `o`, every round count and every
state family.  This is the structural half of the refutation: `hcutfin` is a demand for member
centres *beyond* the horizon, and on an empty body there are no members at all. -/
theorem not_coreDataF_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (hempty : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) P.dq)
    (D : QMCLeafB.RecordsM2.CoreDataF o G t P hn) : False := by
  have hf : QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) (P.K * P.m)
      = false :=
    flagOf_false_of_emptyBody hempty (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) (P.K * P.m)
  exact absurd (D.hcutfin (P.K * P.m) hf) (lt_irrefl _)

#print axioms QMCLeafB.EmptyBodyM5.not_coreDataF_of_emptyBody

/-! ## 4.  The instance: the phase-20 residual is empty at `(G₀, -99999/100000)`

Nothing about the programme's choice of `o = loopBit …` is used — the refutation is uniform in the
verdict bit, which is what makes it structural rather than arithmetic: `hverdict` can always be
satisfied by taking `o G₀ t₀ = false`, so `hcutfin` alone is the unsatisfiable slot. -/

theorem not_coreDataF_G₀ (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (hn : 2 ≤ G₀.n)
    (D : QMCLeafB.RecordsM2.CoreDataF o G₀ t₀ P₀ hn) : False :=
  not_coreDataF_of_emptyBody (G := G₀) (t := t₀) (P := P₀) (fun Q => not_relaxMem_G₀ Q) D

#print axioms QMCLeafB.EmptyBodyM5.not_coreDataF_G₀

/-- **`CoreDataF` is uninhabited at the refuted empty-body point**, for every `o`. -/
theorem coreDataF_G₀_empty (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (hn : 2 ≤ G₀.n) :
    ¬ Nonempty (QMCLeafB.RecordsM2.CoreDataF o G₀ t₀ P₀ hn) :=
  fun ⟨D⟩ => not_coreDataF_G₀ o hn D

#print axioms QMCLeafB.EmptyBodyM5.coreDataF_G₀_empty

/-- `t₀` is inside the interior bracket at `G₀`. -/
theorem t₀_mem_bracket :
    -QMCLeafB.EngineRuntime.Rq G₀ ≤ t₀ ∧
      (t₀ : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G₀ / 40000 : ℚ)) : ℝ) := by
  constructor
  · rw [QMCLeafB.ResidRefute.Rq_G₀]; unfold t₀; norm_num
  · rw [QMCLeafB.ResidRefute.Rq_G₀]; unfold t₀; norm_num

#print axioms QMCLeafB.EmptyBodyM5.t₀_mem_bracket

/-- **The refutation is uniform in the parameter family**: any `P : RunParams G₀` whose tolerance is
the campaign's `dqShallow G₀ = 1/400000` is refuted at `t₀` — in particular both live families
(`paramsKbc2`, and `paramsShallow` at any `K` with the same `dq`). -/
theorem coreDataF_G₀_empty_of_dq (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : QMCLeafB.FinalStroke.RunParams G₀) (hn : 2 ≤ G₀.n) (hdq : P.dq = 1 / 400000) :
    ¬ Nonempty (QMCLeafB.RecordsM2.CoreDataF o G₀ t₀ P hn) := by
  rintro ⟨D⟩
  have hf : QMCLeafB.FlagsM5.flagOf G₀ t₀ P (QMCLeafB.RecordsM2.cXst G₀.n D.X P.dq) (P.K * P.m)
      = false := by
    refine flagOf_false_of_emptyBody (G := G₀) (t := t₀) (P := P) ?_
      (QMCLeafB.RecordsM2.cXst G₀.n D.X P.dq) (P.K * P.m)
    intro Q hM
    have hge := frob_ge_of_relaxMem wMatrixQ_G₀_00 wMatrixQ_G₀_01 wMatrixQ_G₀_10 wMatrixQ_G₀_11 hM
    have hle := hM.trace_le
    rw [hdq] at hge hle
    rw [eps_G₀] at hle
    unfold t₀ at hle
    linarith
  exact absurd (D.hcutfin (P.K * P.m) hf) (lt_irrefl _)

#print axioms QMCLeafB.EmptyBodyM5.coreDataF_G₀_empty_of_dq

/-- **`ResidFinite` is uninhabited at any family with `dq = 1/400000` at `G₀`.** -/
theorem residFinite_empty_of_dq (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hdq : (Pfam G₀).dq = 1 / 400000) :
    ¬ Nonempty (QMCLeafB.RecordsM2.ResidFinite o Pfam) := by
  rintro ⟨H⟩
  exact coreDataF_G₀_empty_of_dq o (Pfam G₀) (le_refl 2) hdq
    ⟨H G₀ t₀ (le_refl 2) t₀_mem_bracket.1 t₀_mem_bracket.2⟩

#print axioms QMCLeafB.EmptyBodyM5.residFinite_empty_of_dq

/-- **`ResidFinite` is uninhabited** at the campaign's parameter family, for every verdict bit. -/
theorem residFinite_empty (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.RecordsM2.ResidFinite o QMCLeafB.UnionShallow.paramsKbc2) := by
  rintro ⟨H⟩
  exact coreDataF_G₀_empty o (le_refl 2)
    ⟨H G₀ t₀ (le_refl 2) t₀_mem_bracket.1 t₀_mem_bracket.2⟩

#print axioms QMCLeafB.EmptyBodyM5.residFinite_empty

/-- The same at the family `solution_of_finite` names, by the uniform-family lemma. -/
theorem residFinite_empty' (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.RecordsM2.ResidFinite o QMCLeafB.UnionShallow.paramsKbc2) :=
  residFinite_empty_of_dq o QMCLeafB.UnionShallow.paramsKbc2
    (by rw [QMCLeafB.UnionShallow.paramsKbc2_dq]; exact dq₀_eq)

#print axioms QMCLeafB.EmptyBodyM5.residFinite_empty'

/-- **The hypothesis of phase-20's `solution_of_finite` is empty.**  (So that theorem is true but
cannot be the leaf's closing stroke: its premise is unsatisfiable.) -/
theorem solution_of_finite_hypothesis_empty :
    ¬ Nonempty (QMCLeafB.RecordsM2.ResidFinite
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :=
  residFinite_empty _

#print axioms QMCLeafB.EmptyBodyM5.solution_of_finite_hypothesis_empty

/-! ## 5.  The diagnosis: which slot fails, and what the restated shape must keep

On the empty body `hverdict` is forced (`o G₀ t₀ = false`), so it costs nothing; `hcutfin` is the
only slot that *cannot* be met.  Both facts are recorded here because they are what the
horizon-bounded restatement has to preserve: the verdict equation stays at horizon `K·m`, and the
two drift slots stay at the run's cut rounds **below** `K·m` (where `simulate_refuted_sound`
consumes them). -/

/-- On the empty body the verdict bit is forced to `false`. -/
theorem hverdict_eq_false_G₀ (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (hn : 2 ≤ G₀.n)
    (D : QMCLeafB.RecordsM2.CoreDataF o G₀ t₀ P₀ hn) : o G₀ t₀ = false := by
  have h := D.hverdict
  have hany : QMCLeafB.SimLoop.anyOk
      (QMCLeafB.FlagsM5.flagOf G₀ t₀ P₀ (QMCLeafB.RecordsM2.cXst G₀.n D.X P₀.dq)) (P₀.K * P₀.m)
      = false :=
    QMCLeafB.ResidRefute.anyOk_all_false _ (P₀.K * P₀.m)
      (fun k _ => flagOf_false_of_emptyBody (G := G₀) (t := t₀) (P := P₀)
        (fun Q => not_relaxMem_G₀ Q) (QMCLeafB.RecordsM2.cXst G₀.n D.X P₀.dq) k)
  rw [hany] at h
  exact h

#print axioms QMCLeafB.EmptyBodyM5.hverdict_eq_false_G₀

/-! ## 7.  Pinch audit: the diagonal overwrite is margin-safe only for *exactly* PSD points

`CoreDataF`'s centres are the **pinched** states `cXst n X dq k = diagPinch (stMat n (X k)) dq`
(`CentreAdm.diagPinch`, diagonal overwritten by `1 - dq/4`).  The tempting shortcut on the production
side is "a member can always be pinched, so keep the pinch and forget the base".  **That is false**:
the pinch moves the diagonal *down* by up to `δ/4` per coordinate, and `qf_diagPinch` shows that this
costs exactly `∑ᵢ (Qᵢᵢ - (1 - δ/4)) xᵢ²` of quadratic-form value — which can spend the whole
`psd_margin` budget.  §7.1 is the repaired statement (it holds at *exactly* PSD unit-diagonal
points, i.e. at the ok-branch's states once brick 1 certifies `EvRun 0`); §7.2 is the
counterexample that kills the shortcut in general, with exact rationals. -/

/-- **The repaired statement.**  At a point that is *exactly* PSD (`0 ≤ qf Q x` for every `x`) with
*unit* diagonal and trace already below the level, the diagonal overwrite is free: the `δ/4`
reduction is absorbed by the `δ/2` margin.  This is the shape the ok-branch production needs (the
states there are unit-diagonal and exactly PSD by `StateDiag`/`psd_of_exactRun`), and it is the only
form in which the pinch is margin-preserving. -/
theorem relaxMem_diagPinch_of_psd {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hA : ∀ i, A i i = 0) (hdq : 0 < δ) (hdq4 : δ ≤ 4)
    (hunit : ∀ i, Q i i = 1)
    (hpsd : ∀ x : Fin n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x)
    (htrace : QMCLeafB.SepOracle.frob A Q ≤ u + δ / 2) :
    QMCLeafB.RelaxOracle.RelaxMem A (QMCLeafB.CentreAdm.diagPinch Q δ) u δ where
  δ_pos := hdq
  psd_margin := by
    intro x
    rw [QMCLeafB.CentreAdm.qf_diagPinch]
    have hsplit : ∑ i, ((1 - δ / 4) - Q i i) * x i ^ 2
        = -(δ / 4) * ∑ i, x i ^ 2 := by
      have hterm : ∀ i : Fin n, ((1 - δ / 4) - Q i i) * x i ^ 2 = (-(δ / 4)) * x i ^ 2 := by
        intro i
        rw [hunit i]
        ring
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i), ← Finset.mul_sum]
    rw [hsplit]
    have hnn : 0 ≤ ∑ i, x i ^ 2 :=
      Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (x i))
    have h0 := hpsd x
    nlinarith
  diag_near := fun i => QMCLeafB.CentreAdm.abs_diagPinch Q hdq hdq4 i
  trace_le := by
    rw [QMCLeafB.CentreAdm.frob_diagPinch hA]
    exact htrace

#print axioms QMCLeafB.EmptyBodyM5.relaxMem_diagPinch_of_psd

/-- The counterexample's member: unit diagonal, on the `psd_margin` boundary at `δ = 1/2`, and its
objective is the level exactly. -/
theorem member_counterexample :
    QMCLeafB.RelaxOracle.RelaxMem (!![0, (1 : ℚ); (1 : ℚ), 0])
      (!![1, (5 : ℚ) / 4; (5 : ℚ) / 4, 1]) (9 / 4) (1 / 2) where
  δ_pos := by norm_num
  psd_margin := by
    intro x
    rw [QMCLeafB.SepOracle.qf_eq_sum]
    simp [Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 + x 1)]
  diag_near := by
    intro i
    fin_cases i <;> norm_num
  trace_le := by
    simp [QMCLeafB.SepOracle.frob]
    norm_num

#print axioms QMCLeafB.EmptyBodyM5.member_counterexample

/-- **The pinch shortcut is dead.**  `Q = !![1, 5/4; 5/4, 1]` is a `RelaxMem` member at `δ = 1/2`,
`u = 9/4`, and it sits exactly on the `psd_margin` boundary.  The diagonal overwrite moves the
diagonal to `7/8`, which subtracts `δ/2` from `qf` at `x = (1,-1)`: the pinched matrix has
`qf = -3/4` against the required `-1/4`.  So a member **cannot** be pinched in general, and any
production route that freezes at a pinched centre must first certify the base point as *exactly* PSD
(the `EvRun 0` route), not merely as a member. -/
theorem pinch_of_member_false :
    ¬ QMCLeafB.RelaxOracle.RelaxMem (!![0, (1 : ℚ); (1 : ℚ), 0])
        (QMCLeafB.CentreAdm.diagPinch (!![1, (5 : ℚ) / 4; (5 : ℚ) / 4, 1]) (1 / 2)) (9 / 4) (1 / 2) := by
  intro hM
  have h := hM.psd_margin (fun i : Fin 2 => if i = 0 then (1 : ℚ) else -1)
  have hsq : (∑ i : Fin 2, (if i = 0 then (1 : ℚ) else -1) ^ 2) = 2 := by
    simp
  have hqf : QMCLeafB.SepOracle.qf
      (QMCLeafB.CentreAdm.diagPinch (!![1, (5 : ℚ) / 4; (5 : ℚ) / 4, 1]) (1 / 2))
      (fun i : Fin 2 => if i = 0 then (1 : ℚ) else -1) = -(3 / 4) := by
    rw [QMCLeafB.SepOracle.qf_eq_sum]
    simp [QMCLeafB.CentreAdm.diagPinch]
    norm_num
  rw [hsq, hqf] at h
  norm_num at h

#print axioms QMCLeafB.EmptyBodyM5.pinch_of_member_false

/-! ## 9.  Second refutation: the shape fails where the body is **nonempty**

`CoreDataF`'s centres are `cXst n X dq k = diagPinch (stMat n (X k)) dq`, whose diagonal is pinned to
the **lower edge** `1 - dq/4` of `RelaxMem.diag_near`'s band.  At a pinched centre the `psd_margin`
therefore starts from a base value `1 - dq/4` rather than from `1`: the admissible quadratic forms are
`dq/2` tighter than at a unit-diagonal centre.  So there is a **sliver of thresholds just above the
emptiness region** where the body is nonempty but **no pinched matrix is a member**, and there
`hcutfin` fails for exactly the same reason as on an empty body.

This is not a curiosity: it is why `hcutfin` cannot be repaired by restricting to nonempty bodies.
At `G₁` (two vertices, one edge of weight `1`; `Rq = 2`, `dqShallow = 1/380000`,
`ε = 1/20000`) and `t₁ = -2 + 71/1520000` (inside the interior bracket), the body contains
`Q₁ = !![1, a; a, 1]` with `a = -(1 + 3/3040000)` (§9.3), while no `Q` with diagonal `1 - dq/4` is a
member (§9.2).  Hence `CoreDataF` is uninhabited at `(G₁, t₁)` — a point whose relaxed body is
**nonempty** — and `ResidFinite` is refuted there as well. -/

/-- The second input: two vertices, one edge of weight `1` (`Rq G₁ = 2`). -/
abbrev G₁ : QuantumMaxCutEnergy.Input := ⟨2, fun _ => (1 : ℚ≥0)⟩

theorem Rq_G₁ : QMCLeafB.EngineRuntime.Rq G₁ = 2 := by
  unfold QMCLeafB.EngineRuntime.Rq
  show 2 * (∑ e : Edge G₁.n, ((G₁.weights e : ℚ≥0) : ℚ)) = 2
  rw [QMCLeafB.ResidRefute.univ_edge_two, Finset.sum_singleton]
  norm_num

theorem eps_G₁ : QMCLeafB.RundataCert.eps G₁ = 1 / 20000 := by
  unfold QMCLeafB.RundataCert.eps
  rw [Rq_G₁]
  norm_num

theorem dq₁_eq : (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq = 1 / 380000 := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  unfold QMCLeafB.RundataParams.dqShallow QMCLeafB.RundataParams.dqShallowCore
  rw [if_neg (by rw [Rq_G₁]; norm_num)]
  unfold QMCLeafB.RundataCert.eps
  rw [Rq_G₁]
  norm_num

/-- The tolerance in the unfolded shape. -/
theorem dqShallow_G₁ : QMCLeafB.RundataParams.dqShallow G₁ = 1 / 380000 := dq₁_eq

theorem wMatrixQ_G₁_00 :
    QMCLeafB.Finalization.wMatrixQ G₁ (0 : Fin 2) (0 : Fin 2) = 0 :=
  QMCLeafB.Finalization.wMatrixQ_apply_of_eq

theorem wMatrixQ_G₁_11 :
    QMCLeafB.Finalization.wMatrixQ G₁ (1 : Fin 2) (1 : Fin 2) = 0 :=
  QMCLeafB.Finalization.wMatrixQ_apply_of_eq

theorem wMatrixQ_G₁_01 :
    QMCLeafB.Finalization.wMatrixQ G₁ (0 : Fin 2) (1 : Fin 2) = 1 := by
  unfold QMCLeafB.Finalization.wMatrixQ
  norm_num [G₁]

theorem wMatrixQ_G₁_10 :
    QMCLeafB.Finalization.wMatrixQ G₁ (1 : Fin 2) (0 : Fin 2) = 1 := by
  unfold QMCLeafB.Finalization.wMatrixQ
  norm_num [G₁]

/-- **The pinched objective floor**, general in the off-diagonal value `c ≥ 0`: at a matrix whose
diagonal is pinned to `1 - δ/4`, the `psd_margin` at `x = (1,1)` gives
`⟪A, Q⟫ = c (Q₀₁ + Q₁₀) ≥ -c (2 + δ/2)`.  Compare §1's `frob_ge_of_relaxMem`, which uses
`diag_near`'s *upper* bound and so applies to un-pinned matrices. -/
theorem frob_ge_of_pinched {u δ c : ℚ} {A Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hc : 0 ≤ c) (h00 : A 0 0 = 0) (h01 : A 0 1 = c) (h10 : A 1 0 = c) (h11 : A 1 1 = 0)
    (hdiag : ∀ i, Q i i = 1 - δ / 4)
    (hM : QMCLeafB.RelaxOracle.RelaxMem A Q u δ) :
    -c * (2 + δ / 2) ≤ QMCLeafB.SepOracle.frob A Q := by
  have hpsd := hM.psd_margin (fun _ : Fin 2 => (1 : ℚ))
  have hsq : (∑ i : Fin 2, ((1 : ℚ)) ^ 2) = 2 := by norm_num
  have hqf : QMCLeafB.SepOracle.qf Q (fun _ : Fin 2 => (1 : ℚ))
      = Q 0 0 + Q 0 1 + Q 1 0 + Q 1 1 := by
    rw [QMCLeafB.SepOracle.qf_eq_sum]
    simp [Fin.sum_univ_two]
    ring
  rw [hsq, hqf] at hpsd
  have hfrob : QMCLeafB.SepOracle.frob A Q = c * Q 0 1 + c * Q 1 0 := by
    simp [QMCLeafB.SepOracle.frob, Fin.sum_univ_two, h00, h01, h10, h11]
  have hd0 := hdiag 0
  have hd1 := hdiag 1
  rw [hfrob]
  nlinarith

#print axioms QMCLeafB.EmptyBodyM5.frob_ge_of_pinched

/-- The sliver, at the literal numbers (`δ = 1/380000`, `ε = 1/20000`). -/
theorem no_pinched_member_G₁_lit (Q : Matrix (Fin 2) (Fin 2) ℚ)
    (hdiag : ∀ i, Q i i = 1 - (1 : ℚ) / 380000 / 4) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
        (-(2 : ℚ) + 71 / 1520000 - 1 / 20000) (1 / 380000) := by
  intro hM
  have hge := frob_ge_of_pinched (c := 1) (δ := 1 / 380000) (u := _) (by norm_num)
    wMatrixQ_G₁_00 wMatrixQ_G₁_01 wMatrixQ_G₁_10 wMatrixQ_G₁_11 hdiag hM
  have hle := hM.trace_le
  nlinarith

#print axioms QMCLeafB.EmptyBodyM5.no_pinched_member_G₁_lit

/-- **No pinched matrix is a member at `(G₁, t₁)`** (campaign form). -/
theorem no_pinched_member_G₁ (Q : Matrix (Fin 2) (Fin 2) ℚ)
    (hdiag : ∀ i, Q i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq / 4) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
        (-(2 : ℚ) + 71 / 1520000 - QMCLeafB.RundataCert.eps G₁)
        (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq := by
  rw [eps_G₁, dq₁_eq]
  rw [dq₁_eq] at hdiag
  exact no_pinched_member_G₁_lit Q hdiag

#print axioms QMCLeafB.EmptyBodyM5.no_pinched_member_G₁

/-- The un-pinched witness of the sliver: unit diagonal, lower eigenvalue `-3·δ/8` (inside the
`δ/2` margin), objective exactly at the level. -/
abbrev Q₁ : Matrix (Fin 2) (Fin 2) ℚ := !![1, -(1 + 3 / 3040000); -(1 + 3 / 3040000), 1]

/-- **The body at `(G₁, t₁)` is NONEMPTY** (at the literal numbers). -/
theorem body_nonempty_G₁_lit :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q₁
      (-(2 : ℚ) + 71 / 1520000 - 1 / 20000) (1 / 380000) where
  δ_pos := by norm_num
  psd_margin := by
    intro x
    rw [QMCLeafB.SepOracle.qf_eq_sum]
    simp [Q₁, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0), sq_nonneg (x 1)]
  diag_near := by
    intro i
    fin_cases i <;> norm_num [Q₁]
  trace_le := by
    simp [QMCLeafB.SepOracle.frob, Fin.sum_univ_two, Q₁]
    norm_num

#print axioms QMCLeafB.EmptyBodyM5.body_nonempty_G₁_lit

/-- **The body at `(G₁, t₁)` is NONEMPTY** (campaign form). -/
theorem body_nonempty_G₁ :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q₁
      (-(2 : ℚ) + 71 / 1520000 - QMCLeafB.RundataCert.eps G₁)
      (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq := by
  rw [eps_G₁, dq₁_eq]
  exact body_nonempty_G₁_lit

#print axioms QMCLeafB.EmptyBodyM5.body_nonempty_G₁

/-- **`CoreDataF` is uninhabited whenever no *pinched* matrix is a member** — the sharp form of §3
(an empty body is the special case, but the sliver above it is covered too). -/
theorem not_coreDataF_of_pinchedEmpty {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (h : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ, (∀ i, Q i i = 1 - P.dq / 4) →
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) P.dq)
    (D : QMCLeafB.RecordsM2.CoreDataF o G t P hn) : False := by
  have hf : QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) (P.K * P.m)
      = false :=
    QMCLeafB.FlagsM5.flagOf_false_of_not_mem G t P (QMCLeafB.RecordsM2.cXst G.n D.X P.dq)
      (P.K * P.m) (h _ (fun i => QMCLeafB.RecordsM2.cXst_diag G.n D.X P.dq (P.K * P.m) i))
  exact absurd (D.hcutfin (P.K * P.m) hf) (lt_irrefl _)

#print axioms QMCLeafB.EmptyBodyM5.not_coreDataF_of_pinchedEmpty

/-- `t₁` is inside the interior bracket at `G₁`. -/
theorem t₁_mem_bracket :
    -QMCLeafB.EngineRuntime.Rq G₁ ≤ -(2 : ℚ) + 71 / 1520000 ∧
      ((-(2 : ℚ) + 71 / 1520000 : ℚ) : ℝ)
        < -(((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ) := by
  constructor
  · rw [Rq_G₁]; norm_num
  · rw [Rq_G₁]; norm_num

#print axioms QMCLeafB.EmptyBodyM5.t₁_mem_bracket

/-- **The shape `CoreDataF` is uninhabited at `(G₁, t₁)`, where the relaxed body is NONEMPTY.** -/
theorem coreDataF_G₁_empty (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (hn : 2 ≤ G₁.n) :
    ¬ Nonempty (QMCLeafB.RecordsM2.CoreDataF o G₁ (-(2 : ℚ) + 71 / 1520000)
      (QMCLeafB.UnionShallow.paramsKbc2 G₁) hn) :=
  fun ⟨D⟩ => not_coreDataF_of_pinchedEmpty (fun Q hdiag => no_pinched_member_G₁ Q hdiag) D

#print axioms QMCLeafB.EmptyBodyM5.coreDataF_G₁_empty

/-- **`ResidFinite` is refuted at a NONEMPTY body.** -/
theorem residFinite_empty_of_body_nonempty (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.RecordsM2.ResidFinite o QMCLeafB.UnionShallow.paramsKbc2) := by
  rintro ⟨H⟩
  exact coreDataF_G₁_empty o (le_refl 2)
    ⟨H G₁ (-(2 : ℚ) + 71 / 1520000) (le_refl 2) t₁_mem_bracket.1 t₁_mem_bracket.2⟩

#print axioms QMCLeafB.EmptyBodyM5.residFinite_empty_of_body_nonempty

/-- **`ResidFinite` is refuted by the strictly weaker "no pinched member" hypothesis** (no empty
body needed): `hcutfin` forces a *pinched* member beyond the horizon. -/
theorem not_residFinite_of_no_pinched_member {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (h : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ, (∀ i, Q i i = 1 - (Pfam G).dq / 4) →
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (Pfam G).dq) :
    (QMCLeafB.RecordsM2.ResidFinite o Pfam) → False :=
  fun H => not_coreDataF_of_pinchedEmpty (P := Pfam G) h (H G t hn hlo hhi)

#print axioms QMCLeafB.EmptyBodyM5.not_residFinite_of_no_pinched_member

/-! ## 11.  Axiom audit -/


#print axioms QMCLeafB.EmptyBodyM5.eps_G₀
#print axioms QMCLeafB.EmptyBodyM5.dq₀_eq
#print axioms QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_00
#print axioms QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_01
#print axioms QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_10
#print axioms QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_11
#print axioms QMCLeafB.EmptyBodyM5.the_gap
#print axioms QMCLeafB.EmptyBodyM5.coreDataF_G₀_empty_of_dq
#print axioms QMCLeafB.EmptyBodyM5.residFinite_empty_of_dq
#print axioms QMCLeafB.EmptyBodyM5.residFinite_empty'

end QMCLeafB.EmptyBodyM5


