-- Prove2me | Definitions.Def_QMCLeafB_okprodB
-- name    : QMCLeafB_okprodB
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T06:12:41.403058+00:00
-- url     : https://prove2.me/theorems/32d2d38b-8f46-4fe6-b4ee-d61c9dc77216
-- title:
--   QMCLeafB okprodB
-- statement:
--   # leaf B phase 21 — `ok-production` at the horizon-bounded residual (swarm `smw1m5nkm`, member m6, d4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_residb_m7
import Definitions.Def_QMCLeafB_okprod_m6
/-
# leaf B phase 21 — `ok-production` at the horizon-bounded residual (swarm `smw1m5nkm`, member m6, d4)

Companion to `Check_okprod_m6`.  d5 (`Check_residb_m7`) refuted-then-replaced phase 20's residual:
`ResidFiniteB` asks for a `CoreDataB` at every interior `(G, t)`, where `CoreDataB` is `CoreDataF`
with `hcutfin` deleted and the two drift slots already at `k < K·m`.  This file delivers

* §1 **the `ok` branch outright** — `coreDataB_of_allOk`: one admissible coded state plus
  `o G t = true` gives a `CoreDataB`, with **both drift slots vacuous** (the constant stream has every
  flag `true`, so no round below the horizon is a cut round);
* §2 **the `cut` branch's exact shape** — `flags_all_false_of_emptyBody` /
  `anyOk_false_of_emptyBody`: at an empty pinched body *every* stream has every flag `false`, so
  `hverdict` degenerates to `o G t = false` (`hverdict_iff_of_emptyBody`) and the two drift slots are
  read at **every** `k < K·m`;
* §3 **the interface for the assembler** — `residFiniteB_of_split`: `ResidFiniteB` from an
  `ok`-branch and a `cut`-branch producer.  Nothing else is needed at this level.

Together with `Check_okprod_m6` (§1 the horizon clause forces a member; §3 the `ok` branch is
discharged by the programme's own accepted round; §5 the verdict leg; §7/§9 the constructive cut
`cutOfC` replacing the opaque `FlagsM5.cutOf`), this pins the leaf's remaining obligation to the
two drift budgets at `false`-bit points, where §7 of `Check_okprod_m6` applies.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
`#print axioms` audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.OkProdB_M6

attribute [local instance] Classical.propDecidable

open QuantumMaxCutEnergy
open QMCLeafB.SepOracle (qf frob)
open QMCLeafB.FlagsM5 (flagOf)
open QMCLeafB.RecordsM2 (cXst)
open QMCLeafB.ResidB_M7 (CoreDataB ResidFiniteB)

/-! ## 1.  The `ok` branch: `CoreDataB` from one admissible coded state -/

/-- **`CoreDataB` from one admissible coded state and a `true` verdict bit.**  The constant stream
makes every canonical flag `true`, so both drift slots have no round below the horizon to speak
about and `hverdict` reads `anyOk` of the all-`ok` stream. -/
theorem coreDataB_of_allOk {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {hn : 2 ≤ G.n} (X₀ : List ℚ) (hKm : 0 < P.K * P.m)
    (hdq : 0 < P.dq) (hdq4 : P.dq ≤ 4)
    (hsym₀ : (QMCLeafB.StateDiag.stMat G.n X₀)ᵀ = QMCLeafB.StateDiag.stMat G.n X₀)
    (hunit : ∀ i, QMCLeafB.StateDiag.stMat G.n X₀ i i = 1)
    (hpsd : ∀ x : Fin G.n → ℚ, 0 ≤ qf (QMCLeafB.StateDiag.stMat G.n X₀) x)
    (htrace : frob (QMCLeafB.Finalization.wMatrixQ G) (QMCLeafB.StateDiag.stMat G.n X₀)
      ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2)
    (hverdict : o G t = true) :
    Nonempty (CoreDataB o G t P hn) := by
  have hflags : ∀ k, flagOf G t P (cXst G.n (fun _ => X₀) P.dq) k = true := fun k =>
    QMCLeafB.RecordsM2.flag_cXst_of_ok k hdq hdq4 hunit hpsd htrace
  have hfalse : ∀ k, flagOf G t P (cXst G.n (fun _ => X₀) P.dq) k = false → False := by
    intro k hk
    rw [hflags k] at hk
    exact absurd hk (by simp)
  refine ⟨{ X := fun _ => X₀
            hsym := fun _ => hsym₀
            hdriftc := fun k _ hk => (hfalse k hk).elim
            hdriftd := fun k _ hk => (hfalse k hk).elim
            hverdict := ?_ }⟩
  rw [hverdict]
  have hstream : (flagOf G t P (cXst G.n (fun _ => X₀) P.dq)) = (fun _ : ℕ => true) :=
    funext hflags
  rw [hstream]
  exact (QMCLeafB.OkProdM6.anyOk_const_true _ hKm).symm

#print axioms QMCLeafB.OkProdB_M6.coreDataB_of_allOk

/-! ## 2.  The `cut` branch: at an empty pinched body every flag is `false` -/

/-- **Every round is a cut round at an empty pinched body** — for *any* coded stream. -/
theorem flags_all_false_of_emptyBody {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (h : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (X : ℕ → List ℚ) (k : ℕ) :
    flagOf G t P (cXst G.n X P.dq) k = false :=
  QMCLeafB.FlagsM5.flagOf_false_of_not_mem G t P (cXst G.n X P.dq) k (h _)

#print axioms QMCLeafB.OkProdB_M6.flags_all_false_of_emptyBody

/-- `anyOk` of the all-`false` stream vanishes. -/
theorem anyOk_const_false : ∀ N : ℕ,
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => false) N = false
  | 0 => rfl
  | (k + 1) => by
      rw [QMCLeafB.SimLoop.anyOk_succ, anyOk_const_false k]
      rfl

#print axioms QMCLeafB.OkProdB_M6.anyOk_const_false

/-- **At an empty pinched body the verdict slot degenerates**: `CoreDataB`'s `hverdict` says exactly
`o G t = false`, for every coded stream. -/
theorem hverdict_iff_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (h : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (X : ℕ → List ℚ) :
    (o G t = QMCLeafB.SimLoop.anyOk
        (flagOf G t P (cXst G.n X P.dq)) (P.K * P.m)) ↔ o G t = false := by
  have hstream : (flagOf G t P (cXst G.n X P.dq)) = (fun _ : ℕ => false) :=
    funext (flags_all_false_of_emptyBody h X)
  rw [hstream, anyOk_const_false (P.K * P.m)]

#print axioms QMCLeafB.OkProdB_M6.hverdict_iff_of_emptyBody

/-! ## 3.  The interface for the assembler

`ResidFiniteB` is a `∀`-closure of a `Type`-valued residual, so the only structural fact the
assembler needs is the two-way case split on the leaf's own verdict bit.  §1 discharges the `true`
side, so what is left named is `cutBranch` alone. -/

/-- **`ResidFiniteB` from the two branches.** -/
def residFiniteB_of_split {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true → Nonempty (CoreDataB o G t (Pfam G) hn))
    (hcut : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = false → Nonempty (CoreDataB o G t (Pfam G) hn)) :
    ResidFiniteB o Pfam := by
  intro G t hn hlo hhi
  cases hv : o G t with
  | true => exact (hok G t hn hlo hhi hv).some
  | false => exact (hcut G t hn hlo hhi hv).some

#print axioms QMCLeafB.OkProdB_M6.residFiniteB_of_split

/-- **The `ok` branch of `ResidFiniteB` is closed** by `coreDataB_of_allOk`: the named `ok`-branch
obligation is only "at each interior point where the leaf's bit is `true`, one admissible coded
state exists". -/
theorem residFiniteB_okBranch {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hKm : ∀ (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n), 0 < (Pfam G).K * (Pfam G).m)
    (hdq : ∀ (G : QuantumMaxCutEnergy.Input), 0 < (Pfam G).dq)
    (hdq4 : ∀ (G : QuantumMaxCutEnergy.Input), (Pfam G).dq ≤ 4)
    (hmem : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = true →
      ∃ X₀ : List ℚ,
        (QMCLeafB.StateDiag.stMat G.n X₀)ᵀ = QMCLeafB.StateDiag.stMat G.n X₀ ∧
        (∀ i, QMCLeafB.StateDiag.stMat G.n X₀ i i = 1) ∧
        (∀ x : Fin G.n → ℚ, 0 ≤ qf (QMCLeafB.StateDiag.stMat G.n X₀) x) ∧
        frob (QMCLeafB.Finalization.wMatrixQ G) (QMCLeafB.StateDiag.stMat G.n X₀)
          ≤ (t - QMCLeafB.RundataCert.eps G) + (Pfam G).dq / 2) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true → Nonempty (CoreDataB o G t (Pfam G) hn) := by
  intro G t hn _ _ hv
  obtain ⟨X₀, hs, hu, hp, ht⟩ := hmem G t hv
  exact coreDataB_of_allOk X₀ (hKm G hn) (hdq G) (hdq4 G) hs hu hp ht hv

#print axioms QMCLeafB.OkProdB_M6.residFiniteB_okBranch

end QMCLeafB.OkProdB_M6


