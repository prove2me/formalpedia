-- Prove2me | Definitions.Def_QMCLeafB_asm40
-- name    : QMCLeafB_asm40
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:10:11.049542+00:00
-- url     : https://prove2.me/theorems/169e9d65-edb4-453d-adaf-2e543380c340
-- title:
--   QMCLeafB asm40
-- statement:
--   # `Check_asm40_m8` — phase 40, member m8, direction d7 (`assembly40`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_asm35
import Definitions.Def_QMCLeafB_pbit33
import Definitions.Def_QMCLeafB_by35
import Definitions.Def_QMCLeafB_thinrec34
/-
# `Check_asm40_m8` — phase 40, member m8, direction d7 (`assembly40`)

**What this file does.**  It fires the leaf end-to-end on the ONLY route that survives phase 40's
parameter check, and it states the exact remainder.

**Why not the closing move.**  The phase-40 charter proposed to enlarge the depth ceiling to
`rmax := 1/(n·n)` so that the standard step's attained ratio `(1-ρ)/(N+ρ)` fits under the leaf's
allowance.  The factor arithmetic is right (`Check_fa40_m8.reuse_ratio_le_inv_dim`,
`reuse_eq_iff`, `reuse_ratio_at_supporting`), but the ceiling is not admissible: `rho0R` DECREASES in
the depth, `rho0R N (1/N) < 1` for every `N ≥ 2`, so `RunParams.hhalve` forces `rmax < 1/N`
(`Check_fa40_m8.no_runParams_rmax_inv_dim` — the family is uninhabited) while the closing move needs
`rmax ≥ 1/N` (`closing_move_impossible`).  The two cannot hold together at any `n ≥ 2`.

**What survives, and is assembled here.**  The `del ≡ 0` route: a rational nonzero normal that puts
the engine's accumulated centre on the FAR SIDE of the whole relaxation (phase 35's
`Bypass35M6.shallowCut_of_separating`).  That certificate's depth check is `0 ≤ rmax²·σ`, which uses
only `P.hrmax` — the ceiling's *value* is irrelevant, so the admissibility obstruction does not reach
it.  So the leaf's last object is exactly phase 38's `SepStream`, unchanged.

The assembly:

* `shallowCut_of_sepStream` — `SepStream` gives `ShallowCut` at every round (reuse: by35);
* `shallowSlotG_of_sepStream` — the family form `Asm35M4.ShallowSlotG`;
* `solution_of_sepStream` — `FinishLine.SolutionStatement` from
  {`Automatic.Poly` bit} + {`1 ≤ K·m`} + {top slice} + {`hok`} + {`SepStream`}, at an ARBITRARY bit
  and family (so a re-pointed programme plugs in);
* `solution40` — the same at the campaign's own programme `Pbit33.o33`/`Pbit33.P33` with the `Poly`
  bit `Pbit33.ho33`, the count `Pbit33.hKm33` and the top slice `ConformanceM8.htop_roundGT`
  DISCHARGED, leaving exactly {`k`, `hk`, `hok`, `SepStream`};
* `solution40_statement` — the verbatim `d9f601e5` sentence.

Discipline: `set_option autoImplicit false`; imports are published `Definitions.*` only (so the gate
is the submission cone); `#print axioms` after every theorem, all exactly
[propext, Classical.choice, Quot.sound].
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Asm40M8

open Matrix
open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates
open QMCLeafB.ThinRec34M4 (ShallowCut NormalCut relaxBallP BodyRec)

/-! ## 1.  The supporting stream (phase 38's `SepStream`, verbatim)

At every round below the horizon the round's own rational normal puts the engine's accumulated
centre on the far side of the WHOLE relaxation.  `rmax`, `σ` and the ellipsoid are unused. -/

/-- A nonzero rational stream which, at every round below the horizon, places the accumulated centre
on the far side of the relaxation: a supporting-hyperplane certificate. -/
def SepStream (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    ∀ k, k < (P G).K * (P G).m → ∀ z ∈ relaxBallP G t (P G),
      (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G (P G) hn (c G t) (hc G t)) k
        ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

/-! ## 2.  The stream gives the shallow cut, the record, and the family slot -/

/-- **`ShallowCut` from a supporting stream** (reuse: phase 35, `del ≡ 0`). -/
theorem shallowCut_of_sepStream {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (hsep : ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (NormalCut G P hn c hc) k
        ≤ (fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ z) :
    ShallowCut G t P hn :=
  QMCLeafB.Bypass35M6.shallowCut_of_separating hn c hc hsep

#print axioms QMCLeafB.Asm40M8.shallowCut_of_sepStream

/-- **The family slot** `ShallowSlotG` from a separating stream — this is the exact interface
`Asm35M4.solution_of_two_slots_shallowCut` consumes. -/
theorem shallowSlotG_of_sepStream
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream P c hc) :
    Asm35M4.ShallowSlotG o P := by
  intro G t hn _hlo _hlt _hb
  exact shallowCut_of_sepStream (P := P G) (c := c G t) (hc := hc G t) (hsep G t hn)
    (hn := hn)

#print axioms QMCLeafB.Asm40M8.shallowSlotG_of_sepStream

/-! ## 2b.  The stream is only owed where the record is owed

`SepStream` as phase 38 stated it quantifies over EVERY interior point.  The record is only owed at
bit-`false` points (`SelfRecG`'s domain), and at a bit-`true` point the body is fat and no supporting
hyperplane through the moving centre need exist.  So the honest slot is the bit-`false`-restricted
one; it is what `ShallowSlotG` consumes, and it is strictly weaker. -/

/-- **The separating stream on the record's own domain** (bit-`false` interior points). -/
def SepStreamG (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = false →
    ∀ k, k < (P G).K * (P G).m → ∀ z ∈ relaxBallP G t (P G),
      (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G (P G) hn (c G t) (hc G t)) k
        ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

/-- The unrestricted stream implies the restricted one. -/
theorem sepStreamG_of_sepStream
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream P c hc) : SepStreamG o P c hc := by
  intro G t hn _hlo _hlt _hb
  exact hsep G t hn

#print axioms QMCLeafB.Asm40M8.sepStreamG_of_sepStream

/-- **The family slot from the restricted stream** — the exact interface
`Asm35M4.solution_of_two_slots_shallowCut` consumes. -/
theorem shallowSlotG_of_sepStreamG
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (H : SepStreamG o P c hc) :
    Asm35M4.ShallowSlotG o P := by
  intro G t hn hlo hlt hb
  exact shallowCut_of_sepStream (P := P G) (hn := hn) (c := c G t) (hc := hc G t)
    (H G t hn hlo hlt hb)

#print axioms QMCLeafB.Asm40M8.shallowSlotG_of_sepStreamG

/-- **`d9f601e5` from {`Automatic.Poly` bit} + {`1 ≤ K·m`} + {top slice} + {`hok`} +
{restricted separating stream}.**  This is the weakest form the assembly has: the geometric slot is
owed only on the record's own domain. -/
theorem solution_of_sepStreamG
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (H : SepStreamG o P c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  Asm35M4.solution_of_two_slots_shallowCut o P ho hKm htop hok
    (shallowSlotG_of_sepStreamG o P c hc H)

#print axioms QMCLeafB.Asm40M8.solution_of_sepStreamG

/-! ## 3.  THE LEAF, FROM SEPARATION, AT AN ARBITRARY PROGRAMME -/

/-- **`d9f601e5` from {`Automatic.Poly` bit} + {`1 ≤ K·m`} + {top slice} + {`hok`} + {`SepStream`}.**
Every hypothesis except the last is a fact about which programme runs; the last is the leaf's whole
analytic content, and it is INDEPENDENT of the depth ceiling. -/
theorem solution_of_sepStream
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream P c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  Asm35M4.solution_of_two_slots_shallowCut o P ho hKm htop hok
    (shallowSlotG_of_sepStream o P c hc hsep)

#print axioms QMCLeafB.Asm40M8.solution_of_sepStream

/-! ## 4.  THE ASSEMBLY AT THE CAMPAIGN'S OWN PROGRAMME

`o33`/`P33` are the programme and family the shelf runs (`rmax = rmaxOf (n·n) = 1/(4n²)` — the
ADMISSIBLE ceiling, see `Check_fa40_m8`).  The `Poly` bit (`Pbit33.ho33`), the count
(`Pbit33.hKm33`) and the top slice (`ConformanceM8.htop_roundGT`) are discharged theorems, so the
remainder is exactly {`k`, `hk`, `hok`, `SepStream`}. -/

/-- **THE LEAF AT `o33` FROM TWO SLOTS.**  The remaining hypotheses are the fuel exponent `k`, the
upper slot `hok` (bit true ⟹ symmetric rational `RelaxMem` at `(t − eps, dqShallow)`), and the
separating rational stream. -/
theorem solution40 (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream QMCLeafB.Pbit33.P33 c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_sepStream QMCLeafB.Pbit33.o33 QMCLeafB.Pbit33.P33
    (QMCLeafB.Pbit33.ho33 k hk)
    (fun G => Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (QMCLeafB.Pbit33.hKm33 G)))
    (fun G t hG hlo hhi =>
      QMCLeafB.ConformanceM8.htop_roundGT (fun G' => QMCLeafB.Pbit33.T33 G')
        (fun G' => QMCLeafB.Pbit33.one_le_T33 G') G t hlo hhi)
    hok c hc hsep

#print axioms QMCLeafB.Asm40M8.solution40

/-- **THE LEAF AT `o33`, in the platform's own type** (the verbatim `d9f601e5` sentence). -/
theorem solution40_statement (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream QMCLeafB.Pbit33.P33 c hc) :
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
  QMCLeafB.FinishLine.solutionStatement_iff_wMatrix.1 (solution40 k hk hok c hc hsep)

#print axioms QMCLeafB.Asm40M8.solution40_statement

/-- **THE ASSEMBLY AT `o33` WITH THE RESTRICTED SLOT** — the weakest exact remainder this file can
state: {`k`, `hk`, `hok`} plus the separating stream at bit-`false` interior points. -/
theorem solution40G (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (H : SepStreamG QMCLeafB.Pbit33.o33 QMCLeafB.Pbit33.P33 c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_sepStreamG QMCLeafB.Pbit33.o33 QMCLeafB.Pbit33.P33
    (QMCLeafB.Pbit33.ho33 k hk)
    (fun G => Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (QMCLeafB.Pbit33.hKm33 G)))
    (fun G t hG hlo hhi =>
      QMCLeafB.ConformanceM8.htop_roundGT (fun G' => QMCLeafB.Pbit33.T33 G')
        (fun G' => QMCLeafB.Pbit33.one_le_T33 G') G t hlo hhi)
    hok c hc H

#print axioms QMCLeafB.Asm40M8.solution40G

/-- **The verbatim `d9f601e5` sentence at `o33`** from the restricted slot. -/
theorem solution40G_statement (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (H : SepStreamG QMCLeafB.Pbit33.o33 QMCLeafB.Pbit33.P33 c hc) :
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
  QMCLeafB.FinishLine.solutionStatement_iff_wMatrix.1 (solution40G k hk hok c hc H)

#print axioms QMCLeafB.Asm40M8.solution40G_statement

/-! ## 5.  The ceiling is not part of the obligation

The depth check at `del ≡ 0` is `0 ≤ rmax²·σ`: it consumes `P.hrmax ≥ 0` and nothing else.  So the
separating route is unaffected by `Check_fa40_m8`'s obstruction — which is why the assembly above is
stated at `P33` (ceiling `1/(4n²)`) without loss. -/

/-- The separating certificate's depth check is satisfied at EVERY nonnegative ceiling. -/
theorem del_zero_check_any_ceiling {σ rmax : ℚ} (hσ : 0 ≤ σ) (hr : 0 ≤ rmax) :
    (0 : ℚ) ^ 2 ≤ rmax ^ 2 * σ := by
  have : (0 : ℚ) ≤ rmax ^ 2 * σ := by positivity
  simpa using this

#print axioms QMCLeafB.Asm40M8.del_zero_check_any_ceiling

end QMCLeafB.Asm40M8


