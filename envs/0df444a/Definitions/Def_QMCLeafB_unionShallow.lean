-- Prove2me | Definitions.Def_QMCLeafB_unionShallow
-- name    : QMCLeafB_unionShallow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:03:06.766205+00:00
-- url     : https://prove2.me/theorems/be4dc39b-35d6-43e8-9ec9-6718f09def9a
-- title:
--   QMCLeafB unionShallow
-- statement:
--   # leaf B phase 16 — brick 5 `union-shallow` (swarm `smw1ez4a9`, member m5, direction d8)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_topSlice
import Definitions.Def_QMCLeafB_runparams_shallow_m5
import Definitions.Def_QMCLeafB_halve_perG_m2
import Definitions.Def_QMCLeafB_integration_m6
import Definitions.Def_QMCLeafB_runparts_dilate_m5
import Definitions.Def_QMCLeafB_budget_bound_m1
import Definitions.Def_QMCLeafB_fuelwire_m4
/-
# leaf B phase 16 — brick 5 `union-shallow` (swarm `smw1ez4a9`, member m5, direction d8)

`QMCLeafB.FinishLine.SolutionStatement` is the trusted `solution_union` form minus three items
(m3's one-step size ledger, m7's `htop` at `2 ≤ G.n`, m4's `RunParts` on the interior bracket).
This file owns **only the deductions** that turn those three into `SolutionStatement`, at the
parameter family the campaign actually runs at.

Why the shelf's strokes cannot be applied as they stand:

* `Conformance.solution_union`, `IntegrateM6.solution_of_bricks` and
  `FuelWire.solution_of_runParts_interior_monoF` ask `htop` on the **whole** bracket including
  `G.n ≤ 1`.  m4's `TopSliceRange.htop_interior_false` shows that is *false* for the concrete
  `RoundProgram` loop, so the `hn` restriction (m4's `soundEpsOnBracket_of_runData_interior_hn`) is
  mandatory.  §1 supplies the missing `hn`-restricted stroke.
* they are stated at `paramsHalve` (`dq = 1`), and `dq = 1` is uninstantiable on the interior
  (`RunParams.hcert`'s rounding budget: `roundCost = 3.61·Rq > 2·eps`).  The coherent family is
  `dq = dqShallow G = (Rq G/40000)/(9·Rq G+1)`, `m = mHalve (n·n)`, `rmax = rmaxOf (n·n)`, with a
  monomial round factor above `budgetRounds` (§2).

Contents:

* §1 `solution_of_runParts_interior_of_params_hn` — the generic stroke: any total parameter family
  `P`, `htop` only at `2 ≤ G.n`, `RunParts` at `P`, fuel `fuelOfProd` at the count `(P G).K·(P G).m`;
* §2 the campaign's family `paramsShallowKf` at `dqShallow` (`m = mHalve (n·n)`,
  `rmax = rmaxOf (n·n)`, `cAq = Rq`), with the round factor left free, plus its field equations;
* §3 `solution_union_shallow_gen` (caller-chosen round factor) and `solution_union_shallow` (m4's
  `Kbc` factor), both consuming the size ledger through `IntegrateM6.orbit_envelope`;
* §4 **`budgetRounds` is monotone in the tolerance**: for `0 < dq ≤ 1` and `1/dq ≤ 2^B`,
  `budgetRounds G dq m ≤ budgetRounds G 1 m + m·B·n²` (all the shelf's estimates are at `dq = 1`);
* §5 the campaign tolerance in bit form: `1/dqShallow = 360000 + 40000/Rq ≤ 2^(bitCost (Rq)+20)`,
  and `dqShallow ≤ 1`;
* §6 the count at the campaign tolerance: `budgetRounds G (dqShallow G) (mHalve (n·n)) ≤ Kbc2 … G`
  with **no hypotheses**, plus the `Poly` and seed facts of `Kbc2`'s fuel length;
* §7 `solution_union_shallow_final` — `SolutionStatement` with **no numeric hypothesis**: the
  residual is exactly the three items (ledger, `htop`, `hd`) plus the init program;
* §8 the interface facts brick 4 needs for `RunPartsDilate.runParts_of_dilated` at the family, and
  the `Rq G = 0` vacuity of the interior bracket (where the rounding budget is *unprovable*, so that
  case must be split off rather than run through the dilation).

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audits at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.UnionShallow

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

local instance instRequestCodingUnion : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The generic stroke, with `htop` only at `2 ≤ G.n` -/

/-- **`SolutionStatement` from the interior run brick at a total parameter family `P`**, asking the
top-slice verdict only where it is true (`2 ≤ G.n`).  Same body as
`FuelWire.solution_of_runParts_interior_of_params`, with
`VerdictSound.soundEpsOnBracket_of_runData_interior` replaced by its `hn`-restricted form
(`TopSliceRange.soundEpsOnBracket_of_runData_interior_hn`).  The fuel is `fuelOfProd` at the count
`(P G).K · (P G).m`, which is exactly the count `RunParts.hverdict` compares the verdict bit against. -/
theorem solution_of_runParts_interior_of_params_hn {σ : Type} [Coding σ]
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (k : ℕ)
    (hKf : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg => (P p.1.1).K * (P p.1.1).m))
    (hseed : ∀ p : QMCLeafB.FuelWire.Pkg,
      (P p.1.1).K * (P p.1.1).m ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k))
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => (P G').K * (P G').m) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => (P G').K * (P G').m)) G t (P G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.LoopRestate.solution_of_loop_bounded init
    (QMCLeafB.FuelWire.fuelOfProd k (fun G => (P G).K) (fun G => (P G).m))
    round verdict hinit (QMCLeafB.FuelWire.poly_fuelOfProd k _ _ hKf) hr hv sizes horbit
    (QMCLeafB.FinalStroke.loopBit init round verdict
      (fun G' _ => (P G').K * (P G').m))
    (fun p => QMCLeafB.FinalStroke.hspec_of_tape_free init _ round verdict
      (fun G' _ => (P G').K * (P G').m) hinitTape
      (fun q => QMCLeafB.FuelWire.fuelOfProd_length k _ _ hseed q) p)
    (QMCLeafB.TopSliceRange.soundEpsOnBracket_of_runData_interior_hn
      (QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => (P G').K * (P G').m)) htop
      (fun G t hn hlo hlt => (hd G t hn hlo hlt).toRunData))

/-! ## 2.  The campaign's parameter family: `dqShallow`, `m = mHalve (n·n)` -/

/-- **The campaign's `RunParams` family at a caller-chosen round factor.**  The tolerance is
`dqShallow G` — the only one at which `hcert`'s rounding budget closes (`dq = 1` dies at
`roundCost = 3.61·Rq > 2·eps`) — the ceiling is `rmaxOf (n·n)` (positive, so cut rounds have a
margin), the halving time is `mHalve (n·n)`, and `K` is the caller's count, which only has to
dominate `budgetRounds G (dqShallow G) (mHalve (n·n))` (brick 1's round-count side condition). -/
noncomputable def paramsShallowKf (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G) :
    (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G :=
  fun G => QMCLeafB.HalvePerG.paramsK G (QMCLeafB.RundataParams.dqShallow G)
    (QMCLeafB.RundataParams.dqShallow_pos G) (Kf G) (hK G)

/-- The monomial round factor of the campaign, at m2's halving time. -/
def KbcShallow (G : QuantumMaxCutEnergy.Input) : ℕ :=
  QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G

/-- Brick 1's round-count side condition at the campaign factor: after
`budgetRounds_le_monomial` with `B = n + 2·bitCost (Rq G) + c`, this is the `1/dq ≤ 2^(2·bitCost+c)`
inequality turned into a count. -/
abbrev ShallowKbound : Prop :=
  ∀ G : QuantumMaxCutEnergy.Input,
    QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
      (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ KbcShallow G

/-- **The campaign's family at the concrete `Kbc` round factor.** -/
noncomputable def paramsShallowK (hKdqs : ShallowKbound) :
    (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G :=
  paramsShallowKf KbcShallow hKdqs

@[simp] theorem paramsShallowKf_K (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (G : QuantumMaxCutEnergy.Input) : (paramsShallowKf Kf hK G).K = Kf G := rfl

@[simp] theorem paramsShallowKf_m (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (G : QuantumMaxCutEnergy.Input) : (paramsShallowKf Kf hK G).m
      = QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

@[simp] theorem paramsShallowKf_dq (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (G : QuantumMaxCutEnergy.Input) : (paramsShallowKf Kf hK G).dq
      = QMCLeafB.RundataParams.dqShallow G := rfl

@[simp] theorem paramsShallowKf_rmax (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (G : QuantumMaxCutEnergy.Input) : (paramsShallowKf Kf hK G).rmax
      = QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) := rfl

/-- The run count of `RunParts` at the family, in closed form — the count the fuel must match. -/
theorem paramsShallowKf_K_mul_m (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (G : QuantumMaxCutEnergy.Input) :
    (paramsShallowKf Kf hK G).K * (paramsShallowKf Kf hK G).m
      = Kf G * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

/-! ## 3.  The union at the campaign family -/

/-- **The glue, at a caller-chosen round factor.**  `SolutionStatement` from the three items:

* the one-step size ledger `(hMinv, hstep, hM)` at the guarded round (brick 2), consumed through
  `IntegrateM6.orbit_envelope` at `sizesOrbitPow (C₀+c+2) kr`;
* `htop` at `2 ≤ G.n` (brick 3);
* `hd`: one `RunParts` per interior `(G, t)` at `paramsShallowKf Kf hK` (brick 4).

Brick 1 enters as `hinit`/`hinitTape` (the init program packed at `2n² + 2·dqShallow²`) and as
`hK`/`hKf`/`hseed` (the round-count side condition at the same tolerance and its fuel arithmetic). -/
theorem solution_union_shallow_gen {σ : Type} [Coding σ]
    (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (k : ℕ)
    (hKf : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)))
    (hseed : ∀ p : QMCLeafB.FuelWire.Pkg,
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
        ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k))
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (M : σ → ℕ) (C₀ c kr : ℕ) (hkr : 1 ≤ kr)
    (hMinv : ∀ s, M (round s) ≤ M s + c)
    (hstep : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => Kf G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (paramsShallowKf Kf hK G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_runParts_interior_of_params_hn (paramsShallowKf Kf hK) k hKf hseed
    init round verdict hinit hr hv
    (QMCLeafB.FinalStroke.sizesOrbitPow (C₀ + c + 2) kr)
    (QMCLeafB.IntegrateM6.orbit_envelope round M C₀ c kr hkr hMinv hstep hM)
    hinitTape htop hd

/-- **The glue at the campaign's concrete `Kbc` round factor.**  Its fuel facts are discharged by
m4's `poly_Kbc_mHalve_mul` and `Kbc_mHalve_le_seed`, so the only count input left is brick 1's
`hKdqs : budgetRounds G (dqShallow G) (mHalve (n·n)) ≤ Kbc (mHalve (n·n))`. -/
theorem solution_union_shallow {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (hKdqs : ShallowKbound)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (M : σ → ℕ) (C₀ c kr : ℕ) (hkr : 1 ≤ kr)
    (hMinv : ∀ s, M (round s) ≤ M s + c)
    (hstep : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => KbcShallow G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => KbcShallow G' * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (paramsShallowK hKdqs G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_union_shallow_gen (fun G => KbcShallow G) k
    (QMCLeafB.FuelWire.poly_Kbc_mHalve_mul)
    (QMCLeafB.FuelWire.Kbc_mHalve_le_seed k hk)
    hKdqs init round verdict hinit hr hv M C₀ c kr hkr hMinv hstep hM hinitTape htop hd


/-- At positive total weight the campaign tolerance is the core formula. -/
theorem dqShallow_eq_core (G : QuantumMaxCutEnergy.Input)
    (hRq : QMCLeafB.EngineRuntime.Rq G ≠ 0) :
    QMCLeafB.RundataParams.dqShallow G = QMCLeafB.RundataParams.dqShallowCore G := by
  unfold QMCLeafB.RundataParams.dqShallow
  rw [if_neg hRq]

/-- `hKdqs` splits: at `Rq G = 0` the tolerance is `1` and the estimate is m1/m4's `dq = 1` bound;
only `Rq G ≠ 0` is new work. -/
theorem shallowKbound_of_dq_one (G : QuantumMaxCutEnergy.Input)
    (hRq : QMCLeafB.EngineRuntime.Rq G = 0) :
    QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
      (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ KbcShallow G := by
  unfold QMCLeafB.RundataParams.dqShallow
  rw [if_pos hRq]
  exact QMCLeafB.FuelWire.budgetRounds_le_Kbc _ G

/-! ## 4.  Killing the count hypothesis: `budgetRounds` is monotone in the tolerance

`RunParams.hbudget`/the fuel need a round factor above `budgetRounds G dqShallow (mHalve (n·n))`.
The shelf's estimates (`BudgetBound.budgetRounds_le_log`, `RoundCountEstimate.budgetRounds_le_bitCost`)
are all stated at `dq = 1`.  Rather than redo the `Nat.clog` argument at a symbolic `dq`, compare the
two radii directly: at `dq ≤ 1` with `1/dq ≤ 2^B`, each round costs at most `B·n²` extra bits, so

  `budgetRounds G dq m ≤ budgetRounds G 1 m + m·B·n²`.

That is the whole difference, and it is all the campaign tolerance needs. -/

/-- The argument of the outer `Nat.clog` in `budgetRounds`, at a given tolerance. -/
noncomputable def roundArg (G : QuantumMaxCutEnergy.Input) (dq : ℚ) : ℝ :=
  2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2))
    / ((dq : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n)

theorem budgetRounds_eq (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G dq m
      = Nat.clog 2 ⌈roundArg G dq⌉₊ * m := rfl

/-- **`roundArg` is multiplicative in the base.** -/
theorem roundArg_eq_pow (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : dq ≠ 0) :
    roundArg G dq
      = 2 * (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))
          * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)) / (dq : ℝ)) ^ (G.n * G.n) := by
  have hM : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 := by
    have h1 : (0 : ℚ) ≤ (G.n : ℚ) ^ 2 := sq_nonneg _
    have h2 : (0 : ℚ) < dq ^ 2 := by
      rcases lt_or_gt_of_ne hdq.symm with h | h
      · nlinarith
      · nlinarith
    nlinarith
  have hr : ((dq : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ≠ 0 := by
    have h1 : (dq : ℝ) ≠ 0 := by exact_mod_cast hdq
    have h2 : (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)) ≠ 0 := by
      have := QMCLeafB.EngineRuntime.Rq_nonneg G
      have : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by exact_mod_cast this
      intro h; linarith
    exact div_ne_zero h1 h2
  unfold roundArg
  rw [QMCLeafB.Boundary.volPot_initShapeOf _ hM]
  have hx : Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))
      / ((dq : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)))
      = Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))
        * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)) / (dq : ℝ) := by
    field_simp
  calc 2 * Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)) ^ (G.n * G.n)
        / ((dq : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n)
      = 2 * (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))
          / ((dq : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)))) ^ (G.n * G.n) := by
        rw [div_pow]
        ring
    _ = 2 * (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))
          * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)) / (dq : ℝ)) ^ (G.n * G.n) := by
        rw [hx]

/-- **The tolerance comparison.**  At `dq ≤ 1` and `1/dq ≤ 2^B`, the round budget's argument grows
by at most `2^(B·n²)` over the `dq = 1` one. -/
theorem roundArg_le (G : QuantumMaxCutEnergy.Input) {dq : ℚ} {B : ℕ}
    (hdq : 0 < dq) (hdq1 : dq ≤ 1) (hB : 1 / dq ≤ (2 : ℚ) ^ B) :
    roundArg G dq ≤ roundArg G 1 * (2 : ℝ) ^ (B * (G.n * G.n)) := by
  have hdq0 : dq ≠ 0 := hdq.ne'
  have hRq : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
    have h := QMCLeafB.EngineRuntime.Rq_nonneg G
    exact_mod_cast h
  set c := 8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  set g := Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 : ℚ) : ℝ)) * c with hg
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  have hsM : Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))
      ≤ Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 : ℚ) : ℝ)) := by
    apply Real.sqrt_le_sqrt
    have h : dq ^ 2 ≤ 1 := by nlinarith
    have h' : (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) ≤ 2 * (G.n : ℚ) ^ 2 + 2 := by linarith
    calc ((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ) ≤ ((2 * (G.n : ℚ) ^ 2 + 2 : ℚ) : ℝ) := by
          exact_mod_cast h'
      _ = _ := rfl
  have hB' : ((1 / dq : ℚ) : ℝ) ≤ (2 : ℝ) ^ B := by exact_mod_cast hB
  have hinv : ((1 / dq : ℚ) : ℝ) = 1 / (dq : ℝ) := by push_cast; ring
  rw [hinv] at hB'
  have hdqpos : (0 : ℝ) < (dq : ℝ) := by exact_mod_cast hdq
  -- the two closed forms
  rw [roundArg_eq_pow G hdq0, roundArg_eq_pow G (one_ne_zero)]
  -- `√M_dq·c/dq ≤ g·2^B`
  have hstep : Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)) * c / (dq : ℝ)
      ≤ g * (2 : ℝ) ^ B := by
    have h1 : Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)) * c / (dq : ℝ)
        = (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)) * c) * (1 / (dq : ℝ)) := by
      ring
    rw [h1]
    have hs : Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)) * c
        ≤ g := by
      rw [hg]
      exact mul_le_mul_of_nonneg_right hsM hc0
    have hs0 : (0 : ℝ) ≤ Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)) * c := by positivity
    calc Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)) * c * (1 / (dq : ℝ))
        ≤ g * (1 / (dq : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hs (by positivity)
      _ ≤ g * (2 : ℝ) ^ B := by
          exact mul_le_mul_of_nonneg_left hB' hg0
  -- raise to the `n²`-th power
  have hpow : (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)) * c / (dq : ℝ))
        ^ (G.n * G.n) ≤ (g * (2 : ℝ) ^ B) ^ (G.n * G.n) := by
    exact pow_le_pow_left₀ (by positivity) hstep _
  have hR : 2 * (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)) * c / (dq : ℝ))
        ^ (G.n * G.n)
      ≤ 2 * g ^ (G.n * G.n) * (2 : ℝ) ^ (B * (G.n * G.n)) := by
    have hexp : (g * (2 : ℝ) ^ B) ^ (G.n * G.n)
        = g ^ (G.n * G.n) * (2 : ℝ) ^ (B * (G.n * G.n)) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm B (G.n * G.n)]
    calc 2 * (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)) * c / (dq : ℝ))
          ^ (G.n * G.n)
        ≤ 2 * (g * (2 : ℝ) ^ B) ^ (G.n * G.n) := by linarith
      _ = 2 * g ^ (G.n * G.n) * (2 : ℝ) ^ (B * (G.n * G.n)) := by rw [hexp]; ring
  calc 2 * (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ)) * c / (dq : ℝ))
        ^ (G.n * G.n)
      ≤ 2 * g ^ (G.n * G.n) * (2 : ℝ) ^ (B * (G.n * G.n)) := hR
    _ = 2 * (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * 1 ^ 2 : ℚ) : ℝ)) * c / ((1 : ℚ) : ℝ))
          ^ (G.n * G.n) * (2 : ℝ) ^ (B * (G.n * G.n)) := by
        rw [hg]; norm_num

/-- **`budgetRounds` at a smaller tolerance.**  The one comparison the campaign tolerance needs:
`dq ≤ 1` and `1/dq ≤ 2^B` cost at most `B·n²` bits per round. -/
theorem budgetRounds_le_one_add (G : QuantumMaxCutEnergy.Input) (m : ℕ) {dq : ℚ} {B : ℕ}
    (hdq : 0 < dq) (hdq1 : dq ≤ 1) (hB : 1 / dq ≤ (2 : ℚ) ^ B) :
    QMCLeafB.FinalStroke.budgetRounds G dq m
      ≤ QMCLeafB.FinalStroke.budgetRounds G 1 m + m * (B * (G.n * G.n)) := by
  have harg := roundArg_le G hdq hdq1 hB
  have hceil : ⌈roundArg G dq⌉₊ ≤ ⌈roundArg G 1⌉₊ * 2 ^ (B * (G.n * G.n)) := by
    rw [Nat.ceil_le]
    refine harg.trans ?_
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (B * (G.n * G.n)) := by positivity
    have h3 : roundArg G 1 ≤ ((⌈roundArg G 1⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    push_cast
    exact mul_le_mul_of_nonneg_right h3 h2
  have hposR : (0 : ℝ) < roundArg G 1 := by
    unfold roundArg
    have hM : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 := by positivity
    rw [QMCLeafB.Boundary.volPot_initShapeOf _ hM]
    have hsq : (0 : ℝ) < Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 : ℚ) : ℝ)) := by
      apply Real.sqrt_pos.mpr
      have h : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 := by positivity
      exact_mod_cast h
    have hR : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
      have h := QMCLeafB.EngineRuntime.Rq_nonneg G
      exact_mod_cast h
    have hden : (0 : ℝ) < (((1 : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) := by
      positivity
    positivity
  have hpos : 1 ≤ ⌈roundArg G 1⌉₊ := by
    have h1 : (0 : ℝ) < ((⌈roundArg G 1⌉₊ : ℕ) : ℝ) := lt_of_lt_of_le hposR (Nat.le_ceil _)
    exact_mod_cast h1
  have h2N : 1 ≤ (2 : ℕ) ^ (B * (G.n * G.n)) := Nat.one_le_two_pow
  have hclog := QMCLeafB.BudgetBound.clog_two_mul_le (x := ⌈roundArg G 1⌉₊)
    (y := 2 ^ (B * (G.n * G.n))) hpos h2N
  have hclog2 : Nat.clog 2 (2 ^ (B * (G.n * G.n))) = B * (G.n * G.n) :=
    Nat.clog_pow 2 (B * (G.n * G.n)) (by norm_num)
  rw [hclog2] at hclog
  have hfinal : Nat.clog 2 ⌈roundArg G dq⌉₊
      ≤ Nat.clog 2 ⌈roundArg G 1⌉₊ + B * (G.n * G.n) :=
    (Nat.clog_mono_right 2 hceil).trans hclog
  rw [budgetRounds_eq, budgetRounds_eq]
  calc Nat.clog 2 ⌈roundArg G dq⌉₊ * m
      ≤ (Nat.clog 2 ⌈roundArg G 1⌉₊ + B * (G.n * G.n)) * m := Nat.mul_le_mul_right m hfinal
    _ = Nat.clog 2 ⌈roundArg G 1⌉₊ * m + m * (B * (G.n * G.n)) := by ring


/-! ## 5.  The campaign tolerance in bit form -/

/-- `1 / Rq G` is under a power of two: the denominator of the total weight is part of `bitCost`. -/
theorem inv_Rq_le_two_pow_bitCost (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    1 / QMCLeafB.EngineRuntime.Rq G
      ≤ (2 : ℚ) ^ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) := by
  set q := QMCLeafB.EngineRuntime.Rq G with hq
  have hnumpos : 0 < q.num := Rat.num_pos.mpr hRq
  have hnum1 : (1 : ℤ) ≤ q.num := hnumpos
  have hden : 0 < q.den := q.den_pos
  have hnum0 : (q.num : ℚ) ≠ 0 := by
    have : (q.num : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hden0 : (q.den : ℚ) ≠ 0 := by
    have h : (0 : ℤ) < (q.den : ℤ) := by exact_mod_cast hden
    have h' : (q.den : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt h)
    exact h'
  have hqeq : q = (q.num : ℚ) / (q.den : ℚ) := by
    rw [Rat.num_div_den]
  have hkey : 1 / q = (q.den : ℚ) * (q.num : ℚ)⁻¹ := by
    nth_rewrite 1 [hqeq]
    rw [one_div, inv_div, div_eq_mul_inv]
  have hnumR : (1 : ℚ) ≤ (q.num : ℚ) := by exact_mod_cast hnum1
  have hdenR : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast hden
  have hsz : (q.den : ℚ) ≤ (2 : ℚ) ^ QMCLeafB.Hspec.bitCost q := by
    have h1 : q.den < 2 ^ Nat.size q.den := Nat.lt_size_self q.den
    have h2 : Nat.size q.den ≤ QMCLeafB.Hspec.bitCost q := by
      unfold QMCLeafB.Hspec.bitCost; omega
    calc (q.den : ℚ) ≤ ((2 ^ Nat.size q.den : ℕ) : ℚ) := by
          exact_mod_cast le_of_lt h1
      _ = (2 : ℚ) ^ Nat.size q.den := by push_cast; ring
      _ ≤ (2 : ℚ) ^ QMCLeafB.Hspec.bitCost q := pow_le_pow_right₀ (by norm_num) h2
  rw [hkey]
  have hinv1 : (q.num : ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hnumR
  calc (q.den : ℚ) * (q.num : ℚ)⁻¹ ≤ (q.den : ℚ) * 1 :=
        mul_le_mul_of_nonneg_left hinv1 hdenR.le
    _ = (q.den : ℚ) := by ring
    _ ≤ _ := hsz

/-- **`dqShallow ≤ 1`** — the tolerance is a fraction of the total weight. -/
theorem dqShallow_le_one (G : QuantumMaxCutEnergy.Input)
    (hRq : QMCLeafB.EngineRuntime.Rq G ≠ 0) :
    QMCLeafB.RundataParams.dqShallow G ≤ 1 := by
  have hpos : 0 < QMCLeafB.EngineRuntime.Rq G := lt_of_le_of_ne
    (QMCLeafB.EngineRuntime.Rq_nonneg G) (Ne.symm hRq)
  rw [dqShallow_eq_core G hRq]
  unfold QMCLeafB.RundataParams.dqShallowCore QMCLeafB.RundataCert.eps
  rw [div_le_iff₀ (by positivity : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1)]
  nlinarith [hpos]

/-- **The campaign tolerance in bit form**: `1/dqShallow ≤ 2^(bitCost (Rq) + 20)`.
`1/dqShallow = 360000 + 40000/Rq`, and the denominator of the total weight costs `bitCost` bits. -/
theorem inv_dqShallow_le (G : QuantumMaxCutEnergy.Input)
    (hRq : QMCLeafB.EngineRuntime.Rq G ≠ 0) :
    1 / QMCLeafB.RundataParams.dqShallow G
      ≤ (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 20) := by
  have hpos : 0 < QMCLeafB.EngineRuntime.Rq G := lt_of_le_of_ne
    (QMCLeafB.EngineRuntime.Rq_nonneg G) (Ne.symm hRq)
  set S := QMCLeafB.EngineRuntime.Rq G with hS
  set bc := QMCLeafB.Hspec.bitCost S with hbc
  have hinv : 1 / QMCLeafB.RundataParams.dqShallow G = 360000 + 40000 / S := by
    rw [dqShallow_eq_core G hRq]
    unfold QMCLeafB.RundataParams.dqShallowCore QMCLeafB.RundataCert.eps
    rw [← hS]
    field_simp
    ring
  have hbc0 : 0 ≤ bc := Nat.zero_le _
  rw [hinv, hbc]
  have h1 : (360000 : ℚ) ≤ (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost S + 19) := by
    have h19 : (360000 : ℚ) ≤ 2 ^ 19 := by norm_num
    calc (360000 : ℚ) ≤ 2 ^ 19 := h19
      _ ≤ 2 ^ (QMCLeafB.Hspec.bitCost S + 19) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (40000 : ℚ) / S ≤ (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost S + 16) := by
    have h := inv_Rq_le_two_pow_bitCost G hpos
    rw [← hS, ← hbc] at h
    have h4 : (40000 : ℚ) = 2 ^ 16 * 40000 / 65536 := by norm_num
    have hle : (40000 : ℚ) / S = (40000) * (1 / S) := by ring
    rw [hle]
    have h40 : (40000 : ℚ) ≤ 2 ^ 16 := by norm_num
    calc (40000 : ℚ) * (1 / S) ≤ (2 : ℚ) ^ 16 * (2 : ℚ) ^ QMCLeafB.Hspec.bitCost S :=
          mul_le_mul h40 h (by positivity) (by positivity)
      _ = (2 : ℚ) ^ (16 + QMCLeafB.Hspec.bitCost S) := (pow_add _ _ _).symm
      _ = (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost S + 16) := by rw [Nat.add_comm]
  have hab : 360000 + 40000 / S ≤ (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost S + 19)
      + (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost S + 16) := add_le_add h1 h2
  have hsum : (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost S + 19) + (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost S + 16)
      ≤ (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost S + 20) := by
    have h16 : (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost S + 16) ≤ (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost S + 19) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hd : (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost S + 20)
        = 2 * (2 : ℚ) ^ (QMCLeafB.Hspec.bitCost S + 19) := by
      rw [show QMCLeafB.Hspec.bitCost S + 20 = (QMCLeafB.Hspec.bitCost S + 19) + 1 by omega,
        pow_succ]
      ring
    rw [hd]
    linarith
  exact hab.trans hsum


/-! ## 6.  The round count at `dqShallow`, and its fuel arithmetic -/

/-- **The campaign round factor**: `mHalve (n·n) · (n+1)² · (2·bitCost (Rq) + n + 29)`.  The extra
`bitCost` over m4's `Kbc` is exactly the cost of running at `dqShallow` instead of `dq = 1`
(§5), and the `+19` absorbs `1/dqShallow = 360000 + 40000/Rq` (§6). -/
def Kbc2 (m : ℕ) (G : QuantumMaxCutEnergy.Input) : ℕ :=
  m * ((G.n + 1) ^ 2
    * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1
        + (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1) + (G.n + 27)))

/-- The `Kbc` factor is below the `Kbc2` factor. -/
theorem Kbc_le_Kbc2 (m : ℕ) (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.FuelWire.Kbc m G ≤ Kbc2 m G := by
  rw [QMCLeafB.FuelWire.Kbc_eq]
  unfold Kbc2
  refine Nat.mul_le_mul_left m (Nat.mul_le_mul_left _ ?_)
  omega

/-- **The round-count estimate at the campaign tolerance.**  `budgetRounds` at `dqShallow` is under
the monomial `Kbc2`: `dq = 1`'s estimate (`BudgetBound.budgetRounds_le_log`) plus the `B·n²` cost of
§5 at `B = bitCost + 20` (§6). -/
theorem budgetRounds_dqShallow_le_Kbc2 (G : QuantumMaxCutEnergy.Input) (m : ℕ)
    (hRq : QMCLeafB.EngineRuntime.Rq G ≠ 0) :
    QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G) m
      ≤ Kbc2 m G := by
  have hstep := budgetRounds_le_one_add G m
    (dq := QMCLeafB.RundataParams.dqShallow G)
    (B := QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 20)
    (QMCLeafB.RundataParams.dqShallow_pos G) (dqShallow_le_one G hRq) (inv_dqShallow_le G hRq)
  have hone := QMCLeafB.BudgetBound.budgetRounds_le_log G m
  have hclog := QMCLeafB.RoundCountEstimate.clog_ceil_Rq_le G
  set bc := QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) with hbc
  -- replace the `clog` by `bitCost + 1` in the `dq = 1` estimate
  have hone' : QMCLeafB.FinalStroke.budgetRounds G 1 m
      ≤ m * ((G.n * G.n + 1) * (bc + 1 + G.n + 8)) := by
    refine hone.trans ?_
    refine Nat.mul_le_mul_left m (Nat.mul_le_mul_left _ ?_)
    omega
  refine hstep.trans ?_
  have hcomb : QMCLeafB.FinalStroke.budgetRounds G 1 m
        + m * ((bc + 20) * (G.n * G.n))
      ≤ m * ((G.n * G.n + 1) * (bc + 1 + G.n + 8))
        + m * ((bc + 20) * (G.n * G.n)) :=
    Nat.add_le_add_right hone' _
  refine hcomb.trans ?_
  -- the `ℕ` arithmetic
  have hkey : (G.n * G.n + 1) * (bc + 1 + G.n + 8) + (bc + 20) * (G.n * G.n)
      ≤ (G.n + 1) ^ 2 * (bc + 1 + (bc + 1) + (G.n + 27)) := by
    have h1 : G.n * G.n + 1 ≤ (G.n + 1) ^ 2 := by nlinarith
    have h2 : bc + 1 + G.n + 8 ≤ bc + 1 + (bc + 1) + (G.n + 27) := by omega
    have h3 : bc + 20 ≤ bc + 1 + (bc + 1) + (G.n + 27) := by omega
    have h4 : G.n * G.n ≤ (G.n + 1) ^ 2 := by nlinarith
    have hm1 : (G.n * G.n + 1) * (bc + 1 + G.n + 8)
        ≤ (G.n + 1) ^ 2 * (bc + 1 + G.n + 8) := Nat.mul_le_mul h1 le_rfl
    have hm2 : (bc + 20) * (G.n * G.n) ≤ (G.n + 1) ^ 2 * (bc + 20) := by
      have h := Nat.mul_le_mul (le_refl (bc + 20)) h4
      calc (bc + 20) * (G.n * G.n) ≤ (bc + 20) * (G.n + 1) ^ 2 := h
        _ = (G.n + 1) ^ 2 * (bc + 20) := by ring
    have hsum : (bc + 1 + G.n + 8) + (bc + 20) = bc + 1 + (bc + 1) + (G.n + 27) := by omega
    calc (G.n * G.n + 1) * (bc + 1 + G.n + 8) + (bc + 20) * (G.n * G.n)
        ≤ (G.n + 1) ^ 2 * (bc + 1 + G.n + 8) + (G.n + 1) ^ 2 * (bc + 20) := Nat.add_le_add hm1 hm2
      _ = (G.n + 1) ^ 2 * ((bc + 1 + G.n + 8) + (bc + 20)) := by ring
      _ = (G.n + 1) ^ 2 * (bc + 1 + (bc + 1) + (G.n + 27)) := by rw [hsum]
  calc m * ((G.n * G.n + 1) * (bc + 1 + G.n + 8))
        + m * ((bc + 20) * (G.n * G.n))
      = m * ((G.n * G.n + 1) * (bc + 1 + G.n + 8) + (bc + 20) * (G.n * G.n)) := by ring
    _ ≤ m * ((G.n + 1) ^ 2 * (bc + 1 + (bc + 1) + (G.n + 27))) := Nat.mul_le_mul_left m hkey
    _ = Kbc2 m G := by rw [Kbc2, hbc]

/-- **The campaign round factor is `Poly`-computable**: `Kbc2 (mHalve (n·n)) G · mHalve (n·n)` is a
program of the request. -/
theorem poly_Kbc2_mHalve_mul :
    Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      Kbc2 (QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) p.1.1
        * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) := by
  have hbc2 : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1
        + (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1)) :=
    QMCLeafB.FuelWire.poly_nat_add QMCLeafB.FuelSlot.poly_bitCost_succ
      QMCLeafB.FuelSlot.poly_bitCost_succ
  have hrest : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg => p.1.1.n + 27) :=
    QMCLeafB.FuelWire.poly_nat_add QMCLeafB.InitVerdict.poly_nIdx
      (Automatic.Poly.const (β := ℕ) 27)
  have hcore : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      (p.1.1.n + 1) ^ 2
        * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1
            + (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1) + (p.1.1.n + 27))) :=
    QMCLeafB.FuelWire.poly_nat_mul (QMCLeafB.InitVerdict.poly_succPow 2)
      (QMCLeafB.FuelWire.poly_nat_add hbc2 hrest)
  exact QMCLeafB.FuelWire.poly_nat_mul
    (QMCLeafB.FuelWire.poly_nat_mul QMCLeafB.FuelWire.poly_mHalve hcore)
    QMCLeafB.FuelWire.poly_mHalve

/-- From `20 ≤ 2^k` to `22 ≤ 2^k` (a power of two above `20` is at least `32`). -/
theorem pow22_le {k : ℕ} (hk : 20 ≤ 2 ^ k) : 22 ≤ 2 ^ k := by
  have h5 : 5 ≤ k := by
    by_contra h
    have hk4 : k ≤ 4 := by omega
    have hle : 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
    norm_num at hle
    omega
  calc (22 : ℕ) ≤ 32 := by norm_num
    _ = 2 ^ 5 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h5

/-- **The campaign round factor's fuel length**: `Kbc2 (mHalve (n·n)) G · mHalve (n·n) ≤ S^(2^k)`
for `20 ≤ 2^k`. -/
theorem Kbc2_mHalve_le_seed (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (p : QMCLeafB.FuelWire.Pkg) :
    Kbc2 (QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) p.1.1
        * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
      ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k) := by
  have hS8 : 8 ≤ QMCLeafB.FuelWire.seedLen p := QMCLeafB.FuelWire.seedLen_ge_eight p
  have hS1 : 1 ≤ QMCLeafB.FuelWire.seedLen p := QMCLeafB.FuelWire.seedLen_one_le p
  have hS2 : 2 ≤ QMCLeafB.FuelWire.seedLen p := by omega
  set S := QMCLeafB.FuelWire.seedLen p with hSdef
  set bc := QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) with hbc
  set m := QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n) with hm
  have hn : p.1.1.n + 1 ≤ S := by
    have h : p.1.1.n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
      QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
    have hSe : S = 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length :=
      QMCLeafB.FuelWire.seedLen_eq p
    omega
  have hA : (p.1.1.n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hn 2
  have hbc4 : bc + p.1.1.n + 10 ≤ S ^ 4 := QMCLeafB.FuelWire.bitCost_add_le_seed_pow p
  have hbcS : bc ≤ S ^ 4 := by omega
  have hS4 : S ^ 4 + S ^ 4 = 2 * S ^ 4 := by ring
  have hE1 : bc + 19 ≤ S ^ 5 := by
    have h19 : 19 ≤ S ^ 2 := by
      have : (64 : ℕ) ≤ S ^ 2 := by
        have h := Nat.pow_le_pow_left hS8 2
        norm_num at h ⊢
        exact h
      omega
    have hb : bc + 19 ≤ S ^ 4 + S ^ 2 := Nat.add_le_add hbcS h19
    have h2 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS1 (by omega)
    have : S ^ 4 + S ^ 2 ≤ S ^ 4 + S ^ 4 := Nat.add_le_add_left h2 _
    rw [hS4] at this
    have h3 : 2 * S ^ 4 ≤ S * S ^ 4 := Nat.mul_le_mul_right _ hS2
    have h4 : S * S ^ 4 = S ^ 5 := by rw [pow_succ']; ring
    omega
  have hB : bc + 1 + (bc + 1) + (p.1.1.n + 27) ≤ S ^ 6 := by
    have hsum : bc + 1 + (bc + 1) + (p.1.1.n + 27) = (bc + p.1.1.n + 10) + (bc + 19) := by omega
    rw [hsum]
    have h5 : bc + 19 ≤ S ^ 5 := hE1
    have h45 : bc + p.1.1.n + 10 ≤ S ^ 5 :=
      le_trans hbc4 (Nat.pow_le_pow_right hS1 (by omega))
    exact QMCLeafB.FuelWire.add_le_pow hS2 h45 h5
  have hcore : (p.1.1.n + 1) ^ 2 * (bc + 1 + (bc + 1) + (p.1.1.n + 27)) ≤ S ^ 8 :=
    QMCLeafB.FuelWire.mul_le_pow hA hB
  have hm7 : m ≤ S ^ 7 := QMCLeafB.FuelWire.mHalve_le_seed p
  have hmm : m * m ≤ S ^ 14 := by
    have h := QMCLeafB.FuelWire.mul_le_pow hm7 hm7
    simpa using h
  have hEq : Kbc2 m p.1.1 * m
      = ((p.1.1.n + 1) ^ 2 * (bc + 1 + (bc + 1) + (p.1.1.n + 27))) * (m * m) := by
    rw [Kbc2, hbc, hm]; ring
  rw [hEq]
  calc ((p.1.1.n + 1) ^ 2 * (bc + 1 + (bc + 1) + (p.1.1.n + 27))) * (m * m)
      ≤ S ^ 8 * S ^ 14 := Nat.mul_le_mul hcore hmm
    _ = S ^ 22 := by rw [← pow_add]
    _ ≤ S ^ (2 ^ k) := Nat.pow_le_pow_right hS1 (pow22_le hk)

/-- **The campaign round factor satisfies brick 1's count side condition, unconditionally.**  At
`Rq G = 0` the tolerance is `1` and m1/m4's estimate applies; otherwise it is §5 + §6. -/
theorem shallowKbound_Kbc2 (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
      (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G := by
  by_cases h : QMCLeafB.EngineRuntime.Rq G = 0
  · exact le_trans (shallowKbound_of_dq_one G h) (Kbc_le_Kbc2 _ G)
  · exact budgetRounds_dqShallow_le_Kbc2 G _ h


/-! ## 8.  Interface facts for brick 4 (`RunParts` at the campaign family)

`RunPartsDilate.runParts_of_dilated` is generic in `P : RunParams G`; at `paramsShallowKf` its two
scalar hypotheses are the facts below, so brick 4 needs no new arithmetic — only the `Rq = 0` case,
where the rounding budget is unprovable and the bracket is empty instead. -/

theorem paramsShallowKf_rmax_pos (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    0 < (paramsShallowKf Kf hK G).rmax :=
  QMCLeafB.RundataHalving.rmaxOf_pos (G.n * G.n) (by
    have h := Nat.mul_le_mul hn hn
    omega)

/-- **The rounding budget at the campaign family** — `RunParams.hcert`'s arithmetic, and the reason
the family cannot be run at `dq = 1`. -/
theorem paramsShallowKf_budget (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * (paramsShallowKf Kf hK G).dq / 4)
      + (paramsShallowKf Kf hK G).dq / 2 - QMCLeafB.RundataCert.eps G
      ≤ QMCLeafB.RundataCert.eps G := by
  rw [paramsShallowKf_dq, dqShallow_eq_core G hRq.ne']
  exact QMCLeafB.RundataParams.dqShallow_budget G hn hRq

/-- At `Rq G = 0` the interior bracket is empty: there is nothing for `RunParts` to say, and the
rounding budget above is *false* there (`eps = 0` but `dq = 1`), so this case must be split off. -/
theorem interior_bracket_empty_of_Rq_zero (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hRq : QMCLeafB.EngineRuntime.Rq G = 0) (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) : False := by
  rw [hRq] at hlo hlt
  have h0 : ((0 : ℚ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hlo
  simp at hlt
  linarith


/-! ## 7.  The final glue: `SolutionStatement` with **no** numeric hypothesis

`shallowKbound_Kbc2` discharges brick 1's count side condition at the campaign factor `Kbc2`, and
`poly_Kbc2_mHalve_mul`/`Kbc2_mHalve_le_seed` its fuel arithmetic.  So the union theorem below has no
numeric residual at all: what is left is exactly the three items (ledger, `htop`, `hd`), the init
program and its tape-freeness. -/

/-- **`SolutionStatement` at the campaign family, all numeric side conditions discharged.**
Residual: the init program `init` (`Poly` + tape-free) from brick 1, the one-step size ledger
`(hMinv, hstep, hM)` from brick 2, `htop` at `2 ≤ G.n` from brick 3, and one `RunParts` per interior
`(G, t)` from brick 4. -/
theorem solution_union_shallow_final {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (M : σ → ℕ) (C₀ c kr : ℕ) (hkr : 1 ≤ kr)
    (hMinv : ∀ s, M (round s) ≤ M s + c)
    (hstep : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => Kbc2 (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
          * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => Kbc2 (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (paramsShallowKf (fun G => Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
          (fun G => shallowKbound_Kbc2 G) G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_union_shallow_gen (fun G => Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G) k
    poly_Kbc2_mHalve_mul (Kbc2_mHalve_le_seed k hk) (fun G => shallowKbound_Kbc2 G)
    init round verdict hinit hr hv M C₀ c kr hkr hMinv hstep hM hinitTape htop hd

/-- The `RunParts` family the final glue consumes, spelled out. -/
abbrev paramsKbc2 : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G :=
  paramsShallowKf (fun G => Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
    (fun G => shallowKbound_Kbc2 G)

@[simp] theorem paramsKbc2_K (G : QuantumMaxCutEnergy.Input) :
    (paramsKbc2 G).K = Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G := rfl

@[simp] theorem paramsKbc2_m (G : QuantumMaxCutEnergy.Input) :
    (paramsKbc2 G).m = QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

@[simp] theorem paramsKbc2_dq (G : QuantumMaxCutEnergy.Input) :
    (paramsKbc2 G).dq = QMCLeafB.RundataParams.dqShallow G := rfl

/-- The run count at `paramsKbc2`, in closed form — the `T` of `RunParts.hverdict` and of the
`htop` instances. -/
theorem paramsKbc2_K_mul_m (G : QuantumMaxCutEnergy.Input) :
    (paramsKbc2 G).K * (paramsKbc2 G).m
      = Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
        * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

/-- The run count at `paramsKbc2` is positive — what the `htop` instances ask for. -/
theorem one_le_Kbc2_mul (G : QuantumMaxCutEnergy.Input) :
    1 ≤ Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
      * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := by
  have hm : 1 ≤ QMCLeafB.HalvePerG.mHalve (G.n * G.n) :=
    QMCLeafB.HalvePerG.one_le_mHalve (G.n * G.n)
  have hK : 1 ≤ Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G := by
    unfold Kbc2
    have h2 : 1 ≤ (G.n + 1) ^ 2 := Nat.one_le_pow 2 (G.n + 1) (by omega)
    have h3 : 1 ≤ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1
        + (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1) + (G.n + 27) := by
      omega
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ QMCLeafB.HalvePerG.mHalve (G.n * G.n) * ((G.n + 1) ^ 2
            * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1
                + (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1) + (G.n + 27))) :=
          Nat.mul_le_mul hm (Nat.mul_le_mul h2 h3)
  calc (1 : ℕ) = 1 * 1 := by ring
    _ ≤ Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
          * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := Nat.mul_le_mul hK hm


/-- **Brick 4's two scalar inputs at `paramsKbc2`** (for `RunPartsDilate.runParts_of_dilated`). -/
theorem paramsKbc2_rmax_pos (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    0 < (paramsKbc2 G).rmax :=
  paramsShallowKf_rmax_pos _ _ G hn

theorem paramsKbc2_budget (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * (paramsKbc2 G).dq / 4)
      + (paramsKbc2 G).dq / 2 - QMCLeafB.RundataCert.eps G
      ≤ QMCLeafB.RundataCert.eps G :=
  paramsShallowKf_budget _ _ G hn hRq

end QMCLeafB.UnionShallow

/-! ## Axiom audit -/

#print axioms QMCLeafB.UnionShallow.solution_of_runParts_interior_of_params_hn
#print axioms QMCLeafB.UnionShallow.paramsShallowKf_K
#print axioms QMCLeafB.UnionShallow.paramsShallowKf_m
#print axioms QMCLeafB.UnionShallow.paramsShallowKf_K_mul_m
#print axioms QMCLeafB.UnionShallow.solution_union_shallow_gen
#print axioms QMCLeafB.UnionShallow.solution_union_shallow
#print axioms QMCLeafB.UnionShallow.paramsShallowKf_rmax_pos
#print axioms QMCLeafB.UnionShallow.paramsShallowKf_budget
#print axioms QMCLeafB.UnionShallow.interior_bracket_empty_of_Rq_zero
#print axioms QMCLeafB.UnionShallow.shallowKbound_of_dq_one
#print axioms QMCLeafB.UnionShallow.budgetRounds_le_one_add
#print axioms QMCLeafB.UnionShallow.inv_Rq_le_two_pow_bitCost
#print axioms QMCLeafB.UnionShallow.dqShallow_le_one
#print axioms QMCLeafB.UnionShallow.inv_dqShallow_le
#print axioms QMCLeafB.UnionShallow.budgetRounds_dqShallow_le_Kbc2
#print axioms QMCLeafB.UnionShallow.poly_Kbc2_mHalve_mul
#print axioms QMCLeafB.UnionShallow.Kbc2_mHalve_le_seed
#print axioms QMCLeafB.UnionShallow.shallowKbound_Kbc2
#print axioms QMCLeafB.UnionShallow.solution_union_shallow_final
#print axioms QMCLeafB.UnionShallow.paramsKbc2_budget
#print axioms QMCLeafB.UnionShallow.one_le_Kbc2_mul
#print axioms QMCLeafB.UnionShallow.paramsKbc2_K_mul_m


