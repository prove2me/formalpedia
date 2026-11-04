-- Prove2me | Definitions.Def_QMCLeafB_fuel_slot_m1
-- name    : QMCLeafB_fuel_slot_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:42:50.907425+00:00
-- url     : https://prove2.me/theorems/6ec525f7-85c5-43c1-92f9-e830e26b8ee0
-- title:
--   QMCLeafB fuel_slot_m1
-- statement:
--   # leaf B phase 13 — `fuel-slot` (swarm `smw17fqzz`, member m1, direction d6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_init_verdict_m8
import Definitions.Def_QMCLeafB_roundcount_estimate_m1
/-
# leaf B phase 13 — `fuel-slot` (swarm `smw17fqzz`, member m1, direction d6)

**The `fuel` slot of `QMCLeafB.InitVerdict.solution_of_loop_hn`, closed at m8's σ.**  m8's residual
after f47 was `hK` (the round count) — now `BudgetBound`/`RoundCountEstimate` — plus a fuel length
that is a `Poly` function of the request, tape-free in its *value*, and below a power of the padded
seed.  This file supplies that:

* `fuelCount m p = 880·m·(n+1)³·(bitCost (Rq G) + 1)³`;
* `poly_fuelCount` — `Automatic.Poly fuelCount` (`poly_succPow`, `poly_bitCostRq`, `Poly.nat_mul`);
* `budgetRounds_le_fuelCount` — `FinalStroke.budgetRounds G 1 m ≤ fuelCount m ((G,[]),t)`, i.e. `hK`;
* `fuelCount_le_seed` — `fuelCount m p ≤ (padList ++ encodeRequest p.1).length ^ (2^k)` for `2^k ≥ 37`,
  exactly `InitVerdict.fuelPad_length_of_le`'s hypothesis;
* `fuel k m := InitVerdict.fuelPad k (fuelCount m)`, with `poly_fuel`, `fuel_length`, and
  `fuel_length_tape_free`: `(fuel k m p).length = fuelCount m ((p.1.1, []), p.2)`, the tape-free `T0`
  that `hspec` needs.

No `sorry`, no `axiom`; audits at the end.
-/

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.FuelSlot

open QuantumMaxCutEnergy

/-- The request coding the closing forms use. -/
local instance instRequestCodingFuelSlot :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- Pointwise product of two `Poly` functions into `ℕ`. -/
theorem poly_mul2 {f g : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ}
    (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun p => f p * g p) :=
  Poly.comp (f := fun x : ℕ × ℕ => x.1 * x.2) (g := fun p => (f p, g p))
    Poly.nat_mul (Poly.pair hf hg)

/-- Pointwise sum of two `Poly` functions into `ℕ`. -/
theorem poly_add2 {f g : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ}
    (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun p => f p + g p) :=
  Poly.comp (f := fun x : ℕ × ℕ => x.1 + x.2) (g := fun p => (f p, g p))
    Poly.nat_add (Poly.pair hf hg)

/-- The `bitCost` of the total weight, plus one, as a `Poly` function of the request. -/
theorem poly_bitCost_succ : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
    QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1) :=
  poly_add2 QMCLeafB.Hspec.poly_bitCostRq (Automatic.Poly.const (β := ℕ) 1)

/-- The round count the run is allowed.  Written in the association the `Poly` composition
produces, so that `poly_fuelCount` is `exact`. -/
def fuelCount (m : ℕ) (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : ℕ :=
  (880 * m) * ((p.1.1.n + 1) ^ 3
    * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1)
        * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1)
            * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1))))

/-- The same count in cube form. -/
theorem fuelCount_eq (m : ℕ) (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    fuelCount m p
      = 880 * m * ((p.1.1.n + 1) ^ 3
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1) ^ 3) := by
  simp only [fuelCount]
  ring

/-- **`Poly`**: the count is a polynomial-time function of the request. -/
theorem poly_fuelCount (m : ℕ) : Automatic.Poly (fuelCount m) := by
  have hbit := poly_bitCost_succ
  have h2 : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1)
        * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1)) :=
    poly_mul2 hbit hbit
  have h3 : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1)
        * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1)
            * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1))) :=
    poly_mul2 hbit h2
  have hn : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (p.1.1.n + 1) ^ 3) := QMCLeafB.InitVerdict.poly_succPow 3
  have hprod : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (p.1.1.n + 1) ^ 3
        * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1)
            * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1)
                * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1)))) :=
    poly_mul2 hn h3
  have hconst : Automatic.Poly (fun _ : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => 880 * m) :=
    Automatic.Poly.const (880 * m)
  exact poly_mul2 hconst hprod

/-- **`hK`**: the count dominates the budget. -/
theorem budgetRounds_le_fuelCount (G : QuantumMaxCutEnergy.Input) (m : ℕ) (t : ℚ) :
    QMCLeafB.FinalStroke.budgetRounds G 1 m ≤ fuelCount m ((G, []), t) := by
  rw [fuelCount_eq]
  refine le_trans (QMCLeafB.RoundCountEstimate.budgetRounds_le_bitCost G m) ?_
  set bc := QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) with hbc
  have hb : (1 : ℕ) ≤ bc + 1 := by omega
  have hcube : bc + 1 ≤ (bc + 1) ^ 3 := by
    have h2 : (1 : ℕ) ≤ (bc + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc bc + 1 = (bc + 1) * 1 := by ring
      _ ≤ (bc + 1) * (bc + 1) ^ 2 := Nat.mul_le_mul_left _ h2
      _ = (bc + 1) ^ 3 := by ring
  have h1 : (1 : ℕ) ≤ (G.n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : (1 : ℕ) ≤ (G.n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h3 : (1 : ℕ) ≤ (bc + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hkey : (G.n + 1) ^ 2 * (bc + G.n + 10) ≤ 880 * ((G.n + 1) ^ 3 * (bc + 1) ^ 3) := by
    rcases Nat.eq_zero_or_pos G.n with h0 | h0
    · rw [h0]
      have e1 : bc + 10 ≤ 11 * (bc + 1) := by omega
      have e2 : 11 * (bc + 1) ≤ 880 * (bc + 1) ^ 3 := by nlinarith [hb, h3]
      simp only [Nat.zero_add, Nat.one_pow, Nat.mul_one]
      nlinarith [e1, e2]
    · have e1 : bc + G.n + 10 ≤ 12 * (G.n + 1) * (bc + 1) := by nlinarith [hb, h0]
      have e2 : 12 * (G.n + 1) * (bc + 1) ≤ 880 * (G.n + 1) * (bc + 1) ^ 3 := by
        have : (12 : ℕ) ≤ 880 := by norm_num
        have hc : (bc + 1) * (bc + 1) ≤ (bc + 1) ^ 3 := by
          have h2' : (1 : ℕ) ≤ bc + 1 := hb
          nlinarith [h3, hb]
        nlinarith [this, hcube, hb]
      nlinarith [e1, e2, h1, h2, h3]
  calc m * ((G.n + 1) ^ 2 * (bc + G.n + 10))
      ≤ m * (880 * ((G.n + 1) ^ 3 * (bc + 1) ^ 3)) := Nat.mul_le_mul_left m hkey
    _ = 880 * m * ((G.n + 1) ^ 3 * (bc + 1) ^ 3) := by ring


/-- **The seed bound**: the count is below `(padList ++ encodeRequest p.1).length ^ (2^k)` for
`2^k ≥ 37`, which is `fuelPad_length_of_le`'s hypothesis. -/
theorem fuelCount_le_seed (m : ℕ) (hm : m ≤ 8) (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ))
    {k : ℕ} (hk : 37 ≤ 2 ^ k) :
    fuelCount m p
      ≤ (QMCLeafB.InitVerdict.padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k) := by
  set L := (QuantumMaxCutEnergy.encodeInput p.1.1).length with hL
  set S := (QMCLeafB.InitVerdict.padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length with hS
  have hpad : QMCLeafB.InitVerdict.padList.length = 8 := QMCLeafB.InitVerdict.padList_length
  have hreq : (QuantumMaxCutEnergy.encodeRequest p.1).length = L + (p.1.2).length := by
    rw [hL]
    simp [QuantumMaxCutEnergy.encodeRequest, List.length_append]
  have hSL : L + 8 ≤ S := by
    rw [hS]
    simp only [List.length_append, hpad, hreq]
    omega
  have hS8 : 8 ≤ S := by
    rw [hS]
    simp only [List.length_append, hpad, hreq]
    omega
  have hn : p.1.1.n ≤ L := by
    rw [hL]
    simp only [QuantumMaxCutEnergy.encodeInput, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  have hbc : QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) ≤ 48 * L + 16 :=
    QMCLeafB.Hspec.bitCost_Rq_le p.1.1
  have h1 : p.1.1.n + 1 ≤ S := by omega
  have h2 : QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1 ≤ 65 * S := by omega
  have h3 : m ≤ S := by omega
  have h4 : (880 : ℕ) ≤ S ^ 4 := by
    have h8 : (8 : ℕ) ^ 4 ≤ S ^ 4 := Nat.pow_le_pow_left hS8 4
    have : (880 : ℕ) ≤ 8 ^ 4 := by norm_num
    exact le_trans this h8
  have hA : (p.1.1.n + 1) ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left h1 3
  have hB : (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1) ^ 3
      ≤ (65 * S) ^ 3 := Nat.pow_le_pow_left h2 3
  rw [fuelCount_eq]
  calc 880 * m * ((p.1.1.n + 1) ^ 3
        * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1) ^ 3)
      ≤ S ^ 4 * S * (S ^ 3 * (65 * S) ^ 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul h4 h3) (Nat.mul_le_mul hA hB)
    _ = 65 ^ 3 * S ^ 11 := by ring
    _ ≤ 2 ^ 19 * S ^ 11 := by
        have h65 : (65 : ℕ) ^ 3 ≤ 2 ^ 19 := by norm_num
        exact Nat.mul_le_mul_right _ h65
    _ ≤ S ^ 19 * S ^ 11 := by
        have h2S : (2 : ℕ) ≤ S := by omega
        have h19 : (2 : ℕ) ^ 19 ≤ S ^ 19 := Nat.pow_le_pow_left h2S 19
        exact Nat.mul_le_mul_right _ h19
    _ = S ^ 30 := by ring
    _ ≤ S ^ (2 ^ k) := Nat.pow_le_pow_right (by omega) (by omega)

/-- **The fuel**: m8's padded-square iterate at the count above. -/
def fuel (k m : ℕ) : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool :=
  QMCLeafB.InitVerdict.fuelPad k (fuelCount m)

/-- **`Poly` for the fuel.** -/
theorem poly_fuel (k m : ℕ) : Automatic.Poly (fuel k m) :=
  QMCLeafB.InitVerdict.poly_fuelPad k (fuelCount m) (poly_fuelCount m)

/-- **The fuel length is exactly the count** — `hfuelLen` for any `2^k ≥ 37`, `m ≤ 8`. -/
theorem fuel_length (k m : ℕ) (hm : m ≤ 8) {hk : 37 ≤ 2 ^ k}
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    (fuel k m p).length = fuelCount m p :=
  QMCLeafB.InitVerdict.fuelPad_length_of_le k (fuelCount m) p (fuelCount_le_seed m hm p hk)

/-- **The count is tape-free**: `T0 G t := fuelCount m ((G, []), t)` is the round count the loop
actually runs, whatever the tape. -/
theorem fuelCount_tape_free (m : ℕ) (G : QuantumMaxCutEnergy.Input) (t : ℚ) (tape : List Bool) :
    fuelCount m ((G, tape), t) = fuelCount m ((G, []), t) := rfl

end QMCLeafB.FuelSlot

/-! ## Axiom audit -/

#print axioms QMCLeafB.FuelSlot.poly_mul2
#print axioms QMCLeafB.FuelSlot.poly_add2
#print axioms QMCLeafB.FuelSlot.poly_bitCost_succ
#print axioms QMCLeafB.FuelSlot.fuelCount_eq
#print axioms QMCLeafB.FuelSlot.poly_fuelCount
#print axioms QMCLeafB.FuelSlot.budgetRounds_le_fuelCount
#print axioms QMCLeafB.FuelSlot.fuelCount_le_seed
#print axioms QMCLeafB.FuelSlot.poly_fuel
#print axioms QMCLeafB.FuelSlot.fuel_length
#print axioms QMCLeafB.FuelSlot.fuelCount_tape_free


