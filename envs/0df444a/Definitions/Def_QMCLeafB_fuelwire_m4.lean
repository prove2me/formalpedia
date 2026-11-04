-- Prove2me | Definitions.Def_QMCLeafB_fuelwire_m4
-- name    : QMCLeafB_fuelwire_m4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:09:19.259587+00:00
-- url     : https://prove2.me/theorems/164d32ca-281b-4d7a-8d4a-614b653ad7e2
-- title:
--   QMCLeafB fuelwire_m4
-- statement:
--   # leaf B phase 14 — brick `fuel-wire` (swarm `smw1a99tp`, member m4, direction d4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_fuel_slot_m1
import Definitions.Def_QMCLeafB_LoopRestate
import Definitions.Def_QMCLeafB_halve_perG_m2
/-
# leaf B phase 14 — brick `fuel-wire` (swarm `smw1a99tp`, member m4, direction d4)

The closing stroke `QMCLeafB.FinalStroke.endgame_of_dominated_rounds_interior` asks for a `Poly`
program `fuel` whose **length is exactly the loop's round count**:

    hfuelLen : ∀ p, (fuel p).length = K p.1.1 * m

`Check_fuel_slot_m1` and `Check_brick_init_verdict_m8` supply the two halves of that (a padded seed
with an exact truncation, and a monomial dominating the budget), but they are wired to the *older*
`InitVerdict.endgame_of_my_loop`, not to the closing stroke.  This file wires them to the stroke:

* §1 the padded seed `seedLen` and the exponent arithmetic;
* §2 two round factors — m1's estimate shape
  `Kbc m G = m·(n+1)²·(bitCost(Rq G) + n + 10)` (whose budget inequality is m1's
  `budgetRounds_le_bitCost` **at `dq = 1`, no hypothesis**) and m8's corrected monomial
  `Kpow d m G = (n+1)^d + m`;
* §3 `fuelOf k Kf m := fuelPad k (Kf G · m)`: `Automatic.Poly` as soon as `Kf G · m` is, exact length
  `Kf G · m` from the seed bound, and the length is tape-free;
* §4 the closing stroke with the fuel slots **discharged** — three variants (interior
  `endgame_of_dominated_rounds_interior`, orbit `endgame_orbit_of_parts`, and
  `LoopRestate.solution_of_loop_bounded`) — plus the two concrete instances of §2, of which the
  `dq = 1` one has *no* fuel or round-count hypothesis left.

No `sorry`, no `axiom`; audits at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.FuelWire

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

local instance instRequestCodingFuelWire : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- The closing input of the leaf. -/
abbrev Pkg := (QuantumMaxCutEnergy.Input × List Bool) × ℚ

/-! ## 1.  The padded seed and its exponent arithmetic -/

/-- **The padded seed of the fuel**: `padList ++ encodeRequest p.1`, whose length is what `fuelPad`
raises to `2^k`. -/
def seedLen (p : Pkg) : ℕ :=
  (QMCLeafB.InitVerdict.padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length

theorem seedLen_eq (p : Pkg) :
    seedLen p = 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length := by
  simp [seedLen, QMCLeafB.InitVerdict.padList_length]

theorem seedLen_ge_eight (p : Pkg) : 8 ≤ seedLen p := by
  rw [seedLen_eq]; omega

theorem seedLen_one_le (p : Pkg) : 1 ≤ seedLen p := le_trans (by norm_num) (seedLen_ge_eight p)

/-- A product of two `S`-powers is an `S`-power. -/
theorem mul_le_pow {a b d e S : ℕ} (ha : a ≤ S ^ d) (hb : b ≤ S ^ e) :
    a * b ≤ S ^ (d + e) := by
  rw [pow_add]
  exact Nat.mul_le_mul ha hb

/-- Pointwise product of two `Poly` functions into `ℕ` (as `Check_fuel_slot_m1`'s `poly_mul2`). -/
theorem poly_nat_mul {f g : Pkg → ℕ} (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun p => f p * g p) :=
  Poly.comp (f := fun y : ℕ × ℕ => y.1 * y.2) (g := fun p => (f p, g p))
    Poly.nat_mul (Poly.pair hf hg)

/-- Pointwise sum of two `Poly` functions into `ℕ`. -/
theorem poly_nat_add {f g : Pkg → ℕ} (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun p => f p + g p) :=
  Poly.comp (f := fun y : ℕ × ℕ => y.1 + y.2) (g := fun p => (f p, g p))
    Poly.nat_add (Poly.pair hf hg)

/-! ## 2.  The two round factors -/

/-! ### 2a.  m1's estimate shape -/

/-- **m1's round-count factor**: the right-hand side of `budgetRounds_le_bitCost`, as a factor of the
round count.  Written in the association the `Poly` composition produces. -/
def Kbc (m : ℕ) (G : QuantumMaxCutEnergy.Input) : ℕ :=
  m * ((G.n + 1) ^ 2
    * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1) + (G.n + 9)))

/-- The same factor in the shape m1's estimate is stated in. -/
theorem Kbc_eq (m : ℕ) (G : QuantumMaxCutEnergy.Input) :
    Kbc m G
      = m * ((G.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10)) := by
  unfold Kbc
  rw [show QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 1 + (G.n + 9)
      = QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 10 by omega]

/-- **The budget inequality at `dq = 1`, with no hypothesis**: m1's `budgetRounds_le_bitCost`. -/
theorem budgetRounds_le_Kbc (m : ℕ) (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.FinalStroke.budgetRounds G 1 m ≤ Kbc m G := by
  rw [Kbc_eq]
  exact QMCLeafB.RoundCountEstimate.budgetRounds_le_bitCost G m

/-- **`Kbc m G · m` is a program.** -/
theorem poly_Kbc_mul (m : ℕ) :
    Automatic.Poly (fun p : Pkg => Kbc m p.1.1 * m) := by
  have hcore : Automatic.Poly (fun p : Pkg =>
      (p.1.1.n + 1) ^ 2
        * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1) + (p.1.1.n + 9))) :=
    poly_nat_mul (QMCLeafB.InitVerdict.poly_succPow 2)
      (poly_nat_add QMCLeafB.FuelSlot.poly_bitCost_succ
        (poly_nat_add QMCLeafB.InitVerdict.poly_nIdx
          (Automatic.Poly.const (β := ℕ) 9)))
  exact poly_nat_mul
    (poly_nat_mul (Automatic.Poly.const (β := ℕ) m) hcore)
    (Automatic.Poly.const (β := ℕ) m)

/-- **The bit cost and the order fit under `S^4`.** -/
theorem bitCost_add_le_seed_pow (p : Pkg) :
    QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10
      ≤ seedLen p ^ 4 := by
  have hS8 : 8 ≤ seedLen p := seedLen_ge_eight p
  have hS : seedLen p = 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length := seedLen_eq p
  have hn : p.1.1.n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
    QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
  have hbc : QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1)
      ≤ 48 * (QuantumMaxCutEnergy.encodeInput p.1.1).length + 16 :=
    QMCLeafB.Hspec.bitCost_Rq_le p.1.1
  have hLI : (QuantumMaxCutEnergy.encodeInput p.1.1).length
      ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length := by
    simp [QuantumMaxCutEnergy.encodeRequest, List.length_append]
  have h1 : QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10
      ≤ 49 * (QuantumMaxCutEnergy.encodeRequest p.1).length + 25 := by omega
  have h2 : 49 * (QuantumMaxCutEnergy.encodeRequest p.1).length + 25 ≤ 76 * seedLen p := by
    omega
  have h512 : (512 : ℕ) ≤ seedLen p ^ 3 := by
    have h := Nat.pow_le_pow_left hS8 3
    simpa using h
  have h3 : 76 * seedLen p ≤ seedLen p ^ 4 := by
    calc 76 * seedLen p ≤ 512 * seedLen p := by
          have h76 : (76 : ℕ) ≤ 512 := by norm_num
          exact Nat.mul_le_mul_right (seedLen p) h76
      _ ≤ seedLen p ^ 3 * seedLen p := Nat.mul_le_mul_right (seedLen p) h512
      _ = seedLen p ^ 4 := by ring
  omega

/-- **The seed bound for m1's factor**, for `m ≤ 8` and `2^k ≥ 8`. -/
theorem Kbc_mul_le_seed (k m : ℕ) (hm : m ≤ 8) (hk : 8 ≤ 2 ^ k) (p : Pkg) :
    Kbc m p.1.1 * m ≤ seedLen p ^ (2 ^ k) := by
  have hS8 : 8 ≤ seedLen p := seedLen_ge_eight p
  have hS1 : 1 ≤ seedLen p := seedLen_one_le p
  have hSn : p.1.1.n + 1 ≤ seedLen p := by
    have h : p.1.1.n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
      QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
    have hS : seedLen p = 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length := seedLen_eq p
    omega
  have hA : (p.1.1.n + 1) ^ 2 ≤ seedLen p ^ 2 := Nat.pow_le_pow_left hSn 2
  have hB : QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10
      ≤ seedLen p ^ 4 := bitCost_add_le_seed_pow p
  have hmS : m ≤ seedLen p := by omega
  have hmm : m * m ≤ seedLen p ^ 2 := by
    calc m * m ≤ seedLen p * seedLen p := Nat.mul_le_mul hmS hmS
      _ = seedLen p ^ 2 := (pow_two _).symm
  have hEq : Kbc m p.1.1 * m
      = ((p.1.1.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10))
        * (m * m) := by
    rw [Kbc_eq]; ring
  rw [hEq]
  calc ((p.1.1.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10)) * (m * m)
      ≤ (seedLen p ^ 2 * seedLen p ^ 4) * seedLen p ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul hA hB) hmm
    _ = seedLen p ^ 8 := by ring
    _ ≤ seedLen p ^ (2 ^ k) := Nat.pow_le_pow_right hS1 hk

/-! ### 2b.  m8's corrected monomial -/

/-- **m8's corrected monomial factor**: `(n+1)^d + m` (the additive `m` is what dominates the empty
graph's budget). -/
def Kpow (d m : ℕ) (G : QuantumMaxCutEnergy.Input) : ℕ := (G.n + 1) ^ d + m

/-- **`Kpow d m G · m` is a program.** -/
theorem poly_Kpow_mul (d m : ℕ) :
    Automatic.Poly (fun p : Pkg => Kpow d m p.1.1 * m) :=
  poly_nat_mul (QMCLeafB.InitVerdict.poly_succPowAdd d m)
    (Automatic.Poly.const (β := ℕ) m)

/-- **The seed bound for m8's factor** (`Check_brick_init_verdict_m8.monomial_add_mul_le_seed_pow`). -/
theorem Kpow_mul_le_seed (k d m : ℕ) (hk : 2 ≤ k) (hd : d + 2 ≤ 2 ^ k) (hm : m ≤ 8) (p : Pkg) :
    Kpow d m p.1.1 * m ≤ seedLen p ^ (2 ^ k) := by
  have h := QMCLeafB.InitVerdict.monomial_add_mul_le_seed_pow k d m hk hd hm p
  simpa [Kpow, seedLen] using h

/-- A sum of two equal `S`-powers is one power higher. -/
theorem add_le_pow {a b e S : ℕ} (hS : 2 ≤ S) (ha : a ≤ S ^ e) (hb : b ≤ S ^ e) :
    a + b ≤ S ^ (e + 1) := by
  have h : S ^ e + S ^ e = 2 * S ^ e := by ring
  have h1 : 2 * S ^ e ≤ S * S ^ e := Nat.mul_le_mul_right _ hS
  have h2 : S * S ^ e = S ^ (e + 1) := (pow_succ' _ _).symm
  omega

/-- **The seed bound for m8's factor**, generalised: `m` only has to be below an `S`-power. -/
theorem Kpow_mul_le_seed_gen (k c d m : ℕ) (hm : m ≤ 8 ^ c) (hd : d + 3 * c + 1 ≤ 2 ^ k)
    (p : Pkg) :
    Kpow d m p.1.1 * m ≤ seedLen p ^ (2 ^ k) := by
  have hS8 : 8 ≤ seedLen p := seedLen_ge_eight p
  have hS1 : 1 ≤ seedLen p := seedLen_one_le p
  have hS2 : 2 ≤ seedLen p := by omega
  have hmS : m ≤ seedLen p ^ c :=
    le_trans hm (Nat.pow_le_pow_left hS8 c)
  have hn : p.1.1.n + 1 ≤ seedLen p := by
    have h : p.1.1.n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
      QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
    have hS : seedLen p = 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length := seedLen_eq p
    omega
  have hA : (p.1.1.n + 1) ^ d ≤ seedLen p ^ d := Nat.pow_le_pow_left hn d
  have hmm : m * m ≤ seedLen p ^ (2 * c) := by
    have h := Nat.mul_le_mul hmS hmS
    rw [← pow_add] at h
    simpa [two_mul] using h
  have h1 : (p.1.1.n + 1) ^ d * m ≤ seedLen p ^ (d + c) := mul_le_pow hA hmS
  have h2 : m * m ≤ seedLen p ^ (2 * c) := hmm
  have hEq : Kpow d m p.1.1 * m = (p.1.1.n + 1) ^ d * m + m * m := by
    unfold Kpow; ring
  rw [hEq]
  have e1 : d + c ≤ d + 3 * c := by omega
  have e2 : 2 * c ≤ d + 3 * c := by omega
  calc (p.1.1.n + 1) ^ d * m + m * m
      ≤ seedLen p ^ (d + 3 * c) + seedLen p ^ (d + 3 * c) :=
        Nat.add_le_add (le_trans h1 (Nat.pow_le_pow_right hS1 e1))
          (le_trans h2 (Nat.pow_le_pow_right hS1 e2))
    _ ≤ seedLen p ^ (d + 3 * c + 1) := add_le_pow hS2 le_rfl le_rfl
    _ ≤ seedLen p ^ (2 ^ k) := Nat.pow_le_pow_right hS1 (by omega)

/-! ## 3.  The fuel of exact round count -/

/-- **The padded fuel at the round count `Kf G · m`.**  `k` squarings of the padded request word,
truncated at `Kf G · m`. -/
def fuelOf (k : ℕ) (Kf : QuantumMaxCutEnergy.Input → ℕ) (m : ℕ) (p : Pkg) : List Bool :=
  QMCLeafB.InitVerdict.fuelPad k (fun q : Pkg => Kf q.1.1 * m) p

theorem fuelOf_eq (k : ℕ) (Kf : QuantumMaxCutEnergy.Input → ℕ) (m : ℕ) (p : Pkg) :
    fuelOf k Kf m p
      = QMCLeafB.InitVerdict.fuelPad k (fun q : Pkg => Kf q.1.1 * m) p := rfl

/-- **The length of the fuel is exactly the round count** — the stroke's `hfuelLen`. -/
theorem fuelOf_length (k : ℕ) (Kf : QuantumMaxCutEnergy.Input → ℕ) (m : ℕ)
    (hseed : ∀ p : Pkg, Kf p.1.1 * m ≤ seedLen p ^ (2 ^ k)) (p : Pkg) :
    (fuelOf k Kf m p).length = Kf p.1.1 * m :=
  QMCLeafB.InitVerdict.fuelPad_length_of_le k _ p (by simpa [seedLen] using hseed p)

/-- **The fuel is a program.** -/
theorem poly_fuelOf (k : ℕ) (Kf : QuantumMaxCutEnergy.Input → ℕ) (m : ℕ)
    (hKf : Automatic.Poly (fun p : Pkg => Kf p.1.1 * m)) :
    Automatic.Poly (fuelOf k Kf m) :=
  QMCLeafB.InitVerdict.poly_fuelPad k (fun q : Pkg => Kf q.1.1 * m) hKf

/-- **The fuel's length is tape-free** (the round count only sees `G`). -/
theorem fuelOf_length_tape_free (k : ℕ) (Kf : QuantumMaxCutEnergy.Input → ℕ) (m : ℕ)
    (hseed : ∀ p : Pkg, Kf p.1.1 * m ≤ seedLen p ^ (2 ^ k))
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (tape : List Bool) :
    (fuelOf k Kf m ((G, tape), t)).length = (fuelOf k Kf m ((G, []), t)).length := by
  rw [fuelOf_length k Kf m hseed, fuelOf_length k Kf m hseed]

/-- **The tape-free round count** the loop is run for. -/
def T0Of (Kf : QuantumMaxCutEnergy.Input → ℕ) (m : ℕ) (G : QuantumMaxCutEnergy.Input)
    (_t : ℚ) : ℕ :=
  Kf G * m

/-- **`hspec` from the fuel's length**: the loop on an arbitrary tape equals `loopBit` at `T0Of`
(as soon as `init` ignores the tape).  `FinalStroke.hspec_of_tape_free`, at the fuel of §3. -/
theorem hspecOf (k : ℕ) (Kf : QuantumMaxCutEnergy.Input → ℕ) (m : ℕ)
    (hseed : ∀ p : Pkg, Kf p.1.1 * m ≤ seedLen p ^ (2 ^ k)) {σ : Type} [Coding σ]
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (p : Pkg) :
    verdict (Nat.iterate round (fuelOf k Kf m p).length (init p))
      = QMCLeafB.FinalStroke.loopBit init round verdict (T0Of Kf m) p.1.1 p.2 :=
  QMCLeafB.FinalStroke.hspec_of_tape_free init (fuelOf k Kf m) round verdict (T0Of Kf m)
    hinitTape (fun q => fuelOf_length k Kf m hseed q) p

/-! ## 4.  The closing stroke with the fuel slots discharged -/

/-! ### 4a.  The interior form (`endgame_of_dominated_rounds_interior`)

Residual after this section: `hK` (the round-count estimate), the four programs, the size slot, the
threshold-top verdict property, and one `RunParts` per bracketed `(G, t)`.  `fuel`, `hfuel` and
`hfuelLen` are theorems now. -/

/-- **`d9f601e5` at the interior stroke, with the fuel wired in.** -/
theorem endgame_of_fuel_interior {σ : Type} [Coding σ]
    (dq : ℚ) (hdq : 0 < dq) (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (k : ℕ) (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hKf : Automatic.Poly (fun p : Pkg => Kf p.1.1 * m))
    (hseed : ∀ p : Pkg, Kf p.1.1 * m ≤ seedLen p ^ (2 ^ k))
    (hK : ∀ G : QuantumMaxCutEnergy.Input, QMCLeafB.FinalStroke.budgetRounds G dq m ≤ Kf G)
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict (fun G' _ => Kf G' * m) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict (fun G' _ => Kf G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G dq hdq rmax hrmax m hm1 (Kf G) (hK G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_of_dominated_rounds_interior dq hdq rmax hrmax m hm1 hhalve
    Kf hK init (fuelOf k Kf m) round verdict hinit (poly_fuelOf k Kf m hKf) hr hv sizes
    hsize hsize0 hinitTape (fun p => fuelOf_length k Kf m hseed p) htop hd

/-- **The `dq = 1` interior stroke with m1's factor**: no fuel, no round-count and no `dq`
hypothesis is left. -/
theorem endgame_of_fuel_interior_dq1 {σ : Type} [Coding σ]
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m) (hm8 : m ≤ 8)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (k : ℕ) (hk : 8 ≤ 2 ^ k)
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => Kbc m G' * m) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict (fun G' _ => Kbc m G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G 1 (by norm_num) rmax hrmax m hm1
          (Kbc m G) (budgetRounds_le_Kbc m G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_of_fuel_interior 1 (by norm_num) rmax hrmax m hm1 hhalve k (Kbc m)
    (poly_Kbc_mul m) (Kbc_mul_le_seed k m hm8 hk) (budgetRounds_le_Kbc m)
    init round verdict hinit hr hv sizes hsize hsize0 hinitTape htop hd

/-- **The interior stroke at m8's monomial**: the seed arithmetic is discharged, the round-count
estimate is the caller's. -/
theorem endgame_of_fuel_interior_monomial {σ : Type} [Coding σ]
    (dq : ℚ) (hdq : 0 < dq) (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (k d : ℕ) (hk : 2 ≤ k) (hd2 : d + 2 ≤ 2 ^ k) (hm8 : m ≤ 8)
    (hK : ∀ G : QuantumMaxCutEnergy.Input, QMCLeafB.FinalStroke.budgetRounds G dq m ≤ Kpow d m G)
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict (fun G' _ => Kpow d m G' * m) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict (fun G' _ => Kpow d m G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G dq hdq rmax hrmax m hm1
          (Kpow d m G) (hK G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_of_fuel_interior dq hdq rmax hrmax m hm1 hhalve k (Kpow d m)
    (poly_Kpow_mul d m) (Kpow_mul_le_seed k d m hk hd2 hm8) hK
    init round verdict hinit hr hv sizes hsize hsize0 hinitTape htop hd

/-! ### 4b.  The orbit form (`endgame_orbit_of_parts`) -/

/-- **`d9f601e5` at the orbit stroke, with the fuel wired in.**  `hsize`/`hsize0` are replaced by
the reachable-orbit envelope `horbit`, and the fuel is the one of §3. -/
theorem endgame_orbit_of_fuel {σ : Type} [Coding σ]
    (k : ℕ) (Kf : QuantumMaxCutEnergy.Input → ℕ) (m : ℕ)
    (hKf : Automatic.Poly (fun p : Pkg => Kf p.1.1 * m))
    (hseed : ∀ p : Pkg, Kf p.1.1 * m ≤ seedLen p ^ (2 ^ k))
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.VerdictSound.RunData
        (QMCLeafB.FinalStroke.loopBit init round verdict (fun G' _ => Kf G' * m)) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_orbit_of_parts init (fuelOf k Kf m) round verdict hinit
    (poly_fuelOf k Kf m hKf) hr hv sizes horbit (T0Of Kf m) hinitTape
    (fun p => fuelOf_length k Kf m hseed p) hd

/-! ### 4c.  The restated-loop form (`LoopRestate.solution_of_loop_bounded`) -/

/-- **`SolutionStatement` from the orbit envelope, with `hspec` and the fuel discharged.**  This is
`LoopRestate.solution_of_loop_bounded` with its `fuel` and `hspec` slots filled by §3 — the form the
integration can call once the bracket soundness `hsound` is available. -/
theorem solution_of_loop_bounded_fuel {σ : Type} [Coding σ]
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (k : ℕ) (Kf : QuantumMaxCutEnergy.Input → ℕ) (m : ℕ)
    (hKf : Automatic.Poly (fun p : Pkg => Kf p.1.1 * m))
    (hseed : ∀ p : Pkg, Kf p.1.1 * m ≤ seedLen p ^ (2 ^ k))
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hsound : QMCLeafB.FinishLine.SoundεOnBracket
      (QMCLeafB.FinalStroke.loopBit init round verdict (T0Of Kf m))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.LoopRestate.solution_of_loop_bounded init (fuelOf k Kf m) round verdict hinit
    (poly_fuelOf k Kf m hKf) hr hv sizes horbit
    (QMCLeafB.FinalStroke.loopBit init round verdict (T0Of Kf m))
    (fun p => hspecOf k Kf m hseed init round verdict hinitTape p) hsound

/-! ## 5.  Per-order parameters

`Check_halve_perG_m2` (§5 there) shows that the closing strokes' **constant** `rmax`/`m` slots are not
inhabitable: `hhalve` fails for every positive constant ceiling.  So the integration has to pass a
*per-order* parameter family `P : (G) → RunParams G` (`FinalStroke.endgame_of_parts`), and then the
fuel's round count is `(P G).K · (P G).m` — a function of the *order*, not a global `K·m`.  This
section is the fuel at that shape. -/

/-- **The padded fuel at a per-order round count `Kf G · mf G`.** -/
def fuelOfProd (k : ℕ) (Kf mf : QuantumMaxCutEnergy.Input → ℕ) (p : Pkg) : List Bool :=
  QMCLeafB.InitVerdict.fuelPad k (fun q : Pkg => Kf q.1.1 * mf q.1.1) p

/-- **Exact length at a per-order round count.** -/
theorem fuelOfProd_length (k : ℕ) (Kf mf : QuantumMaxCutEnergy.Input → ℕ)
    (hseed : ∀ p : Pkg, Kf p.1.1 * mf p.1.1 ≤ seedLen p ^ (2 ^ k)) (p : Pkg) :
    (fuelOfProd k Kf mf p).length = Kf p.1.1 * mf p.1.1 :=
  QMCLeafB.InitVerdict.fuelPad_length_of_le k _ p (by simpa [seedLen] using hseed p)

/-- **The per-order fuel is a program.** -/
theorem poly_fuelOfProd (k : ℕ) (Kf mf : QuantumMaxCutEnergy.Input → ℕ)
    (h : Automatic.Poly (fun p : Pkg => Kf p.1.1 * mf p.1.1)) :
    Automatic.Poly (fuelOfProd k Kf mf) :=
  QMCLeafB.InitVerdict.poly_fuelPad k (fun q : Pkg => Kf q.1.1 * mf q.1.1) h

/-- **`d9f601e5` at the split stroke, with per-order parameters and the fuel discharged.**  The loop's
round count is `(P G).K · (P G).m`, which is exactly what `RunParts.hverdict` compares the verdict bit
against. -/
theorem endgame_of_parts_fuel {σ : Type} [Coding σ]
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (k : ℕ)
    (hKf : Automatic.Poly (fun p : Pkg => (P p.1.1).K * (P p.1.1).m))
    (hseed : ∀ p : Pkg, (P p.1.1).K * (P p.1.1).m ≤ seedLen p ^ (2 ^ k))
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => (P G').K * (P G').m)) G t (P G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_of_parts init
    (fuelOfProd k (fun G => (P G).K) (fun G => (P G).m)) round verdict hinit
    (poly_fuelOfProd k _ _ hKf) hr hv sizes hsize hsize0
    (fun G' _ => (P G').K * (P G').m) hinitTape
    (fun p => fuelOfProd_length k _ _ hseed p) P hd

/-- **The orbit form, with per-order parameters and the fuel discharged.**  This is the variant the
integration should call: `hsize`/`hsize0` are replaced by the reachable-orbit envelope. -/
theorem endgame_orbit_of_parts_fuel {σ : Type} [Coding σ]
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (k : ℕ)
    (hKf : Automatic.Poly (fun p : Pkg => (P p.1.1).K * (P p.1.1).m))
    (hseed : ∀ p : Pkg, (P p.1.1).K * (P p.1.1).m ≤ seedLen p ^ (2 ^ k))
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.VerdictSound.RunData
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => (P G').K * (P G').m)) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_orbit_of_parts init
    (fuelOfProd k (fun G => (P G).K) (fun G => (P G).m)) round verdict hinit
    (poly_fuelOfProd k _ _ hKf) hr hv sizes horbit
    (fun G' _ => (P G').K * (P G').m) hinitTape
    (fun p => fuelOfProd_length k _ _ hseed p) hd

/-! ### 5b.  The per-order round factor

The natural per-order choice is m1's factor at the order's own halving time:
`Korder G = Kbc (mOrder G) G` with `mOrder G = 16·(G.n·G.n)² + 1` (m2's shallow time, incremented so
that it is a monomial with no `max`).  Both `Poly` facts and both seed bounds are proved here, so a
parameter family with these two fields gets the fuel's slots by `exact`. -/

/-- **The per-order halving time as a monomial**: `16·(n·n)² + 1`. -/
def mOrder (G : QuantumMaxCutEnergy.Input) : ℕ := 16 * (G.n * G.n) ^ 2 + 1

/-- **The per-order round factor**: m1's estimate at the order's own halving time. -/
def Korder (G : QuantumMaxCutEnergy.Input) : ℕ := Kbc (mOrder G) G

/-- **The seed bound for m1's factor at a per-order halving time.** -/
theorem Kbc_mul_seed_of_bound (k c : ℕ) (mf : QuantumMaxCutEnergy.Input → ℕ)
    (hm : ∀ p : Pkg, mf p.1.1 ≤ seedLen p ^ c) (hk : 6 + 2 * c ≤ 2 ^ k) (p : Pkg) :
    Kbc (mf p.1.1) p.1.1 * mf p.1.1 ≤ seedLen p ^ (2 ^ k) := by
  have hS1 : 1 ≤ seedLen p := seedLen_one_le p
  have hn : p.1.1.n + 1 ≤ seedLen p := by
    have h : p.1.1.n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
      QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
    have hS : seedLen p = 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length := seedLen_eq p
    omega
  have hA : (p.1.1.n + 1) ^ 2 ≤ seedLen p ^ 2 := Nat.pow_le_pow_left hn 2
  have hB : QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10
      ≤ seedLen p ^ 4 := bitCost_add_le_seed_pow p
  have hAB : (p.1.1.n + 1) ^ 2
        * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10)
      ≤ seedLen p ^ 6 := mul_le_pow hA hB
  have hmS : mf p.1.1 ≤ seedLen p ^ c := hm p
  have hmm : mf p.1.1 * mf p.1.1 ≤ seedLen p ^ (2 * c) := by
    have h := Nat.mul_le_mul hmS hmS
    rw [← pow_add] at h
    simpa [two_mul] using h
  have hEq : Kbc (mf p.1.1) p.1.1 * mf p.1.1
      = ((p.1.1.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10))
        * (mf p.1.1 * mf p.1.1) := by
    rw [Kbc_eq]; ring
  rw [hEq]
  calc ((p.1.1.n + 1) ^ 2
          * (QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + p.1.1.n + 10))
        * (mf p.1.1 * mf p.1.1)
      ≤ seedLen p ^ 6 * seedLen p ^ (2 * c) := Nat.mul_le_mul hAB hmm
    _ = seedLen p ^ (6 + 2 * c) := (pow_add _ _ _).symm
    _ ≤ seedLen p ^ (2 ^ k) := Nat.pow_le_pow_right hS1 hk

/-- **`mOrder` is a program.** -/
theorem poly_mOrder : Automatic.Poly (fun p : Pkg => mOrder p.1.1) := by
  have hnn : Automatic.Poly (fun p : Pkg => p.1.1.n * p.1.1.n) :=
    poly_nat_mul QMCLeafB.InitVerdict.poly_nIdx QMCLeafB.InitVerdict.poly_nIdx
  have hsq : Automatic.Poly (fun p : Pkg => (p.1.1.n * p.1.1.n) ^ 2) :=
    Poly.comp (f := fun y : ℕ => y ^ 2) (g := fun p : Pkg => p.1.1.n * p.1.1.n)
      (QMCLeafB.InitVerdict.poly_pow 2) hnn
  exact poly_nat_add
    (poly_nat_mul (Automatic.Poly.const (β := ℕ) 16) hsq)
    (Automatic.Poly.const (β := ℕ) 1)

/-- **`mOrder G ≤ S^7`** — the per-order halving time is under the seventh power of the padded seed. -/
theorem mOrder_le_seed (p : Pkg) : mOrder p.1.1 ≤ seedLen p ^ 7 := by
  have hS8 : 8 ≤ seedLen p := seedLen_ge_eight p
  have hS1 : 1 ≤ seedLen p := seedLen_one_le p
  have hS2 : 2 ≤ seedLen p := by omega
  have hn : p.1.1.n + 1 ≤ seedLen p := by
    have h : p.1.1.n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
      QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
    have hS : seedLen p = 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length := seedLen_eq p
    omega
  have hn1 : p.1.1.n ≤ seedLen p := by omega
  have hn2 : p.1.1.n * p.1.1.n ≤ seedLen p ^ 2 := by
    calc p.1.1.n * p.1.1.n ≤ seedLen p * seedLen p := Nat.mul_le_mul hn1 hn1
      _ = seedLen p ^ 2 := (pow_two _).symm
  have h4 : (p.1.1.n * p.1.1.n) ^ 2 ≤ seedLen p ^ 4 := by
    have h := Nat.pow_le_pow_left hn2 2
    have h2 : (seedLen p ^ 2) ^ 2 = seedLen p ^ 4 := by ring
    rwa [h2] at h
  have h16 : (16 : ℕ) ≤ seedLen p ^ 2 := by
    have h64 : (16 : ℕ) ≤ 8 ^ 2 := by norm_num
    exact le_trans h64 (Nat.pow_le_pow_left hS8 2)
  have hA : 16 * (p.1.1.n * p.1.1.n) ^ 2 ≤ seedLen p ^ 6 := mul_le_pow h16 h4
  have h1' : (1 : ℕ) ≤ seedLen p ^ 6 := Nat.one_le_pow _ _ hS1
  calc mOrder p.1.1 = 16 * (p.1.1.n * p.1.1.n) ^ 2 + 1 := rfl
    _ ≤ seedLen p ^ 6 + seedLen p ^ 6 := Nat.add_le_add hA h1'
    _ = 2 * seedLen p ^ 6 := by ring
    _ ≤ seedLen p * seedLen p ^ 6 := Nat.mul_le_mul_right _ hS2
    _ = seedLen p ^ 7 := (pow_succ' _ _).symm

/-- **`Korder G · mOrder G` is a program** — the per-order round count of the fuel. -/
theorem poly_Korder_mul :
    Automatic.Poly (fun p : Pkg => Korder p.1.1 * mOrder p.1.1) := by
  have hcore : Automatic.Poly (fun p : Pkg =>
      (p.1.1.n + 1) ^ 2
        * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1) + (p.1.1.n + 9))) :=
    poly_nat_mul (QMCLeafB.InitVerdict.poly_succPow 2)
      (poly_nat_add QMCLeafB.FuelSlot.poly_bitCost_succ
        (poly_nat_add QMCLeafB.InitVerdict.poly_nIdx
          (Automatic.Poly.const (β := ℕ) 9)))
  exact poly_nat_mul (poly_nat_mul poly_mOrder hcore) poly_mOrder

/-- **The seed bound at the per-order factor**: `Korder G · mOrder G ≤ S^(2^k)` for `2^k ≥ 20`. -/
theorem Korder_mul_le_seed (k : ℕ) (hk : 20 ≤ 2 ^ k) (p : Pkg) :
    Korder p.1.1 * mOrder p.1.1 ≤ seedLen p ^ (2 ^ k) :=
  Kbc_mul_seed_of_bound k 7 mOrder (fun q => mOrder_le_seed q) (by omega) p

/-! ### 5c.  The halving inequality is monotone in the halving time

Moving the halving time from m2's `mHalve N = max 1 (16N²)` to the monomial `mOrder` above only makes
the inequality easier, because the contraction factor is at most `1` in every run that satisfies the
inequality at all. -/

/-- **`x^a ≤ 1/2` survives an increase of the exponent** (for `x ≥ 0`). -/
theorem hhalve_mono {x : ℝ} (hx : 0 ≤ x) {a b : ℕ} (hab : a ≤ b) (h : x ^ a ≤ 1 / 2) :
    x ^ b ≤ 1 / 2 := by
  rcases le_total x 1 with hx1 | hx1
  · exact le_trans (pow_le_pow_of_le_one hx hx1 hab) h
  · exfalso
    have h1 : (1 : ℝ) ≤ x ^ a := one_le_pow₀ hx1
    linarith

/-! ## 6.  A per-order parameter family the fuel hypotheses are *theorems* at

`Check_halve_perG_m2` builds the parameter family at the halving time `mHalve N = max 1 (16N²)`.  The
fuel cannot use that `max` directly (a `Nat.max` is not one of the `Automatic.Poly` combinators), so
this section uses the monomial `mOrder = 16N² + 1 ≥ mHalve N` instead: `hhalve` transfers by
`hhalve_mono`, `hbudget` by m1's estimate (`budgetRounds_le_Kbc`), and then §5b's two facts are
exactly the fuel hypotheses.  What is left of the leaf at the end (`solution_of_run`) is the loop's
programs, the orbit size ledger, `init`'s tape-freeness and one run bundle per bracketed `(G, t)`. -/

theorem one_le_mOrder (G : QuantumMaxCutEnergy.Input) : 1 ≤ mOrder G := by
  unfold mOrder; omega

/-- **The monomial halving time dominates m2's `max`-halving time.** -/
theorem mHalve_le_mOrder (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.HalvePerG.mHalve (G.n * G.n) ≤ mOrder G := by
  unfold QMCLeafB.HalvePerG.mHalve QMCLeafB.RundataHalving.mOf mOrder
  rcases Nat.eq_zero_or_pos (G.n * G.n) with ht | ht
  · rw [ht]; simp
  · have h1 : (G.n * G.n) ≤ (G.n * G.n) * (G.n * G.n) := by
      calc (G.n * G.n) = (G.n * G.n) * 1 := by ring
        _ ≤ (G.n * G.n) * (G.n * G.n) := Nat.mul_le_mul_left _ ht
    have hk : 1 ≤ 16 * (G.n * G.n * (G.n * G.n)) := by omega
    have hmax : max 1 (16 * (G.n * G.n * (G.n * G.n)))
        = 16 * (G.n * G.n * (G.n * G.n)) := max_eq_right hk
    rw [hmax]
    have h3 : 16 * (G.n * G.n * (G.n * G.n)) = 16 * (G.n * G.n) ^ 2 := by ring
    omega

/-- **The halving inequality at the monomial halving time.** -/
theorem hhalve_mOrder (G : QuantumMaxCutEnergy.Input) :
    (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n)
      ((QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) : ℚ) : ℝ)))⁻¹ ^ mOrder G ≤ 1 / 2 :=
  hhalve_mono (inv_nonneg.mpr (Real.sqrt_nonneg _)) (mHalve_le_mOrder G)
    (QMCLeafB.HalvePerG.hhalve_perG (G.n * G.n))

/-- **The per-order parameter family**: shallow ceiling `1/(4N)`, halving time `16N² + 1`, tolerance
`dq = 1`, and m1's round factor at the order's own halving time. -/
noncomputable def paramsFuel (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.FinalStroke.runParamsOfK G 1 (by norm_num)
    (QMCLeafB.RundataHalving.rmaxOf (G.n * G.n))
    (QMCLeafB.HalvePerG.rmaxOf_nonneg (G.n * G.n))
    (mOrder G) (one_le_mOrder G) (Korder G) (budgetRounds_le_Kbc (mOrder G) G)
    (hhalve_mOrder G)

@[simp] theorem paramsFuel_K (G : QuantumMaxCutEnergy.Input) : (paramsFuel G).K = Korder G := rfl

@[simp] theorem paramsFuel_m (G : QuantumMaxCutEnergy.Input) : (paramsFuel G).m = mOrder G := rfl

@[simp] theorem paramsFuel_dq (G : QuantumMaxCutEnergy.Input) : (paramsFuel G).dq = 1 := rfl

@[simp] theorem paramsFuel_rmax (G : QuantumMaxCutEnergy.Input) :
    (paramsFuel G).rmax = QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) := rfl

/-- **`d9f601e5` from the run brick at `paramsFuel`.**  Every numeric slot of the closing stroke —
`K`, `m`, `dq`, `cAq`, `rmax`, `hdq`, `hcAq`, `hAsum`, `hrmax`, `hhalve`, `hbudget`, the fuel program
and its exact length — is discharged here.  The residuals are exactly: the loop's `init`/`round`/
`verdict` programs, the orbit size ledger, `init`'s tape-freeness, and the run bundle `hd` at
`paramsFuel`. -/
theorem solution_of_run {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.VerdictSound.RunData
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => (paramsFuel G').K * (paramsFuel G').m)) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_orbit_of_parts_fuel paramsFuel k poly_Korder_mul (Korder_mul_le_seed k hk)
    init round verdict hinit hr hv sizes horbit hinitTape hd

/-! ### 6b.  The interior form: the run brick's actual target

`VerdictSound.soundEpsOnBracket_of_runData_interior` needs the run bundle only on the *open*
interior `[-Rq G, -Rq G/40000)`, plus the verdict bit `true` on the closed top slice.  This is the
statement the `RunParts` brick targets, so it is the one to combine with §5/§6. -/


/-- **`SolutionStatement` from `RunParts` on the interior, at `paramsFuel`.**  All numeric slots and
the fuel are discharged; the residuals are the three loop programs, the orbit size ledger, `init`'s
tape-freeness, the top-slice verdict (`htop`) and one `RunParts` per interior `(G, t)`. -/
theorem solution_of_runParts_interior {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => (paramsFuel G').K * (paramsFuel G').m) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => (paramsFuel G').K * (paramsFuel G').m)) G t (paramsFuel G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.LoopRestate.solution_of_loop_bounded init
    (fuelOfProd k (fun G => (paramsFuel G).K) (fun G => (paramsFuel G).m))
    round verdict hinit
    (poly_fuelOfProd k _ _ poly_Korder_mul) hr hv sizes horbit
    (QMCLeafB.FinalStroke.loopBit init round verdict
      (fun G' _ => (paramsFuel G').K * (paramsFuel G').m))
    (fun p => QMCLeafB.FinalStroke.hspec_of_tape_free init _ round verdict
      (fun G' _ => (paramsFuel G').K * (paramsFuel G').m) hinitTape
      (fun q => fuelOfProd_length k _ _ (Korder_mul_le_seed k hk) q) p)
    (QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData_interior
      (QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => (paramsFuel G').K * (paramsFuel G').m)) htop
      (fun G t h2 hlo hlt => (hd G t h2 hlo hlt).toRunData))

/-- **The same, at an arbitrary per-order parameter family.**  If the `RunParts` brick prefers a
different `P : (G) → RunParams G` (m2's `paramsK`, say), only these two facts about its round count
`(P G).K · (P G).m` are needed. -/
theorem solution_of_runParts_interior_of_params {σ : Type} [Coding σ]
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (k : ℕ)
    (hKf : Automatic.Poly (fun p : Pkg => (P p.1.1).K * (P p.1.1).m))
    (hseed : ∀ p : Pkg, (P p.1.1).K * (P p.1.1).m ≤ seedLen p ^ (2 ^ k))
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
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
    (fuelOfProd k (fun G => (P G).K) (fun G => (P G).m))
    round verdict hinit (poly_fuelOfProd k _ _ hKf) hr hv sizes horbit
    (QMCLeafB.FinalStroke.loopBit init round verdict
      (fun G' _ => (P G').K * (P G').m))
    (fun p => QMCLeafB.FinalStroke.hspec_of_tape_free init _ round verdict
      (fun G' _ => (P G').K * (P G').m) hinitTape
      (fun q => fuelOfProd_length k _ _ hseed q) p)
    (QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData_interior
      (QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => (P G').K * (P G').m)) htop
      (fun G t h2 hlo hlt => (hd G t h2 hlo hlt).toRunData))

/-! ### 6c.  The same at m2's own family (`paramsK`, halving time `max 1 (16N²)`)

`HalvePerG.paramsK` is the family `Check_halve_perG_m2` builds, and the closest one to the run brick.
Its halving time is `mHalve N = max 1 (16N²)`, so the fuel needs `Poly` for `Nat.max` — which the
library has, via `Poly.nat_le` and `Poly.ite` (§6c.1).  With that, the two fuel facts hold at m2's
family too, so the `RunParts` brick can pick either. -/

/-- **`Nat.max` of two programs is a program.** -/
theorem poly_nat_max {f g : Pkg → ℕ} (hf : Automatic.Poly f) (hg : Automatic.Poly g) :
    Automatic.Poly (fun p => max (f p) (g p)) := by
  have hp : Automatic.Poly (fun p : Pkg => decide (f p ≤ g p)) :=
    Poly.comp (f := fun x : ℕ × ℕ => decide (x.1 ≤ x.2)) (g := fun p : Pkg => (f p, g p))
      Poly.nat_le (Poly.pair hf hg)
  have h : Automatic.Poly (fun p : Pkg => if decide (f p ≤ g p) then g p else f p) :=
    Poly.ite hp hg hf
  refine QMCLeafB.FinishLine.poly_of_pointwise h (fun p => ?_)
  rw [Nat.max_def]
  by_cases hle : f p ≤ g p
  · simp [hle]
  · simp [hle]

/-- **m2's halving time is a program.** -/
theorem poly_mHalve :
    Automatic.Poly (fun p : Pkg => QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) := by
  have hnn : Automatic.Poly (fun p : Pkg => p.1.1.n * p.1.1.n) :=
    poly_nat_mul QMCLeafB.InitVerdict.poly_nIdx QMCLeafB.InitVerdict.poly_nIdx
  have h16 : Automatic.Poly (fun p : Pkg => 16 * ((p.1.1.n * p.1.1.n) * (p.1.1.n * p.1.1.n))) :=
    poly_nat_mul (Automatic.Poly.const (β := ℕ) 16) (poly_nat_mul hnn hnn)
  exact poly_nat_max (Automatic.Poly.const (β := ℕ) 1) h16

/-- **`mHalve` is under the seventh power of the padded seed.** -/
theorem mHalve_le_seed (p : Pkg) :
    QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n) ≤ seedLen p ^ 7 := by
  have hS8 : 8 ≤ seedLen p := seedLen_ge_eight p
  have hS1 : 1 ≤ seedLen p := seedLen_one_le p
  have hn : p.1.1.n ≤ seedLen p := by
    have h : p.1.1.n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
      QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
    have hS : seedLen p = 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length := seedLen_eq p
    omega
  have hn2 : p.1.1.n * p.1.1.n ≤ seedLen p ^ 2 := by
    calc p.1.1.n * p.1.1.n ≤ seedLen p * seedLen p := Nat.mul_le_mul hn hn
      _ = seedLen p ^ 2 := (pow_two _).symm
  have hNN : (p.1.1.n * p.1.1.n) * (p.1.1.n * p.1.1.n) ≤ seedLen p ^ 4 := by
    have h := Nat.mul_le_mul hn2 hn2
    rw [← pow_add] at h
    simpa [show 2 + 2 = 4 from rfl] using h
  have h16 : (16 : ℕ) ≤ seedLen p ^ 2 := by
    have h64 : (16 : ℕ) ≤ 8 ^ 2 := by norm_num
    exact le_trans h64 (Nat.pow_le_pow_left hS8 2)
  have hB : 16 * ((p.1.1.n * p.1.1.n) * (p.1.1.n * p.1.1.n)) ≤ seedLen p ^ 6 :=
    mul_le_pow h16 hNN
  have hB7 : 16 * ((p.1.1.n * p.1.1.n) * (p.1.1.n * p.1.1.n)) ≤ seedLen p ^ 7 :=
    le_trans hB (Nat.pow_le_pow_right hS1 (by omega))
  have hone : (1 : ℕ) ≤ seedLen p ^ 7 := Nat.one_le_pow _ _ hS1
  unfold QMCLeafB.HalvePerG.mHalve QMCLeafB.RundataHalving.mOf
  exact max_le hone hB7

/-- **`Kbc` at m2's halving time is a program times the halving time.** -/
theorem poly_Kbc_mHalve_mul :
    Automatic.Poly (fun p : Pkg =>
      Kbc (QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) p.1.1
        * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) := by
  have hcore : Automatic.Poly (fun p : Pkg =>
      (p.1.1.n + 1) ^ 2
        * ((QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq p.1.1) + 1) + (p.1.1.n + 9))) :=
    poly_nat_mul (QMCLeafB.InitVerdict.poly_succPow 2)
      (poly_nat_add QMCLeafB.FuelSlot.poly_bitCost_succ
        (poly_nat_add QMCLeafB.InitVerdict.poly_nIdx
          (Automatic.Poly.const (β := ℕ) 9)))
  exact poly_nat_mul (poly_nat_mul poly_mHalve hcore) poly_mHalve

/-- **The seed bound at m2's halving time**: `Kbc (mHalve N) G · mHalve N ≤ S^(2^k)` for `2^k ≥ 20`. -/
theorem Kbc_mHalve_le_seed (k : ℕ) (hk : 20 ≤ 2 ^ k) (p : Pkg) :
    Kbc (QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) p.1.1
        * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n) ≤ seedLen p ^ (2 ^ k) :=
  Kbc_mul_seed_of_bound k 7
    (fun G => QMCLeafB.HalvePerG.mHalve (G.n * G.n))
    (fun q => mHalve_le_seed q) (by omega) p

/-- **m2's parameter family at m1's round factor and `dq = 1`.** -/
noncomputable def paramsHalve (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.HalvePerG.paramsK G 1 (by norm_num)
    (Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
    (budgetRounds_le_Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)

@[simp] theorem paramsHalve_K (G : QuantumMaxCutEnergy.Input) :
    (paramsHalve G).K = Kbc (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G := rfl

@[simp] theorem paramsHalve_m (G : QuantumMaxCutEnergy.Input) :
    (paramsHalve G).m = QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

/-- **`SolutionStatement` from the interior run brick at m2's family.**  Same residuals as
`solution_of_runParts_interior`, with the run brick's parameters instead of `paramsFuel`'s. -/
theorem solution_of_runParts_interior_halve {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => (paramsHalve G').K * (paramsHalve G').m) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => (paramsHalve G').K * (paramsHalve G').m)) G t (paramsHalve G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_runParts_interior_of_params paramsHalve k poly_Kbc_mHalve_mul
    (Kbc_mHalve_le_seed k hk) init round verdict hinit hr hv sizes horbit hinitTape htop hd

/-! ### 6d.  The general monomial family: any tolerance, any monomial round factor

The run brick fixes the tolerance `dq` (its margin analysis needs a small one) and a round factor `K`
above `budgetRounds`.  The fuel only needs `K · m` to be a **monomial in `n` and `bitCost (Rq G)`**,
because that is what `Automatic.Poly` can compute.  This section provides exactly that shape: the
family `paramsMono dq C e` has `K = C·(n+1)^e + 1` and `m = mHalve (n·n)`, and the fuel facts are
theorems as soon as `C ≤ 8^c` and `2^k ≥ c + e + 8` — no constraint on `dq` beyond `0 < dq`, and the
budget inequality is the caller's one hypothesis. -/

/-- **The monomial round factor** `C·(n+1)^e + 1`. -/
def Kmono (C e : ℕ) (G : QuantumMaxCutEnergy.Input) : ℕ := C * (G.n + 1) ^ e + 1

/-- **`Kmono C e G · mHalve (n·n)` is a program.** -/
theorem poly_Kmono_mHalve_mul (C e : ℕ) :
    Automatic.Poly (fun p : Pkg =>
      Kmono C e p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)) := by
  have hpow : Automatic.Poly (fun p : Pkg => C * (p.1.1.n + 1) ^ e) :=
    poly_nat_mul (Automatic.Poly.const (β := ℕ) C) (QMCLeafB.InitVerdict.poly_succPow e)
  exact poly_nat_mul (poly_nat_add hpow (Automatic.Poly.const (β := ℕ) 1)) poly_mHalve

/-- **The seed bound for the monomial family**: `Kmono C e G · mHalve (n·n) ≤ S^(2^k)` as soon as
`C ≤ 8^c` and `2^k ≥ c + e + 8`. -/
theorem Kmono_mHalve_le_seed (k C e c : ℕ) (hC : C ≤ 8 ^ c) (hk : c + e + 8 ≤ 2 ^ k) (p : Pkg) :
    Kmono C e p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n) ≤ seedLen p ^ (2 ^ k) := by
  have hS8 : 8 ≤ seedLen p := seedLen_ge_eight p
  have hS1 : 1 ≤ seedLen p := seedLen_one_le p
  have hS2 : 2 ≤ seedLen p := by omega
  have hn : p.1.1.n + 1 ≤ seedLen p := by
    have h : p.1.1.n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
      QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
    have hS : seedLen p = 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length := seedLen_eq p
    omega
  have hCc : C ≤ seedLen p ^ c := le_trans hC (Nat.pow_le_pow_left hS8 c)
  have hCe : C * (p.1.1.n + 1) ^ e ≤ seedLen p ^ (c + e) :=
    mul_le_pow hCc (Nat.pow_le_pow_left hn e)
  have hKle : Kmono C e p.1.1 ≤ seedLen p ^ (c + e + 1) := by
    have h1 : (1 : ℕ) ≤ seedLen p ^ (c + e) := Nat.one_le_pow _ _ hS1
    have hsum : C * (p.1.1.n + 1) ^ e + 1 ≤ seedLen p ^ (c + e) + seedLen p ^ (c + e) :=
      Nat.add_le_add hCe h1
    have hstep : seedLen p ^ (c + e) + seedLen p ^ (c + e) ≤ seedLen p ^ (c + e + 1) :=
      add_le_pow hS2 le_rfl le_rfl
    unfold Kmono
    exact le_trans hsum hstep
  have hmH : QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n) ≤ seedLen p ^ 7 := mHalve_le_seed p
  calc Kmono C e p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
      ≤ seedLen p ^ (c + e + 1) * seedLen p ^ 7 := Nat.mul_le_mul hKle hmH
    _ = seedLen p ^ (c + e + 1 + 7) := (pow_add _ _ _).symm
    _ ≤ seedLen p ^ (2 ^ k) := Nat.pow_le_pow_right hS1 (by omega)

/-- **The monomial parameter family**: tolerance `dq` of the caller's choosing, halving time
`mHalve (n·n)`, round factor `C·(n+1)^e + 1` above `budgetRounds`. -/
noncomputable def paramsMono (dq : ℚ) (hdq : 0 < dq) (C e : ℕ) (hC : 1 ≤ C)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G dq (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kmono C e G) :
    (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G :=
  fun G =>
    QMCLeafB.FinalStroke.runParamsOfK G dq hdq
      (QMCLeafB.RundataHalving.rmaxOf (G.n * G.n))
      (QMCLeafB.HalvePerG.rmaxOf_nonneg (G.n * G.n))
      (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) (QMCLeafB.HalvePerG.one_le_mHalve _)
      (Kmono C e G) (hK G) (QMCLeafB.HalvePerG.hhalve_perG (G.n * G.n))

@[simp] theorem paramsMono_K (dq : ℚ) (hdq : 0 < dq) (C e : ℕ) (hC : 1 ≤ C)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G dq (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kmono C e G)
    (G : QuantumMaxCutEnergy.Input) :
    (paramsMono dq hdq C e hC hK G).K = Kmono C e G := rfl

@[simp] theorem paramsMono_m (dq : ℚ) (hdq : 0 < dq) (C e : ℕ) (hC : 1 ≤ C)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G dq (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kmono C e G)
    (G : QuantumMaxCutEnergy.Input) :
    (paramsMono dq hdq C e hC hK G).m = QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

/-- **`SolutionStatement` from the interior run brick at the monomial family.**  The run brick picks
the tolerance `dq` and the monomial `C·(n+1)^e`; the fuel, the halving inequality and the budget
target are discharged here. -/
theorem solution_of_runParts_interior_mono {σ : Type} [Coding σ]
    (dq : ℚ) (hdq : 0 < dq) (C e c k : ℕ) (hC1 : 1 ≤ C) (hCc : C ≤ 8 ^ c)
    (hk : c + e + 8 ≤ 2 ^ k)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G dq (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kmono C e G)
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => (paramsMono dq hdq C e hC1 hK G').K
          * (paramsMono dq hdq C e hC1 hK G').m) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => (paramsMono dq hdq C e hC1 hK G').K
            * (paramsMono dq hdq C e hC1 hK G').m)) G t
        (paramsMono dq hdq C e hC1 hK G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_runParts_interior_of_params (paramsMono dq hdq C e hC1 hK) k
    (poly_Kmono_mHalve_mul C e) (Kmono_mHalve_le_seed k C e c hCc hk)
    init round verdict hinit hr hv sizes horbit hinitTape htop hd

/-- **The monomial family at a per-order tolerance.**  The run brick's tolerance is `dqShallow G`, an
order-dependent rational, so the family must allow that; nothing in the fuel sees `dq`, and the budget
inequality is again the caller's single hypothesis.  This is the shape m5's `runParamsShallow` has,
with the `Nat.clog` round factor replaced by a monomial. -/
noncomputable def paramsMonoF (dqf : QuantumMaxCutEnergy.Input → ℚ) (hdqf : ∀ G, 0 < dqf G) (C e : ℕ)
    (hC : 1 ≤ C)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (dqf G) (QMCLeafB.HalvePerG.mHalve (G.n * G.n))
        ≤ Kmono C e G) :
    (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G :=
  fun G =>
    QMCLeafB.FinalStroke.runParamsOfK G (dqf G) (hdqf G)
      (QMCLeafB.RundataHalving.rmaxOf (G.n * G.n))
      (QMCLeafB.HalvePerG.rmaxOf_nonneg (G.n * G.n))
      (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) (QMCLeafB.HalvePerG.one_le_mHalve _)
      (Kmono C e G) (hK G) (QMCLeafB.HalvePerG.hhalve_perG (G.n * G.n))

@[simp] theorem paramsMonoF_K (dqf : QuantumMaxCutEnergy.Input → ℚ) (hdqf : ∀ G, 0 < dqf G)
    (C e : ℕ) (hC : 1 ≤ C)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (dqf G) (QMCLeafB.HalvePerG.mHalve (G.n * G.n))
        ≤ Kmono C e G) (G : QuantumMaxCutEnergy.Input) :
    (paramsMonoF dqf hdqf C e hC hK G).K = Kmono C e G := rfl

@[simp] theorem paramsMonoF_m (dqf : QuantumMaxCutEnergy.Input → ℚ) (hdqf : ∀ G, 0 < dqf G)
    (C e : ℕ) (hC : 1 ≤ C)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (dqf G) (QMCLeafB.HalvePerG.mHalve (G.n * G.n))
        ≤ Kmono C e G) (G : QuantumMaxCutEnergy.Input) :
    (paramsMonoF dqf hdqf C e hC hK G).m = QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

/-- **`SolutionStatement` from the interior run brick at a per-order tolerance.**  This is the widest
form of the fuel wire: the run brick chooses its own tolerance `dqf G` and its own monomial
`C·(n+1)^e`; what it must supply is `budgetRounds ≤ Kmono C e G` and the `RunParts` bundle at
`paramsMonoF`. -/
theorem solution_of_runParts_interior_monoF {σ : Type} [Coding σ]
    (dqf : QuantumMaxCutEnergy.Input → ℚ) (hdqf : ∀ G, 0 < dqf G)
    (C e c k : ℕ) (hC1 : 1 ≤ C) (hCc : C ≤ 8 ^ c) (hk : c + e + 8 ≤ 2 ^ k)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (dqf G) (QMCLeafB.HalvePerG.mHalve (G.n * G.n))
        ≤ Kmono C e G)
    (init : Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : Pkg, init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => (paramsMonoF dqf hdqf C e hC1 hK G').K
          * (paramsMonoF dqf hdqf C e hC1 hK G').m) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => (paramsMonoF dqf hdqf C e hC1 hK G').K
            * (paramsMonoF dqf hdqf C e hC1 hK G').m)) G t
        (paramsMonoF dqf hdqf C e hC1 hK G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_runParts_interior_of_params (paramsMonoF dqf hdqf C e hC1 hK) k
    (poly_Kmono_mHalve_mul C e) (Kmono_mHalve_le_seed k C e c hCc hk)
    init round verdict hinit hr hv sizes horbit hinitTape htop hd

end QMCLeafB.FuelWire

/-! ## Axiom audit -/

#print axioms QMCLeafB.FuelWire.seedLen_eq
#print axioms QMCLeafB.FuelWire.mul_le_pow
#print axioms QMCLeafB.FuelWire.poly_nat_mul
#print axioms QMCLeafB.FuelWire.poly_nat_add
#print axioms QMCLeafB.FuelWire.Kbc_eq
#print axioms QMCLeafB.FuelWire.budgetRounds_le_Kbc
#print axioms QMCLeafB.FuelWire.poly_Kbc_mul
#print axioms QMCLeafB.FuelWire.bitCost_add_le_seed_pow
#print axioms QMCLeafB.FuelWire.Kbc_mul_le_seed
#print axioms QMCLeafB.FuelWire.poly_Kpow_mul
#print axioms QMCLeafB.FuelWire.Kpow_mul_le_seed
#print axioms QMCLeafB.FuelWire.fuelOf_length
#print axioms QMCLeafB.FuelWire.poly_fuelOf
#print axioms QMCLeafB.FuelWire.fuelOf_length_tape_free
#print axioms QMCLeafB.FuelWire.hspecOf
#print axioms QMCLeafB.FuelWire.endgame_of_fuel_interior
#print axioms QMCLeafB.FuelWire.endgame_of_fuel_interior_dq1
#print axioms QMCLeafB.FuelWire.endgame_of_fuel_interior_monomial
#print axioms QMCLeafB.FuelWire.endgame_orbit_of_fuel
#print axioms QMCLeafB.FuelWire.solution_of_loop_bounded_fuel
#print axioms QMCLeafB.FuelWire.add_le_pow
#print axioms QMCLeafB.FuelWire.Kpow_mul_le_seed_gen
#print axioms QMCLeafB.FuelWire.fuelOfProd_length
#print axioms QMCLeafB.FuelWire.poly_fuelOfProd
#print axioms QMCLeafB.FuelWire.endgame_of_parts_fuel
#print axioms QMCLeafB.FuelWire.endgame_orbit_of_parts_fuel
#print axioms QMCLeafB.FuelWire.Kbc_mul_seed_of_bound
#print axioms QMCLeafB.FuelWire.poly_mOrder
#print axioms QMCLeafB.FuelWire.mOrder_le_seed
#print axioms QMCLeafB.FuelWire.poly_Korder_mul
#print axioms QMCLeafB.FuelWire.Korder_mul_le_seed
#print axioms QMCLeafB.FuelWire.hhalve_mono
#print axioms QMCLeafB.FuelWire.one_le_mOrder
#print axioms QMCLeafB.FuelWire.mHalve_le_mOrder
#print axioms QMCLeafB.FuelWire.hhalve_mOrder
#print axioms QMCLeafB.FuelWire.paramsFuel_K
#print axioms QMCLeafB.FuelWire.paramsFuel_m
#print axioms QMCLeafB.FuelWire.solution_of_run
#print axioms QMCLeafB.FuelWire.solution_of_runParts_interior
#print axioms QMCLeafB.FuelWire.solution_of_runParts_interior_of_params
#print axioms QMCLeafB.FuelWire.poly_nat_max
#print axioms QMCLeafB.FuelWire.poly_mHalve
#print axioms QMCLeafB.FuelWire.mHalve_le_seed
#print axioms QMCLeafB.FuelWire.poly_Kbc_mHalve_mul
#print axioms QMCLeafB.FuelWire.Kbc_mHalve_le_seed
#print axioms QMCLeafB.FuelWire.solution_of_runParts_interior_halve
#print axioms QMCLeafB.FuelWire.poly_Kmono_mHalve_mul
#print axioms QMCLeafB.FuelWire.Kmono_mHalve_le_seed
#print axioms QMCLeafB.FuelWire.paramsMono_K
#print axioms QMCLeafB.FuelWire.solution_of_runParts_interior_mono
#print axioms QMCLeafB.FuelWire.paramsMonoF_K
#print axioms QMCLeafB.FuelWire.solution_of_runParts_interior_monoF


