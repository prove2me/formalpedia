-- Prove2me | Definitions.Def_QMCLeafB_initdq_m1
-- name    : QMCLeafB_initdq_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:53:22.857713+00:00
-- url     : https://prove2.me/theorems/afb3b325-1974-4a8a-8b08-79c305cae21b
-- title:
--   QMCLeafB initdq_m1
-- statement:
--   # leaf B phase 16 — brick 1 `init-dqshallow` (swarm `smw1ez4a9`, member m1, direction d4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_RStInit
import Definitions.Def_QMCLeafB_htop_init_m7
import Definitions.Def_QMCLeafB_runparams_shallow_m5
import Definitions.Def_QMCLeafB_roundcount_estimate_m1
/-
# leaf B phase 16 — brick 1 `init-dqshallow` (swarm `smw1ez4a9`, member m1, direction d4)

The campaign's oracle tolerance is **not** `dq = 1`.  `QMCLeafB.RundataParams.dqShallow_budget`
records why: `RunData.hcert` needs

    roundCost (wMatrixQ G) (3·dq/4) + dq/2 - ε ≤ ε,      ε = Rq G / 40000,

and `roundCost (wMatrixQ G) ν = (1+ν)(2ν+ν²)·Σ|A|`; at `ν = 3/4` that is `(231/64)·Rq G = 3.61·Rq G`,
which is `> 2ε = Rq G/20000` by a factor of `72000`: **no** `ok` round can be certified at slack 1.
The engine must therefore run at

    dqShallow G = (Rq G / 40000) / (9·Rq G + 1),

the largest tolerance for which the rounding still fits (`dqShallow_budget`).

`QMCLeafB.RStInit.init0` (`Check_initpoly_m1`) builds the initial round state at `mu = MOf n =
2n² + 2·1²`, and `RunParts.hwit`/`hcut` name the matrix `initShapeOf (n·n) (2n² + 2·P.dq²)` at the
run's *own* `P.dq`.  So the state's `mu` register and the initial primal code are pinned to `dq`: the
whole init brick has to be rebuilt at `dqShallow`.

This file does that, and nothing else:

* §1 `dqOf`, `muOf G = 2·n² + 2·dqOf G²`; `0 < dqOf G`, `dqOf G ≤ 1`, `muOf` positive and `≥ 1` at
  `2 ≤ G.n` (the range on which `hd` is ever read), `muOf G ≤ (2n+2)²`.
* §2 `init0` at `muOf`, and the readings a `RunParts` proof needs: `stN`, `stA` is the row-major
  code of `wMatQ G`, `stX` is the row-major code of `initShapeOf (n·n) (2n²+2 dqOf²)` — in
  `RunParts`' own spelling — `stT`, `stMu`, `stD`, empty records, `init_normalised`.
* §3 `Poly init0` (the tolerance is a `Poly` function of the request: `Rq_poly_req`, one division
  and one branch).
* §4 the state ignores the random tape (`hinitTape`).
* §5 `fvR (init0 p) = 0` — the number the `htop` brick needs — by the generic
  diagonal-complementary lemma of `Check_htop_init_m7`; it holds at *any* `mu`, which is why the
  rebuilt init does not disturb the `htop` route.
* §6 the round's clip is inert on the initial shape at `2 ≤ G.n`.
* §7 the fuel: §7a `1/dqOf G ≤ 2^(2·bitCost (Rq G) + 26)` — the only place the tolerance enters the
  *count*, and it is a statement about the bit size of `Rq G`, not about `n`; §7b
  `budgetRounds G (dqOf G) m ≤ C·m·(n+1)³·(L+1)³`, a monomial in the dimension and the input length
  `L = (encodeInput G).length`; §7c the assembled `hK` slot with `hbudget` monotone in `K`
  (`FinalStroke.hbudget_of_le_budgetRounds`).

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`; axiom audit
at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.InitDq

open QuantumMaxCutEnergy
open QMCNumericRuntime
open QMCLeafB.InitVerdict
open QMCLeafB.RoundProgram

/-- The request coding of the leaf (definitionally the one every closing module uses). -/
local instance instRequestCodingInitDq :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The campaign tolerance and its box bound -/

/-- **The campaign tolerance**, `RundataParams.dqShallow`. -/
noncomputable def dqOf (G : QuantumMaxCutEnergy.Input) : ℚ :=
  QMCLeafB.RundataParams.dqShallow G

theorem dqOf_pos (G : QuantumMaxCutEnergy.Input) : 0 < dqOf G :=
  QMCLeafB.RundataParams.dqShallow_pos G

theorem dqOf_nonneg (G : QuantumMaxCutEnergy.Input) : 0 ≤ dqOf G := (dqOf_pos G).le

/-- **`dqShallow ≤ 1`**: `ε = Rq/40000 ≤ 9·Rq + 1` for `Rq ≥ 0`, and the `Rq = 0` branch is `1`. -/
theorem dqOf_le_one (G : QuantumMaxCutEnergy.Input) : dqOf G ≤ 1 := by
  unfold dqOf QMCLeafB.RundataParams.dqShallow
  split_ifs with h
  · norm_num
  · have hS : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G := QMCLeafB.RundataArith.Rq_nonneg G
    unfold QMCLeafB.RundataParams.dqShallowCore QMCLeafB.RundataCert.eps
    rw [div_le_one (by linarith : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1)]
    nlinarith

/-- **The box bound of the pivot descent at the campaign tolerance**: `M = 2n² + 2·dq²`.  It is the
`M` of `Boundary.initShapeOf (n·n) M`, i.e. the same object `RunParts.hwit` names. -/
noncomputable def muOf (G : QuantumMaxCutEnergy.Input) : ℚ :=
  2 * ((G.n : ℚ) * (G.n : ℚ)) + 2 * (dqOf G * dqOf G)

/-- `muOf` in the shelf's spelling. -/
theorem muOf_eq (G : QuantumMaxCutEnergy.Input) :
    muOf G = 2 * (G.n : ℚ) ^ 2 + 2 * (dqOf G) ^ 2 := by
  unfold muOf
  simp only [pow_two]

theorem muOf_pos (G : QuantumMaxCutEnergy.Input) : 0 < muOf G := by
  unfold muOf
  have h1 : (0 : ℚ) ≤ (G.n : ℚ) * (G.n : ℚ) := by positivity
  have h2 : 0 < dqOf G * dqOf G := by
    have := dqOf_pos G
    positivity
  nlinarith

/-- **`mu ≥ 1` at `2 ≤ n`** — the range on which the run is ever read (`hd` is only asked inside the
interior bracket, which forces `2 ≤ G.n`).  At `n ≤ 1` the statement is simply false, and it is not
needed there. -/
theorem muOf_ge_one {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) : 1 ≤ muOf G := by
  unfold muOf
  have hnq : (2 : ℚ) ≤ (G.n : ℚ) := by exact_mod_cast hn
  have h1 : (2 : ℚ) * 2 ≤ (G.n : ℚ) * (G.n : ℚ) := by nlinarith
  have h2 : (0 : ℚ) ≤ dqOf G * dqOf G := by
    have := dqOf_nonneg G
    positivity
  nlinarith

/-- **`muOf G ≤ (2n+2)²`** — the starting shape parameter is at most quadratic in the order.  This is
what keeps the round count's logarithm `≈ log(1/dq) + log n`, with no extra `n`-dependence from the
tolerance. -/
theorem muOf_le_sq (G : QuantumMaxCutEnergy.Input) :
    ((muOf G : ℚ) : ℝ) ≤ (2 * (G.n : ℝ) + 2) ^ 2 := by
  have hdq1 : dqOf G ≤ 1 := dqOf_le_one G
  have hdq0 : (0 : ℚ) ≤ dqOf G := dqOf_nonneg G
  have hsq : dqOf G * dqOf G ≤ 1 := by nlinarith
  have hmu : muOf G ≤ 2 * (G.n : ℚ) * (G.n : ℚ) + 2 := by
    unfold muOf
    linarith
  have hcast : ((2 * (G.n : ℚ) * (G.n : ℚ) + 2 : ℚ) : ℝ)
      = 2 * ((G.n : ℝ)) * ((G.n : ℝ)) + 2 := by push_cast; ring
  have hnn : (0 : ℝ) ≤ (G.n : ℝ) := Nat.cast_nonneg _
  calc ((muOf G : ℚ) : ℝ) ≤ ((2 * (G.n : ℚ) * (G.n : ℚ) + 2 : ℚ) : ℝ) := by
        exact_mod_cast hmu
    _ = 2 * ((G.n : ℝ)) * ((G.n : ℝ)) + 2 := hcast
    _ ≤ (2 * (G.n : ℝ) + 2) ^ 2 := by nlinarith

/-! ## 2.  The initial state at `muOf` -/

/-- The initial state as a function of the request's bits, the box bound and the threshold.  Same
shape as `RStInit.initCore`, but `M` is a parameter instead of `MOf (n)`. -/
noncomputable def initCoreD (xs : List Bool) (M : ℚ) (t : ℚ) : RSt :=
  mkSt (inputWidth xs) (QMCLeafB.RStInit.wProg (xs, parseEdges xs))
    (identVia (doubleUp xs) (inputWidth xs) (M⁻¹)) t M (gridOf (inputWidth xs)) [] []

/-- The box bound read off the request's own bit list — the form `Poly` can compute.  Equal to
`muOf p.1.1` (`muOfD_eq`). -/
noncomputable def muOfD (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : ℚ :=
  2 * ((inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) : ℚ)
        * (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) : ℚ))
    + 2 * (dqOf p.1.1 * dqOf p.1.1)

/-- **The initial round state at the campaign tolerance.** -/
noncomputable def init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : RSt :=
  initCoreD (QuantumMaxCutEnergy.encodeRequest p.1) (muOfD p) p.2

@[simp] theorem initCoreD_stN (xs : List Bool) (M t : ℚ) :
    stN (initCoreD xs M t) = inputWidth xs := rfl
@[simp] theorem initCoreD_stA (xs : List Bool) (M t : ℚ) :
    stA (initCoreD xs M t) = QMCLeafB.RStInit.wProg (xs, parseEdges xs) := rfl
@[simp] theorem initCoreD_stX (xs : List Bool) (M t : ℚ) :
    stX (initCoreD xs M t) = identVia (doubleUp xs) (inputWidth xs) (M⁻¹) := rfl
@[simp] theorem initCoreD_stT (xs : List Bool) (M t : ℚ) : stT (initCoreD xs M t) = t := rfl
@[simp] theorem initCoreD_stMu (xs : List Bool) (M t : ℚ) : stMu (initCoreD xs M t) = M := rfl
@[simp] theorem initCoreD_stD (xs : List Bool) (M t : ℚ) :
    stD (initCoreD xs M t) = gridOf (inputWidth xs) := rfl
@[simp] theorem initCoreD_stOks (xs : List Bool) (M t : ℚ) :
    stOks (initCoreD xs M t) = [] := rfl
@[simp] theorem initCoreD_stRec (xs : List Bool) (M t : ℚ) :
    stRec (initCoreD xs M t) = [] := rfl

/-! ### 2a.  Reading the state back -/

theorem stN_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stN (init0 p) = p.1.1.n := by
  show inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) = p.1.1.n
  exact inputWidth_request p.1.1 p.1.2

/-- **The state's `mu` register is `muOf` of the graph**, not of the tape. -/
theorem muOfD_eq (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    muOfD p = muOf p.1.1 := by
  unfold muOfD muOf
  rw [inputWidth_request p.1.1 p.1.2]

theorem stMu_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stMu (init0 p) = muOfD p := rfl

/-- **`stMu (init0 p) = 2·n² + 2·dqOf G²`** — the `2 * (G.n:ℚ)^2 + 2 * P.dq^2` that
`RunParams.hbudget`, `RunParts.hwit` and `RunParts.hcut` all name. -/
theorem stMu_init0_dq (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stMu (init0 p) = 2 * (p.1.1.n : ℚ) ^ 2 + 2 * (dqOf p.1.1) ^ 2 := by
  rw [stMu_init0, muOfD_eq, muOf_eq]

theorem stT_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : stT (init0 p) = p.2 := rfl

theorem stOks_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stOks (init0 p) = [] := rfl

theorem stRec_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stRec (init0 p) = [] := rfl

theorem stD_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stD (init0 p) = gridOf (stN (init0 p)) := rfl

theorem dOf_pos (n : ℕ) : 0 < gridOf n := by
  unfold gridOf
  positivity

theorem stD_pos_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : 0 < stD (init0 p) :=
  dOf_pos _

/-- **`A` is the row-major code of the weight matrix.** -/
theorem stA_correct (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    MatQ.correct G.n (QMCLeafB.RStInit.wMatQ G)
      (stA (init0 ((G, coins), t))) :=
  QMCLeafB.RStInit.wProg_correct G coins

theorem stA_correct_noTape (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    MatQ.correct G.n (QMCLeafB.RStInit.wMatQ G)
      (stA (init0 (QMCLeafB.FinalStroke.noTape G t))) :=
  stA_correct G [] t

theorem stX_correct_core (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    MatQ.correct (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1))
      (QMCLeafB.Boundary.initShapeOf (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1))
        (muOf p.1.1)) (stX (init0 p)) := by
  have hN : inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)
      ≤ (doubleUp (QuantumMaxCutEnergy.encodeRequest p.1)).length := by
    rw [doubleUp_length]
    exact Nat.le_trans (inputWidth_le_length _) (QMCLeafB.RStInit.self_le_mul_self _)
  have hx : stX (init0 p) = identVia (doubleUp (QuantumMaxCutEnergy.encodeRequest p.1))
      (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)) ((muOfD p)⁻¹) := rfl
  have hM : muOfD p = muOf p.1.1 := muOfD_eq p
  refine ⟨?_, ?_⟩
  · rw [hx, identVia_length _ _ hN]
  · intro i j
    rw [hx, identVia_eq_mk _ _ hN, MatQ.entry_mk _ _ i.isLt j.isLt,
      QMCLeafB.InitVerdict.initShapeOf_apply, hM]

/-- **`X` is the row-major code of `initShapeOf (n·n) (muOf G)`.** -/
theorem stX_correct (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    MatQ.correct (stN (init0 p))
      (QMCLeafB.Boundary.initShapeOf (stN (init0 p)) (muOf p.1.1)) (stX (init0 p)) :=
  stX_correct_core p

/-- The same at the graph, so that the index is `G.n`. -/
theorem stX_correct_G (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    MatQ.correct G.n (QMCLeafB.Boundary.initShapeOf G.n (muOf G))
      (stX (init0 ((G, coins), t))) := by
  have h := stX_correct ((G, coins), t)
  rw [stN_init0] at h
  exact h

/-- **In `RunParts`' own spelling**: the code of `initShapeOf (n·n) (2n² + 2·P.dq²)` at
`P.dq = dqOf G`.  This is the statement `RunParts.hwit`/`hcut` read the run's `Aat … 0` off. -/
theorem stX_correct_dq (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    MatQ.correct G.n
      (QMCLeafB.Boundary.initShapeOf G.n (2 * (G.n : ℚ) ^ 2 + 2 * (dqOf G) ^ 2))
      (stX (init0 ((G, coins), t))) := by
  rw [← muOf_eq]
  exact stX_correct_G G coins t

theorem stX_toMatrix_dq (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    MatQ.toMatrix G.n (stX (init0 ((G, coins), t)))
      = QMCLeafB.Boundary.initShapeOf G.n (2 * (G.n : ℚ) ^ 2 + 2 * (dqOf G) ^ 2) :=
  ((MatQ.correct_iff).mp (stX_correct_dq G coins t)).2

theorem stA_toMatrix (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    MatQ.toMatrix G.n (stA (init0 ((G, coins), t))) = QMCLeafB.RStInit.wMatQ G :=
  ((MatQ.correct_iff).mp (stA_correct G coins t)).2

theorem stA_length (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    (stA (init0 ((G, coins), t))).length = G.n * G.n :=
  (stA_correct G coins t).1

/-- **`init_normalised`**: both row-major codes have exactly `n·n` entries. -/
theorem init_normalised (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    (stX (init0 p)).length = stN (init0 p) * stN (init0 p) :=
  (stX_correct p).1

theorem stA_length_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    (stA (init0 p)).length = stN (init0 p) * stN (init0 p) := by
  obtain ⟨⟨G, coins⟩, t⟩ := p
  rw [stN_init0]
  exact stA_length G coins t

/-- The shape's entries are all in `[-1,1]`: the diagonal is `mu⁻¹` with `mu ≥ 1`. -/
theorem stX_entry_abs_le_one (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (coins : List Bool) (t : ℚ) (i j : Fin G.n) :
    |MatQ.entry G.n (stX (init0 ((G, coins), t))) i j| ≤ 1 := by
  have h := stX_correct_G G coins t
  rw [h.2 i j, QMCLeafB.InitVerdict.initShapeOf_apply]
  by_cases hij : (i : ℕ) = (j : ℕ)
  · rw [if_pos hij, abs_inv]
    have h1 : (1 : ℚ) ≤ muOf G := muOf_ge_one hn
    have h2 : (0 : ℚ) < muOf G := muOf_pos G
    rw [abs_of_pos h2, inv_le_one₀ h2]
    exact h1
  · rw [if_neg hij, abs_zero]
    norm_num

/-! ## 3.  The initial state is a program

The only new ingredient relative to `RStInit`: the tolerance `dqOf G` must be `Poly` in the request.
`Rq G` is (`BrickRQ.Rq_poly_req`), `dqShallow` is `if Rq = 0 then 1 else Rq/40000/(9·Rq+1)` — one
comparison, one branch, two divisions — so it is too, and `muOf` follows by arithmetic. -/

theorem poly_mul2 {α : Type} [Coding α] {f g : α → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f a * g a) :=
  Poly.comp (f := fun z : ℚ × ℚ => z.1 * z.2) (g := fun a => (f a, g a))
    Poly.rat_mul (Poly.pair hf hg)

theorem poly_add2 {α : Type} [Coding α] {f g : α → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f a + g a) :=
  Poly.comp (f := fun z : ℚ × ℚ => z.1 + z.2) (g := fun a => (f a, g a))
    Poly.rat_add (Poly.pair hf hg)

theorem poly_div2 {α : Type} [Coding α] {f g : α → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f a / g a) :=
  Poly.comp (f := fun z : ℚ × ℚ => z.1 / z.2) (g := fun a => (f a, g a))
    Poly.rat_div (Poly.pair hf hg)

theorem poly_const_mul {α : Type} [Coding α] (c : ℚ) {f : α → ℚ} (hf : Poly f) :
    Poly (fun a => c * f a) :=
  poly_mul2 (Automatic.Poly.const (β := ℚ) c) hf

theorem poly_const_add {α : Type} [Coding α] (c : ℚ) {f : α → ℚ} (hf : Poly f) :
    Poly (fun a => f a + c) :=
  poly_add2 hf (Automatic.Poly.const (β := ℚ) c)

theorem poly_natCast_comp {α : Type} [Coding α] {f : α → ℕ} (hf : Poly f) :
    Poly (fun a => ((f a : ℕ) : ℚ)) :=
  Poly.comp (f := fun n : ℕ => (n : ℚ)) (g := f) Poly.rat_ofNat hf

theorem poly_Rq_req :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QMCLeafB.EngineRuntime.Rq p.1.1) :=
  Poly.comp (f := fun a : QuantumMaxCutEnergy.Input × List Bool =>
      QMCLeafB.EngineRuntime.Rq a.1) (g := Prod.fst) QMCLeafB.BrickRQ.Rq_poly_req Poly.fst

/-- **The campaign tolerance is a program.** -/
theorem poly_dqOf_req :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => dqOf p.1.1) := by
  have hRq := poly_Rq_req
  have hnum : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QMCLeafB.EngineRuntime.Rq p.1.1 / 40000) :=
    poly_div2 hRq (Automatic.Poly.const (β := ℚ) 40000)
  have h9 : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (9 : ℚ) * QMCLeafB.EngineRuntime.Rq p.1.1) := poly_const_mul 9 hRq
  have hden : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      9 * QMCLeafB.EngineRuntime.Rq p.1.1 + 1) := poly_const_add 1 h9
  have hcore : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QMCLeafB.EngineRuntime.Rq p.1.1 / 40000 / (9 * QMCLeafB.EngineRuntime.Rq p.1.1 + 1)) :=
    poly_div2 hnum hden
  have hz : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      decide (QMCLeafB.EngineRuntime.Rq p.1.1 = 0)) :=
    Poly.rat_eq_comp hRq (Automatic.Poly.const (β := ℚ) 0)
  have hfin : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      if QMCLeafB.EngineRuntime.Rq p.1.1 = 0 then (1 : ℚ)
      else QMCLeafB.EngineRuntime.Rq p.1.1 / 40000 / (9 * QMCLeafB.EngineRuntime.Rq p.1.1 + 1)) :=
    Poly.ite_prop (α := ((QuantumMaxCutEnergy.Input × List Bool) × ℚ))
      (p := fun p => QMCLeafB.EngineRuntime.Rq p.1.1 = 0) hz (Automatic.Poly.const (β := ℚ) 1) hcore
  refine QMCLeafB.FinishLine.poly_of_pointwise hfin (fun p => ?_)
  simp only [dqOf, QMCLeafB.RundataParams.dqShallow, QMCLeafB.RundataParams.dqShallowCore,
    QMCLeafB.RundataCert.eps]

/-- **The box bound is a program.** -/
theorem poly_muOfD_req :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => muOfD p) := by
  have hN := QMCLeafB.RStInit.poly_inputWidth_req
  have hNq : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) : ℚ)) := poly_natCast_comp hN
  have hsq : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) : ℚ)
        * (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) : ℚ)) := poly_mul2 hNq hNq
  have hfirst : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      2 * ((inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) : ℚ)
        * (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) : ℚ))) :=
    poly_const_mul 2 hsq
  have hd := poly_dqOf_req
  have hdsq : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      dqOf p.1.1 * dqOf p.1.1) := poly_mul2 hd hd
  have hsecond : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      2 * (dqOf p.1.1 * dqOf p.1.1)) := poly_const_mul 2 hdsq
  exact poly_add2 hfirst hsecond

theorem poly_X_req :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      identVia (doubleUp (QuantumMaxCutEnergy.encodeRequest p.1))
        (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)) ((muOfD p)⁻¹)) := by
  have hM := poly_muOfD_req
  have hv : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => (muOfD p)⁻¹) :=
    Poly.comp (f := fun q : ℚ => q⁻¹) (g := muOfD)
      (QMCLeafB.InitVerdict.poly_ratInv) hM
  have hN := QMCLeafB.RStInit.poly_inputWidth_req
  refine Poly.comp (f := fun y : (List Bool × ℕ) × ℚ => identVia y.1.1 y.1.2 y.2)
    (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      ((doubleUp (QuantumMaxCutEnergy.encodeRequest p.1),
        inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)), (muOfD p)⁻¹))
    QMCLeafB.InitVerdict.poly_identVia ?_
  exact Poly.pair (Poly.pair QMCLeafB.RStInit.poly_doubleUp_req hN) hv

/-- **`init0` is a program.** -/
theorem poly_init0 : Poly init0 := by
  have hmk := QMCLeafB.RStInit.poly_mkSt (α := ((QuantumMaxCutEnergy.Input × List Bool) × ℚ))
    QMCLeafB.RStInit.poly_inputWidth_req QMCLeafB.RStInit.poly_wProg_req poly_X_req Poly.snd
    poly_muOfD_req QMCLeafB.RStInit.poly_gridOf_req
    (Automatic.Poly.const (α := ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (β := List Bool) [])
    (Automatic.Poly.const (α := ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (β := List ℚ) [])
  exact QMCLeafB.FinishLine.poly_of_pointwise hmk (fun p => rfl)

/-! ## 4.  The state ignores the random tape -/

theorem initCoreD_congr (xs xs' : List Bool) (M : ℚ) (t : ℚ)
    (h1 : inputWidth xs = inputWidth xs') (h2 : parseEdges xs = parseEdges xs') :
    initCoreD xs M t = initCoreD xs' M t := by
  have hN1 : inputWidth xs' ≤ (doubleUp xs).length := by
    rw [doubleUp_length, ← h1]
    exact Nat.le_trans (inputWidth_le_length xs) (QMCLeafB.RStInit.self_le_mul_self _)
  have hN2 : inputWidth xs' ≤ (doubleUp xs').length := by
    rw [doubleUp_length]
    exact Nat.le_trans (inputWidth_le_length xs') (QMCLeafB.RStInit.self_le_mul_self _)
  unfold initCoreD
  rw [QMCLeafB.RStInit.wProg_eq, QMCLeafB.RStInit.wProg_eq, h1, h2,
    identVia_eq_of_le _ _ hN1 hN2]

/-- **`init0` is tape-free** — the `hinitTape` slot of the closing stroke. -/
theorem init0_tape (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2) := by
  have hM : muOfD p = muOfD (QMCLeafB.FinalStroke.noTape p.1.1 p.2) := by
    rw [muOfD_eq, muOfD_eq, QMCLeafB.FinalStroke.noTape_fst]
  show initCoreD (QuantumMaxCutEnergy.encodeRequest (p.1.1, p.1.2)) (muOfD p) p.2
      = initCoreD (QuantumMaxCutEnergy.encodeRequest (p.1.1, ([] : List Bool)))
          (muOfD (QMCLeafB.FinalStroke.noTape p.1.1 p.2)) p.2
  rw [hM]
  refine initCoreD_congr _ _ _ _ ?_ ?_
  · rw [inputWidth_request p.1.1 p.1.2, inputWidth_request p.1.1 ([] : List Bool)]
  · rw [parseEdges_request p.1.1 p.1.2, parseEdges_request p.1.1 ([] : List Bool)]

/-! ## 5.  `fvR` vanishes at the initial state -/

/-- **`fvR (init0 p) = 0`.**  The weight code's diagonal vanishes and the shape code is diagonal, at
*any* `mu`; so this does not depend on the tolerance and the same proof as
`HtopInit.fvR_init0` applies verbatim. -/
theorem fvR_init0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.RoundProgram.fvR (init0 (QMCLeafB.FinalStroke.noTape G t)) = 0 := by
  have hA := stA_correct_noTape G t
  have hX := stX_correct (QMCLeafB.FinalStroke.noTape G t)
  have hN : stN (init0 (QMCLeafB.FinalStroke.noTape G t)) = G.n := stN_init0 _
  have hAlen : (stA (init0 (QMCLeafB.FinalStroke.noTape G t))).length = G.n * G.n := hA.1
  have hXlen : (stX (init0 (QMCLeafB.FinalStroke.noTape G t))).length = G.n * G.n := by
    rw [hX.1, hN]
  have hXlen' : (stX (init0 (QMCLeafB.FinalStroke.noTape G t))).length
      = stN (init0 (QMCLeafB.FinalStroke.noTape G t))
        * stN (init0 (QMCLeafB.FinalStroke.noTape G t)) := by
    rw [hXlen, hN]
  rw [QMCLeafB.RoundProgram.fvR, hN]
  refine QMCLeafB.HtopInit.frobV_eq_zero_of_orth hXlen (fun i j => ?_)
  have h1 : MatQ.entry G.n (stA (init0 (QMCLeafB.FinalStroke.noTape G t))) i j
      = QMCLeafB.RStInit.wMatQ G i j := hA.2 i j
  have h2 : MatQ.entry G.n (stX (init0 (QMCLeafB.FinalStroke.noTape G t))) i j
      = QMCLeafB.Boundary.initShapeOf G.n (muOf G) i j := by
    rw [hN] at hX
    exact hX.2 i j
  rw [h1, h2]
  by_cases hij : i = j
  · subst hij
    rw [QMCLeafB.HtopInit.wMatQ_diag]
    ring
  · rw [QMCLeafB.HtopInit.initShapeOf_offdiag _ _ hij]
    ring

/-! ## 6.  The round's clip is inert on the initial shape -/

theorem inBoxR_muOf_of_abs_le_one {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {q : ℚ}
    (h : |q| ≤ 1) : QMCLeafB.RoundProgram.inBoxR (muOf G) q = true := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hmu : 1 ≤ muOf G := muOf_ge_one hn
  unfold QMCLeafB.RoundProgram.inBoxR
  rw [decide_eq_true (by linarith : -muOf G ≤ q),
    decide_eq_true (by linarith : q ≤ muOf G)]
  rfl

theorem clipRat_muOf_of_abs_le_one {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {q : ℚ}
    (h : |q| ≤ 1) : QMCLeafB.RoundProgram.clipRat (muOf G) q = q :=
  QMCLeafB.RoundProgram.clipRat_of_inBox (inBoxR_muOf_of_abs_le_one hn h)

/-! ## 7.  The fuel at the campaign tolerance

The round count is `FinalStroke.budgetRounds G dq m = SimLoop.simRounds n Φ₀ r m` with
`Φ₀ = volPot (n·n) (initShapeOf (n·n) (2n²+2dq²))` and `r = dq/(8(Rq+1))`.  Since
`2Φ₀/r^{n²} = 2·(√(2n²+2dq²)·8(Rq+1)/dq)^{n²}`, the whole `dq`-dependence of the count is the
factor `1/dq` in the base — so the estimate is the same as at `dq = 1` up to
`clog 2 ⌈1/dq⌉`, and the only thing to prove about the tolerance is that this log is bounded by the
*input length*'s bit cost, not by `n`. -/

/-- The starting shape parameter at a general tolerance. -/
noncomputable def Mparam (G : QuantumMaxCutEnergy.Input) (dq : ℚ) : ℚ :=
  2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2

theorem muOf_eq_Mparam (G : QuantumMaxCutEnergy.Input) : muOf G = Mparam G (dqOf G) := by
  rw [muOf_eq, Mparam]

theorem Mparam_pos (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) :
    0 < Mparam G dq := by
  unfold Mparam
  have h1 : (0 : ℚ) ≤ (G.n : ℚ) ^ 2 := sq_nonneg _
  have h2 : 0 < dq ^ 2 := by positivity
  nlinarith

/-- **`2n² + 2dq² ≤ (2n+2)²` at `dq ≤ 1`** — the starting radius is at most `2(n+1)`. -/
theorem Mparam_le_sq (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (h0 : 0 ≤ dq) (h1 : dq ≤ 1) :
    ((Mparam G dq : ℚ) : ℝ) ≤ (2 * (G.n : ℝ) + 2) ^ 2 := by
  have hsq : dq ^ 2 ≤ 1 := by nlinarith
  have hn0 : (0 : ℚ) ≤ (G.n : ℚ) := Nat.cast_nonneg _
  have hmu : Mparam G dq ≤ 2 * (G.n : ℚ) * (G.n : ℚ) + 2 := by
    unfold Mparam
    nlinarith
  have hcast : ((2 * (G.n : ℚ) * (G.n : ℚ) + 2 : ℚ) : ℝ)
      = 2 * ((G.n : ℝ)) * ((G.n : ℝ)) + 2 := by push_cast; ring
  have hnn : (0 : ℝ) ≤ (G.n : ℝ) := Nat.cast_nonneg _
  calc ((Mparam G dq : ℚ) : ℝ) ≤ ((2 * (G.n : ℚ) * (G.n : ℚ) + 2 : ℚ) : ℝ) := by
        exact_mod_cast hmu
    _ = 2 * ((G.n : ℝ)) * ((G.n : ℝ)) + 2 := hcast
    _ ≤ (2 * (G.n : ℝ) + 2) ^ 2 := by nlinarith

/-- The base whose `n²`-th power is `2Φ₀/r^{n²}` at the tolerance `dq`. -/
noncomputable def baseAdq (G : QuantumMaxCutEnergy.Input) (dq : ℚ) : ℝ :=
  Real.sqrt (((Mparam G dq : ℚ) : ℝ)) * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) / dq)

/-- **The potential identity at a general tolerance.** -/
theorem two_pot_div_dq (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) :
    2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2))
      / ((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))
      = 2 * (baseAdq G dq) ^ (G.n * G.n) := by
  have hM : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 := by
    have h1 : (0 : ℚ) ≤ (G.n : ℚ) ^ 2 := sq_nonneg _
    have h2 : 0 < dq ^ 2 := by positivity
    nlinarith
  have hΦ : QMCLeafB.EngineIterates.volPot (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2))
      = (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))) ^ (G.n * G.n) :=
    QMCLeafB.Boundary.volPot_initShapeOf _ hM
  have hq : ((dq : ℚ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdq)
  have h8 : (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)) ≠ 0 := by
    have := QMCLeafB.BudgetBound.Rq_cast_nonneg G
    intro h; linarith [h]
  have hinv : ((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))))⁻¹
      = 8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ) := by
    field_simp
  have hbase : baseAdq G dq
      = Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))
        * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ)) := by
    unfold baseAdq Mparam
    ring
  calc 2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2))
        / ((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))
      = 2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2))
          * (((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))))⁻¹)
            ^ (G.n * G.n) := by
        rw [inv_pow, ← div_eq_mul_inv]
    _ = 2 * (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))) ^ (G.n * G.n)
          * ((8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ)))
            ^ (G.n * G.n) := by
        rw [hΦ, hinv]
    _ = 2 * (baseAdq G dq) ^ (G.n * G.n) := by
        rw [hbase, mul_pow]
        ring

/-- **`baseAdq ≥ 8·√2 > 1`**: `√(2n²+2dq²) ≥ √2·dq` and `8(Rq+1)/dq ≥ 8/dq`, so the `dq` cancels. -/
theorem baseAdq_ge_eight_sqrt_two (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) :
    8 * Real.sqrt 2 ≤ baseAdq G dq := by
  have hq0 : (0 : ℝ) < ((dq : ℚ) : ℝ) := by exact_mod_cast hdq
  have hRq0 : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) :=
    QMCLeafB.BudgetBound.Rq_cast_nonneg G
  have hMge : ((2 * dq ^ 2 : ℚ) : ℝ) ≤ ((Mparam G dq : ℚ) : ℝ) := by
    have h : (2 * dq ^ 2 : ℚ) ≤ Mparam G dq := by
      unfold Mparam
      nlinarith [sq_nonneg (G.n : ℚ)]
    exact_mod_cast h
  have hsq2 : Real.sqrt (((2 * dq ^ 2 : ℚ) : ℝ)) = Real.sqrt 2 * ((dq : ℚ) : ℝ) := by
    have hcast : (((2 * dq ^ 2 : ℚ) : ℝ)) = 2 * (((dq : ℚ) : ℝ)) ^ 2 := by push_cast; ring
    have hsq : (2 : ℝ) * (((dq : ℚ) : ℝ)) ^ 2 = (Real.sqrt 2 * ((dq : ℚ) : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    rw [hcast, hsq]
    exact Real.sqrt_sq (by positivity)
  have hA : Real.sqrt 2 * ((dq : ℚ) : ℝ) ≤ Real.sqrt (((Mparam G dq : ℚ) : ℝ)) := by
    rw [← hsq2]
    exact Real.sqrt_le_sqrt hMge
  have hB : (8 : ℝ) / ((dq : ℚ) : ℝ)
      ≤ 8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith)
      (le_of_lt (inv_pos.mpr hq0))
  have hB0 : (0 : ℝ) ≤ (8 : ℝ) / ((dq : ℚ) : ℝ) := by positivity
  have hstep := mul_le_mul hA hB hB0 (Real.sqrt_nonneg _)
  have hsimp : (Real.sqrt 2 * ((dq : ℚ) : ℝ)) * ((8 : ℝ) / ((dq : ℚ) : ℝ))
      = 8 * Real.sqrt 2 := by
    field_simp
  unfold baseAdq
  rw [← hsimp]
  exact hstep

/-- `1 ≤ baseAdq` at `0 < dq`. -/
theorem one_le_baseAdq (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) :
    1 ≤ baseAdq G dq := by
  have h := baseAdq_ge_eight_sqrt_two G hdq
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-! ### 7a.  `1/dq` is bounded by the bit cost of `Rq` -/

/-- **`1/Rq ≤ 2 ^ bitCost Rq`**: the reciprocal of the total weight is at most the denominator of
`Rq`, which is `< 2 ^ (Nat.size ·) ≤ 2 ^ bitCost`. -/
theorem inv_Rq_le_two_pow_bitCost (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    (QMCLeafB.EngineRuntime.Rq G)⁻¹
      ≤ (2 : ℚ) ^ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) := by
  set q := QMCLeafB.EngineRuntime.Rq G
  have hinv : q⁻¹ = (q.den : ℚ) / (q.num : ℚ) := by
    rw [Rat.inv_def, Rat.divInt_eq_div]
    push_cast
    ring
  rw [hinv]
  have hmul : ((q.num : ℚ)) = q * (q.den : ℚ) := (Rat.mul_den_eq_num q).symm
  have hden0 : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.den_pos
  have hnum0 : (0 : ℚ) < (q.num : ℚ) := by rw [hmul]; positivity
  have hnum1 : (1 : ℚ) ≤ (q.num : ℚ) := by
    have hZ : (1 : ℤ) ≤ q.num := by
      have hZ0 : (0 : ℤ) < q.num := by exact_mod_cast hnum0
      omega
    exact_mod_cast hZ
  have hle : (q.den : ℚ) / (q.num : ℚ) ≤ (q.den : ℚ) := by
    rw [div_le_iff₀ hnum0]
    nlinarith
  have hsizeNat : q.den ≤ 2 ^ Nat.size q.den := Nat.le_of_lt (Nat.lt_size_self _)
  have hsizeQ : (q.den : ℚ) ≤ (2 : ℚ) ^ Nat.size q.den := by
    have hcast : ((2 ^ Nat.size q.den : ℕ) : ℚ) = (2 : ℚ) ^ Nat.size q.den := by
      push_cast; ring
    calc (q.den : ℚ) ≤ ((2 ^ Nat.size q.den : ℕ) : ℚ) := by exact_mod_cast hsizeNat
      _ = (2 : ℚ) ^ Nat.size q.den := hcast
  have hbc : Nat.size q.den ≤ QMCLeafB.Hspec.bitCost q := by
    simp only [QMCLeafB.Hspec.bitCost]
    omega
  have hpow : (2 : ℚ) ^ Nat.size q.den ≤ (2 : ℚ) ^ QMCLeafB.Hspec.bitCost q :=
    pow_le_pow_right₀ (by norm_num) hbc
  linarith

/-- The `dq`-algebra of the tolerance, abstract in the total weight `S` and its bit cost `B`:
`1/dqShallow = 360000 + 40000/S` and both terms are under `2^(2B+26)`. -/
theorem shallow_inv_algebra {S : ℚ} (hS : 0 < S) {B : ℕ} (hB1 : 1 ≤ B)
    (hSinv : S⁻¹ ≤ (2 : ℚ) ^ B) :
    ((S / 40000) / (9 * S + 1))⁻¹ ≤ (2 : ℚ) ^ (2 * B + 26) := by
  have hSne : S ≠ 0 := ne_of_gt hS
  have hsplit : ((S / 40000) / (9 * S + 1))⁻¹ = 360000 + 40000 / S := by
    rw [div_div, inv_div,
      show 40000 * (9 * S + 1) = 360000 * S + 40000 by ring, add_div,
      mul_div_cancel_right₀ 360000 hSne]
  rw [hsplit]
  have hstep : 40000 / S ≤ 40000 * (2 : ℚ) ^ B := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hSinv (by norm_num)
  have hA : (360000 : ℚ) ≤ (2 : ℚ) ^ 19 := by norm_num
  have hB2 : (2 : ℚ) ^ 19 ≤ (2 : ℚ) ^ (2 * B + 25) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hC : 40000 * (2 : ℚ) ^ B ≤ (2 : ℚ) ^ (B + 16) := by
    have h40000 : (40000 : ℚ) ≤ 2 ^ 16 := by norm_num
    calc 40000 * (2 : ℚ) ^ B ≤ 2 ^ 16 * (2 : ℚ) ^ B :=
          mul_le_mul_of_nonneg_right h40000 (by positivity)
      _ = (2 : ℚ) ^ (16 + B) := by rw [pow_add]
      _ = (2 : ℚ) ^ (B + 16) := by rw [show 16 + B = B + 16 by omega]
  have hD : (2 : ℚ) ^ (B + 16) ≤ (2 : ℚ) ^ (2 * B + 25) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hfin : (2 : ℚ) ^ (2 * B + 25) + (2 : ℚ) ^ (2 * B + 25) = (2 : ℚ) ^ (2 * B + 26) := by
    rw [show 2 * B + 26 = (2 * B + 25) + 1 by omega, pow_succ]
    ring
  linarith

/-- **`1/dqShallow G ≤ 2 ^ (2·bitCost (Rq G) + 26)`** — the campaign tolerance's only contribution to
the round count. -/
theorem inv_dqOf_le (G : QuantumMaxCutEnergy.Input) :
    (dqOf G)⁻¹ ≤ (2 : ℚ) ^ (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 26) := by
  rcases eq_or_lt_of_le (QMCLeafB.RundataArith.Rq_nonneg G) with h0 | hpos
  · have h1 : dqOf G = 1 := by
      unfold dqOf QMCLeafB.RundataParams.dqShallow
      rw [h0, if_pos rfl]
    rw [h1, inv_one]
    exact one_le_pow₀ (by norm_num)
  · have hdq : dqOf G
        = (QMCLeafB.EngineRuntime.Rq G / 40000) / (9 * QMCLeafB.EngineRuntime.Rq G + 1) := by
      unfold dqOf QMCLeafB.RundataParams.dqShallow QMCLeafB.RundataParams.dqShallowCore
        QMCLeafB.RundataCert.eps
      rw [if_neg (ne_of_gt hpos)]
    rw [hdq]
    refine shallow_inv_algebra hpos ?_ (inv_Rq_le_two_pow_bitCost G hpos)
    simp only [QMCLeafB.Hspec.bitCost]
    omega

/-- The same, transported to `ℝ` (the form the potential arithmetic uses). -/
theorem inv_dqOf_le_real (G : QuantumMaxCutEnergy.Input) :
    (((dqOf G : ℚ) : ℝ))⁻¹
      ≤ (2 : ℝ) ^ (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 26) := by
  have h := inv_dqOf_le G
  have hcast : ((((2 : ℚ) ^ (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 26)) : ℚ) : ℝ)
      = (2 : ℝ) ^ (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 26) := by
    push_cast
    ring
  have hinv : (((dqOf G)⁻¹ : ℚ) : ℝ) = (((dqOf G : ℚ) : ℝ))⁻¹ := by push_cast; ring
  rw [← hinv, ← hcast]
  exact_mod_cast h

/-! ### 7b.  `baseAdq` is at most `16(n+1)(⌈Rq⌉+1)·2^(2·bitCost+26)` -/

theorem baseAdq_le_nat (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) (hdq1 : dq ≤ 1)
    (hinq : (((dq : ℚ) : ℝ))⁻¹
      ≤ (2 : ℝ) ^ (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 26)) :
    baseAdq G dq
      ≤ ((16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) : ℕ) : ℝ)
        * (2 : ℝ) ^ (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 26) := by
  have hq0 : (0 : ℝ) < ((dq : ℚ) : ℝ) := by exact_mod_cast hdq
  have hsqrt : Real.sqrt (((Mparam G dq : ℚ) : ℝ)) ≤ 2 * ((G.n : ℕ) : ℝ) + 2 := by
    have h0 : (0 : ℝ) ≤ 2 * ((G.n : ℕ) : ℝ) + 2 := by positivity
    calc Real.sqrt (((Mparam G dq : ℚ) : ℝ)) ≤ Real.sqrt ((2 * ((G.n : ℕ) : ℝ) + 2) ^ 2) :=
          Real.sqrt_le_sqrt (Mparam_le_sq G hdq.le hdq1)
      _ = 2 * ((G.n : ℕ) : ℝ) + 2 := Real.sqrt_sq h0
  have hqle1 : ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ)
      ≤ ((Nat.ceil (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℝ) := by
    have := Nat.le_ceil (QMCLeafB.EngineRuntime.Rq G)
    simpa using this
  have hRq0 : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) :=
    QMCLeafB.BudgetBound.Rq_cast_nonneg G
  have h8 : (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ))
      ≤ 8 * (((Nat.ceil (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℝ) + 1)
        * (2 : ℝ) ^ (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 26) := by
    rw [div_eq_mul_inv]
    have step1 : 8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)
        ≤ 8 * (((Nat.ceil (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℝ) + 1) := by linarith
    have step2 : (0 : ℝ)
        ≤ 8 * (((Nat.ceil (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℝ) + 1) := by
      have hnc : (0 : ℝ) ≤ ((Nat.ceil (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    calc 8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) * (((dq : ℚ) : ℝ))⁻¹
        ≤ 8 * (((Nat.ceil (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℝ) + 1)
            * (((dq : ℚ) : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right step1 (le_of_lt (inv_pos.mpr hq0))
      _ ≤ 8 * (((Nat.ceil (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℝ) + 1)
            * (2 : ℝ) ^ (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 26) :=
          mul_le_mul_of_nonneg_left hinq step2
  have hnat : ((16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) : ℕ) : ℝ)
      = (2 * ((G.n : ℕ) : ℝ) + 2)
        * (8 * (((Nat.ceil (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℝ) + 1)) := by
    push_cast
    ring
  have htail0 : (0 : ℝ) ≤ 8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ) := by
    have : (0 : ℝ) ≤ 8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) := by linarith
    positivity
  unfold baseAdq
  calc Real.sqrt (((Mparam G dq : ℚ) : ℝ))
        * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ))
      ≤ (2 * ((G.n : ℕ) : ℝ) + 2)
          * (8 * (((Nat.ceil (QMCLeafB.EngineRuntime.Rq G) : ℕ) : ℝ) + 1)
            * (2 : ℝ) ^ (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 26)) :=
        mul_le_mul hsqrt h8 htail0 (by linarith)
    _ = ((16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) : ℕ) : ℝ)
          * (2 : ℝ) ^ (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 26) := by
        rw [hnat]; ring

/-- The pure `Nat.clog` chain at the tolerance. -/
theorem clog_four_factor (n b c : ℕ) :
    Nat.clog 2 (16 * (n + 1) * (c + 1) * 2 ^ (2 * b + 26))
      ≤ Nat.clog 2 (c + 1) + n + (2 * b + 31) := by
  have h2 : Nat.clog 2 (16 * (n + 1) * (c + 1))
      ≤ Nat.clog 2 (16 * (n + 1)) + Nat.clog 2 (c + 1) :=
    QMCLeafB.BudgetBound.clog_two_mul_le (x := 16 * (n + 1)) (y := c + 1)
      (by have h : 0 < 16 * (n + 1) := by positivity
          omega) (by omega)
  have h3 : Nat.clog 2 (16 * (n + 1) * (c + 1) * 2 ^ (2 * b + 26))
      ≤ Nat.clog 2 (16 * (n + 1) * (c + 1)) + Nat.clog 2 (2 ^ (2 * b + 26)) :=
    QMCLeafB.BudgetBound.clog_two_mul_le (x := 16 * (n + 1) * (c + 1))
      (y := 2 ^ (2 * b + 26))
      (by have h : 0 < 16 * (n + 1) * (c + 1) := by positivity
          omega) Nat.one_le_two_pow
  have h1 : Nat.clog 2 (16 * (n + 1)) ≤ 4 + Nat.clog 2 (n + 1) := by
    have h := QMCLeafB.BudgetBound.clog_two_mul_le (x := 16) (y := n + 1)
      (by norm_num) (by omega)
    have h16 : Nat.clog 2 16 = 4 := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.clog_pow 2 4 (by norm_num)]
    omega
  have h4 : Nat.clog 2 (2 ^ (2 * b + 26)) = 2 * b + 26 := Nat.clog_pow 2 (2 * b + 26) (by norm_num)
  have hd : Nat.clog 2 (n + 1) ≤ n + 1 := QMCLeafB.BudgetBound.clog_two_le_self (by omega)
  omega

/-- **The logarithm of the initial potential at the campaign tolerance.** -/
theorem clog_baseAdq_le (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq) (hdq1 : dq ≤ 1)
    (hinq : (((dq : ℚ) : ℝ))⁻¹
      ≤ (2 : ℝ) ^ (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 26)) :
    Nat.clog 2 (Nat.ceil (baseAdq G dq))
      ≤ Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n
        + (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 31) := by
  set b := QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) with hb
  have hceil : Nat.ceil (baseAdq G dq)
      ≤ 16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) * 2 ^ (2 * b + 26) := by
    refine Nat.ceil_le.mpr ?_
    have hcast : ((16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) * 2 ^ (2 * b + 26)
        : ℕ) : ℝ)
        = ((16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) : ℕ) : ℝ)
          * (2 : ℝ) ^ (2 * b + 26) := by
      push_cast
      ring
    calc baseAdq G dq
        ≤ ((16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) : ℕ) : ℝ)
          * (2 : ℝ) ^ (2 * b + 26) := baseAdq_le_nat G hdq hdq1 hinq
      _ = ((16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) * 2 ^ (2 * b + 26)
            : ℕ) : ℝ) := by rw [hcast]
  calc Nat.clog 2 (Nat.ceil (baseAdq G dq))
      ≤ Nat.clog 2 (16 * (G.n + 1) * (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1)
        * 2 ^ (2 * b + 26)) := Nat.clog_mono_right 2 hceil
    _ ≤ Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n + (2 * b + 31) :=
        clog_four_factor G.n b (Nat.ceil (QMCLeafB.EngineRuntime.Rq G))

/-! ### 7c.  The round count at the campaign tolerance -/

/-- The `Nat.clog` step: at any base `≥ 1` and `N ≥ 1`, `clog 2 ⌈2·base^N⌉ ≤ N·(clog 2 ⌈base⌉ + 1)`. -/
theorem ceil_two_pow_le {base : ℝ} (h1 : 1 ≤ base) {N : ℕ} (hN1 : 1 ≤ N) :
    Nat.ceil (2 * base ^ N) ≤ ((2 * Nat.ceil base) ^ N : ℕ) := by
  have hnon : (0 : ℝ) ≤ base := le_trans (by norm_num) h1
  have hsAle : base ≤ ((Nat.ceil base : ℕ) : ℝ) := Nat.le_ceil _
  have h2N : (2 : ℝ) ≤ (2 : ℝ) ^ N := by
    have h := QMCLeafB.BudgetBound.two_le_two_pow (N := N) hN1
    have h' : ((2 : ℕ) : ℝ) ≤ (((2 : ℕ) ^ N : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have hs0 : (0 : ℝ) ≤ ((Nat.ceil base : ℕ) : ℝ) := Nat.cast_nonneg _
  refine Nat.ceil_le.mpr ?_
  calc 2 * base ^ N ≤ 2 * ((Nat.ceil base : ℕ) : ℝ) ^ N := by
        have h := pow_le_pow_left₀ hnon hsAle N
        linarith
    _ ≤ (2 : ℝ) ^ N * ((Nat.ceil base : ℕ) : ℝ) ^ N := by
        have hs : (0 : ℝ) ≤ ((Nat.ceil base : ℕ) : ℝ) ^ N := by positivity
        nlinarith
    _ = ((2 : ℝ) * ((Nat.ceil base : ℕ) : ℝ)) ^ N := (mul_pow _ _ _).symm
    _ = (((2 * Nat.ceil base) ^ N : ℕ) : ℝ) := by push_cast; ring

theorem clog_two_pow_le {base : ℝ} (h1 : 1 ≤ base) {N : ℕ} (hN1 : 1 ≤ N) :
    Nat.clog 2 (Nat.ceil (2 * base ^ N)) ≤ N * (Nat.clog 2 (Nat.ceil base) + 1) := by
  refine (Nat.clog_le_iff_le_pow (by norm_num)).mpr ?_
  refine le_trans (ceil_two_pow_le h1 hN1) ?_
  have h2s : (2 * Nat.ceil base) ^ N ≤ (2 ^ (Nat.clog 2 (Nat.ceil base) + 1)) ^ N := by
    apply Nat.pow_le_pow_left
    have h1' : Nat.ceil base ≤ 2 ^ Nat.clog 2 (Nat.ceil base) := Nat.le_pow_clog (by norm_num) _
    calc 2 * Nat.ceil base ≤ 2 * 2 ^ Nat.clog 2 (Nat.ceil base) := by omega
      _ = 2 ^ (Nat.clog 2 (Nat.ceil base) + 1) := by rw [pow_succ]; ring
  calc (2 * Nat.ceil base) ^ N ≤ (2 ^ (Nat.clog 2 (Nat.ceil base) + 1)) ^ N := h2s
    _ = 2 ^ (N * (Nat.clog 2 (Nat.ceil base) + 1)) := by rw [← pow_mul, Nat.mul_comm]

/-- **The round count at a general tolerance.**  `budgetRounds G dq m ≤ m·(n²+1)·(clog⌈base⌉ + 2)`. -/
theorem budgetRounds_le_clog_dq (G : QuantumMaxCutEnergy.Input) {dq : ℚ} (hdq : 0 < dq)
    (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G dq m
      ≤ m * ((G.n * G.n + 1) * (Nat.clog 2 (Nat.ceil (baseAdq G dq)) + 2)) := by
  rcases Nat.eq_zero_or_pos G.n with hn0 | hnpos
  · have hbud : QMCLeafB.FinalStroke.budgetRounds G dq m = m := by
      unfold QMCLeafB.FinalStroke.budgetRounds QMCLeafB.SimLoop.simRounds
      rw [hn0]
      have hM : (0 : ℚ) < 2 * (↑(0 : ℕ) : ℚ) ^ 2 + 2 * dq ^ 2 := by
        have h2 : 0 < dq ^ 2 := by positivity
        nlinarith
      have hΦ : QMCLeafB.EngineIterates.volPot (0 * 0)
          (QMCLeafB.Boundary.initShapeOf (0 * 0) (2 * (↑(0 : ℕ) : ℚ) ^ 2 + 2 * dq ^ 2)) = 1 := by
        rw [QMCLeafB.Boundary.volPot_initShapeOf (0 * 0) hM]
        simp
      rw [hΦ]
      norm_num
    rw [hbud, hn0]
    have h0 : 0 ≤ Nat.clog 2 (Nat.ceil (baseAdq G dq)) := Nat.zero_le _
    nlinarith
  · have hN1 : 1 ≤ G.n * G.n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hbase1 : 1 ≤ baseAdq G dq := one_le_baseAdq G hdq
    have hbud : QMCLeafB.FinalStroke.budgetRounds G dq m
        = Nat.clog 2 ⌈2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
            (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
              (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2))
          / ((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))⌉₊
          * m := rfl
    rw [hbud, two_pot_div_dq G hdq, Nat.mul_comm m]
    refine Nat.mul_le_mul_right m ?_
    refine le_trans (clog_two_pow_le hbase1 hN1) ?_
    have h0 : 0 ≤ Nat.clog 2 (Nat.ceil (baseAdq G dq)) := Nat.zero_le _
    nlinarith

/-- **The round count at the campaign tolerance.** -/
theorem budgetRounds_le_log_dq (G : QuantumMaxCutEnergy.Input) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G (dqOf G) m
      ≤ m * ((G.n * G.n + 1)
          * (Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n
            + (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 33))) := by
  refine le_trans (budgetRounds_le_clog_dq G (dqOf_pos G) m) ?_
  refine Nat.mul_le_mul_left m ?_
  refine Nat.mul_le_mul_left (G.n * G.n + 1) ?_
  have hbase : Nat.clog 2 (Nat.ceil (baseAdq G (dqOf G)))
      ≤ Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n
        + (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 31) :=
    clog_baseAdq_le G (dqOf_pos G) (dqOf_le_one G) (inv_dqOf_le_real G)
  omega

/-- **The round count in `bitCost` form.** -/
theorem budgetRounds_le_bitCost_dq (G : QuantumMaxCutEnergy.Input) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G (dqOf G) m
      ≤ m * ((G.n + 1) ^ 2
          * (3 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 34)) := by
  refine le_trans (budgetRounds_le_log_dq G m) ?_
  refine Nat.mul_le_mul_left m ?_
  have hc := QMCLeafB.RoundCountEstimate.clog_ceil_Rq_le G
  have h1 : G.n * G.n + 1 ≤ (G.n + 1) ^ 2 := by nlinarith
  have h2 : Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n
      + (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 33)
      ≤ 3 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 34 := by omega
  exact Nat.mul_le_mul h1 h2

/-- **The round count in input-length form** — a monomial in the dimension and
`L = (encodeInput G).length`, which is what a `Poly` fuel length needs. -/
theorem budgetRounds_le_input_length_dq (G : QuantumMaxCutEnergy.Input) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G (dqOf G) m
      ≤ 256 * m * ((G.n + 1) ^ 3 * ((encodeInput G).length + 1) ^ 3) := by
  set L := (encodeInput G).length with hL
  have hbc : QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) ≤ 48 * L + 16 :=
    QMCLeafB.Hspec.bitCost_Rq_le G
  refine le_trans (budgetRounds_le_bitCost_dq G m) ?_
  have hkey : (G.n + 1) ^ 2
      * (3 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + G.n + 34)
      ≤ (G.n + 1) ^ 2 * (3 * (48 * L + 16) + G.n + 34) := by
    apply Nat.mul_le_mul_left
    omega
  refine le_trans (Nat.mul_le_mul_left m hkey) ?_
  have hnL : G.n ≤ L := by
    rw [hL]
    simp only [encodeInput, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  have hL3 : L ≤ (L + 1) ^ 3 := by
    have h1 : (L + 1) ≤ (L + 1) ^ 3 := by
      calc (L + 1) = (L + 1) * 1 := by ring
        _ ≤ (L + 1) * (L + 1) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
        _ = (L + 1) ^ 3 := by ring
    omega
  have hX' : 3 * (48 * L + 16) + G.n + 34 ≤ 256 * (L + 1) ^ 3 := by
    have h1 : 144 * L ≤ 144 * (L + 1) ^ 3 := Nat.mul_le_mul_left 144 hL3
    have h2 : G.n ≤ (L + 1) ^ 3 := le_trans hnL hL3
    have h3 : (1 : ℕ) ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hsq : (G.n + 1) ^ 2 ≤ (G.n + 1) ^ 3 := by
    calc (G.n + 1) ^ 2 = (G.n + 1) ^ 2 * 1 := by ring
      _ ≤ (G.n + 1) ^ 2 * (G.n + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (G.n + 1) ^ 3 := by ring
  refine le_trans (Nat.mul_le_mul_left m (Nat.mul_le_mul hsq hX')) ?_
  have hconst : m * ((G.n + 1) ^ 3 * (256 * (L + 1) ^ 3))
      = 256 * m * ((G.n + 1) ^ 3 * (L + 1) ^ 3) := by ring
  rw [hconst]

/-- **The `hK` slot of the closing stroke at the campaign tolerance**, with the monomial count. -/
noncomputable def Kcount (m : ℕ) (G : QuantumMaxCutEnergy.Input) : ℕ :=
  256 * m * ((G.n + 1) ^ 3 * ((encodeInput G).length + 1) ^ 3)

theorem hK_dq (m : ℕ) (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.FinalStroke.budgetRounds G (dqOf G) m ≤ Kcount m G :=
  budgetRounds_le_input_length_dq G m

/-- **`hbudget` at the campaign tolerance is monotone in the round factor** — restated at `dqOf` so
that any `K ≥ Kcount m G` gives `RunParams.hbudget` with nothing further to prove. -/
theorem hbudget_dq (G : QuantumMaxCutEnergy.Input) (m : ℕ) (hm1 : 1 ≤ m)
    {K : ℕ} (hK : QMCLeafB.FinalStroke.budgetRounds G (dqOf G) m ≤ K) :
    QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * (dqOf G) ^ 2)) * (1 / 2) ^ K
      < (((dqOf G : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n) :=
  QMCLeafB.FinalStroke.hbudget_of_le_budgetRounds G (dqOf G) (dqOf_pos G) m hm1 hK

/-- **The fuel count, as a function of the request.**  `Kcount` written on the request's own code:
the order is the request's unary header and `L` is the request's length (which dominates
`(encodeInput G).length`). -/
noncomputable def Kfuel (m : ℕ) (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : ℕ :=
  256 * m * ((inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) + 1) ^ 3
    * ((QuantumMaxCutEnergy.encodeRequest p.1).length + 1) ^ 3)

/-- **`hK` in fuel form**: the round count at the campaign tolerance is under `Kfuel`. -/
theorem hK_fuel (m : ℕ) (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    QMCLeafB.FinalStroke.budgetRounds p.1.1 (dqOf p.1.1) m ≤ Kfuel m p := by
  refine le_trans (budgetRounds_le_input_length_dq p.1.1 m) ?_
  have hn : p.1.1.n = inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) :=
    (inputWidth_request p.1.1 p.1.2).symm
  have hL : (encodeInput p.1.1).length ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length := by
    simp only [QuantumMaxCutEnergy.encodeRequest, List.length_append]
    omega
  have hL' : (encodeInput p.1.1).length + 1
      ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length + 1 := by omega
  unfold Kfuel
  rw [hn]
  refine Nat.mul_le_mul_left (256 * m) ?_
  refine Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 3) (Nat.pow_le_pow_left hL' 3)

/-- **`Kfuel` is a `Poly` function of the request** — the count the fuel slot needs. -/
theorem poly_Kfuel (m : ℕ) :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => ((Kfuel m p : ℕ) : ℚ)) := by
  have hN := QMCLeafB.RStInit.poly_inputWidth_req
  have hL : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => (QuantumMaxCutEnergy.encodeRequest p.1).length) := by
    have henc : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => QuantumMaxCutEnergy.encodeRequest p.1) :=
      Poly.comp (f := fun r : QuantumMaxCutEnergy.Input × List Bool =>
          QuantumMaxCutEnergy.encodeRequest r) (g := Prod.fst)
        ⟨BooleanLists.packProgram.recode QuantumMaxCutEnergy.encodeRequest (fun _ => rfl)
          (fun _ => rfl)⟩ Poly.fst
    exact Poly.comp (f := (List.length : List Bool → ℕ)) (g := _) Poly.list_length henc
  have hNq : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      ((inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) : ℕ) : ℚ)) := poly_natCast_comp hN
  have hLq : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (((QuantumMaxCutEnergy.encodeRequest p.1).length : ℕ) : ℚ)) := poly_natCast_comp hL
  have hN1 : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      ((inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) : ℕ) : ℚ) + 1) :=
    poly_add2 hNq (Automatic.Poly.const (α := ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (β := ℚ) 1)
  have hL1 : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (((QuantumMaxCutEnergy.encodeRequest p.1).length : ℕ) : ℚ) + 1) :=
    poly_add2 hLq (Automatic.Poly.const (α := ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (β := ℚ) 1)
  have hcube : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => (((inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) : ℕ) : ℚ) + 1) ^ 3) := by
    simpa only [pow_three, mul_assoc] using poly_mul2 (poly_mul2 hN1 hN1) hN1
  have hcubeL : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => ((((QuantumMaxCutEnergy.encodeRequest p.1).length : ℕ) : ℚ) + 1) ^ 3) := by
    simpa only [pow_three, mul_assoc] using poly_mul2 (poly_mul2 hL1 hL1) hL1
  have hmm : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => (256 * (m : ℚ)) * ((((inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) : ℕ) : ℚ) + 1) ^ 3 * ((((QuantumMaxCutEnergy.encodeRequest p.1).length : ℕ) : ℚ) + 1) ^ 3)) :=
    poly_const_mul (256 * (m : ℚ)) (poly_mul2 hcube hcubeL)
  refine QMCLeafB.FinishLine.poly_of_pointwise hmm (fun p => ?_)
  unfold Kfuel
  push_cast
  ring


/-- **The two counts agree at the tape-free request**: `Kfuel` (a `Poly` function of the whole
request) equals `Kcount` (the tape-free count whose `hbudget` `RunParams` needs) once the tape is
empty.  So a fuel program computing `Kfuel` has the right length at every `noTape G t`. -/
theorem Kfuel_noTape (m : ℕ) (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    Kfuel m (QMCLeafB.FinalStroke.noTape G t) = Kcount m G := by
  have hw : inputWidth (QuantumMaxCutEnergy.encodeRequest (G, ([] : List Bool))) = G.n :=
    inputWidth_request G []
  have hl : (QuantumMaxCutEnergy.encodeRequest (G, ([] : List Bool))).length
      = (encodeInput G).length := by
    simp only [QuantumMaxCutEnergy.encodeRequest, List.append_nil]
  unfold Kfuel Kcount
  rw [show QMCLeafB.FinalStroke.noTape G t = ((G, ([] : List Bool)), t) from rfl]
  rw [hw, hl]

/-! ### 7d.  The closing stroke at the campaign tolerance — **DO NOT USE, see §7f**

`FinalReunion.endgame_RSt` pins `dq = 1` (its `hK` is `budgetRounds G 1 m ≤ K G`).  The version below
is the same stroke at `dqOf`, with the round count `Kcount m` from §7c and the `RunParts` payload read
at `runParamsOfK G (dqOf G) …`.  Nothing else changes: `init0` is the state of §2 and every one of its
slots is discharged in this file, so what remains of the stroke is `hmono` (the round's size class),
the halving pair `rmax`/`m`, one `hfuelLen`, and one `RunParts` per bracketed `(G,t)`.

**WARNING (see `hhalve-FALSE.md` and §7f).**  This stroke — like every member of the family — takes
`(rmax : ℚ)` and `(m : ℕ)` *global*, with `hhalve : ∀ G, …`.  That hypothesis is **false**: `rho0R
(G.n²) ρ` decreases to `exp(-2ρ)` as `G.n → ∞`, so `(√(rho0R))⁻¹` increases to `exp(ρ) > 1` (ρ > 0)
or to `1` (ρ = 0), and `hhalve` is equivalent to `rho0R ≥ 2^{2/m} > 1`.  No fixed `(rmax, m)` works;
`m` must grow like `2·G.n²·ln2` (already at `rmax = 1/4`, `G.n = 2` the inequality fails for every
`m`).  The stroke is kept only because it is the `dq`-transported statement of the shelf's theorem;
**use `endgame_RSt_dq_shallow` (§7f) instead**, which carries `m`, `rmax` per `G` exactly as
`RundataParams.runParamsShallow` does. -/
theorem endgame_RSt_dq
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (C k : ℕ) (hk : 1 ≤ k)
    (hmono : ∀ (s : RSt) (j : ℕ),
      (enc (QMCLeafB.RoundProgram.round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = Kcount m p.1.1 * m)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict (fun G' _ => Kcount m G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G (dqOf G) (dqOf_pos G) rmax hrmax m hm1
          (Kcount m G) (hK_dq m G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_orbit_of_parts
    init0 fuel QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    poly_init0 hfuel QMCLeafB.RoundProgram.poly_round QMCLeafB.RoundProgram.poly_verdict
    (QMCLeafB.FinalStroke.sizesOrbitPow C k)
    (fun a j hj => QMCLeafB.FinalStroke.orbit_of_monomial_pow QMCLeafB.RoundProgram.round C k hk
      hmono a j hj)
    (fun G' _ => Kcount m G' * m) init0_tape hfuelLen
    (fun G t _ hlo hhi => (hd G t hlo hhi).toRunData)


/-! ### 7e.  Why `dq = 1` is impossible, and the shelf shape of the count -/

/-- **`roundCost (wMatrixQ G) (3/4) = (231/64)·Rq G`** — the exact rounding cost at the slack-1
step. -/
theorem roundCost_wMatrixQ_three_quarters (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 / 4)
      = (231 / 64) * QMCLeafB.EngineRuntime.Rq G := by
  rw [QMCLeafB.RundataCert.roundCost_wMatrixQ, QMCLeafB.RundataCert.sum_abs_wMatrixQ]
  norm_num

/-- **`dq = 1` cannot carry an `ok` round.**  `RunData.hcert` needs
`roundCost A (3·dq/4) + dq/2 - ε ≤ ε`; at `dq = 1` the left side is `(231/64)·Rq + 1/2` against
`2ε = Rq/20000`, and `231/64 > 1/20000`.  So the engine *must* run at a smaller tolerance — this is
the reason `dqShallow` is not a convenience but a requirement. -/
theorem dq_one_budget_fails (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    2 * QMCLeafB.RundataCert.eps G
      < QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * (1 : ℚ) / 4)
        + 1 / 2 := by
  rw [show (3 : ℚ) * 1 / 4 = 3 / 4 by norm_num, roundCost_wMatrixQ_three_quarters]
  unfold QMCLeafB.RundataCert.eps
  nlinarith

/-- **The round count in the shelf's `budgetRounds_le_monomial` shape, at the campaign tolerance.**
`B := n + 3·bitCost (Rq G) + 34` is the log of the starting potential; the tolerance contributes the
`2·bitCost` part of it and nothing else. -/
theorem budgetRounds_le_monomial_dq (G : QuantumMaxCutEnergy.Input) (m L : ℕ)
    (h : G.n + 3 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 34 ≤ (L + 1) ^ 3) :
    QMCLeafB.FinalStroke.budgetRounds G (dqOf G) m
      ≤ m * ((G.n + 1) ^ 3 * (L + 1) ^ 3) := by
  refine le_trans (budgetRounds_le_log_dq G m) ?_
  have hn : G.n * G.n + 1 ≤ (G.n + 1) ^ 3 := by nlinarith
  have hc := QMCLeafB.RoundCountEstimate.clog_ceil_Rq_le G
  have hB : Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1) + G.n
      + (2 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 33)
      ≤ G.n + 3 * QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G) + 34 := by omega
  refine le_trans (Nat.mul_le_mul_left m (Nat.mul_le_mul hn hB)) ?_
  exact Nat.mul_le_mul_left m (Nat.mul_le_mul_left _ h)


/-! ### 7f.  The per-`G` closing stroke — the usable one

§7d inherits the shelf's global `(rmax, m)`, and `hhalve` at a global `m` is false (`hhalve-FALSE.md`).
The stroke below carries the halving data **per `G`**, exactly as `RundataParams.runParamsShallow`
already does, so every one of its hypotheses is satisfiable:

* `mOfG G = 16·G.n⁴` (`RundataHalving.mOf (G.n · G.n)`),
* `rmaxOfG G = 1/(4·G.n²)` (`RundataHalving.rmaxOf (G.n · G.n)`),
* `hhalve` is `RundataHalving.hhalveOf (G.n · G.n)` verbatim, at `2 ≤ G.n`,
* `dq = dqOf G`, `K = Kcount (mOfG G) G` with `hK_dq`.

Residual after this theorem: `hmono` (the round's one-round size class `C`, `k ≥ 1`), one
`hfuelLen : (fuel p).length = Kcount (mOfG p.1.1) p.1.1 * mOfG p.1.1` (tape-free, monomial), and one
`RunParts` per bracketed `(G,t)` at the fixed parameters. -/

/-- The halving time at `G.n²`: `16·G.n⁴`. -/
noncomputable def mOfG (G : QuantumMaxCutEnergy.Input) : ℕ :=
  QMCLeafB.RundataHalving.mOf (G.n * G.n)

/-- The contraction ceiling at `G.n²`: `1/(4·G.n²)`. -/
noncomputable def rmaxOfG (G : QuantumMaxCutEnergy.Input) : ℚ :=
  QMCLeafB.RundataHalving.rmaxOf (G.n * G.n)

theorem mOfG_ge_one {G : QuantumMaxCutEnergy.Input} (hN : 1 ≤ G.n * G.n) : 1 ≤ mOfG G :=
  QMCLeafB.RundataHalving.mOf_ge_one (G.n * G.n) hN

theorem rmaxOfG_nonneg (G : QuantumMaxCutEnergy.Input) : 0 ≤ rmaxOfG G := by
  unfold rmaxOfG QMCLeafB.RundataHalving.rmaxOf
  rcases Nat.eq_zero_or_pos (G.n * G.n) with h | h
  · rw [h]; norm_num
  · have hq : (0 : ℚ) < ((G.n * G.n : ℕ) : ℚ) := by exact_mod_cast h
    positivity

/-- **`RunParams.hhalve` at the per-`G` constants.** -/
theorem hhalveOfG {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) :
    (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((rmaxOfG G : ℚ) : ℝ)))⁻¹ ^ mOfG G
      ≤ 1 / 2 := by
  have hN : 2 ≤ G.n * G.n := by nlinarith
  have h := QMCLeafB.RundataHalving.hhalveOf (G.n * G.n) hN
  unfold mOfG rmaxOfG
  exact h

/-- **The full `RunParams` at the campaign constants**, with `K`, `m`, `dq`, `rmax` all per `G`. -/
noncomputable def paramsShallow (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.FinalStroke.runParamsOfK G (dqOf G) (dqOf_pos G) (rmaxOfG G) (rmaxOfG_nonneg G)
    (mOfG G) (mOfG_ge_one (by nlinarith)) (Kcount (mOfG G) G) (hK_dq (mOfG G) G)
    (hhalveOfG hn)

/-- The tape-free round count of the per-`G` stroke: `K·m` at the campaign constants. -/
noncomputable def Tshallow (G : QuantumMaxCutEnergy.Input) (_t : ℚ) : ℕ :=
  Kcount (mOfG G) G * mOfG G

/-- **The closing stroke at the campaign constants, per `G`** — the usable hook.  There is no
hypothesis here that is not discharged somewhere in this file, in `RundataParams`, or by the caller
(`hmono`, `hfuelLen`, and one `RunParts` per bracketed `(G,t)`). -/
theorem endgame_RSt_dq_shallow
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (C k : ℕ) (hk : 1 ≤ k)
    (hmono : ∀ (s : RSt) (j : ℕ),
      (enc (QMCLeafB.RoundProgram.round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = Tshallow p.1.1 p.2)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), (hn : 2 ≤ G.n) →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict Tshallow) G t (paramsShallow G hn)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_orbit_of_parts
    init0 fuel QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    poly_init0 hfuel QMCLeafB.RoundProgram.poly_round QMCLeafB.RoundProgram.poly_verdict
    (QMCLeafB.FinalStroke.sizesOrbitPow C k)
    (fun a j hj => QMCLeafB.FinalStroke.orbit_of_monomial_pow QMCLeafB.RoundProgram.round C k hk
      hmono a j hj)
    Tshallow init0_tape hfuelLen
    (fun G t h2 hlo hhi => (hd G t h2 hlo hhi).toRunData)

end QMCLeafB.InitDq

/-! ## 8.  Axiom audit -/

#print axioms QMCLeafB.InitDq.dqOf_le_one
#print axioms QMCLeafB.InitDq.muOf_ge_one
#print axioms QMCLeafB.InitDq.muOf_le_sq
#print axioms QMCLeafB.InitDq.stN_init0
#print axioms QMCLeafB.InitDq.muOfD_eq
#print axioms QMCLeafB.InitDq.stMu_init0_dq
#print axioms QMCLeafB.InitDq.stA_correct
#print axioms QMCLeafB.InitDq.stX_correct_dq
#print axioms QMCLeafB.InitDq.stX_toMatrix_dq
#print axioms QMCLeafB.InitDq.init_normalised
#print axioms QMCLeafB.InitDq.stX_entry_abs_le_one
#print axioms QMCLeafB.InitDq.poly_dqOf_req
#print axioms QMCLeafB.InitDq.poly_muOfD_req
#print axioms QMCLeafB.InitDq.poly_init0
#print axioms QMCLeafB.InitDq.init0_tape
#print axioms QMCLeafB.InitDq.fvR_init0
#print axioms QMCLeafB.InitDq.inBoxR_muOf_of_abs_le_one
#print axioms QMCLeafB.InitDq.clipRat_muOf_of_abs_le_one
#print axioms QMCLeafB.InitDq.inv_Rq_le_two_pow_bitCost
#print axioms QMCLeafB.InitDq.shallow_inv_algebra
#print axioms QMCLeafB.InitDq.inv_dqOf_le
#print axioms QMCLeafB.InitDq.inv_dqOf_le_real
#print axioms QMCLeafB.InitDq.baseAdq_le_nat
#print axioms QMCLeafB.InitDq.clog_four_factor
#print axioms QMCLeafB.InitDq.clog_baseAdq_le
#print axioms QMCLeafB.InitDq.budgetRounds_le_clog_dq
#print axioms QMCLeafB.InitDq.budgetRounds_le_log_dq
#print axioms QMCLeafB.InitDq.budgetRounds_le_bitCost_dq
#print axioms QMCLeafB.InitDq.budgetRounds_le_input_length_dq
#print axioms QMCLeafB.InitDq.hK_dq
#print axioms QMCLeafB.InitDq.hbudget_dq
#print axioms QMCLeafB.InitDq.hK_fuel
#print axioms QMCLeafB.InitDq.poly_Kfuel
#print axioms QMCLeafB.InitDq.Kfuel_noTape
#print axioms QMCLeafB.InitDq.endgame_RSt_dq
#print axioms QMCLeafB.InitDq.roundCost_wMatrixQ_three_quarters
#print axioms QMCLeafB.InitDq.dq_one_budget_fails
#print axioms QMCLeafB.InitDq.budgetRounds_le_monomial_dq
#print axioms QMCLeafB.InitDq.rmaxOfG_nonneg
#print axioms QMCLeafB.InitDq.hhalveOfG
#print axioms QMCLeafB.InitDq.paramsShallow
#print axioms QMCLeafB.InitDq.endgame_RSt_dq_shallow


