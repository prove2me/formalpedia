-- Prove2me | Definitions.Def_QMCLeafB_fuel
-- name    : QMCLeafB_fuel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:33:07.495865+00:00
-- url     : https://prove2.me/theorems/d797218a-a7e7-4336-ae24-3cceb78e230f
-- title:
--   QMCLeafB fuel
-- statement:
--   # leaf B phase 11 — brick `fuel` (swarm `smw05147u`, member m8, direction d1)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
/-
# leaf B phase 11 — brick `fuel` (swarm `smw05147u`, member m8, direction d1)

The **fuel list** of the closing form `QMCLeafB.SimPoly.ho_of_loop`: a `Poly` program producing a
`List Bool` whose length is the number of simulate rounds.

`ho_of_loop`'s loop runs `(fuel p).length` rounds, so the fuel has to *hit* the round count
exactly, not merely exceed it.  A `List Bool` of length `T` cannot be written `List.replicate T ()`
(`T` may be a polynomial in the input, and unary expansion is not poly-time in this fragment), but
a list program *can* square its length: `xs.flatMap (fun _ => xs)` has length `xs.length^2`.
Iterating that `k` times gives length `L^(2^k)`, a polynomial of degree `2^k` in the input length
`L`; a final `List.take` at any `Poly` round count `T` with `T ≤ L^(2^k)` gives length **exactly**
`T`.

Contents

* §1 `sqList` — `xs.flatMap (fun _ => xs)`; exact length `xs.length^2`, and
  `sqList_iterate_length`: `(sqList^[k] xs).length = xs.length^(2^k)`.
* §2 `sqListProgram`, `poly_sqList` — the squaring is a `Poly` program (`duplicate` then
  `listFlatMapWith`), hypothesis-free.
* §3 `poly_iterate` — `Poly` is closed under a numeral iterate (re-proved here so that the file
  depends on `Definitions` only; it is the same statement as `QMCLeafB.SimPoly.poly_iterate`).
* §4 **the fuel** `fuel k p = (sqList^[k]) (encodeRequest p.1)`, its program `fuelProgram`
  (built as `fst ∘ wordAsList ∘ sqList^[k]` at the word level, then `recode`d across
  `encodeRequest`), and `poly_fuel`.
* §5 `fuel_length` (`= (encodeRequest p.1).length^(2^k)`), `n_le_request_length`,
  `n_le_fuel_length` (`(p.1.1).n^(2^k) ≤ (fuel k p).length`), and **`mul_pow_le_fuel_length` /
  `roundBudget_le_fuel_length`**: the fuel dominates every monomial budget `C (n+1)^d` with
  `d + C ≤ 2^k` in the graph order — which is the form the closing needs, since the round count
  `simRounds` (`Nat.clog`-based) is not computable by a `Poly` program but *is* bounded by such a
  monomial, and the extra rounds are harmless.
* §6 **the exact-count fuel** `fuelTake k T p = (fuel k p).take (T p)` for any `Poly` round count
  `T`, with `poly_fuelTake` and the exact-length corollaries: `fuelTake_length_of_le`
  (`T p ≤ (encodeRequest p.1).length^(2^k) → (fuelTake k T p).length = T p`),
  `fuelTake_length_of_le_n` (same from `T p ≤ n^(2^k)`), `fuelTake_length_of_le_fuel`
  (`T p ≤ (fuel k p).length`), and `poly_fuelTake_const` / `fuelTake_length_const` at a numeral
  round count.
* §7 the `ho_of_loop` slots, in the argument shape of `QMCLeafB.SimPoly.ho_of_loop`.
* §8 demos (`decide`-checked lengths).
* §9 axiom audit.

**Interface note for the closing member.**  In `QMCLeafB.SimPoly.ho_of_loop` /
`solution_of_loop`, pass

    fuel  := QMCLeafB.Fuel.fuelTake k T
    hfuel := QMCLeafB.Fuel.poly_fuelTake k T hT

and use `QMCLeafB.Fuel.fuelTake_length_of_le` to turn `hTle : ∀ p, T p ≤
(encodeRequest p.1).length ^ (2^k)` into the rewrite `(fuel p).length = T p` that `hspec` needs.
If the round count is a literal numeral, m4's `ho_of_fixed_rounds` avoids fuel altogether.

No `sorry`, no `axiom`; the audit shows the standard three.
-/

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.Fuel

open QuantumMaxCutEnergy

/-! ## 1.  The squaring list function -/

/-- `sqList xs` is the list of `xs.length ^ 2` bits obtained by replacing every entry of `xs` by a
copy of `xs` and concatenating.  It is the length-squaring step of the fuel. -/
def sqList (xs : List Bool) : List Bool := xs.flatMap (fun _ => xs)

/-- Exact length of one squaring step. -/
@[simp] theorem sqList_length (xs : List Bool) : (sqList xs).length = xs.length * xs.length := by
  simp only [sqList, List.length_flatMap]
  simp only [List.map_const', List.sum_replicate]
  simp

/-- **Exact length after `k` squarings**: `xs.length ^ (2 ^ k)`. -/
theorem sqList_iterate_length (k : ℕ) (xs : List Bool) :
    ((sqList^[k]) xs).length = xs.length ^ (2 ^ k) := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', sqList_length, ih, ← Nat.pow_add, Nat.two_pow_succ]

/-! ## 2.  The squaring is a `Poly` program

`duplicate` splits the list into the pair `(xs, xs)` (coded `encodePair e e`), and
`listFlatMapWith` maps every entry of the second copy to the whole first copy and flattens.  Both
pieces are library `PolyProgram`s, so there is nothing to prove but the beta reduction. -/

/-- The length-squaring list program. -/
noncomputable def sqListProgram :
    PolyProgram (encodeList encodeBool) (encodeList encodeBool) sqList :=
  ((PolyProgram.duplicate (encodeList encodeBool)).comp
    (PolyProgram.listFlatMapWith (f := fun x : List Bool × Bool => x.1)
      (PolyProgram.fst (encodeList encodeBool) encodeBool) false false)).congr sqList
    (fun _ => rfl)

/-- **The squaring is `Poly`**, no hypotheses. -/
theorem poly_sqList : Automatic.Poly sqList := ⟨sqListProgram⟩

/-! ## 3.  Numeral iteration of a `Poly` program -/

/-- **`Poly` is closed under a numeral iterate** (one `comp` per copy).  Same statement as
`QMCLeafB.SimPoly.poly_iterate`, re-proved so that this file imports `Definitions` only. -/
theorem poly_iterate {α : Type} [Coding α] {round : α → α}
    (hr : Automatic.Poly round) (n : ℕ) :
    Automatic.Poly (fun a => Nat.iterate round n a) := by
  induction n with
  | zero =>
      have h : (fun a => Nat.iterate round 0 a) = (id : α → α) := by
        funext a
        simp
      rw [h]
      exact Automatic.Poly.identity
  | succ k ih =>
      have h : (fun a => Nat.iterate round (k + 1) a) =
          fun a => round (Nat.iterate round k a) := by
        funext a
        exact Function.iterate_succ_apply' round k a
      rw [h]
      exact Automatic.Poly.comp hr ih

/-- **`sqList^[k]` is `Poly`** for a numeral `k`. -/
theorem poly_sqList_iterate (k : ℕ) : Automatic.Poly (sqList^[k]) := poly_iterate poly_sqList k

/-! ## 4.  The fuel at the leaf's request coding -/

/-- The request coding the closing forms are stated with, spelt exactly as in
`Check_brick_finish_line` / `Check_sim_poly_m4` (`⟨encodeRequest⟩`). -/
local instance instRequestCodingFuel : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **The fuel list**: `k` squarings of the encoded request word.  Its length is
`(encodeRequest p.1).length ^ (2^k)` (§5), i.e. a polynomial of degree `2^k` in the input. -/
def fuel (k : ℕ) (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) : List Bool :=
  (sqList^[k]) (QuantumMaxCutEnergy.encodeRequest p.1)

/-- The fuel program, at the word level: project the request word out of the encoded pair
(`fst`), re-code it as a `List Bool` value (`wordAsList`), then square `k` times. -/
noncomputable def fuelWordProgram (k : ℕ) :
    PolyProgram (encodePair id id) (encodeList encodeBool)
      (fun z : List Bool × List Bool => (sqList^[k]) z.1) :=
  ((PolyProgram.fst (α := List Bool) (β := List Bool) id id).comp PolyProgram.wordAsList).comp
    ((poly_sqList_iterate k).program)

/-- **The fuel is a `Poly` program across `encodeRequest`.**  The `recode` moves the input coding
from `encodePair id id` (the raw split of the encoded request) to the leaf's request coding
`encodePair encodeRequest Ratio.encode`, which is the same word function by definition. -/
noncomputable def fuelProgram (k : ℕ) :
    PolyProgram (encodePair QuantumMaxCutEnergy.encodeRequest Ratio.encode) (encodeList encodeBool)
      (fuel k) :=
  (fuelWordProgram k).recode
    (fun p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ =>
      (QuantumMaxCutEnergy.encodeRequest p.1, Ratio.encode p.2))
    (fun _ => rfl) (fun _ => rfl)

/-- **`poly_fuel`**: the fuel slot `hfuel : Automatic.Poly fuel` of
`QMCLeafB.SimPoly.ho_of_loop`, hypothesis-free. -/
theorem poly_fuel (k : ℕ) : Automatic.Poly (fuel k) := ⟨fuelProgram k⟩

/-! ## 5.  The exact length, and domination of the graph order -/

/-- **The exact length of the fuel**: `(encodeRequest p.1).length ^ (2 ^ k)`. -/
theorem fuel_length (k : ℕ) (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) :
    (fuel k p).length = (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k) :=
  sqList_iterate_length k _

/-- The unary graph prefix sits inside the request word:
`G.n ≤ (encodeRequest (G, coins)).length` (the request word starts with `G.n` `true`s and a
`false`). -/
theorem n_le_request_length (G : QuantumMaxCutEnergy.Input) (coins : List Bool) :
    G.n ≤ (QuantumMaxCutEnergy.encodeRequest (G, coins)).length := by
  rw [QMCNumericRuntime.request_encoding]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- **The fuel dominates `n^(2^k)`**: since the request word is at least as long as the unary
graph order, the `k`-fold squaring is at least an `n^(2^k)`-long list. -/
theorem n_le_fuel_length (k : ℕ) (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) :
    (p.1.1).n ^ (2 ^ k) ≤ (fuel k p).length := by
  rw [fuel_length]
  exact Nat.pow_le_pow_left (n_le_request_length p.1.1 p.1.2) _

/-- The same bound in the form a caller with a polynomial round count uses: the fuel is at least
`L^(2^k)` where `L` is the length of the encoded request. -/
theorem request_length_pow_le_fuel_length (k : ℕ)
    (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) :
    (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k) ≤ (fuel k p).length :=
  le_of_eq (fuel_length k p).symm

/-- The request word contains the unary order **plus** its separator bit, so it is longer than
`G.n + 1`. -/
theorem succ_n_le_request_length (G : QuantumMaxCutEnergy.Input) (coins : List Bool) :
    G.n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest (G, coins)).length := by
  rw [QMCNumericRuntime.request_encoding]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- **The fuel dominates every monomial budget in the graph order.**  This is the form the closing
needs: the number of simulate rounds (`Check_sim_loop_m6.simRounds`, a `Nat.clog` budget) is *not*
computable by a `Poly` program, but for `n ≥ 2` and `d + C ≤ 2^k` the `k`-fold squaring is longer than `C * (n + 1) ^ d`. -/
theorem mul_pow_le_fuel_length (k C d : ℕ)
    (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) (hd : d + C ≤ 2 ^ k)
    (hn : 2 ≤ (p.1.1).n) :
    C * ((p.1.1).n + 1) ^ d ≤ (fuel k p).length := by
  have hL : (p.1.1).n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
    succ_n_le_request_length p.1.1 p.1.2
  have hn' : 2 ≤ (p.1.1).n + 1 := by omega
  have hC' : C ≤ ((p.1.1).n + 1) ^ C :=
    (le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left hn' C)
  rw [fuel_length]
  calc C * ((p.1.1).n + 1) ^ d
      ≤ ((p.1.1).n + 1) ^ C * ((p.1.1).n + 1) ^ d := Nat.mul_le_mul_right _ hC'
    _ = ((p.1.1).n + 1) ^ (C + d) := (Nat.pow_add _ _ _).symm
    _ ≤ ((p.1.1).n + 1) ^ (2 ^ k) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k) := Nat.pow_le_pow_left hL _

/-- **The round-budget corollary.**  A round count bounded by a monomial `C (n+1)^d` in the graph
order is under the fuel's length, i.e. the loop of `ho_of_loop` / `poly_simulate_count` runs at least
`T₀` rounds on `fuel k`.  (The analytic side supplies `hT` from `Check_sim_loop_m6.simRounds`; the
extra rounds beyond `T₀` are harmless because `anyOk`-style verdicts are monotone and the
refutation/feasibility theorems hold on every prefix.) -/
theorem roundBudget_le_fuel_length (k C d T₀ : ℕ)
    (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) (hd : d + C ≤ 2 ^ k)
    (hn : 2 ≤ (p.1.1).n) (hT : T₀ ≤ C * ((p.1.1).n + 1) ^ d) :
    T₀ ≤ (fuel k p).length :=
  hT.trans (mul_pow_le_fuel_length k C d p hd hn)

/-! ## 6.  Exactly `T` rounds: truncating the fuel at a `Poly` round count

`ho_of_loop`'s loop runs `(fuel p).length` rounds.  For a wanted round count `T` (any `Poly`
function of the input, e.g. the boilerplate's `T₀`) the fuel is truncated at `T`: its length is
`min (T p) L^(2^k)`, which *is* `T p` as soon as `T` is under the squaring bound. -/

variable (k : ℕ) (T : (QuantumMaxCutEnergy.Input × List Bool) × ℚ → ℕ)

/-- The truncated fuel: `T p` bits taken from `k` squarings of the request word. -/
def fuelTake (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) : List Bool :=
  (fuel k p).take (T p)

/-- **The truncated fuel is a `Poly` program** for any `Poly` round count `T`. -/
noncomputable def fuelTakeProgram (hT : Automatic.Poly T) :
    PolyProgram (encodePair QuantumMaxCutEnergy.encodeRequest Ratio.encode) (encodeList encodeBool)
      (fuelTake k T) :=
  ((fuelProgram k).fanout hT.program).comp
    ((PolyProgram.listTake (ea := encodeBool) false).congr (fun x : List Bool × ℕ => x.1.take x.2)
      (fun _ => rfl))

/-- **`poly_fuelTake`**: the `hfuel` slot of `QMCLeafB.SimPoly.ho_of_loop` at a prescribed round
count `T`, from `Poly T` alone. -/
theorem poly_fuelTake (hT : Automatic.Poly T) : Automatic.Poly (fuelTake k T) :=
  ⟨fuelTakeProgram k T hT⟩

/-- Length of the truncated fuel: `min (T p) (L ^ (2^k))`. -/
theorem fuelTake_length (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) :
    (fuelTake k T p).length =
      min (T p) ((QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k)) := by
  simp only [fuelTake, List.length_take, fuel_length]

/-- **The exact-count corollary.**  If the wanted round count `T p` is under the squaring bound
`L^(2^k)` (true for every polynomial round count once `2^k` exceeds its degree and `n ≥ 2`), the
truncated fuel has length *exactly* `T p`. -/
theorem fuelTake_length_of_le (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ)
    (h : T p ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k)) :
    (fuelTake k T p).length = T p := by
  rw [fuelTake_length, Nat.min_eq_left h]

/-- The same with the bound measured by the graph order `n` instead of the request word length
(the request word starts with the unary graph order). -/
theorem fuelTake_length_of_le_n (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ)
    (h : T p ≤ (p.1.1).n ^ (2 ^ k)) : (fuelTake k T p).length = T p :=
  fuelTake_length_of_le k T p
    (h.trans (Nat.pow_le_pow_left (n_le_request_length p.1.1 p.1.2) _))

/-- **The corollary in the brief's shape**: if the wanted round count is at most the length of the
squaring fuel, the truncated fuel has length exactly the round count. -/
theorem fuelTake_length_of_le_fuel (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ)
    (h : T p ≤ (fuel k p).length) : (fuelTake k T p).length = T p :=
  fuelTake_length_of_le k T p (by rwa [fuel_length] at h)

/-- The same at a **numeral** round count `T₀` (`ho_of_fixed_rounds` is cheaper when the count is
a literal, but the fuel route must be able to express it too). -/
theorem poly_fuelTake_const (T₀ : ℕ) :
    Automatic.Poly (fuelTake k (fun _ => T₀)) :=
  poly_fuelTake k _ (Automatic.Poly.const T₀)

/-- Length of the fuel at a numeral round count, when the numeral is under the squaring bound. -/
theorem fuelTake_length_const (T₀ : ℕ) (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ)
    (h : T₀ ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k)) :
    (fuelTake k (fun _ => T₀) p).length = T₀ :=
  fuelTake_length_of_le k (fun _ => T₀) p h

/-! ## 7.  The `ho_of_loop` slots

`QMCLeafB.SimPoly.ho_of_loop`'s `hfuel` argument has exactly the type
`Automatic.Poly (fun p : ((Input × List Bool) × ℚ) => fuel p)` at the request coding
`⟨encodeRequest⟩` (this file's `instRequestCodingFuel` is that instance, so the terms below are the
same terms).  The two theorems give that slot at the untruncated and at the truncated fuel. -/

/-- The `hfuel` slot of `ho_of_loop` at the untruncated squaring fuel. -/
theorem hfuel_of_loop_sq (k : ℕ) :
    Automatic.Poly (fun p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ =>
      (sqList^[k]) (QuantumMaxCutEnergy.encodeRequest p.1)) :=
  poly_fuel k

/-- The `hfuel` slot of `ho_of_loop` at the truncated fuel, from `Poly T`. -/
theorem hfuel_of_loop_take (k : ℕ)
    (T : (QuantumMaxCutEnergy.Input × List Bool) × ℚ → ℕ) (hT : Automatic.Poly T) :
    Automatic.Poly (fun p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ =>
      ((sqList^[k]) (QuantumMaxCutEnergy.encodeRequest p.1)).take (T p)) :=
  poly_fuelTake k T hT

/-! ## 8.  Demos (`decide`-checked lengths) -/

/-- One squaring step, unfolded: `[true, false]` becomes its own two copies. -/
example : sqList [true, false] = [true, false, true, false] := rfl

/-- `sqList` on `[true]` is `[true]` (length `1 = 1^2`). -/
example : sqList [true] = [true] := rfl

/-- Two squarings of a two-bit word give `2^4 = 16` bits, `decide`-checked by actually building the
list (the check does not go through `sqList_iterate_length`). -/
example : ((sqList^[2]) [true, false]).length = 16 := by decide

/-- Two squarings of a three-bit word give `3^4 = 81` bits: `sqList_iterate_length` on a case that
is not a power of two. -/
example : ((sqList^[2]) [true, true, false]).length = 81 := by
  rw [sqList_iterate_length]
  norm_num

/-- Five squarings of a three-bit word give `3^32` bits — the polynomial degree doubles at each
squaring. -/
example : ((sqList^[5]) [true, false, true]).length = 3 ^ 32 := by
  rw [sqList_iterate_length]
  norm_num

/-! ## 9.  Axiom audit -/

#print axioms QMCLeafB.Fuel.sqList_length
#print axioms QMCLeafB.Fuel.sqList_iterate_length
#print axioms QMCLeafB.Fuel.poly_sqList
#print axioms QMCLeafB.Fuel.poly_iterate
#print axioms QMCLeafB.Fuel.poly_sqList_iterate
#print axioms QMCLeafB.Fuel.poly_fuel
#print axioms QMCLeafB.Fuel.fuel_length
#print axioms QMCLeafB.Fuel.n_le_request_length
#print axioms QMCLeafB.Fuel.n_le_fuel_length
#print axioms QMCLeafB.Fuel.request_length_pow_le_fuel_length
#print axioms QMCLeafB.Fuel.succ_n_le_request_length
#print axioms QMCLeafB.Fuel.mul_pow_le_fuel_length
#print axioms QMCLeafB.Fuel.roundBudget_le_fuel_length
#print axioms QMCLeafB.Fuel.poly_fuelTake
#print axioms QMCLeafB.Fuel.fuelTake_length
#print axioms QMCLeafB.Fuel.fuelTake_length_of_le
#print axioms QMCLeafB.Fuel.fuelTake_length_of_le_n
#print axioms QMCLeafB.Fuel.fuelTake_length_of_le_fuel
#print axioms QMCLeafB.Fuel.poly_fuelTake_const
#print axioms QMCLeafB.Fuel.fuelTake_length_const
#print axioms QMCLeafB.Fuel.hfuel_of_loop_sq
#print axioms QMCLeafB.Fuel.hfuel_of_loop_take

section Audit

local instance instRequestCodingAudit : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

#check @QMCLeafB.Fuel.poly_fuel
#check @QMCLeafB.Fuel.poly_fuelTake
#check @QMCLeafB.Fuel.fuelTake_length_of_le
#check @QMCLeafB.Fuel.fuel_length
#check @QMCLeafB.Fuel.hfuel_of_loop_take

end Audit

end QMCLeafB.Fuel


