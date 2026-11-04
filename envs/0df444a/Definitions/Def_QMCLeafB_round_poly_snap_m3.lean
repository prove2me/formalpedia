-- Prove2me | Definitions.Def_QMCLeafB_round_poly_snap_m3
-- name    : QMCLeafB_round_poly_snap_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:28:09.6842+00:00
-- url     : https://prove2.me/theorems/0f2d901b-7b76-4682-81c3-e555ce62fb61
-- title:
--   QMCLeafB round_poly_snap_m3
-- statement:
--   # leaf B phase 8 — brick `round-poly-snap` (swarm `smw00sb1m`, member m3, direction d2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ledger_snap
import Definitions.Def_QMCLeafB_MatQ
import Definitions.Def_QMCLeafB_matq_update_m4
/-
# leaf B phase 8 — brick `round-poly-snap` (swarm `smw00sb1m`, member m3, direction d2)

ONE simulate round of the ellipsoid engine as a `Poly` program, with the round's specification
(the height reset, the value track and the per-round charge) transported to the *program's own*
output — and with the grid as an arbitrary input denominator, so that the assembly never has to
compute `2^k`.

## What is here

**§0 `Poly` toolbox.**  The library's `PolyProgram`s promoted to `Automatic.Poly` facts and tagged
`@[fun_prop]`: `Rat.num`, `Rat.den`, `Signed.sign`, `Int.natAbs`, `Signed.value`, `Nat` division,
`mkRat`, `Nat`/`Int` arithmetic.  `Poly f` is `Nonempty (PolyProgram enc enc f)`, so each is a
one-liner, but they are what makes the numeric layer reachable by `fun_prop` instead of hand-built
`comp` chains.

**§1 the dyadic snap is a program (`snapDiv`).**  `snapAbs k` (the ledger's truncation onto the grid
`2^{-k}ℤ`) is written as a program in which the grid **denominator is an input**:

    snapTrunc q = Signed.value (Signed.sign q.num) (q.num.natAbs / q.den)   -- truncation toward 0
    snapDiv d q = mkRat (snapTrunc (q * d)) d                               -- grid 1/d

`snapDiv_two_pow : snapDiv (2^k) q = LedgerSnap.snapAbs k q`, so every theorem about `snapAbs`
(`snapAbs_error`, `hasHeight_snapAbs`, `snapAbs_idem`, …) is available for the program's output at
`d = 2^k` with no re-proof.  But the brick does **not** need that case: §1b proves the ledger facts
for an *arbitrary* denominator,

* `abs_snapDiv_le`  : `|snapDiv d q| ≤ |q|`                    (value contraction),
* `snapDiv_error`   : `|snapDiv d q − q| ≤ 1/d`                (one grid step),
* `hasHeight_snapDiv : |q| ≤ 2^M → 0 < d → d ≤ 2^D → HasHeight (snapDiv d q) (M+D)`
                                                               (**the height reset**),

so a polynomial-size *budget number* is a valid grid: `d := 2^k` is one choice among many.  This
matters because `k ↦ 2^k` is **not** a Poly function (`2^k` has `k+1` bits while `k` has `log k`),
so an assembly that can only use `2^k` would be stuck; with these lemmas it can feed any `d ≥ 2^k`
of polynomial size (`snapDiv_error_two_pow`).

**§2 the row-major bridge.**  `MatQ.correct n X xs` (`xs` is the row-major code of `X`) is preserved
by entrywise mapping (`correct_map`), so the *program's* list iterate is the code of the *ledger's*
matrix iterate.  `Implements n fn FM` names that agreement and is closed under composition.

**§3 ONE simulate round.**  `roundFun step d xs = (step xs).map (snapDiv d)` — the snap brick
composed after the step brick — and `roundFunSep sep upd d xs = (upd (xs, sep xs)).map (snapDiv d)`,
the full round including the separation oracle.  `poly_roundFun`, `poly_roundFun'`,
`poly_roundFunSep_packed` are the `Poly` statements (the oracle's and the step's `Poly` facts are the
only hypotheses) and `roundFun_implementsD` says the program computes the ledger's per-round map
`X ↦ (step X).map (snapDiv d)`.

**§3b the round on m4's real state.**  `Check_matq_update_m4`'s `Step.stepProg` is a machine on
the packed state `RSt = ((n, X), (c, λ))` computing the rank-one update (`Step.stepProg_spec`).
`poly_stepFun` reads it as an `Automatic.Poly` fact and `poly_round_stepFun` composes it with the
snap: **step + snap of one simulate round is a `Poly` program with no hypotheses at all** — the
separation oracle only has to supply the cut vector `c` (`brick-oracle-poly`).

**§4 the ledger, on the program's state.**  `round_iterate_implementsD` identifies the `T`-fold
program output with the matrix iterate; `roundD_height_iterate` / `program_entry_height` give the
height reset on the list the program prints (`≤ M + γT + D`, additive in `T` — the point of
snapping); `program_encode_charge` bounds the printed state by `n²(3(M+γT+D)+10)` bits — polynomial
in the input length, which is what `brick-sim-poly`'s `Tm2Size` chain charges.  `roundMapD_two_pow`
recovers the ledger's `snapAbs` form at `d = 2^k`.

**§4b the error track.**  `EntryLipschitz stepM L` (`one round multiplies an entrywise error by at
most L`) plus the ledger's scalar recursion gives `round_error_iterate : |program − exact| ≤
(T·L^T)/d` entrywise, and `round_error_budget : 2·T·L^T ≤ δ·2^k → d ≥ 2^k → |program − exact| ≤ δ`
— the snap error is inside the tolerated width, which is the `correct`-side half of the round's
specification (`stepProg_correct` supplies the other half).

No `sorry`, no `axiom`; the audit at the end shows the standard three.

## Interface decisions (for the coordinator)

* the round state is `List ℚ`, row-major, tied to `Matrix (Fin n) (Fin n) ℚ` by `MatQ.correct`;
* the grid resolution enters as a **denominator `d : ℕ`** with a size budget `d ≤ 2^D`, not as `k`;
* the round function is `roundFunSep sep upd d` with `Poly sep` (cut vector) and `Poly upd`
  (packed `(X, c) ↦ X'`) the only external `Poly` hypotheses; `roundFun step d` is the same round
  with the oracle already folded into `step`.
-/

set_option linter.unusedVariables false

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.RoundPolySnap

open QMCLeafB.LedgerSnap

/-! ## 0.  The `Poly` toolbox: the numeric primitives as `fun_prop` facts -/

@[fun_prop] theorem poly_ratNum : Poly (fun q : ℚ => q.num) := ⟨PolyProgram.ratNum⟩
@[fun_prop] theorem poly_ratDen : Poly (fun q : ℚ => q.den) := ⟨PolyProgram.ratDen⟩
@[fun_prop] theorem poly_intSign : Poly (fun z : ℤ => Signed.sign z) := ⟨PolyProgram.intSign⟩
@[fun_prop] theorem poly_intAbs : Poly (fun z : ℤ => z.natAbs) := ⟨PolyProgram.intAbs⟩
@[fun_prop] theorem poly_signedValue : Poly (fun x : Bool × ℕ => Signed.value x.1 x.2) :=
  ⟨PolyProgram.intFromParts⟩
@[fun_prop] theorem poly_natDiv : Poly (fun x : ℕ × ℕ => x.1 / x.2) := ⟨PolyProgram.natDiv⟩
@[fun_prop] theorem poly_natMod : Poly (fun x : ℕ × ℕ => x.1 % x.2) := ⟨PolyProgram.natMod⟩
@[fun_prop] theorem poly_mkRat : Poly (fun x : ℤ × ℕ => mkRat x.1 x.2) := ⟨PolyProgram.mkRational⟩
@[fun_prop] theorem poly_natMul : Poly (fun x : ℕ × ℕ => x.1 * x.2) := ⟨PolyProgram.natMul⟩
@[fun_prop] theorem poly_natAdd : Poly (fun x : ℕ × ℕ => x.1 + x.2) := ⟨PolyProgram.natAdd⟩
@[fun_prop] theorem poly_natSub : Poly (fun x : ℕ × ℕ => x.1 - x.2) := ⟨PolyProgram.natSub⟩
@[fun_prop] theorem poly_natLT : Poly (fun x : ℕ × ℕ => decide (x.1 < x.2)) := ⟨PolyProgram.natLT⟩
@[fun_prop] theorem poly_natZero : Poly (fun n : ℕ => decide (n = 0)) := ⟨PolyProgram.natZero⟩
@[fun_prop] theorem poly_intOfNat : Poly (fun n : ℕ => ((n : ℤ))) := ⟨PolyProgram.intOfNat⟩
@[fun_prop] theorem poly_intNeg : Poly (fun z : ℤ => -z) := ⟨PolyProgram.intNeg⟩
@[fun_prop] theorem poly_intAdd : Poly (fun x : ℤ × ℤ => x.1 + x.2) := ⟨PolyProgram.intAdd⟩
@[fun_prop] theorem poly_intSub : Poly (fun x : ℤ × ℤ => x.1 - x.2) := ⟨PolyProgram.intSub⟩

/-! ## 1.  The grid snap, as a program

`snapAbs k` truncates toward zero onto `2^{-k}ℤ` by reading `⌊q·2^k⌋` (resp. `-⌊-q·2^k⌋`) and
dividing by `2^k`.  The program below has the *denominator* `d` as an input:
`snapDiv d q = mkRat (snapTrunc (q·d)) d`, with `snapTrunc` the truncation toward zero `ℚ → ℤ`
through the normal form `q.num / q.den`.  At `d = 2^k` this is literally `snapAbs k`. -/

/-- Truncation toward zero, `ℚ → ℤ`, from the normal form `q.num / q.den` (`q.den > 0`). -/
def snapTrunc (q : ℚ) : ℤ := Signed.value (Signed.sign q.num) (q.num.natAbs / q.den)

/-- **The grid snap with the denominator as an input**: truncate `q` toward zero onto `(1/d)ℤ`. -/
def snapDiv (d : ℕ) (q : ℚ) : ℚ := mkRat (snapTrunc (q * (d : ℚ))) d

/-- On nonnegative arguments truncation *is* the floor. -/
theorem snapTrunc_of_nonneg {q : ℚ} (hq : 0 ≤ q) : snapTrunc q = ⌊q⌋ := by
  have hnum : (0:ℤ) ≤ q.num := Rat.num_nonneg.mpr hq
  have hs : Signed.sign q.num = false := by
    simp only [Signed.sign, decide_eq_false_iff_not]
    exact not_lt.mpr hnum
  rw [snapTrunc, hs, Rat.floor_def']
  simp only [Signed.value, Bool.false_eq_true, if_false]
  rw [← Int.ofNat_ediv_ofNat, Int.natAbs_of_nonneg hnum]

/-- On negative arguments truncation is `-⌊-·⌋`. -/
theorem snapTrunc_of_neg {q : ℚ} (hq : q < 0) : snapTrunc q = -⌊-q⌋ := by
  have hnum : q.num < 0 := lt_of_not_ge (fun h => (not_le.mpr hq) (Rat.num_nonneg.mp h))
  have hs : Signed.sign q.num = true := by
    simp only [Signed.sign, decide_eq_true_iff]
    exact hnum
  have hle : q.num ≤ 0 := le_of_lt hnum
  rw [snapTrunc, hs, Rat.floor_def', Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den]
  simp only [Signed.value, if_true]
  have hle' : -q.num = (q.num.natAbs : ℤ) := by
    rw [Int.eq_neg_natAbs_of_nonpos hle]
    simp
  rw [hle', Int.ofNat_ediv_ofNat]

/-- **The program's snap is the ledger's snap**: at `d = 2^k`, `snapDiv` is exactly
`LedgerSnap.snapAbs k`. -/
theorem snapDiv_two_pow (k : ℕ) (q : ℚ) : snapDiv (2 ^ k) q = snapAbs k q := by
  by_cases hq : 0 ≤ q
  · rw [snapAbs_of_nonneg k hq, snapDiv,
      snapTrunc_of_nonneg (mul_nonneg hq (by positivity)), Rat.mkRat_eq_div]
    norm_cast
  · have hq' : q < 0 := lt_of_not_ge hq
    rw [snapAbs_of_neg k hq', snapDiv,
      snapTrunc_of_neg (mul_neg_of_neg_of_pos hq' (by positivity)), Rat.mkRat_eq_div]
    rw [Nat.cast_pow]
    norm_num
    rw [show -(q * 2 ^ k) = -q * 2 ^ k by ring]
    ring

/-! ### The snap as a `Poly` program -/

@[fun_prop] theorem poly_snapTrunc : Poly (fun q : ℚ => snapTrunc q) := by
  unfold snapTrunc
  fun_prop

/-- **ONE grid snap is a `Poly` program**, uniformly in the grid denominator `d`. -/
@[fun_prop] theorem poly_snapDiv : Poly (fun p : ℕ × ℚ => snapDiv p.1 p.2) := by
  unfold snapDiv
  fun_prop

/-- The snap fixes `0`, so it can be pushed through the row-major code. -/
theorem snapDiv_zero (d : ℕ) : snapDiv d 0 = 0 := by
  simp [snapDiv, snapTrunc, Signed.sign, Signed.value]

/-! ### §1b the ledger facts for an arbitrary denominator -/

theorem floor_nonneg_of_nonneg {a : ℚ} (h : 0 ≤ a) : (0:ℚ) ≤ ((⌊a⌋ : ℤ) : ℚ) := by
  have h' := Int.le_floor.mpr h
  exact_mod_cast h'

/-- Truncation toward zero contracts the absolute value. -/
theorem snapTrunc_abs_le (r : ℚ) : |(snapTrunc r : ℚ)| ≤ |r| := by
  by_cases h : 0 ≤ r
  · have hfl : snapTrunc r = ⌊r⌋ := snapTrunc_of_nonneg h
    have h0 : (0:ℚ) ≤ ((⌊r⌋ : ℤ) : ℚ) := floor_nonneg_of_nonneg h
    rw [hfl, abs_of_nonneg h0, abs_of_nonneg h]
    exact Int.floor_le r
  · have hr : r < 0 := lt_of_not_ge h
    have hpos : (0:ℚ) ≤ -r := le_of_lt (neg_pos.mpr hr)
    have hfl : snapTrunc r = -⌊-r⌋ := snapTrunc_of_neg hr
    have h0 : (0:ℚ) ≤ ((⌊-r⌋ : ℤ) : ℚ) := floor_nonneg_of_nonneg hpos
    have key : ((snapTrunc r : ℤ) : ℚ) = -((⌊-r⌋ : ℤ) : ℚ) := by
      rw [hfl]; push_cast; ring
    rw [key, abs_neg, abs_of_nonneg h0, abs_of_neg hr]
    exact Int.floor_le (-r)

/-- Truncation toward zero errs by less than one. -/
theorem snapTrunc_sub_abs_lt_one (r : ℚ) : |(snapTrunc r : ℚ) - r| < 1 := by
  by_cases h : 0 ≤ r
  · have hfl : snapTrunc r = ⌊r⌋ := snapTrunc_of_nonneg h
    have hle : ((⌊r⌋ : ℤ) : ℚ) ≤ r := Int.floor_le r
    have hlt : r < ((⌊r⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one r
    rw [hfl, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  · have hr : r < 0 := lt_of_not_ge h
    have hfl : snapTrunc r = -⌊-r⌋ := snapTrunc_of_neg hr
    have hle : ((⌊-r⌋ : ℤ) : ℚ) ≤ -r := Int.floor_le (-r)
    have hlt : -r < ((⌊-r⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one (-r)
    have key : ((snapTrunc r : ℤ) : ℚ) - r = -(((⌊-r⌋ : ℤ) : ℚ) - (-r)) := by
      rw [hfl]; push_cast; ring
    rw [key, abs_neg, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith

theorem snapDiv_eq (d : ℕ) (q : ℚ) :
    snapDiv d q = ((snapTrunc (q * (d:ℚ)) : ℤ) : ℚ) / (d : ℚ) :=
  Rat.mkRat_eq_div _ _

/-- **The snap contracts in absolute value.** -/
theorem abs_snapDiv_le (d : ℕ) (hd : 0 < d) (q : ℚ) : |snapDiv d q| ≤ |q| := by
  have hd' : (0:ℚ) < (d:ℚ) := by exact_mod_cast hd
  rw [snapDiv_eq, abs_div, abs_of_pos hd', div_le_iff₀ hd']
  calc |(snapTrunc (q * (d:ℚ)) : ℚ)| ≤ |q * (d:ℚ)| := snapTrunc_abs_le _
    _ = |q| * (d:ℚ) := by rw [abs_mul, abs_of_pos hd']

/-- **The snap's error is at most one grid step.** -/
theorem snapDiv_error (d : ℕ) (hd : 0 < d) (q : ℚ) : |snapDiv d q - q| ≤ 1 / (d:ℚ) := by
  have hd' : (0:ℚ) < (d:ℚ) := by exact_mod_cast hd
  have hdne : (d:ℚ) ≠ 0 := ne_of_gt hd'
  have h : snapDiv d q - q
      = ((snapTrunc (q * (d:ℚ)) : ℚ) - q * (d:ℚ)) / (d:ℚ) := by
    rw [snapDiv_eq]
    field_simp
  rw [h, abs_div, abs_of_pos hd', div_le_div_iff_of_pos_right hd']
  exact le_of_lt (snapTrunc_sub_abs_lt_one _)

/-- **A grid finer than `2^-k` satisfies the ledger's per-round error budget.** -/
theorem snapDiv_error_two_pow {k d : ℕ} (hd : 0 < d) (hk : 2 ^ k ≤ d) (q : ℚ) :
    |snapDiv d q - q| ≤ 1 / 2 ^ k := by
  have h1 : (0:ℚ) < (d:ℚ) := by exact_mod_cast hd
  have h2 : (2:ℚ) ^ k ≤ (d:ℚ) := by exact_mod_cast hk
  calc |snapDiv d q - q| ≤ 1 / (d:ℚ) := snapDiv_error d hd q
    _ ≤ 1 / 2 ^ k := div_le_div_of_nonneg_left (by norm_num) (by positivity) h2

/-- **The height reset for an arbitrary grid `1/d`**: a value bounded by `2^M` snaps to a rational of
height `M + D` as soon as the denominator is at most `2^D` — independent of the operand's height. -/
theorem hasHeight_snapDiv {q : ℚ} {M : ℕ} (hq : |q| ≤ 2 ^ M) {d : ℕ} (hd : 0 < d) {D : ℕ}
    (hdD : d ≤ 2 ^ D) : HasHeight (snapDiv d q) (M + D) := by
  have hd' : (0:ℚ) < (d:ℚ) := by exact_mod_cast hd
  have hm : |(snapTrunc (q * (d:ℚ)) : ℚ)| ≤ 2 ^ (M + D) := by
    calc |(snapTrunc (q * (d:ℚ)) : ℚ)| ≤ |q * (d:ℚ)| := snapTrunc_abs_le _
      _ = |q| * (d:ℚ) := by rw [abs_mul, abs_of_pos hd']
      _ ≤ 2 ^ M * 2 ^ D :=
            mul_le_mul hq (by exact_mod_cast hdD) (by positivity) (by positivity)
      _ = 2 ^ (M + D) := by rw [← pow_add]
  have haZ : |(snapTrunc (q * (d:ℚ)))| ≤ (2:ℤ) ^ (M + D) := by exact_mod_cast hm
  have hdZ : |((d:ℤ))| ≤ (2:ℤ) ^ (M + D) := by
    have h1 : (d:ℤ) ≤ (2:ℤ) ^ D := by exact_mod_cast hdD
    have h2 : (2:ℤ) ^ D ≤ (2:ℤ) ^ (M + D) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [abs_of_nonneg (by positivity : (0:ℤ) ≤ (d:ℤ))]
    linarith
  rw [snapDiv_eq]
  exact OAI.MetricKMedian.Gaussian.ratio_num_den_bound _ _ (by omega) _ haZ hdZ

/-- **The ledger's height reset is the `d = 2^k` case**: `hasHeight_snapAbs` for `snapDiv`. -/
theorem hasHeight_snapDiv_two_pow {q : ℚ} {M : ℕ} (hq : |q| ≤ 2 ^ M) (k : ℕ) :
    HasHeight (snapDiv (2 ^ k) q) (M + k) := by
  rw [snapDiv_two_pow]
  exact hasHeight_snapAbs hq k

/-! ### Entrywise snap of the row-major state -/

/-- **The entrywise snap of the state list is a `Poly` program** (grid `d` an input). -/
theorem poly_snapList : Poly (fun p : ℕ × List ℚ => p.2.map (snapDiv p.1)) := by
  have hfst : Poly (fun x : (ℕ × List ℚ) × ℚ => x.1.1) :=
    Automatic.Poly.comp (f := (Prod.fst : ℕ × List ℚ → ℕ))
      (g := (Prod.fst : (ℕ × List ℚ) × ℚ → ℕ × List ℚ)) Automatic.Poly.fst Automatic.Poly.fst
  have hf : Poly (fun x : (ℕ × List ℚ) × ℚ => snapDiv x.1.1 x.2) :=
    Automatic.Poly.comp (f := fun y : ℕ × ℚ => snapDiv y.1 y.2)
      (g := fun x : (ℕ × List ℚ) × ℚ => (x.1.1, x.2)) poly_snapDiv
      (Automatic.Poly.pair hfst Automatic.Poly.snd)
  exact Automatic.Poly.list_map (f := fun (p : ℕ × List ℚ) (q : ℚ) => snapDiv p.1 q)
    (as := fun p : ℕ × List ℚ => p.2) hf Automatic.Poly.snd

/-- The entrywise snap at a fixed dyadic grid `2^k`. -/
theorem poly_snapList_fixed (k : ℕ) : Poly (fun xs : List ℚ => xs.map (snapDiv (2 ^ k))) := by
  have hf : Poly (fun x : List ℚ × ℚ => snapDiv (2 ^ k) x.2) :=
    Automatic.Poly.comp (f := fun y : ℕ × ℚ => snapDiv y.1 y.2)
      (g := fun x : List ℚ × ℚ => (2 ^ k, x.2)) poly_snapDiv
      (Automatic.Poly.pair (Automatic.Poly.const (2 ^ k)) Automatic.Poly.snd)
  exact Automatic.Poly.list_map (f := fun (_ : List ℚ) (q : ℚ) => snapDiv (2 ^ k) q)
    (as := fun xs : List ℚ => xs) hf Automatic.Poly.identity

/-! ## 2.  The row-major bridge: the program's list is the ledger's matrix -/

/-- `getD` commutes with `map` for a function fixing the default. -/
theorem getD_map_zero {l : List ℚ} {f : ℚ → ℚ} (h0 : f 0 = 0) (N : ℕ) :
    (l.map f).getD N 0 = f (l.getD N 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : l[N]? with
  | none => simp [h0]
  | some a => simp

/-- **`MatQ.correct` is preserved by an entrywise map fixing `0`.** -/
theorem correct_map {n : ℕ} {X : Matrix (Fin n) (Fin n) ℚ} {xs : List ℚ}
    (h : MatQ.correct n X xs) (f : ℚ → ℚ) (h0 : f 0 = 0) :
    MatQ.correct n (X.map f) (xs.map f) := by
  refine ⟨by rw [List.length_map, h.1], fun i j => ?_⟩
  have hh : xs.getD ((i : ℕ) * n + (j : ℕ)) 0 = X i j := h.2 i j
  show (xs.map f).getD ((i : ℕ) * n + (j : ℕ)) 0 = (X.map f) i j
  rw [getD_map_zero h0, Matrix.map_apply, hh]

/-- **The program's snapped list is the code of the ledger's snapped matrix** (general grid). -/
theorem correct_map_snapDiv {n : ℕ} {X : Matrix (Fin n) (Fin n) ℚ} {xs : List ℚ}
    (h : MatQ.correct n X xs) (d : ℕ) :
    MatQ.correct n (X.map (snapDiv d)) (xs.map (snapDiv d)) :=
  correct_map h (snapDiv d) (snapDiv_zero d)

/-- The dyadic form of `correct_map_snapDiv`. -/
theorem correct_map_snapAbs {n : ℕ} {X : Matrix (Fin n) (Fin n) ℚ} {xs : List ℚ}
    (h : MatQ.correct n X xs) (k : ℕ) :
    MatQ.correct n (X.map (snapAbs k)) (xs.map (snapDiv (2 ^ k))) := by
  have h1 : MatQ.correct n (X.map (snapAbs k)) (xs.map (snapAbs k)) :=
    correct_map h (snapAbs k) (snapAbs_zero k)
  have h2 : xs.map (snapDiv (2 ^ k)) = xs.map (snapAbs k) :=
    List.map_congr_left fun q _ => snapDiv_two_pow k q
  rwa [h2]

/-- **`fn` (on row-major codes) implements `FM` (on matrices).** -/
def Implements (n : ℕ) (fn : List ℚ → List ℚ)
    (FM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ (X : Matrix (Fin n) (Fin n) ℚ) (xs : List ℚ), MatQ.correct n X xs →
    MatQ.correct n (FM X) (fn xs)

/-- `Implements` is closed under composition. -/
theorem Implements.comp {n : ℕ} {fn gn : List ℚ → List ℚ}
    {FM GM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ}
    (hg : Implements n gn GM) (hf : Implements n fn FM) :
    Implements n (gn ∘ fn) (GM ∘ FM) :=
  fun X xs h => hg _ _ (hf _ _ h)

/-- **The snap implements the ledger's entrywise snap.** -/
theorem implements_snap (n d : ℕ) :
    Implements n (fun xs => xs.map (snapDiv d)) (fun X => X.map (snapDiv d)) :=
  fun X xs h => correct_map_snapDiv h d

/-! ## 3.  ONE simulate round -/

/-- **One simulated round**: the step program followed by the grid snap. -/
def roundFun (step : List ℚ → List ℚ) (d : ℕ) (xs : List ℚ) : List ℚ :=
  (step xs).map (snapDiv d)

/-- **One simulated round including the separation oracle**: the oracle produces a cut vector from
the state, the update consumes the packed `(X, c)`, the snap resets the heights. -/
def roundFunSep (sep : List ℚ → List ℚ) (upd : List ℚ × List ℚ → List ℚ) (d : ℕ)
    (xs : List ℚ) : List ℚ :=
  (upd (xs, sep xs)).map (snapDiv d)

/-- **The round is a `Poly` program** — the only hypothesis is the step it composes. -/
theorem poly_roundFun (step : List ℚ → List ℚ) (hs : Poly step) (d : ℕ) :
    Poly (fun xs : List ℚ => roundFun step d xs) := by
  have hf : Poly (fun x : List ℚ × ℚ => snapDiv d x.2) :=
    Automatic.Poly.comp (f := fun y : ℕ × ℚ => snapDiv y.1 y.2)
      (g := fun x : List ℚ × ℚ => (d, x.2)) poly_snapDiv
      (Automatic.Poly.pair (Automatic.Poly.const d) Automatic.Poly.snd)
  exact Automatic.Poly.list_map (f := fun (_ : List ℚ) (q : ℚ) => snapDiv d q) (as := step) hf hs

/-- **The round with the grid as an input is a `Poly` program.** -/
theorem poly_roundFun' (step : List ℚ → List ℚ) (hs : Poly step) :
    Poly (fun p : ℕ × List ℚ => roundFun step p.1 p.2) := by
  have hfst : Poly (fun x : (ℕ × List ℚ) × ℚ => x.1.1) :=
    Automatic.Poly.comp (f := (Prod.fst : ℕ × List ℚ → ℕ))
      (g := (Prod.fst : (ℕ × List ℚ) × ℚ → ℕ × List ℚ)) Automatic.Poly.fst Automatic.Poly.fst
  have hf : Poly (fun x : (ℕ × List ℚ) × ℚ => snapDiv x.1.1 x.2) :=
    Automatic.Poly.comp (f := fun y : ℕ × ℚ => snapDiv y.1 y.2)
      (g := fun x : (ℕ × List ℚ) × ℚ => (x.1.1, x.2)) poly_snapDiv
      (Automatic.Poly.pair hfst Automatic.Poly.snd)
  have hstep : Poly (fun p : ℕ × List ℚ => step p.2) :=
    Automatic.Poly.comp (f := step) (g := (Prod.snd : ℕ × List ℚ → List ℚ)) hs Automatic.Poly.snd
  exact Automatic.Poly.list_map (f := fun (p : ℕ × List ℚ) (q : ℚ) => snapDiv p.1 q)
    (as := fun p : ℕ × List ℚ => step p.2) hf hstep

/-- **The full round (oracle ∘ update ∘ snap) is a `Poly` program.** -/
theorem poly_roundFunSep_packed (sep : List ℚ → List ℚ) (upd : List ℚ × List ℚ → List ℚ)
    (hsep : Poly sep) (hupd : Poly upd) (d : ℕ) :
    Poly (fun xs : List ℚ => roundFunSep sep upd d xs) := by
  have hpair : Poly (fun xs : List ℚ => (xs, sep xs)) := Automatic.Poly.pair Automatic.Poly.identity hsep
  have hstep : Poly (fun xs : List ℚ => upd (xs, sep xs)) :=
    Automatic.Poly.comp (f := upd) (g := fun xs : List ℚ => (xs, sep xs)) hupd hpair
  exact poly_roundFun (fun xs => upd (xs, sep xs)) hstep d

/-- The *mathematical* round map with a general grid: `X ↦ (step X).map (snapDiv d)`. -/
def roundMapD {n : ℕ} (stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ) (d : ℕ)
    (X : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  (stepM X).map (snapDiv d)

/-- The ledger's round map: `X ↦ (step X).map (snapAbs k)`. -/
def roundMap {n : ℕ} (stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ) (k : ℕ)
    (X : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  (stepM X).map (snapAbs k)

theorem roundMapD_two_pow {n : ℕ}
    (stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ) (k : ℕ)
    (X : Matrix (Fin n) (Fin n) ℚ) : roundMapD stepM (2 ^ k) X = roundMap stepM k X := by
  ext i j
  simp only [roundMapD, roundMap, Matrix.map_apply, snapDiv_two_pow]

/-- **The round program computes the ledger's round map.** -/
theorem roundFun_implementsD {n : ℕ} {step : List ℚ → List ℚ}
    {stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ}
    (hs : Implements n step stepM) (d : ℕ) :
    Implements n (roundFun step d) (roundMapD stepM d) := by
  intro X xs h
  exact correct_map_snapDiv (hs X xs h) d


/-! ## 3b.  The round on m4's actual packed state

`Check_matq_update_m4`'s `Step.stepProg` is a machine on the packed state
`RSt = ((n, X), (c, λ))` computing the rank-one update `X ↦ X − (λ/(1+λσ))·(Xc)(Xc)ᵀ`
(`Step.stepProg_spec`).  Composing it with the snap gives the *step-plus-snap half of one simulate
round as a `Poly` program with no hypotheses at all* — the separation oracle only has to supply the
cut vector `c` (which is the `oracle-poly` brick's job). -/

open QMCLeafB.MatQUpdate in
/-- **m4's step function is a `Poly` function** (their `stepProg`, read through `Poly`). -/
theorem poly_stepFun : Poly (fun p : Step.RSt => Step.stepFun p) := ⟨Step.stepProg⟩

open QMCLeafB.MatQUpdate in
/-- **Step + snap on the packed state**, unconditionally a `Poly` program. -/
theorem poly_round_stepFun (d : ℕ) :
    Poly (fun p : Step.RSt => (Step.stepFun p).map (snapDiv d)) := by
  have hf : Poly (fun x : Step.RSt × ℚ => snapDiv d x.2) :=
    Automatic.Poly.comp (f := fun y : ℕ × ℚ => snapDiv y.1 y.2)
      (g := fun x : Step.RSt × ℚ => (d, x.2)) poly_snapDiv
      (Automatic.Poly.pair (Automatic.Poly.const d) Automatic.Poly.snd)
  exact Automatic.Poly.list_map (f := fun (_ : Step.RSt) (q : ℚ) => snapDiv d q)
    (as := fun p : Step.RSt => Step.stepFun p) hf poly_stepFun

/-! ## 4.  The ledger on the program's state -/

/-- The snapped matrix iterate stays inside the value box (the snap contracts). -/
theorem roundMapD_value {n : ℕ} (stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ)
    {d M : ℕ} (hd : 0 < d) {X : Matrix (Fin n) (Fin n) ℚ} (hX : MatValueBounded M (stepM X)) :
    MatValueBounded M (roundMapD stepM d X) :=
  fun i j => (abs_snapDiv_le d hd (stepM X i j)).trans (hX i j)

/-- Value track: with a per-round magnitude amplification `2^γ`, `T` snapped rounds stay inside
`2^(M+γT)`. -/
theorem roundD_value_iterate {n : ℕ} (stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ)
    {d M γ : ℕ} (hd : 0 < d)
    (hstep : ∀ (t : ℕ) (X : Matrix (Fin n) (Fin n) ℚ),
      MatValueBounded (M + γ * t) X → MatValueBounded (M + γ * (t + 1)) (stepM X))
    {X₀ : Matrix (Fin n) (Fin n) ℚ} (h0 : MatValueBounded M X₀) (T : ℕ) :
    MatValueBounded (M + γ * T) (((roundMapD stepM d)^[T]) X₀) := by
  induction T with
  | zero => simpa using h0
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact roundMapD_value stepM hd (hstep T _ ih)

/-- **Height reset, on the matrix iterate**: after `T` rounds every entry has height at most
`M + γT + D`, additive in the round count — the point of snapping. -/
theorem roundD_height_iterate {n : ℕ} (stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ)
    {d D M γ : ℕ} (hd : 0 < d) (hdD : d ≤ 2 ^ D)
    (hstep : ∀ (t : ℕ) (X : Matrix (Fin n) (Fin n) ℚ),
      MatValueBounded (M + γ * t) X → MatValueBounded (M + γ * (t + 1)) (stepM X))
    {X₀ : Matrix (Fin n) (Fin n) ℚ} (h0 : MatValueBounded M X₀)
    (h0h : ∀ i j, HasHeight (X₀ i j) (M + D)) (T : ℕ) :
    ∀ i j, HasHeight ((((roundMapD stepM d)^[T]) X₀) i j) (M + γ * T + D) := by
  induction T with
  | zero => exact fun i j => (h0h i j).mono (by omega)
  | succ T ih =>
      have hv := roundD_value_iterate stepM hd hstep h0 T
      have hs : MatValueBounded (M + γ * (T + 1))
          (stepM (((roundMapD stepM d)^[T]) X₀)) := hstep T _ hv
      rw [Function.iterate_succ_apply']
      intro i j
      have := hasHeight_snapDiv (hs i j) hd hdD
      rw [roundMapD, Matrix.map_apply]
      exact this.mono (by omega)

/-- **`T` rounds of the program compute the ledger's snapped iterate.** -/
theorem round_iterate_implementsD {n : ℕ} {step : List ℚ → List ℚ}
    {stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ}
    (hs : Implements n step stepM) (d : ℕ) {X₀ : Matrix (Fin n) (Fin n) ℚ} {xs₀ : List ℚ}
    (h : MatQ.correct n X₀ xs₀) (T : ℕ) :
    MatQ.correct n (((roundMapD stepM d)^[T]) X₀) (((fun xs => roundFun step d xs)^[T]) xs₀) := by
  induction T with
  | zero => simpa using h
  | succ T ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact roundFun_implementsD hs d _ _ ih

/-- **Every entry of the program's printed state has bounded height.** -/
theorem program_entry_height {n : ℕ} {step : List ℚ → List ℚ}
    {stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ}
    (hs : Implements n step stepM) {d D M γ : ℕ} (hd : 0 < d) (hdD : d ≤ 2 ^ D)
    (hstep : ∀ (t : ℕ) (X : Matrix (Fin n) (Fin n) ℚ),
      MatValueBounded (M + γ * t) X → MatValueBounded (M + γ * (t + 1)) (stepM X))
    {X₀ : Matrix (Fin n) (Fin n) ℚ} {xs₀ : List ℚ} (h0 : MatQ.correct n X₀ xs₀)
    (h0v : MatValueBounded M X₀) (h0h : ∀ i j, HasHeight (X₀ i j) (M + D)) (T : ℕ) :
    ∀ i j : Fin n,
      HasHeight ((((fun xs => roundFun step d xs)^[T]) xs₀).getD
        ((i : ℕ) * n + (j : ℕ)) 0) (M + γ * T + D) := by
  intro i j
  have hentry : ((((fun xs => roundFun step d xs)^[T]) xs₀).getD
      ((i : ℕ) * n + (j : ℕ)) 0) = (((roundMapD stepM d)^[T]) X₀) i j :=
    (round_iterate_implementsD hs d h0 T).2 i j
  rw [hentry]
  exact roundD_height_iterate stepM hd hdD hstep h0v h0h T i j

/-- **The per-round charge, on the program's printed state.**  After `T` rounds the whole state
list occupies at most `n²(3(M+γT+D)+10)` bits — linear in the input height and in `T`, hence
polynomial in the input length.  This is the quantity `brick-sim-poly`'s `Tm2Size` ledger charges.
-/
theorem program_encode_charge {n : ℕ} {step : List ℚ → List ℚ}
    {stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ}
    (hs : Implements n step stepM) {d D M γ : ℕ} (hd : 0 < d) (hdD : d ≤ 2 ^ D)
    (hstep : ∀ (t : ℕ) (X : Matrix (Fin n) (Fin n) ℚ),
      MatValueBounded (M + γ * t) X → MatValueBounded (M + γ * (t + 1)) (stepM X))
    {X₀ : Matrix (Fin n) (Fin n) ℚ} {xs₀ : List ℚ} (h0 : MatQ.correct n X₀ xs₀)
    (h0v : MatValueBounded M X₀) (h0h : ∀ i j, HasHeight (X₀ i j) (M + D)) (T : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, (Ratio.encode
        ((((fun xs => roundFun step d xs)^[T]) xs₀).getD
          ((i : ℕ) * n + (j : ℕ)) 0)).length)
      ≤ n * n * (3 * (M + γ * T + D) + 10) := by
  have hentry : ∀ i j : Fin n,
      ((((fun xs => roundFun step d xs)^[T]) xs₀).getD ((i : ℕ) * n + (j : ℕ)) 0)
        = (((roundMapD stepM d)^[T]) X₀) i j := by
    intro i j
    exact (round_iterate_implementsD hs d h0 T).2 i j
  calc (∑ i : Fin n, ∑ j : Fin n, (Ratio.encode
        ((((fun xs => roundFun step d xs)^[T]) xs₀).getD
          ((i : ℕ) * n + (j : ℕ)) 0)).length)
      = ∑ i : Fin n, ∑ j : Fin n, (Ratio.encode ((((roundMapD stepM d)^[T]) X₀) i j)).length := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hentry i j]
    _ ≤ n * n * (3 * (M + γ * T + D) + 10) :=
        state_encode_length _ (roundD_height_iterate stepM hd hdD hstep h0v h0h T)

/-- **The dyadic case**: the same ledger at `d = 2^k` (`D = k`) is the ledger's `snapAbs` iterate. -/
theorem program_entry_height_dyadic {n : ℕ} {step : List ℚ → List ℚ}
    {stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ}
    (hs : Implements n step stepM) (k M γ : ℕ)
    (hstep : ∀ (t : ℕ) (X : Matrix (Fin n) (Fin n) ℚ),
      MatValueBounded (M + γ * t) X → MatValueBounded (M + γ * (t + 1)) (stepM X))
    {X₀ : Matrix (Fin n) (Fin n) ℚ} {xs₀ : List ℚ} (h0 : MatQ.correct n X₀ xs₀)
    (h0v : MatValueBounded M X₀) (h0h : ∀ i j, HasHeight (X₀ i j) (M + k)) (T : ℕ) :
    ∀ i j : Fin n,
      HasHeight ((((fun xs => roundFun step (2 ^ k) xs)^[T]) xs₀).getD
        ((i : ℕ) * n + (j : ℕ)) 0) (M + γ * T + k) :=
  program_entry_height hs (by positivity) (le_refl (2 ^ k)) hstep h0 h0v h0h T


/-! ## 4b.  The error track: the program's iterate against the exact iterate

The last piece of the round's specification: the snapped program's `T`-fold state is within
`δ` of the *exact* iterate `stepM^[T]`, provided the step is entrywise `L`-Lipschitz and the
grid is finer than the ledger's precision `2^{-k}`.  The scalar recursion is the ledger's
`err_le_of_step`; here it is driven by the matrix induction. -/

/-- The scalar error recursion `e ↦ L·e + ε` of the ledger. -/
def errSeq (L ε : ℚ) : ℕ → ℚ
  | 0 => 0
  | (r + 1) => L * errSeq L ε r + ε

@[simp] theorem errSeq_zero (L ε : ℚ) : errSeq L ε 0 = 0 := rfl
@[simp] theorem errSeq_succ (L ε : ℚ) (r : ℕ) : errSeq L ε (r + 1) = L * errSeq L ε r + ε := rfl

theorem errSeq_nonneg {L ε : ℚ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (r : ℕ) : 0 ≤ errSeq L ε r := by
  induction r with
  | zero => simp
  | succ r ih => rw [errSeq_succ]; positivity

/-- The ledger's `err_le_of_step`, for the explicit sequence: `e_R ≤ (R·ε)·L^R`. -/
theorem errSeq_le {L ε : ℚ} (hL : 1 ≤ L) (hε : 0 ≤ ε) (R : ℕ) :
    errSeq L ε R ≤ ((R : ℚ) * ε) * L ^ R := by
  have hLnn : (0:ℚ) ≤ L := le_trans zero_le_one hL
  have h : ∀ r, |errSeq L ε (r + 1)| ≤ L * |errSeq L ε r| + ε := by
    intro r
    rw [abs_of_nonneg (errSeq_nonneg hLnn hε (r + 1)),
      abs_of_nonneg (errSeq_nonneg hLnn hε r)]
    exact le_of_eq rfl
  have hmain := err_le_of_step (e := fun r => errSeq L ε r) hL hε h R
  rw [abs_of_nonneg (errSeq_nonneg hLnn hε R)] at hmain
  simpa using hmain

/-- **The step is entrywise `L`-Lipschitz**: one round multiplies an entrywise error by at most
`L`.  This is the hypothesis under which the snap error accumulates. -/
def EntryLipschitz {n : ℕ} (stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ)
    (L : ℚ) : Prop :=
  ∀ (X Y : Matrix (Fin n) (Fin n) ℚ) (e : ℚ), 0 ≤ e → (∀ i j, |X i j - Y i j| ≤ e) →
    ∀ i j, |stepM X i j - stepM Y i j| ≤ L * e

/-- **The matrix error induction**: after `T` rounds the program's state differs from the exact
iterate entrywise by at most the scalar recursion `errSeq L (1/d) T`. -/
theorem round_error_le_seq {n : ℕ}
    (stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ)
    {d : ℕ} (hd : 0 < d) {L : ℚ} (hL : 1 ≤ L) (hlip : EntryLipschitz stepM L)
    (X₀ : Matrix (Fin n) (Fin n) ℚ) :
    ∀ (T : ℕ) (i j), |(((roundMapD stepM d)^[T]) X₀) i j - ((stepM^[T]) X₀) i j|
      ≤ errSeq L (1 / (d:ℚ)) T := by
  have hLnn : (0:ℚ) ≤ L := le_trans zero_le_one hL
  have hε : (0:ℚ) ≤ 1 / (d:ℚ) := by positivity
  intro T
  induction T with
  | zero => intro i j; simp
  | succ T ih =>
      intro i j
      have he : (0:ℚ) ≤ errSeq L (1 / (d:ℚ)) T := errSeq_nonneg hLnn hε T
      have h1 : |roundMapD stepM d (((roundMapD stepM d)^[T]) X₀) i j
          - stepM (((roundMapD stepM d)^[T]) X₀) i j| ≤ 1 / (d:ℚ) := by
        rw [roundMapD, Matrix.map_apply]
        exact snapDiv_error d hd _
      have h2 : |stepM (((roundMapD stepM d)^[T]) X₀) i j
          - stepM ((stepM^[T]) X₀) i j| ≤ L * errSeq L (1 / (d:ℚ)) T :=
        hlip _ _ _ he ih i j
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', errSeq_succ]
      calc |roundMapD stepM d (((roundMapD stepM d)^[T]) X₀) i j - stepM ((stepM^[T]) X₀) i j|
          = |(roundMapD stepM d (((roundMapD stepM d)^[T]) X₀) i j
              - stepM (((roundMapD stepM d)^[T]) X₀) i j)
            + (stepM (((roundMapD stepM d)^[T]) X₀) i j - stepM ((stepM^[T]) X₀) i j)| := by
            ring_nf
        _ ≤ |roundMapD stepM d (((roundMapD stepM d)^[T]) X₀) i j
              - stepM (((roundMapD stepM d)^[T]) X₀) i j|
            + |stepM (((roundMapD stepM d)^[T]) X₀) i j - stepM ((stepM^[T]) X₀) i j| :=
            abs_add_le _ _
        _ ≤ 1 / (d:ℚ) + L * errSeq L (1 / (d:ℚ)) T := add_le_add h1 h2
        _ = L * errSeq L (1 / (d:ℚ)) T + 1 / (d:ℚ) := by ring

/-- **The program's state is within `T·L^T/d` of the exact iterate**, entrywise. -/
theorem round_error_iterate {n : ℕ}
    (stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ)
    {d : ℕ} (hd : 0 < d) {L : ℚ} (hL : 1 ≤ L) (hlip : EntryLipschitz stepM L)
    (X₀ : Matrix (Fin n) (Fin n) ℚ) (T : ℕ) :
    ∀ i j, |(((roundMapD stepM d)^[T]) X₀) i j - ((stepM^[T]) X₀) i j|
      ≤ ((T : ℚ) * (1 / (d:ℚ))) * L ^ T := by
  have hLnn : (0:ℚ) ≤ L := le_trans zero_le_one hL
  have hε : (0:ℚ) ≤ 1 / (d:ℚ) := by positivity
  intro i j
  refine (round_error_le_seq stepM hd hL hlip X₀ T i j).trans ?_
  have hmain := errSeq_le (L := L) (ε := 1 / (d:ℚ)) hL hε T
  simpa [mul_assoc] using hmain

/-- **The snap error is inside the tolerated width.**  If the grid is at least as fine as
`2^{-k}` and the ledger's precision budget `2·T·L^T ≤ δ·2^k` holds, then after `T` rounds the
program's state is entrywise within `δ` of the exact iterate — `snap_error_budget` absorbed the
factor `T·L^T`, leaving `δ/2`. -/
theorem round_error_budget {n : ℕ}
    (stepM : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ)
    {d k : ℕ} (hd : 0 < d) (hk : 2 ^ k ≤ d) {L δ : ℚ} (hL : 1 ≤ L) (hδ : 0 < δ)
    (hlip : EntryLipschitz stepM L) (X₀ : Matrix (Fin n) (Fin n) ℚ) (T : ℕ)
    (hbudget : 2 * (T : ℚ) * L ^ T ≤ δ * 2 ^ k) :
    ∀ i j, |(((roundMapD stepM d)^[T]) X₀) i j - ((stepM^[T]) X₀) i j| ≤ δ := by
  have hLnn : (0:ℚ) ≤ L := le_trans zero_le_one hL
  have hkpos : (0:ℚ) < (d:ℚ) := by exact_mod_cast hd
  have h2k : (0:ℚ) < 2 ^ k := by positivity
  have hdk : (1:ℚ) / (d:ℚ) ≤ 1 / 2 ^ k := by
    apply div_le_div_of_nonneg_left (by norm_num) h2k (by exact_mod_cast hk)
  have hTL : (0:ℚ) ≤ (T : ℚ) * L ^ T := by positivity
  have hhalf : (T : ℚ) * (1 / 2 ^ k) * L ^ T ≤ δ / 2 := by
    have h := snap_error_budget (T := T) (L := L) (δ := δ) (k := k) hδ hbudget
    calc (T : ℚ) * (1 / 2 ^ k) * L ^ T = (T : ℚ) / 2 ^ k * L ^ T := by ring
      _ ≤ δ / 2 := h
  have hmono : (T : ℚ) * (1 / (d:ℚ)) * L ^ T ≤ (T : ℚ) * (1 / 2 ^ k) * L ^ T := by
    have h1 : (0:ℚ) ≤ (T : ℚ) := Nat.cast_nonneg T
    have h2 : (0:ℚ) ≤ L ^ T := pow_nonneg hLnn T
    nlinarith [hdk, h1, h2]
  intro i j
  have hfin : (T : ℚ) * (1 / (d:ℚ)) * L ^ T ≤ δ := by linarith
  exact (round_error_iterate stepM hd hL hlip X₀ T i j).trans hfin

/-! ## 5.  Axiom audit -/

#print axioms snapDiv_two_pow
#print axioms poly_snapDiv
#print axioms snapDiv_error
#print axioms hasHeight_snapDiv
#print axioms hasHeight_snapDiv_two_pow
#print axioms poly_snapList
#print axioms correct_map_snapAbs
#print axioms poly_roundFunSep_packed
#print axioms roundFun_implementsD
#print axioms round_iterate_implementsD
#print axioms program_entry_height
#print axioms program_encode_charge
#print axioms program_entry_height_dyadic
#print axioms round_error_iterate
#print axioms round_error_budget
#print axioms poly_stepFun
#print axioms poly_round_stepFun

end QMCLeafB.RoundPolySnap


