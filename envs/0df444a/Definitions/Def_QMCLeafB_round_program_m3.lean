-- Prove2me | Definitions.Def_QMCLeafB_round_program_m3
-- name    : QMCLeafB_round_program_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:21:54.183929+00:00
-- url     : https://prove2.me/theorems/dad187ff-ca9e-481f-9ad7-e5e48b425a15
-- title:
--   QMCLeafB round_program_m3
-- statement:
--   # leaf B phase 13 — brick `round-program` (swarm `smw17fqzz`, member m3, direction d1)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_sizes_profile_m7
import Definitions.Def_QMCLeafB_round_poly_snap_m3
import Definitions.Def_QMCLeafB_matq_update_m4
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_sim_poly_m4
/-
# leaf B phase 13 — brick `round-program` (swarm `smw17fqzz`, member m3, direction d1)

## What this file is

`QMCLeafB.VerdictSound.solution_of_loop_via_runData` needs one `Poly` round map on a packed state.
The round is

    oracle  →  branch (ok: freeze / cut: Sherman–Morrison update)  →  dyadic snap  →  record

Everything except the separation oracle was already on the shelf:
`RoundPolySnap.poly_round_stepFun` gives update + snap as a hypothesis-free `Poly` program at a
*numeral* grid, and `SizesProfile.poly_runPivN` gives the (clipped + snapped) LDLᵀ pivot descent —
which is the oracle's PSD test — as a hypothesis-free `Poly` program, but only at **numeral**
parameters `M D d`.

That numeral restriction is the one documented open obligation of `oracle-poly`
(`Check_oracle_poly_m1`, §"What is proved here and what is not"): a round machine is *fixed*, so no
parameter of it may be a numeral chosen per input.  §2-§4 below remove the restriction: the clip box
is taken at a **rational** bound `mu : ℚ` carried by the state (so `2^M` is never computed — that map
is not `Poly`), and the grid `d : ℕ` is carried by the state too.  The result is

  * **`poly_runPivL`** — the normalised pivot descent is a `Poly` program on `(mu, d, block)` with
    **no hypothesis at all**,

which is exactly what a state-level round needs.

## Contents

* §1 `σ = RSt`, the packed round state, its projections, its constructor, and the verdict bit.
* §2 clip into a rational box + snap, as `Poly` functions.
* §3 the height ledger: one normalised step leaves every entry of the continuation of height
  `≤ L + d` whenever the box bound has height `≤ L` (`HasHeight mu L`) — no hypothesis on the operand.
  Together with the (copied) width/height arithmetic `SizesProfile.enc_st_le_monomial` this gives the
  descent's size monomial `128·(2(3(L+d)+10)+1)·(N+1)²`.
* §4 `pivStepR`/`pivStepL`, the descent `runPivL`, and **`poly_runPivL`** (no hypotheses).
* §5 axiom audit.

No `sorry`, no `axiom`.  Standard three axioms throughout.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.RoundProgram

open QMCLeafB.PivotProgram
open QMCLeafB.SizesProfile

/-! ## 1.  `σ`, the packed round state

| field | meaning |
|---|---|
| `n`      | the dimension of the SDP (`wMatrix G` is `n × n`, `n = G.n`) |
| `A`      | row-major code of `wMatrix G`, `n*n` entries |
| `X`      | row-major code of the current primal shape matrix, `n*n` entries |
| `t`      | the threshold of the bracket |
| `mu`     | the entry box bound of the pivot descent (a **rational**, so it can be input data) |
| `d`      | the grid denominator `d` of the round's snap (`snapDiv d`) |
| `oks`    | the per-round `ok` record as `0`/`1` rationals (so `verdict` is a `List.sum`) |
| `rec`    | the per-round payload: for round `k`, the cut normal (resp. `[]`) |

`oks` is a `List ℚ` and not a `List Bool` on purpose: `List.sum` is a compiled program
(`PivotProgram.poly_rat_sum`), so `verdict` is two `Poly` steps, while `List.any` would need a new
fold; `0`/`1` is also the natural rational-tape convention.
-/

/-- **`σ`, the round state.** -/
abbrev RSt : Type := ((ℕ × List ℚ) × (List ℚ × (ℚ × ℚ))) × ((ℕ × List Bool) × List ℚ)

/-- `n` — the SDP dimension. -/
def stN (s : RSt) : ℕ := s.1.1.1
/-- `A` — row-major code of `wMatrix G`. -/
def stA (s : RSt) : List ℚ := s.1.1.2
/-- `X` — row-major code of the current primal shape. -/
def stX (s : RSt) : List ℚ := s.1.2.1
/-- `t` — the bracket threshold. -/
def stT (s : RSt) : ℚ := s.1.2.2.1
/-- `mu` — the entry box bound of the pivot descent. -/
def stMu (s : RSt) : ℚ := s.1.2.2.2
/-- `d` — the grid denominator of the round's snap. -/
def stD (s : RSt) : ℕ := s.2.1.1
/-- `oks` — the per-round `ok` flags.  A `List Bool` and not a `List ℚ`: one fuel bit costs exactly
`3` encoded bits (`encodeBool`), and one `ok` flag costs exactly `3` too, so appending one flag and
consuming one fuel bit is *exactly length-neutral*.  This is what makes the closing stroke's `hsize`
(the forward invariance of a polynomial ball) satisfiable at all; with `List ℚ` flags (8 bits each)
the state grows by 14 bits per round and no polynomial ball is forward invariant. -/
def stOks (s : RSt) : List Bool := s.2.1.2
/-- `rec` — the per-round cut payload. -/
def stRec (s : RSt) : List ℚ := s.2.2

/-- The state constructor. -/
def mkSt (n : ℕ) (A X : List ℚ) (t mu : ℚ) (d : ℕ) (oks : List Bool) (rec : List ℚ) : RSt :=
  (((n, A), (X, (t, mu))), ((d, oks), rec))

@[simp] theorem mkSt_stN (n : ℕ) (A X : List ℚ) (t mu : ℚ) (d : ℕ) (oks : List Bool) (rec : List ℚ) :
    stN (mkSt n A X t mu d oks rec) = n := rfl
@[simp] theorem mkSt_stA (n : ℕ) (A X : List ℚ) (t mu : ℚ) (d : ℕ) (oks : List Bool) (rec : List ℚ) :
    stA (mkSt n A X t mu d oks rec) = A := rfl
@[simp] theorem mkSt_stX (n : ℕ) (A X : List ℚ) (t mu : ℚ) (d : ℕ) (oks : List Bool) (rec : List ℚ) :
    stX (mkSt n A X t mu d oks rec) = X := rfl
@[simp] theorem mkSt_stT (n : ℕ) (A X : List ℚ) (t mu : ℚ) (d : ℕ) (oks : List Bool) (rec : List ℚ) :
    stT (mkSt n A X t mu d oks rec) = t := rfl
@[simp] theorem mkSt_stMu (n : ℕ) (A X : List ℚ) (t mu : ℚ) (d : ℕ) (oks : List Bool) (rec : List ℚ) :
    stMu (mkSt n A X t mu d oks rec) = mu := rfl
@[simp] theorem mkSt_stD (n : ℕ) (A X : List ℚ) (t mu : ℚ) (d : ℕ) (oks : List Bool) (rec : List ℚ) :
    stD (mkSt n A X t mu d oks rec) = d := rfl
@[simp] theorem mkSt_stOks (n : ℕ) (A X : List ℚ) (t mu : ℚ) (d : ℕ) (oks : List Bool) (rec : List ℚ) :
    stOks (mkSt n A X t mu d oks rec) = oks := rfl
@[simp] theorem mkSt_stRec (n : ℕ) (A X : List ℚ) (t mu : ℚ) (d : ℕ) (oks : List Bool) (rec : List ℚ) :
    stRec (mkSt n A X t mu d oks rec) = rec := rfl

/-! ### 1.1  The projections as `Poly` facts -/

@[fun_prop] theorem poly_stN : Poly stN := by unfold stN; fun_prop
@[fun_prop] theorem poly_stA : Poly stA := by unfold stA; fun_prop
@[fun_prop] theorem poly_stX : Poly stX := by unfold stX; fun_prop
@[fun_prop] theorem poly_stT : Poly stT := by unfold stT; fun_prop
@[fun_prop] theorem poly_stMu : Poly stMu := by unfold stMu; fun_prop
@[fun_prop] theorem poly_stD : Poly stD := by unfold stD; fun_prop
@[fun_prop] theorem poly_stOks : Poly stOks := by unfold stOks; fun_prop
@[fun_prop] theorem poly_stRec : Poly stRec := by unfold stRec; fun_prop

/-! ### 1.2  The verdict bit

`verdict` is `decide (0 < (stOks s).sum)`: `true` exactly when some recorded round reported `ok`.
This is `SimLoop.anyOk` in the `0`/`1` representation.
-/

/-- **The verdict bit of the round program.** -/
def verdict (s : RSt) : Bool := decide (0 < ((stOks s).filter id).length)

theorem poly_verdict : Poly verdict := by
  unfold verdict
  have hfilt : Poly (fun s : RSt => (stOks s).filter id) :=
    Poly.list_filter (f := fun (_ : RSt) (b : Bool) => b) (as := stOks)
      (by fun_prop : Poly (fun x : RSt × Bool => x.2)) poly_stOks
  have hlen : Poly (fun s : RSt => ((stOks s).filter id).length) :=
    Poly.comp (f := (List.length : List Bool → ℕ)) (g := fun s : RSt => (stOks s).filter id)
      (Poly.list_length (α := Bool)) hfilt
  exact Poly.nat_lt_comp (Automatic.Poly.const (0 : ℕ)) hlen

/-! ## 2.  Clip into a rational box, then snap -/

/-- The box test `-mu ≤ q ≤ mu` at a rational bound, as a `Bool`. -/
def inBoxR (mu q : ℚ) : Bool := decide (-mu ≤ q) && decide (q ≤ mu)

/-- **The clip into the rational box `|q| ≤ mu`**: the identity inside, `0` outside. -/
def clipRat (mu q : ℚ) : ℚ := if inBoxR mu q then q else 0

/-- **One normalised entry**: clip into the box, then snap onto the grid `1/d`. -/
def nrmQ (mu : ℚ) (d : ℕ) (q : ℚ) : ℚ := QMCLeafB.RoundPolySnap.snapDiv d (clipRat mu q)

theorem inBoxR_iff {mu q : ℚ} : inBoxR mu q = true ↔ -mu ≤ q ∧ q ≤ mu := by
  unfold inBoxR
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

theorem clipRat_of_inBox {mu q : ℚ} (h : inBoxR mu q = true) : clipRat mu q = q := by
  unfold clipRat
  rw [h]
  simp

theorem abs_clipRat_le (mu q : ℚ) : |clipRat mu q| ≤ |mu| := by
  unfold clipRat
  cases h : inBoxR mu q with
  | true =>
      obtain ⟨h1, h2⟩ := inBoxR_iff.mp h
      have h3 : |q| ≤ mu := abs_le.mpr ⟨h1, h2⟩
      exact h3.trans (le_abs_self mu)
  | false => simp

/-- `|q| ≤ |q.num|`: the denominator is a positive integer. -/
theorem abs_le_num (q : ℚ) : |q| ≤ |((q.num : ℚ))| := by
  have hden : (1 : ℚ) ≤ (q.den : ℚ) := by exact_mod_cast q.den_pos
  have hq : |q| = |((q.num : ℚ))| / ((q.den : ℚ)) := by
    conv_lhs => rw [← Rat.num_div_den q]
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (q.den : ℚ))]
  rw [hq]
  exact div_le_self (abs_nonneg _) hden

/-- A rational of height `≤ L` is at most `2^L` in absolute value. -/
theorem abs_le_two_pow {q : ℚ} {L : ℕ} (h : HasHeight q L) : |q| ≤ (2 : ℚ) ^ L := by
  have h1 : |q| ≤ |((q.num : ℚ))| := abs_le_num q
  have h2 : |((q.num : ℚ))| = ((|q.num| : ℤ) : ℚ) := by push_cast; ring
  have h3 : ((|q.num| : ℤ) : ℚ) ≤ (((2 : ℤ) ^ L : ℤ) : ℚ) := by exact_mod_cast h.1
  have h4 : (((2 : ℤ) ^ L : ℤ) : ℚ) = (2 : ℚ) ^ L := by push_cast; ring
  calc |q| ≤ |((q.num : ℚ))| := h1
    _ = ((|q.num| : ℤ) : ℚ) := h2
    _ ≤ (((2 : ℤ) ^ L : ℤ) : ℚ) := h3
    _ = (2 : ℚ) ^ L := h4

/-- `d ≤ 2^d` — the trivial grid exponent, so the state's own `d` serves as its own exponent. -/
theorem self_le_two_pow : ∀ d : ℕ, d ≤ 2 ^ d
  | 0 => by simp
  | (k + 1) => by
      have hk : k ≤ 2 ^ k := self_le_two_pow k
      have h1 : 0 < 2 ^ k := Nat.two_pow_pos k
      have h2 : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      omega

/-- **The height reset.**  A clipped and snapped entry has height `L + D` whenever the box bound has
height `L` and the grid denominator is at most `2^D` — no hypothesis on the operand. -/
theorem hasHeight_nrmQ {mu : ℚ} {L : ℕ} (hmu : HasHeight mu L) {d D : ℕ} (hdD : d ≤ 2 ^ D)
    (q : ℚ) : HasHeight (nrmQ mu d q) (L + D) := by
  unfold nrmQ
  have hval : |clipRat mu q| ≤ (2 : ℚ) ^ L := (abs_clipRat_le mu q).trans (abs_le_two_pow hmu)
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    rw [show (L + D) = L + D from rfl]
    have h0 : QMCLeafB.RoundPolySnap.snapDiv 0 (clipRat mu q) = 0 := by
      unfold QMCLeafB.RoundPolySnap.snapDiv QMCLeafB.RoundPolySnap.snapTrunc
      simp
    rw [h0]
    exact HasHeight.zero (L + D)
  · exact QMCLeafB.RoundPolySnap.hasHeight_snapDiv (M := L) (D := D) (d := d) hval hd hdD

/-! ### 2.1  The row/accumulator normalisation, and its `Poly` facts -/

/-- Normalise a row. -/
def nrmRow (mu : ℚ) (d : ℕ) (v : List ℚ) : List ℚ := v.map (nrmQ mu d)

/-- Normalise a block of rows. -/
def nrmRows (mu : ℚ) (d : ℕ) (rows : Rows) : Rows := rows.map (nrmRow mu d)

/-- Normalise one accumulator entry `(pivot, head row)`. -/
def nrmPair (mu : ℚ) (d : ℕ) (p : ℚ × List ℚ) : ℚ × List ℚ := (nrmQ mu d p.1, nrmRow mu d p.2)

/-- Normalise the accumulator. -/
def nrmAcc (mu : ℚ) (d : ℕ) (acc : Acc) : Acc := acc.map (nrmPair mu d)

/-- Normalise the whole descent state. -/
def nrmSt (mu : ℚ) (d : ℕ) (st : St) : St := (nrmRows mu d st.1, nrmAcc mu d st.2)

theorem nrmRow_length (mu : ℚ) (d : ℕ) (v : List ℚ) : (nrmRow mu d v).length = v.length := by
  simp [nrmRow]

theorem nrmRows_length (mu : ℚ) (d : ℕ) (rows : Rows) :
    (nrmRows mu d rows).length = rows.length := by
  simp [nrmRows]

theorem nrmAcc_length (mu : ℚ) (d : ℕ) (acc : Acc) : (nrmAcc mu d acc).length = acc.length := by
  simp [nrmAcc]

theorem nrmSt_fst (mu : ℚ) (d : ℕ) (st : St) : (nrmSt mu d st).1 = nrmRows mu d st.1 := rfl
theorem nrmSt_snd (mu : ℚ) (d : ℕ) (st : St) : (nrmSt mu d st).2 = nrmAcc mu d st.2 := rfl

theorem poly_inBoxR : Poly (fun p : ℚ × ℚ => inBoxR p.1 p.2) := by
  unfold inBoxR
  fun_prop

theorem poly_clipRat : Poly (fun p : ℚ × ℚ => clipRat p.1 p.2) := by
  unfold clipRat
  exact Poly.ite poly_inBoxR Poly.snd (Automatic.Poly.const 0)

theorem poly_nrmQ : Poly (fun p : (ℚ × ℕ) × ℚ => nrmQ p.1.1 p.1.2 p.2) := by
  unfold nrmQ
  have hclip : Poly (fun p : (ℚ × ℕ) × ℚ => clipRat p.1.1 p.2) :=
    Poly.comp (f := fun y : ℚ × ℚ => clipRat y.1 y.2)
      (g := fun p : (ℚ × ℕ) × ℚ => (p.1.1, p.2)) poly_clipRat
      (Poly.pair (f := fun p : (ℚ × ℕ) × ℚ => p.1.1)
        (g := fun p : (ℚ × ℕ) × ℚ => p.2) (by fun_prop) (by fun_prop))
  exact Poly.comp (f := fun y : ℕ × ℚ => QMCLeafB.RoundPolySnap.snapDiv y.1 y.2)
    (g := fun p : (ℚ × ℕ) × ℚ => (p.1.2, clipRat p.1.1 p.2))
    QMCLeafB.RoundPolySnap.poly_snapDiv
    (Poly.pair (f := fun p : (ℚ × ℕ) × ℚ => p.1.2)
      (g := fun p : (ℚ × ℕ) × ℚ => clipRat p.1.1 p.2) (by fun_prop) hclip)

theorem poly_nrmRow : Poly (fun p : (ℚ × ℕ) × List ℚ => nrmRow p.1.1 p.1.2 p.2) := by
  unfold nrmRow
  have hf : Poly (fun x : ((ℚ × ℕ) × List ℚ) × ℚ => nrmQ x.1.1.1 x.1.1.2 x.2) :=
    Poly.comp (f := fun y : (ℚ × ℕ) × ℚ => nrmQ y.1.1 y.1.2 y.2)
      (g := fun x : ((ℚ × ℕ) × List ℚ) × ℚ => (x.1.1, x.2)) poly_nrmQ
      (Poly.pair (f := fun x : ((ℚ × ℕ) × List ℚ) × ℚ => x.1.1)
        (g := fun x : ((ℚ × ℕ) × List ℚ) × ℚ => x.2) (by fun_prop) (by fun_prop))
  exact Poly.list_map (f := fun (p : (ℚ × ℕ) × List ℚ) (q : ℚ) => nrmQ p.1.1 p.1.2 q)
    (as := fun p : (ℚ × ℕ) × List ℚ => p.2) hf (by fun_prop)

theorem poly_nrmRows : Poly (fun p : (ℚ × ℕ) × Rows => nrmRows p.1.1 p.1.2 p.2) := by
  unfold nrmRows
  have hf : Poly (fun x : ((ℚ × ℕ) × Rows) × List ℚ => nrmRow x.1.1.1 x.1.1.2 x.2) :=
    Poly.comp (f := fun y : (ℚ × ℕ) × List ℚ => nrmRow y.1.1 y.1.2 y.2)
      (g := fun x : ((ℚ × ℕ) × Rows) × List ℚ => (x.1.1, x.2)) poly_nrmRow
      (Poly.pair (f := fun x : ((ℚ × ℕ) × Rows) × List ℚ => x.1.1)
        (g := fun x : ((ℚ × ℕ) × Rows) × List ℚ => x.2) (by fun_prop) (by fun_prop))
  exact Poly.list_map (f := fun (p : (ℚ × ℕ) × Rows) (v : List ℚ) => nrmRow p.1.1 p.1.2 v)
    (as := fun p : (ℚ × ℕ) × Rows => p.2) hf (by fun_prop)

theorem poly_nrmPair : Poly (fun p : (ℚ × ℕ) × (ℚ × List ℚ) => nrmPair p.1.1 p.1.2 p.2) := by
  unfold nrmPair
  have h1 : Poly (fun p : (ℚ × ℕ) × (ℚ × List ℚ) => nrmQ p.1.1 p.1.2 p.2.1) :=
    Poly.comp (f := fun y : (ℚ × ℕ) × ℚ => nrmQ y.1.1 y.1.2 y.2)
      (g := fun p : (ℚ × ℕ) × (ℚ × List ℚ) => (p.1, p.2.1)) poly_nrmQ
      (Poly.pair (f := fun p : (ℚ × ℕ) × (ℚ × List ℚ) => p.1)
        (g := fun p : (ℚ × ℕ) × (ℚ × List ℚ) => p.2.1) (by fun_prop) (by fun_prop))
  have h2 : Poly (fun p : (ℚ × ℕ) × (ℚ × List ℚ) => nrmRow p.1.1 p.1.2 p.2.2) :=
    Poly.comp (f := fun y : (ℚ × ℕ) × List ℚ => nrmRow y.1.1 y.1.2 y.2)
      (g := fun p : (ℚ × ℕ) × (ℚ × List ℚ) => (p.1, p.2.2)) poly_nrmRow
      (Poly.pair (f := fun p : (ℚ × ℕ) × (ℚ × List ℚ) => p.1)
        (g := fun p : (ℚ × ℕ) × (ℚ × List ℚ) => p.2.2) (by fun_prop) (by fun_prop))
  exact Poly.pair h1 h2

theorem poly_nrmAcc : Poly (fun p : (ℚ × ℕ) × Acc => nrmAcc p.1.1 p.1.2 p.2) := by
  unfold nrmAcc
  have hf : Poly (fun x : ((ℚ × ℕ) × Acc) × (ℚ × List ℚ) => nrmPair x.1.1.1 x.1.1.2 x.2) :=
    Poly.comp (f := fun y : (ℚ × ℕ) × (ℚ × List ℚ) => nrmPair y.1.1 y.1.2 y.2)
      (g := fun x : ((ℚ × ℕ) × Acc) × (ℚ × List ℚ) => (x.1.1, x.2)) poly_nrmPair
      (Poly.pair (f := fun x : ((ℚ × ℕ) × Acc) × (ℚ × List ℚ) => x.1.1)
        (g := fun x : ((ℚ × ℕ) × Acc) × (ℚ × List ℚ) => x.2) (by fun_prop) (by fun_prop))
  exact Poly.list_map (f := fun (p : (ℚ × ℕ) × Acc) (q : ℚ × List ℚ) => nrmPair p.1.1 p.1.2 q)
    (as := fun p : (ℚ × ℕ) × Acc => p.2) hf (by fun_prop)

theorem poly_nrmSt : Poly (fun p : (ℚ × ℕ) × St => nrmSt p.1.1 p.1.2 p.2) := by
  unfold nrmSt
  have h1 : Poly (fun p : (ℚ × ℕ) × St => nrmRows p.1.1 p.1.2 p.2.1) :=
    Poly.comp (f := fun y : (ℚ × ℕ) × Rows => nrmRows y.1.1 y.1.2 y.2)
      (g := fun p : (ℚ × ℕ) × St => (p.1, p.2.1)) poly_nrmRows
      (Poly.pair (f := fun p : (ℚ × ℕ) × St => p.1)
        (g := fun p : (ℚ × ℕ) × St => p.2.1) (by fun_prop) (by fun_prop))
  have h2 : Poly (fun p : (ℚ × ℕ) × St => nrmAcc p.1.1 p.1.2 p.2.2) :=
    Poly.comp (f := fun y : (ℚ × ℕ) × Acc => nrmAcc y.1.1 y.1.2 y.2)
      (g := fun p : (ℚ × ℕ) × St => (p.1, p.2.2)) poly_nrmAcc
      (Poly.pair (f := fun p : (ℚ × ℕ) × St => p.1)
        (g := fun p : (ℚ × ℕ) × St => p.2.2) (by fun_prop) (by fun_prop))
  exact Poly.pair h1 h2

/-! ## 3.  The height and width ledger -/

theorem nrmRow_height {mu : ℚ} {L : ℕ} (hmu : HasHeight mu L) {d D : ℕ} (hdD : d ≤ 2 ^ D)
    (v : List ℚ) : ∀ q ∈ nrmRow mu d v, HasHeight q (L + D) := by
  intro q hq
  simp only [nrmRow, List.mem_map] at hq
  obtain ⟨r, _, rfl⟩ := hq
  exact hasHeight_nrmQ hmu hdD r

theorem nrmRows_height {mu : ℚ} {L : ℕ} (hmu : HasHeight mu L) {d D : ℕ} (hdD : d ≤ 2 ^ D)
    (rows : Rows) : RowsHeight (nrmRows mu d rows) (L + D) :=
  fun _ hv => by
    simp only [nrmRows, List.mem_map] at hv
    obtain ⟨w, _, rfl⟩ := hv
    exact nrmRow_height hmu hdD w

theorem nrmAcc_height {mu : ℚ} {L : ℕ} (hmu : HasHeight mu L) {d D : ℕ} (hdD : d ≤ 2 ^ D)
    (acc : Acc) : AccHeight (nrmAcc mu d acc) (L + D) := by
  intro p hp
  simp only [nrmAcc, List.mem_map] at hp
  obtain ⟨r, _, rfl⟩ := hp
  exact ⟨hasHeight_nrmQ hmu hdD _, nrmRow_height hmu hdD _⟩

theorem nrmRows_width (mu : ℚ) (d : ℕ) {rows : Rows} {K : ℕ} (h : RowsWidth rows K) :
    RowsWidth (nrmRows mu d rows) K := by
  intro v hv
  simp only [nrmRows, List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  rw [nrmRow_length]
  exact h w hw

theorem nrmAcc_width (mu : ℚ) (d : ℕ) {acc : Acc} {K : ℕ} (h : AccWidth acc K) :
    AccWidth (nrmAcc mu d acc) K := by
  intro p hp
  simp only [nrmAcc, List.mem_map] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  simp only [nrmPair, nrmRow_length]
  exact h r hr

theorem nrmAcc_cons_width {mu : ℚ} {d : ℕ} {a : ℚ × List ℚ} {acc : Acc} {N : ℕ}
    (ha : a.2.length ≤ N) (h : AccWidth acc N) : AccWidth (nrmAcc mu d (a :: acc)) N := by
  intro p hp
  have he : nrmAcc mu d (a :: acc) = nrmPair mu d a :: nrmAcc mu d acc := by
    simp [nrmAcc]
  rw [he] at hp
  rcases List.mem_cons.mp hp with hmem | hmem
  · rw [hmem]
    simp only [nrmPair, nrmRow_length]
    exact ha
  · exact nrmAcc_width mu d h p hmem

/-! ## 4.  The state-dependent normalised descent -/

/-- `drop` continuation, normalised (state-dependent grid and box). -/
def brDropR (mu : ℚ) (d : ℕ) (st : St) : Ans ⊕ St :=
  Sum.inr (nrmRows mu d (dropRows st.1), nrmAcc mu d st.2)

/-- `schur` continuation, normalised (state-dependent grid and box). -/
def brSchurR (mu : ℚ) (d : ℕ) (st : St) : Ans ⊕ St :=
  Sum.inr (nrmRows mu d (schurRows st.1),
    nrmAcc mu d ((piv st.1, headTail st.1) :: st.2))

/-- **The state-dependent normalised descent step.** -/
def pivStepR (mu : ℚ) (d : ℕ) (st : St) : Ans ⊕ St :=
  if st.1.isEmpty then brStop st
  else if piv st.1 < 0 then brNeg st
  else if piv st.1 = 0 then (if rowSq (headTail st.1) = 0 then brDropR mu d st else brZero st)
  else brSchurR mu d st

/-- **The descent loop's input**: the parameters paired with the block. -/
abbrev LSt : Type := (ℚ × ℕ) × St

/-- The stop branch at the loop's input type. -/
def brStopL (_ : LSt) : Ans ⊕ LSt := Sum.inl (false, [])
/-- The negative-pivot branch. -/
def brNegL (p : LSt) : Ans ⊕ LSt := Sum.inl (true, negWitness p.2.1)
/-- The zero-pivot-with-nonzero-row-squares branch. -/
def brZeroL (p : LSt) : Ans ⊕ LSt := Sum.inl (true, zeroWitness p.2.1)
/-- The drop continuation. -/
def brDropL (p : LSt) : Ans ⊕ LSt :=
  Sum.inr (p.1, (nrmRows p.1.1 p.1.2 (dropRows p.2.1), nrmAcc p.1.1 p.1.2 p.2.2))
/-- The Schur continuation. -/
def brSchurL (p : LSt) : Ans ⊕ LSt :=
  Sum.inr (p.1, (nrmRows p.1.1 p.1.2 (schurRows p.2.1),
    nrmAcc p.1.1 p.1.2 ((piv p.2.1, headTail p.2.1) :: p.2.2)))

/-- **One descent step at the loop's input type.** -/
def pivStepL (p : LSt) : Ans ⊕ LSt :=
  if p.2.1.isEmpty then brStopL p
  else if piv p.2.1 < 0 then brNegL p
  else if piv p.2.1 = 0 then (if rowSq (headTail p.2.1) = 0 then brDropL p else brZeroL p)
  else brSchurL p

theorem pivStepL_def (p : LSt) :
    pivStepL p =
      (if p.2.1.isEmpty then brStopL p
      else if piv p.2.1 < 0 then brNegL p
      else if piv p.2.1 = 0 then (if rowSq (headTail p.2.1) = 0 then brDropL p else brZeroL p)
      else brSchurL p) := rfl

/-! ### 4.1  `Poly` of the branches and the step -/

theorem poly_brStopL : Poly brStopL := by
  unfold brStopL
  exact QMCLeafB.PolyLoop.poly_sumInl_comp (Automatic.Poly.const (false, ([] : List ℚ)))

theorem poly_brNegL : Poly brNegL := by
  unfold brNegL
  have h : Poly (fun p : LSt => negWitness p.2.1) :=
    Poly.comp (f := negWitness) (g := fun p : LSt => p.2.1) poly_negWitness (by fun_prop)
  exact QMCLeafB.PolyLoop.poly_sumInl_comp
    (Poly.pair (f := fun p : LSt => true) (g := fun p : LSt => negWitness p.2.1)
      (Automatic.Poly.const true) h)

theorem poly_brZeroL : Poly brZeroL := by
  unfold brZeroL
  have h : Poly (fun p : LSt => zeroWitness p.2.1) :=
    Poly.comp (f := zeroWitness) (g := fun p : LSt => p.2.1) poly_zeroWitness (by fun_prop)
  exact QMCLeafB.PolyLoop.poly_sumInl_comp
    (Poly.pair (f := fun p : LSt => true) (g := fun p : LSt => zeroWitness p.2.1)
      (Automatic.Poly.const true) h)

theorem poly_brDropL : Poly brDropL := by
  have h1 : Poly (fun p : LSt => nrmRows p.1.1 p.1.2 (dropRows p.2.1)) :=
    Poly.comp (f := fun y : (ℚ × ℕ) × Rows => nrmRows y.1.1 y.1.2 y.2)
      (g := fun p : LSt => (p.1, dropRows p.2.1)) poly_nrmRows
      (Poly.pair (f := fun p : LSt => p.1) (g := fun p : LSt => dropRows p.2.1) (by fun_prop)
        (Poly.comp (f := dropRows) (g := fun p : LSt => p.2.1) poly_dropRows (by fun_prop)))
  have h2 : Poly (fun p : LSt => nrmAcc p.1.1 p.1.2 p.2.2) :=
    Poly.comp (f := fun y : (ℚ × ℕ) × Acc => nrmAcc y.1.1 y.1.2 y.2)
      (g := fun p : LSt => (p.1, p.2.2)) poly_nrmAcc
      (Poly.pair (f := fun p : LSt => p.1) (g := fun p : LSt => p.2.2) (by fun_prop) (by fun_prop))
  unfold brDropL
  exact QMCLeafB.PolyLoop.poly_sumInr_comp
    (Poly.pair (f := fun p : LSt => p.1)
      (g := fun p : LSt => (nrmRows p.1.1 p.1.2 (dropRows p.2.1), nrmAcc p.1.1 p.1.2 p.2.2))
      (by fun_prop) (Poly.pair h1 h2))

theorem poly_brSchurL : Poly brSchurL := by
  have hpiv : Poly (fun p : LSt => piv p.2.1) :=
    Poly.comp (f := piv) (g := fun p : LSt => p.2.1) poly_piv (by fun_prop)
  have hhead : Poly (fun p : LSt => headTail p.2.1) :=
    Poly.comp (f := headTail) (g := fun p : LSt => p.2.1) poly_headTail (by fun_prop)
  have hlist : Poly (fun p : LSt => (piv p.2.1, headTail p.2.1) :: p.2.2) :=
    Poly.comp (f := fun z : (ℚ × List ℚ) × Acc => z.1 :: z.2)
      (g := fun p : LSt => ((piv p.2.1, headTail p.2.1), p.2.2)) Poly.list_cons
      (Poly.pair (f := fun p : LSt => (piv p.2.1, headTail p.2.1))
        (g := fun p : LSt => p.2.2) (Poly.pair hpiv hhead) (by fun_prop))
  have h1 : Poly (fun p : LSt => nrmRows p.1.1 p.1.2 (schurRows p.2.1)) :=
    Poly.comp (f := fun y : (ℚ × ℕ) × Rows => nrmRows y.1.1 y.1.2 y.2)
      (g := fun p : LSt => (p.1, schurRows p.2.1)) poly_nrmRows
      (Poly.pair (f := fun p : LSt => p.1) (g := fun p : LSt => schurRows p.2.1) (by fun_prop)
        (Poly.comp (f := schurRows) (g := fun p : LSt => p.2.1) poly_schurRows (by fun_prop)))
  have h2 : Poly (fun p : LSt => nrmAcc p.1.1 p.1.2 ((piv p.2.1, headTail p.2.1) :: p.2.2)) :=
    Poly.comp (f := fun y : (ℚ × ℕ) × Acc => nrmAcc y.1.1 y.1.2 y.2)
      (g := fun p : LSt => (p.1, (piv p.2.1, headTail p.2.1) :: p.2.2)) poly_nrmAcc
      (Poly.pair (f := fun p : LSt => p.1)
        (g := fun p : LSt => (piv p.2.1, headTail p.2.1) :: p.2.2) (by fun_prop) hlist)
  unfold brSchurL
  exact QMCLeafB.PolyLoop.poly_sumInr_comp
    (Poly.pair (f := fun p : LSt => p.1)
      (g := fun p : LSt => (nrmRows p.1.1 p.1.2 (schurRows p.2.1),
        nrmAcc p.1.1 p.1.2 ((piv p.2.1, headTail p.2.1) :: p.2.2)))
      (by fun_prop) (Poly.pair h1 h2))

theorem poly_pivStepL : Poly pivStepL := by
  have hEmpty : Poly (fun p : LSt => p.2.1.isEmpty) :=
    Poly.comp (f := (List.isEmpty : Rows → Bool)) (g := fun p : LSt => p.2.1)
      Poly.list_empty (by fun_prop)
  have hpiv : Poly (fun p : LSt => piv p.2.1) :=
    Poly.comp (f := piv) (g := fun p : LSt => p.2.1) poly_piv (by fun_prop)
  have hhead : Poly (fun p : LSt => headTail p.2.1) :=
    Poly.comp (f := headTail) (g := fun p : LSt => p.2.1) poly_headTail (by fun_prop)
  have hneg : Poly (fun p : LSt => decide (piv p.2.1 < 0)) :=
    Poly.rat_lt_comp hpiv (Automatic.Poly.const (0 : ℚ))
  have hzero : Poly (fun p : LSt => decide (piv p.2.1 = 0)) :=
    Poly.rat_eq_comp hpiv (Automatic.Poly.const (0 : ℚ))
  have hsq : Poly (fun p : LSt => rowSq (headTail p.2.1)) :=
    Poly.comp (f := rowSq) (g := fun p : LSt => headTail p.2.1) poly_rowSq hhead
  have hsqz : Poly (fun p : LSt => decide (rowSq (headTail p.2.1) = 0)) :=
    Poly.rat_eq_comp hsq (Automatic.Poly.const (0 : ℚ))
  have inner : Poly (fun p : LSt =>
      if rowSq (headTail p.2.1) = 0 then brDropL p else brZeroL p) :=
    Poly.ite_prop (p := fun p : LSt => rowSq (headTail p.2.1) = 0) hsqz poly_brDropL poly_brZeroL
  have mid : Poly (fun p : LSt =>
      if piv p.2.1 = 0 then (if rowSq (headTail p.2.1) = 0 then brDropL p else brZeroL p)
      else brSchurL p) :=
    Poly.ite_prop (p := fun p : LSt => piv p.2.1 = 0) hzero inner poly_brSchurL
  have outer : Poly (fun p : LSt =>
      if piv p.2.1 < 0 then brNegL p
      else (if piv p.2.1 = 0 then (if rowSq (headTail p.2.1) = 0 then brDropL p else brZeroL p)
        else brSchurL p)) :=
    Poly.ite_prop (p := fun p : LSt => piv p.2.1 < 0) hneg poly_brNegL mid
  exact Poly.ite (p := fun p : LSt => p.2.1.isEmpty) hEmpty poly_brStopL outer

/-! ### 4.2  The state after one step -/

theorem brDropL_inr {p : LSt} {q1 : ℚ × ℕ} {q2 : St} (h : brDropL p = Sum.inr (q1, q2)) :
    q1 = p.1 ∧ q2 = (nrmRows p.1.1 p.1.2 (dropRows p.2.1), nrmAcc p.1.1 p.1.2 p.2.2) := by
  obtain ⟨⟨m1, m2⟩, s⟩ := p
  have hh := Sum.inr.inj h
  simp only [Prod.mk.injEq] at hh
  exact ⟨hh.1.symm, hh.2.symm⟩

theorem brSchurL_inr {p : LSt} {q1 : ℚ × ℕ} {q2 : St} (h : brSchurL p = Sum.inr (q1, q2)) :
    q1 = p.1 ∧ q2 = (nrmRows p.1.1 p.1.2 (schurRows p.2.1),
      nrmAcc p.1.1 p.1.2 ((piv p.2.1, headTail p.2.1) :: p.2.2)) := by
  obtain ⟨⟨m1, m2⟩, s⟩ := p
  have hh := Sum.inr.inj h
  simp only [Prod.mk.injEq] at hh
  exact ⟨hh.1.symm, hh.2.symm⟩

theorem pivStepL_length_pos {st : St} (h : ¬ st.1.isEmpty = true) : 0 < st.1.length := by
  cases hl : st.1 with
  | nil => simp [hl] at h
  | cons r rs => simp

theorem pivStepL_snd_shape {p p' : LSt} (h : pivStepL p = Sum.inr p') :
    p'.2.1.length + p'.2.2.length ≤ p.2.1.length + p.2.2.length := by
  rw [pivStepL_def] at h
  by_cases h1 : p.2.1.isEmpty
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    have hpos := pivStepL_length_pos h1
    by_cases h2 : piv p.2.1 < 0
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : piv p.2.1 = 0
      · rw [if_pos h3] at h
        by_cases h4 : rowSq (headTail p.2.1) = 0
        · rw [if_pos h4] at h
          rw [(brDropL_inr (q1 := p'.1) (q2 := p'.2) h).2]
          simp only [nrmRows_length, nrmAcc_length, dropRows, List.length_map, List.length_tail]
          omega
        · rw [if_neg h4] at h; cases h
      · rw [if_neg h3] at h
        rw [(brSchurL_inr (q1 := p'.1) (q2 := p'.2) h).2]
        have hs := schurRows_length p.2.1
        rw [List.length_tail] at hs
        simp only [nrmRows_length, nrmAcc_length, List.length_cons]
        omega

theorem pivStepL_snd_block_length {p p' : LSt} (h : pivStepL p = Sum.inr p') :
    p'.2.1.length < p.2.1.length := by
  rw [pivStepL_def] at h
  by_cases h1 : p.2.1.isEmpty
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    have hpos := pivStepL_length_pos h1
    by_cases h2 : piv p.2.1 < 0
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : piv p.2.1 = 0
      · rw [if_pos h3] at h
        by_cases h4 : rowSq (headTail p.2.1) = 0
        · rw [if_pos h4] at h
          rw [(brDropL_inr (q1 := p'.1) (q2 := p'.2) h).2]
          simp only [nrmRows_length, dropRows, List.length_map, List.length_tail]
          omega
        · rw [if_neg h4] at h; cases h
      · rw [if_neg h3] at h
        rw [(brSchurL_inr (q1 := p'.1) (q2 := p'.2) h).2]
        have hs := schurRows_length p.2.1
        rw [List.length_tail] at hs
        simp only [nrmRows_length]
        omega

theorem pivStepL_snd_height {p p' : LSt} {L D : ℕ} (hmu : HasHeight p.1.1 L)
    (hdD : p.1.2 ≤ 2 ^ D) (h : pivStepL p = Sum.inr p') :
    RowsHeight p'.2.1 (L + D) ∧ AccHeight p'.2.2 (L + D) := by
  rw [pivStepL_def] at h
  by_cases h1 : p.2.1.isEmpty
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : piv p.2.1 < 0
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : piv p.2.1 = 0
      · rw [if_pos h3] at h
        by_cases h4 : rowSq (headTail p.2.1) = 0
        · rw [if_pos h4] at h
          rw [(brDropL_inr (q1 := p'.1) (q2 := p'.2) h).2]
          exact ⟨nrmRows_height hmu hdD _, nrmAcc_height hmu hdD _⟩
        · rw [if_neg h4] at h; cases h
      · rw [if_neg h3] at h
        rw [(brSchurL_inr (q1 := p'.1) (q2 := p'.2) h).2]
        exact ⟨nrmRows_height hmu hdD _, nrmAcc_height hmu hdD _⟩

theorem pivStepL_snd_width {p p' : LSt} {N : ℕ} (h : pivStepL p = Sum.inr p')
    (hW : RowsWidth p.2.1 N) (hWa : AccWidth p.2.2 N) :
    RowsWidth p'.2.1 N ∧ AccWidth p'.2.2 N := by
  rw [pivStepL_def] at h
  by_cases h1 : p.2.1.isEmpty
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : piv p.2.1 < 0
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : piv p.2.1 = 0
      · rw [if_pos h3] at h
        by_cases h4 : rowSq (headTail p.2.1) = 0
        · rw [if_pos h4] at h
          rw [(brDropL_inr (q1 := p'.1) (q2 := p'.2) h).2]
          exact ⟨nrmRows_width _ _ (rowsWidth_dropRows hW), nrmAcc_width _ _ hWa⟩
        · rw [if_neg h4] at h; cases h
      · rw [if_neg h3] at h
        rw [(brSchurL_inr (q1 := p'.1) (q2 := p'.2) h).2]
        exact ⟨nrmRows_width _ _ (rowsWidth_schurRows hW), nrmAcc_cons_width hW.headTail hWa⟩

theorem pivStepL_snd_fst {p p' : LSt} (h : pivStepL p = Sum.inr p') : p'.1 = p.1 := by
  rw [pivStepL_def] at h
  by_cases h1 : p.2.1.isEmpty
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : piv p.2.1 < 0
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : piv p.2.1 = 0
      · rw [if_pos h3] at h
        by_cases h4 : rowSq (headTail p.2.1) = 0
        · rw [if_pos h4] at h
          exact (brDropL_inr (q1 := p'.1) (q2 := p'.2) h).1
        · rw [if_neg h4] at h; cases h
      · rw [if_neg h3] at h
        exact (brSchurL_inr (q1 := p'.1) (q2 := p'.2) h).1

/-! ### 4.3  The descent, and its `Poly` proof -/

/-- The descent with explicit fuel. -/
def runPivLFuel : ℕ → LSt → Ans
  | 0, _ => (false, [])
  | (k + 1), p =>
    match pivStepL p with
    | Sum.inl a => a
    | Sum.inr p' => runPivLFuel k p'

/-- The state-dependent normalised descent: the number of rows is enough fuel. -/
def runPivL (p : LSt) : Ans := runPivLFuel p.2.1.length p

theorem runPivLFuel_succ (k : ℕ) (p : LSt) :
    runPivLFuel (k + 1) p = (match pivStepL p with
      | Sum.inl a => a
      | Sum.inr p' => runPivLFuel k p') := rfl

/-- The size monomial of the state-dependent descent: `44000·(X+1)^5`. -/
noncomputable def szPoly : Polynomial ℕ := Polynomial.C 44000 * (Polynomial.X + 1) ^ 5

theorem szPoly_eval (L : ℕ) : szPoly.eval L = 44000 * (L + 1) ^ 5 := by
  simp [szPoly, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_pow]

/-- The size charge of one descent state, from the `St` part alone.  `Q(L) = 128(12L+21)(L+1)²` is
the monomial at height `L + L` and shape `L`. -/
theorem enc_LSt_le (p : LSt) {L₀ : ℕ} (hpar : (enc p.1).length ≤ L₀)
    (hst : (enc p.2).length ≤ 128 * (2 * (3 * (2 * L₀) + 10) + 1) * (L₀ + 1) ^ 2) :
    (enc p).length ≤ 44000 * (L₀ + 1) ^ 5 := by
  have e : (enc p : List Bool) = encodePair (enc : ℚ × ℕ → List Bool) (enc : St → List Bool) p :=
    rfl
  rw [e, encodePair_length]
  have hQ : 128 * (2 * (3 * (2 * L₀) + 10) + 1) * (L₀ + 1) ^ 2 ≤ 2688 * (L₀ + 1) ^ 5 := by
    have h1 : 2 * (3 * (2 * L₀) + 10) + 1 ≤ 21 * (L₀ + 1) := by omega
    have h2 : 128 * (2 * (3 * (2 * L₀) + 10) + 1) * (L₀ + 1) ^ 2
        ≤ 128 * (21 * (L₀ + 1)) * (L₀ + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
    have h3 : 128 * (21 * (L₀ + 1)) * (L₀ + 1) ^ 2 = 2688 * ((L₀ + 1) ^ 3) := by ring
    have h4 : 2688 * ((L₀ + 1) ^ 3) ≤ 2688 * ((L₀ + 1) ^ 5) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    calc 128 * (2 * (3 * (2 * L₀) + 10) + 1) * (L₀ + 1) ^ 2
        ≤ 128 * (21 * (L₀ + 1)) * (L₀ + 1) ^ 2 := h2
      _ = 2688 * ((L₀ + 1) ^ 3) := h3
      _ ≤ 2688 * ((L₀ + 1) ^ 5) := h4
  have hsum : 2 * (enc p.1).length + 1 + (enc p.2).length
      ≤ 2 * L₀ + 1 + 2688 * (L₀ + 1) ^ 5 := by
    have h2 : (enc p.2).length ≤ 2688 * (L₀ + 1) ^ 5 := hst.trans hQ
    have h3 : 2 * (enc p.1).length + 1 ≤ 2 * L₀ + 1 := by omega
    exact Nat.add_le_add h3 h2
  have hfin : 2 * L₀ + 1 + 2688 * (L₀ + 1) ^ 5 ≤ 44000 * (L₀ + 1) ^ 5 := by
    have hp2 : L₀ + 1 ≤ (L₀ + 1) ^ 5 := by
      rw [show (5:ℕ) = 4 + 1 by norm_num, pow_succ]
      calc L₀ + 1 = (L₀ + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (L₀ + 1) * (L₀ + 1) ^ 4 := Nat.mul_le_mul_left _ (pow_pos (Nat.succ_pos L₀) 4)
        _ = (L₀ + 1) ^ 4 * (L₀ + 1) := Nat.mul_comm _ _
    have hp3 : L₀ ≤ (L₀ + 1) ^ 5 := Nat.le_trans (Nat.le_succ L₀) hp2
    have hp4 : 1 ≤ (L₀ + 1) ^ 5 := by
      have h := Nat.pow_le_pow_right (Nat.succ_pos L₀) (by omega : 0 ≤ 5)
      simpa using h
    have e1 : 2 * L₀ ≤ 2 * ((L₀ + 1) ^ 5) := Nat.mul_le_mul_left 2 hp3
    have e2 : 2 * L₀ + 1 ≤ 3 * ((L₀ + 1) ^ 5) := by omega
    have e3 : 2 * L₀ + 1 + 2688 * ((L₀ + 1) ^ 5) ≤ 44000 * ((L₀ + 1) ^ 5) := by omega
    exact e3
  exact le_trans hsum hfin

/-- `Q(L) = 128·(2(3(2L)+10)+1)·(L+1)²` is the monomial `Csizes (L+L) 0 * (L+1)^2`. -/
theorem Csizes_two (L : ℕ) :
    Csizes (L + L) 0 = 128 * (2 * (3 * (2 * L) + 10) + 1) := by
  rw [Csizes]
  have h : 3 * ((L + L) + 0) + 10 = 3 * (2 * L) + 10 := by omega
  rw [h]

/-- The descent is a bounded run of the step inside the monomial, from the shape/invariant data at
the start. -/
theorem runPivLFuel_bounded (L₀ : ℕ) :
    ∀ (k : ℕ) (mu : ℚ) (d : ℕ) (st : St), (enc (mu, d)).length ≤ L₀ →
      HasHeight mu L₀ → d ≤ 2 ^ L₀ →
      RowsWidth st.1 L₀ → AccWidth st.2 L₀ →
      st.1.length + st.2.length ≤ 2 * L₀ → st.1.length ≤ L₀ →
      (enc st).length ≤ 128 * (2 * (3 * (2 * L₀) + 10) + 1) * (L₀ + 1) ^ 2 →
      st.1.length ≤ k →
      ∃ n ≤ k + 1, BoundedRun (enc : LSt → List Bool) pivStepL
        (44000 * (L₀ + 1) ^ 5) n ((mu, d), st) (runPivLFuel k ((mu, d), st)) := by
  intro k
  induction k with
  | zero =>
      intro mu d st hpar hmu hd hW hPa hshape hrows hsz hle
      have hempty : st.1 = [] := List.eq_nil_of_length_eq_zero (by omega)
      have his : st.1.isEmpty = true := by simp [hempty]
      have hstep : pivStepL ((mu, d), st) = Sum.inl (false, []) := by
        rw [pivStepL_def, if_pos his]
        rfl
      refine ⟨1, by omega, ?_⟩
      rw [runPivLFuel]
      exact BoundedRun.stop (enc_LSt_le ((mu, d), st) hpar hsz) hstep
  | succ k ih =>
      intro mu d st hpar hmu hd hW hPa hshape hrows hsz hle
      have hszL : (enc ((mu, d), st)).length ≤ 44000 * (L₀ + 1) ^ 5 :=
        enc_LSt_le ((mu, d), st) hpar hsz
      rw [runPivLFuel_succ]
      cases hstep : pivStepL ((mu, d), st) with
      | inl a => exact ⟨1, by omega, BoundedRun.stop hszL hstep⟩
      | inr p' =>
          have hfst : p'.1 = (mu, d) := pivStepL_snd_fst hstep
          have hbl := pivStepL_snd_block_length hstep
          have hsh := pivStepL_snd_shape hstep
          have hdD : ((mu, d), st).1.2 ≤ 2 ^ L₀ := hd
          have hh := pivStepL_snd_height (p := ((mu, d), st)) (p' := p') (L := L₀) (D := L₀)
            hmu hdD hstep
          have hw := pivStepL_snd_width (p := ((mu, d), st)) (p' := p') hstep hW hPa
          have hsh' : p'.2.1.length + p'.2.2.length ≤ st.1.length + st.2.length := hsh
          have hbl' : p'.2.1.length < st.1.length := hbl
          have hpar' : (enc p'.1).length ≤ L₀ := by rw [hfst]; exact hpar
          have hmu' : HasHeight p'.1.1 L₀ := by rw [hfst]; exact hmu
          have hd' : p'.1.2 ≤ 2 ^ L₀ := by rw [hfst]; exact hd
          have hrows' : p'.2.1.length ≤ L₀ := Nat.le_trans (Nat.le_of_lt hbl') hrows
          have hacc' : p'.2.2.length ≤ 2 * L₀ :=
            Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans hsh' hshape)
          have hsz'' :
              (enc p'.2).length ≤ 128 * (2 * (3 * (2 * L₀) + 10) + 1) * (L₀ + 1) ^ 2 := by
            have h0 : (enc p'.2).length ≤ Csizes (L₀ + L₀) 0 * (L₀ + 1) ^ 2 :=
              enc_st_le_monomial (M := L₀ + L₀) (D := 0) (N := L₀) hh.1 hh.2 hw.1 hw.2 hrows' hacc'
            rw [Csizes_two] at h0
            exact h0
          have hsh'' : p'.2.1.length + p'.2.2.length ≤ 2 * L₀ := Nat.le_trans hsh' hshape
          have hfuel : p'.2.1.length ≤ k := by omega
          obtain ⟨m, hm, hrun⟩ := ih p'.1.1 p'.1.2 p'.2 hpar' hmu' hd' hw.1 hw.2 hsh'' hrows'
            hsz'' hfuel
          exact ⟨m + 1, by omega, BoundedRun.step hszL hstep hrun⟩

/-- **The state-dependent normalised pivot descent is a `Poly` program** — with *no* hypothesis on
sizes, heights, the box bound or the grid.  This is the form a fixed round machine needs: `mu` and
`d` are data, not numerals. -/
theorem poly_runPivL : Poly (fun p : LSt => runPivL p) := by
  refine QMCLeafB.PolyLoop.poly_loop (f := pivStepL) poly_pivStepL
    (fun p : LSt => runPivL p) (Polynomial.X + 1) szPoly ?_
  intro a
  have hpair : (enc a : List Bool)
      = encodePair (enc : ℚ × ℕ → List Bool) (enc : St → List Bool) a := rfl
  have hpairR : (enc a.1 : List Bool)
      = encodePair (enc : ℚ → List Bool) (enc : ℕ → List Bool) a.1 := rfl
  have hpairS : (enc a.2 : List Bool)
      = encodePair (enc : Rows → List Bool) (enc : Acc → List Bool) a.2 := rfl
  have hL1 : (enc a.1).length ≤ (enc a).length := by
    rw [hpair, encodePair_length]; omega
  have hL2 : (enc a.2).length ≤ (enc a).length := by
    rw [hpair, encodePair_length]; omega
  have hmu0 : HasHeight a.1.1 (enc a.1.1).length := Ratio.height_length a.1.1
  have hL1' : (enc a.1.1).length ≤ (enc a).length := by
    have h4 : (enc a.1.1).length ≤ (enc a.1).length := by
      rw [hpairR, encodePair_length]; omega
    omega
  have hmu : HasHeight a.1.1 (enc a).length := HasHeight.mono hmu0 hL1'
  have hbits : a.1.2 ≤ 2 ^ (enc a).length := by
    have h1 : a.1.2 ≤ 2 ^ (a.1.2).bits.length := NatBinary.le_two_pow_length a.1.2
    have h2 : (a.1.2).bits.length = (enc a.1.2).length := rfl
    have h3 : (enc a.1.2).length ≤ (enc a.1).length := by
      rw [hpairR, encodePair_length]; omega
    rw [h2] at h1
    exact le_trans h1 (Nat.pow_le_pow_right (by omega) (by omega))
  have hW : RowsWidth a.2.1 (enc a).length := by
    intro v hv
    have h1 : v.length ≤ (enc v).length := EncodedList.length_le (ea := (enc : ℚ → List Bool)) v
    have h2 : (enc v).length ≤ (enc a.2.1).length :=
      EncodedList.member_length (ea := (enc : List ℚ → List Bool)) a.2.1 v hv
    have h3 : (enc a.2.1).length ≤ (enc a.2).length := by
      rw [hpairS, encodePair_length]; omega
    omega
  have hPa : AccWidth a.2.2 (enc a).length := by
    intro q hq
    have h1 : q.2.length ≤ (enc q.2).length :=
      EncodedList.length_le (ea := (enc : ℚ → List Bool)) q.2
    have h2 : (enc q).length ≤ (enc a.2.2).length :=
      EncodedList.member_length (ea := (enc : ℚ × List ℚ → List Bool)) a.2.2 q hq
    have hq' : (enc q : List Bool) = encodePair (enc : ℚ → List Bool) (enc : List ℚ → List Bool) q :=
      rfl
    rw [hq', encodePair_length] at h2
    have h4 : (enc a.2.2).length ≤ (enc a.2).length := by
      rw [hpairS, encodePair_length]; omega
    omega
  have hsplit : (enc a.2.1).length + (enc a.2.2).length ≤ (enc a.2).length := by
    rw [hpairS, encodePair_length]
    omega
  have hshape : a.2.1.length + a.2.2.length ≤ 2 * (enc a).length := by
    have h1 : a.2.1.length ≤ (enc a.2.1).length :=
      EncodedList.length_le (ea := (enc : List ℚ → List Bool)) a.2.1
    have h2 : a.2.2.length ≤ (enc a.2.2).length :=
      EncodedList.length_le (ea := (enc : ℚ × List ℚ → List Bool)) a.2.2
    omega
  have hrows : a.2.1.length ≤ (enc a).length := by
    have h1 : a.2.1.length ≤ (enc a.2.1).length :=
      EncodedList.length_le (ea := (enc : List ℚ → List Bool)) a.2.1
    have h2 : (enc a.2.1).length ≤ (enc a.2).length := by
      rw [hpairS, encodePair_length]; omega
    omega
  have hsz : (enc a.2).length
      ≤ 128 * (2 * (3 * (2 * (enc a).length) + 10) + 1) * ((enc a).length + 1) ^ 2 := by
    refine hL2.trans ?_
    have hK : (enc a).length ≤ 128 * (2 * (3 * (2 * (enc a).length) + 10) + 1) := by
      have h0 : 128 * (2 * (3 * (2 * (enc a).length) + 10) + 1)
          = 128 * (12 * (enc a).length + 21) := by ring
      omega
    have hP : 1 ≤ ((enc a).length + 1) ^ 2 := by
      have h := Nat.pow_le_pow_right (by omega : 0 < (enc a).length + 1) (by omega : 0 ≤ 2)
      simpa using h
    calc (enc a).length ≤ 128 * (2 * (3 * (2 * (enc a).length) + 10) + 1) := hK
      _ = 128 * (2 * (3 * (2 * (enc a).length) + 10) + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ 128 * (2 * (3 * (2 * (enc a).length) + 10) + 1) * ((enc a).length + 1) ^ 2 :=
            Nat.mul_le_mul_left _ hP
  obtain ⟨n, hn, hrun⟩ := runPivLFuel_bounded (enc a).length a.2.1.length a.1.1 a.1.2 a.2 hL1 hmu
    hbits hW hPa hshape hrows hsz (le_refl _)
  refine ⟨n, ?_, ?_⟩
  · have h1 : ((Polynomial.X + 1 : Polynomial ℕ)).eval (enc a).length = (enc a).length + 1 := by
      simp [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    rw [h1]
    omega
  · have h2 : szPoly.eval (enc a).length = 44000 * ((enc a).length + 1) ^ 5 := szPoly_eval _
    rw [h2]
    exact hrun

/-! ## 6.  The separation oracle on the state

The oracle's PSD test is §4's `runPivL`.  What is still needed is the row-major ↔ block reshaping
(the library's `MatQ.Runtime.m_idx`), the two scalar tests (`∑|Xᵢᵢ − 1|` and `[A, X]`), and the two
cut normals (`v vᵀ` and `diagonal (sign (1 − Xᵢᵢ))`), each as a `Poly` function of the state.

Everything in this section is `Poly (fun p : <state> => ...)` with **no hypotheses**.
-/

/-- `List.range n`, read off the code itself. -/
def idxs (p : ℕ × List ℚ) : List ℕ := List.range (p.2.take p.1).length

/-- The `(i,j)` entry of the row-major code. -/
def entV (p : ℕ × List ℚ) (i j : ℕ) : ℚ := p.2.getD (i * p.1 + j) 0

/-- Row `i` of the block. -/
def rowOf (p : ℕ × List ℚ) (i : ℕ) : List ℚ := (idxs p).map (fun j => entV p i j)

/-- The block form of the row-major code. -/
def toRows (p : ℕ × List ℚ) : Rows := (idxs p).map (rowOf p)

/-- `|q|` as a `Poly`-friendly function. -/
def absq (q : ℚ) : ℚ := if q < 0 then -q else q

theorem absq_eq (q : ℚ) : absq q = |q| := by
  unfold absq
  by_cases h : q < 0
  · rw [if_pos h, abs_of_neg h]
  · rw [if_neg h, abs_of_nonneg (by linarith)]

/-- `∑ᵢ |Xᵢᵢ − 1|` on the code. -/
def diagSumV (p : ℕ × List ℚ) : ℚ := ((idxs p).map (fun i => absq (entV p i i - 1))).sum

/-- `[A, X] = ∑ᵢ ∑ⱼ Aᵢⱼ Xᵢⱼ` on two codes. -/
def frobV (q : ℕ × (List ℚ × List ℚ)) : ℚ :=
  ((idxs (q.1, q.2.2)).map (fun i =>
    ((idxs (q.1, q.2.2)).map (fun j =>
      q.2.1.getD (i * q.1 + j) 0 * q.2.2.getD (i * q.1 + j) 0)).sum)).sum

/-- The cut normal `v vᵀ` of a coded violated direction. -/
def vecMulVecF (p : ℕ × List ℚ) : List ℚ :=
  (idxs p).flatMap (fun i => (idxs p).map (fun j => p.2.getD i 0 * p.2.getD j 0))

/-- `sign q` as a rational. -/
def sgnOf (q : ℚ) : ℚ := if q < 0 then -1 else if q = 0 then 0 else 1

/-- The diagonal sign matrix `diagonal (sign (1 − Xᵢᵢ))`, row-major. -/
def diagSignF (p : ℕ × List ℚ) : List ℚ :=
  (idxs p).flatMap (fun i => (idxs p).map (fun j => if i = j then sgnOf (1 - entV p i i) else 0))

theorem poly_idxs : Poly idxs := ⟨MatQ.Runtime.m_idx⟩

theorem poly_entV : Poly (fun z : (ℕ × List ℚ) × ℕ × ℕ => entV z.1 z.2.1 z.2.2) := by
  unfold entV
  exact Poly.comp (f := fun y : List ℚ × ℕ => y.1[y.2]?.getD (0 : ℚ))
    (g := fun z : (ℕ × List ℚ) × ℕ × ℕ => (z.1.2, z.2.1 * z.1.1 + z.2.2))
    (Poly.list_getD (0 : ℚ))
    (Poly.pair (f := fun z : (ℕ × List ℚ) × ℕ × ℕ => z.1.2)
      (g := fun z : (ℕ × List ℚ) × ℕ × ℕ => z.2.1 * z.1.1 + z.2.2) (by fun_prop) (by fun_prop))

theorem poly_entV2 : Poly (fun z : (ℕ × List ℚ) × ℕ => entV z.1 z.2 z.2) :=
  Poly.comp (f := fun w : (ℕ × List ℚ) × ℕ × ℕ => entV w.1 w.2.1 w.2.2)
    (g := fun z : (ℕ × List ℚ) × ℕ => (z.1, z.2, z.2)) poly_entV
    (Poly.pair (f := fun z : (ℕ × List ℚ) × ℕ => z.1)
      (g := fun z : (ℕ × List ℚ) × ℕ => (z.2, z.2)) (by fun_prop)
      (Poly.pair (by fun_prop) (by fun_prop)))

theorem poly_absq : Poly absq := by
  unfold absq
  exact Poly.ite_prop (p := fun q : ℚ => q < 0)
    (Poly.rat_lt_comp (Poly.identity (α := ℚ)) (Automatic.Poly.const (0 : ℚ)))
    Poly.rat_neg (Poly.identity (α := ℚ))

theorem poly_sgnOf : Poly sgnOf := by
  unfold sgnOf
  have hlt : Poly (fun q : ℚ => decide (q < 0)) :=
    Poly.rat_lt_comp (Poly.identity (α := ℚ)) (Automatic.Poly.const (0 : ℚ))
  have heq : Poly (fun q : ℚ => decide (q = 0)) :=
    Poly.rat_eq_comp (Poly.identity (α := ℚ)) (Automatic.Poly.const (0 : ℚ))
  exact Poly.ite_prop (p := fun q : ℚ => q < 0) hlt (Automatic.Poly.const (-1))
    (Poly.ite_prop (p := fun q : ℚ => q = 0) heq (Automatic.Poly.const 0)
      (Automatic.Poly.const 1))

theorem poly_rowOf : Poly (fun z : (ℕ × List ℚ) × ℕ => rowOf z.1 z.2) := by
  unfold rowOf
  have hf : Poly (fun x : ((ℕ × List ℚ) × ℕ) × ℕ => entV x.1.1 x.1.2 x.2) :=
    Poly.comp (f := fun z : (ℕ × List ℚ) × ℕ × ℕ => entV z.1 z.2.1 z.2.2)
      (g := fun x : ((ℕ × List ℚ) × ℕ) × ℕ => (x.1.1, x.1.2, x.2)) poly_entV
      (Poly.pair (f := fun x : ((ℕ × List ℚ) × ℕ) × ℕ => x.1.1)
        (g := fun x : ((ℕ × List ℚ) × ℕ) × ℕ => (x.1.2, x.2)) (by fun_prop)
        (Poly.pair (by fun_prop) (by fun_prop)))
  exact Poly.list_map (f := fun (z : (ℕ × List ℚ) × ℕ) (j : ℕ) => entV z.1 z.2 j)
    (as := fun z : (ℕ × List ℚ) × ℕ => idxs z.1) hf
    (Poly.comp (f := idxs) (g := fun z : (ℕ × List ℚ) × ℕ => z.1) poly_idxs (by fun_prop))

theorem poly_toRows : Poly (fun p : ℕ × List ℚ => toRows p) := by
  unfold toRows
  have hf : Poly (fun x : (ℕ × List ℚ) × ℕ => rowOf x.1 x.2) :=
    Poly.comp (f := fun z : (ℕ × List ℚ) × ℕ => rowOf z.1 z.2)
      (g := fun x : (ℕ × List ℚ) × ℕ => x) poly_rowOf (by fun_prop)
  exact Poly.list_map (f := fun (p : ℕ × List ℚ) (i : ℕ) => rowOf p i)
    (as := fun p : ℕ × List ℚ => idxs p) hf poly_idxs

theorem poly_diagSumV : Poly (fun p : ℕ × List ℚ => diagSumV p) := by
  unfold diagSumV
  have hsub : Poly (fun x : (ℕ × List ℚ) × ℕ => entV x.1 x.2 x.2 - 1) := by
    have h3 : Poly (fun x : (ℕ × List ℚ) × ℕ => (entV x.1 x.2 x.2, (1 : ℚ))) :=
      Poly.pair poly_entV2 (Automatic.Poly.const 1)
    exact Poly.comp (f := fun y : ℚ × ℚ => y.1 - y.2)
      (g := fun x : (ℕ × List ℚ) × ℕ => (entV x.1 x.2 x.2, (1 : ℚ))) Poly.rat_sub h3
  have hf : Poly (fun x : (ℕ × List ℚ) × ℕ => absq (entV x.1 x.2 x.2 - 1)) :=
    Poly.comp (f := absq) (g := fun x : (ℕ × List ℚ) × ℕ => entV x.1 x.2 x.2 - 1) poly_absq hsub
  have hlist : Poly (fun p : ℕ × List ℚ => (idxs p).map (fun i => absq (entV p i i - 1))) :=
    Poly.list_map (f := fun (p : ℕ × List ℚ) (i : ℕ) => absq (entV p i i - 1))
      (as := fun p : ℕ × List ℚ => idxs p) hf poly_idxs
  exact Poly.comp (f := List.sum) (g := fun p : ℕ × List ℚ =>
    (idxs p).map (fun i => absq (entV p i i - 1))) PivotProgram.poly_rat_sum hlist

theorem poly_frobV : Poly (fun q : ℕ × (List ℚ × List ℚ) => frobV q) := by
  unfold frobV
  have hf : Poly (fun x : ((ℕ × (List ℚ × List ℚ)) × ℕ) × ℕ =>
      x.1.1.2.1.getD (x.1.2 * x.1.1.1 + x.2) 0 * x.1.1.2.2.getD (x.1.2 * x.1.1.1 + x.2) 0) := by
    have hA : Poly (fun x : ((ℕ × (List ℚ × List ℚ)) × ℕ) × ℕ =>
        x.1.1.2.1.getD (x.1.2 * x.1.1.1 + x.2) 0) :=
      Poly.comp (f := fun y : List ℚ × ℕ => y.1[y.2]?.getD (0 : ℚ))
        (g := fun x : ((ℕ × (List ℚ × List ℚ)) × ℕ) × ℕ =>
          (x.1.1.2.1, x.1.2 * x.1.1.1 + x.2)) (Poly.list_getD (0 : ℚ))
        (Poly.pair (by fun_prop) (by fun_prop))
    have hX : Poly (fun x : ((ℕ × (List ℚ × List ℚ)) × ℕ) × ℕ =>
        x.1.1.2.2.getD (x.1.2 * x.1.1.1 + x.2) 0) :=
      Poly.comp (f := fun y : List ℚ × ℕ => y.1[y.2]?.getD (0 : ℚ))
        (g := fun x : ((ℕ × (List ℚ × List ℚ)) × ℕ) × ℕ =>
          (x.1.1.2.2, x.1.2 * x.1.1.1 + x.2)) (Poly.list_getD (0 : ℚ))
        (Poly.pair (by fun_prop) (by fun_prop))
    exact Poly.comp (f := fun y : ℚ × ℚ => y.1 * y.2)
      (g := fun x : ((ℕ × (List ℚ × List ℚ)) × ℕ) × ℕ =>
        (x.1.1.2.1.getD (x.1.2 * x.1.1.1 + x.2) 0,
         x.1.1.2.2.getD (x.1.2 * x.1.1.1 + x.2) 0)) Poly.rat_mul (Poly.pair hA hX)
  have hidx : Poly (fun q : ℕ × (List ℚ × List ℚ) => idxs (q.1, q.2.2)) :=
    Poly.comp (f := idxs) (g := fun q : ℕ × (List ℚ × List ℚ) => (q.1, q.2.2)) poly_idxs
      (by fun_prop)
  have hrow : Poly (fun z : (ℕ × (List ℚ × List ℚ)) × ℕ =>
      ((idxs (z.1.1, z.1.2.2)).map (fun j =>
        z.1.2.1.getD (z.2 * z.1.1 + j) 0 * z.1.2.2.getD (z.2 * z.1.1 + j) 0)).sum) := by
    have hmap : Poly (fun z : (ℕ × (List ℚ × List ℚ)) × ℕ =>
        (idxs (z.1.1, z.1.2.2)).map (fun j =>
          z.1.2.1.getD (z.2 * z.1.1 + j) 0 * z.1.2.2.getD (z.2 * z.1.1 + j) 0)) :=
      Poly.list_map (f := fun (z : (ℕ × (List ℚ × List ℚ)) × ℕ) (j : ℕ) =>
          z.1.2.1.getD (z.2 * z.1.1 + j) 0 * z.1.2.2.getD (z.2 * z.1.1 + j) 0)
        (as := fun z : (ℕ × (List ℚ × List ℚ)) × ℕ => idxs (z.1.1, z.1.2.2)) hf
        (Poly.comp (f := fun q : ℕ × (List ℚ × List ℚ) => idxs (q.1, q.2.2))
          (g := fun z : (ℕ × (List ℚ × List ℚ)) × ℕ => z.1) hidx (by fun_prop))
    exact Poly.comp (f := List.sum) (g := fun z : (ℕ × (List ℚ × List ℚ)) × ℕ =>
      (idxs (z.1.1, z.1.2.2)).map (fun j =>
        z.1.2.1.getD (z.2 * z.1.1 + j) 0 * z.1.2.2.getD (z.2 * z.1.1 + j) 0))
      PivotProgram.poly_rat_sum hmap
  have houter : Poly (fun q : ℕ × (List ℚ × List ℚ) =>
      (idxs (q.1, q.2.2)).map (fun i =>
        ((idxs (q.1, q.2.2)).map (fun j =>
          q.2.1.getD (i * q.1 + j) 0 * q.2.2.getD (i * q.1 + j) 0)).sum)) :=
    Poly.list_map (f := fun (q : ℕ × (List ℚ × List ℚ)) (i : ℕ) =>
        ((idxs (q.1, q.2.2)).map (fun j =>
          q.2.1.getD (i * q.1 + j) 0 * q.2.2.getD (i * q.1 + j) 0)).sum)
      (as := fun q : ℕ × (List ℚ × List ℚ) => idxs (q.1, q.2.2)) hrow hidx
  exact Poly.comp (f := List.sum) (g := fun q : ℕ × (List ℚ × List ℚ) =>
    (idxs (q.1, q.2.2)).map (fun i =>
      ((idxs (q.1, q.2.2)).map (fun j =>
        q.2.1.getD (i * q.1 + j) 0 * q.2.2.getD (i * q.1 + j) 0)).sum))
    PivotProgram.poly_rat_sum houter

theorem poly_vecMulVecF : Poly (fun p : ℕ × List ℚ => vecMulVecF p) := by
  unfold vecMulVecF
  have hf : Poly (fun x : (ℕ × List ℚ) × ℕ =>
      (idxs x.1).map (fun j => x.1.2.getD x.2 0 * x.1.2.getD j 0)) := by
    have hinner : Poly (fun y : ((ℕ × List ℚ) × ℕ) × ℕ =>
        y.1.1.2.getD y.1.2 0 * y.1.1.2.getD y.2 0) := by
      have h1 : Poly (fun y : ((ℕ × List ℚ) × ℕ) × ℕ => y.1.1.2.getD y.1.2 0) :=
        Poly.comp (f := fun w : List ℚ × ℕ => w.1[w.2]?.getD (0 : ℚ))
          (g := fun y : ((ℕ × List ℚ) × ℕ) × ℕ => (y.1.1.2, y.1.2)) (Poly.list_getD (0 : ℚ))
          (Poly.pair (by fun_prop) (by fun_prop))
      have h2 : Poly (fun y : ((ℕ × List ℚ) × ℕ) × ℕ => y.1.1.2.getD y.2 0) :=
        Poly.comp (f := fun w : List ℚ × ℕ => w.1[w.2]?.getD (0 : ℚ))
          (g := fun y : ((ℕ × List ℚ) × ℕ) × ℕ => (y.1.1.2, y.2)) (Poly.list_getD (0 : ℚ))
          (Poly.pair (by fun_prop) (by fun_prop))
      exact Poly.comp (f := fun w : ℚ × ℚ => w.1 * w.2)
        (g := fun y : ((ℕ × List ℚ) × ℕ) × ℕ =>
          (y.1.1.2.getD y.1.2 0, y.1.1.2.getD y.2 0)) Poly.rat_mul (Poly.pair h1 h2)
    exact Poly.list_map (f := fun (x : (ℕ × List ℚ) × ℕ) (j : ℕ) =>
        x.1.2.getD x.2 0 * x.1.2.getD j 0)
      (as := fun x : (ℕ × List ℚ) × ℕ => idxs x.1) hinner
      (Poly.comp (f := idxs) (g := fun x : (ℕ × List ℚ) × ℕ => x.1) poly_idxs (by fun_prop))
  exact Poly.list_flatMap (f := fun (p : ℕ × List ℚ) (i : ℕ) =>
      (idxs p).map (fun j => p.2.getD i 0 * p.2.getD j 0))
    (as := fun p : ℕ × List ℚ => idxs p) hf poly_idxs

theorem poly_diagSignF : Poly (fun p : ℕ × List ℚ => diagSignF p) := by
  unfold diagSignF
  have hf : Poly (fun x : (ℕ × List ℚ) × ℕ =>
      (idxs x.1).map (fun j => if x.2 = j then sgnOf (1 - entV x.1 x.2 x.2) else 0)) := by
    have hinner : Poly (fun y : ((ℕ × List ℚ) × ℕ) × ℕ =>
        if y.1.2 = y.2 then sgnOf (1 - entV y.1.1 y.1.2 y.1.2) else 0) := by
      have hcond : Poly (fun y : ((ℕ × List ℚ) × ℕ) × ℕ => decide (y.1.2 = y.2)) :=
        Poly.nat_eq_comp (by fun_prop : Poly (fun y : ((ℕ × List ℚ) × ℕ) × ℕ => y.1.2))
          (by fun_prop : Poly (fun y : ((ℕ × List ℚ) × ℕ) × ℕ => y.2))
      have hsgn : Poly (fun y : ((ℕ × List ℚ) × ℕ) × ℕ =>
          sgnOf (1 - entV y.1.1 y.1.2 y.1.2)) := by
        have he : Poly (fun y : ((ℕ × List ℚ) × ℕ) × ℕ => entV y.1.1 y.1.2 y.1.2) :=
          Poly.comp (f := fun z : (ℕ × List ℚ) × ℕ => entV z.1 z.2 z.2)
            (g := fun y : ((ℕ × List ℚ) × ℕ) × ℕ => y.1) poly_entV2 (by fun_prop)
        have hsub : Poly (fun y : ((ℕ × List ℚ) × ℕ) × ℕ => (1 : ℚ) - entV y.1.1 y.1.2 y.1.2) := by
          have hp : Poly (fun y : ((ℕ × List ℚ) × ℕ) × ℕ =>
              ((1 : ℚ), entV y.1.1 y.1.2 y.1.2)) :=
            Poly.pair (Automatic.Poly.const 1) he
          exact Poly.comp (f := fun w : ℚ × ℚ => w.1 - w.2) (g := fun y : ((ℕ × List ℚ) × ℕ) × ℕ =>
            ((1 : ℚ), entV y.1.1 y.1.2 y.1.2)) Poly.rat_sub hp
        exact Poly.comp (f := sgnOf) (g := fun y : ((ℕ × List ℚ) × ℕ) × ℕ =>
          1 - entV y.1.1 y.1.2 y.1.2) poly_sgnOf hsub
      exact Poly.ite_prop (p := fun y : ((ℕ × List ℚ) × ℕ) × ℕ => y.1.2 = y.2) hcond hsgn
        (Automatic.Poly.const 0)
    exact Poly.list_map (f := fun (x : (ℕ × List ℚ) × ℕ) (j : ℕ) =>
        if x.2 = j then sgnOf (1 - entV x.1 x.2 x.2) else 0)
      (as := fun x : (ℕ × List ℚ) × ℕ => idxs x.1) hinner
      (Poly.comp (f := idxs) (g := fun x : (ℕ × List ℚ) × ℕ => x.1) poly_idxs (by fun_prop))
  exact Poly.list_flatMap (f := fun (p : ℕ × List ℚ) (i : ℕ) =>
      (idxs p).map (fun j => if i = j then sgnOf (1 - entV p i i) else 0))
    (as := fun p : ℕ × List ℚ => idxs p) hf poly_idxs

/-! ### 6.1  The three scalars the round needs -/

/-- The scalar scaling `q ↦ c * q` of a whole code. -/
def scaleL (z : ℚ × List ℚ) : List ℚ := z.2.map (fun q => z.1 * q)

theorem poly_scaleL : Poly scaleL := by
  unfold scaleL
  exact Poly.list_map (f := fun (z : ℚ × List ℚ) (q : ℚ) => z.1 * q) (as := Prod.snd)
    (Poly.comp (f := fun w : ℚ × ℚ => w.1 * w.2)
      (g := fun x : (ℚ × List ℚ) × ℚ => (x.1.1, x.2)) Poly.rat_mul
      (Poly.pair (by fun_prop) (by fun_prop)))
    (by fun_prop)

/-- The inner product of two codes, as a `Poly` function. -/
def dotZ (q : List ℚ × List ℚ) : ℚ := ((q.1.zip q.2).map (fun z : ℚ × ℚ => z.1 * z.2)).sum

theorem poly_dotZ : Poly dotZ := ⟨MatQ.Runtime.dotProgram⟩

/-- `σ = cᵀ X c` on `(n, (X, c))`: the primal scalar of the GLS step. -/
def sigOf (p : ℕ × (List ℚ × List ℚ)) : ℚ :=
  dotZ (p.2.2, MatQ.Runtime.mulVecRaw (p.1, (p.2.1, p.2.2)))

/-- `β = 2/(n−1)`. -/
def betaOf (z : ℚ × ℚ) : ℚ := 2 / (z.1 - 1)

theorem poly_betaOf : Poly betaOf := by
  unfold betaOf
  exact Poly.comp (f := fun w : ℚ × ℚ => w.1 / w.2)
    (g := fun z : ℚ × ℚ => ((2 : ℚ), z.1 - 1)) Poly.rat_div
    (Poly.pair (Automatic.Poly.const 2)
      (Poly.comp (f := fun w : ℚ × ℚ => w.1 - w.2)
        (g := fun z : ℚ × ℚ => (z.1, (1 : ℚ))) Poly.rat_sub
        (Poly.pair (by fun_prop) (Automatic.Poly.const 1))))

/-- The Sherman–Morrison multiplier `λ = β/σ`. -/
def lamOf (p : ℕ × (List ℚ × List ℚ)) : ℚ := betaOf ((p.1 : ℚ), (0 : ℚ)) / sigOf p

/-- `α⁻¹ = (n+1)/(n−1)` (the depth-`1` GLS scaling, `alphaQ n 1` inverted). -/
def alphInv (n : ℕ) : ℚ := ((n : ℚ) + 1) / ((n : ℚ) - 1)

theorem poly_sigOf : Poly sigOf := by
  unfold sigOf
  have hmv : Poly (fun p : ℕ × (List ℚ × List ℚ) =>
      MatQ.Runtime.mulVecRaw (p.1, (p.2.1, p.2.2))) :=
    Poly.comp (f := MatQ.Runtime.mulVecRaw) (g := fun p : ℕ × (List ℚ × List ℚ) => p)
      ⟨MatQ.Runtime.mulVecProgram⟩ (by fun_prop)
  exact Poly.comp (f := dotZ) (g := fun p : ℕ × (List ℚ × List ℚ) =>
    (p.2.2, MatQ.Runtime.mulVecRaw (p.1, (p.2.1, p.2.2)))) poly_dotZ
    (Poly.pair (by fun_prop) hmv)

theorem poly_lamOf : Poly lamOf := by
  unfold lamOf
  have hb : Poly (fun p : ℕ × (List ℚ × List ℚ) => betaOf ((p.1 : ℚ), (0 : ℚ))) :=
    Poly.comp (f := betaOf) (g := fun p : ℕ × (List ℚ × List ℚ) => ((p.1 : ℚ), (0 : ℚ)))
      poly_betaOf (Poly.pair (by fun_prop) (Automatic.Poly.const 0))
  exact Poly.comp (f := fun w : ℚ × ℚ => w.1 / w.2)
    (g := fun p : ℕ × (List ℚ × List ℚ) => (betaOf ((p.1 : ℚ), (0 : ℚ)), sigOf p)) Poly.rat_div
    (Poly.pair hb poly_sigOf)

theorem poly_alphInv : Poly (fun n : ℕ => alphInv n) := by
  unfold alphInv
  exact Poly.comp (f := fun w : ℚ × ℚ => w.1 / w.2)
    (g := fun n : ℕ => ((n : ℚ) + 1, (n : ℚ) - 1)) Poly.rat_div
    (Poly.pair
      (Poly.comp (f := fun w : ℚ × ℚ => w.1 + w.2) (g := fun n : ℕ => ((n : ℚ), (1 : ℚ)))
        Poly.rat_add (Poly.pair (by fun_prop : Poly (fun n : ℕ => (n : ℚ))) (Automatic.Poly.const 1)))
      (Poly.comp (f := fun w : ℚ × ℚ => w.1 - w.2) (g := fun n : ℕ => ((n : ℚ), (1 : ℚ)))
        Poly.rat_sub (Poly.pair (by fun_prop : Poly (fun n : ℕ => (n : ℚ))) (Automatic.Poly.const 1))))

/-! ### 6.2  The oracle and the round -/

/-- `∑ᵢ |Xᵢᵢ − 1|` on the state. -/
def dvR (s : RSt) : ℚ := diagSumV (stN s, stX s)

/-- `[A, X]` on the state. -/
def fvR (s : RSt) : ℚ := frobV (stN s, (stA s, stX s))

/-- The PSD test's answer on the state. -/
def pivAns (s : RSt) : Ans := runPivL ((stMu s, stD s), (toRows (stN s, stX s), []))

/-- The PSD branch's cut data: the witness's `v vᵀ`, or `ok`. -/
def pivCutF (z : ℕ × Ans) : Ans :=
  if z.2.1 then (true, vecMulVecF (z.1, z.2.2)) else (false, [])

/-- The PSD branch on the state. -/
def pivCut (s : RSt) : Ans := pivCutF (stN s, pivAns s)

/-- The threshold branch: `t ≤ [A,X]` asks the PSD test, otherwise the trace cut. -/
def threshB (s : RSt) : Ans := if stT s ≤ fvR s then pivCut s else (true, stA s)

/-- **The separation oracle on the state.**  `(true, c)` = a cut with normal `c`; `(false, [])` = `ok`.
Branches: the summed diagonal cut, the threshold cut, and the normalised pivot descent (§4). -/
def oracleR (s : RSt) : Ans := if dvR s = 0 then threshB s else (true, diagSignF (stN s, stX s))

/-- The Sherman–Morrison output of the round (before scaling and snapping). -/
noncomputable def stepY (s : RSt) : List ℚ :=
  QMCLeafB.MatQUpdate.Step.stepFun
    ((stN s, stX s), ((oracleR s).2, lamOf (stN s, (stX s, (oracleR s).2))))

/-- The depth-`1` GLS scaling `α⁻¹ • ·`, applied to the Sherman–Morrison output. -/
noncomputable def scaleY (s : RSt) : List ℚ :=
  QMCLeafB.MatQUpdate.smulRaw ((stN s, stepY s), alphInv (stN s))

/-- The round's new primal shape: scaled, then **clipped into the state's box and snapped** onto the
state's grid.  The clip is not cosmetic: `snapDiv` alone bounds the height by `h + log d` where `h` is
the height of `stepY`, and the Sherman–Morrison quotient `λ/(1+λσ)` multiplies heights per round, so
without the clip no polynomial `sizes` exists (this is exactly why `SizesProfile` clips).  On a state
already inside the box the clip is inert (`clipRat_of_inBox`). -/
noncomputable def snapY (s : RSt) : List ℚ := nrmRow (stMu s) (stD s) (scaleY s)

/-- The cut branch of one round. -/
noncomputable def roundCut (s : RSt) : RSt :=
  mkSt (stN s) (stA s) (snapY s) (stT s) (stMu s) (stD s) (stOks s ++ [false])
    (oracleR s).2

/-- The `ok` branch of one round: the state is frozen, the round recorded as `ok` (`1`). -/
noncomputable def roundOk (s : RSt) : RSt :=
  mkSt (stN s) (stA s) (stX s) (stT s) (stMu s) (stD s) (stOks s ++ [true]) (stRec s)

/-- **One round of the GLS shallow-cut engine, on the packed state.**  Cut branch: the oracle's
normal, the Sherman–Morrison update `X ← X − (λ/(1+λσ))(Xc)(Xc)ᵀ` at `λ = β/σ`, the depth-`1`
scaling `α⁻¹ = (n+1)/(n−1)` (`rStep`'s `alphaQ n 1`, inverted), then the dyadic snap onto the
state's grid; the round is recorded as a cut (`0`) with its normal appended to `rec`.  `ok` branch:
the state is frozen and the round recorded as `ok` (`1`), so every later round is `ok` again and the
closing stroke's `hcert` sees one and the same primal point across all `ok` rounds. -/
noncomputable def round (s : RSt) : RSt := if (oracleR s).1 then roundCut s else roundOk s

theorem round_eq (s : RSt) : round s = if (oracleR s).1 then roundCut s else roundOk s := rfl

/-! ### 6.3  `Poly` of the round -/

theorem poly_dvR : Poly dvR :=
  Poly.comp (f := fun p : ℕ × List ℚ => diagSumV p)
    (g := fun s : RSt => (stN s, stX s)) poly_diagSumV
    (Poly.pair (f := fun s : RSt => stN s) (g := fun s : RSt => stX s) poly_stN poly_stX)

theorem poly_fvR : Poly fvR :=
  Poly.comp (f := fun q : ℕ × (List ℚ × List ℚ) => frobV q)
    (g := fun s : RSt => (stN s, (stA s, stX s))) poly_frobV
    (Poly.pair (f := fun s : RSt => stN s)
      (g := fun s : RSt => (stA s, stX s)) poly_stN
      (Poly.pair (f := fun s : RSt => stA s) (g := fun s : RSt => stX s) poly_stA poly_stX))

theorem poly_toRowsR : Poly (fun s : RSt => toRows (stN s, stX s)) :=
  Poly.comp (f := fun p : ℕ × List ℚ => toRows p) (g := fun s : RSt => (stN s, stX s)) poly_toRows
    (Poly.pair (f := fun s : RSt => stN s) (g := fun s : RSt => stX s) poly_stN poly_stX)

theorem poly_pivAns : Poly pivAns :=
  Poly.comp (f := fun p : LSt => runPivL p)
    (g := fun s : RSt => ((stMu s, stD s), (toRows (stN s, stX s), []))) poly_runPivL
    (Poly.pair (f := fun s : RSt => (stMu s, stD s))
      (g := fun s : RSt => (toRows (stN s, stX s), ([] : Acc)))
      (Poly.pair (f := fun s : RSt => stMu s) (g := fun s : RSt => stD s) poly_stMu poly_stD)
      (Poly.pair (f := fun s : RSt => toRows (stN s, stX s))
        (g := fun s : RSt => ([] : Acc)) poly_toRowsR (Automatic.Poly.const [])))

theorem poly_pivCutF : Poly pivCutF := by
  have hb : Poly (fun z : ℕ × Ans => z.2.1) := by fun_prop
  have h1 : Poly (fun z : ℕ × Ans => (true, vecMulVecF (z.1, z.2.2))) :=
    Poly.pair (f := fun z : ℕ × Ans => true)
      (g := fun z : ℕ × Ans => vecMulVecF (z.1, z.2.2)) (Automatic.Poly.const true)
      (Poly.comp (f := fun p : ℕ × List ℚ => vecMulVecF p)
        (g := fun z : ℕ × Ans => (z.1, z.2.2)) poly_vecMulVecF
        (Poly.pair (f := fun z : ℕ × Ans => z.1) (g := fun z : ℕ × Ans => z.2.2)
          (by fun_prop) (by fun_prop)))
  have h2 : Poly (fun _ : ℕ × Ans => ((false, ([] : List ℚ)) : Ans)) :=
    Automatic.Poly.const (false, ([] : List ℚ))
  unfold pivCutF
  exact Poly.ite (p := fun z : ℕ × Ans => z.2.1) hb h1 h2

theorem poly_pivCut : Poly pivCut :=
  Poly.comp (f := pivCutF) (g := fun s : RSt => (stN s, pivAns s)) poly_pivCutF
    (Poly.pair (f := fun s : RSt => stN s) (g := fun s : RSt => pivAns s) poly_stN poly_pivAns)

theorem poly_threshB : Poly threshB := by
  have hc : Poly (fun s : RSt => decide (stT s ≤ fvR s)) :=
    Poly.rat_le_comp poly_stT poly_fvR
  have h2 : Poly (fun s : RSt => ((true, stA s) : Ans)) :=
    Poly.pair (f := fun s : RSt => true) (g := fun s : RSt => stA s) (Automatic.Poly.const true)
      poly_stA
  unfold threshB
  exact Poly.ite_prop (p := fun s : RSt => stT s ≤ fvR s) hc poly_pivCut h2

theorem poly_oracleR : Poly oracleR := by
  have hc : Poly (fun s : RSt => decide (dvR s = 0)) :=
    Poly.comp (f := fun q : ℚ => decide (q = 0)) (g := dvR)
      (Poly.rat_eq_comp (Poly.identity (α := ℚ)) (Automatic.Poly.const (0 : ℚ))) poly_dvR
  have h1 : Poly (fun s : RSt => ((true, diagSignF (stN s, stX s)) : Ans)) :=
    Poly.pair (f := fun s : RSt => true) (g := fun s : RSt => diagSignF (stN s, stX s))
      (Automatic.Poly.const true)
      (Poly.comp (f := fun p : ℕ × List ℚ => diagSignF p) (g := fun s : RSt => (stN s, stX s))
        poly_diagSignF
        (Poly.pair (f := fun s : RSt => stN s) (g := fun s : RSt => stX s) poly_stN poly_stX))
  unfold oracleR
  exact Poly.ite_prop (p := fun s : RSt => dvR s = 0) hc poly_threshB h1

theorem poly_stepY : Poly stepY := by
  have hlam : Poly (fun s : RSt => lamOf (stN s, (stX s, (oracleR s).2))) :=
    Poly.comp (f := fun p : ℕ × (List ℚ × List ℚ) => lamOf p)
      (g := fun s : RSt => (stN s, (stX s, (oracleR s).2))) poly_lamOf
      (Poly.pair (f := fun s : RSt => stN s)
        (g := fun s : RSt => (stX s, (oracleR s).2)) poly_stN
        (Poly.pair (f := fun s : RSt => stX s) (g := fun s : RSt => (oracleR s).2) poly_stX
          (Poly.comp (f := fun z : Ans => z.2) (g := oracleR) (by fun_prop) poly_oracleR)))
  have hpair : Poly (fun s : RSt =>
      ((stN s, stX s), ((oracleR s).2, lamOf (stN s, (stX s, (oracleR s).2))))) :=
    Poly.pair (f := fun s : RSt => (stN s, stX s))
      (g := fun s : RSt => ((oracleR s).2, lamOf (stN s, (stX s, (oracleR s).2))))
      (Poly.pair (f := fun s : RSt => stN s) (g := fun s : RSt => stX s) poly_stN poly_stX)
      (Poly.pair (f := fun s : RSt => (oracleR s).2)
        (g := fun s : RSt => lamOf (stN s, (stX s, (oracleR s).2)))
        (Poly.comp (f := fun z : Ans => z.2) (g := oracleR) (by fun_prop) poly_oracleR) hlam)
  unfold stepY
  exact Poly.comp (f := QMCLeafB.MatQUpdate.Step.stepFun) (g := fun s : RSt =>
    ((stN s, stX s), ((oracleR s).2, lamOf (stN s, (stX s, (oracleR s).2)))))
    QMCLeafB.RoundPolySnap.poly_stepFun hpair

theorem poly_scaleY : Poly scaleY := by
  have hpair : Poly (fun s : RSt => ((stN s, stepY s), alphInv (stN s))) :=
    Poly.pair (f := fun s : RSt => (stN s, stepY s)) (g := fun s : RSt => alphInv (stN s))
      (Poly.pair (f := fun s : RSt => stN s) (g := fun s : RSt => stepY s) poly_stN poly_stepY)
      (Poly.comp (f := fun n : ℕ => alphInv n) (g := stN) poly_alphInv poly_stN)
  exact Poly.comp (f := QMCLeafB.MatQUpdate.smulRaw) (g := fun s : RSt =>
    ((stN s, stepY s), alphInv (stN s))) ⟨QMCLeafB.MatQUpdate.smulProgram⟩ hpair

theorem poly_snapY : Poly snapY := by
  have h : Poly (fun s : RSt => nrmRow (stMu s) (stD s) (scaleY s)) :=
    Poly.comp (f := fun p : (ℚ × ℕ) × List ℚ => nrmRow p.1.1 p.1.2 p.2)
      (g := fun s : RSt => ((stMu s, stD s), scaleY s)) poly_nrmRow
      (Poly.pair (f := fun s : RSt => (stMu s, stD s)) (g := fun s : RSt => scaleY s)
        (Poly.pair (f := fun s : RSt => stMu s) (g := fun s : RSt => stD s) poly_stMu poly_stD)
        poly_scaleY)
  unfold snapY
  exact h

theorem poly_mkSt_c {n : RSt → ℕ} {A X : RSt → List ℚ} {t mu : RSt → ℚ}
    {d : RSt → ℕ} {oks : RSt → List Bool} {rec : RSt → List ℚ} (hn : Poly n) (hA : Poly A) (hX : Poly X) (ht : Poly t)
    (hmu : Poly mu) (hd : Poly d) (hoks : Poly oks) (hrec : Poly rec) :
    Poly (fun s : RSt => mkSt (n s) (A s) (X s) (t s) (mu s) (d s) (oks s) (rec s)) := by
  unfold mkSt
  exact Poly.pair
    (Poly.pair (Poly.pair hn hA) (Poly.pair hX (Poly.pair ht hmu)))
    (Poly.pair (Poly.pair hd hoks) hrec)

theorem poly_roundCut : Poly roundCut := by
  have hoks : Poly (fun s : RSt => stOks s ++ ([false] : List Bool)) :=
    Poly.comp (f := fun z : List Bool × List Bool => z.1 ++ z.2)
      (g := fun s : RSt => (stOks s, ([false] : List Bool)))
      (Poly.list_append (α := Bool))
      (Poly.pair (f := fun s : RSt => stOks s) (g := fun s : RSt => ([false] : List Bool))
        poly_stOks (Automatic.Poly.const [false]))
  have hrec : Poly (fun s : RSt => (oracleR s).2) :=
    Poly.comp (f := fun z : Ans => z.2) (g := oracleR) (by fun_prop) poly_oracleR
  exact poly_mkSt_c poly_stN poly_stA poly_snapY poly_stT poly_stMu poly_stD hoks hrec

theorem poly_roundOk : Poly roundOk := by
  have hoks : Poly (fun s : RSt => stOks s ++ ([true] : List Bool)) :=
    Poly.comp (f := fun z : List Bool × List Bool => z.1 ++ z.2)
      (g := fun s : RSt => (stOks s, ([true] : List Bool)))
      (Poly.list_append (α := Bool))
      (Poly.pair (f := fun s : RSt => stOks s) (g := fun s : RSt => ([true] : List Bool))
        poly_stOks (Automatic.Poly.const [true]))
  exact poly_mkSt_c poly_stN poly_stA poly_stX poly_stT poly_stMu poly_stD hoks poly_stRec

theorem poly_cutFlag : Poly (fun s : RSt => (oracleR s).1) :=
  Poly.comp (f := fun z : Ans => z.1) (g := oracleR) (by fun_prop) poly_oracleR

/-- **The round is an `Automatic.Poly` program** — no hypothesis at all. -/
theorem poly_round : Poly round := by
  have h : round = (fun s : RSt => if (oracleR s).1 then roundCut s else roundOk s) := by
    funext s
    exact round_eq s
  rw [h]
  exact Poly.ite (p := fun s : RSt => (oracleR s).1) poly_cutFlag poly_roundCut poly_roundOk

/-! ## 7.  The size slot's easy half, `hsize0`

`solution_of_loop_via_runData` asks for two size facts.  `hsize0` is the trivial one and is discharged
here at the same monomial as the descent (`44000·(X+1)^5`); `hsize` (the forward invariance of the ball)
is **not** discharged, and there is a counting argument
(`hsize-obstruction.md` in the member's directory) that it cannot be, for this stroke as stated:
its RHS does not mention the quantified state, and one fuel bit is exactly as expensive as one `ok`
flag, so it forces the round to be length-non-increasing, which no `Poly` round with `n²` entries can
be. -/

/-- The `sizes` monomial proposed to the closing stroke. -/
noncomputable def sizesPoly : Polynomial ℕ := Polynomial.C 44000 * (Polynomial.X + 1) ^ 5

theorem sizesPoly_eval (L : ℕ) : sizesPoly.eval L = 44000 * (L + 1) ^ 5 := by
  simp [sizesPoly, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_pow]

/-- `L ≤ 44000·(L+1)^5` — the reason `hsize0` is free. -/
theorem le_sizesPoly_eval (L : ℕ) : L ≤ sizesPoly.eval L := by
  rw [sizesPoly_eval]
  have hp : L + 1 ≤ (L + 1) ^ 5 := by
    rw [show (5:ℕ) = 4 + 1 by norm_num, pow_succ]
    calc L + 1 = (L + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (L + 1) * (L + 1) ^ 4 := Nat.mul_le_mul_left _ (pow_pos (Nat.succ_pos _) 4)
      _ = (L + 1) ^ 4 * (L + 1) := Nat.mul_comm _ _
  have h4 : (L + 1) ^ 5 ≤ 44000 * (L + 1) ^ 5 := by
    calc (L + 1) ^ 5 = 1 * (L + 1) ^ 5 := (Nat.one_mul _).symm
      _ ≤ 44000 * (L + 1) ^ 5 := Nat.mul_le_mul_right _ (by norm_num : 1 ≤ 44000)
  exact Nat.le_trans (Nat.le_succ L) (Nat.le_trans hp h4)

/-- **`hsize0` holds** at `sizesPoly`, for the state encoding `SimPoly.encSt`. -/
theorem hsize0_holds (a : RSt × List Bool) :
    (QMCLeafB.SimPoly.encSt a).length
      ≤ sizesPoly.eval (QMCLeafB.SimPoly.encSt a).length :=
  le_sizesPoly_eval _

/-! ## 8.  The verdict bit `o`, and `hspec`, reduced to tape-freeness

`solution_of_loop_via_runData`'s `hspec` is

    ∀ p, verdict (Nat.iterate round (fuel p).length (init p)) = o p.1.1 p.2

`o : Input → ℚ → Bool` does **not** see the random tape `p.1.2`, while `init` and `fuel` may.  So
`hspec` is exactly the statement that `init` and `fuel` do not read the tape.  The lemma below fixes
the shape of `o` (it must be the `verdict` of the loop at the *tape-free* initial state and round
count) and reduces `hspec` to the two tape-freeness equations — which is what `init-and-verdict` and
`fuel-count` must deliver.  This is the only place the tape enters the round brick. -/

/-- **`hspec` from tape-freeness.**  If `init` and the round count do not depend on the random tape,
then `o` is the loop's verdict and `hspec` holds definitionally. -/
theorem hspec_of_tapeFree
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (init0 : QuantumMaxCutEnergy.Input → ℚ → RSt)
    (T : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinit : ∀ (G : QuantumMaxCutEnergy.Input) (σ : List Bool) (t : ℚ),
      init ((G, σ), t) = init0 G t)
    (hfuel : ∀ (G : QuantumMaxCutEnergy.Input) (σ : List Bool) (t : ℚ),
      (fuel ((G, σ), t)).length = T G t) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (fuel p).length (init p))
        = (fun (G : QuantumMaxCutEnergy.Input) (t : ℚ) =>
            verdict (Nat.iterate round (T G t) (init0 G t))) p.1.1 p.2 := by
  rintro ⟨⟨G, σ⟩, t⟩
  rw [hfuel G σ t, hinit G σ t]

/-- **The recommended shape of `o`** for the closing stroke: the verdict of the tape-free loop. -/
noncomputable def oOf (init0 : QuantumMaxCutEnergy.Input → ℚ → RSt)
    (T : QuantumMaxCutEnergy.Input → ℚ → ℕ) (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Bool :=
  verdict (Nat.iterate round (T G t) (init0 G t))

/-- `hspec_of_tapeFree`, stated with `oOf`. -/
theorem hspec_oOf
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (init0 : QuantumMaxCutEnergy.Input → ℚ → RSt)
    (T : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinit : ∀ (G : QuantumMaxCutEnergy.Input) (σ : List Bool) (t : ℚ),
      init ((G, σ), t) = init0 G t)
    (hfuel : ∀ (G : QuantumMaxCutEnergy.Input) (σ : List Bool) (t : ℚ),
      (fuel ((G, σ), t)).length = T G t) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (fuel p).length (init p)) = oOf init0 T p.1.1 p.2 :=
  hspec_of_tapeFree init fuel init0 T hinit hfuel

/-! ## 9.  `RunData.hverdict`: `anyOk` *is* `verdict` on the record

If the assembly defines the run's `ok : ℕ → Bool` from the iterates and the state records
`oks = (List.range N).map ok`, then `RunData.hverdict`
(`o G t = anyOk ok (K*m)`) is the theorem below plus `o = oOf init0 T` — no extra mathematics. -/

/-- The verdict bit on a list of flags. -/
def anyL (l : List Bool) : Bool := decide (0 < (l.filter id).length)

theorem verdict_eq_anyL (s : RSt) : verdict s = anyL (stOks s) := rfl

/-- **`SimLoop.anyOk` is `anyL` of the flag list.** -/
theorem anyOk_eq_anyL (ok : ℕ → Bool) :
    ∀ N : ℕ, QMCLeafB.SimLoop.anyOk ok N = anyL ((List.range N).map ok)
  | 0 => by
      simp [QMCLeafB.SimLoop.anyOk, anyL]
  | (k + 1) => by
      rw [QMCLeafB.SimLoop.anyOk_succ, anyOk_eq_anyL ok k]
      cases h : ok k <;> simp [anyL, List.range_succ, h]

/-- `RunData.hverdict` at the concrete verdict: if the state's flag list is the run's `ok` prefix,
the verdict bit is exactly `SimLoop.anyOk ok N`. -/
theorem verdict_eq_anyOk {s : RSt} {ok : ℕ → Bool} {N : ℕ}
    (h : stOks s = (List.range N).map ok) :
    verdict s = QMCLeafB.SimLoop.anyOk ok N := by
  rw [verdict_eq_anyL, h, ← anyOk_eq_anyL]

/-! ## 10.  Axiom audit -/

#print axioms QMCLeafB.RoundProgram.poly_verdict
#print axioms QMCLeafB.RoundProgram.hasHeight_nrmQ
#print axioms QMCLeafB.RoundProgram.poly_pivStepL
#print axioms QMCLeafB.RoundProgram.poly_runPivL
#print axioms QMCLeafB.RoundProgram.poly_diagSumV
#print axioms QMCLeafB.RoundProgram.poly_frobV
#print axioms QMCLeafB.RoundProgram.poly_vecMulVecF
#print axioms QMCLeafB.RoundProgram.poly_diagSignF
#print axioms QMCLeafB.RoundProgram.poly_sigOf
#print axioms QMCLeafB.RoundProgram.poly_lamOf
#print axioms QMCLeafB.RoundProgram.poly_oracleR
#print axioms QMCLeafB.RoundProgram.poly_stepY
#print axioms QMCLeafB.RoundProgram.poly_scaleY
#print axioms QMCLeafB.RoundProgram.poly_snapY
#print axioms QMCLeafB.RoundProgram.poly_roundCut
#print axioms QMCLeafB.RoundProgram.poly_roundOk
#print axioms QMCLeafB.RoundProgram.poly_round
#print axioms QMCLeafB.RoundProgram.le_sizesPoly_eval
#print axioms QMCLeafB.RoundProgram.hsize0_holds
#print axioms QMCLeafB.RoundProgram.hspec_of_tapeFree
#print axioms QMCLeafB.RoundProgram.hspec_oOf
#print axioms QMCLeafB.RoundProgram.anyOk_eq_anyL
#print axioms QMCLeafB.RoundProgram.verdict_eq_anyOk
#print axioms QMCLeafB.RoundProgram.sizesPoly_eval

#check @QMCLeafB.RoundProgram.poly_round
#check @QMCLeafB.RoundProgram.poly_runPivL
#check @QMCLeafB.RoundProgram.poly_verdict
#check @QMCLeafB.RoundProgram.round
#check @QMCLeafB.RoundProgram.RSt
#check @QMCLeafB.RoundProgram.mkSt
#check @QMCLeafB.RoundProgram.oracleR
#check @QMCLeafB.RoundProgram.szPoly_eval

end QMCLeafB.RoundProgram


