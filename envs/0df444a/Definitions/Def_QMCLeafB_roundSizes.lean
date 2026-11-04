-- Prove2me | Definitions.Def_QMCLeafB_roundSizes
-- name    : QMCLeafB_roundSizes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:46:26.512579+00:00
-- url     : https://prove2.me/theorems/3d4435d5-9a51-454c-9aa6-bdf0280873ef
-- title:
--   QMCLeafB roundSizes
-- statement:
--   # leaf B phase 14 — the size slot at `RSt`: encoding ledger, the obstruction, and the fuel-joint repair
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_RStInit
/-
# leaf B phase 14 — the size slot at `RSt`: encoding ledger, the obstruction, and the fuel-joint repair
(member m1, direction d7)

## Why this file exists

Every closing stroke on the shelf carries a size hypothesis.  At `RoundProgram.RSt` the shape offered
by `QMCLeafB.FinalReunion.endgame_RSt` (and by `endgame_orbit`/`endgame_orbit_sq` at the other σ) is

    hmono : ∀ (s : σ) (j : ℕ), (enc (round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k.

**That hypothesis is unsatisfiable**, and §2 below proves it: `RoundProgram.round` appends exactly one
flag to `stOks` per call (`RStInit.stOks_round`), the flag list is a field of `σ`, one flag costs `3`
encoded bits (`encodeBool b = [b]` inside `encodeList`), so the encoded length of the iterate grows
linearly in `j` while the right-hand side is a constant once `s` is fixed.  m7's remark
(`Check_final_stroke_m7.lean:439`) identifies the cause and the cure — *the fuel pays for the flags,
and the fuel is not part of `σ`* — but the stated theorems still ask for the state-only form, so the
integration has to switch to the **joint** envelope that `QMCLeafB.FinalStroke.endgame_orbit_of_parts`
consumes:

    horbit : ∀ (a : σ × List Bool) (j : ℕ), j ≤ a.2.length →
      (encSt (round^[j] a.1, a.2.drop j)).length ≤ sizes.eval ((encSt a).length).

§4 supplies exactly that, from the *honest* per-round class

    hstate : ∀ (s : RSt) (T : ℕ), (enc (round^[T] s)).length ≤ C * ((enc s).length + 1) ^ kB + 3 * T

— a monomial in the *state* plus the honest `3` bits per round for the flag — and shows the `+3T` is
absorbed by the fuel (`3 * j ≤ (encSt a).length` whenever `j ≤ a.2.length`), at the cost of the
constant `2C+2` (`sizesOrbitPow C kB`).  §5 assembles the endgame at `RSt` with that slot; the only
size obligation left is `hstate`, which is a length bound on the round *alone* (no round index).

## Contents

* §1 encoded lengths of the packed state: the flag list's `3` bits per element, field monotonicity,
  the full 8-field formula, and the joint `(state, fuel)` formula.
* §2 the obstruction `state_only_monomial_fails`.
* §3 the clip at `mu = 2n²+2` is inert on PSD unit-diagonal shapes: `|Xᵢⱼ| ≤ 1` over `ℚ`
  (`RoundingOut.abs_entry_le` at `ν = 0`), hence `nrmQ`/`nrmRow` are pure snaps there.
* §4 `horbit_of_honest_class` and the endgame `endgame_RSt_joint`.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.RoundSizes

open QuantumMaxCutEnergy

local instance instRequestCodingM1b :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  Encoded lengths of the packed state -/

theorem encodeList_bool_length : ∀ l : List Bool, (encodeList encodeBool l).length = 3 * l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons b t ih =>
      rw [EncodedList.cons_length, ih]
      simp [encodeBool]
      ring

/-- **One flag costs three bits.** -/
theorem enc_bool_list (l : List Bool) : (enc l).length = 3 * l.length :=
  encodeList_bool_length l

theorem enc_fst_le {α β : Type} [Coding α] [Coding β] (x : α × β) :
    (enc x.1).length ≤ (enc x).length := by
  have h : (enc x).length = 2 * (enc x.1).length + 1 + (enc x.2).length :=
    encodePair_length (enc : α → List Bool) (enc : β → List Bool) x
  omega

theorem enc_snd_le {α β : Type} [Coding α] [Coding β] (x : α × β) :
    (enc x.2).length ≤ (enc x).length := by
  have h : (enc x).length = 2 * (enc x.1).length + 1 + (enc x.2).length :=
    encodePair_length (enc : α → List Bool) (enc : β → List Bool) x
  omega

/-- **The flag list is paid for, three bits a flag.**  This is the whole obstruction in one line: the
state's own encoding contains its flag list at full price. -/
theorem enc_ge_oks (s : QMCLeafB.RoundProgram.RSt) :
    3 * (QMCLeafB.RoundProgram.stOks s).length ≤ (enc s).length := by
  have h1 : (enc s).length
      = 2 * (enc s.1).length + 1 + (enc s.2).length :=
    encodePair_length _ _ s
  have h2 : (enc s.2).length
      = 2 * (enc s.2.1).length + 1 + (enc s.2.2).length :=
    encodePair_length _ _ s.2
  have h3 : (enc s.2.1).length
      = 2 * (enc s.2.1.1).length + 1 + (enc s.2.1.2).length :=
    encodePair_length _ _ s.2.1
  have h4 : (enc s.2.1.2).length = 3 * (QMCLeafB.RoundProgram.stOks s).length := by
    rw [enc_bool_list]
    rfl
  omega

/-- **The encoded length of the packed state, field by field.** -/
theorem enc_len_formula (s : QMCLeafB.RoundProgram.RSt) :
    (enc s).length
      = 2 * (2 * (2 * (enc (QMCLeafB.RoundProgram.stN s)).length + 1
              + (enc (QMCLeafB.RoundProgram.stA s)).length)
            + 1
            + (2 * (enc (QMCLeafB.RoundProgram.stX s)).length + 1
              + (2 * (enc (QMCLeafB.RoundProgram.stT s)).length + 1
                + (enc (QMCLeafB.RoundProgram.stMu s)).length)))
        + 1
        + (2 * (2 * (enc (QMCLeafB.RoundProgram.stD s)).length + 1
              + (enc (QMCLeafB.RoundProgram.stOks s)).length)
            + 1
            + (enc (QMCLeafB.RoundProgram.stRec s)).length) := by
  have h1 : (enc s).length
      = 2 * (enc s.1).length + 1 + (enc s.2).length :=
    encodePair_length _ _ s
  have h2 : (enc s.2).length
      = 2 * (enc s.2.1).length + 1 + (enc s.2.2).length :=
    encodePair_length _ _ s.2
  have h3 : (enc s.2.1).length
      = 2 * (enc s.2.1.1).length + 1 + (enc s.2.1.2).length :=
    encodePair_length _ _ s.2.1
  have h4 : (enc s.1).length
      = 2 * (enc s.1.1).length + 1 + (enc s.1.2).length :=
    encodePair_length _ _ s.1
  have h5 : (enc s.1.2).length
      = 2 * (enc s.1.2.1).length + 1 + (enc s.1.2.2).length :=
    encodePair_length _ _ s.1.2
  have h6 : (enc s.1.2.2).length
      = 2 * (enc s.1.2.2.1).length + 1 + (enc s.1.2.2.2).length :=
    encodePair_length _ _ s.1.2.2
  have h7 : (enc s.1.1).length
      = 2 * (enc s.1.1.1).length + 1 + (enc s.1.1.2).length :=
    encodePair_length _ _ s.1.1
  unfold QMCLeafB.RoundProgram.stN QMCLeafB.RoundProgram.stA QMCLeafB.RoundProgram.stX
    QMCLeafB.RoundProgram.stT QMCLeafB.RoundProgram.stMu QMCLeafB.RoundProgram.stD
    QMCLeafB.RoundProgram.stOks QMCLeafB.RoundProgram.stRec
  omega

/-- **The joint `(state, fuel)` encoding**: the state's encoding, plus the fuel at three bits a bit. -/
theorem encSt_len {σ : Type} [Coding σ] (a : σ × List Bool) :
    (QMCLeafB.SimPoly.encSt a).length = 2 * (enc a.1).length + 1 + 3 * a.2.length := by
  have h := encodePair_length (enc : σ → List Bool) (enc : List Bool → List Bool) a
  rw [enc_bool_list] at h
  exact h

/-- **A rational list's encoding, from the heights of its entries.**  The missing piece between a
height bound (`nrmRow_height`, `hasHeight_nrmQ`, `HasHeight.mul`) and an encoded-length bound: every
entry costs at most `3H + 10` bits (`CertSize.encode_length_le_of_hasHeight`), and the list coding adds
one separator per entry. -/
theorem encList_rat_length_le (l : List ℚ) {H : ℕ} (h : ∀ q ∈ l, HasHeight q H) :
    (encodeList Ratio.encode l).length ≤ l.length * (6 * H + 21) := by
  induction l with
  | nil => simp [encodeList]
  | cons a t ih =>
      have hentry : (Ratio.encode a).length ≤ 3 * H + 10 :=
        QMCLeafB.CertSize.encode_length_le_of_hasHeight (h a (by simp))
      have htail := ih (fun q hq => h q (List.mem_cons_of_mem a hq))
      rw [EncodedList.cons_length, List.length_cons]
      have hstep : 2 * (Ratio.encode a).length + 1 ≤ 6 * H + 21 := by omega
      calc 2 * (Ratio.encode a).length + 1 + (encodeList Ratio.encode t).length
          ≤ (6 * H + 21) + t.length * (6 * H + 21) := Nat.add_le_add hstep htail
        _ = (t.length + 1) * (6 * H + 21) := by ring

/-- The same at the state's shape register. -/
theorem enc_stX_le (s : QMCLeafB.RoundProgram.RSt) {H : ℕ}
    (h : ∀ q ∈ QMCLeafB.RoundProgram.stX s, HasHeight q H) :
    (enc (QMCLeafB.RoundProgram.stX s)).length
      ≤ (QMCLeafB.RoundProgram.stX s).length * (6 * H + 21) :=
  encList_rat_length_le _ h

/-- The same at the state's weight-matrix register. -/
theorem enc_stA_le (s : QMCLeafB.RoundProgram.RSt) {H : ℕ}
    (h : ∀ q ∈ QMCLeafB.RoundProgram.stA s, HasHeight q H) :
    (enc (QMCLeafB.RoundProgram.stA s)).length
      ≤ (QMCLeafB.RoundProgram.stA s).length * (6 * H + 21) :=
  encList_rat_length_le _ h

/-- The same at the state's recorded-normal register. -/
theorem enc_stRec_le (s : QMCLeafB.RoundProgram.RSt) {H : ℕ}
    (h : ∀ q ∈ QMCLeafB.RoundProgram.stRec s, HasHeight q H) :
    (enc (QMCLeafB.RoundProgram.stRec s)).length
      ≤ (QMCLeafB.RoundProgram.stRec s).length * (6 * H + 21) :=
  encList_rat_length_le _ h

/-- A bound on `enc` of a `List ℚ` from its own length, at the invariant height `H`. -/
theorem enc_le_of_heights (l : List ℚ) {H : ℕ} (h : ∀ q ∈ l, HasHeight q H) :
    (enc l).length ≤ l.length * (6 * H + 21) :=
  encList_rat_length_le l h

/-- **The fuel pays for the flags**: at every round of the run (`j ≤ fuel length`) the flags written
so far cost at most the joint encoding's length. -/
theorem flags_paid_by_fuel (a : QMCLeafB.RoundProgram.RSt × List Bool) (j : ℕ)
    (hj : j ≤ a.2.length) : 3 * j ≤ (QMCLeafB.SimPoly.encSt a).length := by
  rw [encSt_len]
  omega

/-! ## 2.  The obstruction: the state-only monomial class is unsatisfiable -/

/-- **`hmono` of `endgame_orbit`/`endgame_orbit_sq`/`endgame_RSt` is FALSE.**  The round appends one
flag per call (`RStInit.stOks_round`, hence `RStInit.stOks_iterate`), the flag list is a field of the
state, and one flag costs three bits; the iterate's encoding therefore grows without bound while the
right-hand side is fixed by the starting state. -/
theorem state_only_monomial_fails (C k : ℕ) :
    ¬ ∀ (s : QMCLeafB.RoundProgram.RSt) (j : ℕ),
        (enc (QMCLeafB.RoundProgram.round^[j] s)).length
          ≤ C * ((enc s).length + 1) ^ k := by
  intro h
  let s0 : QMCLeafB.RoundProgram.RSt := QMCLeafB.RoundProgram.mkSt 0 [] [] 0 0 0 [] []
  let M : ℕ := C * ((enc s0).length + 1) ^ k
  have hJ : (enc (QMCLeafB.RoundProgram.round^[M + 1] s0)).length ≤ M := h s0 (M + 1)
  have hoks : (QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundProgram.round^[M + 1] s0)).length
      = M + 1 := by
    rw [QMCLeafB.RStInit.stOks_iterate]
    simp [s0, M]
  have h3 := enc_ge_oks (QMCLeafB.RoundProgram.round^[M + 1] s0)
  omega

/-- The same, in the exact shape of the closing stroke's hypothesis: there is no constant and no
exponent that make the state-only orbit class hold. -/
theorem no_state_only_orbit_class :
    ¬ ∃ C k : ℕ, 1 ≤ k ∧ ∀ (s : QMCLeafB.RoundProgram.RSt) (j : ℕ),
        (enc (QMCLeafB.RoundProgram.round^[j] s)).length
          ≤ C * ((enc s).length + 1) ^ k := by
  rintro ⟨C, k, -, h⟩
  exact state_only_monomial_fails C k h

/-! ## 3.  The clip at `mu = 2n²+2` is inert on PSD unit-diagonal shapes

The round clips every entry into `|q| ≤ stMu s` before snapping (`nrmQ`).  At the initial state
`stMu = 2n² + 2dq² ≥ 1` (`RStInit.muOf_ge_one`), and a PSD shape with unit diagonal has all entries in
`[-1,1]` — over `ℚ`, from the two sign tests alone (`RoundingOut.two_mul_abs_entry_le_diag_add`).  So
on the feasible range the round's normalisation is a pure snap, and the clip only truncates the
infeasible excursions. -/

/-- **A PSD unit-diagonal rational shape has entries in `[-1,1]`.** -/
theorem abs_entry_le_one {n : ℕ} {X : Matrix (Fin n) (Fin n) ℚ} (hX : Xᵀ = X)
    (hXp : QMCLeafB.RoundingOut.RatPSD X) (hdiag : ∀ i, X i i = 1) (i j : Fin n) :
    |X i j| ≤ 1 := by
  have h := QMCLeafB.RoundingOut.abs_entry_le (ν := 0) hX hXp (fun k => by
    rw [hdiag k, sub_self, abs_zero]) i j
  simpa using h

/-- The initial box bound is `≥ 1`, so the clip is the identity on `[-1,1]`. -/
theorem clipRat_muOf_eq (n : ℕ) {q : ℚ} (h : |q| ≤ 1) :
    QMCLeafB.RoundProgram.clipRat (QMCLeafB.RStInit.muOf n) q = q :=
  QMCLeafB.RStInit.clipRat_muOf_of_abs_le_one n h

/-- **On the feasible range the round's normalisation of one entry is a pure snap.** -/
theorem nrmQ_muOf_eq_snapDiv (n d : ℕ) {q : ℚ} (h : |q| ≤ 1) :
    QMCLeafB.RoundProgram.nrmQ (QMCLeafB.RStInit.muOf n) d q
      = QMCLeafB.RoundPolySnap.snapDiv d q := by
  unfold QMCLeafB.RoundProgram.nrmQ
  rw [clipRat_muOf_eq n h]

/-- **…and of a whole shape.** -/
theorem nrmRow_muOf_eq_map_snapDiv (n d : ℕ) {v : List ℚ} (h : ∀ q ∈ v, |q| ≤ 1) :
    QMCLeafB.RoundProgram.nrmRow (QMCLeafB.RStInit.muOf n) d v
      = v.map (QMCLeafB.RoundPolySnap.snapDiv d) := by
  unfold QMCLeafB.RoundProgram.nrmRow
  exact List.map_congr_left (fun q hq => nrmQ_muOf_eq_snapDiv n d (h q hq))

/-! ## 4.  The honest per-round class gives the fuel-joint orbit envelope -/

/-- The arithmetic core: the flag's `3` bits per round are absorbed by the joint encoding, at the
cost of the constant `2C+2`. -/
theorem arith_core {C kB L j A : ℕ} (hkB : 1 ≤ kB) (hjA : j ≤ A) (h3A : 3 * A ≤ L) :
    2 * (C * (L + 1) ^ kB + 3 * j) + 1 + 3 * (A - j) ≤ (2 * C + 2) * (L + 1) ^ kB := by
  set M := (L + 1) ^ kB with hM
  have hM1 : L + 1 ≤ M := by
    rw [hM]
    have h := Nat.pow_le_pow_right (by omega : 0 < L + 1) hkB
    simpa using h
  have hexp : (2 * C + 2) * M = 2 * (C * M) + 2 * M := by ring
  rw [hexp]
  have hsub : 3 * (A - j) = 3 * A - 3 * j := Nat.mul_sub _ _ _
  have h3j : 3 * j ≤ 3 * A := Nat.mul_le_mul_left 3 hjA
  have h6A : 6 * A ≤ 2 * L := by omega
  omega

/-- **The fuel-joint orbit envelope from a single bound at round `j`.**  This is the arithmetic core:
if the `j`-th iterate's encoding is at most the state's monomial plus `3j` (the flags), the joint
`(state, fuel)` encoding of the pair `(round^[j] a.1, fuel.drop j)` is inside `sizesOrbitPow C kB`. -/
theorem horbit_of_single (C kB : ℕ) (hkB : 1 ≤ kB)
    (a : QMCLeafB.RoundProgram.RSt × List Bool) (j : ℕ) (hj : j ≤ a.2.length)
    (hbound : (enc (QMCLeafB.RoundProgram.round^[j] a.1)).length
      ≤ C * ((enc a.1).length + 1) ^ kB + 3 * j) :
    (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundProgram.round^[j] a.1, a.2.drop j)).length
      ≤ (QMCLeafB.FinalStroke.sizesOrbitPow C kB).eval
          ((QMCLeafB.SimPoly.encSt a).length) := by
  simp only [QMCLeafB.FinalStroke.sizesOrbitPow_eval, encSt_len]
  have hbase : (enc a.1).length + 1
      ≤ 2 * (enc a.1).length + 1 + 3 * a.2.length + 1 := by omega
  have hmono : (enc (QMCLeafB.RoundProgram.round^[j] a.1)).length
      ≤ C * (2 * (enc a.1).length + 1 + 3 * a.2.length + 1) ^ kB + 3 * j := by
    refine le_trans hbound ?_
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase kB)) _
  have hdrop : (a.2.drop j).length = a.2.length - j := List.length_drop
  have h3A : 3 * a.2.length ≤ 2 * (enc a.1).length + 1 + 3 * a.2.length := by omega
  rw [hdrop]
  have s1 : 2 * (enc (QMCLeafB.RoundProgram.round^[j] a.1)).length + 1
      ≤ 2 * (C * (2 * (enc a.1).length + 1 + 3 * a.2.length + 1) ^ kB + 3 * j) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 hmono) 1
  exact le_trans (Nat.add_le_add_right s1 (3 * (a.2.length - j))) (arith_core hkB hj h3A)

/-- **The fuel-joint orbit envelope, from the honest (state-monomial + 3-per-round) class.**  This is
the `horbit` slot of `QMCLeafB.FinalStroke.endgame_orbit_of_parts`, at `sizes = sizesOrbitPow C kB`.

Note that `hstate` is quantified over *all* states and round counts; §4b replaces it by the single-step
form measured against the initial state, which is what a heights-along-the-run ledger produces. -/
theorem horbit_of_honest_class (C kB : ℕ) (hkB : 1 ≤ kB)
    (hstate : ∀ (s : QMCLeafB.RoundProgram.RSt) (T : ℕ),
      (enc (QMCLeafB.RoundProgram.round^[T] s)).length
        ≤ C * ((enc s).length + 1) ^ kB + 3 * T)
    (a : QMCLeafB.RoundProgram.RSt × List Bool) (j : ℕ) (hj : j ≤ a.2.length) :
    (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundProgram.round^[j] a.1, a.2.drop j)).length
      ≤ (QMCLeafB.FinalStroke.sizesOrbitPow C kB).eval
          ((QMCLeafB.SimPoly.encSt a).length) :=
  horbit_of_single C kB hkB a j hj (hstate a.1 j)

/-! ### 4b.  Only a *single-step* bound along the orbit is needed

The honest class of §4 still quantifies over every state and every round count.  A heights-along-the-run
ledger cannot deliver that (it knows nothing about states off the run); what it *can* deliver is the
single step, measured against the starting state:

    hstep : ∀ j, j < fuel.length →
      (enc (round (round^[j] s₀))).length ≤ C * ((enc s₀).length + 1) ^ kB + 3 * (j + 1)

("the state at round `j+1` costs at most `C` times the *initial* state's monomial, plus the `j+1`
flags").  That is enough: the `j`-form follows by one `≤` at `j = 0` and the step at `j - 1`. -/

/-- **A single-step orbit bound gives the honest class along the orbit.** -/
theorem state_class_of_step (C kB : ℕ) (hkB : 1 ≤ kB) (hC : 1 ≤ C)
    (a : QMCLeafB.RoundProgram.RSt × List Bool)
    (hstep : ∀ j, j < a.2.length →
      (enc (QMCLeafB.RoundProgram.round (QMCLeafB.RoundProgram.round^[j] a.1))).length
        ≤ C * ((enc a.1).length + 1) ^ kB + 3 * (j + 1)) :
    ∀ j, j ≤ a.2.length →
      (enc (QMCLeafB.RoundProgram.round^[j] a.1)).length
        ≤ C * ((enc a.1).length + 1) ^ kB + 3 * j := by
  intro j
  induction j with
  | zero =>
      intro _
      have h1 : (enc a.1).length + 1 ≤ ((enc a.1).length + 1) ^ kB := by
        have h := Nat.pow_le_pow_right (by omega : 0 < (enc a.1).length + 1) hkB
        simpa using h
      have h2 : (enc a.1).length ≤ C * ((enc a.1).length + 1) ^ kB := by
        calc (enc a.1).length ≤ (enc a.1).length + 1 := by omega
          _ ≤ ((enc a.1).length + 1) ^ kB := h1
          _ ≤ C * ((enc a.1).length + 1) ^ kB := Nat.le_mul_of_pos_left _ (by omega)
      simpa using h2
  | succ k ih =>
      intro hk
      rw [Function.iterate_succ_apply']
      exact hstep k (by omega)

/-- **The fuel-joint envelope, from the single-step orbit bound.**  This is the usable form of the size
slot at `RSt`: the remaining obligation is one length bound for one round, measured against the
starting state. -/
theorem horbit_of_orbit_step (C kB : ℕ) (hkB : 1 ≤ kB) (hC : 1 ≤ C)
    (a : QMCLeafB.RoundProgram.RSt × List Bool)
    (hstep : ∀ j, j < a.2.length →
      (enc (QMCLeafB.RoundProgram.round (QMCLeafB.RoundProgram.round^[j] a.1))).length
        ≤ C * ((enc a.1).length + 1) ^ kB + 3 * (j + 1))
    (j : ℕ) (hj : j ≤ a.2.length) :
    (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundProgram.round^[j] a.1, a.2.drop j)).length
      ≤ (QMCLeafB.FinalStroke.sizesOrbitPow C kB).eval
          ((QMCLeafB.SimPoly.encSt a).length) :=
  horbit_of_single C kB hkB a j hj (state_class_of_step C kB hkB hC a hstep j hj)

/-- The envelope in the exact shape the endgame consumes. -/
theorem horbit_RSt (C kB : ℕ) (hkB : 1 ≤ kB)
    (hstate : ∀ (s : QMCLeafB.RoundProgram.RSt) (T : ℕ),
      (enc (QMCLeafB.RoundProgram.round^[T] s)).length
        ≤ C * ((enc s).length + 1) ^ kB + 3 * T) :
    ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundProgram.round^[j] a.1, a.2.drop j)).length
        ≤ (QMCLeafB.FinalStroke.sizesOrbitPow C kB).eval
            ((QMCLeafB.SimPoly.encSt a).length) :=
  fun a j hj => horbit_of_honest_class C kB hkB hstate a j hj

/-! ## 5.  The endgame at `RSt` with the honest size class

The `hmono` argument of `QMCLeafB.FinalReunion.endgame_RSt` is replaced by §4's honest class; nothing
else changes, so the residual is the same as there (`K`, `rmax`, `m`, `hhalve`, the fuel length and
`RunParts` per bracketed `(G,t)`) plus `hstate`. -/

theorem endgame_RSt_joint
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G 1 m ≤ K G)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (C kB : ℕ) (hkB : 1 ≤ kB)
    (hstate : ∀ (s : QMCLeafB.RoundProgram.RSt) (T : ℕ),
      (enc (QMCLeafB.RoundProgram.round^[T] s)).length
        ≤ C * ((enc s).length + 1) ^ kB + 3 * T)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict (fun G' _ => K G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G 1 (by norm_num) rmax hrmax m hm1 (K G) (hK G)
          (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_orbit_of_parts
    QMCLeafB.RStInit.init0 fuel QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    QMCLeafB.RStInit.poly_init0 hfuel QMCLeafB.RoundProgram.poly_round
    QMCLeafB.RoundProgram.poly_verdict
    (QMCLeafB.FinalStroke.sizesOrbitPow C kB)
    (horbit_RSt C kB hkB hstate)
    (fun G' _ => K G' * m)
    QMCLeafB.RStInit.init0_tape hfuelLen
    (fun G t _ hlo hhi => (hd G t hlo hhi).toRunData)

/-- **The endgame at `RSt` with the size slot in single-step orbit form.**  Same as `endgame_RSt_joint`
but the size hypothesis is one round's length bound measured against the starting state (`hstep`), which
is the form a heights-along-the-run ledger can produce. -/
theorem endgame_RSt_step
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G 1 m ≤ K G)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (C kB : ℕ) (hkB : 1 ≤ kB) (hC : 1 ≤ C)
    (hstep : ∀ (a : QMCLeafB.RoundProgram.RSt × List Bool) (j : ℕ), j < a.2.length →
      (enc (QMCLeafB.RoundProgram.round (QMCLeafB.RoundProgram.round^[j] a.1))).length
        ≤ C * ((enc a.1).length + 1) ^ kB + 3 * (j + 1))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict (fun G' _ => K G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G 1 (by norm_num) rmax hrmax m hm1 (K G) (hK G)
          (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_orbit_of_parts
    QMCLeafB.RStInit.init0 fuel QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    QMCLeafB.RStInit.poly_init0 hfuel QMCLeafB.RoundProgram.poly_round
    QMCLeafB.RoundProgram.poly_verdict
    (QMCLeafB.FinalStroke.sizesOrbitPow C kB)
    (fun a j hj => horbit_of_orbit_step C kB hkB hC a (hstep a) j hj)
    (fun G' _ => K G' * m)
    QMCLeafB.RStInit.init0_tape hfuelLen
    (fun G t _ hlo hhi => (hd G t hlo hhi).toRunData)

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.RoundSizes.enc_ge_oks
#print axioms QMCLeafB.RoundSizes.enc_len_formula
#print axioms QMCLeafB.RoundSizes.encSt_len
#print axioms QMCLeafB.RoundSizes.encList_rat_length_le
#print axioms QMCLeafB.RoundSizes.enc_le_of_heights
#print axioms QMCLeafB.RoundSizes.enc_stX_le
#print axioms QMCLeafB.RoundSizes.enc_stA_le
#print axioms QMCLeafB.RoundSizes.enc_stRec_le
#print axioms QMCLeafB.RoundSizes.state_only_monomial_fails
#print axioms QMCLeafB.RoundSizes.no_state_only_orbit_class
#print axioms QMCLeafB.RoundSizes.abs_entry_le_one
#print axioms QMCLeafB.RoundSizes.nrmRow_muOf_eq_map_snapDiv
#print axioms QMCLeafB.RoundSizes.horbit_of_single
#print axioms QMCLeafB.RoundSizes.horbit_of_honest_class
#print axioms QMCLeafB.RoundSizes.state_class_of_step
#print axioms QMCLeafB.RoundSizes.horbit_of_orbit_step
#print axioms QMCLeafB.RoundSizes.endgame_RSt_joint
#print axioms QMCLeafB.RoundSizes.endgame_RSt_step

end QMCLeafB.RoundSizes


