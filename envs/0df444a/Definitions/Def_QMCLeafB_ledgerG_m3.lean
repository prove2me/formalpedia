-- Prove2me | Definitions.Def_QMCLeafB_ledgerG_m3
-- name    : QMCLeafB_ledgerG_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:59:29.201878+00:00
-- url     : https://prove2.me/theorems/72e7197b-d13e-4f09-929d-58ca24d0fb5f
-- title:
--   QMCLeafB ledgerG_m3
-- statement:
--   # leaf B phase 16 — brick `ledgerg` (swarm `smw1ez4a9`, member m3, direction d1)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_capguard_m3
import Definitions.Def_QMCLeafB_guard
import Definitions.Def_QMCLeafB_integration_m6
/-
# leaf B phase 16 — brick `ledgerg` (swarm `smw1ez4a9`, member m3, direction d1)

The closing stroke's size slot, at the guarded round.  `QMCLeafB.CapGuard.LedgerG M c` is the trio

* `M (roundG s) ≤ M s + c`              (the cap moves with the appended flag only),
* `(enc (roundG s)).length ≤ max ((enc s).length + c) (M s)`   (one step either costs the flag or
  lands inside the cap),
* `∃ C₀ k, ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ k`           (the cap is polynomial in the state's
  *own* encoding).

`Msz` (`Check_roundsize_m6`) fails the third slot: its caps are `n * n`-based and `n` is only `log n`
bits of the state (`RoundOrbit` records the refutation).  `MszG` (`Check_capguard_m3`) replaces
`n * n` by `|X|`; at a *normalised* state (`|X| = n*n`) the two coincide, and `roundG` freezes every
other state, so `n ≤ |X| + 1` is available exactly where the `n²`-entry oracle call happens.

Contents:

* §1 the linear encoding facts for `RSt` (`skel`'s exact formula, every component ≤ `|enc s|`).
* §2 `kapH`/`capRecG` monotonicity, and the parametric recorder cap `capRecL`.
* §3 the `cut` branch at a normalised state: `aX`, `aRec`, `capXG` all stay under the `|X|`-caps,
  using m6's `oracleR_length_le` transported through `capRec ≤ capRecG`.
* §4 the `ok` branch (`roundOk` freezes everything but the flag) and the assembled steps for
  `roundG` by guard case analysis.
* §5 the polynomial cap: `MszG s ≤ 11448595 * (|enc s| + 1)^6`, hence `LedgerG MszG 6`.
* §6 consumption at `IntegrateM6.solution_of_bricks` — kept only as the *seam record*: that stroke
  asks `htop` on the whole bracket (including `G.n ≤ 1`), which is false, so the usable consumption
  lives in the companion file `Check_ledgerG_union_m3.lean` (it needs m5's `UnionShallow`, hence the
  split, so that this brick's audit does not depend on a moving module).
* §6d `roundG_iterate_eq_round_of_normalised` / `loopBit_G_eq_of_normalised`: `GuardedRound.loopBit_G_eq`
  generalised from `RStInit.init0` to ANY init that starts normalised — the guarded and the shelf
  loop have the same verdict bit, which is what a rebuilt init needs.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.CapGuard

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram
open QMCLeafB.RoundSizeM6
open QMCLeafB.GuardedRound

/-! ## 1.  The encoding of `RSt` is linear in its parts -/

/-- **`skel`'s exact formula.**  `RSt` is a nested product, so `enc` of it is a chain of
`encodePair`s; `quote`ing the left component of every pair costs `2·|·| + 1`. -/
theorem skel_formula (s : RSt) :
    skel s = 8 * (enc (stN s)).length + 4 * (encodeList (enc : ℚ → List Bool) (stA s)).length
      + 4 * (enc (stT s)).length + 2 * Lmu s + 4 * Ld s + 14 := by
  obtain ⟨⟨⟨n, A⟩, X, t, mu⟩, ⟨d, oks⟩, rec⟩ := s
  simp only [skel, Lmu, Ld, stN, stA, stT, stMu, stD]
  simp
  simp only [EncodedList.nil, List.length_nil]
  ring_nf

theorem Lmu_le_skel (s : RSt) : Lmu s ≤ skel s := by
  rw [skel_formula]; omega

theorem Ld_le_skel (s : RSt) : Ld s ≤ skel s := by
  rw [skel_formula]; omega

theorem aA_le_skel (s : RSt) : (encodeList (enc : ℚ → List Bool) (stA s)).length ≤ skel s := by
  rw [skel_formula]; omega

theorem lenA_le_skel (s : RSt) : (stA s).length ≤ skel s := by
  have h := EncodedList.length_le (enc : ℚ → List Bool) (stA s)
  have h2 := aA_le_skel s
  omega

theorem skel_le_enc (s : RSt) : skel s ≤ (enc s).length := by
  rw [QMCLeafB.RoundSizeM6.enc_decomp]; omega

theorem aX_le_enc (s : RSt) : aX s ≤ (enc s).length := by
  rw [QMCLeafB.RoundSizeM6.enc_decomp]; omega

theorem aRec_le_enc (s : RSt) : aRec s ≤ (enc s).length := by
  rw [QMCLeafB.RoundSizeM6.enc_decomp]; omega

theorem oks_le_enc (s : RSt) : (stOks s).length ≤ (enc s).length := by
  rw [QMCLeafB.RoundSizeM6.enc_decomp]; omega

theorem lenX_le_aX (s : RSt) : (stX s).length ≤ aX s :=
  EncodedList.length_le (enc : ℚ → List Bool) (stX s)

theorem lenX_le_enc (s : RSt) : (stX s).length ≤ (enc s).length :=
  le_trans (lenX_le_aX s) (aX_le_enc s)

theorem Lmu_le_enc (s : RSt) : Lmu s ≤ (enc s).length := le_trans (Lmu_le_skel s) (skel_le_enc s)
theorem Ld_le_enc (s : RSt) : Ld s ≤ (enc s).length := le_trans (Ld_le_skel s) (skel_le_enc s)
theorem aA_le_enc (s : RSt) :
    (encodeList (enc : ℚ → List Bool) (stA s)).length ≤ (enc s).length :=
  le_trans (aA_le_skel s) (skel_le_enc s)
theorem lenA_le_enc (s : RSt) : (stA s).length ≤ (enc s).length :=
  le_trans (lenA_le_skel s) (skel_le_enc s)

/-- `baseG` is linear in the state's own encoding. -/
theorem baseG_le (s : RSt) : baseG s ≤ 10 * ((enc s).length + 1) := by
  have h1 := skel_le_enc s; have h2 := aX_le_enc s; have h3 := aRec_le_enc s
  have h4 := Lmu_le_enc s; have h5 := Ld_le_enc s; have h6 := lenX_le_enc s
  have h7 := lenA_le_enc s; have h8 := aA_le_enc s; have h9 := oks_le_enc s
  simp only [baseG]; omega

/-! ## 2.  Heights, the parametric recorder cap, and its monotonicities -/

theorem kapH_mono_N {H N N' : ℕ} (h : N ≤ N') : kapH H N ≤ kapH H N' := by
  have h1 : N * (6 * (2 * H) + 21) ≤ N' * (6 * (2 * H) + 21) := Nat.mul_le_mul_right _ h
  have h2 : H + N * (6 * (2 * H) + 21) ≤ H + N' * (6 * (2 * H) + 21) := by omega
  have h3 : 6 * (H + N * (6 * (2 * H) + 21)) + 21
      ≤ 6 * (H + N' * (6 * (2 * H) + 21)) + 21 := by omega
  have h4 : N * (6 * (H + N * (6 * (2 * H) + 21)) + 21)
      ≤ N' * (6 * (H + N' * (6 * (2 * H) + 21)) + 21) := Nat.mul_le_mul h h3
  simp only [kapH, qfH]
  omega

/-- The recorder cap with the entry count `N` as a parameter (`capRecG` is the case `N = |X|`). -/
noncomputable def capRecL (s : RSt) (N H : ℕ) : ℕ :=
  (encodeList (enc : ℚ → List Bool) (stA s)).length
    + (N + 1) * (N + 1) * (6 * (2 * kapH (H + Lmu s + Ld s) (N + 1)) + 21)
    + (N + 1) * (N + 1) * 33 + 1

theorem capRecG_eq_capRecL (s : RSt) (H : ℕ) :
    capRecG s H = capRecL s ((stX s).length) H := rfl

theorem capRecL_mono_N (s : RSt) {N N' H : ℕ} (h : N ≤ N') :
    capRecL s N H ≤ capRecL s N' H := by
  have h1 : N + 1 ≤ N' + 1 := by omega
  have h2 : kapH (H + Lmu s + Ld s) (N + 1) ≤ kapH (H + Lmu s + Ld s) (N' + 1) :=
    kapH_mono_N h1
  have h3 : 6 * (2 * kapH (H + Lmu s + Ld s) (N + 1)) + 21
      ≤ 6 * (2 * kapH (H + Lmu s + Ld s) (N' + 1)) + 21 := by omega
  have h4 : (N + 1) * (N + 1) ≤ (N' + 1) * (N' + 1) := Nat.mul_le_mul h1 h1
  have h5 : (N + 1) * (N + 1) * (6 * (2 * kapH (H + Lmu s + Ld s) (N + 1)) + 21)
      ≤ (N' + 1) * (N' + 1) * (6 * (2 * kapH (H + Lmu s + Ld s) (N' + 1)) + 21) :=
    Nat.mul_le_mul h4 h3
  have h6 : (N + 1) * (N + 1) * 33 ≤ (N' + 1) * (N' + 1) * 33 := Nat.mul_le_mul_right 33 h4
  simp only [capRecL]
  omega

theorem capRecL_mono_H (s : RSt) {N H H' : ℕ} (h : H ≤ H') :
    capRecL s N H ≤ capRecL s N H' := by
  have h1 : H + Lmu s + Ld s ≤ H' + Lmu s + Ld s := by omega
  have h2 : kapH (H + Lmu s + Ld s) (N + 1) ≤ kapH (H' + Lmu s + Ld s) (N + 1) :=
    kapH_mono h1
  have h3 : 6 * (2 * kapH (H + Lmu s + Ld s) (N + 1)) + 21
      ≤ 6 * (2 * kapH (H' + Lmu s + Ld s) (N + 1)) + 21 := by omega
  have h4 : (N + 1) * (N + 1) * (6 * (2 * kapH (H + Lmu s + Ld s) (N + 1)) + 21)
      ≤ (N + 1) * (N + 1) * (6 * (2 * kapH (H' + Lmu s + Ld s) (N + 1)) + 21) :=
    Nat.mul_le_mul_left _ h3
  simp only [capRecL]
  omega

theorem capRecG_mono_H (s : RSt) {H H' : ℕ} (h : H ≤ H') : capRecG s H ≤ capRecG s H' := by
  rw [capRecG_eq_capRecL, capRecG_eq_capRecL]
  exact capRecL_mono_H s h

/-- `capRecL` looks at `X` only through its length, so it is invariant under the round. -/
theorem capRecL_round (s : RSt) (N H : ℕ) :
    capRecL (round s) N H = capRecL s N H := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := round_components s
  simp only [capRecL, h2, Lmu_round, Ld_round]

theorem capRecG_round_le (s : RSt) (hn : (stX s).length = stN s * stN s) (H : ℕ) :
    capRecG (round s) H ≤ capRecG s H := by
  rw [capRecG_eq_capRecL, capRecG_eq_capRecL, capRecL_round]
  refine capRecL_mono_N s ?_
  rcases round_eq s with hr
  by_cases hc : (oracleR s).1 = true
  · rw [stX_round_cut s hc, hn]; exact snapY_length_le s
  · have hf : (oracleR s).1 = false := by simpa using hc
    rw [stX_round_ok s hf]

/-! ## 3.  The cut branch at a normalised state -/

/-- From a normalised state, `n ≤ |X| + 1`. -/
theorem stN_le_lenX_succ (s : RSt) (hn : (stX s).length = stN s * stN s) :
    stN s ≤ (stX s).length + 1 := by
  have h : stN s ≤ stN s * stN s := by
    rcases Nat.eq_zero_or_pos (stN s) with h0 | h0
    · omega
    · calc stN s = stN s * 1 := by ring
        _ ≤ stN s * stN s := Nat.mul_le_mul_left _ h0
  omega

theorem capX_eq_capXG (s : RSt) (hn : (stX s).length = stN s * stN s) :
    capX s = capXG s := by
  simp only [capX, capXG, hn]

/-- **The recorder cap with `n` replaced by `|X|`** dominates m6's cap. -/
theorem capRec_le_capRecG (s : RSt) (hn : stN s ≤ (stX s).length + 1) (H : ℕ) :
    capRec s H ≤ capRecG s H := by
  have hsq : stN s * stN s ≤ ((stX s).length + 1) * ((stX s).length + 1) :=
    Nat.mul_le_mul hn hn
  have hk : kapH (H + Lmu s + Ld s) (stN s)
      ≤ kapH (H + Lmu s + Ld s) ((stX s).length + 1) := kapH_mono_N hn
  have hk2 : 6 * (2 * kapH (H + Lmu s + Ld s) (stN s)) + 21
      ≤ 6 * (2 * kapH (H + Lmu s + Ld s) ((stX s).length + 1)) + 21 := by omega
  have h1 : (stN s * stN s) * (6 * (2 * kapH (H + Lmu s + Ld s) (stN s)) + 21)
      ≤ ((stX s).length + 1) * ((stX s).length + 1)
          * (6 * (2 * kapH (H + Lmu s + Ld s) ((stX s).length + 1)) + 21) :=
    Nat.mul_le_mul hsq hk2
  have h2 : (stN s * stN s) * 33 ≤ ((stX s).length + 1) * ((stX s).length + 1) * 33 :=
    Nat.mul_le_mul_right 33 hsq
  simp only [capRec, capRecG]
  omega

/-- The `X`-side of a cut round stays inside the `|X|`-based cap. -/
theorem aX_round_le_G (s : RSt) (hn : (stX s).length = stN s * stN s)
    (h : (oracleR s).1 = true) : aX (round s) ≤ max (aX s) (capXG s) := by
  have h1 := aX_round_le s h
  rw [capX_eq_capXG s hn] at h1
  exact le_trans h1 (le_max_right _ _)

/-- The `rec`-side of a cut round stays inside the `|X|`-based cap. -/
theorem aRec_round_le_G (s : RSt) (hn : (stX s).length = stN s * stN s)
    (h : (oracleR s).1 = true) :
    aRec (round s) ≤ capRecG s (max (aX s) (capXG s)) := by
  have h1 := oracleR_length_le s
  rw [capX_eq_capXG s hn] at h1
  have h2 : capRec s (max (aX s) (capXG s)) ≤ capRecG s (max (aX s) (capXG s)) :=
    capRec_le_capRecG s (stN_le_lenX_succ s hn) _
  simp only [aRec, stRec_round_cut s h]
  exact le_trans h1 h2

/-- The `X`-side cap does not grow (it depends on `n, mu, d`, and `|X|` shrinks). -/
theorem capXG_round_le (s : RSt) (hn : (stX s).length = stN s * stN s) :
    capXG (round s) ≤ capXG s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := round_components s
  have hlen : (stX (round s)).length ≤ (stX s).length := by
    rcases round_eq s with hr
    by_cases hc : (oracleR s).1 = true
    · rw [stX_round_cut s hc, hn]; exact snapY_length_le s
    · have hf : (oracleR s).1 = false := by simpa using hc
      rw [stX_round_ok s hf]
  simp only [capXG, Lmu_round, Ld_round]
  exact Nat.mul_le_mul_right _ hlen

/-! ## 4.  The one-step ledger at `roundG` -/

/-- The state's own encoding is dominated by the cap. -/
theorem enc_le_MszG (s : RSt) : (enc s).length ≤ MszG s := by
  simp only [MszG, QMCLeafB.RoundSizeM6.enc_decomp]
  omega

/-- **The one-step cap transport**: if everything the cap looks at moves inside the old cap (plus
one flag), the cap grows by exactly the flag.  Both the `cut` and the `ok` branch instantiate this. -/
theorem MszG_step {s s' : RSt} (hskel : skel s' ≤ skel s)
    (hoks : (stOks s').length ≤ (stOks s).length + 1)
    (haX : aX s' ≤ max (aX s) (capXG s))
    (haXG : capXG s' ≤ max (aX s) (capXG s))
    (haRec : aRec s' ≤ max (aRec s) (capRecG s (max (aX s) (capXG s))))
    (hcapRec : capRecG s' (max (aX s') (capXG s'))
      ≤ max (aRec s) (capRecG s (max (aX s) (capXG s)))) :
    MszG s' ≤ MszG s + 6 := by
  have h1 : max (aX s') (capXG s') ≤ max (aX s) (capXG s) := max_le haX haXG
  have h2 : max (aRec s') (capRecG s' (max (aX s') (capXG s')))
      ≤ max (aRec s) (capRecG s (max (aX s) (capXG s))) := max_le haRec hcapRec
  simp only [MszG]
  omega

/-- **One cut round stays inside the `|X|`-based cap** (at a normalised state). -/
theorem enc_round_cut_le_G (s : RSt) (hn : (stX s).length = stN s * stN s)
    (h : (oracleR s).1 = true) : (enc (round s)).length ≤ MszG s := by
  have hX := aX_round_le_G s hn h
  have hR := aRec_round_le_G s hn h
  have hoks : (stOks (round s)).length = (stOks s).length + 1 := by
    rw [oks_round_cut s h, List.length_append]; simp
  rw [enc_round_decomp s, hoks]
  simp only [MszG]
  omega

theorem MszG_round_cut_le_G (s : RSt) (hn : (stX s).length = stN s * stN s)
    (h : (oracleR s).1 = true) : MszG (round s) ≤ MszG s + 6 := by
  have hX := aX_round_le_G s hn h
  have hR := aRec_round_le_G s hn h
  have hXG : capXG (round s) ≤ max (aX s) (capXG s) :=
    le_trans (capXG_round_le s hn) (le_max_right _ _)
  have hRG : capRecG (round s) (max (aX (round s)) (capXG (round s)))
      ≤ capRecG s (max (aX s) (capXG s)) :=
    le_trans (capRecG_mono_H (round s) (max_le hX hXG))
      (capRecG_round_le s hn (max (aX s) (capXG s)))
  have hoks : (stOks (round s)).length ≤ (stOks s).length + 1 := by
    rw [oks_round_cut s h, List.length_append]; simp
  exact MszG_step (le_of_eq (skel_round s)) hoks hX hXG (le_trans hR (le_max_right _ _))
    (le_trans hRG (le_max_right _ _))

/-- `roundOk` freezes everything but the flag, so the cap grows by exactly `6`. -/
theorem MszG_roundOk (s : RSt) : MszG (roundOk s) = MszG s + 6 := by
  simp only [MszG, roundOk, mkSt, stN, stA, stX, stT, stMu, stD, stOks, stRec, skel, aX, aRec,
    capXG, capRecG, Lmu, Ld, List.length_append, List.length_cons, List.length_nil]
  ring_nf

theorem enc_roundOk (s : RSt) : (enc (roundOk s)).length = (enc s).length + 6 :=
  QMCLeafB.IntegrateM6.enc_roundOk_eq (stN s) (stA s) (stX s) (stT s) (stMu s) (stD s) (stOks s)
    (stRec s)

theorem round_of_not_cut (s : RSt) (h : (oracleR s).1 = false) : round s = roundOk s := by
  rw [round_eq, if_neg (by simpa using h)]

theorem MszG_roundG_le (s : RSt) : MszG (roundG s) ≤ MszG s + 6 := by
  by_cases hn : (stX s).length = stN s * stN s
  · rw [roundG_of_normalised s hn]
    by_cases h : (oracleR s).1 = true
    · exact MszG_round_cut_le_G s hn h
    · have hf : (oracleR s).1 = false := by simpa using h
      rw [round_of_not_cut s hf]
      exact le_of_eq (MszG_roundOk s)
  · rw [roundG_of_abnormal s hn]
    exact le_of_eq (MszG_roundOk s)

theorem enc_roundG_le (s : RSt) : (enc (roundG s)).length ≤ max ((enc s).length + 6) (MszG s) := by
  by_cases hn : (stX s).length = stN s * stN s
  · rw [roundG_of_normalised s hn]
    by_cases h : (oracleR s).1 = true
    · exact le_trans (enc_round_cut_le_G s hn h) (le_max_right _ _)
    · have hf : (oracleR s).1 = false := by simpa using h
      rw [round_of_not_cut s hf, enc_roundOk]
      exact le_max_left _ _
  · rw [roundG_of_abnormal s hn, enc_roundOk]
    exact le_max_left _ _

/-! ## 5.  The polynomial cap -/

theorem pow_le_pow_of_le {B : ℕ} (hB : 1 ≤ B) {e f : ℕ} (h : e ≤ f) : B ^ e ≤ B ^ f :=
  Nat.pow_le_pow_right hB h

/-- **`kapH` is `B⁴`-bounded** once its height and width parameters are `B²`- and `B`-bounded. -/
theorem kapH_le_pow {H N B : ℕ} (hH : H ≤ 4002 * B ^ 2) (hN : N ≤ B) (hB : 1 ≤ B) :
    kapH H N ≤ 952710 * B ^ 4 := by
  have h1 : 6 * (2 * H) + 21 ≤ 132099 * B ^ 2 := by nlinarith
  have h2 : N * (6 * (2 * H) + 21) ≤ 132099 * B ^ 3 := by
    calc N * (6 * (2 * H) + 21) ≤ B * (132099 * B ^ 2) := Nat.mul_le_mul hN h1
      _ = 132099 * B ^ 3 := by ring
  have h3 : H + N * (6 * (2 * H) + 21) ≤ 136101 * B ^ 3 := by
    have h3a : B ^ 2 ≤ B ^ 3 := pow_le_pow_of_le hB (by norm_num)
    nlinarith
  have h4 : 6 * (H + N * (6 * (2 * H) + 21)) + 21 ≤ 816607 * B ^ 3 := by
    have h4a : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have h5 : N * (6 * (H + N * (6 * (2 * H) + 21)) + 21) ≤ 816607 * B ^ 4 := by
    calc N * (6 * (H + N * (6 * (2 * H) + 21)) + 21) ≤ B * (816607 * B ^ 3) :=
          Nat.mul_le_mul hN h4
      _ = 816607 * B ^ 4 := by ring
  have h6 : N * (6 * (2 * H) + 21) ≤ 132099 * B ^ 4 := by
    have h6a : B ^ 3 ≤ B ^ 4 := pow_le_pow_of_le hB (by norm_num)
    nlinarith
  have h7 : 2 ≤ 2 * B ^ 4 := by
    have h7a : 1 ≤ B ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have h8 : H ≤ 4002 * B ^ 4 := by
    have h8a : B ^ 2 ≤ B ^ 4 := pow_le_pow_of_le hB (by norm_num)
    nlinarith
  have hqf : qfH H N ≤ 816607 * B ^ 4 := h5
  simp only [kapH]
  nlinarith

/-- **The recorder cap is `B⁶`-bounded.** -/
theorem capRecG_le_pow (s : RSt) :
    capRecG s (max (aX s) (capXG s)) ≤ 11432576 * ((enc s).length + 1) ^ 6 := by
  set B := (enc s).length + 1 with hBdef
  have hB : 1 ≤ B := by omega
  have haX : aX s ≤ B := by have h := aX_le_enc s; omega
  have hcapX : capXG s ≤ 4000 * B ^ 2 := by
    have h1 := capXG_le s
    have h2 := baseG_le s
    have h3 : baseG s ^ 2 ≤ (10 * B) ^ 2 := Nat.pow_le_pow_left h2 2
    nlinarith
  have hH0 : max (aX s) (capXG s) ≤ 4000 * B ^ 2 := by
    refine max_le ?_ hcapX
    have hb : B ≤ 4000 * B ^ 2 := by nlinarith
    omega
  have hH1 : max (aX s) (capXG s) + Lmu s + Ld s ≤ 4002 * B ^ 2 := by
    have h1 := Lmu_le_enc s
    have h2 := Ld_le_enc s
    have hb : B ≤ B ^ 2 := by nlinarith
    nlinarith
  have hN : (stX s).length + 1 ≤ B := by
    have h1 := lenX_le_aX s
    have h2 := aX_le_enc s
    omega
  have hkap := kapH_le_pow (H := max (aX s) (capXG s) + Lmu s + Ld s) (N := (stX s).length + 1)
    hH1 hN hB
  have hK : 6 * (2 * kapH (max (aX s) (capXG s) + Lmu s + Ld s) ((stX s).length + 1)) + 21
      ≤ 11432541 * B ^ 4 := by
    have hone : 1 ≤ B ^ 4 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hsq : ((stX s).length + 1) * ((stX s).length + 1) ≤ B * B := Nat.mul_le_mul hN hN
  have hprod : ((stX s).length + 1) * ((stX s).length + 1)
      * (6 * (2 * kapH (max (aX s) (capXG s) + Lmu s + Ld s) ((stX s).length + 1)) + 21)
      ≤ 11432541 * B ^ 6 := by
    calc ((stX s).length + 1) * ((stX s).length + 1)
          * (6 * (2 * kapH (max (aX s) (capXG s) + Lmu s + Ld s) ((stX s).length + 1)) + 21)
        ≤ (B * B) * (11432541 * B ^ 4) := Nat.mul_le_mul hsq hK
      _ = 11432541 * B ^ 6 := by ring
  have hsq33 : ((stX s).length + 1) * ((stX s).length + 1) * 33 ≤ 33 * B ^ 6 := by
    have h2 : B * B ≤ B ^ 6 := by
      calc B * B = B ^ 2 := by ring
        _ ≤ B ^ 6 := pow_le_pow_of_le hB (by norm_num)
    calc ((stX s).length + 1) * ((stX s).length + 1) * 33 ≤ (B * B) * 33 :=
          Nat.mul_le_mul_right 33 hsq
      _ = 33 * (B * B) := by ring
      _ ≤ 33 * B ^ 6 := Nat.mul_le_mul_left 33 h2
  have hLA := aA_le_enc s
  have hB6 : B ≤ B ^ 6 := by
    calc B = B ^ 1 := by ring
      _ ≤ B ^ 6 := pow_le_pow_of_le hB (by norm_num)
  have hone6 : 1 ≤ B ^ 6 := Nat.one_le_pow _ _ (by omega)
  simp only [capRecG]
  nlinarith

/-- **The `|X|`-based cap is polynomial in the state's own encoding** — the slot `Msz` fails. -/
theorem MszG_le_pow (s : RSt) : MszG s ≤ 11448595 * ((enc s).length + 1) ^ 6 := by
  set B := (enc s).length + 1 with hBdef
  have hB : 1 ≤ B := by omega
  have hB6 : B ≤ B ^ 6 := by
    calc B = B ^ 1 := by ring
      _ ≤ B ^ 6 := pow_le_pow_of_le hB (by norm_num)
  have hskel : skel s ≤ B ^ 6 := by
    have h1 := skel_le_enc s
    have h2 : B ≤ B ^ 6 := hB6
    omega
  have hcapX : capXG s ≤ 4000 * B ^ 2 := by
    have h1 := capXG_le s
    have h2 := baseG_le s
    have h3 : baseG s ^ 2 ≤ (10 * B) ^ 2 := Nat.pow_le_pow_left h2 2
    nlinarith
  have hH0 : max (aX s) (capXG s) ≤ 4000 * B ^ 2 := by
    refine max_le ?_ hcapX
    have haX : aX s ≤ B := by have h := aX_le_enc s; omega
    have hb : B ≤ 4000 * B ^ 2 := by nlinarith
    omega
  have hX4 : 4 * max (aX s) (capXG s) ≤ 16000 * B ^ 6 := by
    have h1 : B ^ 2 ≤ B ^ 6 := pow_le_pow_of_le hB (by norm_num)
    nlinarith
  have hRec : max (aRec s) (capRecG s (max (aX s) (capXG s))) ≤ 11432576 * B ^ 6 := by
    refine max_le ?_ (capRecG_le_pow s)
    have h1 := aRec_le_enc s
    have h2 : B ≤ 11432576 * B ^ 6 := by nlinarith
    omega
  have hoks : 6 * (stOks s).length ≤ 6 * B ^ 6 := by
    have h1 := oks_le_enc s
    nlinarith
  have h6 : 6 ≤ 6 * B ^ 6 := by nlinarith
  simp only [MszG]
  nlinarith

/-- **The guarded round's size ledger.** -/
theorem ledgerG_MszG : LedgerG MszG 6 :=
  ⟨MszG_roundG_le, enc_roundG_le, 11448595, 6, MszG_le_pow⟩

/-- **The orbit envelope (`horbit`) of the guarded loop, for free.**  This is
`IntegrateM6.orbit_envelope` at `roundG`/`MszG` — the slot `LoopRestate.solution_of_loop_bounded`
takes, at `sizesOrbitPow (11448595 + 6 + 2) 6`.  Anything consuming the loop-bounded stroke
directly (rather than through `solution_of_bricks`) can use it as is. -/
theorem horbit_roundG (a : RSt × List Bool) (j : ℕ) (hj : j ≤ a.2.length) :
    (QMCLeafB.SimPoly.encSt (roundG^[j] a.1, a.2.drop j)).length
      ≤ (QMCLeafB.FinalStroke.sizesOrbitPow (11448595 + 6 + 2) 6).eval
          (QMCLeafB.SimPoly.encSt a).length :=
  QMCLeafB.IntegrateM6.orbit_envelope roundG MszG 11448595 6 6 (by norm_num)
    MszG_roundG_le enc_roundG_le MszG_le_pow a j hj

/-! ## 6.  Consumption: the endgame at the guarded round, `hM` deleted -/

local instance instRequestCodingLedgerG :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **`IntegrateM6.solution_of_bricks` at `round = roundG`, `M = MszG`, `c = 6`.**  The `hM` slot
(which is false for m6's `n*n`-based `Msz`) is supplied by `ledgerG_MszG`; nothing else changes. -/
theorem solution_of_bricks_G
    (init0 : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → QMCLeafB.RoundProgram.RSt)
    (hinit0 : Automatic.Poly init0)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init0 roundG QMCLeafB.RoundProgram.verdict
        (fun G' _ => K G') G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.VerdictSound.RunData
        (QMCLeafB.FinalStroke.loopBit init0 roundG QMCLeafB.RoundProgram.verdict
          (fun G' _ => K G')) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.IntegrateM6.solution_of_bricks init0 fuel roundG QMCLeafB.RoundProgram.verdict
    hinit0 hfuel poly_roundG QMCLeafB.RoundProgram.poly_verdict
    MszG 11448595 6 6 (by norm_num) MszG_roundG_le enc_roundG_le MszG_le_pow
    K hinitTape hfuelLen htop hd

/-- **The endgame at the guarded round**: `IntegrateM6.endgame_RSt_ledger` with its size slots
(`M`, `C₀`, `c`, `k`, `hk`, `hMinv`, `hstep`, `hM`) deleted and `round` replaced by `roundG`. -/
theorem endgame_RSt_G
    (rmax : QuantumMaxCutEnergy.Input → ℚ) (m : QuantumMaxCutEnergy.Input → ℕ)
    (dq : QuantumMaxCutEnergy.Input → ℚ)
    (hrmax : ∀ G : QuantumMaxCutEnergy.Input, 0 ≤ rmax G)
    (hm1 : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ m G)
    (hdq : ∀ G : QuantumMaxCutEnergy.Input, 0 < dq G)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((rmax G : ℚ) : ℝ)))⁻¹ ^ (m G)
        ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (dq G) (m G) ≤ K G)
    (init0 : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → QMCLeafB.RoundProgram.RSt)
    (hinit0 : Automatic.Poly init0)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m p.1.1)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init0 roundG QMCLeafB.RoundProgram.verdict
        (fun G' _ => K G' * m G') G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init0 roundG QMCLeafB.RoundProgram.verdict
          (fun G' _ => K G' * m G')) G t
        (QMCLeafB.FinalStroke.runParamsOfK G (dq G) (hdq G) (rmax G) (hrmax G) (m G) (hm1 G)
          (K G) (hK G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_bricks_G init0 hinit0 hinitTape fuel hfuel (fun G => K G * m G) hfuelLen htop
    (fun G t hn hlo hhi => (hd G t hn hlo hhi).toRunData)

/-- **Drop-in for `IntegrateM6.endgame_RSt_ledger`**: same hypotheses read at the shelf round
`RoundProgram.round`, size slots deleted (the guard is inert along `RStInit.init0`'s run, so the
loop bit is the same one). -/
theorem endgame_RSt_init0_G
    (rmax : QuantumMaxCutEnergy.Input → ℚ) (m : QuantumMaxCutEnergy.Input → ℕ)
    (dq : QuantumMaxCutEnergy.Input → ℚ)
    (hrmax : ∀ G : QuantumMaxCutEnergy.Input, 0 ≤ rmax G)
    (hm1 : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ m G)
    (hdq : ∀ G : QuantumMaxCutEnergy.Input, 0 < dq G)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((rmax G : ℚ) : ℝ)))⁻¹ ^ (m G)
        ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (dq G) (m G) ≤ K G)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m p.1.1)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
        QMCLeafB.RoundProgram.verdict (fun G' _ => K G' * m G') G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict (fun G' _ => K G' * m G')) G t
        (QMCLeafB.FinalStroke.runParamsOfK G (dq G) (hdq G) (rmax G) (hrmax G) (m G) (hm1 G)
          (K G) (hK G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_RSt_G rmax m dq hrmax hm1 hdq hhalve K hK QMCLeafB.RStInit.init0
    QMCLeafB.RStInit.poly_init0 QMCLeafB.RStInit.init0_tape fuel hfuel hfuelLen
    (fun G t h1 h2 => by rw [loopBit_G_eq]; exact htop G t h1 h2)
    (fun G t hn hlo hhi => by
      have hloop : QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundG
            QMCLeafB.RoundProgram.verdict (fun G' _ => K G' * m G')
          = QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
            QMCLeafB.RoundProgram.verdict (fun G' _ => K G' * m G') := by
        funext G' t'
        exact loopBit_G_eq (fun G' _ => K G' * m G') G' t'
      rw [hloop]
      exact hd G t hn hlo hhi)

/-! ## 6d.  Any *normalised* init runs the guarded loop: `roundG` can be replaced by `round`

`GuardedRound.loopBit_G_eq` is stated at m1's `RStInit.init0`; brick 1's rebuilt init is a different
program, so the transfer is re-proved here from its one real ingredient — the initial state being
**normalised** (`|X| = n·n`), which is what makes the guard inert along the whole orbit. -/

theorem roundG_iterate_eq_round_of_normalised
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (hnorm : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (stX (init p)).length = stN (init p) * stN (init p))
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : ∀ j : ℕ,
      roundG^[j] (init p) = QMCLeafB.RoundProgram.round^[j] (init p) := by
  intro j
  have hmain : ∀ i : ℕ,
      (stX (roundG^[i] (init p))).length = stN (roundG^[i] (init p)) * stN (roundG^[i] (init p))
      ∧ roundG^[i] (init p) = QMCLeafB.RoundProgram.round^[i] (init p) := by
    intro i
    induction i with
    | zero => exact ⟨hnorm p, rfl⟩
    | succ m ih =>
        obtain ⟨hn, he⟩ := ih
        have hstep : roundG^[m + 1] (init p) = roundG (roundG^[m] (init p)) :=
          Function.iterate_succ_apply' _ m _
        have hround : QMCLeafB.RoundProgram.round^[m + 1] (init p)
            = QMCLeafB.RoundProgram.round (roundG^[m] (init p)) := by
          rw [Function.iterate_succ_apply', he]
        refine ⟨?_, ?_⟩
        · rw [hstep]
          exact roundG_normalised _ hn
        · rw [hstep, hround, roundG_of_normalised _ hn]
  exact (hmain j).2

theorem loopBit_G_eq_of_normalised
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (hnorm : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (stX (init p)).length = stN (init p) * stN (init p))
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.FinalStroke.loopBit init roundG QMCLeafB.RoundProgram.verdict T0 G t
      = QMCLeafB.FinalStroke.loopBit init QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict T0 G t := by
  unfold QMCLeafB.FinalStroke.loopBit
  rw [roundG_iterate_eq_round_of_normalised init hnorm]

end QMCLeafB.CapGuard

/-! ## 7.  Axiom audit -/

#print axioms QMCLeafB.CapGuard.skel_formula
#print axioms QMCLeafB.CapGuard.baseG_le
#print axioms QMCLeafB.CapGuard.kapH_mono_N
#print axioms QMCLeafB.CapGuard.capRecG_round_le
#print axioms QMCLeafB.CapGuard.capRec_le_capRecG
#print axioms QMCLeafB.CapGuard.aRec_round_le_G
#print axioms QMCLeafB.CapGuard.capXG_round_le
#print axioms QMCLeafB.CapGuard.enc_round_cut_le_G
#print axioms QMCLeafB.CapGuard.MszG_step
#print axioms QMCLeafB.CapGuard.MszG_round_cut_le_G
#print axioms QMCLeafB.CapGuard.MszG_roundOk
#print axioms QMCLeafB.CapGuard.enc_roundOk
#print axioms QMCLeafB.CapGuard.MszG_roundG_le
#print axioms QMCLeafB.CapGuard.enc_roundG_le
#print axioms QMCLeafB.CapGuard.kapH_le_pow
#print axioms QMCLeafB.CapGuard.capRecG_le_pow
#print axioms QMCLeafB.CapGuard.MszG_le_pow
#print axioms QMCLeafB.CapGuard.ledgerG_MszG
#print axioms QMCLeafB.CapGuard.horbit_roundG
#print axioms QMCLeafB.CapGuard.solution_of_bricks_G
#print axioms QMCLeafB.CapGuard.endgame_RSt_G
#print axioms QMCLeafB.CapGuard.endgame_RSt_init0_G
#print axioms QMCLeafB.CapGuard.roundG_iterate_eq_round_of_normalised
#print axioms QMCLeafB.CapGuard.loopBit_G_eq_of_normalised


