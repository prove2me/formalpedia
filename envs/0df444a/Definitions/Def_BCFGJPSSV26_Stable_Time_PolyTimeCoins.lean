-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeCoins
-- name    : BCFGJPSSV26_Stable_Time_PolyTimeCoins
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:21:59.119056+00:00
-- url     : https://prove2.me/theorems/0d1bec14-4ffb-4025-9eba-84644e3ed0e9
-- title:
--   BCFGJPSSV26.Stable.Time.PolyTimeCoins — Coins and the client sampling in polynomial time
-- statement:
--   This is module `BCFGJPSSV26.Stable.Time.PolyTimeCoins` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Certificates for the coin primitives of `BCFGJPSSV26/Stable/Alg/Coins.lean` (chunks, fair bits,
--   uniform choices, weighted samples), the radius grid, the client sampling
--   (`BCFGJPSSV26.Stable.csRun`) and the coloring (`BCFGJPSSV26.Stable.colors`).
--
--   An accessor `ch : ℕ → ℕ` of chunks is certified as the function `(a, i) ↦ ch a i` of the input
--   and a binary index. The client sampling is a fold of `2 s` iterations that each append at most one
--   dummy, computed from the input and the iteration alone, so its states grow by a bounded amount.
--
--   **Contents.** The module is published as a whole: 22 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeCoins`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/PolyTimeCoins.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClientSampling
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coloring
public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeLS
public import Definitions.Def_BuhaiPapers_Background_PolyTime_Lists

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Time.PolyTimeCoins` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Coins and the client sampling in polynomial time

Certificates for the coin primitives of `BCFGJPSSV26/Stable/Alg/Coins.lean` (chunks, fair bits,
uniform choices, weighted samples), the radius grid, the client sampling
(`BCFGJPSSV26.Stable.csRun`) and the coloring (`BCFGJPSSV26.Stable.colors`).

An accessor `ch : ℕ → ℕ` of chunks is certified as the function `(a, i) ↦ ch a i` of the input
and a binary index. The client sampling is a fold of `2 s` iterations that each append at most one
dummy, computed from the input and the iteration alone, so its states grow by a bounded amount.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable.PolyTime

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### Sizes -/

theorem exists_le_pow {β : Type} {size u : β → ℕ} (h : PolyBounded size u) :
    ∃ c d, ∀ a, u a ≤ c * (size a + 1) ^ d := by
  obtain ⟨bound, hb, hu⟩ := h
  obtain ⟨c, d, hcd⟩ := Cslib.polynomiallyBounded_iff_le.1 hb
  exact ⟨c, d, fun a ↦ (hu a).trans (hcd _)⟩

theorem length_encList_append_singleton {β : Type} (e : β ↪ List Bool) (l : List β) (a : β) :
    (encList e (l ++ [a])).length = (encList e l).length + (2 * (e a).length + 1) := by
  rw [length_encList, length_encList, List.map_append, List.sum_append]
  simp

/-! ### Chunks -/

theorem finset_sum_range_eq (f : ℕ → ℕ) (n : ℕ) :
    ∑ t ∈ Finset.range n, f t = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
    simp

theorem chunkVal_eq_sum (b : ℕ) (l : List Bool) (e : ℕ) :
    Sampling.chunkVal b l e =
      ((List.range b).map fun t ↦ if l.getD (e * b + t) false then 2 ^ t else 0).sum :=
  finset_sum_range_eq _ b

/-- **A chunk** of `b` bits, `b` in unary and the index in binary. -/
@[fun_prop]
theorem chunkVal' {b e : α → ℕ} {l : α → List Bool} (hb : ComputableInPolyTime b input encUnary)
    (hl : ComputableInPolyTime l input encBits) (he : ComputableInPolyTime e input encNat) :
    ComputableInPolyTime (fun a ↦ Sampling.chunkVal (b a) (l a) (e a)) input encNat := by
  simp only [chunkVal_eq_sum]
  have hbit : ComputableInPolyTime (fun p : α × ℕ ↦ (l p.1).getD (e p.1 * b p.1 + p.2) false)
      (encPair input encUnary) encBool :=
    listGetD_binary (encA := encBool) (encL := encBits) false (hl.comp (fst _ _))
      (binAdd' (binMul' (he.comp (fst _ _)) (unary_to_binary.comp (hb.comp (fst _ _))))
        (unary_to_binary.comp (snd _ _)))
  have hmap : ComputableInPolyTime (fun a ↦ (List.range (b a)).map fun t ↦
      if (l a).getD (e a * b a + t) false then 2 ^ t else 0) input (encList encNat) :=
    mapWithInput (f := fun a t ↦ if (l a).getD (e a * b a + t) false then 2 ^ t else 0)
      (unary_range' hb) (ite' hbit (binary_two_pow.comp (snd _ _)) (const 0))
  exact .of_tidy (ComputableTidilyInPolyTime.binary_sum.comp hmap.tidy)

/-- An accessor of chunks, certified with a binary index. -/
abbrev ChAcc (input : α ↪ List Bool) (ch : α → ℕ → ℕ) : Prop :=
  ComputableInPolyTime (fun p : α × ℕ ↦ ch p.1 p.2) (encPair input encNat) encNat

/-- Reading an accessor at a computed index. -/
theorem chAt {ch : α → ℕ → ℕ} {i : α → ℕ} (hch : ChAcc input ch)
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ ch a (i a)) input encNat :=
  hch.comp (g := fun a ↦ (a, i a)) (id'.prod hi)

/-- An accessor of the input with a changed parameter. -/
theorem ChAcc.comp' {β : Type} {encB : β ↪ List Bool} {ch : β → ℕ → ℕ} (hch : ChAcc encB ch)
    {f : α → β} (hf : ComputableInPolyTime f input encB) :
    ChAcc input fun a ↦ ch (f a) :=
  hch.comp (g := fun p : α × ℕ ↦ (f p.1, p.2)) ((hf.comp (fst _ _)).prod (snd _ _))

/-- **A window** of an accessor. -/
theorem window' {ch : α → ℕ → ℕ} {o M : α → ℕ} (hch : ChAcc input ch)
    (ho : ComputableInPolyTime o input encNat) (hM : ComputableInPolyTime M input encNat) :
    ChAcc input fun a ↦ window (ch a) (o a) (M a) := by
  unfold window
  exact ite_decide (binary_lt' (snd _ _) (hM.comp (fst _ _)))
    (hch.comp (g := fun p : α × ℕ ↦ (p.1, o p.1 + p.2))
      ((fst _ _).prod (binAdd' (ho.comp (fst _ _)) (snd _ _)))) (const 0)

/-! ### Coin primitives -/

@[fun_prop]
theorem cbit' {b u : α → ℕ} (hb : ComputableInPolyTime b input encUnary)
    (hu : ComputableInPolyTime u input encNat) :
    ComputableInPolyTime (fun a ↦ cbit (b a) (u a)) input encBool := by
  unfold cbit
  exact binary_lt' (binMul' (const 2) hu) (binary_two_pow.comp hb)

@[fun_prop]
theorem cunif' {M u : α → ℕ} (hM : ComputableInPolyTime M input encNat)
    (hu : ComputableInPolyTime u input encNat) :
    ComputableInPolyTime (fun a ↦ cunif (M a) (u a)) input encNat := by
  unfold cunif
  exact binMod' hu hM

@[fun_prop]
theorem wsample' {b u : α → ℕ} {w : α → List ℚ} (hb : ComputableInPolyTime b input encUnary)
    (hw : ComputableInPolyTime w input (encList encRat))
    (hu : ComputableInPolyTime u input encNat) :
    ComputableInPolyTime (fun a ↦ wsample (b a) (w a) (u a)) input encNat := by
  unfold wsample
  have hw' : ComputableInPolyTime (fun p : α × ℕ ↦ w p.1) (encPair input encUnary)
      (encList encRat) := hw.comp (fst _ _)
  have htake : ComputableInPolyTime (fun p : α × ℕ ↦ (w p.1).take (p.2 + 1))
      (encPair input encUnary) (encList encRat) :=
    .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hw'.tidy
      (unary_add' (snd _ _) (const 1)).tidy)
  have htest : ComputableInPolyTime (fun p : α × ℕ ↦
      decide (((u p.1 : ℕ) : ℚ) * (w p.1).sum < 2 ^ b p.1 * ((w p.1).take (p.2 + 1)).sum))
      (encPair input encUnary) encBool :=
    rat_lt' (rat_mul' (rat_natCast' (hu.comp (fst _ _))) (rat_sum' hw'))
      (rat_mul' (rat_two_pow' (hb.comp (fst _ _))) (rat_sum' htake))
  have hfind := findWithInput (test := fun a i ↦
    decide (((u a : ℕ) : ℚ) * (w a).sum < 2 ^ b a * ((w a).take (i + 1)).sum))
    (unary_range' ((length_list encRat).comp hw)) htest
  exact unary_to_binary.comp ((optionGetD encUnary).comp (hfind.prod (const 0)))

/-! ### The radius grid -/

theorem grid_eq (N : ℕ) (r₀ : ℚ) (x : ℕ) :
    grid N r₀ x = r₀ / ((N ^ 3 : ℕ) : ℚ) * (((N + 1) ^ x : ℕ) / ((N ^ x : ℕ) : ℚ)) := by
  unfold grid
  push_cast
  rw [div_pow]

/-- The grid, with `N` and the exponent in unary. -/
theorem grid_polytime : ComputableInPolyTime (fun p : ℕ × ℚ × ℕ ↦ grid p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encRat encUnary)) encRat := by
  simp only [grid_eq]
  have hN : ComputableInPolyTime (fun p : ℕ × ℚ × ℕ ↦ p.1)
      (encPair encUnary (encPair encRat encUnary)) encNat := unary_to_binary.comp (fst _ _)
  have hx : ComputableInPolyTime (fun p : ℕ × ℚ × ℕ ↦ p.2.2)
      (encPair encUnary (encPair encRat encUnary)) encUnary := (snd _ _).comp (snd _ _)
  exact rat_mul' (rat_div' ((fst _ _).comp (snd _ _)) (rat_natCast' (binary_pow' hN (const 3))))
    (rat_div' (rat_natCast' (binary_pow' (binAdd' hN (const 1)) hx))
      (rat_natCast' (binary_pow' hN hx)))

/-- A grid point with a computed exponent below `10 N² + 1`. -/
theorem grid' {N u : α → ℕ} {r : α → ℚ} (hN : ComputableInPolyTime N input encUnary)
    (hr : ComputableInPolyTime r input encRat) (hu : ComputableInPolyTime u input encNat) :
    ComputableInPolyTime (fun a ↦ grid (N a) (r a) (cunif (Par.Gr (N a)) (u a))) input
      encRat := by
  have hG : ComputableInPolyTime (fun a ↦ Par.Gr (N a)) input encUnary := by
    unfold Par.Gr
    have h := unary_add' (unary_mul' (const 10) (unary_mul' hN hN)) (const (encIn := input) 1)
    simpa only [sq] using h
  have hx : ComputableInPolyTime (fun a ↦ cunif (Par.Gr (N a)) (u a)) input encUnary :=
    binary_to_unary_bounded (cunif' (unary_to_binary.comp hG) hu) hG fun a ↦ by
      unfold cunif
      exact (Nat.mod_lt _ (by unfold Par.Gr; omega)).le
  exact grid_polytime.comp (g := fun a ↦ (N a, r a, cunif (Par.Gr (N a)) (u a)))
    (hN.prod (hr.prod hx))

/-! ### The client sampling -/

/-- The dummy that an iteration of the client sampling may add. -/
def csDum (N : ℕ) (x : Raw) (LS : List ℕ) (b us ur : ℕ) : DumQ :=
  (wsample b ((List.range x.n).map fun j ↦ x.dSetQ j LS) us,
    grid N (x.dSetQ (wsample b ((List.range x.n).map fun j ↦ x.dSetQ j LS) us) LS)
      (cunif (Par.Gr N) ur))

theorem csStep_eq (N : ℕ) (x : Raw) (LS : List ℕ) (b : ℕ) (Λ : List DumQ) (us uk ur : ℕ) :
    csStep N x LS b Λ us uk ur = if cbit b uk then Λ else Λ ++ [csDum N x LS b us ur] := rfl

theorem csDum' {N b us ur : α → ℕ} {x : α → Raw} {LS : α → List ℕ}
    (hN : ComputableInPolyTime N input encUnary) (hx : ComputableInPolyTime x input encRaw)
    (hn : ∀ a, (x a).n ≤ (x a).table.length)
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hb : ComputableInPolyTime b input encUnary) (hus : ComputableInPolyTime us input encNat)
    (hur : ComputableInPolyTime ur input encNat) :
    ComputableInPolyTime (fun a ↦ csDum (N a) (x a) (LS a) (b a) (us a) (ur a)) input
      encDum := by
  unfold csDum
  have hw : ComputableInPolyTime (fun a ↦ (List.range (x a).n).map fun j ↦ (x a).dSetQ j (LS a))
      input (encList encRat) :=
    mapWithInput (f := fun a j ↦ (x a).dSetQ j (LS a)) (rangeN' hx (raw_n' hx) hn)
      (dSetQ' (hx.comp (fst _ _)) (snd _ _) (hLS.comp (fst _ _)))
  have hl := wsample' hb hw hus
  exact hl.prod (grid' hN (dSetQ' hx hl hLS) hur)

/-- **The client sampling**, when the clients are at most the rows of the table. -/
theorem csRun' {N s b : α → ℕ} {x : α → Raw} {LS : α → List ℕ} {ch : α → ℕ → ℕ}
    (hN : ComputableInPolyTime N input encUnary) (hx : ComputableInPolyTime x input encRaw)
    (hn : ∀ a, (x a).n ≤ (x a).table.length)
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hs : ComputableInPolyTime s input encUnary) (hb : ComputableInPolyTime b input encUnary)
    (hch : ChAcc input ch) :
    ComputableInPolyTime (fun a ↦ csRun (N a) (x a) (LS a) (s a) (b a) (ch a)) input
      (encList encDum) := by
  unfold csRun
  simp only [csStep_eq]
  -- the dummy of iteration `i`
  have hdum : ComputableInPolyTime (fun p : α × ℕ ↦ csDum (N p.1) (x p.1) (LS p.1) (b p.1)
      (ch p.1 (3 * p.2)) (ch p.1 (3 * p.2 + 2))) (encPair input encUnary) encDum := by
    have hi : ComputableInPolyTime (fun p : α × ℕ ↦ p.2) (encPair input encUnary) encNat :=
      unary_to_binary.comp (snd _ _)
    exact csDum' (hN.comp (fst _ _)) (hx.comp (fst _ _)) (fun p ↦ hn p.1) (hLS.comp (fst _ _))
      (hb.comp (fst _ _)) (chAt (hch.comp' (fst _ _)) (binMul' (const 3) hi))
      (chAt (hch.comp' (fst _ _)) (binAdd' (binMul' (const 3) hi) (const 2)))
  obtain ⟨cD, dD, hD⟩ := exists_le_pow hdum.polyBounded_length
  have hstep : ComputableInPolyTime (fun p : (α × List DumQ) × ℕ ↦
      if cbit (b p.1.1) (ch p.1.1 (3 * p.2 + 1)) then p.1.2 else
        p.1.2 ++ [csDum (N p.1.1) (x p.1.1) (LS p.1.1) (b p.1.1) (ch p.1.1 (3 * p.2))
          (ch p.1.1 (3 * p.2 + 2))]) (encPair (encPair input (encList encDum)) encUnary)
      (encList encDum) := by
    have hi : ComputableInPolyTime (fun p : (α × List DumQ) × ℕ ↦ p.2)
        (encPair (encPair input (encList encDum)) encUnary) encNat :=
      unary_to_binary.comp (snd _ _)
    refine ite' (cbit' (hb.comp ((fst _ _).comp (fst _ _)))
      (chAt (hch.comp' ((fst _ _).comp (fst _ _))) (binAdd' (binMul' (const 3) hi) (const 1))))
      ((snd _ _).comp (fst _ _)) (listAppend' ((snd _ _).comp (fst _ _)) (cons' ?_ (const [])))
    exact hdum.comp (g := fun p : (α × List DumQ) × ℕ ↦ (p.1.1, p.2))
      (((fst _ _).comp (fst _ _)).prod (snd _ _))
  refine foldlWith_of_bounded_growth (par := fun a ↦ a) (list := fun a ↦ List.range (2 * s a))
    (init := fun _ ↦ []) id' (unary_range' (unary_mul' (const 2) hs)) (const []) hstep
    (growth := fun a ↦ 2 * (cD * (2 * (input a).length + 2 * s a + 2) ^ dD) + 1) ?_ ?_
  · exact ((PolyBounded.const 2).mul ((PolyBounded.const cD).mul
      ((((PolyBounded.const 2).mul .self).add (((PolyBounded.const 2).mul hs.polyBounded).add
        (.const 2))).pow dD))).add (.const 1)
  · intro a Λ i hi
    have hi' := List.mem_range.1 hi
    have hd := hD (a, i)
    dsimp only at hd
    have hle : (encPair input encUnary (a, i)).length + 1 ≤ 2 * (input a).length + 2 * s a + 2 := by
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega
    have hd' := hd.trans (Nat.mul_le_mul_left cD (Nat.pow_le_pow_left hle dD))
    split_ifs
    · omega
    · rw [length_encList_append_singleton]
      omega

/-! ### The coloring -/

theorem colors' {b : α → ℕ} {LS : α → List ℕ} {ch : α → ℕ → ℕ}
    (hb : ComputableInPolyTime b input encUnary)
    (hLS : ComputableInPolyTime LS input (encList encNat)) (hch : ChAcc input ch) :
    ComputableInPolyTime (fun a ↦ colors (b a) (LS a) (ch a)) input (encList encBool) := by
  unfold colors
  exact mapWithInput (f := fun a i ↦ cbit (b a) (ch a i))
    (unary_range' ((length_list encNat).comp hLS))
    (cbit' (hb.comp (fst _ _)) (chAt (hch.comp' (fst _ _)) (unary_to_binary.comp (snd _ _))))

theorem redOf' {LS : α → List ℕ} {col : α → List Bool}
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hcol : ComputableInPolyTime col input (encList encBool)) :
    ComputableInPolyTime (fun a ↦ redOf (LS a) (col a)) input (encList encNat) := by
  unfold redOf
  exact listFilterMap (f := fun _ (p : ℕ × Bool) ↦ if p.2 then some p.1 else none) 0
    ((zip encNat encBool).comp (hLS.prod hcol))
    (ite' ((snd _ _).comp (snd _ _)) ((optionSome encNat).comp ((fst _ _).comp (snd _ _)))
      (const none))

theorem blueOf' {LS : α → List ℕ} {col : α → List Bool}
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hcol : ComputableInPolyTime col input (encList encBool)) :
    ComputableInPolyTime (fun a ↦ blueOf (LS a) (col a)) input (encList encNat) := by
  unfold blueOf
  exact listFilterMap (f := fun _ (p : ℕ × Bool) ↦ if p.2 then none else some p.1) 0
    ((zip encNat encBool).comp (hLS.prod hcol))
    (ite' ((snd _ _).comp (snd _ _)) (const none)
      ((optionSome encNat).comp ((fst _ _).comp (snd _ _))))

end BCFGJPSSV26.Stable.PolyTime


