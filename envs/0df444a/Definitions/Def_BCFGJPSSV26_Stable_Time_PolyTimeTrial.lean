-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeTrial
-- name    : BCFGJPSSV26_Stable_Time_PolyTimeTrial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:30:45.591208+00:00
-- url     : https://prove2.me/theorems/51bbb8fa-920e-4a14-8e25-5e393982ad6e
-- title:
--   BCFGJPSSV26.Stable.Time.PolyTimeTrial — A trial runs in polynomial time
-- statement:
--   This is module `BCFGJPSSV26.Stable.Time.PolyTimeTrial` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   `BCFGJPSSV26.Stable.trialAt_polytime`: trial `t` of the core, reading its chunks
--   of the coins, is polynomial-time in `(N, I, L, LS, B, coins, t)` with `N`, `L`, `B`, `t` in unary,
--   one certificate for all `N`. Its loops are bounded by `s`, `M₂`, `k` and the enumerations of
--   `[N]^ρ` by `B`. Pieces: the coin primitives and the client sampling
--   (`BCFGJPSSV26/Stable/Time/PolyTimeCoins.lean`), the cluster sampling, a fold of
--   `BCFGJPSSV26.Stable.ksStep` whose states grow by a bounded amount
--   (`BCFGJPSSV26/Stable/Time/PolyTimeKS.lean`), the exact mixed distances and `g`, the greedy and the
--   candidates (`BCFGJPSSV26/Stable/Time/PolyTimeSubmod.lean`). Intermediate rationals need no
--   explicit bit bounds: those of the folds' states are values of polynomial-time functions of the
--   input (table entries, grid points of table entries), and the others are recomputed from the input
--   at every step.
--
--   The trial enumerates the clients and the facilities, whose numbers are written in binary, so the
--   certificate is for the tuples whose table has a row for each point (as for an instance), and the
--   empty list otherwise.
--
--   **Contents.** The module is published as a whole: 9 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeTrial`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/PolyTimeTrial.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Trial
public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeSubmod
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Time.PolyTimeTrial` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# A trial runs in polynomial time

`BCFGJPSSV26.Stable.trialAt_polytime`: trial `t` of the core, reading its chunks
of the coins, is polynomial-time in `(N, I, L, LS, B, coins, t)` with `N`, `L`, `B`, `t` in unary,
one certificate for all `N`. Its loops are bounded by `s`, `M₂`, `k` and the enumerations of
`[N]^ρ` by `B`. Pieces: the coin primitives and the client sampling
(`BCFGJPSSV26/Stable/Time/PolyTimeCoins.lean`), the cluster sampling, a fold of
`BCFGJPSSV26.Stable.ksStep` whose states grow by a bounded amount
(`BCFGJPSSV26/Stable/Time/PolyTimeKS.lean`), the exact mixed distances and `g`, the greedy and the
candidates (`BCFGJPSSV26/Stable/Time/PolyTimeSubmod.lean`). Intermediate rationals need no
explicit bit bounds: those of the folds' states are values of polynomial-time functions of the
input (table entries, grid points of table entries), and the others are recomputed from the input
at every step.

The trial enumerates the clients and the facilities, whose numbers are written in binary, so the
certificate is for the tuples whose table has a row for each point (as for an instance), and the
empty list otherwise.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

section

open Encoding

/-- Trial `t` of the core on the coins. -/
def trialAt (y : ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ) : List (List ℕ) :=
  trial y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 fun i ↦
    Sampling.chunkVal (Par.bits y.1 (encRaw y.2.1).length) y.2.2.2.2.2.1
      (y.2.2.2.2.2.2 * Par.Ctr y.1 y.2.2.1 y.2.1.k + i)

/-- The encoding of the inputs of a trial. -/
abbrev encTrialIn : ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ ↪ List Bool :=
  encPair encUnary (encPair encRaw (encPair encUnary (encPair (encList encNat)
    (encPair encUnary (encPair encBits encUnary)))))

end

namespace PolyTime

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

theorem trialCands_eq (N : ℕ) (x : Raw) (L : ℕ) (LS : List ℕ) (B : ℕ) (ch₁ ch₂ ch₃ : ℕ → ℕ) :
    trialCands N x L LS B ch₁ ch₂ ch₃ = (List.range (Par.s N L + 1)).filterMap fun p' ↦
      candidate N x (Par.s N L) B
        (ksLS' LS (ksRun N x LS (csRun N x LS (Par.s N L) (Par.bits N (encRaw x).length) ch₁)
          (Par.s N L) (Par.bits N (encRaw x).length) ch₂))
        (csRun N x LS (Par.s N L) (Par.bits N (encRaw x).length) ch₁ ++
          (ksRun N x LS (csRun N x LS (Par.s N L) (Par.bits N (encRaw x).length) ch₁)
            (Par.s N L) (Par.bits N (encRaw x).length) ch₂).dums)
        (colors (Par.bits N (encRaw x).length)
          (ksLS' LS (ksRun N x LS (csRun N x LS (Par.s N L) (Par.bits N (encRaw x).length) ch₁)
            (Par.s N L) (Par.bits N (encRaw x).length) ch₂)) ch₃) p' := rfl

/-- **The candidates of a trial**, on tuples with a row for each point. -/
theorem trialCands' {N L B : α → ℕ} {x : α → Raw} {LS : α → List ℕ} {ch₁ ch₂ ch₃ : α → ℕ → ℕ}
    (hN : ComputableInPolyTime N input encUnary) (hx : ComputableInPolyTime x input encRaw)
    (hfit : ∀ a, (x a).n + (x a).m ≤ (x a).table.length)
    (hL : ComputableInPolyTime L input encUnary)
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hB : ComputableInPolyTime B input encUnary) (h₁ : ChAcc input ch₁) (h₂ : ChAcc input ch₂)
    (h₃ : ChAcc input ch₃) :
    ComputableInPolyTime (fun a ↦ trialCands (N a) (x a) (L a) (LS a) (B a) (ch₁ a) (ch₂ a)
      (ch₃ a)) input encLL := by
  simp only [trialCands_eq]
  have hn : ∀ a, (x a).n ≤ (x a).table.length := fun a ↦ by have := hfit a; omega
  have hs : ComputableInPolyTime (fun a ↦ Par.s (N a) (L a)) input encUnary := by
    unfold Par.s
    exact unary_mul' (unary_mul' (const 632) hN) hL
  have hb : ComputableInPolyTime (fun a ↦ Par.bits (N a) (encRaw (x a)).length) input
      encUnary := by
    unfold Par.bits
    exact unary_add' ((encoding_length encRaw).comp hx) (unary_mul' (const 7) hN)
  have hΛ₁ := csRun' hN hx hn hLS hs hb h₁
  have hst := ksRun' hN hx hn hLS hΛ₁ hs hb h₂
  have hLS' : ComputableInPolyTime (fun a ↦ ksLS' (LS a) (ksRun (N a) (x a) (LS a)
      (csRun (N a) (x a) (LS a) (Par.s (N a) (L a)) (Par.bits (N a) (encRaw (x a)).length)
        (ch₁ a)) (Par.s (N a) (L a)) (Par.bits (N a) (encRaw (x a)).length) (ch₂ a))) input
      (encList encNat) := by
    unfold ksLS'
    exact filterNotMem' hLS (ksDel' hst)
  have hΛ := listAppend' hΛ₁ (ksDums' hst)
  have hcol := colors' hb hLS' h₃
  exact listFilterMap [] (unary_range' (unary_add' hs (const 1)))
    (candidate' (hN.comp (fst _ _)) (hx.comp (fst _ _)) (fun p ↦ hfit p.1)
      (unary_to_binary.comp (hs.comp (fst _ _))) (hB.comp (fst _ _)) (hLS'.comp (fst _ _))
      (hΛ.comp (fst _ _)) (hcol.comp (fst _ _)) (snd _ _))

/-- **A trial**, on tuples with a row for each point. -/
theorem trial' {N L B : α → ℕ} {x : α → Raw} {LS : α → List ℕ} {ch : α → ℕ → ℕ}
    (hN : ComputableInPolyTime N input encUnary) (hx : ComputableInPolyTime x input encRaw)
    (hfit : ∀ a, (x a).n + (x a).m ≤ (x a).table.length)
    (hL : ComputableInPolyTime L input encUnary)
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hB : ComputableInPolyTime B input encUnary) (hch : ChAcc input ch) :
    ComputableInPolyTime (fun a ↦ trial (N a) (x a) (L a) (LS a) (B a) (ch a)) input encLL := by
  unfold trial
  have hs : ComputableInPolyTime (fun a ↦ 6 * Par.s (N a) (L a)) input encNat := by
    unfold Par.s
    exact unary_to_binary.comp (unary_mul' (const 6) (unary_mul' (unary_mul' (const 632) hN) hL))
  have hM : ComputableInPolyTime (fun a ↦ Par.M₂ (N a) (L a)) input encNat := by
    unfold Par.M₂ Par.s
    exact unary_to_binary.comp (unary_add' (unary_mul' (const 20)
      (unary_mul' (unary_mul' (const 632) hN) hL)) (const 20))
  exact trialCands' hN hx hfit hL hLS hB (window' hch (const 0) hs) (window' hch hs hM)
    (window' hch (binAdd' hs hM) (raw_k' hx))

end PolyTime

open PolyTime Turing.MultiTapeTM ComputableInPolyTime

/-- The tuple with no points when the table lacks rows. -/
def fixR (x : Raw) : Raw := if x.n + x.m ≤ x.table.length then x else (0, 0, x.k, x.table)

theorem fixR_fit (x : Raw) : (fixR x).n + (fixR x).m ≤ (fixR x).table.length := by
  unfold fixR
  split_ifs with h
  · exact h
  · exact Nat.zero_le _

theorem fixR_polytime : ComputableInPolyTime fixR encRaw encRaw := by
  unfold fixR
  exact ite_decide (binary_le' (binAdd' (raw_n' id') (raw_m' id'))
    (unary_to_binary.comp (raw_rows' id'))) id'
    ((const 0).prod ((const 0).prod ((raw_k' id').prod (raw_table' id'))))

/-- **A trial is polynomial-time**, on the tuples whose table has a row for each point (as for an
instance): the trial enumerates the clients and the facilities, whose numbers are written in
binary. -/
theorem trialAt_polytime :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun y ↦ if y.2.1.n + y.2.1.m ≤ y.2.1.table.length then trialAt y else [])
      encTrialIn (Encoding.encList (Encoding.encList Encoding.encNat)) := by
  have hN : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ ↦ y.1)
      encTrialIn encUnary := fst _ _
  have hx₀ : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ ↦ y.2.1)
      encTrialIn encRaw := (fst _ _).comp (snd _ _)
  have hx := fixR_polytime.comp hx₀
  have hL : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ ↦ y.2.2.1)
      encTrialIn encUnary := (fst _ _).comp ((snd _ _).comp (snd _ _))
  have hLS : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ ↦
      y.2.2.2.1) encTrialIn (encList encNat) :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))
  have hB : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ ↦
      y.2.2.2.2.1) encTrialIn encUnary :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))
  have hc : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ ↦
      y.2.2.2.2.2.1) encTrialIn encBits :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))))
  have ht : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ ↦
      y.2.2.2.2.2.2) encTrialIn encUnary :=
    (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))))
  have hb : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ ↦
      Par.bits y.1 (encRaw (fixR y.2.1)).length) encTrialIn encUnary := by
    unfold Par.bits
    exact unary_add' ((encoding_length encRaw).comp hx) (unary_mul' (const 7) hN)
  have hCtr : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ ↦
      Par.Ctr y.1 y.2.2.1 (fixR y.2.1).k) encTrialIn encNat := by
    unfold Par.Ctr Par.M₂ Par.s
    exact binAdd' (unary_to_binary.comp (unary_add' (unary_mul' (const 6)
      (unary_mul' (unary_mul' (const 632) hN) hL)) (unary_add' (unary_mul' (const 20)
        (unary_mul' (unary_mul' (const 632) hN) hL)) (const 20)))) (raw_k' hx)
  have hch : ChAcc encTrialIn fun y i ↦
      Sampling.chunkVal (Par.bits y.1 (encRaw (fixR y.2.1)).length) y.2.2.2.2.2.1
        (y.2.2.2.2.2.2 * Par.Ctr y.1 y.2.2.1 (fixR y.2.1).k + i) :=
    chunkVal' (hb.comp (fst _ _)) (hc.comp (fst _ _))
      (binAdd' (binMul' (unary_to_binary.comp (ht.comp (fst _ _))) (hCtr.comp (fst _ _)))
        (snd _ _))
  have htr := trial' hN hx (fun y ↦ fixR_fit y.2.1) hL hLS hB hch
  have hcond : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ ↦
      decide (y.2.1.n + y.2.1.m ≤ y.2.1.table.length)) encTrialIn encBool :=
    binary_le' (binAdd' (raw_n' hx₀) (raw_m' hx₀)) (unary_to_binary.comp (raw_rows' hx₀))
  refine (ite_decide hcond htr (const [])).of_enc_eq fun y ↦ ?_
  by_cases h : y.2.1.n + y.2.1.m ≤ y.2.1.table.length
  · have hfix : fixR y.2.1 = y.2.1 := by
      unfold fixR
      exact if_pos h
    simp only [Function.comp_apply]
    rw [if_pos h, if_pos h, hfix]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

end BCFGJPSSV26.Stable


