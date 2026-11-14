-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime
-- name    : BCFGJPSSV26_Stable_Time_RunTime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:38:10.637395+00:00
-- url     : https://prove2.me/theorems/ee4766f2-ef61-4638-a68e-3820ef1989ff
-- title:
--   BCFGJPSSV26.Stable.Time.RunTime — The running time of the algorithm
-- statement:
--   This is module `BCFGJPSSV26.Stable.Time.RunTime` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   **With `N` as an input** (`BCFGJPSSV26.Stable.algN`: the algorithm `BCFGJPSSV26.Stable.alg` for
--   the `N` it reads in unary, `BCFGJPSSV26.Stable.alg_eq_algN`), on `((I, L), N)` with coins `r`, the
--   machine
--
--   * writes the budget `B = stableTime e₁ (I, L)`, `e₁ = 10⁶ N²`, in unary, in time polynomial in the
--     weight `W = stableTime (e₁ + 2) (I, L) = B · 2^(2L) (|I| + 2)²`
--     (`BCFGJPSSV26.Stable.exists_budget_inO`, as `SoS.Solver.exists_budget_inO`);
--   * keeps the first `min(B, R Ctr b)` coins, in time linear in the input plus a polynomial in `W`
--     (`Turing.MultiTapeTM.ComputableInO.take'`, as in `Background/BlackBox.lean`);
--   * runs the core, which is polynomial-time (`BCFGJPSSV26.Stable.coreAlg_polytime`).
--
--   Each polynomial-time step gets an input of length `O(W)`, since `2 N + 1 ≤ B` and
--   `|(I, L)| < 2^(2L) (|I| + 2)²` (`BCFGJPSSV26.Stable.comp_pow`). So the machine runs within
--   `O(W^E + |(((I, L), N), r)|)` for one `E` and every `N`, and `W^E ≤ stableTime (d e₁ + d) (I, L)`
--   for `d = 2 E` (`BCFGJPSSV26.Stable.exists_algN_inO`).
--
--   **With the accuracy as an input** (`BCFGJPSSV26.Stable.algQ`), on `((I, L), ε)` the machine
--   computes `N = BCFGJPSSV26.Stable.accN ε`, in time linear in the encoding of `ε` plus a polynomial
--   in `N` (`BCFGJPSSV26.Stable.exists_accN_inO`), and runs the algorithm for `N`. As
--   `N ≤ 2⁸ (⌈1/ε⌉ + 1)`, the time of both steps is
--   `O(stableTimeOf a 2 ((I, L), ε) + |(((I, L), ε), r)|)`, where
--   `stableTimeOf a 2 ((I, L), ε) = stableTime (a (⌈1/ε⌉ + 1)²) (I, L)`, for an absolute
--   `a = d' (10⁶ · 2¹⁶ + 1)` (`BCFGJPSSV26.Stable.stableTime_le_stableTimeOf`,
--   `BCFGJPSSV26.Stable.exists_runsInTime`); `d'` bounds `d` and the degree of the computation of `N`.
--   The budget `B` is at most `stableTimeOf a 2 ((I, L), ε)` too.
--
--   The algorithm reads the first `R Ctr b` coins, at most `B` when `k ≤ m`
--   (`BCFGJPSSV26.Stable.Par.coinLen_le_budget`); when `m < k` the core outputs all the facilities
--   whatever the coins (`BCFGJPSSV26.Stable.coreAlg_of_le`), so it may read only the first
--   `min(B, R Ctr b)` coins (`BCFGJPSSV26.Stable.algN_eq_core`).
--
--   **Contents.** The module is published as a whole: 32 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.exists_algN_inO`, `BCFGJPSSV26.Stable.exists_runsInTime` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/RunTime.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeCore
public import Definitions.Def_BCFGJPSSV26_Stable_Time_Accuracy
public import Definitions.Def_BuhaiPapers_Background_BlackBox
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Constructible

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Time.RunTime` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The running time of the algorithm

**With `N` as an input** (`BCFGJPSSV26.Stable.algN`: the algorithm `BCFGJPSSV26.Stable.alg` for
the `N` it reads in unary, `BCFGJPSSV26.Stable.alg_eq_algN`), on `((I, L), N)` with coins `r`, the
machine

* writes the budget `B = stableTime e₁ (I, L)`, `e₁ = 10⁶ N²`, in unary, in time polynomial in the
  weight `W = stableTime (e₁ + 2) (I, L) = B · 2^(2L) (|I| + 2)²`
  (`BCFGJPSSV26.Stable.exists_budget_inO`, as `SoS.Solver.exists_budget_inO`);
* keeps the first `min(B, R Ctr b)` coins, in time linear in the input plus a polynomial in `W`
  (`Turing.MultiTapeTM.ComputableInO.take'`, as in `Background/BlackBox.lean`);
* runs the core, which is polynomial-time (`BCFGJPSSV26.Stable.coreAlg_polytime`).

Each polynomial-time step gets an input of length `O(W)`, since `2 N + 1 ≤ B` and
`|(I, L)| < 2^(2L) (|I| + 2)²` (`BCFGJPSSV26.Stable.comp_pow`). So the machine runs within
`O(W^E + |(((I, L), N), r)|)` for one `E` and every `N`, and `W^E ≤ stableTime (d e₁ + d) (I, L)`
for `d = 2 E` (`BCFGJPSSV26.Stable.exists_algN_inO`).

**With the accuracy as an input** (`BCFGJPSSV26.Stable.algQ`), on `((I, L), ε)` the machine
computes `N = BCFGJPSSV26.Stable.accN ε`, in time linear in the encoding of `ε` plus a polynomial
in `N` (`BCFGJPSSV26.Stable.exists_accN_inO`), and runs the algorithm for `N`. As
`N ≤ 2⁸ (⌈1/ε⌉ + 1)`, the time of both steps is
`O(stableTimeOf a 2 ((I, L), ε) + |(((I, L), ε), r)|)`, where
`stableTimeOf a 2 ((I, L), ε) = stableTime (a (⌈1/ε⌉ + 1)²) (I, L)`, for an absolute
`a = d' (10⁶ · 2¹⁶ + 1)` (`BCFGJPSSV26.Stable.stableTime_le_stableTimeOf`,
`BCFGJPSSV26.Stable.exists_runsInTime`); `d'` bounds `d` and the degree of the computation of `N`.
The budget `B` is at most `stableTimeOf a 2 ((I, L), ε)` too.

The algorithm reads the first `R Ctr b` coins, at most `B` when `k ≤ m`
(`BCFGJPSSV26.Stable.Par.coinLen_le_budget`); when `m < k` the core outputs all the facilities
whatever the coins (`BCFGJPSSV26.Stable.coreAlg_of_le`), so it may read only the first
`min(B, R Ctr b)` coins (`BCFGJPSSV26.Stable.algN_eq_core`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-! ### The budget in binary -/

/-- The budget in binary, one certificate for all `N`. -/
theorem budget_polytime :
    ComputableInPolyTime (fun z : ℕ × Instance × ℕ ↦ Par.budget z.1 z.2.1 z.2.2)
      (encPair encUnary (encPair encInstance encUnary)) encNat := by
  unfold Par.budget stableTime Par.e₁
  have hN : ComputableInPolyTime (fun z : ℕ × Instance × ℕ ↦ z.1)
      (encPair encUnary (encPair encInstance encUnary)) encUnary := fst _ _
  have hI : ComputableInPolyTime (fun z : ℕ × Instance × ℕ ↦ z.2.1)
      (encPair encUnary (encPair encInstance encUnary)) encInstance := (fst _ _).comp (snd _ _)
  have hL : ComputableInPolyTime (fun z : ℕ × Instance × ℕ ↦ z.2.2)
      (encPair encUnary (encPair encInstance encUnary)) encUnary := (snd _ _).comp (snd _ _)
  have he : ComputableInPolyTime (fun z : ℕ × Instance × ℕ ↦ 10 ^ 6 * z.1 ^ 2)
      (encPair encUnary (encPair encInstance encUnary)) encUnary := by
    have h := unary_mul' (const (encIn := encPair encUnary (encPair encInstance encUnary))
      (10 ^ 6)) (unary_mul' hN hN)
    simpa only [sq] using h
  have h1 : ComputableInPolyTime (fun z : ℕ × Instance × ℕ ↦ 2 ^ (10 ^ 6 * z.1 ^ 2 * z.2.2))
      (encPair encUnary (encPair encInstance encUnary)) encNat :=
    binary_two_pow.comp (unary_mul' he hL)
  have hlen : ComputableInPolyTime (fun z : ℕ × Instance × ℕ ↦ (encInstance z.2.1).length + 2)
      (encPair encUnary (encPair encInstance encUnary)) encNat :=
    PolyTime.binAdd' (unary_to_binary.comp ((encoding_length encInstance).comp hI)) (const 2)
  exact PolyTime.binMul' h1 (binary_pow' hlen he)

/-! ### Sizes -/

theorem stableTime_add (a b : ℕ) (x : Instance × ℕ) :
    stableTime (a + b) x = stableTime a x * stableTime b x := by
  unfold stableTime
  rw [add_mul, pow_add, pow_add]
  ring

theorem one_le_stableTime (e : ℕ) (x : Instance × ℕ) : 1 ≤ stableTime e x :=
  Nat.one_le_iff_ne_zero.2 (by unfold stableTime; positivity)

theorem stableTime_pow (e E : ℕ) (x : Instance × ℕ) :
    stableTime e x ^ E = stableTime (E * e) x := by
  unfold stableTime
  rw [mul_pow, ← pow_mul, ← pow_mul]
  congr 2 <;> ring

/-- `2^e ≤ stableTime e`. -/
theorem two_pow_le_stableTime (e : ℕ) (x : Instance × ℕ) : 2 ^ e ≤ stableTime e x := by
  unfold stableTime
  calc 2 ^ e ≤ (((encInstance x.1).length + 2)) ^ e := Nat.pow_le_pow_left (by omega) _
    _ ≤ _ := Nat.le_mul_of_pos_left _ (by positivity)

/-- The instance with `L` is shorter than `stableTime 2`. -/
theorem length_le_stableTime_two (x : Instance × ℕ) :
    (encPair encInstance encUnary x).length + 1 ≤ stableTime 2 x := by
  rw [length_encPair, encUnary_apply, List.length_replicate]
  unfold stableTime
  set a := (encInstance x.1).length
  have h1 : x.2 + 1 ≤ 2 ^ (2 * x.2) :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : 2 * a + 4 ≤ (a + 2) ^ 2 := by nlinarith
  calc 2 * a + 1 + x.2 + 1 ≤ (x.2 + 1) * (2 * a + 4) := by nlinarith
    _ ≤ 2 ^ (2 * x.2) * (a + 2) ^ 2 := Nat.mul_le_mul h1 h2

/-- `N^D ≤ stableTime (D e₁)`. -/
theorem pow_le_stableTime (N D : ℕ) (x : Instance × ℕ) :
    N ^ D ≤ stableTime (D * Par.e₁ N) x := by
  have hN : N ≤ Par.e₁ N := by
    unfold Par.e₁
    nlinarith [Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) N]
  calc N ^ D ≤ (2 ^ N) ^ D := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = 2 ^ (N * D) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (D * Par.e₁ N) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    _ ≤ _ := two_pow_le_stableTime _ _

/-- The number `N` in unary is shorter than the budget. -/
theorem two_mul_le_budget (N : ℕ) (I : Instance) (L : ℕ) : 2 * N + 1 ≤ Par.budget N I L := by
  have h1 : 2 * N + 1 ≤ 2 ^ (2 * N) := Nat.lt_two_pow_self
  have h2 : 2 * N ≤ Par.e₁ N := by
    unfold Par.e₁
    nlinarith [Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) N]
  exact h1.trans ((Nat.pow_le_pow_right (by norm_num) h2).trans (two_pow_le_stableTime _ _))

/-- The weight `W = stableTime (e₁ + 2) (I, L) = B · stableTime 2 (I, L)` of an input
`((I, L), N)`, where `B` is the budget. -/
def wt (y : (Instance × ℕ) × ℕ) : ℕ := stableTime (Par.e₁ y.2 + 2) y.1

theorem wt_eq (y : (Instance × ℕ) × ℕ) :
    wt y = Par.budget y.2 y.1.1 y.1.2 * stableTime 2 y.1 :=
  stableTime_add _ _ _

theorem one_le_wt (y : (Instance × ℕ) × ℕ) : 1 ≤ wt y := one_le_stableTime _ _

theorem budget_le_wt (y : (Instance × ℕ) × ℕ) : Par.budget y.2 y.1.1 y.1.2 ≤ wt y := by
  rw [wt_eq]
  exact Nat.le_mul_of_pos_right _ (one_le_stableTime _ _)

theorem stableTime_two_le_wt (y : (Instance × ℕ) × ℕ) : stableTime 2 y.1 ≤ wt y := by
  rw [wt_eq]
  exact Nat.le_mul_of_pos_left _ (one_le_stableTime _ _)

/-- The inputs `((I, L), N)`, with `L` and `N` in unary. -/
abbrev encILN : (Instance × ℕ) × ℕ ↪ List Bool := encPair (encPair encInstance encUnary) encUnary

/-- The inputs `((I, L), N)` with coins. -/
abbrev encILNr : ((Instance × ℕ) × ℕ) × List Bool ↪ List Bool := encPair encILN encBits

/-! ### Writing the budget -/

/-- **Writing the budget**: in time polynomial in the weight, with one degree for all `N`. -/
theorem exists_budget_inO : ∃ D : ℕ,
    ComputableInO (fun y : (Instance × ℕ) × ℕ ↦ Par.budget y.2 y.1.1 y.1.2) encILN encUnary
      (fun y ↦ wt y ^ D) (fun y ↦ wt y ^ D) := by
  obtain ⟨c, d, hO⟩ := exists_inO_pow budget_polytime
  have hU := ComputableInO.natToUnary.comp' hO
  have hg : ComputableInO (fun y : (Instance × ℕ) × ℕ ↦ (y.2, y.1)) encILN
      (encPair encUnary (encPair encInstance encUnary))
      (fun y ↦ (encILN y).length + (encILN y).length)
      (fun y ↦ (encILN y).length + (encILN y).length) :=
    (ComputableInO.snd _ _).prod (ComputableInO.fst _ _)
  have h := hU.comp' hg
  have hb : ∀ y : (Instance × ℕ) × ℕ, (encILN y).length + (encILN y).length +
      (c * ((encPair encUnary (encPair encInstance encUnary) (y.2, y.1)).length + 1) ^ d +
        (Par.budget y.2 y.1.1 y.1.2 + 1) ^ 2) ≤ (10 + c * 2 ^ d) * (wt y ^ (d + 2) + 1) := by
    intro y
    have hW := one_le_wt y
    have hB := budget_le_wt y
    have hS := stableTime_two_le_wt y
    have hX := length_le_stableTime_two y.1
    have hN := two_mul_le_budget y.2 y.1.1 y.1.2
    have hl : (encILN y).length + 1 ≤ 3 * wt y := by
      simp only [encILN, length_encPair, encUnary_apply, List.length_replicate] at hX ⊢
      omega
    have hz : (encPair encUnary (encPair encInstance encUnary) (y.2, y.1)).length + 1 ≤
        2 * wt y := by
      simp only [length_encPair, encUnary_apply, List.length_replicate] at hX ⊢
      omega
    have hWd : wt y ^ d ≤ wt y ^ (d + 2) := Nat.pow_le_pow_right hW (by omega)
    have hW2 : wt y ^ 2 ≤ wt y ^ (d + 2) := Nat.pow_le_pow_right hW (by omega)
    have hW1 : wt y ≤ wt y ^ (d + 2) := Nat.le_self_pow (by omega) _
    have h1 : c * ((encPair encUnary (encPair encInstance encUnary) (y.2, y.1)).length + 1) ^ d ≤
        c * 2 ^ d * wt y ^ (d + 2) := by
      rw [mul_assoc]
      refine Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hz _).trans ?_)
      rw [mul_pow]
      exact Nat.mul_le_mul_left _ hWd
    have h2 : (Par.budget y.2 y.1.1 y.1.2 + 1) ^ 2 ≤ 4 * wt y ^ (d + 2) := by
      have : (Par.budget y.2 y.1.1 y.1.2 + 1) ^ 2 ≤ (2 * wt y) ^ 2 :=
        Nat.pow_le_pow_left (by omega) _
      rw [mul_pow] at this
      omega
    generalize c * ((encPair encUnary (encPair encInstance encUnary) (y.2, y.1)).length + 1) ^ d
      = X at h1 ⊢
    generalize (Par.budget y.2 y.1.1 y.1.2 + 1) ^ 2 = Y at h2 ⊢
    generalize wt y ^ (d + 2) = P at h1 h2 hW1 ⊢
    generalize c * 2 ^ d = Q at h1 ⊢
    nlinarith [Nat.zero_le Q]
  refine ⟨d + 2, h.mono _ hb fun y ↦ (hb y).trans' ?_⟩
  dsimp only
  have := budget_le_wt y
  have : Par.budget y.2 y.1.1 y.1.2 ≤ (Par.budget y.2 y.1.1 y.1.2 + 1) ^ 2 := by nlinarith
  omega

/-! ### The coins and the core -/

/-- The core with its coins given as numbers `0, 1`, on tuples with a row for each point. -/
def coreN (y : ℕ × Raw × ℕ × List ℕ × ℕ) : List ℕ :=
  if y.2.1.n + y.2.1.m ≤ y.2.1.table.length then
    coreAlg y.1 y.2.1 y.2.2.1 (y.2.2.2.1.map fun c ↦ decide (c = 1)) y.2.2.2.2 else []

/-- The encoding of the inputs of `BCFGJPSSV26.Stable.coreN`. -/
abbrev encCoreN : ℕ × Raw × ℕ × List ℕ × ℕ ↪ List Bool :=
  encPair encUnary (encPair encRaw (encPair encUnary (encPair (encList encUnary) encUnary)))

theorem coreN_polytime : ComputableInPolyTime coreN encCoreN encCenters := by
  have hc : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List ℕ × ℕ ↦
      y.2.2.2.1.map fun c ↦ decide (c = 1)) encCoreN (encList encBool) :=
    mapWithInput (f := fun _ (c : ℕ) ↦ decide (c = 1))
      ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))
      (decide_eq' (encB := encUnary) (snd _ _) (const 1))
  have hb : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List ℕ × ℕ ↦
      y.2.2.2.1.map fun c ↦ decide (c = 1)) encCoreN encBits :=
    .of_tidy (ComputableTidilyInPolyTime.listToBits.comp hc.tidy)
  exact coreAlg_polytime.comp (g := fun y : ℕ × Raw × ℕ × List ℕ × ℕ ↦
    (y.1, y.2.1, y.2.2.1, y.2.2.2.1.map fun c ↦ decide (c = 1), y.2.2.2.2))
    ((fst _ _).prod (((fst _ _).comp (snd _ _)).prod (((fst _ _).comp ((snd _ _).comp
      (snd _ _))).prod (hb.prod ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
        (snd _ _))))))))

/-- The number of coins kept: `min(B, R Ctr b)`. -/
def coinCnt (z : ℕ × (Instance × ℕ) × ℕ) : ℕ := min z.2.2 (Par.coinLen z.1 z.2.1.1 z.2.1.2)

/-- The encoding of the inputs of `BCFGJPSSV26.Stable.coinCnt`. -/
abbrev encCnt : ℕ × (Instance × ℕ) × ℕ ↪ List Bool :=
  encPair encUnary (encPair (encPair encInstance encUnary) encUnary)

theorem coinCnt_polytime : ComputableInPolyTime coinCnt encCnt encUnary := by
  unfold coinCnt Par.coinLen Par.R Par.Ctr Par.M₂ Par.s Par.bits
  have hN : ComputableInPolyTime (fun z : ℕ × (Instance × ℕ) × ℕ ↦ z.1) encCnt encUnary :=
    fst _ _
  have hI : ComputableInPolyTime (fun z : ℕ × (Instance × ℕ) × ℕ ↦ z.2.1.1) encCnt
      encInstance := (fst _ _).comp ((fst _ _).comp (snd _ _))
  have hL : ComputableInPolyTime (fun z : ℕ × (Instance × ℕ) × ℕ ↦ z.2.1.2) encCnt encUnary :=
    (snd _ _).comp ((fst _ _).comp (snd _ _))
  have hB : ComputableInPolyTime (fun z : ℕ × (Instance × ℕ) × ℕ ↦ z.2.2) encCnt encUnary :=
    (snd _ _).comp (snd _ _)
  have hs : ComputableInPolyTime (fun z : ℕ × (Instance × ℕ) × ℕ ↦ 632 * z.1 * z.2.1.2)
      encCnt encUnary := unary_mul' (unary_mul' (const 632) hN) hL
  have hR : ComputableInPolyTime (fun z : ℕ × (Instance × ℕ) × ℕ ↦
      z.1 ^ (200 * (632 * z.1 * z.2.1.2) + 1)) encCnt encNat :=
    binary_pow' (unary_to_binary.comp hN) (unary_add' (unary_mul' (const 200) hs) (const 1))
  have hC : ComputableInPolyTime (fun z : ℕ × (Instance × ℕ) × ℕ ↦
      6 * (632 * z.1 * z.2.1.2) + (20 * (632 * z.1 * z.2.1.2) + 20) + z.2.1.1.k) encCnt
      encNat :=
    PolyTime.binAdd' (unary_to_binary.comp (unary_add' (unary_mul' (const 6) hs)
      (unary_add' (unary_mul' (const 20) hs) (const 20)))) (Combine.k_polytime.comp hI)
  have hb : ComputableInPolyTime (fun z : ℕ × (Instance × ℕ) × ℕ ↦
      (encInstance z.2.1.1).length + 7 * z.1) encCnt encNat :=
    unary_to_binary.comp (unary_add' ((encoding_length encInstance).comp hI)
      (unary_mul' (const 7) hN))
  exact binary_min_unary' hB (PolyTime.binMul' (PolyTime.binMul' hR hC) hb)

theorem length_distTable (I : Instance) : (distTable I).length = I.n + I.m := by
  simp [distTable]

/-! ### The algorithm for every `N` -/

/-- **The algorithm with `N` as an input**: on `((I, L), N)` and coins, the algorithm
`BCFGJPSSV26.Stable.alg` for `N` (`BCFGJPSSV26.Stable.alg_eq_algN`). -/
def algN (y : ((Instance × ℕ) × ℕ) × List Bool) : List ℕ :=
  coreAlg y.1.2 (toRaw y.1.1.1) y.1.1.2 (y.2.take (Par.coinLen y.1.2 y.1.1.1 y.1.1.2))
    (Par.budget y.1.2 y.1.1.1 y.1.1.2)

theorem alg_eq_algN (P : Prm) (xr : (Instance × ℕ) × List Bool) :
    alg P xr = algN ((xr.1, P.N), xr.2) := rfl

/-- The algorithm reads no coins for `N = 0`, and at most the budget otherwise. -/
theorem coinLen_le_budget' {I : Instance} (hk : I.k ≤ I.m) (N L : ℕ) :
    Par.coinLen N I L ≤ Par.budget N I L := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Par.coinLen, Par.R]
  · exact Par.coinLen_le_budget hk hN

/-- **The algorithm reads at most `min(B, R Ctr b)` coins.** -/
theorem algN_eq_core (y : ((Instance × ℕ) × ℕ) × List Bool) :
    algN y = coreN (y.1.2, toRaw y.1.1.1, y.1.1.2,
      (y.2.map Universal.eBit).take (coinCnt (y.1.2, y.1.1, Par.budget y.1.2 y.1.1.1 y.1.1.2)),
      Par.budget y.1.2 y.1.1.1 y.1.1.2) := by
  obtain ⟨⟨⟨I, L⟩, N⟩, r⟩ := y
  have hfit : (toRaw I).n + (toRaw I).m ≤ (toRaw I).table.length := by
    rw [Raw.table_toRaw, length_distTable]
    rfl
  unfold coreN algN
  simp only
  rw [if_pos hfit, map_eBit_take]
  unfold coinCnt
  simp only
  by_cases hk : I.k ≤ I.m
  · rw [min_eq_right (coinLen_le_budget' hk N L)]
  · rw [coreAlg_of_le (by simp only [Raw.m_toRaw, Raw.k_toRaw]; omega),
      coreAlg_of_le (by simp only [Raw.m_toRaw, Raw.k_toRaw]; omega)]

/-! ### The algorithm with the accuracy as an input -/

/-- The parameters for the accuracy `ε`: `N = BCFGJPSSV26.Stable.accN ε ≥ 256`. -/
def prmOf (ε : ℚ) : Prm := ⟨accN ε, (le_accN ε).trans' (by norm_num)⟩

/-- **The algorithm of Theorem 1.3**: on `((I, L), ε)` and coins, the algorithm
`BCFGJPSSV26.Stable.alg` for `N = BCFGJPSSV26.Stable.accN ε`
(`BCFGJPSSV26.Stable.algQ_eq`). -/
def algQ (x : ((Instance × ℕ) × ℚ) × List Bool) : List ℕ := algN ((x.1.1, accN x.1.2), x.2)

theorem algQ_eq (I : Instance) (L : ℕ) (ε : ℚ) (r : List Bool) :
    algQ (((I, L), ε), r) = alg (prmOf ε) ((I, L), r) := rfl

/-- The inputs `((I, L), ε)`. -/
abbrev encILQ : (Instance × ℕ) × ℚ ↪ List Bool := encPair (encPair encInstance encUnary) encRat

/-- `stableTime (d e₁ + d) ≤ stableTimeOf a 2` for `N = accN ε` and
`a = d (10⁶ · 2¹⁶ + 1)`, as `N ≤ 2⁸ (⌈1/ε⌉ + 1)`. -/
theorem stableTime_le_stableTimeOf (d : ℕ) (x : (Instance × ℕ) × ℚ) :
    stableTime (d * Par.e₁ (accN x.2) + d) x.1 ≤
      stableTimeOf (d * (10 ^ 6 * 2 ^ 16 + 1)) 2 x := by
  unfold stableTimeOf
  refine stableTime_mono ?_ _
  set c := ⌈1 / x.2⌉₊
  have hN := accN_le x.2
  have hc : 1 ≤ (c + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hN2 : accN x.2 ^ 2 ≤ 2 ^ 16 * (c + 1) ^ 2 := by
    calc accN x.2 ^ 2 ≤ (256 * (c + 1)) ^ 2 := Nat.pow_le_pow_left hN _
      _ = 2 ^ 16 * (c + 1) ^ 2 := by ring
  unfold Par.e₁
  calc d * (10 ^ 6 * accN x.2 ^ 2) + d ≤ d * (10 ^ 6 * (2 ^ 16 * (c + 1) ^ 2)) + d * (c + 1) ^ 2 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hN2))
          (Nat.le_mul_of_pos_right _ hc)
    _ = d * (10 ^ 6 * 2 ^ 16 + 1) * (c + 1) ^ 2 := by ring

end BCFGJPSSV26.Stable


