-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Top65Correct
-- name    : LinearSetReconciliation327_Main_Top65Correct
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-21T10:22:52.997634+00:00
-- url     : https://prove2.me/theorems/6dbe70ba-f492-4083-88b4-8a166d48b7de
-- title:
--   Theorem 6.5, conjunct 8: the correctness half, the abstract recovery law, and the seed-indexed bridge
-- statement:
--   **The correctness half of Theorem 6.5's conjunct 8, with the platform interfaces it consumes.**  This bundle records exactly what the platform already supplies for the decoder's correctness and what it does not.
--
--   §1 defines `Up5Export`: Theorem 5.1's export clause in the shape a pipeline stage consumes — the toggle and decoder are single compiled blocks with *base-relative* contracts, the payload base in register $r_{15}$ and the table base in $r_{14}$.  `up5Export_togglesWithin` and `up5Export_decoderStart` prove that at base $0$ the two clauses *imply* 5.1's own toggle conjunct and 5.1's own `OutputsSupport` conclusion, so the export is a genuine strengthening of 5.1's machine content, not a restatement of 6.5.
--
--   §2 proves `allValid_of_valid`: if the root satisfies `Node.Valid`, `Node.WF` and `AllBounds` hold, then `AllValid` holds at *every* node of the recursion tree.  This is the bridge between `theorem_4_9`'s hypothesis set (root `Valid`) and the newer platform theorem `hint_decode_correct` (hypothesis `AllValid` at every node); the two hypothesis sets are equivalent.
--
--   §3 proves the abstract recovery law `decode_of_allValid` and `decode_of_valid_bounds`: for a CR family with `CR.Recovers`, $T.WF$, $T.AllBounds$ and root $T.Valid$, one has
--
--   $$
--   T.\mathrm{decode}\ CR\ r\ (T.\mathrm{sketch}\ CR\ r\ x)\ J = \mathrm{some}\ x
--   $$
--
--   for every seed $r$ — the deterministic half of conjunct 8 at the abstract level, routed through the Proved platform theorems `theorem_4_9` and `hint_decode_correct`.
--
--   §4 defines `TopDecCorrectsEnv`, the correctness predicate at a *family* of environments indexed by the seed (6.5 runs its decoder under `spec.env W det r`), and proves `conjunct8_of_correctsEnv`: conjunct 7 (the decoder halts) together with worst-case correctness yields conjunct 8's probability inequality **with no loss in $\varepsilon$** — the event holds at every seed, so its probability is $1$, and $\varepsilon$ can only come from the stages' own failure probabilities.
--
--   §5 is the stage-by-stage accounting: which of the six §9.2 stages close from a proved platform statement (2.1, 2.3, 5.1 and the time shapes) and which need a program or a contract that does not exist yet (the prologue, the assembly and residual blocks, the base-relative exports and the loop dispatchers).
--
--   **Formalization Note** Definitions and fully proved lemmas only; no `sorry`, no new axiom.  The declarations that cite the platform theorems inherit their proofs, not their statements' placeholder `sorryAx`.  `prU_eq_card`/`prU_mono`/`prU_true` are re-proved here because the platform's `Theorems` mirrors export statements only.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §9.2 and Theorem 6.5, PDF p.31 (printed p.30); Theorem 5.1 (export clause) and Theorem 4.9; Proposition 2.1 and Proposition 2.3 for the stage accounting.  Extracted from `Solutions/Sol_theorem_6_5.lean` §11 and `Solutions/_65_correct_block.lean.txt`.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Definitions.Def_LinearSetReconciliation327_Main_Top65Dec
import Definitions.Def_LinearSetReconciliation327_Main_NodeValidity
import Theorems.Thm_LinearSetReconciliation327_Main_theorem_4_9
import Theorems.Thm_LinearSetReconciliation327_Main_hint_decode_correct
/-!
# `Top65Correct`: the correctness half of Theorem 6.5's conjunct 8

Conjunct 8 of `theorem_6_5_statement` has two halves:

* a **probability** half — `1 - ε ≤ prU (fun r => ∃ s', HaltsWithin … ∧ OutputsSupport s' x)`, whose
  content is the paper's union bound over the tree's capacity bounds;
* a **correctness** half — every halting run from the sketch of `x` outputs `supp x`, i.e.
  `TopDecCorrects` (`Definitions.Def_…_Top65Dec` §13.7).

This module records, with nothing unproved, exactly what the *platform* now supplies for both halves
and what it does not.  Its content:

* §1 `Up5Export` — the export clause of Theorem 5.1, with `down` (the decoder run at a caller-chosen
  payload base) in the shape a pipeline stage consumes.  `up5Export_togglesWithin` and
  `up5Export_decoderStart` show the two clauses are not vacuous: at base `0` they *imply* 5.1's own
  toggle conjunct and 5.1's own `OutputsSupport` conclusion.
* §2 `allValid_of_valid` — the root's `Node.Valid` together with `AllBounds` gives `AllValid` at
  every node.  This is the missing bridge between `theorem_4_9`'s hypothesis set and the new
  platform theorem `hint_decode_correct`, whose hypothesis is `AllValid`.
* §3 `decode_of_allValid`, `decode_of_valid_bounds` — the abstract recovery law, by the two platform
  routes (`hint_decode_correct` and `theorem_4_9`); they agree, and 4.9's hypothesis is the weaker.
* §4 `TopDecCorrectsEnv` — `TopDecCorrects` with the environment a *family* over the seed, which is
  what `theorem_6_5_statement` actually runs its decoder under (`spec.env W det r`), and
  `conjunct8_of_correctsEnv`: conjuncts 7 + 8 of 6.5 follow from a worst-case correctness statement
  **with no `ε` loss at all** (`1 - ε ≤ 1 = prU True`).
* §5 the stage-by-stage accounting: which of the six stages of §9.2 close from a proved platform
  statement and which need a statement that does not exist.
-/

set_option autoImplicit false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

open Classical

/-! ## 0. `prU` arithmetic -/

/-- Unfolding `prU` (with the same `Classical` decidability instance the definition used). -/
lemma prU_eq_card {α : Type} [Fintype α] (P : α → Prop) :
    prU P = ((univ.filter P).card : ℝ) / (Fintype.card α : ℝ) := rfl

/-- `prU` is monotone in the event. -/
lemma prU_mono {α : Type} [Fintype α] {P Q : α → Prop} (h : ∀ a, P a → Q a) : prU P ≤ prU Q := by
  have h1 : (univ.filter P).card ≤ (univ.filter Q).card := by
    apply Finset.card_le_card
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, h a ha.2⟩
  rw [prU_eq_card P, prU_eq_card Q]
  exact div_le_div_of_nonneg_right (by exact_mod_cast h1) (by positivity)

/-- The probability of a certain event is one. -/
lemma prU_true {α : Type} [Fintype α] [Nonempty α] : prU (fun _ : α => True) = 1 := by
  rw [prU_eq_card]
  simp

/-! ## 1. The export clause of Theorem 5.1 (`Up5Export`)

`theorem_5_1`'s *statement* exports its two witnesses as bare `Program`s, with `TogglesWithin` and
`HaltsWithin … (decoderStart W y J)`.  Both notions pin the payload at word `0` and every register
but `r0`–`r2` at `0`, so neither transports to a block running at the composite's word base, and a
bare `Program` ending in `halt` cannot be sequenced (published: `step_halt_self`,
`append_halt_frozen`, `togglesWithin_exists_halt`; and `togglesWithin_without_frame`,
`togglesWithin_no_offset_transport` in `Solutions/_65_cond_block.lean.txt` §4 exhibit the frame and
the transport failures with a four-instruction program).

`Up5Export` is the extra content 6.5's composite needs *from 5.1's own construction*: each witness is
one compiled `Stmt` (`Definitions.Def_…_DecoderModel`, so `Sup.compile δ` is the same block at
offset `δ`), and each has a **base-relative** contract.  Register `r15` is the payload base and `r14`
the table base (the tree's convention, not 5.1's decoder's `r15 = 1`, `r14 = W`; see
`Solutions/PROMPT_5_1_EXPORT.md`). -/
structure Up5Export (progUp progDec : Program) (Cu : ℝ) (pu : ℕ) (Cd : ℝ) : Prop where
  /-- 5.1's toggle program is one compiled block followed by `halt`. -/
  block : ∃ Sup : Stmt, Sup.compile 0 ++ [Instr.halt] = progUp
  /-- **The per-block toggle contract**: from *any* payload word base `β` (`r15`), *any* `det` base
  `δ` (`r14`), *any* coordinate `i` (`r0`) and *any* environment of the right width, the block XORs
  the column `H_s e_i` into the words `[β, β + wordsOf)`, leaves every other word alone (the frame
  clause), and stops at its own end. -/
  up : ∀ (n W N Ms : ℕ) (E : RAMEnv) (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2))
      (δ β : ℕ) (y : Fin Ms → ZMod 2) (i : Fin N) (s : RAMState),
      E.W = W → s.pc = 0 → s.regs 14 = δ → s.regs 15 = β → s.regs 0 = i.val →
      (∀ j < wordsOf W Ms, s.mem (β + j) = packMem W y j) →
      ∃ s', HaltsWithin progUp E (Cu * lg (n : ℝ) ^ pu) s s' ∧
        s'.regs 15 = β ∧ s'.regs 0 = s.regs 0 ∧
        (∀ j < wordsOf W Ms, s'.mem (β + j) = packMem W (y + Hs (Pi.single i 1)) j) ∧
        (∀ c, c ∉ Finset.range (wordsOf W Ms) → s'.mem (β + c) = s.mem (β + c))
  /-- 5.1's decoder is one compiled block followed by `halt`. -/
  dblock : ∃ Sdec : Stmt, Sdec.compile 0 ++ [Instr.halt] = progDec
  /-- **The decoder's contract at a caller-chosen payload base** — the one external gap of 6.5's
  conjuncts 7–8.  From `pc = 0`, the payload `hintMem W x J` (syndrome followed by the hint) at word
  base `r15 = base`, and nothing assumed about the rest of memory, the block halts within 5.1's
  budget `Cd · N · exp (Cd (lg lg n)²)` with the explicit output `supp x`, and writes nothing below
  `base` (so the blocks of a dispatcher laid out at increasing bases do not clobber each other). -/
  down : ∀ (n W N Ms : ℕ) (E : RAMEnv) (x : Fin Ms → ZMod 2) (J : List ℕ)
      (base : ℕ) (s : RAMState),
      E.W = W → s.pc = 0 → s.regs 15 = base →
      (∀ j < wordsOf W Ms, s.mem (base + j) = hintMem W x J j) →
      ∃ s', HaltsWithin progDec E (Cd * (N : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2)) s s' ∧
        OutputsSupport s' x ∧
        (∀ c, c < base → s'.mem c = s.mem c)

/-- **The export clause is a genuine strengthening of 5.1's own toggle conjunct**: from `Up5Export`,
`TogglesWithin` at the child's parameters and 5.1's budget follows by the `β = δ = 0` instance — the
state `TogglesWithin` starts from has every register except `r0` equal to `0`, so `r14 = r15 = 0`. -/
theorem up5Export_togglesWithin {progUp progDec : Program} {Cu : ℝ} {pu : ℕ} {Cd : ℝ} {n : ℕ}
    (h : Up5Export progUp progDec Cu pu Cd) (E : RAMEnv) {N M : ℕ}
    (H : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)) :
    TogglesWithin progUp E H (Cu * lg (n : ℝ) ^ pu) := by
  intro y i
  obtain ⟨s', hhalt, -, -, hmem, -⟩ :=
    h.up n E.W N M E H 0 0 y i (initState (packMem E.W y) i.val 0 0) rfl rfl
      (by simp [initState]) (by simp [initState]) (by simp [initState])
      (by intro j _; simp [initState])
  refine ⟨s', hhalt, fun addr haddr => ?_⟩
  simpa using hmem addr haddr

/-- **The `down` clause is not vacuous**: at base `0` and from `decoderStart` it yields 5.1's own
recovery conclusion — `OutputsSupport` of a halting run of 5.1's decoder within 5.1's budget. -/
theorem up5Export_decoderStart {progUp progDec : Program} {Cu : ℝ} {pu : ℕ} {Cd : ℝ}
    (h : Up5Export progUp progDec Cu pu Cd) {W M N n : ℕ} (E : RAMEnv) (hEW : E.W = W)
    (x : Fin M → ZMod 2) (J : List ℕ) :
    ∃ s', HaltsWithin progDec E (Cd * (N : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2))
      (decoderStart W x J) s' ∧ OutputsSupport s' x := by
  have hpc : (decoderStart W x J).pc = 0 := by simp [decoderStart, initState]
  have h15 : (decoderStart W x J).regs 15 = 0 := by simp [decoderStart, initState]
  have hmem : ∀ j < wordsOf W M, (decoderStart W x J).mem (0 + j) = hintMem W x J j := by
    intro j _
    simp [decoderStart, initState]
  obtain ⟨s', h1, h2, -⟩ := h.down n W N M E x J 0 (decoderStart W x J) hEW hpc h15 hmem
  exact ⟨s', h1, h2⟩

/-! ## 2. `AllValid` from the root's `Valid`

`hint_decode_correct`'s hypothesis is `AllValid` at every node; the hypotheses 6.5 can supply (and
the ones `theorem_4_9` uses) are `Valid` at the *root* plus `AllBounds`.  This section proves the
bridge.  At a `recursive` node the child receives `C_s(x) + P_s` with hint `J_s`, and the bounds
`U_s ≤ X_s`, `V_s ≤ Y_s` are exactly `|J_s| ≤ X_s` and `|(C_s(x) + P_s) \ J_s| ≤ Y_s`. -/

namespace C65

lemma filter_symmDiff (p : ℕ → Prop) [DecidablePred p] (A B : Finset ℕ) :
    (symmDiff A B).filter p = symmDiff (A.filter p) (B.filter p) := by
  classical
  ext a
  simp only [mem_symmDiff, mem_filter]
  tauto


/-- The parity of a symmetric-difference cardinality is the XOR of the two parities (each coordinate
in the intersection contributes twice). -/
lemma odd_card_symmDiff (A B : Finset ℕ) :
    Odd (symmDiff A B).card ↔ (Odd A.card ∧ ¬ Odd B.card) ∨ (Odd B.card ∧ ¬ Odd A.card) := by
  classical
  have hdisj1 : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have hdisj2 : Disjoint (A \ B) (A ∩ B) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).2
  have hdisj3 : Disjoint (B \ A) (A ∩ B) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).1
  have hAB : (symmDiff A B).card = (A \ B).card + (B \ A).card := by
    rw [symmDiff_def, sup_eq_union]
    exact Finset.card_union_of_disjoint hdisj1
  have hA : A.card = (A \ B).card + (A ∩ B).card := by
    have hunion : A \ B ∪ A ∩ B = A := by
      ext a
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    calc A.card = (A \ B ∪ A ∩ B).card := by rw [hunion]
      _ = (A \ B).card + (A ∩ B).card := Finset.card_union_of_disjoint hdisj2
  have hB : B.card = (B \ A).card + (A ∩ B).card := by
    have hunion : B \ A ∪ A ∩ B = B := by
      ext a
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    calc B.card = (B \ A ∪ A ∩ B).card := by rw [hunion]
      _ = (B \ A).card + (A ∩ B).card := Finset.card_union_of_disjoint hdisj3
  rw [hAB, hA, hB, Nat.odd_add, Nat.odd_add, Nat.odd_add, ← Nat.not_odd_iff_even,
    ← Nat.not_odd_iff_even]
  tauto

open Classical in
/-- The CR syndrome `CR_{N,t} x` is additive in `x` (each row of the syndrome is one syndrome bit). -/
lemma sketch_symmDiff (CR : CRFamily) (N t : ℕ) (x y : Finset ℕ) :
    CR.sketch N t (symmDiff x y) = symmDiff (CR.sketch N t x) (CR.sketch N t y) := by
  classical
  ext r
  have hfilt : (symmDiff x y).filter (fun i => r ∈ CR.col N t i) =
      symmDiff (x.filter fun i => r ∈ CR.col N t i) (y.filter fun i => r ∈ CR.col N t i) :=
    filter_symmDiff _ x y
  simp only [CRFamily.sketch, hfilt, mem_symmDiff, mem_filter, mem_range, true_and,
    odd_card_symmDiff]
  tauto


/-! ## 8. The hint matrix `H`

`H r` is the flattened sketch: the support of `x`, flattened through `bitVal`, for the tree seed
obtained from the public seed `r`.  The seed splitting itself is built in section 8b below. -/

/-- The support of a `ZMod 2` vector over `[N]`, as the `Finset ℕ` on which `Node.sketch` acts. -/
def support {N : ℕ} (x : Fin N → ZMod 2) : Finset ℕ := (univ.filter fun i => x i = 1).image Fin.val


/-- The column of a singleton input is a subset of `[m]`. -/
lemma column_subset_range (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ) (s : Fin sch.ℓ) :
    sch.column lr x s ⊆ range sch.m := by
  intro v hv
  unfold RowScheme.column RowScheme.rowsWhere at hv
  rw [mem_image] at hv
  obtain ⟨j, -, rfl⟩ := hv
  exact mem_range.mpr j.isLt


/-! # 12.  `Node.decode` correctness, and `hgood` for Theorem 5.1's conjunct 8

`uuu51` reduced conjunct 8 to the semantic hypothesis

```
hgood : ∀ i : Fin N, (i.val ∈ Φ (cnt - 1) ↔ x i = 1)
```

where `Φ (cnt - 1)` is the set returned by the last schedule call — the root's residual `CR` call,
which is last because `decSched` appends it after the children (`decSched` `.recursive` case) and
`hintP.tree` never returns `.store`.  No *per-call* contract can imply `hgood` (a contract on one call
cannot see the union of the calls' sets), so it must come from the **assembly**: when every node's
decode succeeds, the tree decode reconstructs `x`.

This section supplies exactly that:

* `decode_sketch` — `Node.decode CR T r (Node.sketch CR T r x) J = some x` under the per-node
  hypotheses `WF`, `AllBounds`, `AllValid` and `CR.Recovers`.  The proof is a recursion mirroring
  `Node.decode`: `store` is `rfl`, `cr` is `CR.dec`, and `direct` / `recursive` say "the stored
  columns (resp. the children) yield the exact transcript, hence the assembled estimate is
  `exactEstimate`, hence the residual's error has weight `Z ≤ t` and `CR.Recovers` finishes".
* `AllValid` — `Valid` at every node — plus `allValid_of_valid`: the root's `Valid` together with
  `WF` and `AllBounds` *already* gives it (`U_s ≤ X_s`, `V_s ≤ Y_s` turn the child's input into a
  valid instance), so it is **not** an extra assumption.
* `hgood_of_decode` / `hgood_lastCall` — `hgood`, and the proof that its only non-per-node input is
  the *interface equation* identifying `Φ (cnt - 1)` with the decode's answer.

## 12.1  Membership, counting and `ZMod 2` helpers -/

/-- Membership in `rowsWhere`: the image is injective. -/
lemma mem_rowsWhere {sch : RowScheme} (P : Fin sch.m → Prop) (j : Fin sch.m) :
    j.val ∈ sch.rowsWhere P ↔ P j := by
  classical
  unfold RowScheme.rowsWhere
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j', hj', hv⟩
    have hP : P j' := by
      have h2 := hj'
      simp only [Finset.mem_filter] at h2
      exact h2.2
    have hjj : j' = j := Fin.ext hv
    rwa [hjj] at hP
  · intro h
    refine ⟨j, ?_, rfl⟩
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h⟩


/-- `rowsWhere` lands in `[m]`. -/
lemma rowsWhere_subset_range (sch : RowScheme) (P : Fin sch.m → Prop) :
    sch.rowsWhere P ⊆ Finset.range sch.m := by
  intro a ha
  unfold RowScheme.rowsWhere at ha
  rw [Finset.mem_image] at ha
  obtain ⟨j, -, rfl⟩ := ha
  exact Finset.mem_range.mpr j.isLt


/-- A symmetric difference stays inside `[N]`. -/
lemma symmDiff_subset_range {N : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ Finset.range N) (hB : B ⊆ Finset.range N) :
    symmDiff A B ⊆ Finset.range N := by
  intro a ha
  rcases Finset.mem_symmDiff.mp ha with ⟨h, -⟩ | ⟨h, -⟩
  · exact hA h
  · exact hB h


/-- The column membership, unfolded: row `j` is in `C_s(x)` iff its codeword bit is `1`. -/
lemma mem_column_iff (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ) (s : Fin sch.ℓ)
    (j : Fin sch.m) :
    j.val ∈ sch.column lr x s ↔ sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1 := by
  classical
  unfold RowScheme.column
  exact mem_rowsWhere _ j


/-- A membership indicator over a set whose membership is a codeword bit. -/
lemma ite_mem_code {S : Finset ℕ} {a : ℕ} {c : ZMod 2} (h : a ∈ S ↔ c = 1) :
    (if a ∈ S then (1 : ZMod 2) else 0) = c := by
  by_cases hS : a ∈ S
  · rw [if_pos hS]; exact (h.mp hS).symm
  · rw [if_neg hS]
    rcases zmod2_eq_zero_or_one c with hc | hc
    · exact hc.symm
    · exact absurd (h.mpr hc) hS


/-- Counting `[m]`-membership: for `S ⊆ [m]`, the `Fin m` filter and `S` have the same cardinality. -/
lemma card_fin_filter_eq {m : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range m) :
    (Finset.univ.filter fun j : Fin m => (j.val : ℕ) ∈ S).card = S.card := by
  classical
  have himg : (Finset.univ.filter fun j : Fin m => (j.val : ℕ) ∈ S).image
      (fun j : Fin m => j.val) = S := by
    ext a
    rw [Finset.mem_image]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have h2 := hj
      simp only [Finset.mem_filter] at h2
      exact h2.2
    · intro ha
      refine ⟨⟨a, Finset.mem_range.mp (hS ha)⟩, ?_, rfl⟩
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ha⟩
  have hc : ((Finset.univ.filter fun j : Fin m => (j.val : ℕ) ∈ S).image
      (fun j : Fin m => j.val)).card
      = (Finset.univ.filter fun j : Fin m => (j.val : ℕ) ∈ S).card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext h)
  rw [← hc, himg]


/-- `Finset.filter` does not depend on which `DecidablePred` instance is used. -/
lemma filter_congr_dec {α : Type} (p : α → Prop) (d₁ d₂ : DecidablePred p) (s : Finset α) :
    @Finset.filter α p d₁ s = @Finset.filter α p d₂ s := by
  ext a
  rw [@Finset.mem_filter α p d₁ s a, @Finset.mem_filter α p d₂ s a]


/-- `|J_s| = U_s`: both count the rows whose prediction is `⊥`.  The two filters are built by
different definitions and hence carry different `DecidablePred` instances, so they are compared
through `filter_congr_dec`. -/
lemma exactHint_card (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ) :
    (sch.exactHint lr x J s).card = sch.U lr x J s := by
  have key : ∀ (d : DecidablePred fun j : Fin sch.m => sch.exactPred lr x J s j = none),
      (sch.exactHint lr x J s).card
        = (@Finset.filter (Fin sch.m)
            (fun j => sch.exactPred lr x J s j = none) d Finset.univ).card := by
    intro d
    unfold RowScheme.exactHint RowScheme.rowsWhere
    rw [← show (@Finset.filter (Fin sch.m)
          (fun j => sch.exactPred lr x J s j = none)
          (fun a => Classical.propDecidable (sch.exactPred lr x J s a = none))
          Finset.univ).card
        = (@Finset.filter (Fin sch.m)
            (fun j => sch.exactPred lr x J s j = none) d Finset.univ).card from
      congrArg Finset.card (filter_congr_dec _ _ d Finset.univ)]
    exact Finset.card_image_of_injective _ (fun a b h => Fin.ext h)
  unfold RowScheme.U
  exact key _


/-- `ZMod 2` has no third value: `b ≠ c ↔ ¬ ((c = 1) ↔ (b = 1))`. -/
lemma zmod2_ne_iff_not_iff (b c : ZMod 2) :
    b ≠ c ↔ ¬ ((c = 1) ↔ (b = 1)) := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one c with rfl | rfl <;> simp


/-- The pointwise shape of `(C_s + P_s) \ J_s`: a wrong prediction. -/
lemma symmDiff_sdiff_hint_iff (p : Option (ZMod 2)) (c : ZMod 2) :
    (¬ ((c = 1) ↔ (p = some 1)) ∧ p ≠ none) ↔ ∃ b, p = some b ∧ b ≠ c := by
  constructor
  · rintro ⟨hiff, hne⟩
    obtain ⟨b, hb⟩ : ∃ b, p = some b := by
      cases p with
      | none => exact absurd rfl hne
      | some b => exact ⟨b, rfl⟩
    refine ⟨b, hb, ?_⟩
    rw [hb, Option.some.injEq] at hiff
    exact (zmod2_ne_iff_not_iff b c).mpr hiff
  · rintro ⟨b, hb, hne⟩
    subst hb
    refine ⟨?_, by simp⟩
    rw [Option.some.injEq]
    exact (zmod2_ne_iff_not_iff b c).mp hne


/-- `|(C_s + P_s) \ J_s| = V_s`: a coordinate is in the difference iff its prediction is wrong. -/
lemma exactChild_diff_hint_card (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) :
    ((sch.exactChildInput lr x J s) \ (sch.exactHint lr x J s)).card = sch.V lr x J s := by
  classical
  have hD : (sch.exactChildInput lr x J s \ sch.exactHint lr x J s) ⊆ Finset.range sch.m :=
    fun a ha => (symmDiff_subset_range (column_subset_range sch lr x s)
      (rowsWhere_subset_range sch _)) (Finset.mem_sdiff.mp ha).1
  have hstep : ∀ j : Fin sch.m,
      (j.val ∈ sch.exactChildInput lr x J s \ sch.exactHint lr x J s) ↔
        ∃ b, sch.exactPred lr x J s j = some b ∧
          b ≠ sch.code j (lr.2 j) (sch.rowOf lr x j) s := by
    intro j
    have hcol : j.val ∈ sch.column lr x s ↔
        sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1 := mem_column_iff sch lr x s j
    have hP : j.val ∈ sch.exactP lr x J s ↔ sch.exactPred lr x J s j = some 1 := by
      unfold RowScheme.exactP
      exact mem_rowsWhere _ j
    have hH : j.val ∈ sch.exactHint lr x J s ↔ sch.exactPred lr x J s j = none := by
      unfold RowScheme.exactHint
      exact mem_rowsWhere _ j
    have hs : (j.val ∈ symmDiff (sch.column lr x s) (sch.exactP lr x J s)) ↔
        ¬ ((j.val ∈ sch.column lr x s) ↔ (j.val ∈ sch.exactP lr x J s)) := by
      rw [Finset.mem_symmDiff]
      tauto
    unfold RowScheme.exactChildInput
    rw [Finset.mem_sdiff, hs, hcol, hP, hH]
    exact symmDiff_sdiff_hint_iff _ _
  rw [← card_fin_filter_eq hD]
  have hVdef : sch.V lr x J s =
      (Finset.univ.filter fun j : Fin sch.m => ∃ b, sch.exactPred lr x J s j = some b ∧
        b ≠ sch.code j (lr.2 j) (sch.rowOf lr x j) s).card := rfl
  rw [hVdef]
  exact congrArg Finset.card (Finset.ext fun j => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hstep j)


/-! ## 12.2  `symmDiff`, `assemble` and `Valid` helpers -/

/-- Cancelling a symmetric difference: `A Δ (B Δ A) = B`. -/
lemma symmDiff_self_cancel (A B : Finset ℕ) : symmDiff A (symmDiff B A) = B := by
  ext a
  simp only [Finset.mem_symmDiff]
  tauto


/-- The assembled vector lands in `[N]`. -/
lemma assemble_subset_range (N m : ℕ) (π : Equiv.Perm (Fin N)) (est : ℕ → Finset ℕ) :
    assemble N m π est ⊆ Finset.range N := by
  intro a ha
  rw [assemble, Finset.mem_image] at ha
  obtain ⟨i, -, rfl⟩ := ha
  exact Finset.mem_range.mpr i.isLt


/-- The assembled row estimates land in `[N]`. -/
lemma assembled_subset_range (sch : RowScheme) (lr : sch.LocalSeed) (J : Finset ℕ)
    (pref : Fin sch.m → List (ZMod 2)) :
    sch.assembled lr J pref ⊆ Finset.range sch.N :=
  assemble_subset_range sch.N sch.m lr.1 _


/-- The capacity bound of a valid instance: `|x| ≤ X + Y`. -/
lemma Valid.card_le {N X Y : ℕ} {x J : Finset ℕ} (h : Node.Valid N X Y x J) :
    x.card ≤ X + Y := by
  obtain ⟨-, -, hJ, hx⟩ := h
  have h1 : (x \ J).card + (x ∩ J).card = x.card := Finset.card_sdiff_add_card_inter x J
  have h2 : (x ∩ J).card ≤ J.card := Finset.card_le_card Finset.inter_subset_right
  omega


/-- The universe bound of a valid instance: `|x| ≤ N`. -/
lemma Valid.card_le_N {N X Y : ℕ} {x J : Finset ℕ} (h : Node.Valid N X Y x J) :
    x.card ≤ N := by
  have h1 : x.card ≤ (Finset.range N).card := Finset.card_le_card h.1
  rwa [Finset.card_range] at h1


theorem allValid_of_valid :
    ∀ (T : Node), ∀ (X Y : ℕ) (r : Node.Seed T) (x J : Finset ℕ),
      Node.WF T X Y → Node.AllBounds T r x J → Node.Valid T.N X Y x J →
        AllValid X Y T r x J := by
  intro T
  induction T with
  | store N =>
      intro X Y r x J _ _ _
      trivial
  | cr N t =>
      intro X Y r x J _ _ hV
      exact hV
  | direct sch t =>
      intro X Y r x J _ _ hV
      exact hV
  | recursive sch t Xs Ys child ih =>
      intro X Y r x J hWF hB hV
      obtain ⟨htN, hWFc⟩ := hWF
      obtain ⟨hZ, hUV⟩ := hB
      refine ⟨hV, ?_⟩
      intro s
      apply ih s (Xs s) (Ys s) (r.2 s) (sch.exactChildInput r.1 x J s)
        (sch.exactHint r.1 x J s) (hWFc s).2 (hUV s).2.2
      rw [(hWFc s).1]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact symmDiff_subset_range (column_subset_range sch r.1 x s)
          (rowsWhere_subset_range sch _)
      · exact rowsWhere_subset_range sch _
      · have h1 := exactHint_card sch r.1 x J s
        have h2 := (hUV s).1
        omega
      · have h1 := exactChild_diff_hint_card sch r.1 x J s
        have h2 := (hUV s).2.1
        omega

end C65

/-- **`AllValid` is not an extra assumption**: the root's `Valid`, together with `WF` and `AllBounds`,
already gives `Valid` at every node.  Hence `hint_decode_correct`'s hypothesis is implied by
`theorem_4_9`'s. -/
theorem allValid_of_valid :
    ∀ (T : Node), ∀ (X Y : ℕ) (r : Node.Seed T) (x J : Finset ℕ),
      Node.WF T X Y → Node.AllBounds T r x J → Node.Valid T.N X Y x J →
        AllValid X Y T r x J :=
  C65.allValid_of_valid

/-! ## 3. The abstract recovery law, by both platform routes -/

/-- The law from the new platform theorem `hint_decode_correct` (theorem id
`0a2f9539-5c95-4a80-812b-b0ff01e68b73`, status **Proved**). -/
theorem decode_of_allValid {CR : CRFamily} (hRec : CR.Recovers) {T : Node} {X Y : ℕ}
    {r : Node.Seed T} {x J : Finset ℕ} (hWF : T.WF X Y) (hB : T.AllBounds r x J)
    (hV : AllValid X Y T r x J) :
    Node.decode CR T r (Node.sketch CR T r x) J = some x :=
  hint_decode_correct CR hRec T X Y r x J hWF hB hV

/-- The same law from `theorem_4_9` (status **Proved**), whose hypothesis is strictly weaker: `Valid`
at the root instead of `AllValid` at every node. -/
theorem decode_of_valid_bounds {CR : CRFamily} (hRec : CR.Recovers) {T : Node} {X Y : ℕ}
    {r : Node.Seed T} {x J : Finset ℕ} (hWF : T.WF X Y) (hB : T.AllBounds r x J)
    (hV : Node.Valid T.N X Y x J) :
    Node.decode CR T r (Node.sketch CR T r x) J = some x :=
  (theorem_4_9 CR hRec T X Y hWF x J hV).1 r hB

/-- The two routes agree, and the second one goes through for every hypothesis the first accepts
(the `AllValid` of the first is produced by §2). -/
theorem decode_of_allValid_via_49 {CR : CRFamily} (hRec : CR.Recovers) {T : Node} {X Y : ℕ}
    {r : Node.Seed T} {x J : Finset ℕ} (hWF : T.WF X Y) (hB : T.AllBounds r x J)
    (hV : Node.Valid T.N X Y x J) :
    Node.decode CR T r (Node.sketch CR T r x) J = some x :=
  decode_of_allValid hRec hWF hB (allValid_of_valid T X Y r x J hWF hB hV)

/-! ## 4. Conjunct 8 from worst-case correctness

`TopDecCorrects` (`Def_…_Top65Dec` §13.7) fixes one environment `E`.  But 6.5 runs its decoder under
`spec.env W det r`, which *depends on the seed*, so the predicate has to be stated for a family of
environments.  `TopDecCorrectsEnv` is that correction; `topDecCorrectsEnv_of_fixed` recovers the
fixed-environment form, and `conjunct8_of_correctsEnv` shows the payoff: **given conjunct 7 (the
decoder halts), a worst-case correctness statement closes conjunct 8 with no probability loss at
all** — the `ε` of 6.5 can only come from the stages failing, never from the composition. -/

/-- The correctness half of conjunct 8, with the environment a family over the seed. -/
def TopDecCorrectsEnv {ι : Type} (Sinit Srow Sdec Sassem Sres Scr : Stmt) (env : ι → RAMEnv)
    {n M : ℕ} (D : (Fin n → ZMod 2) → Fin M → ZMod 2) (Tdec : ℝ) : Prop :=
  ∀ (i : ι) (x : Fin n → ZMod 2) (s' : RAMState),
    (∃ k : ℕ, (k : ℝ) ≤ Tdec ∧
      (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (env i))^[k]
        (decoderStart (env i).W (D x) []) = s' ∧
      Halted (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) s') →
    OutputsSupport s' x

/-- The seed-independent form is the constant family. -/
theorem topDecCorrectsEnv_of_fixed {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv} {n M : ℕ}
    {D : (Fin n → ZMod 2) → Fin M → ZMod 2} {Tdec : ℝ}
    (h : TopDecCorrects Sinit Srow Sdec Sassem Sres Scr E D Tdec) :
    TopDecCorrectsEnv Sinit Srow Sdec Sassem Sres Scr (fun _ : Unit => E) D Tdec := by
  intro i x s' hs'
  exact h x s' hs'

/-- **Conjunct 8 of Theorem 6.5, from conjunct 7 and the correctness half — with no `ε`.**

`prU` of the recovery event is `1`, because the event holds at *every* seed: conjunct 7 supplies a
halting run and the correctness hypothesis identifies its output.  So `ε` enters 6.5 only through the
stages (the `prU` conjuncts of 5.1, 2.1, 2.3 and the capacity bounds), never through this step. -/
theorem conjunct8_of_correctsEnv {ι : Type} [Fintype ι] [Nonempty ι]
    {Sinit Srow Sdec Sassem Sres Scr : Stmt} {env : ι → RAMEnv} {n M : ℕ}
    {D : (Fin n → ZMod 2) → Fin M → ZMod 2} {Tdec eps : ℝ}
    (hHalt : ∀ (i : ι) (y : Fin M → ZMod 2), ∃ s' : RAMState,
      HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (env i) Tdec
        (decoderStart (env i).W y []) s')
    (hCorr : TopDecCorrectsEnv Sinit Srow Sdec Sassem Sres Scr env D Tdec) (heps : 0 ≤ eps)
    (x : Fin n → ZMod 2) :
    1 - eps ≤ prU (fun i : ι => ∃ s' : RAMState,
      HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (env i) Tdec
        (decoderStart (env i).W (D x) []) s' ∧ OutputsSupport s' x) := by
  have hle : prU (fun _ : ι => True) ≤
      prU (fun i : ι => ∃ s' : RAMState,
        HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (env i) Tdec
          (decoderStart (env i).W (D x) []) s' ∧ OutputsSupport s' x) := by
    apply prU_mono
    intro i _
    obtain ⟨s', hs'⟩ := hHalt i (D x)
    exact ⟨s', hs', hCorr i x s' hs'⟩
  rw [prU_true] at hle
  linarith

/-! ## 5. The stage-by-stage accounting (conjunct 8)

§9.2's decoder is `topDecStmt = Sinit → loop Srow → loop Sdec → Sassem → Sres → Scr`
(`Def_…_Top65Dec`).  `TopDecRuns` records one `StageRun` per block, and `haltsWithin_topDec_of_runs`
composes them into conjunct 7.  The **postconditions** of those `StageRun`s are `fun _ => True` for
the four middle blocks, so `TopDecRuns` carries no decoded data and cannot yield correctness.

| stage | what the platform proves | what is still missing |
|---|---|---|
| `Sinit` | nothing | the `Stmt` itself: no prologue is defined anywhere; `det`'s header format is a convention (§13.7 (P)), not a definition |
| `row` (`d` × `proposition_2_1`) | 2.1's per-call contract (`∃ W det, … HaltsWithin progDec (detEnv W det) … ∧ (s'.regs 2 ≠ 0 → ∃ x, … OutputsSupport s' x)`), and `haltsWithin_rowLoop_shape` turns a per-row `Sem` into `(Kr+5) d (lg n)^{pr+1}` | 2.1's `progDec` is exported as a bare `Program`, not as a base-relative `Stmt`; the loop body's address arithmetic and the per-row `det` base are not defined |
| `col` (`ℓ` × `theorem_5_1`) | 5.1's `OutputsSupport` conjunct, and `haltsWithin_colLoop_shape` turns a per-child `Sem` into `(7C²e⁶+3) d exp((7C²e⁶+3)(lg lg n)²)` | exactly `Up5Export.down` (§1) — and, even with it, the dispatcher that computes each block's payload base `β_s` and `det` base `δ_s` from `det` does not exist, so the loop-head family `s j` of `stageRun_counted_loop` cannot be built |
| `Sassem` | `RowScheme.assembled`'s definition only | the assembly program and its contract (`RowScheme.assembled` is a *function*, not code) |
| `Sres` | nothing | the residual-syndrome program (`a + CR x̂`); `CRFamily.sketch` is a function |
| `Scr` (`proposition_2_3`) | 2.3's `OutputsSupport` conjunct and `cr_time_shape` (its time inside 6.5's budget) | 2.3's decoder as a base-relative `Stmt` (a second `down`-shaped export, from Proposition 2.3) |

So: **no stage of the pipeline closes unconditionally today.**  Three of them (`row`, `col`, `cr`)
would close from a `down`-shaped export of *their own* sub-decoder — `Up5Export.down` is the `col`
one, Proposition 2.1's decoder needs the same shape for `row`, and Proposition 2.3's for `cr` — plus,
for the two loops, the dispatcher's per-iteration address arithmetic (`β_s`, `δ_s` read out of
`det`), which is not defined anywhere either.  The other three (`init`, `as`, `res`) close from
nothing at all, because their `Stmt`s are not defined: §13.7 (P) fixes `det`'s header *by convention*
and `RowScheme.assembled` / `CRFamily.sketch` are functions, not code.

What is *no longer* missing is the abstract law: `decode_of_valid_bounds` (§3) gives
`Node.decode CR T r (Node.sketch CR T r x) J = some x` from `T.WF`, `AllBounds` at one seed and
`Valid` at the root — i.e. the recovery law 6.5's conjunct 8 needs at the *abstract* level, for one
seed, with no probability.  The whole remaining distance is the machine bridge, and §4 shows that
bridge loses nothing: one worst-case correctness statement closes conjunct 8 outright. -/

end LinearSetReconciliation327.Main


