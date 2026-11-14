-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelNormalForm
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelNormalForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:49.743224+00:00
-- url     : https://prove2.me/theorems/6d39c1d2-2daf-4cfd-b28a-08c69fc625b2
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelNormalForm — The existing single-machine tidy normalization construction
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelNormalForm` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Machine declarations are moved from their original module without changing programs or resource
--   formulas. Higher computability-calculus theorems remain in the original facade.
--
--   **Contents.** The module is published as a whole: 20 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelNormalForm`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/KernelNormalForm.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (coordinate with crei on #611)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ClearShadowed
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapes
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindInput
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs
public import Definitions.Def_Cslib_254e30e_Foundations_Data_Fin_Tuple
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fin.Tuple.Embedding
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapesView
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelNormalForm` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # The existing single-machine tidy normalization construction

Machine declarations are moved from their original module without changing programs or resource
formulas. Higher computability-calculus theorems remain in the original facade.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*} [DecidableEq Symbol] {input : List Symbol} {m₀ m₁ : Symbol}

/-! ### Clearing a work tape and its shadow -/

/-- The embedding of work tape `i` and its shadow `k + i`. -/
def pairEmb (i : Fin k) : Fin 2 ↪ Fin (k + k) :=
  Function.Embedding.embFinTwo (Fin.castAdd_ne_natAdd i i)

@[simp] theorem pairEmb_zero (i : Fin k) : pairEmb i 0 = Fin.castAdd k i := rfl

/-- The shadow of work tape `i` is tape `k + i`, written `i.addNat k` in simp normal form. -/
@[simp] theorem pairEmb_one (i : Fin k) : pairEmb i 1 = i.addNat k :=
  Fin.natAdd_eq_addNat k i

/-- The tapes of the pair `i` are work tape `i` and its shadow. -/
theorem pairIdx_eq_iff {j : Fin (k + k)} {i : Fin k} :
    pairIdx j = i ↔ j = Fin.castAdd k i ∨ j = i.addNat k := by
  refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
  · simp only [pairIdx_castAdd, Fin.castAdd_inj, ← Fin.natAdd_eq_addNat, Fin.castAdd_ne_natAdd,
      or_false]
  · simp only [pairIdx_natAdd, ← Fin.natAdd_eq_addNat, Fin.natAdd_inj,
      (Fin.castAdd_ne_natAdd _ _).symm, false_or]

/-- Tape `j` is a tape of the pair `i` exactly when it is work tape `i` or its shadow. -/
theorem partialInv_pairEmb (i : Fin k) (j : Fin (k + k)) :
    partialInv (pairEmb i) j =
      if j = Fin.castAdd k i then some 0 else if j = i.addNat k then some 1 else none := by
  split_ifs with h₀ h₁
  · exact h₀ ▸ partialInv_embed (pairEmb i) 0
  · exact h₁ ▸ pairEmb_one i ▸ partialInv_embed (pairEmb i) 1
  · refine partialInv_eq_none _ ?_
    rintro ⟨a, rfl⟩
    fin_cases a <;> simp_all [pairEmb_one]

variable {σ σ' : Type*}

/-- Work tape `i` of `C` and its shadow `k + i` are ready to be cleared: the heads of both are on
cell `c - a`, the shadow marks cells `V` that together with `c - a` form the interval `[-a, b]`,
and the work tape is blank outside it. -/
structure PairReady (m₀ m₁ : Symbol) (C : Cfg (k + k) Symbol σ input) (i : Fin k) (a b c : ℕ)
    (V : Finset ℤ) : Prop where
  /-- The head of the work tape is on cell `c - a`. -/
  pos_castAdd : C.workTapePos (Fin.castAdd k i) = c - a
  /-- The head of the shadow is on cell `c - a`. -/
  pos_natAdd : C.workTapePos (Fin.natAdd k i) = c - a
  /-- The marked cells and the cell under the heads form the interval `[-a, b]`. -/
  insert_eq : insert ((c : ℤ) - a) V = Finset.Icc (-(a : ℤ)) b
  /-- The shadow marks the cells `V`. -/
  shadow_eq : C.workTapes (Fin.natAdd k i) = shadowTape m₀ m₁ V
  /-- The work tape is blank outside `[-a, b]`. -/
  blank : ∀ y ∉ Finset.Icc (-(a : ℤ)) b, C.workTapes (Fin.castAdd k i) y = none

/-- `C`, halted, with the work tapes in `l` and their shadows blank and their heads on the start
cell. -/
def clearedCfg (l : List (Fin k)) (C : Cfg (k + k) Symbol σ input) :
    Cfg (k + k) Symbol σ' input :=
  ⟨none, C.inputPos, fun j => if pairIdx j ∈ l then fun _ => none else C.workTapes j,
    fun j => if pairIdx j ∈ l then 0 else C.workTapePos j, C.output⟩

omit [DecidableEq Symbol] in
@[simp] theorem clearedCfg_nil (C : Cfg (k + k) Symbol σ input) :
    clearedCfg (σ' := σ') [] C = C.withState none := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;>
    simp only [clearedCfg, List.not_mem_nil, ↓reduceIte, Cfg.withState]

omit [DecidableEq Symbol] in
theorem clearedCfg_cons {σ₁ : Type*} (i : Fin k) (l : List (Fin k))
    (C : Cfg (k + k) Symbol σ input) :
    clearedCfg (σ' := σ') (i :: l) C =
      clearedCfg (σ' := σ') l (clearedCfg (σ' := σ₁) [i] C) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;>
    simp only [clearedCfg, List.mem_cons] <;>
    by_cases hj : pairIdx j = i <;> by_cases hj' : pairIdx j ∈ l <;> simp [hj, hj']

omit [DecidableEq Symbol] in
@[simp] theorem Sequential.rightCfg_clearedCfg {State₀ State₁ : Type*} (l : List (Fin k))
    (C : Cfg (k + k) Symbol σ input) :
    Sequential.rightCfg (State₀ := State₀) (clearedCfg (σ' := State₁) l C) =
      clearedCfg (σ' := State₀ ⊕ State₁) l C := rfl

omit [DecidableEq Symbol] in
/-- Clearing tapes `l` preserves `PairReady` on any tape `i ∉ l`. -/
theorem PairReady.clearedCfg {C : Cfg (k + k) Symbol σ input} {i : Fin k} {a b c : ℕ}
    {V : Finset ℤ} {l : List (Fin k)} (h : PairReady m₀ m₁ C i a b c V) (hil : i ∉ l) :
    PairReady m₀ m₁ (Turing.MultiTapeTM.clearedCfg (σ' := σ') l C) i a b c V where
  pos_castAdd := by simp [Turing.MultiTapeTM.clearedCfg, hil, h.pos_castAdd]
  pos_natAdd := by simpa [Turing.MultiTapeTM.clearedCfg, hil] using h.pos_natAdd
  insert_eq := h.insert_eq
  shadow_eq := by simpa [Turing.MultiTapeTM.clearedCfg, hil] using h.shadow_eq
  blank y hy := by simp [Turing.MultiTapeTM.clearedCfg, hil, h.blank y hy]

/-- **Clearing one work tape and its shadow** inside a machine with `k + k` work tapes. -/
theorem runFrom_clearShadowed_pairEmb (hm : m₀ ≠ m₁) {C : Cfg (k + k) Symbol σ input} {i : Fin k}
    {a b c : ℕ} {V : Finset ℤ} (h : PairReady m₀ m₁ C i a b c V) :
    ((clearShadowed m₀ m₁).extendTapes (pairEmb i)).runFrom (C.withState (some .start))
        (a + 2 * b + c + 5) = clearedCfg [i] C := by
  have hview : viewCfg (pairEmb i) (C.withState (some .start)) =
      ClearShadowed.cfg (some .start) C.inputPos (C.workTapes (Fin.castAdd k i))
        (shadowTape m₀ m₁ V) (c - a) C.output := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;> fin_cases j
    · rfl
    · exact h.shadow_eq
    · exact h.pos_castAdd
    · exact h.pos_natAdd
  rw [runFrom_extendTapes, hview, runFrom_clearShadowed hm h.insert_eq h.blank]
  have hne : i.addNat k ≠ Fin.castAdd k i := by
    rw [← Fin.natAdd_eq_addNat]
    exact (Fin.castAdd_ne_natAdd i i).symm
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;>
    simp only [embed, partialInv_pairEmb, clearedCfg, List.mem_singleton, Cfg.withState,
      pairIdx_eq_iff] <;>
    by_cases h₀ : j = Fin.castAdd k i <;> by_cases h₁ : j = i.addNat k <;>
    simp [h₀, h₁, hne]

/-- The control states of `clearList` for a list of length `n`. -/
def ClearListState : ℕ → Type
  | 0 => Unit
  | n + 1 => ClearShadowedState ⊕ ClearListState n

instance instFiniteClearListState : (n : ℕ) → Finite (ClearListState n)
  | 0 => inferInstanceAs (Finite Unit)
  | n + 1 =>
    haveI := instFiniteClearListState n
    inferInstanceAs (Finite (ClearShadowedState ⊕ ClearListState n))

variable (m₀ m₁) in
/-- Clear the work tapes in `l` along their shadows, one after the other. -/
noncomputable def clearList :
    (l : List (Fin k)) → MultiTapeTM (k + k) Symbol (ClearListState l.length)
  | [] => nop (k + k) Symbol
  | i :: l => ((clearShadowed m₀ m₁).extendTapes (pairEmb i)).seq (clearList l)

/-- **Clearing a list of work tapes** with their shadows, each ready to be cleared: a run path of
`clearList m₀ m₁ l` to the configuration with these tapes cleared. -/
theorem exists_runPath_clearList (hm : m₀ ≠ m₁) (l : List (Fin k)) (hl : l.Nodup)
    (a b c : Fin k → ℕ) (V : Fin k → Finset ℤ) (C : Cfg (k + k) Symbol σ input)
    (hC : ∀ i ∈ l, PairReady m₀ m₁ C i (a i) (b i) (c i) (V i)) :
    ∃ p : (clearList m₀ m₁ l).RunPath input,
      p.head = C.withState (some (clearList m₀ m₁ l).q₀) ∧ p.last = clearedCfg l C ∧
        p.time ≤ (l.map fun i => a i + 2 * b i + c i + 5).sum + 1 := by
  induction l generalizing C σ with
  | nil =>
    exact ⟨.ofDeterministic _ _ 1, rfl,
      (runFrom_nop_withState C).trans (clearedCfg_nil C).symm, le_rfl⟩
  | cons i l ih =>
    obtain ⟨hil, hl⟩ := List.nodup_cons.1 hl
    have hmid := runFrom_clearShadowed_pairEmb hm (hC i List.mem_cons_self)
    obtain ⟨p₁, hh₁, hl₁, ht₁⟩ := ih hl (clearedCfg (σ' := σ) [i] C) fun j hj =>
      (hC j (List.mem_cons_of_mem _ hj)).clearedCfg (by simp [ne_of_mem_of_not_mem hj hil])
    -- clear tape `i`, then the others
    obtain ⟨p, hh, hl', ht, -⟩ := exists_runPath_seq
      (p₀ := .ofDeterministic ((clearShadowed m₀ m₁).extendTapes (pairEmb i))
        (C.withState (some .start)) (a i + 2 * b i + c i + 5)) (p₁ := p₁)
      (by rw [MultiTapeNTM.RunPath.last_ofDeterministic, hmid]; rfl)
      (by rw [hh₁, MultiTapeNTM.RunPath.last_ofDeterministic, hmid]; rfl) (by rw [hl₁]; rfl)
    refine ⟨p, hh, hl'.trans ?_, ?_⟩
    · rw [hl₁, Sequential.rightCfg_clearedCfg]
      exact (clearedCfg_cons i l C).symm
    · change p.length ≤ a i + 2 * b i + c i + 5 + p₁.length at ht
      change p₁.length ≤ _ at ht₁
      change p.length ≤ _
      rw [List.map_cons, List.sum_cons]
      omega

/-! ### The tidy normal form -/

variable {State : Type*}

variable (m₀ m₁) in
/-- The tidy normal form of `tm`: run `tm` with shadowed work tapes, clear every work tape along
its shadow, and rewind the input head. The symbols `m₀` and `m₁` mark the shadows. -/
noncomputable def tidy (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + k) Symbol
      ((Option State ⊕ ClearListState (List.finRange k).length) ⊕ RewindState) :=
  ((shadow m₀ m₁ tm).seq (clearList m₀ m₁ (List.finRange k))).seq
    ((rewindInput Symbol).extendTapes (noTapes (k + k)))

variable {tm : MultiTapeTM k Symbol State}

omit [DecidableEq Symbol] in
/-- The configuration in which the clearing phase ends: halted, with blank work tapes and every
head on its start cell. -/
private theorem clearedCfg_finRange (C : Cfg (k + k) Symbol σ input) :
    clearedCfg (σ' := σ') (List.finRange k) C = ⟨none, C.inputPos, fun _ _ => none, fun _ => 0,
      C.output⟩ := by
  simp [clearedCfg]

/-- **The run of the tidy normal form.** If `tm` first halts at step `u`, having used `S` cells,
then `tidy m₀ m₁ tm` has a run path to the halted configuration with blank work tapes, every head on
its start cell and the output of `tm`, taking at most `2 u + 3 S + 2 k + 4` steps and visiting at
most `2 S + 2 k (3 S + 2 k + 3)` cells. -/
theorem exists_runPath_tidy (hm : m₀ ≠ m₁) {u : ℕ}
    (hlt : ∀ m < u, ¬(tm.runFrom (tm.initCfg input) m).Halted)
    (hu : (tm.runFrom (tm.initCfg input) u).Halted) :
    ∃ p : (tidy m₀ m₁ tm).RunPath input, p.head = (tidy m₀ m₁ tm).initCfg input ∧
      p.last = wordsCfg input none (fun _ => []) (tm.runFrom (tm.initCfg input) u).output ∧
      p.time ≤ 2 * u +
        3 * (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) u).space + 2 * k + 4 ∧
      p.space ≤ 2 * (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) u).space +
        2 * k * (3 * (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) u).space + 2 * k +
          3) := by
  set c₀ := tm.initCfg input
  set D := tm.runFrom c₀ u
  set S := (MultiTapeNTM.RunPath.ofDeterministic tm c₀ u).space
  set C₁ := Shadow.cfg m₀ m₁ D (Shadow.visited tm c₀ u)
  -- the visited cells of each tape form an interval `[L i, R i]` around the start cell
  choose L R hLR using fun i => exists_visitedByTapeHead_eq_Icc (tm := tm) c₀ u i
  have h0 : ∀ i, (0 : ℤ) ∈ Finset.Icc (L i) (R i) := fun i =>
    hLR i ▸ MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic.2 ⟨0, by omega, rfl⟩
  have hp : ∀ i, D.workTapePos i ∈ Finset.Icc (L i) (R i) := fun i =>
    hLR i ▸ MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic.2 ⟨u, le_rfl, rfl⟩
  simp only [Finset.mem_Icc] at h0 hp
  set a : Fin k → ℕ := fun i => (-L i).toNat
  set b : Fin k → ℕ := fun i => (R i).toNat
  set c : Fin k → ℕ := fun i => (D.workTapePos i - L i).toNat
  have ha : ∀ i, (a i : ℤ) = -L i := fun i => Int.toNat_of_nonneg (by have := h0 i; omega)
  have hb : ∀ i, (b i : ℤ) = R i := fun i => Int.toNat_of_nonneg (h0 i).2
  have hc : ∀ i, (c i : ℤ) = D.workTapePos i - L i := fun i =>
    Int.toNat_of_nonneg (by have := hp i; omega)
  have hready : ∀ i ∈ List.finRange k,
      PairReady m₀ m₁ C₁ i (a i) (b i) (c i) (Shadow.visited tm c₀ u i) := fun i _ => by
    have hIcc : Finset.Icc (-(a i : ℤ)) (b i) = Finset.Icc (L i) (R i) := by rw [ha, hb, neg_neg]
    refine ⟨?_, ?_, ?_, ?_, fun y hy => ?_⟩
    · simp only [C₁, Shadow.cfg, Fin.append_left, ha, hc]
      ring
    · simp only [C₁, Shadow.cfg, Fin.append_right, ha, hc]
      ring
    · rw [hIcc, ← hLR, Shadow.visitedByTapeHead_eq_insert, ha, hc]
      congr 1
      ring
    · simp only [C₁, Shadow.cfg, Fin.append_right]
    · rw [hIcc, ← hLR] at hy
      simp only [C₁, Shadow.cfg, Fin.append_left]
      exact workTapes_runFrom_eq_of_notMem_visitedByTapeHead hy
  -- the three phases: shadowing, clearing, rewinding the input head
  have hA : (shadow m₀ m₁ tm).runFrom ((shadow m₀ m₁ tm).initCfg input) (u + 1) = C₁ :=
    runFrom_shadow hlt
  have hC₁ : C₁.Halted := by
    simp only [Cfg.Halted, C₁, Shadow.cfg, Option.map_eq_none_iff]
    exact hu
  obtain ⟨pB, hhB, hlB, htB⟩ := exists_runPath_clearList hm (List.finRange k)
    (List.nodup_finRange k) a b c (Shadow.visited tm c₀ u) C₁ hready
  rw [clearedCfg_finRange] at hlB
  obtain ⟨pAB, hhAB, hlAB, htAB, hsAB⟩ := exists_runPath_seq_space_le
    (p₀ := .ofDeterministic (shadow m₀ m₁ tm) ((shadow m₀ m₁ tm).initCfg input) (u + 1))
    (p₁ := pB) (by rw [MultiTapeNTM.RunPath.last_ofDeterministic, hA]; exact hC₁)
    (by rw [hhB, MultiTapeNTM.RunPath.last_ofDeterministic, hA]) (by rw [hlB])
  set R₀ : Cfg (k + k) Symbol RewindState input :=
    (Sequential.rightCfg (State₀ := Option State)
      (⟨none, C₁.inputPos, fun _ _ => none, fun _ => 0, C₁.output⟩ :
        Cfg (k + k) Symbol (ClearListState (List.finRange k).length) input)).withState
      (some ((rewindInput Symbol).extendTapes (noTapes (k + k))).q₀)
  have hR : ((rewindInput Symbol).extendTapes (noTapes (k + k))).runFrom R₀
      (C₁.inputPos.val - 1 + 2) = ⟨none, 1, fun _ _ => none, fun _ => 0, C₁.output⟩ := by
    rw [runFrom_noTapes]
    simp only [R₀, noTapesCfg, Cfg.withState, Sequential.rightCfg, Cfg.mapState, extendTapes_q₀,
      runFrom_rewindInput]
  obtain ⟨p, hh, hl, ht, hs⟩ := exists_runPath_seq_space_le (p₀ := pAB)
    (p₁ := .ofDeterministic ((rewindInput Symbol).extendTapes (noTapes (k + k))) R₀
      (C₁.inputPos.val - 1 + 2))
    (by rw [hlAB, hlB]; rfl) (by rw [hlAB, hlB]; rfl)
    (by rw [MultiTapeNTM.RunPath.last_ofDeterministic, hR])
  -- the time bound
  set Tc := ((List.finRange k).map fun i => a i + 2 * b i + c i + 5).sum + 1
  have hcard (i : Fin k) :
      a i + b i + 1 = (MultiTapeNTM.RunPath.ofDeterministic tm c₀ u).spaceUsedByTape i := by
    rw [MultiTapeNTM.RunPath.spaceUsedByTape, hLR, Int.card_Icc]
    have := ha i
    have := hb i
    omega
  have hTc : Tc ≤ 3 * S + 2 * k + 1 := by
    have hsum : ((List.finRange k).map fun i => a i + 2 * b i + c i + 5).sum ≤
        ∑ i, (3 * (MultiTapeNTM.RunPath.ofDeterministic tm c₀ u).spaceUsedByTape i + 2) := by
      rw [← Fin.sum_univ_def]
      refine Finset.sum_le_sum fun i _ => ?_
      have := hcard i
      have := hp i
      have := ha i
      have := hb i
      have := hc i
      omega
    have : ∑ i, (3 * (MultiTapeNTM.RunPath.ofDeterministic tm c₀ u).spaceUsedByTape i + 2) =
        3 * S + 2 * k := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [S, MultiTapeNTM.RunPath.space, mul_comm]
    omega
  have hTr : C₁.inputPos.val - 1 + 2 ≤ u + 2 := by
    have h₁ : (D.inputPos : ℕ) ≤ (c₀.inputPos : ℕ) + u := inputPos_runFrom_le tm c₀ u
    have h₂ : (c₀.inputPos : ℕ) = 1 := rfl
    change (D.inputPos : ℕ) - 1 + 2 ≤ u + 2
    omega
  change pB.length ≤ Tc at htB
  refine ⟨p, hh.trans (by rw [hhAB]; rfl), hl.trans ?_, ?_, ?_⟩
  · rw [MultiTapeNTM.RunPath.last_ofDeterministic, hR]
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i
    exact tapeOfList_nil.symm
  · change p.length ≤ pAB.length + (C₁.inputPos.val - 1 + 2) at ht
    change pAB.length ≤ u + 1 + pB.length at htAB
    change p.length ≤ _
    omega
  · -- the shadowing phase visits `2 S` cells, the clearing phase at most one new cell per tape and
    -- step, and the rewinding phase one cell per tape
    refine hs.trans ?_
    have hsA : (MultiTapeNTM.RunPath.ofDeterministic (shadow m₀ m₁ tm)
        ((shadow m₀ m₁ tm).initCfg input) (u + 1)).space = 2 * S := space_shadow hlt
    have hsB : pB.space ≤ (k + k) * pB.length + (k + k) :=
      pB.space_le_mul_time_add_one.trans_eq (Nat.mul_add_one _ _)
    have hsR : (MultiTapeNTM.RunPath.ofDeterministic
        ((rewindInput Symbol).extendTapes (noTapes (k + k))) R₀ (C₁.inputPos.val - 1 + 2)).space ≤
        k + k :=
      space_noTapes_le _ _ _
    have h₂ : (k + k) * pB.length ≤ 2 * k * (3 * S + 2 * k + 1) :=
      (Nat.mul_le_mul_left _ (htB.trans hTc)).trans_eq (by ring)
    have h₃ : 2 * k * (3 * S + 2 * k + 3) = 2 * k * (3 * S + 2 * k + 1) + 4 * k := by ring
    omega

/-- **The tidy normal form.** What `tm` computes within `t` steps and `s` cells,
`tidy m₀ m₁ tm` computes tidily within `2 t + 3 s + 2 k + 4` steps and `2 s + 2 k (3 s + 2 k + 3)`
cells, for any two distinct marks `m₀` and `m₁`. -/
theorem ComputesInTimeAndSpace.computesTidily_tidy (hm : m₀ ≠ m₁) {output : List Symbol}
    {t s : ℕ} (h : tm.ComputesInTimeAndSpace input output t s) :
    (tidy m₀ m₁ tm).ComputesTidilyInTimeAndSpace input output (2 * t + 3 * s + 2 * k + 4)
      (2 * s + 2 * k * (3 * s + 2 * k + 3)) := by
  obtain ⟨⟨u', hu', hout⟩, ht, hs⟩ := h
  -- the first step at which `tm` has halted
  obtain ⟨u, -, hu, hlt⟩ := exists_haltsAt hu'
  have hut : u ≤ t := Nat.le_of_not_lt fun h => hlt t h (runsInTime_iff_halted.mp ht)
  have hout' : (tm.runFrom (tm.initCfg input) u).output = output := by
    rw [← hout, runFrom_eq_of_halt _ _ (Nat.le_of_not_lt fun h => hlt u' h hu') hu]
  have hS := space_le_of_runsInSpace hs u
  obtain ⟨p, hhead, hlast, htime, hspace⟩ := exists_runPath_tidy hm hlt hu
  rw [computesTidily_iff]
  refine ⟨p, hhead.trans (initCfg_eq_wordsCfg input), hlast.trans (by rw [hout']), by omega,
    hspace.trans (Nat.add_le_add (Nat.mul_le_mul_left 2 hS) (Nat.mul_le_mul_left _ ?_))⟩
  omega

end Turing.MultiTapeTM


