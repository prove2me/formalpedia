-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_ColWrap20261122
-- name    : LinearSetReconciliation327_Main_ColWrap20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T08:32:33.170784+00:00
-- url     : https://prove2.me/theorems/dc53b0db-eff2-48f3-a0c2-f3c3c2a37706
-- title:
--   The column counter wrapper `save r1,r2; setup delta,beta_j; Sdec; restore r1,r2`
-- statement:
--   `DownBlkSemAtW` constrains memory only, while the column loop's counter is `r1` and its bound `r2` and Theorem 5.1's decoder reads both; so the real child cannot be hosted by `topLoop Sdec` directly.  This bundle supplies the wrapper `save r1,r2 -> r14 := delta, r15 := beta0 + r1*ms -> Sdec -> restore r1,r2`, with the two save cells just outside the child's workspace, and proves the two straight-line blocks exactly (`cwPre_sem`, `cwPost_sem`), the wrapper's run (`cwRun`, cost `9 + Tdec + 4`, payloads below `gamma` framed), its run-form counter contract (`colCounter_wrap`) and every child payload's preservation.  Axiom-clean; local `cpl` 8 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's column stage and Theorem 5.1's decoder (the two-window `DownBlkSemAtW` contract).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_ColWire2aPart220261122

/-!
# `ColWrap` — the per-child `save / setup / restore` wrapper

`DownBlkSemAtW` constrains **memory only** and never registers, while the column loop's counter is
`r1` and its bound `r2`; the real 5.1 decoder *reads* `r1`/`r2`.  `topLoop Sdec` therefore cannot
host the real child directly.

This bundle supplies the wrapper

`save r1,r2  →  setup r14 := δ, r15 := β_j  →  Sdec  →  restore r1,r2`

with `β_j = β0 + j·ms` computed from the counter `r1`, its two save cells at `γ + ws` and
`γ + ws + 1` (outside the child's workspace), and proves the two straight-line blocks and the
wrapper's run.

**One caveat, isolated.**  `DownBlkSemAtW`'s `I`-frame is
`∀ n mem, I n mem → ∀ a, a < γ ∨ γ + ws ≤ a → mem a = s.mem a`, a range that contains the
wrapper's two save cells.  The wrapper writes them, so the caller's frame for `s` does not transfer
to the child's entry `s1`.  The theorems below therefore take the frame on the two-word-larger
exclusion `a < γ ∨ γ + ws + 2 ≤ a` together with the pinning of the two scratch cells;
`cwRun` is otherwise complete.  (Equivalently: the column invariant must not constrain the
wrapper's private scratch words.)
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace W65C

open RSD

/-! ## 1. The wrapper program -/

/-- Save `r1, r2` at `γ + ws` and `γ + ws + 1`, then set `r14 := δ` and
`r15 := β0 + r1 · ms` (the counter `r1` is `j`).  Nine instructions. -/
def cwPre (δ β0 ms γ ws : ℕ) : List Instr :=
  [ iImm r4 (γ + ws), iSt r4 r1,
    iImm r4 (γ + ws + 1), iSt r4 r2,
    iImm r14 δ,
    iImm r3 ms, iMul r15 r1 r3,
    iImm r3 β0, iAdd r15 r15 r3 ]

/-- Restore `r1, r2` from the two save cells.  Four instructions. -/
def cwPost (γ ws : ℕ) : List Instr :=
  [ iImm r4 (γ + ws), iLd r1 r4,
    iImm r4 (γ + ws + 1), iLd r2 r4 ]

/-- The per-child wrapper. -/
def cwWrap (Sdec : Stmt) (δ β0 ms γ ws : ℕ) : Stmt :=
  .seq (.code (cwPre δ β0 ms γ ws)) (.seq Sdec (.code (cwPost γ ws)))

lemma cwPre_len (δ β0 ms γ ws : ℕ) : (cwPre δ β0 ms γ ws).length = 9 := rfl

lemma cwPost_len (γ ws : ℕ) : (cwPost γ ws).length = 4 := rfl

lemma cwWrap_len (Sdec : Stmt) (δ β0 ms γ ws : ℕ) :
    (cwWrap Sdec δ β0 ms γ ws).len = 9 + Sdec.len + 4 := by
  simp [cwWrap, cwPre_len, cwPost_len, Stmt.len]
  omega

lemma cwPre_noBranch (δ β0 ms γ ws : ℕ) : NoBranch (cwPre δ β0 ms γ ws) := by
  simp [cwPre, NoBranch, Instr.NoBranchI]

lemma cwPost_noBranch (γ ws : ℕ) : NoBranch (cwPost γ ws) := by
  simp [cwPost, NoBranch, Instr.NoBranchI]

/-! ## 2. The two straight-line blocks -/

/-- **The wrapper's prologue.**  From any state with `r1 = j`, `r2 = n` at `base`, nine steps take
it to `base + 9` with `r14 = δ`, `r15 = β0 + j·ms`, the two save cells set, `r1`/`r2` untouched,
and the rest of memory framed. -/
theorem cwPre_sem {P : Program} {E : RAMEnv} {base : ℕ} {s : RAMState}
    {δ β0 ms γ ws j n : ℕ}
    (hAt : At P base (cwPre δ β0 ms γ ws)) (hpc : s.pc = base)
    (hW : 1 < 2 ^ E.W) (hj : j < 2 ^ E.W) (hn : n < 2 ^ E.W) (hδ : δ < 2 ^ E.W)
    (hms : ms < 2 ^ E.W) (hβ : β0 + j * ms < 2 ^ E.W) (hcell1 : γ + ws + 1 < 2 ^ E.W)
    (h1 : s.regs 1 = j) (h2 : s.regs 2 = n) :
    Sem P E base (base + 9) s (fun k s' => k = 9 ∧ s'.pc = base + 9 ∧
      s'.regs 1 = j ∧ s'.regs 2 = n ∧ s'.regs 14 = δ ∧ s'.regs 15 = β0 + j * ms ∧
      s'.mem (γ + ws) = j ∧ s'.mem (γ + ws + 1) = n ∧
      (∀ q, q ≠ γ + ws → q ≠ γ + ws + 1 → s'.mem q = s.mem q)) := by
  refine Sem.mono (Sem.block P E base (cwPre δ β0 ms γ ws) s hAt
    (cwPre_noBranch δ β0 ms γ ws) hpc) ?_
  rintro k s' ⟨hk, rfl⟩
  have h1' : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hms' : ms % 2 ^ E.W = ms := Nat.mod_eq_of_lt hms
  have hδ' : δ % 2 ^ E.W = δ := Nat.mod_eq_of_lt hδ
  have hj' : j % 2 ^ E.W = j := Nat.mod_eq_of_lt hj
  have hn' : n % 2 ^ E.W = n := Nat.mod_eq_of_lt hn
  have hβ' : (j * ms + β0) % 2 ^ E.W = β0 + j * ms := by
    rw [Nat.add_comm, Nat.mod_eq_of_lt hβ]
  have hc1 : (γ + ws) % 2 ^ E.W = γ + ws := Nat.mod_eq_of_lt (by omega)
  have hc2 : (γ + ws + 1) % 2 ^ E.W = γ + ws + 1 := Nat.mod_eq_of_lt hcell1
  refine ⟨hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [cwPre, runBlock_cons, runBlock_nil, execInstr, hpc]
  · simp [cwPre, runBlock_cons, runBlock_nil, execInstr, h1, hj', hc1, hc2]
  · simp [cwPre, runBlock_cons, runBlock_nil, execInstr, h2, hn', hc1, hc2]
  · simp [cwPre, runBlock_cons, runBlock_nil, execInstr, hδ']
  · simp [cwPre, runBlock_cons, runBlock_nil, execInstr, hms', h1, hj', hβ', hδ']
  · simp [cwPre, runBlock_cons, runBlock_nil, execInstr, h1, h2, hj', hn', hc1, hc2]
  · simp [cwPre, runBlock_cons, runBlock_nil, execInstr, h1, h2, hj', hn', hc1, hc2]
  · intro q hq1 hq2
    simp [cwPre, runBlock_cons, runBlock_nil, execInstr, Function.update_of_ne, hc1, hc2, hq1, hq2]

/-- **The wrapper's epilogue.**  From a state with the two save cells holding `j` and `n`, four
steps restore `r1 = j`, `r2 = n` and touch no memory. -/
theorem cwPost_sem {P : Program} {E : RAMEnv} {base : ℕ} {s : RAMState} {γ ws j n : ℕ}
    (hAt : At P base (cwPost γ ws)) (hpc : s.pc = base)
    (hW : 1 < 2 ^ E.W) (hj : j < 2 ^ E.W) (hn : n < 2 ^ E.W) (hcell1 : γ + ws + 1 < 2 ^ E.W)
    (h1 : s.mem (γ + ws) = j) (h2 : s.mem (γ + ws + 1) = n) :
    Sem P E base (base + 4) s (fun k s' => k = 4 ∧ s'.pc = base + 4 ∧
      s'.regs 1 = j ∧ s'.regs 2 = n ∧ s'.mem = s.mem) := by
  refine Sem.mono (Sem.block P E base (cwPost γ ws) s hAt
    (cwPost_noBranch γ ws) hpc) ?_
  rintro k s' ⟨hk, rfl⟩
  have hc1 : (γ + ws) % 2 ^ E.W = γ + ws := Nat.mod_eq_of_lt (by omega)
  have hc2 : (γ + ws + 1) % 2 ^ E.W = γ + ws + 1 := Nat.mod_eq_of_lt hcell1
  refine ⟨hk, ?_, ?_, ?_, ?_⟩
  · simp [cwPost, runBlock_cons, runBlock_nil, execInstr, hc1, hc2, hpc]
  · simp [cwPost, runBlock_cons, runBlock_nil, execInstr, hc1, hc2, h1,
      Nat.mod_eq_of_lt hj]
  · simp [cwPost, runBlock_cons, runBlock_nil, execInstr, hc1, hc2, h2,
      Nat.mod_eq_of_lt hn]
  · simp [cwPost, runBlock_cons, runBlock_nil, execInstr, hc1, hc2]

/-! ## 3. The wrapper's three `At` blocks -/

/-- Splitting the wrapper's compiled code into its three blocks. -/
theorem cwAt_parts {P : Program} {base : ℕ} {Sdec : Stmt} {δ β0 ms γ ws : ℕ}
    (hAt : At P base ((cwWrap Sdec δ β0 ms γ ws).compile base)) :
    At P base (cwPre δ β0 ms γ ws) ∧
      At P (base + 9) (Sdec.compile (base + 9)) ∧
      At P (base + 9 + Sdec.len) (cwPost γ ws) := by
  have hparts : At P base (cwPre δ β0 ms γ ws ++
      (Sdec.compile (base + 9) ++ cwPost γ ws)) := by
    simpa [cwWrap, Stmt.compile, Stmt.len, cwPre_len] using hAt
  obtain ⟨hPre, hRest⟩ := At.append.mp hparts
  obtain ⟨hChild, hPost⟩ := At.append.mp hRest
  refine ⟨hPre, ?_, ?_⟩
  · simpa [cwPre_len] using hChild
  · rw [Stmt.length_compile] at hPost
    rw [cwPre_len] at hPost
    simpa using hPost

/-! ## 4. The wrapper's run -/

/-- **The wrapper's run.**  From a loop head with `r1 = j`, `r2 = n` and the child's payload at
`β_j = β0 + j·ms`, the wrapper saves the two counters, sets `r14 = δ`, `r15 = β_j`, runs
`DownBlkSemAtW`'s child, and restores the counters: cost `9 + Tdec + 4`, exit at
`base + (cwWrap …).len`, `r1 = j`, `r2 = n`, and **every address below `γ`** unchanged.

The two frame hypotheses are the isolated caveat of the module header: `hIFrame` excludes the
wrapper's two scratch cells `γ+ws, γ+ws+1`, and `hIPin` says the invariant pins them.  With them,
`hIFrame**` below transfers the caller's frame to the child's entry state. -/
theorem cwRun {P : Program} {E : RAMEnv} {a : ℕ} {Tdec : ℝ} {Sdec : Stmt}
    {Bw ms ws N Ms : ℕ} {I : ℕ → (ℕ → ℕ) → Prop}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    {δ β0 γ : ℕ} {j n : ℕ} {s : RAMState}
    {header control hintMap resultMap listBase table count : ℕ}
    {y : Fin Ms → ZMod 2} {J : List ℕ}
    (hdown : DownBlkSemAtW Sdec E Tdec Bw ms ws I Hs)
    (hAt : At P a ((cwWrap Sdec δ β0 ms γ ws).compile a))
    (hW : 1 < 2 ^ E.W) (hell : n < 2 ^ E.W) (hj : j < n)
    (hpc : s.pc = a) (h1 : s.regs 1 = j) (h2 : s.regs 2 = n)
    (hfit : wordsOf E.W Ms ≤ ms) (hβtop : β0 + j * ms + ms ≤ 2 ^ E.W)
    (hβγ : β0 + j * ms + ms ≤ γ)
    (hws : ws ≤ 2 ^ E.W) (hγws : γ + ws ≤ 2 ^ E.W) (hcell1 : γ + ws + 1 < 2 ^ E.W)
    (hδ : δ + Bw ≤ 2 ^ E.W) (hδW : δ < 2 ^ E.W) (hmsW : ms < 2 ^ E.W)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (hmem : ∀ q < wordsOf E.W Ms, s.mem (β0 + j * ms + q) = packMem E.W y q)
    (hHint : γ ≤ hintMap) (hHintTop : hintMap + N < γ + ws)
    (hControl : γ ≤ control) (hControlTop : control + 4 ≤ γ + ws)
    (hList : γ ≤ listBase) (hListTop : listBase + N ≤ γ + ws)
    (hIFrame : ∀ n' mem, I n' mem → ∀ a', a' < γ ∨ γ + ws + 2 ≤ a' → mem a' = s.mem a')
    (hIPin : ∀ n' mem, I n' mem → mem (γ + ws) = j ∧ mem (γ + ws + 1) = n) :
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ 9 + Tdec + 4 ∧ (step P E)^[k] s = s' ∧
      s'.pc = a + (cwWrap Sdec δ β0 ms γ ws).len ∧ s'.regs 1 = j ∧ s'.regs 2 = n ∧
      (∀ q < γ, s'.mem q = s.mem q) := by
  obtain ⟨hAtPre, hAtChild, hAtPost⟩ := cwAt_parts (Sdec := Sdec) hAt
  have hβW : β0 + j * ms < 2 ^ E.W := by omega
  have hjW : j < 2 ^ E.W := by omega
  -- 1. the save/setup block
  obtain ⟨-, k1, s1, hrun1, hpc1, hq1⟩ :=
    cwPre_sem (P := P) (E := E) (base := a) (s := s)
      (δ := δ) (β0 := β0) (ms := ms) (γ := γ) (ws := ws) (j := j) (n := n)
      hAtPre hpc hW hjW hell hδW hmsW hβW hcell1 h1 h2
  obtain ⟨hk1', hpc1', hr1, hr2, hr14, hr15, hsave1, hsave2, hframe1⟩ := hq1
  -- 2. the child, with the two save cells handled by the frame hypotheses
  have hmem1 : ∀ q < wordsOf E.W Ms, s1.mem (β0 + j * ms + q) = packMem E.W y q := by
    intro q hq
    rw [hframe1 _ (by omega) (by omega)]
    exact hmem q hq
  have hIFrame1 : ∀ n' mem, I n' mem → ∀ a', a' < γ ∨ γ + ws ≤ a' → mem a' = s1.mem a' := by
    intro n' mem hI' a' ha'
    obtain ⟨hpin1, hpin2⟩ := hIPin n' mem hI'
    by_cases ha1 : a' = γ + ws
    · subst ha1
      rw [hpin1, hsave1]
    · by_cases ha2 : a' = γ + ws + 1
      · subst ha2
        rw [hpin2, hsave2]
      · have hlt : a' < γ ∨ γ + ws + 2 ≤ a' := by
          rcases ha' with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
        rw [hIFrame n' mem hI' a' hlt, hframe1 a' ha1 ha2]
  obtain ⟨kc, outc, hkc, hrunC, hpcC, hframeC, -⟩ :=
    hdown P (a + 9) δ (β0 + j * ms) γ hfit hβtop hws hγws
      header control hintMap resultMap listBase table count y J s1 hAtChild hpc1' hδ hdr
      hr14 hr15 hmem1 hHint hHintTop hControl hControlTop hList hListTop
      (Or.inl hβγ) hIFrame1
  -- 3. the restore block
  have hout1 : outc.mem (γ + ws) = j := by
    rw [hframeC (γ + ws) (Or.inr (le_refl _))]; exact hsave1
  have hout2 : outc.mem (γ + ws + 1) = n := by
    rw [hframeC (γ + ws + 1) (Or.inr (by omega))]; exact hsave2
  obtain ⟨-, k3, s3, hrun3, hpc3, hq3⟩ :=
    cwPost_sem (P := P) (E := E) (base := a + 9 + Sdec.len) (s := outc)
      (γ := γ) (ws := ws) (j := j) (n := n) hAtPost hpcC hW hjW hell hcell1 hout1 hout2
  obtain ⟨hk3', hpc3', hr3a, hr3b, hmem3⟩ := hq3
  -- 4. compose the three runs
  refine ⟨k1 + kc + k3, s3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1' : (k1 : ℝ) = 9 := by exact_mod_cast hk1'
    have h3' : (k3 : ℝ) = 4 := by exact_mod_cast hk3'
    push_cast
    nlinarith
  · rw [show k1 + kc + k3 = k3 + (kc + k1) from by omega]
    rw [Function.iterate_add_apply, Function.iterate_add_apply, hrun1, hrunC, hrun3]
  · rw [hpc3', cwWrap_len]
    omega
  · simpa [h1] using hr3a
  · simpa [h2] using hr3b
  · intro q hq
    rw [hmem3]
    rw [hframeC q (Or.inl hq)]
    exact hframe1 q (by omega) (by omega)

/-- **`ColCounter` for the wrapper, in the run form the loop consumes.**  The wrapper's actual run
restores `r1` and `r2`; this is the theorem that replaces the named hypothesis `ColCounter`. -/
theorem colCounter_wrap {P : Program} {E : RAMEnv} {a : ℕ} {Tdec : ℝ} {Sdec : Stmt}
    {Bw ms ws N Ms : ℕ} {I : ℕ → (ℕ → ℕ) → Prop}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    {δ β0 γ : ℕ} {j n : ℕ} {s : RAMState}
    {header control hintMap resultMap listBase table count : ℕ}
    {y : Fin Ms → ZMod 2} {J : List ℕ}
    (hdown : DownBlkSemAtW Sdec E Tdec Bw ms ws I Hs)
    (hAt : At P a ((cwWrap Sdec δ β0 ms γ ws).compile a))
    (hW : 1 < 2 ^ E.W) (hell : n < 2 ^ E.W) (hj : j < n)
    (hpc : s.pc = a) (h1 : s.regs 1 = j) (h2 : s.regs 2 = n)
    (hfit : wordsOf E.W Ms ≤ ms) (hβtop : β0 + j * ms + ms ≤ 2 ^ E.W)
    (hβγ : β0 + j * ms + ms ≤ γ)
    (hws : ws ≤ 2 ^ E.W) (hγws : γ + ws ≤ 2 ^ E.W) (hcell1 : γ + ws + 1 < 2 ^ E.W)
    (hδ : δ + Bw ≤ 2 ^ E.W) (hδW : δ < 2 ^ E.W) (hmsW : ms < 2 ^ E.W)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (hmem : ∀ q < wordsOf E.W Ms, s.mem (β0 + j * ms + q) = packMem E.W y q)
    (hHint : γ ≤ hintMap) (hHintTop : hintMap + N < γ + ws)
    (hControl : γ ≤ control) (hControlTop : control + 4 ≤ γ + ws)
    (hList : γ ≤ listBase) (hListTop : listBase + N ≤ γ + ws)
    (hIFrame : ∀ n' mem, I n' mem → ∀ a', a' < γ ∨ γ + ws + 2 ≤ a' → mem a' = s.mem a')
    (hIPin : ∀ n' mem, I n' mem → mem (γ + ws) = j ∧ mem (γ + ws + 1) = n) :
    ∃ (k : ℕ) (out : RAMState), (k : ℝ) ≤ 9 + Tdec + 4 ∧ (step P E)^[k] s = out ∧
      out.pc = a + (cwWrap Sdec δ β0 ms γ ws).len ∧
      out.regs 1 = s.regs 1 ∧ out.regs 2 = s.regs 2 := by
  obtain ⟨k, out, hk, hrun, hpcOut, hr1, hr2, -⟩ :=
    cwRun (P := P) (E := E) (a := a) (Tdec := Tdec) (Sdec := Sdec)
      (Bw := Bw) (ms := ms) (ws := ws) (N := N) (Ms := Ms) (I := I) (Hs := Hs)
      (δ := δ) (β0 := β0) (γ := γ) (header := header) (control := control)
      (hintMap := hintMap) (resultMap := resultMap) (listBase := listBase)
      (table := table) (count := count) (y := y) (J := J) (j := j) (n := n) (s := s)
      hdown hAt hW hell hj hpc h1 h2 hfit hβtop hβγ hws hγws hcell1 hδ hδW hmsW
      hdr hmem hHint hHintTop hControl hControlTop hList hListTop hIFrame hIPin
  exact ⟨k, out, hk, hrun, hpcOut, hr1.trans h1.symm, hr2.trans h2.symm⟩

end W65C
end LinearSetReconciliation327.Main


