-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Memory_PhysicalNormalizationLayout
-- name    : CSL_Interchange_Framework_Memory_PhysicalNormalizationLayout
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:55:25.440948+00:00
-- url     : https://prove2.me/theorems/e1a6fd7e-7063-4c71-8bd0-efa9e86d7345
-- title:
--   Coded sorting library: Interchange / Framework / Memory / PhysicalNormalizationLayout
-- statement:
--   Module `CodedSorting.Interchange.Framework.Memory.PhysicalNormalizationLayout` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   A counted-state compact-to-dedicated converter on one finite block disk.
--   Source and target addresses occupy disjoint halves of that disk. The fixed
--   seven-phase program stores its phase and loop counter in ordinary global words;
--   it does not retain a list of commands or an old RAM snapshot across transfers.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Memory.PhysicalNormalizationLayout

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Programs_FixedPolicyNormalization
import Definitions.Def_CSL_Shared_Words_WordConvention

/-! A counted-state compact-to-dedicated converter on one finite block disk.
Source and target addresses occupy disjoint halves of that disk. The fixed
seven-phase program stores its phase and loop counter in ordinary global words;
it does not retain a list of commands or an old RAM snapshot across transfers.
-/
set_option autoImplicit false
namespace CSL.PhysicalNormalizationLayout
open WordControl

variable {R B b d w : ℕ}

/-- The two ranges are addresses on one disk, not two retained disk copies.
`finSumFinEquiv` places them in adjacent ranges of Fin (R+R). -/
abbrev Address (R : ℕ) := Fin R ⊕ Fin R
abbrev Disk (R B w : ℕ) := Address R → Words B w

structure State (R B b d w : ℕ) where
  buffer : Words B w
  scratch : Words b w
  counter : Words d w
  phase : Word w
  disk : Disk R B w

structure Program (R B b d w : ℕ) where
  blocks : ℕ
  block_bound : blocks ≤ R
  counter_bound : blocks < (2^w)^d
  positive_region : 0<R
  positive_block : 0<B
  block_ratio : b≤B
  phase_capacity : 8≤2^w
  padding : Word w

def phaseCode (p : Program R B b d w) (k : Fin 8) : Word w :=
  ⟨k.val,lt_of_lt_of_le k.isLt p.phase_capacity⟩

def counterCode (d w j : ℕ) : Words d w :=
  finFunctionFinEquiv.symm ⟨j % (2^w)^d,Nat.mod_lt _ (by positivity)⟩

@[simp] theorem decode_counterCode (j : ℕ) :
    decodeWords (counterCode d w j) = j % (2^w)^d := by
  simp [counterCode,decodeWords]

/-- Addresses are evaluated from the counted counter. Live loop iterations
have j<R; the modular fallback merely makes the fixed program total. -/
def index (p : Program R B b d w) (j : ℕ) : Fin R :=
  ⟨j%R,Nat.mod_lt _ p.positive_region⟩

def current (s : State R B b d w) : ℕ := decodeWords s.counter

def nextPhase (p : Program R B b d w) (k : Fin 8) (s : State R B b d w) :=
  {s with phase := phaseCode p k}

/-- One transition performs at most one actual B-word transfer. Local phases
only transform the displayed resident arrays. The source and target ranges
of this same disk are disjoint by their address constructors. -/
def step (p : Program R B b d w) (s : State R B b d w) : State R B b d w × ℕ :=
  let j := current s
  if j < p.blocks then
    match s.phase.val with
    | 0 => (nextPhase p 1 {s with scratch := fun _ => p.padding},0)
    | 1 => (nextPhase p 2 {s with buffer := s.disk (.inl (index p (j*b/B)))},1)
    | 2 => (nextPhase p 3 {s with scratch := LayoutConversion.extract B b (j*b) (j*b/B) p.positive_block s.buffer s.scratch},0)
    | 3 => (nextPhase p 4 {s with buffer := s.disk (.inl (index p (j*b/B+1)))},1)
    | 4 => (nextPhase p 5 {s with scratch := LayoutConversion.extract B b (j*b) (j*b/B+1) p.positive_block s.buffer s.scratch},0)
    | 5 => (nextPhase p 6 {s with buffer := Normalization.pack p.padding s.scratch},0)
    | 6 => (nextPhase p 0 {s with counter := counterCode d w (j+1), disk := Function.update s.disk (.inr (index p j)) s.buffer},1)
    | _ => (s,0)
  else (s,0)

def run (p : Program R B b d w) : ℕ → State R B b d w → State R B b d w × ℕ
  | 0,s => (s,0)
  | fuel+1,s =>
      let first := step p s
      let rest := run p fuel first.1
      (rest.1,first.2+rest.2)

def initial (p : Program R B b d w) (j : ℕ) (disk : Disk R B w) : State R B b d w :=
  ⟨fun _ => p.padding,fun _ => p.padding,counterCode d w j,phaseCode p 0,disk⟩

/-- This is a proof-only abbreviation for the two source block reads already
present in the concrete seven phases above, not a primitive of the machine. -/
def expanded (p : Program R B b d w) (disk : Disk R B w) (j : ℕ) : Words B w :=
  let first := disk (.inl (index p (j*b/B)))
  let saved := LayoutConversion.extract B b (j*b) (j*b/B) p.positive_block
    first (fun _ => p.padding)
  let second := disk (.inl (index p (j*b/B+1)))
  Normalization.pack p.padding
    (LayoutConversion.extract B b (j*b) (j*b/B+1) p.positive_block second saved)

def written (p : Program R B b d w) (disk : Disk R B w) (j : ℕ) : Disk R B w :=
  Function.update disk (.inr (index p j)) (expanded p disk j)

/-- Finite-word state decoding is exact at every live iteration, including
the completed endpoint j=blocks. -/
theorem counter_fits (p : Program R B b d w) (j : ℕ) (h : j≤p.blocks) :
    decodeWords (counterCode d w j)=j := by
  rw [decode_counterCode,Nat.mod_eq_of_lt (h.trans_lt p.counter_bound)]

theorem run_add (p : Program R B b d w) (n m : ℕ) (s : State R B b d w) :
    run p (n+m) s =
      ((run p m (run p n s).1).1,(run p n s).2+(run p m (run p n s).1).2) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih => rw [Nat.succ_add]; simp only [run,ih,Nat.add_assoc]

/-- One actual cycle preserves the source range and writes the packed logical
block into the addressed target block. All input buffer contents are arbitrary. -/
theorem seven_steps (p : Program R B b d w) (s : State R B b d w)
    (j : ℕ) (hj : j<p.blocks) (hc : current s=j) (hp : s.phase=phaseCode p 0) :
    (run p 7 s).1.disk = written p s.disk j ∧
    current (run p 7 s).1=j+1 ∧
    (run p 7 s).1.phase=phaseCode p 0 ∧
    (run p 7 s).2=3 := by
  have hlive : ∀ t : State R B b d w, current t = j → step p t =
      (match t.phase.val with
      | 0 => (nextPhase p 1 {t with scratch := fun _ => p.padding},0)
      | 1 => (nextPhase p 2 {t with buffer := t.disk (.inl (index p (j*b/B)))},1)
      | 2 => (nextPhase p 3 {t with scratch := LayoutConversion.extract B b (j*b) (j*b/B) p.positive_block t.buffer t.scratch},0)
      | 3 => (nextPhase p 4 {t with buffer := t.disk (.inl (index p (j*b/B+1)))},1)
      | 4 => (nextPhase p 5 {t with scratch := LayoutConversion.extract B b (j*b) (j*b/B+1) p.positive_block t.buffer t.scratch},0)
      | 5 => (nextPhase p 6 {t with buffer := Normalization.pack p.padding t.scratch},0)
      | 6 => (nextPhase p 0 {t with counter := counterCode d w (j+1), disk := Function.update t.disk (.inr (index p j)) t.buffer},1)
      | _ => (t,0)) := by
    intro t ht
    simp only [step, ht, if_pos hj]
  have hrun : ∀ (k : ℕ) (t : State R B b d w), run p (k+1) t = ((run p k (step p t).1).1, (step p t).2 + (run p k (step p t).1).2) := by
    intro k t; rfl
  have hcur : ∀ (t : State R B b d w) (k : Fin 8) (f : State R B b d w → State R B b d w),
      (∀ u, (f u).counter = u.counter) → current t = j → current (nextPhase p k (f t)) = j := by
    intro t k f hf ht
    simp only [current, nextPhase, hf]; exact ht
  -- the seven intermediate states
  set s1 := nextPhase p 1 {s with scratch := fun _ => p.padding} with hs1
  have h0 : step p s = (s1, 0) := by rw [hlive s hc, hp]; rfl
  have c1 : current s1 = j := hc
  set s2 := nextPhase p 2 {s1 with buffer := s1.disk (.inl (index p (j*b/B)))} with hs2
  have h1 : step p s1 = (s2, 1) := by rw [hlive s1 c1]; rfl
  have c2 : current s2 = j := hc
  set s3 := nextPhase p 3 {s2 with scratch := LayoutConversion.extract B b (j*b) (j*b/B) p.positive_block s2.buffer s2.scratch} with hs3
  have h2 : step p s2 = (s3, 0) := by rw [hlive s2 c2]; rfl
  have c3 : current s3 = j := hc
  set s4 := nextPhase p 4 {s3 with buffer := s3.disk (.inl (index p (j*b/B+1)))} with hs4
  have h3 : step p s3 = (s4, 1) := by rw [hlive s3 c3]; rfl
  have c4 : current s4 = j := hc
  set s5 := nextPhase p 5 {s4 with scratch := LayoutConversion.extract B b (j*b) (j*b/B+1) p.positive_block s4.buffer s4.scratch} with hs5
  have h4 : step p s4 = (s5, 0) := by rw [hlive s4 c4]; rfl
  have c5 : current s5 = j := hc
  set s6 := nextPhase p 6 {s5 with buffer := Normalization.pack p.padding s5.scratch} with hs6
  have h5 : step p s5 = (s6, 0) := by rw [hlive s5 c5]; rfl
  have c6 : current s6 = j := hc
  set s7 := nextPhase p 0 {s6 with counter := counterCode d w (j+1), disk := Function.update s6.disk (.inr (index p j)) s6.buffer} with hs7
  have h6 : step p s6 = (s7, 1) := by rw [hlive s6 c6]; rfl
  have hr : run p 7 s = (s7, 3) := by
    rw [hrun, h0, hrun, h1, hrun, h2, hrun, h3, hrun, h4, hrun, h5, hrun, h6]
    rfl
  rw [hr]
  refine ⟨?_, ?_, rfl, rfl⟩
  · rfl
  · simp only [s7, current, nextPhase, decode_counterCode]
    exact Nat.mod_eq_of_lt (show j+1 < (2^w)^d by have := p.counter_bound; omega)

/-- Source preservation is structural: no target address can equal a source
address, so no source snapshot is needed in resident memory. -/
theorem written_source (p : Program R B b d w) (disk : Disk R B w) (j : ℕ)
    (i : Fin R) : written p disk j (.inl i)=disk (.inl i) := by
  simp [written]

/-- Proof-only specification of the successive target updates. Execution
uses `run` and its counted counter, not this recursion index. -/
def writtenLoop (p : Program R B b d w) : ℕ → Disk R B w → Disk R B w
  | 0,disk => disk
  | n+1,disk => written p (writtenLoop p n disk) n

/-- The complete fixed phase program executes every loop iteration. The
observation horizon 7*n is ghost state; control comes from the stored words. -/
theorem loop_refines (p : Program R B b d w) (disk : Disk R B w)
    (n : ℕ) (hn : n≤p.blocks) :
    (run p (7*n) (initial p 0 disk)).1.disk = writtenLoop p n disk ∧
    current (run p (7*n) (initial p 0 disk)).1=n ∧
    (run p (7*n) (initial p 0 disk)).1.phase=phaseCode p 0 ∧
    (run p (7*n) (initial p 0 disk)).2=3*n := by
  induction n with
  | zero => simp [run,initial,current,writtenLoop]
  | succ n ih =>
    have prev := ih (by omega)
    have hs := seven_steps p (run p (7*n) (initial p 0 disk)).1 n
      (by omega) prev.2.1 prev.2.2.1
    rw [show 7*(n+1)=7*n+7 by omega,run_add]
    refine ⟨?_,hs.2.1,hs.2.2.1,?_⟩
    · rw [hs.1,prev.1]
      rfl
    · rw [prev.2.2.2,hs.2.2.2]
      omega

theorem writtenLoop_source (p : Program R B b d w) (disk : Disk R B w)
    (n : ℕ) (i : Fin R) : writtenLoop p n disk (.inl i)=disk (.inl i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [writtenLoop,written_source,ih]

theorem expanded_source_congr (p : Program R B b d w) (x y : Disk R B w)
    (h : ∀ i,x (.inl i)=y (.inl i)) (j : ℕ) : expanded p x j=expanded p y j := by
  simp only [expanded,h]

theorem index_val (p : Program R B b d w) (j : ℕ) (hj : j<R) :
    (index p j).val=j := Nat.mod_eq_of_lt hj

theorem writtenLoop_target (p : Program R B b d w) (disk : Disk R B w)
    (n : ℕ) (hn : n≤p.blocks) (j : ℕ) (hj : j<n) :
    writtenLoop p n disk (.inr (index p j))=expanded p disk j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [writtenLoop]
    by_cases he : j=n
    · subst j
      simp only [written,Function.update_self]
      exact expanded_source_congr p _ _ (writtenLoop_source p disk n) n
    · have hne : index p j≠index p n := by
        intro hx
        have hv := congrArg Fin.val hx
        rw [index_val p j (by have := p.block_bound; omega),
          index_val p n (by have := p.block_bound; omega)] at hv
        exact he hv
      rw [written,Function.update_of_ne (by simpa using hne)]
      exact ih (by omega) (by omega)

/-- Flat view of the physical source range. Positions of all live compact
records lie inside that range; the total view extends periodically outside. -/
def sourceWord (p : Program R B b d w) (disk : Disk R B w) : BlockReflection.Disk (Word w) :=
  fun y => disk (.inl (index p (y/B))) ⟨y%B,Nat.mod_lt _ p.positive_block⟩

theorem read_sourceWord (p : Program R B b d w) (disk : Disk R B w) (a : ℕ) :
    BlockReflection.readBlock (sourceWord p disk) B a = disk (.inl (index p a)) := by
  funext i
  have hd : (a*B+i.val)/B=a := by
    rw [Nat.mul_comm a B,Nat.mul_add_div p.positive_block,
      Nat.div_eq_of_lt i.isLt,Nat.add_zero]
  have hm : (a*B+i.val)%B=i.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt i.isLt]
  simp only [BlockReflection.readBlock,sourceWord,hd,hm,Fin.eta]

theorem expanded_logicalRead (p : Program R B b d w) (disk : Disk R B w) (j : ℕ) :
    expanded p disk j = Normalization.pack p.padding
      (LayoutConversion.logicalRead (sourceWord p disk) p.padding B b (j*b) p.positive_block) := by
  simp only [LayoutConversion.logicalRead,read_sourceWord,expanded]

/-- Exact compact-to-dedicated semantics of the SAME physical execution,
including preserved source blocks, final counter, termination phase and I/O. -/
theorem actual_expansion (p : Program R B b d w) (disk : Disk R B w) :
    let result := run p (7*p.blocks) (initial p 0 disk)
    (∀ j : Fin p.blocks,∀ i : Fin B,
      result.1.disk (.inr (index p j.val)) i =
        if i.val<b then sourceWord p disk (j.val*b+i.val) else p.padding) ∧
    (∀ i : Fin R,result.1.disk (.inl i)=disk (.inl i)) ∧
    current result.1=p.blocks ∧ result.1.phase=phaseCode p 0 ∧ result.2=3*p.blocks := by
  try dsimp only
  have h := loop_refines p disk p.blocks (le_refl _)
  refine ⟨?_,?_,h.2.1,h.2.2.1,h.2.2.2⟩
  · intro j i
    rw [h.1,writtenLoop_target p disk p.blocks (le_refl _) j.val j.isLt,
      expanded_logicalRead]
    simp only [Normalization.pack]
    split_ifs with hi
    · exact LayoutConversion.logicalRead_correct (sourceWord p disk) p.padding
        B b (j.val*b) p.positive_block p.block_ratio ⟨i.val,hi⟩
    · rfl
  · intro i
    rw [h.1,writtenLoop_source]

/-- Program parameters and code are fixed BEFORE choosing input disk data. -/
theorem one_program_all_inputs (p : Program R B b d w) :
    ∃ machine : ℕ → State R B b d w → State R B b d w × ℕ,
      ∀ disk : Disk R B w,
      (∀ j : Fin p.blocks,∀ i : Fin b,
        (machine (7*p.blocks) (initial p 0 disk)).1.disk
          (.inr (index p j.val)) (i.castLE p.block_ratio) =
            sourceWord p disk (j.val*b+i.val)) ∧
      (machine (7*p.blocks) (initial p 0 disk)).2=3*p.blocks := by
  refine ⟨run p,?_⟩
  intro disk
  have h := actual_expansion p disk
  refine ⟨?_,h.2.2.2.2⟩
  intro j i
  simpa only [Fin.coe_castLE,if_pos i.isLt] using h.1 j (i.castLE p.block_ratio)

/-- The completed state genuinely halts from its resident counter. It does
not rely on the external proof horizon being used as machine control. -/
theorem completed_halts (p : Program R B b d w) (disk : Disk R B w) :
    step p (run p (7*p.blocks) (initial p 0 disk)).1 =
      ((run p (7*p.blocks) (initial p 0 disk)).1,0) := by
  have h := (actual_expansion p disk).2.2.1
  simp [step,h]

/-- No modulo wrap occurs at an actual compact input position. The periodic
extension of sourceWord is used only to make out-of-range read ports total. -/
theorem live_source_address (p : Program R B b d w) (y : ℕ) (hy : y<p.blocks*b) :
    (index p (y/B)).val=y/B := by
  apply index_val
  apply (Nat.div_lt_iff_lt_mul p.positive_block).2
  calc
    y < p.blocks*b := hy
    _ ≤ R*b := Nat.mul_le_mul_right b p.block_bound
    _ ≤ R*B := Nat.mul_le_mul_left R p.block_ratio

/-- Addresses in the two disjoint regions have ordinary consecutive physical
block numbers. -/
def physicalAddress (a : Address R) : Fin (R+R) := finSumFinEquiv a

theorem physicalAddress_injective : Function.Injective (@physicalAddress R) :=
  finSumFinEquiv.injective

/-- A fixed number of ordinary global words suffices for physical address
values whenever the global disk bound is established. This is the actual
consecutive address, not an abstract counting-only existence statement. -/
def addressWords (a : Address R) : Words d w := counterCode d w (physicalAddress a).val

theorem addressWords_decode (hcap : R+R ≤ (2^w)^d) (a : Address R) :
    decodeWords (addressWords (d:=d) (w:=w) a)=(physicalAddress a).val := by
  rw [addressWords,decode_counterCode,
    Nat.mod_eq_of_lt ((physicalAddress a).isLt.trans_le hcap)]

/-- Even if a separate d-word address port is reserved during each I/O,
the full payload, scratch, loop counter, phase and port fit this budget. -/
theorem memory_with_address_port (M : ℕ) (h : B+b+2*d+1≤M) :
    Fintype.card (((Fin B ⊕ Fin b) ⊕ (Fin d ⊕ Fin 1)) ⊕ Fin d) ≤ M := by
  simp only [Fintype.card_sum,Fintype.card_fin]
  omega

/-- All resident cells, including loop and phase control, are explicit. -/
theorem resident_word_count : Fintype.card ((Fin B ⊕ Fin b) ⊕ (Fin d ⊕ Fin 1)) =
    B+b+d+1 := by simp; omega

theorem resident_configuration_count :
    Fintype.card ((Words B w × Words b w) × (Words d w × Word w)) =
      (2^w)^(B+b+d+1) := by
  simp [Words,Word,pow_add,Nat.mul_assoc]

theorem common_disk_address_count : Fintype.card (Address R)=R+R := by simp [Address]

end CSL.PhysicalNormalizationLayout


