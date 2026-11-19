-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_CoreRAMFoundation
-- name    : DecrAlmostLinearSSSP_CoreRAMFoundation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T17:30:33.190584+00:00
-- url     : https://prove2.me/theorems/806657b1-c118-4b32-8a9e-b0b20d812089
-- title:
--   Scalar RAM core and normalization representations
-- statement:
--   This module provides finite scalar-RAM representations and native programs for the normalized decremental SSSP core and its polynomial-domain input adapter.
--
--   For an original directed input with $n$ vertices, $k$ labelled edges, size bound $m$ and positive integer weight bound $W$, the adapter adds a sink vertex, redirects original edges entering the source to that sink, and adds permanent source edges. Its parameters are
--
--   $$n'=n+1,\qquad k'=k+n,\qquad m'=4m,\qquad S=8(n+1)W.$$
--
--   The public readout classifies an estimate above $S/2$ as infinity. The core representations retain distinct logical edge identifiers, real labels, cached capacities and gradients, historical return samples, pending linked queues and actual cut-program machine states. Finite instruction sequences construct these representations, call the cut program, refresh records, repair labels and forward deletions. The normalization program constructs the augmented graph tape and instruments source stores to update public answers.
--
--   These interfaces support proofs of termination, simultaneous distance accuracy, exact unreachability and charged maintenance work. Those implementation guarantees are separate theorem obligations. This module does not supply a dynamic-cut oracle or a successful-execution certificate as graph input.
--
--   **Formalization Note** The module imports the shared scalar-RAM foundation. It includes elementary representation, address and frame proofs needed to construct dependent records, together with the data structures and finite programs. Native source-memory addresses use a disjoint shifted bank; all program operations are charged scalar instructions.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, October 2026 submission #912, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf, p.4 unnumbered normalization reductions; Theorem 3.1 p.6; Sections 3.1-3.5 pp.7-17; Lemma 4.1 p.18 scalar arithmetic model. The sink/sentinel adapter is an explicit implementation of the unnumbered reductions, not an attribution to a numbered lemma.

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Adapters
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Algorithm
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Core
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_CutProtocol
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Graph
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Machine
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Potential
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_all_target_certificate
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_cache_accuracy
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_potential_lower_bound
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_stable_labels
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_toggle_descent
import Mathlib
section CoreModule37
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
def accumulate (acc counter limit factor unit : ℕ) : Cmd :=
  .loop (.natLess counter limit) (.seq (nadd acc acc factor) (nadd counter counter unit))
end DecrAlmostLinearSSSP.Decremental.Structured
end CoreModule37
section CoreModule38
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
attribute [local instance] Classical.propDecidable
def conditionalOne (test : Test) (k : ℕ) : Cmd := .branch test (natural k 1) .skip
noncomputable def conditionalOneState (test : Test) (k : ℕ) (s : Data) : Data := by
  classical
  exact if test.holds s then {s with natReg := Function.update s.natReg k 1} else s
end DecrAlmostLinearSSSP.Decremental.Structured
end CoreModule38
section CoreModule45
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
def oldVertex (i : Input) (v : Fin i.n) : Fin (i.n+1) := v.castSucc
def sink (i : Input) : Fin (i.n+1) := Fin.last i.n
def source (i : Input) : Fin (i.n+1) := oldVertex i i.source
def target (i : Input) (v : Fin i.n) : Fin (i.n+1) :=
  ⟨if v.val < i.source.val then v.val else v.val+1,by split_ifs <;> omega⟩
lemma target_ne_source (i : Input) (v : Fin i.n) : target i v ≠ source i := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [target,source,oldVertex] at hv
  split_ifs at hv <;> omega
lemma target_surjective (i : Input) (v : Fin (i.n+1)) (hne : v ≠ source i) :
    ∃ j, target i j = v := by
  have hv := v.isLt
  have hs := i.source.isLt
  have hn : v.val ≠ i.source.val := by intro h;apply hne;exact Fin.ext h
  let j : Fin i.n := ⟨if v.val < i.source.val then v.val else v.val-1,by split_ifs <;> omega⟩
  refine ⟨j,Fin.ext ?_⟩
  dsimp [target,j]
  split_ifs <;> omega
def oldEdge (i : Input) (e : Fin i.k) : Fin (i.k+i.n) := e.castAdd i.n
def addedEdge (i : Input) (v : Fin i.n) : Fin (i.k+i.n) := v.natAdd i.k
def tail (i : Input) (e : Fin (i.k+i.n)) : Fin (i.n+1) :=
  if h : e.val < i.k then oldVertex i (i.graph.tail ⟨e.val,h⟩) else source i
def head (i : Input) (e : Fin (i.k+i.n)) : Fin (i.n+1) :=
  if h : e.val < i.k then
    if i.graph.head ⟨e.val,h⟩ = i.source then sink i else oldVertex i (i.graph.head ⟨e.val,h⟩)
  else target i ⟨e.val-i.k,by omega⟩
def sentinel (i : Input) : ℕ := 8*(i.n+1)*i.W
def weight (i : Input) (e : Fin (i.k+i.n)) : ℕ :=
  if h : e.val < i.k then i.weight ⟨e.val,h⟩ else sentinel i
def input (i : Input) : Input where
  n := i.n+1
  k := i.k+i.n
  graph := ⟨tail i,head i⟩
  source := source i
  weight := weight i
  W := sentinel i
  accuracy := i.accuracy
  size := 4*i.size
lemma old_edge_tail (i : Input) (e : Fin i.k) : tail i (oldEdge i e) = oldVertex i (i.graph.tail e) := by
  simp [tail,oldEdge]
lemma old_edge_head (i : Input) (e : Fin i.k) : head i (oldEdge i e) =
    if i.graph.head e = i.source then sink i else oldVertex i (i.graph.head e) := by
  simp [head,oldEdge] <;> rfl
lemma old_edge_weight (i : Input) (e : Fin i.k) : weight i (oldEdge i e) = i.weight e := by
  simp [weight,oldEdge]
lemma added_edge_tail (i : Input) (v : Fin i.n) : tail i (addedEdge i v) = source i := by
  simp [tail,addedEdge]
lemma added_edge_head (i : Input) (v : Fin i.n) : head i (addedEdge i v) = target i v := by
  simp [head,addedEdge,show ¬i.k+v.val < i.k by omega]
lemma added_edge_weight (i : Input) (v : Fin i.n) : weight i (addedEdge i v) = sentinel i := by
  simp [weight,addedEdge]
lemma no_incoming_source (i : Input) (e : Fin (i.k+i.n)) : head i e ≠ source i := by
  unfold head
  split_ifs with h he
  · intro hh
    have hv := congrArg Fin.val hh
    dsimp [sink,source,oldVertex] at hv
    omega
  · intro hh
    apply he
    apply Fin.ext
    exact congrArg (fun z : Fin (i.n+1) => z.val) hh
  · exact target_ne_source i _
lemma reachable (i : Input) (v : Fin (i.n+1)) :
    Reachable (input i).graph Finset.univ (source i) v := by
  classical
  by_cases he : v = source i
  · subst v;exact ⟨[],Walk.nil _⟩
  · obtain ⟨j,hj⟩ := target_surjective i v he
    refine ⟨[addedEdge i j],?_⟩
    have ht := added_edge_tail i j
    have hh := (added_edge_head i j).trans hj
    have hw := Walk.cons (u := source i) (g := (input i).graph) (active := Finset.univ)
      (addedEdge i j) (Finset.mem_univ _) (Walk.nil ((input i).graph.head (addedEdge i j)))
    change Walk (input i).graph Finset.univ (tail i (addedEdge i j)) (head i (addedEdge i j)) [addedEdge i j] at hw
    rwa [ht,hh] at hw
lemma sink_ne_old (i : Input) (v : Fin i.n) : sink i ≠ oldVertex i v := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [sink,oldVertex] at hv
  omega
lemma tail_ne_sink (i : Input) (e : Fin (i.k+i.n)) : tail i e ≠ sink i := by
  unfold tail
  split
  · exact Ne.symm (sink_ne_old i _)
  · exact Ne.symm (sink_ne_old i _)
end DecrAlmostLinearSSSP.Decremental.Normalize
end CoreModule45
section CoreModule46
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize
lemma sentinel_ge (i : Input) (hi : i.Valid) : 1 ≤ sentinel i := by
  have hn := i.source.isLt
  have hW := hi.2.2.1
  unfold sentinel
  nlinarith
lemma valid (i : Input) (hi : i.Valid) : (input i).Valid := by
  have hn := i.source.isLt
  have hm := hi.1
  have hk := hi.2.1
  have hW := hi.2.2.1
  have hs := sentinel_ge i hi
  refine ⟨by dsimp [input];omega,by dsimp [input];omega,hs,hi.2.2.2.1,hi.2.2.2.2.1,?_⟩
  intro e
  change 1 ≤ weight i e ∧ weight i e ≤ sentinel i
  unfold weight
  split_ifs with h
  · have he := hi.2.2.2.2.2 ⟨e.val,h⟩
    refine ⟨he.1,he.2.trans ?_⟩
    unfold sentinel
    nlinarith
  · exact ⟨hs,le_rfl⟩
lemma weight_range (i : Input) (hi : i.Valid) (d : ℕ) (hW : i.W ≤ i.size^d) :
    (input i).W ≤ (input i).size^(d+3) := by
  have hn := i.source.isLt
  have hm := hi.1
  have hms : 1 ≤ i.size := by omega
  have hn1 : i.n+1 ≤ 2*i.size := by omega
  have hp : i.size^d ≤ (4*i.size)^d := Nat.pow_le_pow_left (by omega) d
  change 8*(i.n+1)*i.W ≤ (4*i.size)^(d+3)
  calc
    _ ≤ 16*i.size*(4*i.size)^d := by nlinarith
    _ ≤ (4*i.size)^3*(4*i.size)^d := by
      apply Nat.mul_le_mul_right
      have hx : 16*i.size ≤ (4*i.size)^2 := by nlinarith
      exact hx.trans (pow_le_pow_right₀ (show 1 ≤ 4*i.size by omega) (by omega))
    _ = _ := by rw [pow_add];ring
noncomputable def core (i : Input) (hi : i.Valid) (hn : 2 ≤ i.n) (d : ℕ)
    (hW : i.W ≤ i.size^d) (heps : 1/(i.size:ℝ) < i.accuracy) (heps1 : i.accuracy < 1) : Core where
  input := input i
  valid := valid i hi
  two := by dsimp [input];omega
  epsilon_low := by
    have hnm := hi.1
    have hm : (0:ℝ) < i.size := by exact_mod_cast (show 0 < i.size by omega)
    change 1/((4*i.size:ℕ):ℝ) < i.accuracy
    have hh : (i.size:ℝ) ≤ (4*i.size:ℕ) := by push_cast;linarith
    exact (one_div_le_one_div_of_le hm hh).trans_lt heps
  epsilon_high := heps1
  initially_reachable := reachable i
  no_incoming_source := no_incoming_source i
  weightExponent := d+3
  weightRange := weight_range i hi d hW
end DecrAlmostLinearSSSP.Decremental.Normalize
end CoreModule46
section CoreModule47
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
noncomputable def active (i : Input) (a : Finset (Fin i.k)) : Finset (Fin (i.k+i.n)) := by
  classical
  exact Finset.univ.filter fun e => ∀ h : e.val < i.k, (⟨e.val,h⟩ : Fin i.k) ∈ a
end DecrAlmostLinearSSSP.Decremental.Normalize
end CoreModule47
section CoreModule48
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule48
section CoreModule49
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end CoreModule49
section CoreModule50
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end CoreModule50
section CoreModule51
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
def cutoff (i : Input) : ℕ := 4*(i.n+1)*i.W
noncomputable def sanitize (i : Input) (D : ℝ≥0∞) : ℝ≥0∞ := if (cutoff i : ℝ≥0∞) < D then ⊤ else D
end DecrAlmostLinearSSSP.Decremental.Normalize
end CoreModule51
section CoreModule58
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Instrumented
open Structured
def instruction (action : Instruction → Cmd) (pc : ℕ) (ins : Instruction) : Cmd :=
  .seq (.seq (natural 2 (pc+1)) (nadd 3 3 1)) (action ins)
def dispatch (action : Instruction → Cmd) : ℕ → List Instruction → Cmd
  | _,[] => .seq (natural 5 1) (natural 4 1)
  | pc,ins::rest => .seq (natural 8 (pc+1))
      (.branch (.natLess 2 8) (instruction action pc ins) (dispatch action (pc+1) rest))
def charge (bound : Instruction → ℕ) (code : List Instruction) : ℕ :=
  (code.map (fun ins => bound ins+5)).sum
def MachineRep (B F : ℕ) (s : Data) (g : Machine) : Prop :=
  ShadowDataRep B F s g ∧ s.natReg 0 = B ∧ s.natReg 1 = 1 ∧ s.natReg 7 = F ∧
    s.realReg 7 = (F : ℝ) ∧ s.natReg 4 ≤ 1
structure ActionSpec (action : Instruction → Cmd) (bound : Instruction → ℕ)
    (P : Data → Machine → Prop) (B F : ℕ) : Prop where
  header : ∀ s g, P s g → P
    {s with natReg := Function.update (Function.update s.natReg 2 (g.pc+1)) 3 (s.natReg 3+1)}
    {g with pc := g.pc+1,work := g.work+1}
  scratch : ∀ s g x, P s g → P {s with natReg := Function.update s.natReg 8 x} g
  action_eval : ∀ s g ins, MachineRep B F s g → P s g →
    ∃ cost t, Eval (action ins) s cost t ∧ cost ≤ bound ins ∧
      MachineRep B F t (instructionEffect ins g) ∧ P t (instructionEffect ins g)
end DecrAlmostLinearSSSP.Decremental.Instrumented
end CoreModule58
section CoreModule59
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Instrumented
open Structured
def interpreter (action : Instruction → Cmd) (code : List Instruction) : Cmd :=
  .loop (.natLess 4 1) (dispatch action 0 code)
end DecrAlmostLinearSSSP.Decremental.Instrumented
end CoreModule59
section CoreModule60
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
def prefixAtoms : List Atom := [⟨.nadd 18 6 1,trivial⟩,⟨.loadN 20 18,trivial⟩,
  ⟨.loadN 22 6,trivial⟩,⟨.load 20 6,trivial⟩,⟨.natural 30 0,trivial⟩]
def prefixCode : Cmd := sequence (prefixAtoms.map Cmd.atom)
noncomputable def prepared (s : Data) : Data := prefixAtoms.foldl (fun t a => a.effect t) s
def flagCode : Cmd := .seq (conditionalOne (.natLess 1 22) 30) (conditionalOne (.realLess 26 20) 30)
noncomputable def flagged (s : Data) : Data :=
  conditionalOneState (.realLess 26 20) 30 (conditionalOneState (.natLess 1 22) 30 s)
def inner : Cmd := .seq prefixCode (.seq flagCode (.seq (storeN 20 30) (store 20 20)))
def callback : Cmd := .branch (.natLess 6 16) inner .skip
noncomputable def committed (s : Data) : Data :=
  let t := flagged (prepared s)
  {t with natMem := Function.update t.natMem (t.natReg 20) (t.natReg 30), realMem := Function.update t.realMem (t.natReg 20) (t.realReg 20)}
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule60
section CoreModule64
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule64
section CoreModule65
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
noncomputable def answerFlag (i : Input) (g : Machine) (v : ℕ) : ℕ :=
  if 0 < g.natMem v ∨ (cutoff i : ℝ) < g.realMem v then 1 else 0
structure Image (i : Input) (B : ℕ) (bad : Option ℕ) (s : Data) (g : Machine) : Prop where
  room : i.n ≤ B
  limit : s.natReg 16 = B+4*i.n+2
  threshold : s.realReg 26 = (cutoff i : ℝ)
  mapping : ∀ v : Fin i.n, s.natMem (B+4*v.val+3) = v.val
  values : ∀ v : Fin i.n, bad ≠ some v.val → s.realMem v.val = g.realMem v.val
  flags : ∀ v : Fin i.n, bad ≠ some v.val → s.natMem v.val = answerFlag i g v.val
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule65
section CoreModule66
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
def prepareAtoms : List Atom := [⟨.nadd 76 66 26,trivial⟩,⟨.natural 78 0,trivial⟩,⟨.natural 80 0,trivial⟩,
  ⟨.nadd 82 70 70,trivial⟩,⟨.nadd 82 82 82,trivial⟩,⟨.nadd 82 82 82,trivial⟩]
def prepareCode : Cmd := sequence (prepareAtoms.map Cmd.atom)
noncomputable def prepareData (s : Data) : Data := prepareAtoms.foldl (fun t a => a.effect t) s
def weightCode : Cmd := .seq prepareCode (accumulate 78 80 76 82 26)
def headerAtoms (entry : ℕ) : List Atom := [
  ⟨.nadd 0 74 56,trivial⟩,⟨.natural 1 1,trivial⟩,⟨.natural 2 entry,trivial⟩,
  ⟨.natural 3 0,trivial⟩,⟨.natural 4 0,trivial⟩,⟨.natural 5 0,trivial⟩,⟨.natural 7 2,trivial⟩,⟨.rational 7 2,trivial⟩,
  ⟨.nadd 9 76 76,trivial⟩,⟨.nadd 11 68 66,trivial⟩,⟨.nadd 11 11 11,trivial⟩,
  ⟨.nadd 13 64 64,trivial⟩,⟨.nadd 13 13 13,trivial⟩,⟨.nadd 13 13 13,trivial⟩,
  ⟨.nadd 15 78 78,trivial⟩,⟨.nadd 17 72 72,trivial⟩,⟨.add 9 64 56,trivial⟩,
  ⟨.cast 26 78,trivial⟩,⟨.rational 28 (1/2),trivial⟩,⟨.mul 26 26 28,trivial⟩,
  ⟨.nadd 16 66 66,trivial⟩,⟨.nadd 16 16 16,trivial⟩,⟨.nadd 16 16 74,trivial⟩,⟨.nadd 16 16 14,trivial⟩]
def headerCode (entry : ℕ) : Cmd := sequence ((headerAtoms entry).map Cmd.atom)
noncomputable def headerData (entry : ℕ) (s : Data) : Data := (headerAtoms entry).foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule66
section CoreModule68
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule68
section CoreModule69
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
def fieldAtoms : List Atom := [⟨.loadN 84 80,trivial⟩,⟨.nadd 84 84 84,trivial⟩,
  ⟨.storeN 82 84,trivial⟩,⟨.nadd 80 80 26,trivial⟩,⟨.nadd 82 82 88,trivial⟩]
def fieldCode : Cmd := sequence (fieldAtoms.map Cmd.atom)
noncomputable def fieldData (s : Data) : Data := fieldAtoms.foldl (fun t a => a.effect t) s
def headRedirect : Cmd := .branch (.natLess 84 72) .skip
  (.branch (.natLess 72 84) .skip (nadd 84 66 56))
noncomputable def redirected (s : Data) : Data := by
  classical
  exact if s.natReg 84 = s.natReg 72 then {s with natReg := Function.update s.natReg 84 (s.natReg 66+s.natReg 56)} else s
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule69
section CoreModule70
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
def headSuffixAtoms : List Atom := [⟨.nadd 84 84 84,trivial⟩,⟨.storeN 82 84,trivial⟩,
  ⟨.nadd 80 80 26,trivial⟩,⟨.nadd 82 82 88,trivial⟩]
def headSuffix : Cmd := sequence (headSuffixAtoms.map Cmd.atom)
noncomputable def headLoaded (s : Data) : Data := {s with natReg := Function.update s.natReg 84 (s.natMem (s.natReg 80))}
noncomputable def headData (s : Data) : Data := headSuffixAtoms.foldl (fun t a => a.effect t) (redirected (headLoaded s))
def headCode : Cmd := .seq (loadN 84 80) (.seq headRedirect headSuffix)
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule70
section CoreModule108
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceMemory
end CoreModule108
section CoreModule109
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule109
section CoreModule110
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
def recordCode : Cmd := .seq fieldCode (.seq headCode (.seq fieldCode (nadd 90 90 26)))
noncomputable def recordData (s : Data) : Data :=
  let t := fieldData (headData (fieldData s))
  {t with natReg := Function.update t.natReg 90 (t.natReg 90+t.natReg 26)}
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule110
section CoreModule111
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule111
section CoreModule112
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule112
section CoreModule114
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize
noncomputable def natPrefix (f : ℕ → ℕ) (bound a : ℕ) : ℕ := if a < bound then f a else 0
end DecrAlmostLinearSSSP.Decremental.Normalize
end CoreModule114
section CoreModule115
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end CoreModule115
section CoreModule116
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
structure CopyInvariant (i : Input) (p : Program) (B : ℕ) (s : Data) : Prop where
  captured : InputCapture.Captured i s
  base_room : i.n+3*i.k ≤ B
  count : s.natReg 90 ≤ i.k
  source : s.natReg 80 = i.n+3*s.natReg 90
  dest : s.natReg 82 = bankAddress B 0 (i.n+1+3*s.natReg 90)
  stride : s.natReg 88 = 4
  image : SourceMemory.Image B 0 s (natPrefix (initialMachine p (input i)).natMem (i.n+1+3*s.natReg 90)) (fun _ => 0)
  raw : ∀ a, a < B → s.natMem a = (initialMachine p i).natMem a
def copyLoop : Cmd := .loop (.natLess 90 68) recordCode
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule116
section CoreModule117
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
structure Registers (i : Input) (p : Program) (s : Data) : Prop where
  base : s.natReg 0 = i.n+3*i.k+2
  unit : s.natReg 1 = 1
  factor : s.natReg 7 = 2
  realFactor : s.realReg 7 = 2
  pc : s.natReg 2 = p.initPC
  work : s.natReg 3 = 0
  halted : s.natReg 4 = 0
  fault : s.natReg 5 = 0
  natReg : ∀ j, s.natReg (shadowReg j) = 2*(initialMachine p (input i)).natReg j
  realReg : ∀ j, s.realReg (shadowReg j) = (initialMachine p (input i)).realReg j
  limit : s.natReg 16 = (i.n+3*i.k+2)+4*i.n+2
  threshold : s.realReg 26 = (cutoff i : ℝ)
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule117
section CoreModule119
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
def copyStartAtoms : List Atom := [⟨.nadd 80 66 56,trivial⟩,⟨.nadd 82 76 76,trivial⟩,
  ⟨.nadd 82 82 82,trivial⟩,⟨.nadd 82 82 74,trivial⟩,⟨.nadd 82 82 14,trivial⟩,
  ⟨.natural 88 4,trivial⟩,⟨.natural 90 0,trivial⟩]
def copyStart : Cmd := sequence (copyStartAtoms.map Cmd.atom)
noncomputable def copyStarted (s : Data) : Data := copyStartAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule119
section CoreModule120
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
def sentinelPrefixAtoms : List Atom := [⟨.nadd 84 72 72,trivial⟩,⟨.storeN 82 84,trivial⟩,
  ⟨.nadd 82 82 88,trivial⟩,⟨.nadd 84 90 56,trivial⟩]
def sentinelSuffixAtoms : List Atom := [⟨.nadd 84 84 84,trivial⟩,⟨.storeN 82 84,trivial⟩,
  ⟨.nadd 82 82 88,trivial⟩,⟨.nadd 84 78 78,trivial⟩,⟨.storeN 82 84,trivial⟩,
  ⟨.nadd 82 82 88,trivial⟩,⟨.storeN 92 90,trivial⟩,⟨.nadd 92 92 88,trivial⟩,⟨.nadd 90 90 26,trivial⟩]
def sentinelPrefix : Cmd := sequence (sentinelPrefixAtoms.map Cmd.atom)
def sentinelSuffix : Cmd := sequence (sentinelSuffixAtoms.map Cmd.atom)
noncomputable def sentinelPrepared (s : Data) : Data := sentinelPrefixAtoms.foldl (fun t a => a.effect t) s
noncomputable def sentinelShifted (s : Data) : Data :=
  if s.natReg 90 < s.natReg 72 then s else {s with natReg := Function.update s.natReg 84 (s.natReg 84+s.natReg 26)}
noncomputable def sentinelData (s : Data) : Data := sentinelSuffixAtoms.foldl (fun t a => a.effect t) (sentinelShifted (sentinelPrepared s))
def sentinelBody : Cmd := .seq sentinelPrefix
  (.seq (.branch (.natLess 90 72) .skip (nadd 84 84 26)) sentinelSuffix)
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule120
section CoreModule121
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule121
section CoreModule122
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule122
section CoreModule123
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceMemory
end CoreModule123
section CoreModule124
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
structure SentinelInvariant (i : Input) (p : Program) (B : ℕ) (s : Data) : Prop where
  captured : InputCapture.Captured i s
  count : s.natReg 90 ≤ i.n
  dest : s.natReg 82 = bankAddress B 0 (i.n+1+3*(i.k+s.natReg 90))
  map : s.natReg 92 = B+4*s.natReg 90+3
  stride : s.natReg 88 = 4
  weight : s.natReg 78 = sentinel i
  image : SourceMemory.Image B 0 s (natPrefix (initialMachine p (input i)).natMem (i.n+1+3*(i.k+s.natReg 90))) (fun _ => 0)
  mapping : ∀ v : Fin i.n, v.val < s.natReg 90 → s.natMem (B+4*v.val+3) = v.val
  raw : ∀ a, a < B → s.natMem a = (initialMachine p i).natMem a
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule124
section CoreModule125
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
def sentinelLoop : Cmd := .loop (.natLess 90 66) sentinelBody
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule125
section CoreModule126
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
def sentinelStartAtoms : List Atom := [⟨.natural 90 0,trivial⟩,⟨.nadd 92 74 26,trivial⟩,⟨.nadd 92 92 14,trivial⟩]
def sentinelStart : Cmd := sequence (sentinelStartAtoms.map Cmd.atom)
noncomputable def sentinelStarted (s : Data) : Data := sentinelStartAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule126
section CoreModule127
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule127
section CoreModule128
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule128
section CoreModule129
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
def writtenAddress (ins : Instruction) (g : Machine) : Option ℕ :=
  match ins with | .store a _ | .storeN a _ => some (g.natReg a) | _ => none
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule129
section CoreModule130
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end CoreModule130
section CoreModule131
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
def action (ins : Instruction) : Cmd := match ins with
  | .store _ _ | .storeN _ _ => .seq (shadowAction ins) callback
  | _ => shadowAction ins
def bound (ins : Instruction) : ℕ := actionBound ins+12
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule131
section CoreModule132
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
def bootCode (p : Program) : Cmd := .seq InputCapture.code (.seq weightCode
  (.seq (headerCode p.initPC) (.seq copyStart (.seq copyLoop (.seq sentinelStart sentinelLoop)))))
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule132
section CoreModule133
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule133
section CoreModule134
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
def updateHeaderAtoms (entry : ℕ) : List Atom := [⟨.nadd 19 5 5,trivial⟩,
  ⟨.natural 2 entry,trivial⟩,⟨.natural 4 0,trivial⟩,⟨.natural 5 0,trivial⟩]
def updateHeader (p : Program) : Cmd := sequence ((updateHeaderAtoms p.update).map Cmd.atom)
noncomputable def externallySupplied (s : Data) (e : ℕ) : Data := {s with natReg := Function.update s.natReg 5 e}
noncomputable def updateStarted (p : Program) (s : Data) (e : ℕ) : Data :=
  (updateHeaderAtoms p.update).foldl (fun t a => a.effect t) (externallySupplied s e)
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule134
section CoreModule139
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
def initialization (p : Program) : Cmd := .seq (bootCode p) (interpreter action p.code)
def update (p : Program) : Cmd := .seq (updateHeader p) (interpreter action p.code)
def program (p : Program) : Program := Structured.program (initialization p) (update p)
def dispatchCost (p : Program) : ℕ := charge bound p.code+3
def Boundary (i : Input) (c g : Machine) : Prop :=
  MachineRep (i.n+3*i.k+2) 2 (data c) g ∧ Image i (i.n+3*i.k+2) none (data c) g
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule139
section CoreModule140
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule140
section CoreModule141
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
def Correct (i : Input) (ds : List (Fin i.k)) (c : Machine) : Prop :=
  stored c i.source.val = 0 ∧
    (∀ v : Fin i.n, c.natMem v.val ≤ 1 ∧ (c.natMem v.val = 0 → 0 ≤ c.realMem v.val)) ∧
    ∀ v : Fin i.n, i.dist ds v ≤ stored c v.val ∧ stored c v.val ≤ ENNReal.ofReal (1+i.accuracy)*i.dist ds v ∧
      (stored c v.val = ⊤ ↔ ¬Reachable i.graph (live ds) i.source v)
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule141
section CoreModule144
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
noncomputable def overhead (a : ℕ → ℝ) (m : ℕ) : ℝ := 1+a (4*m)
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule144
section CoreModule145
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end CoreModule145
section CoreModule146
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule146
section CoreModule147
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule147
section CoreModule148
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
def cutDirection {n : ℕ} (C : Finset (Fin n)) (tau : ℝ) (v : Fin n) : ℝ :=
  if v ∈ C then tau else 0
end DecrAlmostLinearSSSP.Decremental
end CoreModule148
section CoreModule149
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule149
section CoreModule150
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule150
section CoreModule151
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule151
section CoreModule152
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule152
section CoreModule153
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule153
section CoreModule154
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def cacheModel (b : Core) (s : State b) (e : Edge b) : ℝ :=
  coefficient b e / max (cost b s.active e + initialLabel b (tail b e) -
    initialLabel b (head b e) + s.baseline e) (kappa b)
structure CacheInvariant (b : Core) (K : ℝ) (s : State b) : Prop where
  model : ∀ e, s.cache e = cacheModel b s e
  gradient_eq : s.cachedGradient = gradient b s.cache
  detector : ∀ e, e ∉ s.pending →
    |s.cache e * (s.y (tail b e) - s.y (head b e) - s.baseline e)| < K ^ (-2 : ℤ)
end DecrAlmostLinearSSSP.Decremental
end CoreModule154
section CoreModule155
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule155
section CoreModule156
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule156
section CoreModule157
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule157
section CoreModule158
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def reportedToggle (b : Core) (K : ℝ) (s : State b) (r : CutReply b)
    (reports : List (Edge b)) : State b := {toggle b K s r with pending := reports}
def ReportsComplete (b : Core) (K : ℝ) (s : State b) (r : CutReply b)
    (reports : List (Edge b)) : Prop :=
  ∀ e, K^(-2 : ℤ) ≤ |s.cache e*((toggle b K s r).y (tail b e)-
    (toggle b K s r).y (head b e)-s.baseline e)| → e ∈ reports
end DecrAlmostLinearSSSP.Decremental
end CoreModule158
section CoreModule159
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule159
section CoreModule160
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule160
section CoreModule161
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule161
section CoreModule162
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule162
section CoreModule163
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule163
section CoreModule164
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
structure RuntimeInvariant (b : Core) (K : ℝ) (s : State b) : Prop where
  cache : CacheInvariant b K s
  counter : s.nonzeroEntries = ∑ v, nonzero (s.cachedGradient v)
  sample : ∀ v : ReturnVertex b, s.sample v.val = initialLabel b v.val+s.baseline (.inr v)
  output : ∀ v, s.output v = if v = b.input.source then 0 else readout b (s.sample v)
  energy : potential b s.active (labels b s)+(s.toggles : ℝ)*(1/(8*K^3)) ≤
    potential b Finset.univ (initialLabel b)
end DecrAlmostLinearSSSP.Decremental
end CoreModule164
section CoreModule165
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule165
section CoreModule166
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def repairLimit (b : Core) (K : ℝ) : ℕ :=
  ⌈16*K^3*A b*b.input.size*Real.log (2*Q b)⌉₊+1
noncomputable def runtimeRepairRank (b : Core) (K : ℝ) (s : State b) : ℕ × ℕ :=
  if s.stopped then (0,0) else (repairLimit b K-s.toggles+1,s.pending.length+1)
end DecrAlmostLinearSSSP.Decremental
end CoreModule166
section CoreModule167
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule167
section CoreModule168
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule168
section CoreModule169
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule169
section CoreModule170
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule170
section CoreModule172
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def coreLength (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (e : Fin b.input.k) : ℝ :=
  max (slack b active p (.inl e)) (kappa b)
end DecrAlmostLinearSSSP.Decremental
end CoreModule172
section CoreModule173
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule173
section CoreModule174
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule174
section CoreModule175
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
structure ReadoutCertificate (b : Core) (s : State b) : Prop where
  targets : AllTarget b s.active (labels b s)
  samples : ∀ v, v ≠ b.input.source →
    (1-b.input.accuracy/8)*labels b s v ≤ s.sample v ∧
    s.sample v ≤ (1+b.input.accuracy/8)*labels b s v
  output : ∀ v, s.output v = if v = b.input.source then 0 else readout b (s.sample v)
end DecrAlmostLinearSSSP.Decremental
end CoreModule175
section CoreModule176
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
inductive RuntimeRepairStep (b : Core) (K : ℝ) : State b → State b → Prop
  | refresh (s : State b) (e : Edge b) (es : List (Edge b))
      (running : s.stopped = false) (pending : s.pending = e::es) :
      RuntimeRepairStep b K s (DecrAlmostLinearSSSP.Decremental.refresh b s e)
  | toggle (s : State b) (r : CutReply b) (reports : List (Edge b))
      (running : s.stopped = false) (drained : s.pending = [])
      (quality : RatioGuarantee (cachedPhysical b s) K r.G r.U r.cut)
      (failed : r.G/r.U < -1/(4*K)) (complete : ReportsComplete b K s r reports) :
      RuntimeRepairStep b K s (reportedToggle b K s r reports)
  | stop (s : State b) (running : s.stopped = false) (drained : s.pending = [])
      (test : s.nonzeroEntries = 0 ∨ ∃ r : CutReply b,
        RatioGuarantee (cachedPhysical b s) K r.G r.U r.cut ∧ -1/(4*K) ≤ r.G/r.U) :
      RuntimeRepairStep b K s {s with stopped := true}
end DecrAlmostLinearSSSP.Decremental
end CoreModule176
section CoreModule177
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule177
section CoreModule178
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def toggleVolume {n k : ℕ} (ops : List (CutOp n k)) : ℕ :=
  (ops.filter (fun op => match op with | .toggle _ => true | _ => false)).length
def reportVolume (cs : List Machine) : ℕ := ((cs.drop 1).map reportCount).sum
structure CutSession (impl : CutImplementation) (n k m exponent : ℕ) (first : Machine)
    (K ξ h Γ init : ℝ) : Prop where
  total : ∀ ops cs, CutRun impl n k m exponent first ops cs →
    ∀ c, cs.getLast? = some c → ∀ op, CutOp.Valid (impl.view n k c) op →
      (applyPhysical (impl.view n k c).physical op).Valid m exponent →
      ∃ d, Ends impl.program (cutRequest impl.program c op) d ∧
        CutTransition K ξ (impl.view n k c) op d (impl.view n k d)
  transition : ∀ ops cs, CutRun impl n k m exponent first ops cs →
    ∀ (j : ℕ) c d op, cs[j]? = some c → cs[j+1]? = some d → ops[j]? = some op →
      CutTransition K ξ (impl.view n k c) op d (impl.view n k d)
  reports : ∀ ops cs, CutRun impl n k m exponent first ops cs →
    (reportVolume cs : ℝ) ≤ Γ*(toggleVolume ops)/ξ
  work : ∀ ops cs, CutRun impl n k m exponent first ops cs →
    ∀ last, cs.getLast? = some last →
      (last.work+6*ops.length : ℕ) ≤ init+h*((ops.length : ℝ)+reportVolume cs)
end DecrAlmostLinearSSSP.Decremental
end CoreModule178
section CoreModule179
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule179
section CoreModule180
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
noncomputable def primitiveRealRead (ins : Instruction) (s : Data) (k : ℕ) : ℝ :=
  match ins with
  | .rational d q => if k=d then (q : ℝ) else s.realReg k
  | .cast d a => if k=d then (s.natReg a : ℝ) else s.realReg k
  | .add d a b => if k=d then s.realReg a+s.realReg b else s.realReg k
  | .sub d a b => if k=d then s.realReg a-s.realReg b else s.realReg k
  | .mul d a b => if k=d then s.realReg a*s.realReg b else s.realReg k
  | .div d a b => if k=d then s.realReg a/s.realReg b else s.realReg k
  | .log d a => if k=d then Real.log (s.realReg a) else s.realReg k
  | .load d a => if k=d then s.realMem (s.natReg a) else s.realReg k
  | _ => s.realReg k
noncomputable def primitiveNatRead (ins : Instruction) (s : Data) (k : ℕ) : ℕ :=
  match ins with
  | .natural d q => if k=d then q else s.natReg k
  | .nadd d a b => if k=d then s.natReg a+s.natReg b else s.natReg k
  | .nsub d a b => if k=d then s.natReg a-s.natReg b else s.natReg k
  | .loadN d a => if k=d then s.natMem (s.natReg a) else s.natReg k
  | _ => s.natReg k
end DecrAlmostLinearSSSP.Decremental.Structured
end CoreModule180
section CoreModule181
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
def natAtoms (slot source : ℕ) : List Atom := [⟨.natural 630 (2*slot),trivial⟩,
  ⟨.nadd 630 50 630,trivial⟩,⟨.storeN 630 source,trivial⟩]
def natCode (slot source : ℕ) : Cmd := Structured.sequence ((natAtoms slot source).map Cmd.atom)
noncomputable def natResult (slot source : ℕ) (s : Data) : Data :=
  (natAtoms slot source).foldl (fun t a => a.effect t) s
def realAtoms (slot source : ℕ) : List Atom := [⟨.natural 630 (2*slot),trivial⟩,
  ⟨.nadd 630 50 630,trivial⟩,⟨.store 630 source,trivial⟩]
def realCode (slot source : ℕ) : Cmd := Structured.sequence ((realAtoms slot source).map Cmd.atom)
noncomputable def realResult (slot source : ℕ) (s : Data) : Data :=
  (realAtoms slot source).foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end CoreModule181
section CoreModule182
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
structure SavedImage (N : ℕ) (g : Machine) (s : Data) : Prop where
  nat : ∀ j < N, s.natMem (s.natReg 50+2*j) = 2*g.natReg j
  real : ∀ j < N, s.realMem (s.natReg 50+2*j) = g.realReg j
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end CoreModule182
section CoreModule184
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule184
section CoreModule194
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
structure Image (B R N : ℕ) (g : Machine) (s : Data) : Prop where
  base : s.natReg 74 = B
  factor : s.natReg 112 = 2
  record : s.natReg 106 = R
  savedBase : s.natReg 50 = R+8
  zero : s.natReg 56 = 0
  realMem : ∀ a, s.realMem (B+2*(2*a+1)) = g.realMem a
  natMem : ∀ a, s.natMem (B+2*(2*a+1)) = 2*g.natMem a
  work : s.natMem (R+6) = g.work
  saved : CoreRequest.SavedImage N g s
  tail : ∀ j, N ≤ j → s.natReg (shadowReg j) = 0 ∧ s.realReg (shadowReg j) = 0
end DecrAlmostLinearSSSP.Decremental.CoreSource
end CoreModule194
section CoreModule195
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end CoreModule195
section CoreModule196
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
def tagCode (tag : ℕ) : Cmd := .seq (natural 632 (2*tag)) (natCode 5 632)
def endpointCode : Cmd := Structured.sequence [nadd 636 626 626,nadd 638 628 628]
def eraseCode : Cmd := .seq (tagCode 1) (natCode 6 560)
def insertCode : Cmd := .seq (tagCode 0) (.seq (natCode 6 560)
  (.seq endpointCode (.seq (natCode 8 636) (.seq (natCode 9 638) (realCode 2 612)))))
def pairedCode : Cmd := .seq (tagCode 2) (.seq endpointCode
  (.seq (natCode 8 638) (.seq (natCode 9 636) (realCode 2 614))))
def ratioCode : Cmd := tagCode 3
def toggleCode : Cmd := .seq (tagCode 4) (.seq (div 640 510 31) (realCode 2 640))
def queryCode (encodedVertex : ℕ) : Cmd := .seq (tagCode 5) (natCode 6 encodedVertex)
noncomputable def tagged (tag : ℕ) (s : Data) : Data :=
  natResult 5 632 {s with natReg := Function.update s.natReg 632 (2*tag)}
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end CoreModule196
section CoreModule197
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end CoreModule197
section CoreModule198
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end CoreModule198
section CoreModule199
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end CoreModule199
section CoreModule200
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CorePending
open Structured
attribute [local instance] Classical.propDecidable
def address {l : ℕ} (B : ℕ) (e : Fin l) (offset : ℕ) : ℕ := B+10*e.val+2*offset+1
def token {l : ℕ} : List (Fin l) → ℕ
  | [] => 0
  | e::_ => 2*e.val+2
def Links {l : ℕ} (B : ℕ) : List (Fin l) → (ℕ → ℕ) → Prop
  | [],_ => True
  | e::xs,mem => mem (address B e 1) = token xs ∧ Links B xs mem
structure View {l : ℕ} (B : ℕ) (xs : List (Fin l)) (s : Data) : Prop where
  nodup : xs.Nodup
  flags : ∀ e : Fin l, s.natMem (address B e 0) = if e ∈ xs then 1 else 0
  head : s.natReg 546 = token xs
  links : Links B xs s.natMem
lemma Links.congr {l : ℕ} {B : ℕ} {xs : List (Fin l)} {mem mem' : ℕ → ℕ}
    (h : Links B xs mem) (he : ∀ e ∈ xs, mem' (address B e 1) = mem (address B e 1)) : Links B xs mem' := by
  induction xs with
  | nil => trivial
  | cons e xs ih =>
    exact ⟨(he e (by simp)).trans h.1,ih h.2 (fun f hf => he f (by simp [hf]))⟩
def prefixAtoms : List Atom := [⟨.nadd 562 560 560,trivial⟩,⟨.nadd 564 562 562,trivial⟩,
  ⟨.nadd 566 564 560,trivial⟩,⟨.nadd 568 552 566,trivial⟩,
  ⟨.loadN 570 568,trivial⟩,⟨.nadd 572 568 14,trivial⟩]
def prefixCode : Cmd := Structured.sequence (prefixAtoms.map Cmd.atom)
noncomputable def prefixData (s : Data) : Data := prefixAtoms.foldl (fun t a => a.effect t) s
def insertCode : Cmd := Structured.sequence [storeN 572 546,storeN 568 26,nadd 546 560 14]
def code : Cmd := .seq prefixCode (.branch (.natLess 570 26) insertCode .skip)
noncomputable def inserted (s : Data) : Data := {s with
  natMem := Function.update (Function.update s.natMem (s.natReg 572) (s.natReg 546)) (s.natReg 568) 1
  natReg := Function.update s.natReg 546 (s.natReg 560+2)}
end DecrAlmostLinearSSSP.Decremental.CorePending
end CoreModule200
section CoreModule201
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def returnIndex (b : Core) (v : ReturnVertex b) : Fin (b.input.n-1) :=
  ⟨if v.val.val < b.input.source.val then v.val.val else v.val.val-1,by
    have hv := v.val.isLt
    have hs := b.input.source.isLt
    have hne : v.val.val ≠ b.input.source.val := fun hh => v.property (Fin.ext hh)
    split_ifs <;> omega⟩
def returnVertex (b : Core) (j : Fin (b.input.n-1)) : ReturnVertex b :=
  ⟨⟨if j.val < b.input.source.val then j.val else j.val+1,by
    have hj := j.isLt
    have hs := b.input.source.isLt
    split_ifs <;> omega⟩,by
    intro hh
    have he := congrArg Fin.val hh
    dsimp at he
    split_ifs at he <;> omega⟩
def returnIndexEquiv (b : Core) : ReturnVertex b ≃ Fin (b.input.n-1) where
  toFun := returnIndex b
  invFun := returnVertex b
  left_inv v := by
    apply Subtype.ext
    apply Fin.ext
    have hv := v.val.isLt
    have hs := b.input.source.isLt
    have hne : v.val.val ≠ b.input.source.val := fun hh => v.property (Fin.ext hh)
    dsimp [returnVertex,returnIndex]
    split_ifs <;> omega
  right_inv j := by
    apply Fin.ext
    have hj := j.isLt
    have hs := b.input.source.isLt
    dsimp [returnVertex,returnIndex]
    split_ifs <;> omega
abbrev logicalCount (b : Core) : ℕ := b.input.k+(b.input.n-1)
def logicalIndexEquiv (b : Core) : Edge b ≃ Fin (logicalCount b) :=
  (Equiv.sumCongr (Equiv.refl (Fin b.input.k)) (returnIndexEquiv b)).trans finSumFinEquiv
end DecrAlmostLinearSSSP.Decremental
end CoreModule201
section CoreModule202
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreMemory
def field (b : Core) (B : ℕ) (e : Edge b) (offset : ℕ) : ℕ :=
  B+10*(logicalIndexEquiv b e).val+2*offset+1
def gradientBase (b : Core) (B : ℕ) : ℕ := B+10*logicalCount b+1
def gradientCell (b : Core) (B : ℕ) (v : Fin b.input.n) : ℕ := gradientBase b B+2*v.val
def sourceRecord (b : Core) (B : ℕ) : ℕ := gradientBase b B+2*b.input.n
def encodedEdge (b : Core) (e : Edge b) : ℕ := 2*(logicalIndexEquiv b e).val
def queueToken (b : Core) (e : Edge b) : ℕ := encodedEdge b e+2
lemma field_below_gradient (b : Core) (B : ℕ) (e : Edge b) (a : ℕ) (ha : a < 5) :
    field b B e a < gradientBase b B := by
  have he := (logicalIndexEquiv b e).isLt
  dsimp [field,gradientBase]
  omega
lemma gradient_below_source (b : Core) (B : ℕ) (v : Fin b.input.n) : gradientCell b B v < sourceRecord b B := by
  have hv := v.isLt
  dsimp [gradientCell,sourceRecord]
  omega
end DecrAlmostLinearSSSP.Decremental.CoreMemory
end CoreModule202
section CoreModule203
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
def addressAtoms : List Atom := [⟨.nadd 574 568 14,trivial⟩,⟨.nadd 576 574 14,trivial⟩,
  ⟨.nadd 578 576 14,trivial⟩,⟨.nadd 580 578 14,trivial⟩]
def addressCode : Cmd := Structured.sequence (addressAtoms.map Cmd.atom)
noncomputable def addressed (s : Data) : Data := addressAtoms.foldl (fun t a => a.effect t) s
def loadAtoms : List Atom := [⟨.load 600 568,trivial⟩,⟨.load 602 574,trivial⟩,⟨.load 604 576,trivial⟩,
  ⟨.load 606 580,trivial⟩,⟨.loadN 626 576,trivial⟩,⟨.loadN 628 578,trivial⟩,⟨.loadN 648 580,trivial⟩]
def loadCode : Cmd := Structured.sequence (loadAtoms.map Cmd.atom)
noncomputable def loaded (s : Data) : Data := loadAtoms.foldl (fun t a => a.effect t) s
def code : Cmd := .seq addressCode loadCode
noncomputable def result (s : Data) : Data := loaded (addressed s)
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end CoreModule203
section CoreModule204
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRecord
open Structured
def atoms : List Atom := [⟨.storeN 568 56,trivial⟩,⟨.storeN 574 56,trivial⟩,
  ⟨.storeN 576 626,trivial⟩,⟨.storeN 578 628,trivial⟩,⟨.storeN 580 648,trivial⟩,
  ⟨.store 568 612,trivial⟩,⟨.store 574 602,trivial⟩,⟨.store 576 604,trivial⟩,⟨.store 580 606,trivial⟩]
def code : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def result (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
structure Addresses (base : ℕ) (s : Data) : Prop where
  root : s.natReg 568 = base
  next : s.natReg 574 = base+2
  tail : s.natReg 576 = base+4
  head : s.natReg 578 = base+6
  flag : s.natReg 580 = base+8
end DecrAlmostLinearSSSP.Decremental.CoreRecord
end CoreModule204
section CoreModule205
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress
open Structured
def code : Cmd := .seq CorePending.prefixCode CoreGeometry.addressCode
noncomputable def result (s : Data) : Data := CoreGeometry.addressed (CorePending.prefixData s)
end DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress
end CoreModule205
section CoreModule206
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient
open Structured
def atoms : List Atom := [⟨.nadd 620 626 626,trivial⟩,⟨.nadd 620 554 620,trivial⟩,
  ⟨.loadN 662 620,trivial⟩,⟨.cast 602 662,trivial⟩,⟨.mul 602 504 602,trivial⟩]
def code : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def result (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient
end CoreModule206
section CoreModule207
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDegree
open Structured
attribute [local instance] Classical.propDecidable
def atoms (vertex : ℕ) : List Atom := [⟨.nadd 620 vertex vertex,trivial⟩,⟨.nadd 620 554 620,trivial⟩,
  ⟨.loadN 662 620,trivial⟩,⟨.nadd 662 662 26,trivial⟩,⟨.storeN 620 662,trivial⟩]
def code (vertex : ℕ) : Cmd := Structured.sequence ((atoms vertex).map Cmd.atom)
noncomputable def result (vertex : ℕ) (s : Data) : Data := (atoms vertex).foldl (fun t a => a.effect t) s
structure Image {n : ℕ} (base : ℕ) (heads : List (Fin n)) (s : Data) : Prop where
  entries : ∀ v, s.natMem (base+2*v.val) = heads.count v
end DecrAlmostLinearSSSP.Decremental.CoreDegree
end CoreModule207
section CoreModule215
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDegree
attribute [local instance] Classical.propDecidable
noncomputable def heads (b : Core) : ℕ → List (Fin b.input.n)
  | 0 => []
  | t+1 => if ht : t < b.input.k then b.input.graph.head ⟨t,ht⟩::heads b t else heads b t
def reverseGraph (b : Core) : Digraph b.input.n b.input.k := ⟨b.input.graph.head,b.input.graph.tail⟩
end DecrAlmostLinearSSSP.Decremental.CoreDegree
end CoreModule215
section CoreModule216
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreTape
open Structured
def atoms : List Atom := [⟨.loadN 626 652,trivial⟩,⟨.nadd 652 652 26,trivial⟩,
  ⟨.loadN 628 652,trivial⟩,⟨.nadd 652 652 26,trivial⟩,
  ⟨.loadN 654 652,trivial⟩,⟨.nadd 652 652 26,trivial⟩,
  ⟨.cast 604 654,trivial⟩,⟨.div 604 604 502,trivial⟩]
def code : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def result (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.CoreTape
end CoreModule216
section CoreModule217
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialDifference
open Structured
def ordinary : Cmd := add 606 56 56
def sourceTail : Cmd := sub 606 56 514
def code : Cmd := .branch (.natLess 626 72) ordinary (.branch (.natLess 72 626) ordinary sourceTail)
noncomputable def result (s : Data) : Data := {s with realReg := Function.update s.realReg 606 (if s.natReg 626 = s.natReg 72 then -s.realReg 514 else 0)}
end DecrAlmostLinearSSSP.Decremental.CoreInitialDifference
end CoreModule217
section CoreModule229
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
open Structured
def flagAtoms : List Atom := [⟨.rational 602 1,trivial⟩,⟨.natural 648 0,trivial⟩]
def flagCode : Cmd := Structured.sequence (flagAtoms.map Cmd.atom)
noncomputable def flagged (s : Data) : Data := flagAtoms.foldl (fun t a => a.effect t) s
def code : Cmd := .seq CoreTape.code (.seq CoreEdgeAddress.code (.seq flagCode CoreInitialDifference.code))
structure Loaded (b : Core) (B : ℕ) (e : Fin b.input.k) (s : Data) : Prop where
  addresses : CoreRecord.Addresses (CoreMemory.field b B (.inl e) 0) s
  tail : s.natReg 626 = (b.input.graph.tail e).val
  head : s.natReg 628 = (b.input.graph.head e).val
  coefficient : s.realReg 602 = 1
  cost : s.realReg 604 = (b.input.weight e : ℝ)/Q b
  initial : s.realReg 606 = initialLabel b (DecrAlmostLinearSSSP.Decremental.tail b (.inl e))-initialLabel b (DecrAlmostLinearSSSP.Decremental.head b (.inl e))
  returnFlag : s.natReg 648 = 0
  cursor : s.natReg 652 = b.input.n+3*(e.val+1)
end DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
end CoreModule229
section CoreModule230
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
def hAtoms : List Atom := [⟨.cast 500 66,trivial⟩,⟨.cast 502 70,trivial⟩,⟨.mul 500 500 502,trivial⟩,
  ⟨.rational 520 4,trivial⟩,⟨.mul 500 500 520,trivial⟩]
def qAtoms : List Atom := [⟨.cast 502 66,trivial⟩,⟨.mul 502 502 500,trivial⟩,
  ⟨.rational 520 8,trivial⟩,⟨.mul 502 502 520,trivial⟩]
def argumentAtoms : List Atom := [⟨.nadd 520 64 26,trivial⟩,⟨.cast 522 520,trivial⟩,⟨.log 522 522,trivial⟩,
  ⟨.rational 524 2,trivial⟩,⟨.log 524 524,trivial⟩,⟨.div 522 522 524,trivial⟩,
  ⟨.rational 524 32,trivial⟩,⟨.mul 522 522 524,trivial⟩,⟨.div 522 522 64,trivial⟩]
def hCode : Cmd := Structured.sequence (hAtoms.map Cmd.atom)
def qCode : Cmd := Structured.sequence (qAtoms.map Cmd.atom)
def argumentCode : Cmd := Structured.sequence (argumentAtoms.map Cmd.atom)
def header : Cmd := .seq hCode (.seq qCode argumentCode)
noncomputable def hData (s : Data) : Data := hAtoms.foldl (fun t a => a.effect t) s
noncomputable def qData (s : Data) : Data := qAtoms.foldl (fun t a => a.effect t) s
noncomputable def argumentData (s : Data) : Data := argumentAtoms.foldl (fun t a => a.effect t) s
noncomputable def headed (s : Data) : Data := argumentData (qData (hData s))
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end CoreModule230
section CoreModule231
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
def finishAtoms : List Atom := [
  ⟨.add 504 526 56,trivial⟩,⟨.cast 528 64,trivial⟩,⟨.mul 506 504 528,trivial⟩,
  ⟨.mul 506 506 502,trivial⟩,⟨.mul 506 506 506,trivial⟩,⟨.rational 530 1,trivial⟩,
  ⟨.div 506 530 506,trivial⟩,⟨.mul 508 506 506,trivial⟩,⟨.div 508 530 508,trivial⟩,
  ⟨.add 512 442 56,trivial⟩,⟨.mul 510 512 512,trivial⟩,⟨.div 510 530 510,trivial⟩,
  ⟨.rational 532 2,trivial⟩,⟨.mul 514 502 532,trivial⟩,⟨.div 514 530 514,trivial⟩,
  ⟨.div 516 500 502,trivial⟩,⟨.div 518 64 532,trivial⟩,⟨.add 518 530 518,trivial⟩,
  ⟨.mul 518 518 502,trivial⟩,⟨.div 534 500 532,trivial⟩,⟨.nsub 536 66 26,trivial⟩,
  ⟨.nadd 536 536 68,trivial⟩,⟨.nadd 540 64 64,trivial⟩]
def finish : Cmd := Structured.sequence (finishAtoms.map Cmd.atom)
noncomputable def finished (s : Data) : Data := finishAtoms.foldl (fun t a => a.effect t) s
structure Values (b : Core) (K : ℝ) (s : Data) : Prop where
  Hvalue : s.realReg 500 = H b
  Qvalue : s.realReg 502 = Q b
  Avalue : s.realReg 504 = A b
  kappaValue : s.realReg 506 = kappa b
  capacityBound : s.realReg 508 = (kappa b)^(-2 : ℤ)
  threshold : s.realReg 510 = K^(-2 : ℤ)
  quality : s.realReg 512 = K
  initial : s.realReg 514 = 1/(2*Q b)
  deletedCost : s.realReg 516 = H b/Q b
  readoutFactor : s.realReg 518 = (1+b.input.accuracy/2)*Q b
  infinityThreshold : s.realReg 534 = H b/2
  edgeCount : s.natReg 536 = logicalCount b
  cutSize : s.natReg 540 = 2*b.input.size
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end CoreModule231
section CoreModule232
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
lemma Values.frame (b : Core) (K : ℝ) {s t : Data} (h : Values b K s)
    (hn : ∀ k, k ∈ ([536,540] : List ℕ) → t.natReg k = s.natReg k)
    (hr : ∀ k, k ∈ ([500,502,504,506,508,510,512,514,516,518,534] : List ℕ) → t.realReg k = s.realReg k) :
    Values b K t := by
  exact ⟨(hr 500 (by simp)).trans h.Hvalue,(hr 502 (by simp)).trans h.Qvalue,
    (hr 504 (by simp)).trans h.Avalue,(hr 506 (by simp)).trans h.kappaValue,
    (hr 508 (by simp)).trans h.capacityBound,(hr 510 (by simp)).trans h.threshold,
    (hr 512 (by simp)).trans h.quality,(hr 514 (by simp)).trans h.initial,
    (hr 516 (by simp)).trans h.deletedCost,(hr 518 (by simp)).trans h.readoutFactor,
    (hr 534 (by simp)).trans h.infinityThreshold,(hn 536 (by simp)).trans h.edgeCount,
    (hn 540 (by simp)).trans h.cutSize⟩
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end CoreModule232
section CoreModule233
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreControl
open Structured
def atoms : List Atom := [⟨.nadd 542 536 536,trivial⟩,⟨.nadd 544 68 68,trivial⟩,
  ⟨.natural 546 0,trivial⟩,⟨.natural 550 0,trivial⟩,⟨.natural 650 1,trivial⟩,
  ⟨.nadd 552 74 26,trivial⟩,⟨.nadd 554 542 542,trivial⟩,⟨.nadd 554 554 554,trivial⟩,
  ⟨.nadd 554 554 542,trivial⟩,⟨.nadd 554 554 552,trivial⟩,
  ⟨.nadd 106 66 66,trivial⟩,⟨.nadd 106 106 554,trivial⟩,
  ⟨.natural 600 8,trivial⟩,⟨.nadd 50 106 600,trivial⟩,⟨.natural 112 2,trivial⟩,
  ⟨.rational 656 4,trivial⟩,⟨.rational 658 (-1),trivial⟩,⟨.mul 656 656 512,trivial⟩,⟨.div 520 658 656,trivial⟩]
def code : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def result (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
structure Layout (b : Core) (B : ℕ) (s : Data) : Prop where
  recordBase : s.natReg 552 = B+1
  gradientBase : s.natReg 554 = CoreMemory.gradientBase b B
  sourceRecord : s.natReg 106 = CoreMemory.sourceRecord b B
  savedBase : s.natReg 50 = CoreMemory.sourceRecord b B+8
  bankFactor : s.natReg 112 = 2
  edgeLimit : s.natReg 542 = 2*logicalCount b
  coreLimit : s.natReg 544 = 2*b.input.k
end DecrAlmostLinearSSSP.Decremental.CoreControl
end CoreModule233
section CoreModule234
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
lemma Captured.named_frame (i : Input) {s t : Data} (h : Captured i s)
    (hn : ∀ k, k ∈ ([56,26,14,34,36,64,66,68,70,72,74,48,58] : List ℕ) → t.natReg k = s.natReg k)
    (hr : ∀ k, k ∈ ([56,64,58] : List ℕ) → t.realReg k = s.realReg k) : Captured i t :=
  ⟨(hn 56 (by simp)).trans h.zeroN,(hr 56 (by simp)).trans h.zeroR,
    (hn 26 (by simp)).trans h.unit,(hn 14 (by simp)).trans h.two,
    (hn 34 (by simp)).trans h.scanZero,(hn 36 (by simp)).trans h.scanUnit,
    (hn 64 (by simp)).trans h.size,(hn 66 (by simp)).trans h.vertices,
    (hn 68 (by simp)).trans h.edges,(hn 70 (by simp)).trans h.weightBound,
    (hn 72 (by simp)).trans h.source,(hr 64 (by simp)).trans h.accuracy,
    (hn 74 (by simp)).trans h.base,(hn 48 (by simp)).trans h.utilityBase,
    (hn 58 (by simp)).trans h.factor,(hr 58 (by simp)).trans h.argument⟩
end DecrAlmostLinearSSSP.Decremental.InputCapture
end CoreModule234
section CoreModule235
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreControl
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreControl
end CoreModule235
section CoreModule236
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
end CoreModule236
section CoreModule237
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
def fieldAtoms : List Atom := [⟨.nadd 628 72 56,trivial⟩,⟨.natural 648 1,trivial⟩,
  ⟨.add 604 56 56,trivial⟩,⟨.add 606 514 56,trivial⟩]
def fieldCode : Cmd := Structured.sequence (fieldAtoms.map Cmd.atom)
noncomputable def fieldResult (s : Data) : Data := fieldAtoms.foldl (fun t a => a.effect t) s
def headerCode : Cmd := .seq CoreEdgeAddress.code (.seq CoreReturnCoefficient.code fieldCode)
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end CoreModule237
section CoreModule238
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRefresh
open Structured
def labelAtoms : List Atom := [⟨.sub 616 608 610,trivial⟩,⟨.add 616 616 606,trivial⟩,⟨.add 618 604 616,trivial⟩]
def labelCode : Cmd := Structured.sequence (labelAtoms.map Cmd.atom)
noncomputable def labelled (s : Data) : Data := labelAtoms.foldl (fun t a => a.effect t) s
def clipCode : Cmd := .branch (.realLess 618 506) (add 618 506 56) .skip
noncomputable def clipped (s : Data) : Data := {s with realReg := Function.update s.realReg 618 (max (s.realReg 618) (s.realReg 506))}
def finishAtoms : List Atom := [⟨.div 612 602 618,trivial⟩,⟨.sub 614 612 600,trivial⟩]
def finishCode : Cmd := Structured.sequence (finishAtoms.map Cmd.atom)
noncomputable def finished (s : Data) : Data := finishAtoms.foldl (fun t a => a.effect t) s
def code : Cmd := .seq labelCode (.seq clipCode finishCode)
noncomputable def result (s : Data) : Data := finished (clipped (labelled s))
end DecrAlmostLinearSSSP.Decremental.CoreRefresh
end CoreModule238
section CoreModule239
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
structure Loaded (b : Core) (B : ℕ) (v : ReturnVertex b) (s : Data) : Prop where
  addresses : CoreRecord.Addresses (CoreMemory.field b B (.inr v) 0) s
  coefficient : s.realReg 602 = DecrAlmostLinearSSSP.Decremental.coefficient b (.inr v)
  cost : s.realReg 604 = 0
  initial : s.realReg 606 = initialLabel b v.val-initialLabel b b.input.source
  tail : s.natReg 626 = v.val.val
  head : s.natReg 628 = b.input.source.val
  returnFlag : s.natReg 648 = 1
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end CoreModule239
section CoreModule240
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end CoreModule240
section CoreModule241
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
def returnBit (b : Core) : Edge b → ℕ
  | .inl _ => 0
  | .inr _ => 1
structure Image (b : Core) (B : ℕ) (state : State b) (s : Data) : Prop where
  cache : ∀ e, s.realMem (CoreMemory.field b B e 0) = state.cache e
  coefficient : ∀ e, s.realMem (CoreMemory.field b B e 1) = DecrAlmostLinearSSSP.Decremental.coefficient b e
  cost : ∀ e, s.realMem (CoreMemory.field b B e 2) = DecrAlmostLinearSSSP.Decremental.cost b state.active e
  initial : ∀ e, s.realMem (CoreMemory.field b B e 4) = initialLabel b (tail b e)-initialLabel b (head b e)
  tail : ∀ e, s.natMem (CoreMemory.field b B e 2) = (DecrAlmostLinearSSSP.Decremental.tail b e).val
  head : ∀ e, s.natMem (CoreMemory.field b B e 3) = (DecrAlmostLinearSSSP.Decremental.head b e).val
  returnFlag : ∀ e, s.natMem (CoreMemory.field b B e 4) = returnBit b e
  samples : ∀ v : ReturnVertex b, s.realMem (CoreMemory.field b B (.inr v) 3) = state.sample v.val
structure Loaded (b : Core) (state : State b) (e : Edge b) (s : Data) : Prop where
  oldCache : s.realReg 600 = state.cache e
  coefficient : s.realReg 602 = DecrAlmostLinearSSSP.Decremental.coefficient b e
  cost : s.realReg 604 = DecrAlmostLinearSSSP.Decremental.cost b state.active e
  initial : s.realReg 606 = initialLabel b (tail b e)-initialLabel b (head b e)
  tail : s.natReg 626 = (DecrAlmostLinearSSSP.Decremental.tail b e).val
  head : s.natReg 628 = (DecrAlmostLinearSSSP.Decremental.head b e).val
  returnFlag : s.natReg 648 = returnBit b e
lemma Image.frame (b : Core) (B : ℕ) (state : State b) {s t : Data} (h : Image b B state s)
    (hr : ∀ e j, j < 5 → t.realMem (CoreMemory.field b B e j) = s.realMem (CoreMemory.field b B e j))
    (hn : ∀ e j, j < 5 → t.natMem (CoreMemory.field b B e j) = s.natMem (CoreMemory.field b B e j)) : Image b B state t := by
  exact ⟨fun e => (hr e 0 (by omega)).trans (h.cache e),
    fun e => (hr e 1 (by omega)).trans (h.coefficient e),
    fun e => (hr e 2 (by omega)).trans (h.cost e),
    fun e => (hr e 4 (by omega)).trans (h.initial e),
    fun e => (hn e 2 (by omega)).trans (h.tail e),
    fun e => (hn e 3 (by omega)).trans (h.head e),
    fun e => (hn e 4 (by omega)).trans (h.returnFlag e),
    fun v => (hr (.inr v) 3 (by omega)).trans (h.samples v)⟩
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end CoreModule241
section CoreModule242
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRecord
open Structured
structure Initialized (b : Core) (B : ℕ) (e : Edge b) (s : Data) : Prop where
  mark : s.natMem (CoreMemory.field b B e 0) = 0
  next : s.natMem (CoreMemory.field b B e 1) = 0
  tail : s.natMem (CoreMemory.field b B e 2) = (DecrAlmostLinearSSSP.Decremental.tail b e).val
  head : s.natMem (CoreMemory.field b B e 3) = (DecrAlmostLinearSSSP.Decremental.head b e).val
  returnFlag : s.natMem (CoreMemory.field b B e 4) = CoreGeometry.returnBit b e
  capacity : s.realMem (CoreMemory.field b B e 0) = DecrAlmostLinearSSSP.Decremental.capacity b Finset.univ (initialLabel b) e
  coefficient : s.realMem (CoreMemory.field b B e 1) = DecrAlmostLinearSSSP.Decremental.coefficient b e
  cost : s.realMem (CoreMemory.field b B e 2) = DecrAlmostLinearSSSP.Decremental.cost b Finset.univ e
  initial : s.realMem (CoreMemory.field b B e 4) = initialLabel b (DecrAlmostLinearSSSP.Decremental.tail b e)-initialLabel b (DecrAlmostLinearSSSP.Decremental.head b e)
  sample : match e with | .inl _ => True | .inr v => s.realMem (CoreMemory.field b B e 3) = initialLabel b v.val
end DecrAlmostLinearSSSP.Decremental.CoreRecord
end CoreModule242
section CoreModule243
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CoreOutput
open Structured
def clampCode : Cmd := .branch (.realLess 624 56) (add 624 56 56) .skip
noncomputable def clamped (s : Data) : Data := {s with realReg := Function.update s.realReg 624 (max 0 (s.realReg 624))}
def finitePrefix : List Atom := [⟨.natural 622 0,trivial⟩,⟨.mul 624 518 616,trivial⟩]
noncomputable def finitePrepared (s : Data) : Data := finitePrefix.foldl (fun t a => a.effect t) s
def finiteCode : Cmd := .seq (Structured.sequence (finitePrefix.map Cmd.atom))
  (.seq clampCode (Structured.sequence [store 620 624,storeN 620 622]))
noncomputable def finiteResult (s : Data) : Data :=
  let t := clamped (finitePrepared s)
  {t with
    realMem := Function.update t.realMem (t.natReg 620) (t.realReg 624),
    natMem := Function.update t.natMem (t.natReg 620) (t.natReg 622)}
def infiniteCode : Cmd := Structured.sequence [natural 622 1,storeN 620 622]
noncomputable def infiniteResult (s : Data) : Data :=
  {s with
    natReg := Function.update s.natReg 622 1,
    natMem := Function.update s.natMem (s.natReg 620) 1}
def code : Cmd := .seq (mul 620 502 616) (.branch (.realLess 534 620) infiniteCode finiteCode)
end DecrAlmostLinearSSSP.Decremental.CoreOutput
end CoreModule243
section CoreModule244
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreOutput
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreOutput
end CoreModule244
section CoreModule245
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReturn
open Structured
def code : Cmd := .seq (store 578 616) (.seq (nadd 620 626 56) CoreOutput.code)
end DecrAlmostLinearSSSP.Decremental.CoreReturn
end CoreModule245
section CoreModule246
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
def storeCode : Cmd := .seq CoreRefresh.code (.seq CoreRecord.code CoreReturn.code)
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end CoreModule246
section CoreModule247
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNonzero
open Structured
def code (source target : ℕ) : Cmd := .branch (.realLess source 56) (natural target 1)
  (.branch (.realLess 56 source) (natural target 1) (natural target 0))
noncomputable def result (source target : ℕ) (s : Data) : Data :=
  {s with natReg := Function.update s.natReg target (nonzero (s.realReg source))}
end DecrAlmostLinearSSSP.Decremental.CoreNonzero
end CoreModule247
section CoreModule248
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradient
open Structured
def prefixAtoms : List Atom := [⟨.load 628 620,trivial⟩,⟨.add 630 628 626,trivial⟩]
def prefixCode : Cmd := Structured.sequence (prefixAtoms.map Cmd.atom)
noncomputable def prepared (s : Data) : Data := prefixAtoms.foldl (fun t a => a.effect t) s
def suffixAtoms : List Atom := [⟨.nadd 550 550 634,trivial⟩,⟨.nsub 550 550 632,trivial⟩,⟨.store 620 630,trivial⟩]
def suffixCode : Cmd := Structured.sequence (suffixAtoms.map Cmd.atom)
noncomputable def finished (s : Data) : Data := suffixAtoms.foldl (fun t a => a.effect t) s
def code : Cmd := .seq prefixCode (.seq (CoreNonzero.code 628 632)
  (.seq (CoreNonzero.code 630 634) suffixCode))
noncomputable def result (s : Data) : Data := finished
  (CoreNonzero.result 630 634 (CoreNonzero.result 628 632 (prepared s)))
end DecrAlmostLinearSSSP.Decremental.CoreGradient
end CoreModule248
section CoreModule249
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradient
open Structured
attribute [local instance] Classical.propDecidable
structure Image {n : ℕ} (base : ℕ) (g : Fin n → ℝ) (s : Data) : Prop where
  entries : ∀ v, s.realMem (base+2*v.val) = g v
  count : s.natReg 550 = ∑ v, nonzero (g v)
lemma Image.frame {n : ℕ} (base : ℕ) (g : Fin n → ℝ) {s t : Data} (h : Image base g s)
    (hr : ∀ v : Fin n, t.realMem (base+2*v.val) = s.realMem (base+2*v.val))
    (hc : t.natReg 550 = s.natReg 550) : Image base g t :=
  ⟨fun v => (hr v).trans (h.entries v),hc.trans h.count⟩
end DecrAlmostLinearSSSP.Decremental.CoreGradient
end CoreModule249
section CoreModule250
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints
open Structured
def tailAtoms : List Atom := [⟨.nadd 620 626 626,trivial⟩,⟨.nadd 620 554 620,trivial⟩,⟨.sub 626 56 612,trivial⟩]
def headAtoms : List Atom := [⟨.nadd 620 628 628,trivial⟩,⟨.nadd 620 554 620,trivial⟩,⟨.add 626 612 56,trivial⟩]
def tailCode : Cmd := Structured.sequence (tailAtoms.map Cmd.atom)
def headCode : Cmd := Structured.sequence (headAtoms.map Cmd.atom)
noncomputable def tailPrepared (s : Data) : Data := tailAtoms.foldl (fun t a => a.effect t) s
noncomputable def headPrepared (s : Data) : Data := headAtoms.foldl (fun t a => a.effect t) s
def code : Cmd := .seq tailCode (.seq CoreGradient.code (.seq headCode CoreGradient.code))
end DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints
end CoreModule250
section CoreModule251
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints
end CoreModule251
section CoreModule252
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
def evenDestination : Instruction → Bool
  | .rational d _ | .natural d _ | .cast d _ | .add d _ _ | .sub d _ _
  | .mul d _ _ | .div d _ _ | .log d _ | .nadd d _ _ | .nsub d _ _ | .load d _ | .loadN d _ => d%2 == 0
  | _ => true
def evenRegisters : Cmd → Bool
  | .skip => true
  | .atom a => evenDestination a.instruction
  | .seq a b | .branch _ a b => evenRegisters a && evenRegisters b
  | .loop _ a => evenRegisters a
end DecrAlmostLinearSSSP.Decremental.Structured
end CoreModule252
section CoreModule253
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
def advanceAtoms : List Atom := [⟨.nadd 560 560 14,trivial⟩,⟨.nadd 626 626 26,trivial⟩]
def advanceCode : Cmd := Structured.sequence (advanceAtoms.map Cmd.atom)
def nonsourceCode : Cmd := .seq headerCode (.seq storeCode (.seq CoreGradientEndpoints.code advanceCode))
def skipSource : Cmd := nadd 626 626 26
def body : Cmd := .branch (.natLess 626 72) nonsourceCode (.branch (.natLess 72 626) nonsourceCode skipSource)
def loop : Cmd := .loop (.natLess 626 66) body
def code : Cmd := .seq (natural 626 0) loop
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end CoreModule253
section CoreModule254
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
noncomputable def advanced (s : Data) : Data := advanceAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end CoreModule254
section CoreModule255
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreMemory
open Structured
def Protected (b : Core) (B j : ℕ) : Prop :=
  (∀ e : Edge b, ∀ offset < 5, j ≠ field b B e offset) ∧
    (∀ v : Fin b.input.n, j ≠ gradientCell b B v)
def Frame (b : Core) (B : ℕ) (s t : Data) : Prop :=
  ∀ j, Protected b B j → t.natMem j = s.natMem j ∧ t.realMem j = s.realMem j
def EdgeFrame (b : Core) (B : ℕ) (e : Edge b) (s t : Data) : Prop :=
  ∀ j, (∀ offset < 5, j ≠ field b B e offset) →
    j ≠ gradientCell b B (tail b e) → j ≠ gradientCell b B (head b e) →
    t.natMem j = s.natMem j ∧ t.realMem j = s.realMem j
end DecrAlmostLinearSSSP.Decremental.CoreMemory
end CoreModule255
section CoreModule256
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreMemory
open Structured
def ReturnEdgeFrame (b : Core) (B : ℕ) (v : ReturnVertex b) (s t : Data) : Prop :=
  ∀ j, j ≠ v.val.val → (∀ offset < 5, j ≠ field b B (.inr v) offset) →
    j ≠ gradientCell b B v.val → j ≠ gradientCell b B b.input.source →
    t.natMem j = s.natMem j ∧ t.realMem j = s.realMem j
def ReturnFrame (b : Core) (B : ℕ) (s t : Data) : Prop :=
  ∀ j, Protected b B j → b.input.n ≤ j → t.natMem j = s.natMem j ∧ t.realMem j = s.realMem j
end DecrAlmostLinearSSSP.Decremental.CoreMemory
end CoreModule256
section CoreModule257
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def initialContribution (b : Core) (e : Edge b) (v : Fin b.input.n) : ℝ :=
  (if head b e = v then capacity b Finset.univ (initialLabel b) e else 0)-
    (if tail b e = v then capacity b Finset.univ (initialLabel b) e else 0)
noncomputable def initialGradientThrough (b : Core) (t : ℕ) (v : Fin b.input.n) : ℝ :=
  ∑ j ∈ Finset.range t, if hj : j < logicalCount b then
    initialContribution b ((logicalIndexEquiv b).symm ⟨j,hj⟩) v else 0
end DecrAlmostLinearSSSP.Decremental
end CoreModule257
section CoreModule258
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end CoreModule258
section CoreModule259
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
structure InitialPublic (b : Core) (upto : ℕ) (s : Data) : Prop where
  sourceNat : s.natMem b.input.source.val = 0
  sourceReal : s.realMem b.input.source.val = 0
  answers : ∀ u : Fin b.input.n, u.val < upto → u ≠ b.input.source →
    stored s.machine u.val = readout b (initialLabel b u)
  normal : ∀ u : Fin b.input.n, u.val < upto → s.natMem u.val ≤ 1 ∧ (s.natMem u.val = 0 → 0 ≤ s.realMem u.val)
lemma stored_memory_congr (s t : Data) (j : ℕ) (hn : t.natMem j = s.natMem j) (hr : t.realMem j = s.realMem j) :
    stored t.machine j = stored s.machine j := by
  unfold stored
  change (if t.natMem j = 1 then ⊤ else ENNReal.ofReal (t.realMem j)) =
    (if s.natMem j = 1 then ⊤ else ENNReal.ofReal (s.realMem j))
  rw [hn,hr]
end DecrAlmostLinearSSSP.Decremental
end CoreModule259
section CoreModule260
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def returnsBefore (b : Core) (upto : ℕ) : ℕ := upto-(if b.input.source.val < upto then 1 else 0)
end DecrAlmostLinearSSSP.Decremental
end CoreModule260
section CoreModule261
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreControl
open Structured
lemma Layout.frame (b : Core) (B : ℕ) {s t : Data} (h : Layout b B s)
    (hf : ∀ k, k ∈ ([552,554,106,50,112,542,544] : List ℕ) → t.natReg k = s.natReg k) : Layout b B t :=
  ⟨(hf 552 (by simp)).trans h.recordBase,(hf 554 (by simp)).trans h.gradientBase,
    (hf 106 (by simp)).trans h.sourceRecord,(hf 50 (by simp)).trans h.savedBase,
    (hf 112 (by simp)).trans h.bankFactor,(hf 542 (by simp)).trans h.edgeLimit,
    (hf 544 (by simp)).trans h.coreLimit⟩
end DecrAlmostLinearSSSP.Decremental.CoreControl
end CoreModule261
section CoreModule262
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
structure Invariant (b : Core) (B : ℕ) (K : ℝ) (upto : ℕ) (s : Data) : Prop where
  bound : upto ≤ b.input.n
  captured : InputCapture.Captured b.input s
  parameters : CoreParameters.Values b K s
  layout : CoreControl.Layout b B s
  vertex : s.natReg 626 = upto
  counter : s.natReg 560 = 2*(b.input.k+returnsBefore b upto)
  degrees : ∀ u, s.natMem (CoreMemory.gradientCell b B u) = indegree b u
  gradient : CoreGradient.Image (CoreMemory.gradientBase b B) (initialGradientThrough b (b.input.k+returnsBefore b upto)) s
  cores : ∀ e : Fin b.input.k, CoreRecord.Initialized b B (.inl e) s
  returns : ∀ v : ReturnVertex b, v.val.val < upto → CoreRecord.Initialized b B (.inr v) s
  publicArray : InitialPublic b upto s
  yTail : s.realReg 608 = 0
  yHead : s.realReg 610 = 0
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end CoreModule262
section CoreModule263
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end CoreModule263
section CoreModule264
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end CoreModule264
section CoreModule265
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
def code : Cmd := .seq CoreInitializeHeader.code (.seq CoreRefresh.code
  (.seq CoreRecord.code (.seq (CoreDegree.code 628) (.seq CoreGradientEndpoints.code (nadd 560 560 14)))))
def loop : Cmd := .loop (.natLess 560 544) code
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end CoreModule265
section CoreModule266
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end CoreModule266
section CoreModule267
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end CoreModule267
section CoreModule268
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
end CoreModule268
section CoreModule269
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeStore
open Structured
def code : Cmd := .seq CoreRefresh.code CoreRecord.code
noncomputable def result (s : Data) : Data := CoreRecord.result (CoreRefresh.result s)
end DecrAlmostLinearSSSP.Decremental.CoreInitializeStore
end CoreModule269
section CoreModule270
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions
open Structured
def code : Cmd := .seq (CoreDegree.code 628) (.seq CoreGradientEndpoints.code (nadd 560 560 14))
end DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions
end CoreModule270
section CoreModule271
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end CoreModule271
section CoreModule272
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end CoreModule272
section CoreModule273
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
structure Invariant (b : Core) (B : ℕ) (K : ℝ) (upto : ℕ) (s : Data) : Prop where
  bound : upto ≤ b.input.k
  captured : InputCapture.Captured b.input s
  parameters : CoreParameters.Values b K s
  layout : CoreControl.Layout b B s
  tape : Exact.Adjacency.Tape b.input s
  counter : s.natReg 560 = 2*upto
  cursor : s.natReg 652 = b.input.n+3*upto
  records : ∀ e : Fin b.input.k, e.val < upto → CoreRecord.Initialized b B (.inl e) s
  degrees : CoreDegree.Image (CoreMemory.gradientBase b B) (CoreDegree.heads b upto) s
  gradient : CoreGradient.Image (CoreMemory.gradientBase b B) (initialGradientThrough b upto) s
  yTail : s.realReg 608 = 0
  yHead : s.realReg 610 = 0
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end CoreModule273
section CoreModule274
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end CoreModule274
section CoreModule275
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
def startAtoms : List Atom := [⟨.natural 560 0,trivial⟩,⟨.nadd 652 66 56,trivial⟩,
  ⟨.rational 608 0,trivial⟩,⟨.rational 610 0,trivial⟩]
def startCode : Cmd := Structured.sequence (startAtoms.map Cmd.atom)
noncomputable def started (s : Data) : Data := startAtoms.foldl (fun t a => a.effect t) s
def corePassCode : Cmd := .seq startCode loop
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end CoreModule275
section CoreModule276
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end CoreModule276
section CoreModule277
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
def recordsCode : Cmd := .seq CoreInitializeEdge.corePassCode CoreInitializeReturn.code
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end CoreModule277
section CoreModule278
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
namespace DecrAlmostLinearSSSP.Decremental.CorePending
end DecrAlmostLinearSSSP.Decremental.CorePending
end CoreModule278
section CoreModule279
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CorePending
open Structured
attribute [local instance] Classical.propDecidable
def popCode : Cmd := .seq (nsub 560 546 14) (.seq prefixCode
  (Structured.sequence [loadN 546 572,storeN 568 56]))
noncomputable def popped (s : Data) : Data := {s with
  natReg := Function.update s.natReg 546 (s.natMem (s.natReg 572))
  natMem := Function.update s.natMem (s.natReg 568) 0}
end DecrAlmostLinearSSSP.Decremental.CorePending
end CoreModule279
section CoreModule280
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CorePending
open Structured
lemma View.frame {l B : ℕ} {xs : List (Fin l)} {s t : Data} (h : View B xs s)
    (hh : t.natReg 546 = s.natReg 546)
    (hm : ∀ e : Fin l, ∀ a < 2, t.natMem (address B e a) = s.natMem (address B e a)) : View B xs t := by
  refine ⟨h.nodup,fun e => (hm e 0 (by omega)).trans (h.flags e),hh.trans h.head,?_⟩
  exact h.links.congr (fun e _ => hm e 1 (by omega))
def MemoryFrame (B l : ℕ) (s t : Data) : Prop :=
  ∀ j, (∀ e : Fin l, j ≠ address B e 0 ∧ j ≠ address B e 1) → t.natMem j = s.natMem j
end DecrAlmostLinearSSSP.Decremental.CorePending
end CoreModule280
section CoreModule281
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
def Address (b : Core) (B j : ℕ) : Prop :=
  j < B ∨ (∃ r, j = B+2*r+1 ∧ j < CoreMemory.sourceRecord b B)
def NatRegisters : List ℕ := [14,26,34,36,48,50,56,58,64,66,68,70,72,74,106,112,536,540,542,544,546,550,552,554]
def RealRegisters : List ℕ := [56,58,64,500,502,504,506,508,510,512,514,516,518,534]
structure Image (b : Core) (B : ℕ) (K : ℝ) (state : State b) (s : Data) : Prop where
  captured : InputCapture.Captured b.input s
  parameters : CoreParameters.Values b K s
  layout : CoreControl.Layout b B s
  base : s.natReg 74 = B
  geometry : CoreGeometry.Image b B state s
  gradient : CoreGradient.Image (CoreMemory.gradientBase b B) state.cachedGradient s
  pending : CorePending.View B (state.pending.map (logicalIndexEquiv b)) s
  answers : ∀ v : Fin b.input.n, stored s.machine v.val = state.output v
  normal : ∀ v : Fin b.input.n, s.natMem v.val ≤ 1 ∧ (s.natMem v.val = 0 → 0 ≤ s.realMem v.val)
lemma address_field (b : Core) (B : ℕ) (e : Edge b) (offset : ℕ) (ho : offset < 5) :
    Address b B (CoreMemory.field b B e offset) := by
  right
  refine ⟨5*(logicalIndexEquiv b e).val+offset,?_,?_⟩
  · dsimp [CoreMemory.field];omega
  · exact (CoreMemory.field_below_gradient b B e offset ho).trans_le (by dsimp [CoreMemory.sourceRecord];omega)
lemma address_gradient (b : Core) (B : ℕ) (v : Fin b.input.n) : Address b B (CoreMemory.gradientCell b B v) := by
  right
  exact ⟨5*logicalCount b+v.val,by dsimp [CoreMemory.gradientCell,CoreMemory.gradientBase];omega,
    CoreMemory.gradient_below_source b B v⟩
lemma address_pending (b : Core) (B : ℕ) (e : Fin (logicalCount b)) (offset : ℕ) (ho : offset < 2) :
    Address b B (CorePending.address B e offset) := by
  have hh := address_field b B ((logicalIndexEquiv b).symm e) offset (by omega)
  simpa [CorePending.address,CoreMemory.field] using hh
lemma Image.frame (b : Core) (B : ℕ) (K : ℝ) (state : State b) {s t : Data}
    (h : Image b B K state s) (hB : b.input.n ≤ B)
    (hn : ∀ k, k ∈ NatRegisters → t.natReg k = s.natReg k)
    (hr : ∀ k, k ∈ RealRegisters → t.realReg k = s.realReg k)
    (hm : ∀ address, Address b B address → t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) :
    Image b B K state t := by
  have hn' (k : ℕ) (hk : k ∈ ([56,26,14,34,36,64,66,68,70,72,74,48,58] : List ℕ)) : t.natReg k = s.natReg k := hn k ((by simp [List.Subset,NatRegisters] : ([56,26,14,34,36,64,66,68,70,72,74,48,58] : List ℕ).Subset NatRegisters) hk)
  have hr' (k : ℕ) (hk : k ∈ ([56,64,58] : List ℕ)) : t.realReg k = s.realReg k := hr k ((by simp [List.Subset,RealRegisters] : ([56,64,58] : List ℕ).Subset RealRegisters) hk)
  have hpub (v : Fin b.input.n) := hm v.val (Or.inl (by have hh := v.isLt;omega))
  refine ⟨h.captured.named_frame b.input hn' hr',
    h.parameters.frame b K (fun k hk => hn k ((by simp [List.Subset,NatRegisters] : ([536,540] : List ℕ).Subset NatRegisters) hk))
      (fun k hk => hr k ((by simp [List.Subset,RealRegisters] : ([500,502,504,506,508,510,512,514,516,518,534] : List ℕ).Subset RealRegisters) hk)),
    h.layout.frame b B (fun k hk => hn k ((by simp [List.Subset,NatRegisters] : ([552,554,106,50,112,542,544] : List ℕ).Subset NatRegisters) hk)),
    (hn 74 (by simp [NatRegisters])).trans h.base,
    h.geometry.frame b B state (fun e j hj => (hm _ (address_field b B e j hj)).2)
      (fun e j hj => (hm _ (address_field b B e j hj)).1),
    h.gradient.frame _ _ (fun v => (hm _ (address_gradient b B v)).2) (hn 550 (by simp [NatRegisters])),
    h.pending.frame (hn 546 (by simp [NatRegisters]))
      (fun e j hj => (hm _ (address_pending b B e j hj)).1),
    fun v => (stored_memory_congr s t v.val (hpub v).1 (hpub v).2).trans (h.answers v),?_⟩
  intro v
  simpa only [(hpub v).1,(hpub v).2] using h.normal v
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule281
section CoreModule282
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end CoreModule282
section CoreModule283
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
noncomputable def endpoints (s : Data) : Data :=
  {s with natReg := Function.update (Function.update s.natReg 636 (s.natReg 626+s.natReg 626)) 638 (s.natReg 628+s.natReg 628)}
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end CoreModule283
section CoreModule284
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule284
section CoreModule285
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
def Preserves (b : Core) (B : ℕ) (K : ℝ) (state : State b) (cmd : Cmd) : Prop :=
  ∀ s cost t, Image b B K state s → Eval cmd s cost t → Image b B K state t
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule285
section CoreModule286
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule286
section CoreModule287
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule287
section CoreModule288
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end CoreModule288
section CoreModule289
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
structure Context (b : Core) (B N m exponent : ℕ) (impl : CutImplementation)
    (K0 ξ h Γ init : ℝ) (s : Data) where
  first : Machine
  current : Machine
  ops : List (CutOp b.input.n (logicalCount b))
  machines : List Machine
  session : CutSession impl b.input.n (logicalCount b) m exponent first K0 ξ h Γ init
  run : CutRun impl b.input.n (logicalCount b) m exponent first ops machines
  last : machines.getLast? = some current
  zeroTail : ZeroRegisterTail N current
  image : CoreSource.Image B (CoreMemory.sourceRecord b B) N current s
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule289
section CoreModule290
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def queryCode (N source : ℕ) (p : Program) : Cmd :=
  .seq (CoreRequest.queryCode source) (SourceCall.code N p.update p)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule290
section CoreModule291
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
lemma Image.frame (B R N : ℕ) (g : Machine) {s t : Data} (h : Image B R N g s)
    (hn : ∀ k, k ∈ ([74,112,106,50,56] : List ℕ) → t.natReg k = s.natReg k)
    (htail : ∀ j, N ≤ j → t.natReg (shadowReg j) = s.natReg (shadowReg j) ∧ t.realReg (shadowReg j) = s.realReg (shadowReg j))
    (hguest : ∀ a, t.natMem (B+2*(2*a+1)) = s.natMem (B+2*(2*a+1)) ∧
      t.realMem (B+2*(2*a+1)) = s.realMem (B+2*(2*a+1)))
    (hwork : t.natMem (R+6) = s.natMem (R+6))
    (hsaved : ∀ j < N, t.natMem (R+8+2*j) = s.natMem (R+8+2*j) ∧ t.realMem (R+8+2*j) = s.realMem (R+8+2*j)) :
    Image B R N g t := by
  refine ⟨(hn 74 (by simp)).trans h.base,(hn 112 (by simp)).trans h.factor,
    (hn 106 (by simp)).trans h.record,(hn 50 (by simp)).trans h.savedBase,
    (hn 56 (by simp)).trans h.zero,fun a => (hguest a).2.trans (h.realMem a),
    fun a => (hguest a).1.trans (h.natMem a),hwork.trans h.work,?_,?_⟩
  · constructor
    · intro j hj
      rw [hn 50 (by simp),h.savedBase,(hsaved j hj).1]
      simpa only [h.savedBase] using h.saved.nat j hj
    · intro j hj
      rw [hn 50 (by simp),h.savedBase,(hsaved j hj).2]
      simpa only [h.savedBase] using h.saved.real j hj
  · intro j hj
    exact ⟨(htail j hj).1.trans (h.tail j hj).1,(htail j hj).2.trans (h.tail j hj).2⟩
end DecrAlmostLinearSSSP.Decremental.CoreSource
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def Context.of_image {b : Core} {B N m exponent : ℕ} {K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {s t : Data} (ctx : Context b B N m exponent impl K0 ξ h Γ init s)
    (ht : CoreSource.Image B (CoreMemory.sourceRecord b B) N ctx.current t) :
    Context b B N m exponent impl K0 ξ h Γ init t :=
  ⟨ctx.first,ctx.current,ctx.ops,ctx.machines,ctx.session,ctx.run,ctx.last,ctx.zeroTail,ht⟩
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule291
section CoreModule292
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule292
section CoreModule293
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def captureQueryCode (N source dest : ℕ) (p : Program) : Cmd := .seq (queryCode N source p) (add dest 29 56)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule293
section CoreModule294
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule294
section CoreModule295
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def indexedPhysical (b : Core) (s : State b) {l : ℕ} (E : Edge b ≃ Fin l) : Physical b.input.n l :=
  {graph := ⟨fun e => tail b (E.symm e),fun e => head b (E.symm e)⟩
   active := Finset.univ
   u := fun e => s.cache (E.symm e)
   gamma := s.cachedGradient}
end DecrAlmostLinearSSSP.Decremental
end CoreModule295
section CoreModule296
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule296
section CoreModule297
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
structure CutModel (b : Core) {l : ℕ} (E : Edge b ≃ Fin l) (s : State b) (c : CutState b.input.n l) : Prop where
  physical : c.physical = indexedPhysical b s E
  y : c.y = s.y
  baseline : ∀ e, e ∉ s.pending → c.baseline (E e) = s.baseline e
noncomputable def modelReply (b : Core) {l : ℕ} (c : CutState b.input.n l) : CutReply b :=
  ⟨c.lastG,c.lastU,c.lastCut⟩
end DecrAlmostLinearSSSP.Decremental
end CoreModule297
section CoreModule298
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def labelsCode (N : ℕ) (p : Program) : Cmd :=
  .seq (captureQueryCode N 636 608 p) (captureQueryCode N 638 610 p)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule298
section CoreModule299
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def eraseCode (N : ℕ) (p : Program) : Cmd := .seq CoreRequest.eraseCode (SourceCall.code N p.update p)
def insertCode (N : ℕ) (p : Program) : Cmd := .seq CoreRequest.insertCode (SourceCall.code N p.update p)
def pairedCode (N : ℕ) (p : Program) : Cmd := .seq CoreRequest.pairedCode (SourceCall.code N p.update p)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule299
section CoreModule300
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule300
section CoreModule301
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule301
section CoreModule302
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule302
section CoreModule303
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule303
section CoreModule304
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule304
section CoreModule305
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule305
section CoreModule306
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule306
section CoreModule307
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule307
section CoreModule308
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule308
section CoreModule309
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule309
section CoreModule310
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
structure RuntimeBounds (b : Core) (K : ℝ) (s : State b) : Prop where
  invariant : RuntimeInvariant b K s
  lower : ∀ e, 1 ≤ s.cache e
end DecrAlmostLinearSSSP.Decremental
end CoreModule310
section CoreModule311
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule311
section CoreModule312
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule312
section CoreModule313
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule313
section CoreModule314
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule314
section CoreModule315
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule315
section CoreModule316
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule316
section CoreModule317
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule317
section CoreModule318
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule318
section CoreModule319
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule319
section CoreModule320
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def RefreshValidity (b : Core) (s : State b) (e : Edge b) : Prop :=
  let E := logicalIndexEquiv b
  let before := indexedPhysical b s E
  let erased := applyPhysical before (.erase (E e))
  let inserted := applyPhysical erased (.insert (E e) (tail b e) (head b e) (capacity b s.active (labels b s) e))
  let paired := applyPhysical inserted (.paired (head b e) (tail b e) (capacity b s.active (labels b s) e-s.cache e))
  erased.Valid (2*b.input.size) (4*b.weightExponent+68) ∧
    inserted.Valid (2*b.input.size) (4*b.weightExponent+68) ∧
    paired = indexedPhysical b (refresh b s e) E ∧ paired.Valid (2*b.input.size) (4*b.weightExponent+68)
end DecrAlmostLinearSSSP.Decremental
end CoreModule320
section CoreModule321
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def physicalRefreshCode (N : ℕ) (p : Program) : Cmd := .seq (eraseCode N p) (.seq (insertCode N p) (pairedCode N p))
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule321
section CoreModule322
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end CoreModule322
section CoreModule323
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule323
section CoreModule324
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRefreshRead
open Structured
def code : Cmd := .seq CorePending.prefixCode (.seq CoreGeometry.code CoreRequest.endpointCode)
noncomputable def result (s : Data) : Data := CoreRequest.endpoints (CoreGeometry.result (CorePending.prefixData s))
end DecrAlmostLinearSSSP.Decremental.CoreRefreshRead
end CoreModule324
section CoreModule325
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRefresh
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRefresh
end CoreModule325
section CoreModule326
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end CoreModule326
section CoreModule327
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule327
section CoreModule328
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradientDelta
open Structured
def code : Cmd := .seq (add 698 612 56) (.seq (add 612 614 56)
  (.seq CoreGradientEndpoints.code (add 612 698 56)))
end DecrAlmostLinearSSSP.Decremental.CoreGradientDelta
end CoreModule328
section CoreModule329
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule329
section CoreModule330
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end CoreModule330
section CoreModule331
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule331
section CoreModule332
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule332
section CoreModule333
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end CoreModule333
section CoreModule334
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
noncomputable def cacheGradientState (b : Core) (state : State b) (e : Edge b) (f delta : ℝ) : State b :=
  {state with cache := Function.update state.cache e f, cachedGradient := fun v => state.cachedGradient v-(if v = tail b e then delta else 0)+(if v = head b e then delta else 0)}
def prefixCode : Cmd := .seq (store 568 612) CoreGradientDelta.code
end DecrAlmostLinearSSSP.Decremental.CoreCommit
end CoreModule334
section CoreModule335
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end CoreModule335
section CoreModule336
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule336
section CoreModule337
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
noncomputable def returnState (b : Core) (state : State b) : Edge b → State b
  | .inl _ => state
  | .inr v => {state with sample := Function.update state.sample v.val (labels b state v.val), output := Function.update state.output v.val (readout b (labels b state v.val))}
def returnCode : Cmd := .branch (.natLess 56 648) CoreReturn.code .skip
end DecrAlmostLinearSSSP.Decremental.CoreCommit
end CoreModule337
section CoreModule338
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
def headCode : Cmd := .seq prefixCode (.seq returnCode CorePending.popCode)
end DecrAlmostLinearSSSP.Decremental.CoreCommit
end CoreModule338
section CoreModule339
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def refreshCode (N : ℕ) (p : Program) : Cmd := .seq CoreRefreshRead.code
  (.seq (labelsCode N p) (.seq CoreRefresh.code (.seq (physicalRefreshCode N p) CoreCommit.headCode)))
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule339
section CoreModule340
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHeadSelect
open Structured
def code : Cmd := nsub 560 546 14
noncomputable def result (s : Data) : Data := {s with natReg := Function.update s.natReg 560 (s.natReg 546-s.natReg 14)}
end DecrAlmostLinearSSSP.Decremental.CoreHeadSelect
end CoreModule340
section CoreModule341
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def drainOneCode (N : ℕ) (p : Program) : Cmd := .seq CoreHeadSelect.code (refreshCode N p)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule341
section CoreModule342
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCommit
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule342
section CoreModule343
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
structure Environment (B l : ℕ) (s : Data) : Prop where
  base : s.natReg 74 = B
  geometry : s.natReg 552 = B+1
  two : s.natReg 14 = 2
  one : s.natReg 26 = 1
  limit : s.natReg 542 = 2*l
def fetchAtoms : List Atom := [⟨.nadd 584 580 580,trivial⟩,⟨.nadd 584 74 584,trivial⟩,
  ⟨.nadd 584 584 14,trivial⟩,⟨.loadN 560 584,trivial⟩]
def fetchCode : Cmd := Structured.sequence (fetchAtoms.map Cmd.atom)
noncomputable def fetched (s : Data) : Data := fetchAtoms.foldl (fun t a => a.effect t) s
def body : Cmd := .seq fetchCode (.seq (.branch (.natLess 560 542) CorePending.code .skip) (nadd 580 580 14))
def loop : Cmd := .loop (.natLess 580 582) body
def push (l : ℕ) (xs : List (Fin l)) (v : ℕ) : List (Fin l) :=
  if h : v < l then if (⟨v,h⟩ : Fin l) ∈ xs then xs else ⟨v,h⟩::xs else xs
end DecrAlmostLinearSSSP.Decremental.CoreReports
end CoreModule343
section CoreModule344
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreReports
end CoreModule344
section CoreModule345
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
def consume (l : ℕ) (xs : List (Fin l)) (reports : List ℕ) : List (Fin l) := reports.foldl (push l) xs
end DecrAlmostLinearSSSP.Decremental.CoreReports
end CoreModule345
section CoreModule346
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
def setupAtoms : List Atom := [⟨.nadd 582 23 56,trivial⟩,⟨.natural 580 0,trivial⟩]
def setup : Cmd := Structured.sequence (setupAtoms.map Cmd.atom)
noncomputable def setupData (s : Data) : Data := setupAtoms.foldl (fun t a => a.effect t) s
def code : Cmd := .seq setup loop
noncomputable def reportList (g : Machine) : List ℕ := List.ofFn (fun j : Fin (reportCount g) => g.natMem j.val)
end DecrAlmostLinearSSSP.Decremental.CoreReports
end CoreModule346
section CoreModule347
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
end DecrAlmostLinearSSSP.Decremental.CoreReports
end CoreModule347
section CoreModule348
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def ratioCode (N : ℕ) (p : Program) : Cmd := .seq CoreRequest.ratioCode (SourceCall.code N p.update p)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule348
section CoreModule349
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreReports
end CoreModule349
section CoreModule350
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end CoreModule350
section CoreModule351
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule351
section CoreModule352
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
end DecrAlmostLinearSSSP.Decremental.CoreReports
end CoreModule352
section CoreModule353
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def toggleCode (N : ℕ) (p : Program) : Cmd := .seq
  (.seq CoreRequest.toggleCode (SourceCall.code N p.update p)) CoreReports.code
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule353
section CoreModule354
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def stopCode : Cmd := natural 650 0
noncomputable def stoppedData (s : Data) : Data := {s with natReg := Function.update s.natReg 650 0}
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule354
section CoreModule355
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCommit
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule355
section CoreModule356
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRatioGuard
open Structured
def code : Cmd := div 700 29 31
noncomputable def result (s : Data) : Data := {s with realReg := Function.update s.realReg 700 (s.realReg 29/s.realReg 31)}
end DecrAlmostLinearSSSP.Decremental.CoreRatioGuard
end CoreModule356
section CoreModule357
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
def stoppedBit {b : Core} (s : State b) : ℕ := if s.stopped then 1 else 0
def nativeCredit (N D work calls reports stopped : ℕ) : ℕ :=
  D*work+100*(N+1)*calls+20*reports+10*stopped
end DecrAlmostLinearSSSP.Decremental.CoreRepair
end CoreModule357
section CoreModule358
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
def OperationDebt (b : Core) (s : State b) (calls reports offset : ℕ) : Prop :=
  calls+5*s.pending.length ≤ 5*reports+2*s.toggles+offset+stoppedBit s
end DecrAlmostLinearSSSP.Decremental.CoreRepair
end CoreModule358
section CoreModule359
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
def RatioShape (b : Core) (K : ℝ) (before after : State b)
    (N D oldWork newWork oldCalls newCalls oldReports newReports oldToggles newToggles cost : ℕ) : Prop :=
  (∃ (r : CutReply b) (xs : List (Edge b)) (emitted : ℕ),
    after = reportedToggle b K before r xs ∧ newCalls = oldCalls+2 ∧ newReports = oldReports+emitted ∧
    xs.length ≤ emitted ∧ newToggles = oldToggles+1 ∧
    cost ≤ D*(newWork-oldWork)+16*N+48+18*emitted) ∨
  (after = {before with stopped := true} ∧ newCalls = oldCalls+1 ∧ newReports = oldReports ∧
    newToggles = oldToggles ∧ cost ≤ D*(newWork-oldWork)+8*N+23)
end DecrAlmostLinearSSSP.Decremental.CoreRepair
end CoreModule359
section CoreModule360
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def ratioDecisionCode (N : ℕ) (p : Program) : Cmd := .seq (ratioCode N p)
  (.seq CoreRatioGuard.code (.branch (.realLess 700 520) (toggleCode N p) stopCode))
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule360
section CoreModule361
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def bodyCode (N : ℕ) (p : Program) : Cmd := .branch (.natLess 56 546) (drainOneCode N p)
  (.branch (.natLess 56 550) (ratioDecisionCode N p) stopCode)
def credit (b : Core) (N : ℕ) (p : Program) (state : State b) (current : Machine)
    (ops : List (CutOp b.input.n (logicalCount b))) (machines : List Machine) : ℕ :=
  CoreRepair.nativeCredit N (dispatchCharge p.code+2) current.work ops.length (reportVolume machines) (CoreRepair.stoppedBit state)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule361
section CoreModule362
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
open Structured
structure Snapshot (b : Core) where
  state : State b
  current : Machine
  ops : List (CutOp b.input.n (logicalCount b))
  machines : List Machine
structure Repr (b : Core) (B N offset : ℕ) (K K0 h Γ init : ℝ)
    (impl : CutImplementation) (first : Machine) (active : Finset (Fin b.input.k)) (q : Snapshot b) (s : Data) : Prop where
  bounds : RuntimeBounds b K q.state
  host : CoreHost.Image b B K q.state s
  model : CutModel b (logicalIndexEquiv b) q.state (impl.view b.input.n (logicalCount b) q.current)
  run : CutRun impl b.input.n (logicalCount b) (2*b.input.size) (4*b.weightExponent+68) first q.ops q.machines
  last : q.machines.getLast? = some q.current
  zeroTail : ZeroRegisterTail N q.current
  image : CoreSource.Image B (CoreMemory.sourceRecord b B) N q.current s
  running : s.natReg 650 = (if q.state.stopped then 0 else 1)
  threshold : s.realReg 520 = -1/(4*K)
  debt : CoreRepair.OperationDebt b q.state q.ops.length (reportVolume q.machines) offset
  toggleCount : toggleVolume q.ops = q.state.toggles
  complete : q.state.stopped = true → ReadoutCertificate b q.state
  active_eq : q.state.active = active
  drained : q.state.stopped = true → q.state.pending = []
def Repr.context {b : Core} {B N offset : ℕ} {K K0 h Γ init : ℝ}
    {impl : CutImplementation} {first : Machine} {active : Finset (Fin b.input.k)} {q : Snapshot b} {s : Data}
    (hSession : CutSession impl b.input.n (logicalCount b) (2*b.input.size) (4*b.weightExponent+68) first K0 (K^(-2 : ℤ)) h Γ init)
    (hq : Repr b B N offset K K0 h Γ init impl first active q s) :
    Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s :=
  ⟨first,q.current,q.ops,q.machines,hSession,hq.run,hq.last,hq.zeroTail,hq.image⟩
def credit (b : Core) (N : ℕ) (p : Program) (q : Snapshot b) : ℕ :=
  CoreNativeCut.credit b N p q.state q.current q.ops q.machines
noncomputable def relation (b : Core) (K : ℝ) : Snapshot b → Snapshot b → Prop :=
  InvImage (Prod.Lex Nat.lt Nat.lt) (fun q => runtimeRepairRank b K q.state)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
end CoreModule362
section CoreModule363
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end CoreModule363
section CoreModule364
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end CoreModule364
section CoreModule365
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
open Structured
def loopCode (N : ℕ) (p : Program) : Cmd := .loop (.natLess 56 650) (bodyCode N p)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
end CoreModule365
section CoreModule366
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepairControl
open Structured
def atoms : List Atom := [⟨.rational 656 4,trivial⟩,⟨.mul 656 656 512,trivial⟩,
  ⟨.rational 658 (-1),trivial⟩,⟨.div 520 658 656,trivial⟩,⟨.natural 650 1,trivial⟩]
def code : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def result (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.CoreRepairControl
end CoreModule366
section CoreModule367
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def repairCode (N : ℕ) (p : Program) : Cmd := .seq CoreRepairControl.code (Repair.loopCode N p)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule367
section CoreModule368
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDeletion
open Structured
lemma host_input (b : Core) (B : ℕ) (K : ℝ) (state : State b) (s : Data) (value : ℕ)
    (h : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) :
    CoreHost.Image b B K state {s with natReg := Function.update s.natReg 5 value} := by
  apply h.frame b B K state hB
  · intro k hk
    apply Function.update_of_ne _ _ _
    simp only [CoreHost.NatRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  · intro k hk;rfl
  · intro j hj;exact ⟨rfl,rfl⟩
lemma source_input (b : Core) (B N : ℕ) (g : Machine) (s : Data) (value : ℕ)
    (h : CoreSource.Image B (CoreMemory.sourceRecord b B) N g s) :
    CoreSource.Image B (CoreMemory.sourceRecord b B) N g {s with natReg := Function.update s.natReg 5 value} := by
  apply h.frame B _ N g
  · intro k hk
    apply Function.update_of_ne _ _ _
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  · intro j hj
    exact ⟨Function.update_of_ne (by dsimp [shadowReg];omega) _ _,rfl⟩
  · intro j;exact ⟨rfl,rfl⟩
  · rfl
  · intro j hj;exact ⟨rfl,rfl⟩
def encodeCode : Cmd := nadd 560 5 5
noncomputable def encoded (s : Data) : Data := {s with natReg := Function.update s.natReg 560 (s.natReg 5+s.natReg 5)}
end DecrAlmostLinearSSSP.Decremental.CoreDeletion
end CoreModule368
section CoreModule369
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end CoreModule369
section CoreModule370
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule370
section CoreModule371
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDeletion
open Structured
def headerCode : Cmd := .seq encodeCode (.seq CoreEdgeAddress.code (store 576 516))
end DecrAlmostLinearSSSP.Decremental.CoreDeletion
end CoreModule371
section CoreModule372
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDeletion
noncomputable def pendingState (b : Core) (s : State b) (e : Fin b.input.k) : State b :=
  {s with active := s.active.erase e, pending := [.inl e], stopped := false, history := s.history++[.deletion e]}
end DecrAlmostLinearSSSP.Decremental.CoreDeletion
end CoreModule372
section CoreModule373
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule373
section CoreModule374
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule374
section CoreModule375
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDeletion
open Structured
def prepareCode : Cmd := .seq headerCode CorePending.code
end DecrAlmostLinearSSSP.Decremental.CoreDeletion
end CoreModule375
section CoreModule376
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
end DecrAlmostLinearSSSP.Decremental.CoreRepair
end CoreModule376
section CoreModule377
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def forcedDeletionCode (N : ℕ) (p : Program) : Cmd := .seq CoreDeletion.prepareCode (refreshCode N p)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule377
section CoreModule378
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def updateCode (N : ℕ) (p : Program) : Cmd := .seq (forcedDeletionCode N p) (repairCode N p)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule378
section CoreModule379
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule379
section CoreModule380
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule380
section CoreModule381
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule381
section CoreModule382
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule382
section CoreModule383
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule383
section CoreModule384
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
def rootPowerAtoms : List Atom := [
  ⟨.cast 410 408,trivial⟩,
  ⟨.mul 412 410 410,trivial⟩,
  ⟨.mul 414 412 412,trivial⟩,
  ⟨.mul 416 414 414,trivial⟩,
  ⟨.mul 418 416 414,trivial⟩]
def rootPower : Cmd := sequence (rootPowerAtoms.map Cmd.atom)
noncomputable def powered (s : Data) : Data := rootPowerAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end CoreModule384
section CoreModule385
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def cutLogHeight (m : ℕ) : ℕ := Exact.height (max 2 m)
noncomputable def cutRoot (m : ℕ) : ℕ := Nat.nthRoot 12 (cutLogHeight m)+1
noncomputable def computableCutQuality (N m : ℕ) : ℝ := (2 : ℝ)^(N*(cutRoot m)^11)
end DecrAlmostLinearSSSP.Decremental
end CoreModule385
section CoreModule386
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
def heightStartAtoms : List Atom := [⟨.natural 402 1,trivial⟩,⟨.natural 404 0,trivial⟩,⟨.nadd 406 64 26,trivial⟩]
def heightBodyAtoms : List Atom := [⟨.nadd 402 402 402,trivial⟩,⟨.nadd 404 404 26,trivial⟩]
def heightStart : Cmd := Structured.sequence (heightStartAtoms.map Cmd.atom)
def heightBody : Cmd := Structured.sequence (heightBodyAtoms.map Cmd.atom)
def heightLoop : Cmd := .loop (.natLess 402 406) heightBody
noncomputable def heightStarted (s : Data) : Data := heightStartAtoms.foldl (fun t a => a.effect t) s
noncomputable def heightAdvanced (s : Data) : Data := heightBodyAtoms.foldl (fun t a => a.effect t) s
structure HeightRep (m : ℕ) (s : Data) : Prop where
  counter : s.natReg 404 ≤ cutLogHeight m
  power : s.natReg 402 = 2^s.natReg 404
  limit : s.natReg 406 = m+1
  size : s.natReg 64 = m
  unit : s.natReg 26 = 1
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end CoreModule386
section CoreModule387
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
def rootBody : Cmd := .seq (nadd 408 408 26) rootPower
noncomputable def rootAdvanced (s : Data) : Data :=
  powered {s with natReg := Function.update s.natReg 408 (s.natReg 408+s.natReg 26)}
def rootLoop : Cmd := .loop (.realLess 418 420) rootBody
structure RootRep (t : ℕ) (s : Data) : Prop where
  counter : s.natReg 408 ≤ Nat.nthRoot 12 t+1
  positive : 1 ≤ s.natReg 408
  power : s.realReg 418 = (s.natReg 408 : ℝ)^12
  limit : s.realReg 420 = (t+1 : ℕ)
  unit : s.natReg 26 = 1
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end CoreModule387
section CoreModule388
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
def rootStartAtoms : List Atom := [⟨.natural 408 1,trivial⟩,⟨.nadd 450 404 26,trivial⟩,⟨.cast 420 450,trivial⟩]
def rootPrefix : Cmd := Structured.sequence (rootStartAtoms.map Cmd.atom)
def rootStart : Cmd := .seq rootPrefix rootPower
noncomputable def rootPrefixData (s : Data) : Data := rootStartAtoms.foldl (fun t a => a.effect t) s
noncomputable def rootStarted (s : Data) : Data := powered (rootPrefixData s)
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end CoreModule388
section CoreModule389
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
def exponentAtoms (N : ℕ) : List Atom := [
  ⟨.cast 424 408,trivial⟩,⟨.mul 426 424 424,trivial⟩,⟨.mul 428 426 426,trivial⟩,
  ⟨.mul 430 428 428,trivial⟩,⟨.mul 432 426 424,trivial⟩,⟨.mul 434 430 432,trivial⟩,
  ⟨.natural 436 N,trivial⟩,⟨.cast 436 436,trivial⟩,⟨.mul 438 436 434,trivial⟩,
  ⟨.rational 440 0,trivial⟩,⟨.rational 442 1,trivial⟩,⟨.rational 444 1,trivial⟩,⟨.rational 446 2,trivial⟩]
def exponentStart (N : ℕ) : Cmd := Structured.sequence ((exponentAtoms N).map Cmd.atom)
noncomputable def exponentStarted (N : ℕ) (s : Data) : Data := (exponentAtoms N).foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end CoreModule389
section CoreModule390
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
def qualityBodyAtoms : List Atom := [⟨.mul 442 442 446,trivial⟩,⟨.add 440 440 444,trivial⟩]
def qualityBody : Cmd := Structured.sequence (qualityBodyAtoms.map Cmd.atom)
def qualityLoop : Cmd := .loop (.realLess 440 438) qualityBody
noncomputable def qualityAdvanced (s : Data) : Data := qualityBodyAtoms.foldl (fun t a => a.effect t) s
noncomputable def QualityRep (E : ℕ) (s : Data) : Prop :=
  ∃ j : ℕ, j ≤ E ∧ s.realReg 440 = j ∧ s.realReg 442 = (2 : ℝ)^j ∧
    s.realReg 438 = E ∧ s.realReg 444 = 1 ∧ s.realReg 446 = 2
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end CoreModule390
section CoreModule391
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
def code (N : ℕ) : Cmd := .seq heightStart (.seq heightLoop (.seq rootStart
  (.seq rootLoop (.seq (exponentStart N) qualityLoop))))
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end CoreModule391
section CoreModule392
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end CoreModule392
section CoreModule393
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end CoreModule393
section CoreModule394
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreQuality
open Structured
def code (N : ℕ) : Cmd := .seq (nadd 600 64 56) (.seq (nadd 64 64 64)
  (.seq (CutQualityNative.code N) (nadd 64 600 56)))
noncomputable def saved (s : Data) : Data := {s with natReg := Function.update s.natReg 600 (s.natReg 64+s.natReg 56)}
noncomputable def prepared (s : Data) : Data :=
  {saved s with natReg := Function.update (saved s).natReg 64 ((saved s).natReg 64+(saved s).natReg 64)}
noncomputable def restored (s : Data) : Data := {s with natReg := Function.update s.natReg 64 (s.natReg 600+s.natReg 56)}
end DecrAlmostLinearSSSP.Decremental.CoreQuality
end CoreModule394
section CoreModule395
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end CoreModule395
section CoreModule396
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCeiling
open Structured
def startAtoms : List Atom := [⟨.natural 526 0,trivial⟩,⟨.cast 526 526,trivial⟩]
def bodyAtoms : List Atom := [⟨.nadd 526 526 26,trivial⟩,⟨.cast 526 526,trivial⟩]
def start : Cmd := Structured.sequence (startAtoms.map Cmd.atom)
def body : Cmd := Structured.sequence (bodyAtoms.map Cmd.atom)
def loop : Cmd := .loop (.realLess 526 522) body
noncomputable def started (s : Data) : Data := startAtoms.foldl (fun t a => a.effect t) s
noncomputable def advanced (s : Data) : Data := bodyAtoms.foldl (fun t a => a.effect t) s
structure Rep (x : ℝ) (s : Data) : Prop where
  target : s.realReg 522 = x
  unit : s.natReg 26 = 1
  value : s.realReg 526 = (s.natReg 526 : ℝ)
  bound : s.natReg 526 ≤ ⌈x⌉₊
end DecrAlmostLinearSSSP.Decremental.CoreCeiling
end CoreModule396
section CoreModule397
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCeiling
end CoreModule397
section CoreModule398
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
def code : Cmd := .seq header (.seq (.seq CoreCeiling.start CoreCeiling.loop) finish)
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end CoreModule398
section CoreModule399
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
def registerCode (N : ℕ) : Cmd := .seq InputCapture.code
  (.seq (CoreQuality.code N) (.seq CoreParameters.code CoreControl.code))
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end CoreModule399
section CoreModule400
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
def bootRecordsCode (N : ℕ) : Cmd := .seq (registerCode N) recordsCode
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end CoreModule400
section CoreModule401
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
noncomputable def primitiveNatMemory (ins : Instruction) (s : Data) (address : ℕ) : ℕ :=
  match ins with
  | .storeN a d => if address = s.natReg a then s.natReg d else s.natMem address
  | _ => s.natMem address
noncomputable def primitiveRealMemory (ins : Instruction) (s : Data) (address : ℕ) : ℝ :=
  match ins with
  | .store a d => if address = s.natReg a then s.realReg d else s.realMem address
  | _ => s.realMem address
end DecrAlmostLinearSSSP.Decremental.Structured
end CoreModule401
section CoreModule402
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestEdge
open Structured
def atoms : List Atom := [⟨.nadd 680 560 560,trivial⟩,⟨.nadd 682 680 680,trivial⟩,
  ⟨.nadd 684 682 680,trivial⟩,⟨.nadd 684 74 684,trivial⟩,⟨.nadd 684 684 14,trivial⟩,
  ⟨.nadd 686 626 626,trivial⟩,⟨.nadd 688 628 628,trivial⟩,⟨.storeN 684 686,trivial⟩,
  ⟨.nadd 684 684 690,trivial⟩,⟨.storeN 684 688,trivial⟩,⟨.nadd 684 684 690,trivial⟩,
  ⟨.storeN 684 14,trivial⟩,⟨.nadd 692 74 680,trivial⟩,⟨.nadd 692 692 14,trivial⟩,
  ⟨.store 692 600,trivial⟩,⟨.nadd 560 560 14,trivial⟩]
def code : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def result (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.CoreGuestEdge
end CoreModule402
section CoreModule403
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestEdge
end CoreModule403
section CoreModule404
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestGamma
open Structured
def atoms : List Atom := [⟨.nadd 680 626 626,trivial⟩,⟨.nadd 682 554 680,trivial⟩,
  ⟨.load 694 682,trivial⟩,⟨.nadd 684 542 680,trivial⟩,⟨.nadd 684 684 684,trivial⟩,
  ⟨.nadd 684 74 684,trivial⟩,⟨.nadd 684 684 14,trivial⟩,⟨.store 684 694,trivial⟩,
  ⟨.nadd 626 626 26,trivial⟩]
def code : Cmd := Structured.sequence (atoms.map Cmd.atom)
noncomputable def result (s : Data) : Data := atoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.CoreGuestGamma
end CoreModule404
section CoreModule405
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
def edgeBody : Cmd := .seq CorePending.prefixCode (.seq CoreGeometry.code CoreGuestEdge.code)
def edgeLoop : Cmd := .loop (.natLess 560 542) edgeBody
def edgeStart : Cmd := Structured.sequence [natural 560 0,natural 690 4]
def gammaLoop : Cmd := .loop (.natLess 626 66) CoreGuestGamma.code
def code : Cmd := .seq edgeStart (.seq edgeLoop (.seq (natural 626 0) gammaLoop))
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end CoreModule405
section CoreModule406
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end CoreModule406
section CoreModule407
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
structure EdgePrefix (b : Core) (B : ℕ) (state : State b) (upto : ℕ) (s : Data) : Prop where
  tails : ∀ d : Fin (logicalCount b), d.val < upto → s.natMem (B+12*d.val+2) = 2*(tail b ((logicalIndexEquiv b).symm d)).val
  heads : ∀ d : Fin (logicalCount b), d.val < upto → s.natMem (B+12*d.val+6) = 2*(head b ((logicalIndexEquiv b).symm d)).val
  active : ∀ d : Fin (logicalCount b), d.val < upto → s.natMem (B+12*d.val+10) = 2
  capacities : ∀ d : Fin (logicalCount b), d.val < upto → s.realMem (B+4*d.val+2) = state.cache ((logicalIndexEquiv b).symm d)
  natZero : ∀ j, 3*upto ≤ j → s.natMem (B+4*j+2) = 0
  realZero : ∀ j, upto ≤ j → s.realMem (B+4*j+2) = 0
structure EdgeInvariant (b : Core) (B : ℕ) (state : State b) (upto : ℕ) (s : Data) : Prop where
  bound : upto ≤ logicalCount b
  geometry : CoreGeometry.Image b B state s
  gradient : CoreGradient.Image (CoreMemory.gradientBase b B) state.cachedGradient s
  captured : InputCapture.Captured b.input s
  layout : CoreControl.Layout b B s
  base : s.natReg 74 = B
  counter : s.natReg 560 = 2*upto
  four : s.natReg 690 = 4
  cells : EdgePrefix b B state upto s
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end CoreModule407
section CoreModule408
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end CoreModule408
section CoreModule409
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
noncomputable def edgesStarted (s : Data) : Data :=
  {s with natReg := Function.update (Function.update s.natReg 560 0) 690 4}
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end CoreModule409
section CoreModule410
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
structure GammaPrefix (b : Core) (B : ℕ) (state : State b) (upto : ℕ) (s : Data) : Prop where
  tails : ∀ d : Fin (logicalCount b), s.natMem (B+12*d.val+2) = 2*(tail b ((logicalIndexEquiv b).symm d)).val
  heads : ∀ d : Fin (logicalCount b), s.natMem (B+12*d.val+6) = 2*(head b ((logicalIndexEquiv b).symm d)).val
  active : ∀ d : Fin (logicalCount b), s.natMem (B+12*d.val+10) = 2
  capacities : ∀ d : Fin (logicalCount b), s.realMem (B+4*d.val+2) = state.cache ((logicalIndexEquiv b).symm d)
  gamma : ∀ v : Fin b.input.n, v.val < upto → s.realMem (B+4*(logicalCount b+v.val)+2) = state.cachedGradient v
  natZero : ∀ j, 3*logicalCount b ≤ j → s.natMem (B+4*j+2) = 0
  realZero : ∀ j, logicalCount b+upto ≤ j → s.realMem (B+4*j+2) = 0
structure GammaInvariant (b : Core) (B : ℕ) (state : State b) (upto : ℕ) (s : Data) : Prop where
  bound : upto ≤ b.input.n
  geometry : CoreGeometry.Image b B state s
  gradient : CoreGradient.Image (CoreMemory.gradientBase b B) state.cachedGradient s
  captured : InputCapture.Captured b.input s
  layout : CoreControl.Layout b B s
  base : s.natReg 74 = B
  vertex : s.natReg 626 = upto
  cells : GammaPrefix b B state upto s
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end CoreModule410
section CoreModule411
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end CoreModule411
section CoreModule412
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end CoreModule412
section CoreModule413
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end CoreModule413
section CoreModule416
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
open Structured
def fieldAtoms : List Atom := [⟨.nadd 630 50 56,trivial⟩,⟨.nadd 670 66 66,trivial⟩,
  ⟨.storeN 630 670,trivial⟩,⟨.store 630 510,trivial⟩,⟨.nadd 630 630 14,trivial⟩,
  ⟨.nadd 672 536 536,trivial⟩,⟨.storeN 630 672,trivial⟩,⟨.store 630 508,trivial⟩,
  ⟨.nadd 630 630 14,trivial⟩,⟨.nadd 674 540 540,trivial⟩,⟨.storeN 630 674,trivial⟩]
def fieldCode : Cmd := Structured.sequence (fieldAtoms.map Cmd.atom)
noncomputable def fieldResult (s : Data) : Data := fieldAtoms.foldl (fun t a => a.effect t) s
end DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
end CoreModule416
section CoreModule417
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
end CoreModule417
section CoreModule418
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
open Structured
def code (N : ℕ) : Cmd := .seq (SnapshotFill.code N) fieldCode
end DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
end CoreModule418
section CoreModule419
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end CoreModule419
section CoreModule420
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end CoreModule420
section CoreModule421
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
def bootCutInputCode (N registers : ℕ) : Cmd :=
  .seq (bootRecordsCode N) (.seq CoreGuestCopy.code (CoreInitialSaved.code registers))
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end CoreModule421
section CoreModule422
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule422
section CoreModule423
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
def sourceRegisters (p : Program) : ℕ := registerBound p.code+10
def bootCutCode (N : ℕ) (p : Program) : Cmd := .seq (bootCutInputCode N (sourceRegisters p))
  (SourceCall.code (sourceRegisters p) p.initPC p)
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end CoreModule423
section CoreModule424
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end CoreModule424
section CoreModule425
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule425
section CoreModule426
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def initCode (qualityPower : ℕ) (p : Program) : Cmd := .seq (CoreInitialize.bootCutCode qualityPower p)
  (repairCode (CoreInitialize.sourceRegisters p) p)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule426
section CoreModule427
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
structure Ready (b : Core) (B N : ℕ) (K K0 h Γ init : ℝ) (impl : CutImplementation)
    (deleted : List (Fin b.input.k)) (s : Data) where
  state : State b
  context : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s
  host : CoreHost.Image b B K state s
  bounds : RuntimeBounds b K state
  model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) context.current)
  stopped : state.stopped = true
  certificate : ReadoutCertificate b state
  pending : state.pending = []
  active : state.active = live deleted
  debt : CoreRepair.OperationDebt b state context.ops.length (reportVolume context.machines) (6*deleted.length)
  toggles : toggleVolume context.ops = state.toggles
def Ready.credit {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ} {impl : CutImplementation}
    {deleted : List (Fin b.input.k)} {s : Data} (r : Ready b B N K K0 h Γ init impl deleted s) : ℕ :=
  CoreNativeCut.credit b N impl.program r.state r.context.current r.context.ops r.context.machines
def coreProgram (qualityPower : ℕ) (p : Program) : Program :=
  Structured.program (initCode qualityPower p) (updateCode (CoreInitialize.sourceRegisters p) p)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule427
section CoreModule428
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule428
section CoreModule429
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
noncomputable def Ready.external {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ} {impl : CutImplementation}
    {deleted : List (Fin b.input.k)} {s : Data} (r : Ready b B N K K0 h Γ init impl deleted s)
    (hB : b.input.n ≤ B) (value : ℕ) :
    Ready b B N K K0 h Γ init impl deleted {s with natReg := Function.update s.natReg 5 value} :=
  let ctx := r.context.of_image (CoreDeletion.source_input b B N r.context.current s value r.context.image)
  ⟨r.state,ctx,CoreDeletion.host_input b B K r.state s value r.host hB,r.bounds,r.model,r.stopped,r.certificate,r.pending,r.active,r.debt,r.toggles⟩
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule429
section CoreModule430
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule430
section CoreModule431
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
noncomputable def initialBudget (b : Core) (qualityPower : ℕ) (p : Program) (init : ℝ) : ℝ :=
  ((80000*(qualityPower+1)+265)*b.input.size+
    4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*CoreInitialize.sourceRegisters p+120 : ℕ)+
    (dispatchCharge p.code+2)*init+8
noncomputable def Completed (b : Core) (qualityPower : ℕ) (impl : CutImplementation)
    (K0 h Γ init : ℝ) (deleted : List (Fin b.input.k)) (c : Machine) : Prop :=
  ∃ ready : Ready b (b.input.n+3*b.input.k+2) (CoreInitialize.sourceRegisters impl.program)
      (computableCutQuality qualityPower (2*b.input.size)) K0 h Γ init impl deleted (Structured.data c),
    ((c.work+6*deleted.length : ℕ) : ℝ) ≤ initialBudget b qualityPower impl.program init+(ready.credit : ℝ)
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule431
section CoreModule432
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule432
section CoreModule433
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
end DecrAlmostLinearSSSP.Decremental.CoreRepair
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule433
section CoreModule434
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule434
section CoreModule435
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def coreLogOverhead (m : ℕ) : ℝ := 1+Real.log (max 2 m : ℕ)
end DecrAlmostLinearSSSP.Decremental
end CoreModule435
section CoreModule436
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def coreRuntimeOverhead (h Γ a : ℕ → ℝ) (N m : ℕ) : ℝ :=
  1+a (2*m)+(1+h (2*m))*(1+Γ (2*m))*(computableCutQuality N (2*m))^5*(coreLogOverhead m)^2
end DecrAlmostLinearSSSP.Decremental
end CoreModule436
section CoreModule437
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule437
section CoreModule438
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule438
section CoreModule439
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
noncomputable def coreConstant (d qualityPower : ℕ) (p : Program) (C : ℝ) : ℝ :=
  (80000*(qualityPower+1)+265+14*CoreInitialize.sourceRegisters p+400 : ℕ)+
    4*(dispatchCharge p.code+2 : ℕ)*C+
    10000*(d+8 : ℕ)*((dispatchCharge p.code+2 : ℕ)+100*(CoreInitialize.sourceRegisters p+1 : ℕ))
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule439
section CoreModule440
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule440
section CoreModule441
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end CoreModule441
section CoreModule442
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end CoreModule442


