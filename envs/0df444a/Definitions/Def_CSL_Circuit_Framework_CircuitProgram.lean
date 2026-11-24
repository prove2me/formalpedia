-- Prove2me | Definitions.Def_CSL_Circuit_Framework_CircuitProgram
-- name    : CSL_Circuit_Framework_CircuitProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:21:46.952593+00:00
-- url     : https://prove2.me/theorems/6a3feaf7-f93e-4690-9f13-4f80e6cffdc8
-- title:
--   Coded sorting library: Circuit / Framework / CircuitProgram
-- statement:
--   Module `CodedSorting.Circuit.Framework.CircuitProgram` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Finite register-level XOR programs and the exact block port graph.
--   No arbitrary correct function is admitted as a gate: gates have finite explicit
--   control sets and simultaneous XOR updates, and their semantics is fixed below.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Framework.CircuitProgram

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Framework_Circuit
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Finite register-level XOR programs and the exact block port graph.
No arbitrary correct function is admitted as a gate: gates have finite explicit
control sets and simultaneous XOR updates, and their semantics is fixed below. -/
set_option autoImplicit false

namespace CSL.CircuitProgram

theorem ite_inst_congr {α : Sort*} {p : Prop} (i1 i2 : Decidable p) (a b : α) :
    @ite α p i1 a b = @ite α p i2 a b := by congr

theorem sum_ite_mem_any {ι M : Type*} [Fintype ι] [AddCommMonoid M] (s : Finset ι) (f : ι → M)
    (inst : ∀ i, Decidable (i ∈ s)) :
    (∑ i, @ite _ (i ∈ s) (inst i) (f i) 0) = ∑ i ∈ s, f i := by
  classical
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

open CSL.Circuit
open scoped BigOperators

/-- A node reads exactly its listed ports and updates the listed targets. -/
structure XorGate (R : Type*) [DecidableEq R] where
  ports : Finset R
  targets : Finset R
  controls : R → Finset R
  targets_subset : targets ⊆ ports
  controls_subset : ∀ r ∈ targets, controls r ⊆ ports

namespace XorGate
variable {R : Type*} [DecidableEq R]

def eval (g : XorGate R) (s : R → Bit) (r : R) : Bit :=
  if r ∈ g.targets then s r + ∑ c ∈ g.controls r, s c else s r

theorem eval_outside_ports (g : XorGate R) (s : R → Bit) (r : R)
    (h : r ∉ g.ports) : g.eval s r = s r := by
  have ht : r ∉ g.targets := fun hr => h (g.targets_subset hr)
  simp [eval, ht]

theorem eval_congr_on_ports (g : XorGate R) (s t : R → Bit)
    (h : ∀ r ∈ g.ports, s r = t r) (r : R) (hr : r ∈ g.ports) :
    g.eval s r = g.eval t r := by
  unfold eval
  by_cases ht : r ∈ g.targets
  · simp only [if_pos ht, h r hr]
    congr 1
    apply Finset.sum_congr rfl
    intro c hc
    exact h c (g.controls_subset r ht hc)
  · simp [ht, h r hr]

theorem eval_add (g : XorGate R) (s t : R → Bit) :
    g.eval (s + t) = g.eval s + g.eval t := by
  funext r
  by_cases h : r ∈ g.targets
  · simp [eval, h, Finset.sum_add_distrib]
    ring
  · simp [eval, h]

theorem eval_smul (g : XorGate R) (a : Bit) (s : R → Bit) :
    g.eval (a • s) = a • g.eval s := by
  funext r
  by_cases h : r ∈ g.targets
  · simp [eval, h, smul_eq_mul, Finset.mul_sum, mul_add]
  · simp [eval, h]

def linearMap (g : XorGate R) : (R → Bit) →ₗ[Bit] (R → Bit) where
  toFun := g.eval
  map_add' := g.eval_add
  map_smul' := g.eval_smul

end XorGate

def runProgram {R : Type*} [DecidableEq R] :
    List (XorGate R) → (R → Bit) → (R → Bit)
  | [], s => s
  | g :: gs, s => runProgram gs (g.eval s)

theorem runProgram_add {R : Type*} [DecidableEq R]
    (p : List (XorGate R)) (s t : R → Bit) :
    runProgram p (s + t) = runProgram p s + runProgram p t := by
  induction p generalizing s t with
  | nil => rfl
  | cons g gs ih =>
    simp only [runProgram, XorGate.eval_add, ih]

theorem runProgram_smul {R : Type*} [DecidableEq R]
    (p : List (XorGate R)) (a : Bit) (s : R → Bit) :
    runProgram p (a • s) = a • runProgram p s := by
  induction p generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [runProgram, XorGate.eval_smul, ih]

def programLinearMap {R : Type*} [DecidableEq R]
    (p : List (XorGate R)) : (R → Bit) →ₗ[Bit] (R → Bit) where
  toFun := runProgram p
  map_add' := runProgram_add p
  map_smul' := runProgram_smul p

namespace XorGate
variable {R : Type*} [DecidableEq R]
def delta (g : XorGate R) (s : R → Bit) (r : R) : Bit :=
  if r ∈ g.targets then ∑ c ∈ g.controls r, s c else 0

theorem eval_eq_add_delta (g : XorGate R) (s : R → Bit) (r : R) :
    g.eval s r = s r + g.delta s r := by
  by_cases h : r ∈ g.targets <;> simp [eval, delta, h]

theorem delta_eval (g h : XorGate R) (s : R → Bit)
    (hn : ∀ r ∈ g.targets, ∀ c ∈ g.controls r, c ∉ h.targets) (r : R) :
    g.delta (h.eval s) r = g.delta s r := by
  unfold delta
  split_ifs with hr
  · apply Finset.sum_congr rfl
    intro c hc
    simp [eval, hn r hr c hc]
  · rfl
end XorGate

/-- Controls are never overwritten anywhere in this gate batch. -/
def IndependentControls {R : Type*} [DecidableEq R] (p : List (XorGate R)) : Prop :=
  ∀ g ∈ p, ∀ h ∈ p, ∀ r ∈ g.targets, ∀ c ∈ g.controls r, c ∉ h.targets

theorem runProgram_deltas {R : Type*} [DecidableEq R]
    (p : List (XorGate R)) (hp : IndependentControls p) (s : R → Bit) (r : R) :
    runProgram p s r = s r + (p.map (fun g => g.delta s r)).sum := by
  induction p generalizing s with
  | nil => simp [runProgram]
  | cons g gs ih =>
    have ht : IndependentControls gs := by
      intro h hh k hk r hr c hc
      exact hp h (by simp [hh]) k (by simp [hk]) r hr c hc
    rw [runProgram, ih ht]
    have hm : gs.map (fun h => h.delta (g.eval s) r) =
        gs.map (fun h => h.delta s r) := by
      apply List.map_congr_left
      intro h hh
      apply XorGate.delta_eval
      intro r hr c hc
      exact hp h (by simp [hh]) g (by simp) r hr c hc
    rw [hm, XorGate.eval_eq_add_delta]
    simp [add_assoc]

theorem runProgram_append {R : Type*} [DecidableEq R]
    (p q : List (XorGate R)) (s : R → Bit) :
    runProgram (p ++ q) s = runProgram q (runProgram p s) := by
  induction p generalizing s with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, runProgram, ih]

namespace XorGate
variable {R S : Type*} [Fintype R] [DecidableEq R] [DecidableEq S]

noncomputable def liftControls (e : R ↪ S) (g : XorGate R) (q : S) : Finset S := by
  classical
  exact (Finset.univ.filter (fun c => ∃ r, e r = q ∧ c ∈ g.controls r)).map e

theorem liftControls_at (e : R ↪ S) (g : XorGate R) (r : R) :
    liftControls e g (e r) = (g.controls r).map e := by
  classical
  unfold liftControls
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r', h, hc⟩
    have he : r' = r := e.injective h
    simpa [he] using hc
  · intro hc
    exact ⟨r, rfl, hc⟩

noncomputable def lift (e : R ↪ S) (g : XorGate R) : XorGate S := by
  classical
  exact {
    ports := g.ports.map e
    targets := g.targets.map e
    controls := liftControls e g
    targets_subset := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hq
      exact Finset.mem_map.mpr ⟨r, g.targets_subset hr, rfl⟩
    controls_subset := by
      intro q hq c hc
      obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hq
      rw [liftControls_at] at hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hc
      exact Finset.mem_map.mpr ⟨a, g.controls_subset r hr ha, rfl⟩ }

theorem eval_lift_at (e : R ↪ S) (g : XorGate R) (s : S → Bit) (r : R) :
    (g.lift e).eval s (e r) = g.eval (s ∘ e) r := by
  classical
  simp [eval, lift, liftControls_at, Finset.sum_map]

theorem eval_lift_outside (e : R ↪ S) (g : XorGate R) (s : S → Bit) (q : S)
    (hq : ∀ r, e r ≠ q) : (g.lift e).eval s q = s q := by
  apply eval_outside_ports
  intro hm
  obtain ⟨r, _, he⟩ := Finset.mem_map.mp hm
  exact hq r he
end XorGate

 theorem runProgram_lift_restrict {R S : Type*} [Fintype R]
    [DecidableEq R] [DecidableEq S] (e : R ↪ S)
    (p : List (XorGate R)) (s : S → Bit) :
    runProgram (p.map (XorGate.lift e)) s ∘ e = runProgram p (s ∘ e) := by
  induction p generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, runProgram]
    rw [ih]
    apply congrArg (runProgram gs)
    funext r
    exact XorGate.eval_lift_at e g s r

theorem runProgram_lift_outside {R S : Type*} [Fintype R]
    [DecidableEq R] [DecidableEq S] (e : R ↪ S)
    (p : List (XorGate R)) (s : S → Bit) (q : S)
    (hq : ∀ r, e r ≠ q) : runProgram (p.map (XorGate.lift e)) s q = s q := by
  induction p generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, runProgram]
    rw [ih]
    exact XorGate.eval_lift_outside e g s q hq

noncomputable def partitionProgram {K R S : Type*} [Fintype R]
    [DecidableEq R] [DecidableEq S] (e : K → R ↪ S)
    (ks : List K) (p : List (XorGate R)) : List (XorGate S) :=
  ks.flatMap (fun k => p.map (XorGate.lift (e k)))

theorem partitionProgram_restrict {K R S : Type*} [Fintype R]
    [DecidableEq K] [DecidableEq R] [DecidableEq S]
    (e : K → R ↪ S) (hd : ∀ k l, k ≠ l → ∀ r t, e k r ≠ e l t)
    (ks : List K) (hn : ks.Nodup) (p : List (XorGate R))
    (s : S → Bit) (k : K) :
    runProgram (partitionProgram e ks p) s ∘ e k =
      if k ∈ ks then runProgram p (s ∘ e k) else s ∘ e k := by
  induction ks generalizing s with
  | nil => simp [partitionProgram, runProgram]
  | cons l ls ih =>
    obtain ⟨hl, hls⟩ := List.nodup_cons.mp hn
    simp only [partitionProgram, List.flatMap_cons, runProgram_append]
    change runProgram (partitionProgram e ls p)
      (runProgram (p.map (XorGate.lift (e l))) s) ∘ e k = _
    rw [ih hls]
    by_cases he : l = k
    · subst l
      simp only [List.mem_cons, true_or, ite_true, hl, ite_false]
      exact runProgram_lift_restrict (e k) p s
    · have hp : runProgram (p.map (XorGate.lift (e l))) s ∘ e k = s ∘ e k := by
        funext r
        exact runProgram_lift_outside (e l) p s (e k r)
          (fun t => hd l k he t r)
      rw [hp]
      simp [he, Ne.symm he]

theorem partitionProgram_outside {K R S : Type*} [Fintype R]
    [DecidableEq R] [DecidableEq S] (e : K → R ↪ S)
    (ks : List K) (p : List (XorGate R)) (s : S → Bit) (q : S)
    (hq : ∀ k ∈ ks, ∀ r, e k r ≠ q) :
    runProgram (partitionProgram e ks p) s q = s q := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [partitionProgram, List.flatMap_cons, runProgram_append]
    change runProgram (partitionProgram e ks p)
      (runProgram (p.map (XorGate.lift (e k))) s) q = _
    rw [ih _ (fun l hl => hq l (by simp [hl]))]
    exact runProgram_lift_outside (e k) p s q (hq k (by simp))

variable {d : ℕ}

noncomputable instance sideDecidable (S T : Triple d) : Decidable (side S T) :=
  Classical.propDecidable _

noncomputable instance sideIndexFintype (d : ℕ) : Fintype (SideIndex d) :=
  Fintype.ofFinite _

/-- Exact register index set of the full three-round construction. -/
abbrev GlobalReg (d : ℕ) :=
  (DataIndex d ⊕ DataIndex d) ⊕
    (Fin 3 × GroupIndex d × (SideIndex d ⊕ Fin d))

noncomputable instance globalRegDecidableEq (d : ℕ) : DecidableEq (GlobalReg d) :=
  Classical.decEq _

def encodeGlobal (s : GlobalState d) : GlobalReg d → Bit
  | .inl (.inl a) => s.x a
  | .inl (.inr a) => s.y a
  | .inr (j,k,.inl a) => (s.aux j k).1 a
  | .inr (j,k,.inr i) => (s.aux j k).2 i

def decodeGlobal (s : GlobalReg d → Bit) : GlobalState d :=
  ⟨fun a => s (.inl (.inl a)), fun a => s (.inl (.inr a)),
    fun j k => (fun a => s (.inr (j,k,.inl a)),
      fun i => s (.inr (j,k,.inr i)))⟩

@[simp] theorem decodeGlobal_encodeGlobal (s : GlobalState d) :
    decodeGlobal (encodeGlobal s) = s := by
  cases s
  rfl

@[simp] theorem encodeGlobal_decodeGlobal (s : GlobalReg d → Bit) :
    encodeGlobal (decodeGlobal s) = s := by
  funext r
  rcases r with (a | a) | ⟨j,k,(a|i)⟩ <;> rfl

def globalSwap : Equiv.Perm (GlobalReg d) :=
  Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _)

@[simp] theorem globalSwap_involutive (r : GlobalReg d) :
    globalSwap (globalSwap r) = r := by
  rcases r with (a | a) | ⟨j,k,(a|i)⟩ <;> rfl

theorem encode_threeRoundCircuit_correct (s : GlobalState d) :
    encodeGlobal (threeRoundCircuit s) = encodeGlobal s ∘ globalSwap := by
  rw [threeRoundCircuit_correct]
  funext r
  rcases r with (a | a) | ⟨j,k,(a|i)⟩ <;> rfl

noncomputable section

@[simp] theorem side_of_sideIndex (a : SideIndex d) : side a.val.1 a.val.2 :=
  a.property

/-- Local registers; side indices include only actual side wires. -/
inductive LocalReg (d : ℕ) where
  | x : Triple d → LocalReg d
  | y : Triple d → LocalReg d
  | a : SideIndex d → LocalReg d
  | c : Fin d → LocalReg d
  deriving DecidableEq, Fintype

/-- The eight gate classes in Fig. 5, with the displayed indexed vertices. -/
inductive LocalGate (d : ℕ) where
  | g0 : Triple d → LocalGate d
  | g1 : LocalGate d
  | g2 : Triple d → LocalGate d
  | g3 : LocalGate d
  | g4 : LocalGate d
  | g5 : Triple d → LocalGate d
  | g6 : LocalGate d
  | g7 : Triple d → LocalGate d
  deriving DecidableEq, Fintype

/-- Consecutive visited vertices on each register wire, in execution order. -/
def localWireVisits : LocalReg d → List (LocalGate d)
  | .x T => [.g2 T, .g3, .g6, .g7 T]
  | .y S => [.g0 S, .g1, .g4, .g5 S]
  | .a a => [.g0 a.val.1, .g2 a.val.2, .g5 a.val.1, .g7 a.val.2]
  | .c _ => [.g1, .g3, .g4, .g6]

/-- This is the port incidence read directly from the four wire lists. -/
noncomputable def gatePorts (g : LocalGate d) : Finset (LocalReg d) := by
  classical
  exact Finset.univ.filter (fun r => g ∈ localWireVisits r)

@[simp] theorem mem_gatePorts (g : LocalGate d) (r : LocalReg d) :
    r ∈ gatePorts g ↔ g ∈ localWireVisits r := by
  classical
  simp [gatePorts]

/-- Whether a register is updated at this vertex; `backward=true` is the
second operation set, on exactly the same node and port graph. -/
def targetRel : Bool → LocalGate d → LocalReg d → Prop
  | false, .g0 S, .y U => U = S
  | false, .g1, .y _ => True
  | false, .g2 T, .a a => a.val.2 = T
  | false, .g3, .c _ => True
  | false, .g4, .y _ => True
  | false, .g5 S, .y U => U = S
  | false, .g6, .c _ => True
  | false, .g7 T, .a a => a.val.2 = T
  | true, .g0 S, .a a => a.val.1 = S
  | true, .g1, .c _ => True
  | true, .g2 T, .x U => U = T
  | true, .g3, .x _ => True
  | true, .g4, .c _ => True
  | true, .g5 S, .a a => a.val.1 = S
  | true, .g6, .x _ => True
  | true, .g7 T, .x U => U = T
  | _, _, _ => False

/-- Actual control-to-target incidences of the two operation sets. -/
def controlRel : Bool → LocalGate d → LocalReg d → LocalReg d → Prop
  | false, .g0 S, .y U, .a a => U = S ∧ a.val.1 = S
  | false, .g1, .y S, .c i => i ∈ S.val
  | false, .g2 T, .a a, .x U => a.val.2 = T ∧ U = T
  | false, .g3, .c i, .x T => i ∈ T.val
  | false, .g4, .y S, .c i => i ∈ S.val
  | false, .g5 S, .y U, .a a => U = S ∧ a.val.1 = S
  | false, .g6, .c i, .x T => i ∈ T.val
  | false, .g7 T, .a a, .x U => a.val.2 = T ∧ U = T
  | true, .g0 S, .a a, .y U => a.val.1 = S ∧ U = S
  | true, .g1, .c i, .y S => i ∈ S.val
  | true, .g2 T, .x U, .a a => U = T ∧ a.val.2 = T
  | true, .g3, .x T, .c i => i ∈ T.val
  | true, .g4, .c i, .y S => i ∈ S.val
  | true, .g5 S, .a a, .y U => a.val.1 = S ∧ U = S
  | true, .g6, .x T, .c i => i ∈ T.val
  | true, .g7 T, .x U, .a a => U = T ∧ a.val.2 = T
  | _, _, _, _ => False

instance targetRelDecidable (b : Bool) (g : LocalGate d) (r : LocalReg d) :
    Decidable (targetRel b g r) := Classical.propDecidable _

instance controlRelDecidable (b : Bool) (g : LocalGate d) (r c : LocalReg d) :
    Decidable (controlRel b g r c) := Classical.propDecidable _

theorem target_in_ports (b : Bool) (g : LocalGate d) (r : LocalReg d)
    (h : targetRel b g r) : r ∈ gatePorts g := by
  cases b <;> cases g <;> cases r <;>
    simp_all [targetRel, localWireVisits]

theorem control_in_ports (b : Bool) (g : LocalGate d) (r c : LocalReg d)
    (h : controlRel b g r c) : c ∈ gatePorts g := by
  cases b <;> cases g <;> cases r <;> cases c <;>
    simp_all [controlRel, localWireVisits]

/-- Every paper vertex is now an explicit finite XOR gate. -/
def localXorGate (b : Bool) (g : LocalGate d) : XorGate (LocalReg d) := by
  classical
  exact {
    ports := gatePorts g
    targets := Finset.univ.filter (targetRel b g)
    controls := fun r => Finset.univ.filter (controlRel b g r)
    targets_subset := by
      intro r hr
      exact target_in_ports b g r (Finset.mem_filter.mp hr).2
    controls_subset := by
      intro r hr c hc
      exact control_in_ports b g r c (Finset.mem_filter.mp hc).2 }

/-- In particular, the two operation sets have identical ports at EVERY
individual vertex, not merely equal input-output maps. -/
theorem localXorGate_same_ports (g : LocalGate d) :
    (localXorGate false g).ports = (localXorGate true g).ports := rfl

@[simp] theorem eval_localXorGate (b : Bool) (g : LocalGate d)
    (s : LocalReg d → Bit) (r : LocalReg d) :
    (localXorGate b g).eval s r =
      if targetRel b g r then
        s r + ∑ c, if controlRel b g r c then s c else 0
      else s r := by
  classical
  simp [localXorGate, XorGate.eval, Finset.sum_filter]

def localRegEquiv : LocalReg d ≃
    (Triple d ⊕ Triple d) ⊕ (SideIndex d ⊕ Fin d) where
  toFun
    | .x T => .inl (.inl T)
    | .y S => .inl (.inr S)
    | .a a => .inr (.inl a)
    | .c i => .inr (.inr i)
  invFun
    | .inl (.inl T) => .x T
    | .inl (.inr S) => .y S
    | .inr (.inl a) => .a a
    | .inr (.inr i) => .c i
  left_inv r := by cases r <;> rfl
  right_inv r := by rcases r with (T|S)|(a|i) <;> rfl

theorem sum_localReg (f : LocalReg d → Bit) :
    ∑ r, f r = ((∑ T, f (.x T)) + ∑ S, f (.y S)) +
      ((∑ a, f (.a a)) + ∑ i, f (.c i)) := by
  rw [← Equiv.sum_comp localRegEquiv.symm f]
  simp [Fintype.sum_sum_type, localRegEquiv]

/-- Total gate order, retaining separate indexed vertices at layers 0,2,5,7. -/
def localGateOrder : List (LocalGate d) :=
  (Finset.univ.toList.map .g0) ++ [.g1] ++
  (Finset.univ.toList.map .g2) ++ [.g3, .g4] ++
  (Finset.univ.toList.map .g5) ++ [.g6] ++
  (Finset.univ.toList.map .g7)

def localProgram (b : Bool) : List (XorGate (LocalReg d)) :=
  localGateOrder.map (localXorGate b)

/-- The four families of non-public vertices. -/
def indexedNode (k : Fin 4) (T : Triple d) : LocalGate d :=
  match k.val with
  | 0 => .g0 T
  | 1 => .g2 T
  | 2 => .g5 T
  | _ => .g7 T

def indexedBatch (b : Bool) (k : Fin 4) : List (XorGate (LocalReg d)) :=
  Finset.univ.toList.map (fun T => localXorGate b (indexedNode k T))

theorem indexed_controls_independent (b : Bool) (k : Fin 4) :
    IndependentControls (indexedBatch (d := d) b k) := by
  classical
  intro g hg h hh r hr c hc hct
  obtain ⟨S,_,rfl⟩ := List.mem_map.mp hg
  obtain ⟨T,_,rfl⟩ := List.mem_map.mp hh
  simp only [localXorGate, Finset.mem_filter, Finset.mem_univ, true_and] at hr hc hct
  fin_cases k <;> cases b <;> cases r <;> cases c <;>
    simp_all [indexedNode, targetRel, controlRel]

theorem run_indexedBatch (b : Bool) (k : Fin 4)
    (s : LocalReg d → Bit) (r : LocalReg d) :
    runProgram (indexedBatch b k) s r = s r +
      ∑ T, (localXorGate b (indexedNode k T)).delta s r := by
  rw [runProgram_deltas _ (indexed_controls_independent b k)]
  simp [indexedBatch, List.map_map, Finset.sum_map_toList]

@[simp] theorem delta_localXorGate (b : Bool) (g : LocalGate d)
    (s : LocalReg d → Bit) (r : LocalReg d) :
    (localXorGate b g).delta s r =
      if targetRel b g r then ∑ c, if controlRel b g r c then s c else 0 else 0 := by
  classical
  simp [localXorGate, XorGate.delta, Finset.sum_filter]

def encodeBlock (s : BlockState d) : LocalReg d → Bit
  | .x T => s.x T
  | .y S => s.y S
  | .a a => s.a a.val.1 a.val.2
  | .c i => s.c i

def decodeBlock (s : LocalReg d → Bit) : BlockState d :=
  ⟨fun T => s (.x T), fun S => s (.y S),
    extendSide (fun a => s (.a a)), fun i => s (.c i)⟩

@[simp] theorem encodeBlock_decodeBlock (s : LocalReg d → Bit) :
    encodeBlock (decodeBlock s) = s := by
  funext r
  cases r with
  | x T => rfl
  | y S => rfl
  | a a => simp [encodeBlock, decodeBlock, extendSide, a.property]
  | c i => rfl

theorem sum_sideIndex (f : Triple d × Triple d → Bit) :
    ∑ a : SideIndex d, f a.val =
      ∑ S, ∑ T, if side S T then f (S,T) else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p => side p.1 p.2)) (by simp)]
  rw [Finset.sum_filter]
  exact Fintype.sum_prod_type _

theorem sum_side_row (s : BlockState d) (S : Triple d) :
    (∑ a : SideIndex d, if a.val.1 = S then s.a a.val.1 a.val.2 else 0) =
      sideRead s.a S := by
  classical
  rw [sum_sideIndex (fun p => if p.1 = S then s.a p.1 p.2 else 0)]
  unfold sideRead
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  have h : ∀ U : Triple d, (if side U T then
      (if U = S then s.a U T else 0) else 0) =
      if U = S then (if side S T then s.a S T else 0) else 0 := by
    intro U
    by_cases he : U = S
    · subst U; simp
    · simp [he]
  simp_rw [h]
  simp

theorem sum_side_col (s : BlockState d) (T : Triple d) :
    (∑ a : SideIndex d, if a.val.2 = T then s.a a.val.1 a.val.2 else 0) =
      sideRead (fun U S => s.a S U) T := by
  classical
  rw [sum_sideIndex (fun p => if p.2 = T then s.a p.1 p.2 else 0)]
  unfold sideRead
  apply Finset.sum_congr rfl
  intro S _
  have h : ∀ U : Triple d, (if side S U then
      (if U = T then s.a S U else 0) else 0) =
      if U = T then (if side T S then s.a S T else 0) else 0 := by
    intro U
    by_cases he : U = T
    · subst U; simp [side_symmetric]
    · simp [he]
  simp_rw [h]
  simp

def forwardIndexedLayer (k : Fin 4) (s : BlockState d) : BlockState d :=
  if k.val = 0 ∨ k.val = 2 then g0 s else g2 s

theorem forward_indexedBatch (k : Fin 4) (s : BlockState d) :
    runProgram (indexedBatch false k) (encodeBlock s) =
      encodeBlock (forwardIndexedLayer k s) := by
  classical
  funext r
  rw [run_indexedBatch]
  fin_cases k <;> cases r <;>
    simp [indexedNode, delta_localXorGate, targetRel, sum_localReg, controlRel,
      forwardIndexedLayer, encodeBlock, g0, g2, updateSide, sum_side_row]

theorem forward_public1 (s : BlockState d) :
    (localXorGate false .g1).eval (encodeBlock s) = encodeBlock (g1 s) := by
  classical
  funext r
  cases r <;>
    simp [eval_localXorGate, targetRel, sum_localReg, controlRel,
      encodeBlock, g1, centreRead, Fintype.sum_ite_mem] <;>
    first | exact sum_ite_mem_any _ _ _ |
      exact Fintype.sum_congr _ _ (fun _ => ite_inst_congr _ _ _ _)

theorem forward_public3 (s : BlockState d) :
    (localXorGate false .g3).eval (encodeBlock s) = encodeBlock (g3 s) := by
  classical
  funext r
  cases r <;>
    simp [eval_localXorGate, targetRel, sum_localReg, controlRel,
      encodeBlock, g3, updateCentre, centreIncrement] <;>
    exact Fintype.sum_congr _ _ (fun _ => ite_inst_congr _ _ _ _)

theorem forward_public4 (s : BlockState d) :
    (localXorGate false .g4).eval (encodeBlock s) = encodeBlock (g1 s) := by
  classical
  funext r
  cases r <;>
    simp [eval_localXorGate, targetRel, sum_localReg, controlRel,
      encodeBlock, g1, centreRead, Fintype.sum_ite_mem] <;>
    first | exact sum_ite_mem_any _ _ _ |
      exact Fintype.sum_congr _ _ (fun _ => ite_inst_congr _ _ _ _)

theorem forward_public6 (s : BlockState d) :
    (localXorGate false .g6).eval (encodeBlock s) = encodeBlock (g3 s) := by
  classical
  funext r
  cases r <;>
    simp [eval_localXorGate, targetRel, sum_localReg, controlRel,
      encodeBlock, g3, updateCentre, centreIncrement] <;>
    exact Fintype.sum_congr _ _ (fun _ => ite_inst_congr _ _ _ _)

theorem localProgram_forward (s : BlockState d) :
    runProgram (localProgram false) (encodeBlock s) = encodeBlock (firstBlock s) := by
  unfold localProgram localGateOrder
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  change runProgram
    (indexedBatch false 0 ++ [localXorGate false .g1] ++
      indexedBatch false 1 ++ [localXorGate false .g3, localXorGate false .g4] ++
      indexedBatch false 2 ++ [localXorGate false .g6] ++ indexedBatch false 3)
    (encodeBlock s) = _
  simp only [runProgram_append, runProgram, forward_indexedBatch,
    forward_public1, forward_public3, forward_public4, forward_public6]
  rfl

@[simp] theorem side_reverse_of_sideIndex (a : SideIndex d) : side a.val.2 a.val.1 :=
  (side_symmetric _ _).mp a.property

def switched (f : BlockState d → BlockState d) (s : BlockState d) : BlockState d :=
  swapInterfaces (f (swapInterfaces s))

def backwardIndexedLayer (k : Fin 4) (s : BlockState d) : BlockState d :=
  if k.val = 0 ∨ k.val = 2 then switched g2 s else switched g0 s

theorem backward_indexedBatch (k : Fin 4) (s : BlockState d) :
    runProgram (indexedBatch true k) (encodeBlock s) =
      encodeBlock (backwardIndexedLayer k s) := by
  classical
  funext r
  rw [run_indexedBatch]
  fin_cases k <;> cases r <;>
    simp [indexedNode, delta_localXorGate, targetRel, sum_localReg, controlRel,
      backwardIndexedLayer, switched, swapInterfaces, encodeBlock,
      g0, g2, updateSide, sum_side_col]

theorem backward_public1 (s : BlockState d) :
    (localXorGate true .g1).eval (encodeBlock s) = encodeBlock (switched g3 s) := by
  classical
  funext r
  cases r <;>
    simp [eval_localXorGate, targetRel, sum_localReg, controlRel,
      switched, swapInterfaces, encodeBlock, g3, updateCentre, centreIncrement] <;>
    exact Fintype.sum_congr _ _ (fun _ => ite_inst_congr _ _ _ _)

theorem backward_public3 (s : BlockState d) :
    (localXorGate true .g3).eval (encodeBlock s) = encodeBlock (switched g1 s) := by
  classical
  funext r
  cases r <;>
    simp [eval_localXorGate, targetRel, sum_localReg, controlRel,
      switched, swapInterfaces, encodeBlock, g1, centreRead, Fintype.sum_ite_mem] <;>
    first | exact sum_ite_mem_any _ _ _ |
      exact Fintype.sum_congr _ _ (fun _ => ite_inst_congr _ _ _ _)

theorem backward_public4 (s : BlockState d) :
    (localXorGate true .g4).eval (encodeBlock s) = encodeBlock (switched g3 s) := by
  classical
  funext r
  cases r <;>
    simp [eval_localXorGate, targetRel, sum_localReg, controlRel,
      switched, swapInterfaces, encodeBlock, g3, updateCentre, centreIncrement] <;>
    exact Fintype.sum_congr _ _ (fun _ => ite_inst_congr _ _ _ _)

theorem backward_public6 (s : BlockState d) :
    (localXorGate true .g6).eval (encodeBlock s) = encodeBlock (switched g1 s) := by
  classical
  funext r
  cases r <;>
    simp [eval_localXorGate, targetRel, sum_localReg, controlRel,
      switched, swapInterfaces, encodeBlock, g1, centreRead, Fintype.sum_ite_mem] <;>
    first | exact sum_ite_mem_any _ _ _ |
      exact Fintype.sum_congr _ _ (fun _ => ite_inst_congr _ _ _ _)

theorem localProgram_backward (s : BlockState d) :
    runProgram (localProgram true) (encodeBlock s) = encodeBlock (secondBlock s) := by
  unfold localProgram localGateOrder
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  change runProgram
    (indexedBatch true 0 ++ [localXorGate true .g1] ++
      indexedBatch true 1 ++ [localXorGate true .g3, localXorGate true .g4] ++
      indexedBatch true 2 ++ [localXorGate true .g6] ++ indexedBatch true 3)
    (encodeBlock s) = _
  simp only [runProgram_append, runProgram, backward_indexedBatch,
    backward_public1, backward_public3, backward_public4, backward_public6]
  simp only [backwardIndexedLayer, Fin.reduceFinMk, switched]
  simp only [swapInterfaces_twice]
  rfl

def blockOperation (b : Bool) : BlockState d → BlockState d :=
  if b then secondBlock else firstBlock

theorem localProgram_correct (b : Bool) (s : BlockState d) :
    runProgram (localProgram b) (encodeBlock s) = encodeBlock (blockOperation b s) := by
  cases b
  · exact localProgram_forward s
  · exact localProgram_backward s

def localToGlobalFun (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (k : GroupIndex d) : LocalReg d → GlobalReg d
  | .x T => .inl (.inl (e.symm (k,T)))
  | .y S => .inl (.inr (e.symm (k,S)))
  | .a a => .inr (j,k,.inl a)
  | .c i => .inr (j,k,.inr i)

def localToGlobal (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (k : GroupIndex d) : LocalReg d ↪ GlobalReg d where
  toFun := localToGlobalFun e j k
  inj' := by
    intro r t h
    cases r <;> cases t <;>
      simp_all [localToGlobalFun, e.symm.injective.eq_iff]

theorem localToGlobal_apply (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (k : GroupIndex d) (r : LocalReg d) :
    localToGlobal e j k r = localToGlobalFun e j k r := rfl

theorem localToGlobal_disjoint (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (k l : GroupIndex d) (hkl : k ≠ l)
    (r t : LocalReg d) : localToGlobal e j k r ≠ localToGlobal e j l t := by
  intro he
  cases r <;> cases t <;>
    simp_all [localToGlobal_apply, localToGlobalFun, Function.Embedding.coeFn_mk, e.symm.injective.eq_iff]

theorem restrictGlobal_groupInput (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (s : GlobalState d) (k : GroupIndex d) :
    encodeGlobal s ∘ localToGlobal e j k = encodeBlock (groupInput e j s k) := by
  funext r
  cases r with
  | x T => rfl
  | y S => rfl
  | a a =>
    simp [encodeGlobal, localToGlobal_apply, localToGlobalFun, encodeBlock,
      groupInput, extendSide, Function.comp_def, a.property]
  | c i => rfl

/-- A round is a genuine concatenation of the finite blocks, one per group. -/
def roundProgram (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (b : Bool) : List (XorGate (GlobalReg d)) :=
  partitionProgram (localToGlobal e j) Finset.univ.toList (localProgram b)

theorem run_round_at (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (b : Bool) (s : GlobalState d) (k : GroupIndex d) (r : LocalReg d) :
    runProgram (roundProgram e j b) (encodeGlobal s) (localToGlobal e j k r) =
      encodeBlock (blockOperation b (groupInput e j s k)) r := by
  have h := partitionProgram_restrict (localToGlobal e j)
    (localToGlobal_disjoint e j) Finset.univ.toList (Finset.nodup_toList _)
    (localProgram b) (encodeGlobal s) k
  simp only [Finset.mem_toList, Finset.mem_univ, ite_true] at h
  rw [restrictGlobal_groupInput, localProgram_correct] at h
  exact congrFun h r

theorem run_round_aux_other (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j j' : Fin 3) (hj : j ≠ j') (b : Bool) (s : GlobalReg d → Bit)
    (k : GroupIndex d) (a : SideIndex d ⊕ Fin d) :
    runProgram (roundProgram e j b) s (.inr (j',k,a)) = s (.inr (j',k,a)) := by
  apply partitionProgram_outside
  intro l _ r
  cases r <;> simp [localToGlobal_apply, localToGlobalFun, hj]

theorem roundProgram_correct (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (b : Bool) (s : GlobalState d) :
    runProgram (roundProgram e j b) (encodeGlobal s) =
      encodeGlobal (executeGrouped e j (blockOperation b) s) := by
  funext q
  rcases q with (a|a)|⟨j',k,(a|i)⟩
  · have h := run_round_at e j b s (e a).1 (.x (e a).2)
    simpa [localToGlobal_apply, localToGlobalFun, encodeBlock, encodeGlobal,
      executeGrouped] using h
  · have h := run_round_at e j b s (e a).1 (.y (e a).2)
    simpa [localToGlobal_apply, localToGlobalFun, encodeBlock, encodeGlobal,
      executeGrouped] using h
  · by_cases hj : j' = j
    · subst j'
      have h := run_round_at e j b s k (.a a)
      simpa [localToGlobal_apply, localToGlobalFun, encodeBlock, encodeGlobal,
        executeGrouped, restrictSide] using h
    · rw [run_round_aux_other e j j' (Ne.symm hj)]
      simp [encodeGlobal, executeGrouped, hj]
  · by_cases hj : j' = j
    · subst j'
      have h := run_round_at e j b s k (.c i)
      simpa [localToGlobal_apply, localToGlobalFun, encodeBlock, encodeGlobal,
        executeGrouped] using h
    · rw [run_round_aux_other e j j' (Ne.symm hj)]
      simp [encodeGlobal, executeGrouped, hj]

/-- The actual finite gate list for all three rounds of the paper. -/
def globalProgram (d : ℕ) : List (XorGate (GlobalReg d)) :=
  roundProgram grouping1 0 false ++ roundProgram grouping2 1 true ++
    roundProgram grouping3 2 false

theorem globalProgram_eq_threeRound (s : GlobalState d) :
    runProgram (globalProgram d) (encodeGlobal s) =
      encodeGlobal (threeRoundCircuit s) := by
  unfold globalProgram
  simp only [runProgram_append, roundProgram_correct]
  rfl

/-- No unproved local-function hypothesis: this executes the explicit finite
list of XOR gates and proves the complete demanded permutation. -/
theorem globalProgram_correct (s : GlobalReg d → Bit) :
    runProgram (globalProgram d) s = s ∘ globalSwap := by
  have h := globalProgram_eq_threeRound (decodeGlobal s)
  rw [encodeGlobal_decodeGlobal, encode_threeRoundCircuit_correct,
    encodeGlobal_decodeGlobal] at h
  exact h

/-- Vertex identities, independent of the Boolean choice of gate operation. -/
abbrev GlobalGate (d : ℕ) := Fin 3 × GroupIndex d × LocalGate d

instance globalGateDecidableEq (d : ℕ) : DecidableEq (GlobalGate d) := Classical.decEq _

def groupingAt (j : Fin 3) : DataIndex d ≃ GroupIndex d × Triple d :=
  match j.val with
  | 0 => grouping1
  | 1 => grouping2
  | _ => grouping3

def operationAt (j : Fin 3) : Bool := decide (j.val = 1)

def groupNodeOrder (j : Fin 3) : List (GlobalGate d) :=
  Finset.univ.toList.flatMap (fun k : GroupIndex d =>
    localGateOrder.map (fun g => (j,k,g)))

def globalGateOrder (d : ℕ) : List (GlobalGate d) :=
  groupNodeOrder 0 ++ groupNodeOrder 1 ++ groupNodeOrder 2

def globalNodeGate (u : GlobalGate d) : XorGate (GlobalReg d) :=
  (localXorGate (operationAt u.1) u.2.2).lift
    (localToGlobal (groupingAt u.1) u.1 u.2.1)

theorem globalGateOrder_program :
    (globalGateOrder d).map globalNodeGate = globalProgram d := by
  simp [globalGateOrder, groupNodeOrder, globalNodeGate, globalProgram,
    roundProgram, partitionProgram, localProgram, groupingAt, operationAt,
    List.map_append, List.map_flatMap, List.map_map, Function.comp_def]

def dataGateVisits (isX : Bool) (a : DataIndex d) (j : Fin 3) : List (GlobalGate d) :=
  let b := groupingAt j a
  (localWireVisits (if isX then .x b.2 else .y b.2)).map (fun g => (j,b.1,g))

/-- Explicit chronological vertices along every actual register wire. -/
def globalWireVisits : GlobalReg d → List (GlobalGate d)
  | .inl (.inl a) => dataGateVisits true a 0 ++ dataGateVisits true a 1 ++ dataGateVisits true a 2
  | .inl (.inr a) => dataGateVisits false a 0 ++ dataGateVisits false a 1 ++ dataGateVisits false a 2
  | .inr (j,k,.inl a) => (localWireVisits (.a a)).map (fun g => (j,k,g))
  | .inr (j,k,.inr i) => (localWireVisits (.c i)).map (fun g => (j,k,g))

theorem filter_singleton_of_nodup {A : Type*} [DecidableEq A]
    (l : List A) (hn : l.Nodup) (a : A) (ha : a ∈ l) :
    l.filter (fun b => decide (b = a)) = [a] := by
  induction l with
  | nil => simp at ha
  | cons b bs ih =>
    obtain ⟨hb, hbs⟩ := List.nodup_cons.mp hn
    by_cases he : b = a
    · subst b
      have hf : bs.filter (fun b => decide (b = a)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hbm
        simp only [decide_eq_true_eq]
        intro hba
        subst b
        exact hb hbm
      simp [hf]
    · have htail : a ∈ bs := by simpa [Ne.symm he] using ha
      simp [he, ih hbs htail]

@[simp] theorem filter_univ_singleton {A : Type*} [Fintype A] [DecidableEq A] (a : A) :
    Finset.univ.toList.filter (fun b => decide (b = a)) = [a] :=
  filter_singleton_of_nodup _ (Finset.nodup_toList _) a (by simp)

theorem flatMap_if_single {A B : Type*} [Fintype A] [DecidableEq A]
    (a : A) (f : A → List B) :
    Finset.univ.toList.flatMap (fun b => if b = a then f b else []) = f a := by
  have h : ∀ l : List A,
      l.flatMap (fun b => if b = a then f b else []) =
        (l.filter (fun b => decide (b = a))).flatMap f := by
    intro l
    induction l with
    | nil => rfl
    | cons b bs ih =>
      by_cases he : b = a <;> simp [he, ih]
  rw [h, filter_univ_singleton]
  simp

theorem localGateOrder_filter (r : LocalReg d) :
    localGateOrder.filter (fun g => decide (r ∈ gatePorts g)) = localWireVisits r := by
  cases r <;>
    simp [localGateOrder, List.filter_append, List.filter_map,
      localWireVisits, mem_gatePorts, Function.comp_def]

theorem localGateOrder_filter_visits (r : LocalReg d) :
    localGateOrder.filter (fun g => decide (g ∈ localWireVisits r)) = localWireVisits r := by
  simpa only [mem_gatePorts] using localGateOrder_filter r

theorem mem_group_gate_ports (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (k l : GroupIndex d) (b : Bool) (g : LocalGate d) (r : LocalReg d) :
    localToGlobal e j k r ∈ ((localXorGate b g).lift (localToGlobal e j l)).ports ↔
      k = l ∧ r ∈ gatePorts g := by
  classical
  by_cases he : k = l
  · subst l
    simp [XorGate.lift, localXorGate]
  · constructor
    · intro hm
      obtain ⟨t, ht, het⟩ := Finset.mem_map.mp hm
      exact (localToGlobal_disjoint e j l k (Ne.symm he) t r het).elim
    · intro hh
      exact (he hh.1).elim

theorem filter_groupNodeOrder_at (j : Fin 3) (k : GroupIndex d) (r : LocalReg d) :
    (groupNodeOrder j).filter
      (fun u => decide (localToGlobal (groupingAt j) j k r ∈ (globalNodeGate u).ports)) =
        (localWireVisits r).map (fun g => (j,k,g)) := by
  classical
  unfold groupNodeOrder
  rw [List.filter_flatMap]
  have hb : ∀ l : GroupIndex d,
      (localGateOrder.map (fun g => (j,l,g))).filter
        (fun u => decide (localToGlobal (groupingAt j) j k r ∈ (globalNodeGate u).ports)) =
      if l = k then (localWireVisits r).map (fun g => (j,l,g)) else [] := by
    intro l
    rw [List.filter_map]
    by_cases he : l = k
    · subst l
      simp [globalNodeGate, Function.comp_def, mem_group_gate_ports,
        localGateOrder_filter, localGateOrder_filter_visits]
    · simp [globalNodeGate, Function.comp_def, mem_group_gate_ports, he, Ne.symm he]
  simp_rw [hb]
  exact flatMap_if_single k _

theorem other_round_aux_not_in_ports (j j' : Fin 3) (hj : j ≠ j')
    (k l : GroupIndex d) (a : SideIndex d ⊕ Fin d) (g : LocalGate d) :
    (.inr (j',k,a) : GlobalReg d) ∉ (globalNodeGate (j,l,g)).ports := by
  intro hm
  obtain ⟨r, _, hr⟩ := Finset.mem_map.mp hm
  cases r <;> simp [localToGlobal_apply, localToGlobalFun] at hr
  all_goals exact hj hr.1

theorem filter_groupNodeOrder_aux_other (j j' : Fin 3) (hj : j ≠ j')
    (k : GroupIndex d) (a : SideIndex d ⊕ Fin d) :
    (groupNodeOrder j).filter
      (fun u => decide ((.inr (j',k,a) : GlobalReg d) ∈ (globalNodeGate u).ports)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro u hu
  obtain ⟨l, _, h⟩ := List.mem_flatMap.mp hu
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp h
  simpa using other_round_aux_not_in_ports j j' hj k l a g

theorem filter_groupNodeOrder_data (j : Fin 3) (a : DataIndex d) (b : Bool) :
    (groupNodeOrder j).filter
      (fun u => decide ((if b then .inl (.inl a) else .inl (.inr a) : GlobalReg d)
        ∈ (globalNodeGate u).ports)) = dataGateVisits b a j := by
  have h := filter_groupNodeOrder_at j (groupingAt j a).1
    (if b then .x (groupingAt j a).2 else .y (groupingAt j a).2)
  cases b <;>
    simpa [localToGlobal_apply, localToGlobalFun, dataGateVisits] using h

/-- The hand-written wire paths are EXACTLY the incident gates in the actual
program order. This connects the drawn graph to the gate-list semantics. -/
theorem globalWireVisits_eq_filter (r : GlobalReg d) :
    globalWireVisits r = (globalGateOrder d).filter
      (fun u => decide (r ∈ (globalNodeGate u).ports)) := by
  rcases r with (a|a)|⟨j,k,(a|i)⟩
  · simp only [globalWireVisits, globalGateOrder, List.filter_append]
    exact congrArg₂ List.append
      (congrArg₂ List.append (filter_groupNodeOrder_data 0 a true).symm
        (filter_groupNodeOrder_data 1 a true).symm)
      (filter_groupNodeOrder_data 2 a true).symm
  · simp only [globalWireVisits, globalGateOrder, List.filter_append]
    exact congrArg₂ List.append
      (congrArg₂ List.append (filter_groupNodeOrder_data 0 a false).symm
        (filter_groupNodeOrder_data 1 a false).symm)
      (filter_groupNodeOrder_data 2 a false).symm
  · have h := filter_groupNodeOrder_at j k (.a a)
    simp only [localToGlobal_apply, localToGlobalFun, Function.Embedding.coeFn_mk] at h
    fin_cases j <;>
      simp [globalWireVisits, globalGateOrder, List.filter_append,
        filter_groupNodeOrder_aux_other]
    all_goals exact h.symm
  · have h := filter_groupNodeOrder_at j k (.c i)
    simp only [localToGlobal_apply, localToGlobalFun, Function.Embedding.coeFn_mk] at h
    fin_cases j <;>
      simp [globalWireVisits, globalGateOrder, List.filter_append,
        filter_groupNodeOrder_aux_other]
    all_goals exact h.symm

end

end CSL.CircuitProgram


