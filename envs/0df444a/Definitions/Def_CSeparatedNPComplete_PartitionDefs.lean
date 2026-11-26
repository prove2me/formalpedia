-- Prove2me | Definitions.Def_CSeparatedNPComplete_PartitionDefs
-- name    : CSeparatedNPComplete_PartitionDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:45:55.023509+00:00
-- url     : https://prove2.me/theorems/80fb8e1d-df8f-4e4c-b7e4-b00da993e3e5
-- title:
--   Partition Defs
-- statement:
--   Definitions and structural lemmas for Partition Defs, from Tomislav Prusina (tomo61098/c-separated-np-complete-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Fixed-threshold Gaussian c-separation gadget equivalence and square-partition reduction development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionDefs.lean

module
public import Definitions.Def_CSeparatedNPComplete_Definitions
public import Mathlib.Analysis.Real.Sqrt
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace CSeparatedNPComplete
def is_binary {n : Nat} (a : Vec n) : Prop := ∀ i, a i = 0 ∨ a i = 1
def is_vec_leq {n : Nat} (a b : Vec n) : Prop := ∀ i, a i ≤ b i
def perf_square_vec {n : Nat} (s : Vec n) : Prop :=
  ∀ i, ∃ k : Nat, s i = (k : ℝ) * (k : ℝ)
def box_constraints {n : Nat} (a : Vec n) : Prop :=
  is_vec_leq 0 a ∧ is_vec_leq a 1
def is_ec_partition {n : Nat} (a s : Vec n) : Prop :=
  is_binary a ∧ dot a 1 = (n : ℝ) / 2 ∧ dot a s = dot s 1 / 2
def canon_e {n : Nat} (k : Nat) : Vec n := fun i => if i.val = k then 1 else 0
def hinge (c D S : ℝ) : ℝ := max 0 (c - D / S)
def gaussian_pair_stats {n : Nat} (a : Vec n) (p : Gaussian n × Gaussian n) : ℝ × ℝ :=
  (dot a (sqVec (p.1.1 - p.2.1)), max (dot a p.1.2) (dot a p.2.2))
def gaussian_pair_hinge {n : Nat} (c : ℝ) (a : Vec n) (g h : Gaussian n) : ℝ :=
  let (D, S) := gaussian_pair_stats a (g, h)
  hinge c D S
def hinge_against {n : Nat} (c : ℝ) (a : Vec n) (g : Gaussian n) :
    List (Gaussian n) → ℝ
  | [] => 0
  | h :: tail => gaussian_pair_hinge c a g h + hinge_against c a g tail
def hinge_form {n : Nat} (c : ℝ) (a : Vec n) : List (Gaussian n) → ℝ
  | [] => 0
  | g :: tail => hinge_against c a g tail + hinge_form c a tail
def hinge_to {n : Nat} (c : ℝ) (a : Vec n) (L : List (Gaussian n))
    (g : Gaussian n) : ℝ := (L.map (fun h => gaussian_pair_hinge c a h g)).sum
def gaussian_schedule_separation_sum (m : ℝ) (i k : Nat) : ℝ :=
  ∑ j ∈ Finset.range k, (m ^ i - m ^ j) ^ 2
def gaussian_schedule_mu {n : Nat} (m : ℝ) (i : Nat) : Vec n := fun _ => m ^ i
def gaussian_schedule_sigma {n : Nat} (m : ℝ) (i : Nat) : Vec n :=
  if i = 0 then 1 else
    fun j => gaussian_schedule_separation_sum m i i * (m * canon_e (i - 1) j + 1)
def gaussian_schedule_class {n : Nat} (m : ℝ) (i : Nat) : Gaussian n :=
  (gaussian_schedule_mu m i, gaussian_schedule_sigma m i)
def gaussian_schedule {n : Nat} (m : ℝ) (k : Nat) : List (Gaussian n) :=
  (List.range k).map (gaussian_schedule_class m)
def gaussian_schedule_hinge_correction {n : Nat} (a : Vec n) (k : Nat) : ℝ :=
  ∑ j ∈ Finset.range k, (1 + dot a (canon_e j))⁻¹
def second_gadget_gamma (n : Nat) (m : ℝ) : ℝ :=
  m + gaussian_schedule_separation_sum m n n
def second_gadget_mu1 {n : Nat} (m c : ℝ) : Vec n :=
  fun _ => second_gadget_gamma n m * (3 * c + m ^ n)
def second_gadget_mu2 {n : Nat} (m c : ℝ) (s : Vec n) : Vec n :=
  fun i => second_gadget_gamma n m * (3 * c + m ^ n + m * Real.sqrt (s i))
def second_gadget_mu3 {n : Nat} (m c : ℝ) : Vec n :=
  fun _ => second_gadget_gamma n m * (2 * c + m ^ n)
def second_gadget_sigma1 {n : Nat} (m : ℝ) : Vec n :=
  fun _ => second_gadget_gamma n m * second_gadget_gamma n m
def second_gadget_sigma2 {n : Nat} (m : ℝ) : Vec n :=
  fun _ => second_gadget_gamma n m * second_gadget_gamma n m * m
def second_gadget_sigma3 {n : Nat} (m : ℝ) (s : Vec n) : Vec n :=
  fun i => second_gadget_gamma n m * second_gadget_gamma n m * m * s i
def second_gadget_g1 {n : Nat} (m c : ℝ) : Gaussian n :=
  (second_gadget_mu1 m c, second_gadget_sigma1 m)
def second_gadget_g2 {n : Nat} (m c : ℝ) (s : Vec n) : Gaussian n :=
  (second_gadget_mu2 m c s, second_gadget_sigma2 m)
def second_gadget_g3 {n : Nat} (m c : ℝ) (s : Vec n) : Gaussian n :=
  (second_gadget_mu3 m c, second_gadget_sigma3 m s)
def second_gadget_instance {n : Nat} (m c : ℝ) (s : Vec n) : List (Gaussian n) :=
  [second_gadget_g1 m c, second_gadget_g2 m c s, second_gadget_g3 m c s]
def second_gadget_partition_instance {n : Nat} (m : ℝ) (s : Vec n) :
    List (Gaussian n) := second_gadget_instance m (dot s 1 / 2) s
def partition_gadget_schedule (d : Nat) (s : Vec d) : List (Gaussian d) :=
  second_gadget_partition_instance ((d : ℝ) / 2) s ++
    gaussian_schedule ((d : ℝ) / 2) (d + 1)
def partition_schedule_threshold (d : Nat) (s : Vec d) : ℝ :=
  dot s 1 / 2 * (d : ℝ) * ((d : ℝ) + 1) / 2 - 3 * (d : ℝ) / 4
end CSeparatedNPComplete


