-- Prove2me | Definitions.Def_ChipFiringWithLean_Algorithms
-- name    : ChipFiringWithLean_Algorithms
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:51:28.615402+00:00
-- url     : https://prove2.me/theorems/4898f246-40b2-4337-9767-ac2f832482fc
-- title:
--   Algorithms
-- statement:
--   Definitions and structural lemmas for Algorithms, from DhyeyMavani2003/chip-firing-with-lean contributors (see pinned LICENSE and source headers)'s pinned Chip-firing on multigraphs and Riemann-Roch for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Algorithms.lean

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CF
open Finset BigOperators List
@[simp]
def is_effective (D : CFDiv G) : Bool := decide (∀ v, D v ≥ 0)
def divisorMagnitude (G : CFGraph) (D : CFDiv G) : Nat :=
  ∑ v : G.V, Int.natAbs (D v)
def greedyFuel (G : CFGraph) (D : CFDiv G) : Nat :=
  (Fintype.card G.V + 1) * (divisorMagnitude G D + 1) ^ 2 + 1
def nonSourceChipCount (G : CFGraph) (q : G.V) (D : CFDiv G) : Nat :=
  ∑ v ∈ Finset.univ.erase q, Int.toNat (D v)
@[simp]
noncomputable def greedyWinnable (G : CFGraph) (D : CFDiv G) : Bool × Option (CFDiv G) :=
  let rec loop (current_D : CFDiv G) (M : Finset G.V) (script : CFDiv G) (fuel : Nat) : Bool × Option (CFDiv G) :=
    if _h_fuel_zero : fuel = 0 then (false, none) -- Fuel exhaustion implies failure
    else if is_effective current_D then (true, some script)
    else if M = Finset.univ then (false, none) -- All vertices borrowed, still not effective
    else
      -- Find any in-debt vertex. The marked set only records which vertices have
      -- borrowed at least once; it does not prevent a vertex from borrowing again.
      match Finset.univ.toList.find? (fun v => current_D v < 0) with
      | some v =>
          let next_D := borrowing_move G current_D v
          let next_M := insert v M
          -- Update script: decrement count for borrowing vertex v
          let next_script : CFDiv G := script - one_chip v
          loop next_D next_M next_script (fuel - 1)
      | none => -- No vertex is in debt, but `D` is not effective.
          -- This state implies unwinnability because we can't make progress.
          (false, none)
  termination_by fuel
  decreasing_by simp_wf; exact Nat.pos_of_ne_zero _h_fuel_zero -- Simpler explicit proof
  -- Initial call with generous fuel
  let max_fuel := greedyFuel G D
  loop D ∅ (0 : CFDiv G) max_fuel
noncomputable def findBurnableVertex (G : CFGraph) (c : G.V → ℤ) (S : Finset G.V) : Option { v : G.V // v ∈ S } :=
  -- Iterate through the list representation and find the first match
  -- Need to get proof v ∈ S, which is guaranteed by iterating S.toList
  let p := fun v => decide (c v < outdeg_S G S v) -- Use decide
  match h : S.toList.find? p with -- Use find? directly now (List is open)
  | some v =>
    -- Prove v is in the original finset S
    have h_mem_list : v ∈ S.toList := List.mem_of_find?_eq_some h
    have h_mem_finset : v ∈ S := Finset.mem_toList.mp h_mem_list
    some ⟨v, h_mem_finset⟩
  | none => none
@[simp]
noncomputable def dharBurningSet (G : CFGraph) (q : G.V) (c : G.V → ℤ) : Finset G.V :=
  let initial_S := Finset.univ.erase q
  let rec loop (S : Finset G.V) (fuel : Nat) : Finset G.V :=
    -- Check fuel for termination safety
    if _h_fuel_zero : fuel = 0 then S -- Name hypothesis
    else
      match findBurnableVertex G c S with
      -- If a burnable vertex v is found, remove it and recurse
      | some ⟨v, hv⟩ => loop (S.erase v) (fuel - 1)
      -- If no burnable vertex found in S, S is stable, return it
      | none        => S
  termination_by fuel
  decreasing_by simp_wf; exact Nat.pos_of_ne_zero _h_fuel_zero -- Simpler explicit proof
  loop initial_S (Fintype.card G.V + 1)
@[simp]
noncomputable def fireSet (G : CFGraph) (D : CFDiv G) (S : Finset G.V) : CFDiv G :=
  -- Use foldl directly now (List is open)
  foldl (fun current_D v => firing_move G current_D v) D S.toList
noncomputable def makeNonNegativeExceptQ (G : CFGraph) (q : G.V) (D : CFDiv G) (max_fuel : Nat) : Option (CFDiv G) :=
  let rec loop (current_D : CFDiv G) (fuel : Nat) : Option (CFDiv G) :=
    if _h_fuel_zero : fuel = 0 then none -- Name hypothesis
    else
      -- Check if any vertex v != q has D(v) < 0
      let non_q_vertices := Finset.univ.erase q
      -- Use `find?` to efficiently check for a negative vertex
      match non_q_vertices.toList.find? (fun v => current_D v < 0) with
      | none => some current_D -- Goal reached: all v != q are non-negative
      | some v => -- Found a vertex v != q with current_D v < 0
          -- Borrow at the in-debt non-source vertex and continue.
          loop (borrowing_move G current_D v) (fuel - 1)
  termination_by fuel
  decreasing_by simp_wf; exact Nat.pos_of_ne_zero _h_fuel_zero -- Simpler explicit proof
  loop D max_fuel
@[simp]
noncomputable def findQReducedDivisor (G : CFGraph) (q : G.V) (D : CFDiv G) : Option (CFDiv G) :=
  -- Preprocessing: borrow at in-debt non-source vertices until D(v) >= 0 for v != q.
  -- Use chip-size-aware fuel rather than a graph-size-only bound.
  let preprocess_fuel : Nat := greedyFuel G D
  match makeNonNegativeExceptQ G q D preprocess_fuel with
  | none => none -- Preprocessing failed
  | some D_preprocessed =>
      let rec loop (current_D : CFDiv G) (fuel : Nat) : CFDiv G :=
        if h_fuel_zero : fuel = 0 then -- Name hypothesis
          -- Fuel exhausted in main loop, return current state (might not be fully q-reduced)
          current_D
        else
          -- Use current_D as the configuration function for dharBurningSet
          let S := dharBurningSet G q current_D
          -- If the set S is non-empty, fire it and continue looping
          if hs : S.Nonempty then
            loop (fireSet G current_D S) (fuel - 1)
          else
            -- S is empty, the divisor is q-reduced
            current_D
      termination_by fuel
      decreasing_by simp_wf; exact Nat.pos_of_ne_zero h_fuel_zero -- Simpler explicit proof
      -- Estimate fuel for main loop from possible q-effective non-source chip vectors.
      let main_loop_fuel := (nonSourceChipCount G q D_preprocessed + 1) ^ Fintype.card G.V + 1
      some (loop D_preprocessed main_loop_fuel)
@[simp]
noncomputable def burn (G : CFGraph) (q : G.V) (c : G.V → ℤ) : Finset G.V :=
  dharBurningSet G q c
@[simp]
noncomputable def dhar (G : CFGraph) (D : CFDiv G) (v : G.V) : Option (CFDiv G) :=
  findQReducedDivisor G v D
@[simp]
noncomputable def isWinnable (G : CFGraph) (q : G.V) (D : CFDiv G) : Bool :=
  match findQReducedDivisor G q D with
  | none => false -- Reduction process failed (preprocessing or main loop fuel)
  | some D_q => D_q q >= 0
def burning_indeg (G : CFGraph) (B : Finset G.V) (v : G.V) : ℤ :=
  ∑ u ∈ B, (num_edges G u v : ℤ)
@[simp]
noncomputable def dharBurningSetWithOrientation (G : CFGraph) (q : G.V) (c : G.V → ℤ)
  : Finset G.V × Multiset (G.V × G.V) :=
  let initial_S := Finset.univ.erase q
  let initial_B := {q}
  let initial_O := (∅ : Multiset (G.V × G.V))

  let rec loop (current_S : Finset G.V) (current_B : Finset G.V) (current_O : Multiset (G.V × G.V)) (fuel : Nat)
    : Finset G.V × Multiset (G.V × G.V) :=
    if h_fuel : fuel = 0 then (current_S, current_O) -- Fuel exhausted, return current state
    else
      -- Find vertices in S that burn in this step
      let newly_burned_list := current_S.toList.filter (fun v => burning_indeg G current_B v > c v)
      let newly_burned := newly_burned_list.toFinset -- Use List.toFinset

      -- If no new vertices burned, the process stabilizes
      if newly_burned.card = 0 then (current_S, current_O) -- Use card = 0 check
      else
        -- Update S and B
        let next_S := current_S.filter (fun v => v ∉ newly_burned) -- Manual set difference
        let next_B := current_B ∪ newly_burned

        -- Update Orientation: Add edges from current_B to newly_burned
        -- Use Finset.sum for clarity and potentially better type inference
        let edges_to_add : Multiset (G.V × G.V) :=
          Finset.sum newly_burned (fun v_new => -- Sum over newly burned vertices
            Finset.sum current_B (fun u => -- For each u in the burning set
              Multiset.replicate (num_edges G u v_new) (u, v_new) -- Create edges u -> v_new
            )
          )

        let next_O := current_O + edges_to_add

        -- Recurse
        loop next_S next_B next_O (fuel - 1)

  termination_by fuel
  decreasing_by simp_wf; exact Nat.pos_of_ne_zero h_fuel -- Use robust termination proof

  -- Initial call with fuel based on number of vertices
  loop initial_S initial_B initial_O (Fintype.card G.V + 1)
end CF


