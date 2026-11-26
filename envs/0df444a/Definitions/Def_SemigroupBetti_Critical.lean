-- Prove2me | Definitions.Def_SemigroupBetti_Critical
-- name    : SemigroupBetti_Critical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:52:28.174659+00:00
-- url     : https://prove2.me/theorems/cced483d-14a9-4eb6-8510-048ddea1de8d
-- title:
--   Critical
-- statement:
--   Definitions and structural lemmas for Critical, from Ben Keene (BenKeene/semigroup-betti; see pinned Apache-2.0 LICENSE and source headers)'s pinned Linear upper bound for the first Betti number of four-generated numerical semigroups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_pos
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_single
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.mem_fiber
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp


set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SemigroupBetti
open Finset
namespace GenData
variable (G : GenData)
def IsCritCand (i : Fin 4) (k : ℕ) : Prop :=
  1 ≤ k ∧ ∃ y ∈ G.fiber (k * G.n i), y ≠ Pi.single i k
instance (i : Fin 4) : DecidablePred (G.IsCritCand i) := fun k =>
  inferInstanceAs (Decidable (1 ≤ k ∧ ∃ y ∈ G.fiber (k * G.n i), y ≠ Pi.single i k))
lemma isCritCand_iff {i : Fin 4} {k : ℕ} :
    G.IsCritCand i k ↔ 1 ≤ k ∧ ∃ y : Fin 4 → ℕ, G.nu y = k * G.n i ∧ y ≠ Pi.single i k := by
  simp [IsCritCand]
lemma isCritCand_n {i j : Fin 4} (hji : j ≠ i) : G.IsCritCand i (G.n j) := by
  rw [isCritCand_iff]
  refine ⟨G.n_pos j, Pi.single j (G.n i), by rw [G.nu_single, mul_comm], ?_⟩
  intro h
  have := congrFun h j
  simp [hji, (G.n_pos i).ne'] at this
lemma succ_ne (i : Fin 4) : i + 1 ≠ i := by fin_cases i <;> decide
lemma crit_exists (i : Fin 4) : ∃ k, G.IsCritCand i k := ⟨_, G.isCritCand_n (succ_ne i)⟩
def crit (i : Fin 4) : ℕ := Nat.find (G.crit_exists i)
def critVertex (i : Fin 4) : G.fiber (G.crit i * G.n i) :=
  ⟨Pi.single i (G.crit i), G.mem_fiber.2 (G.nu_single i _)⟩
def HasSingletonComp (d : ℕ) : Prop :=
  ∃ C : (G.nabla d).ConnectedComponent, (G.compSupp C).card = 1
noncomputable def singletonDegrees : Finset ℕ := by
  classical
  exact (range (G.H + 1)).filter (fun d => G.contributes d ∧ G.HasSingletonComp d)
noncomputable def sigma : ℕ := ∑ d ∈ G.singletonDegrees, (G.ncomp d - 1)
def critIndices (d : ℕ) : Finset (Fin 4) := univ.filter (fun i => G.crit i * G.n i = d)
end GenData
end SemigroupBetti


