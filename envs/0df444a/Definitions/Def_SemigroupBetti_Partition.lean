-- Prove2me | Definitions.Def_SemigroupBetti_Partition
-- name    : SemigroupBetti_Partition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:53:13.304006+00:00
-- url     : https://prove2.me/theorems/bd416b91-685f-48cf-a55b-a7e36bb9a7da
-- title:
--   Partition
-- statement:
--   Definitions and structural lemmas for Partition, from Ben Keene (BenKeene/semigroup-betti; see pinned Apache-2.0 LICENSE and source headers)'s pinned Linear upper bound for the first Betti number of four-generated numerical semigroups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean

module
public import Definitions.Def_SemigroupBetti_Critical
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SemigroupBetti
open Finset
namespace GenData
variable (G : GenData)
def IsSplit (d : ℕ) (K : Finset (Fin 4)) : Prop :=
  ∃ C C' : (G.nabla d).ConnectedComponent, C ≠ C' ∧ G.compSupp C = K ∧ G.compSupp C' = Kᶜ
noncomputable def fam (K : Finset (Fin 4)) : Finset ℕ := by
  classical
  exact (range (G.H + 1)).filter
    (fun d => G.contributes d ∧ ¬ G.HasSingletonComp d ∧ G.IsSplit d K)
noncomputable def famP : Finset ℕ := G.fam {0, 1}
noncomputable def famQ : Finset ℕ := G.fam {0, 2}
noncomputable def famE : Finset ℕ := G.fam {0, 3}
noncomputable def P : ℕ := G.famP.card
noncomputable def Q : ℕ := G.famQ.card
noncomputable def E : ℕ := G.famE.card
noncomputable def sel (d : ℕ) (K : Finset (Fin 4)) : Fin 4 → ℕ := by
  classical
  exact if h : ∃ z : Fin 4 → ℕ, G.nu z = d ∧ supp z = K then h.choose else 0
end GenData
end SemigroupBetti


