-- Prove2me | Definitions.Def_N25_LocalCarrier
-- name    : N25_LocalCarrier
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:17.579866+00:00
-- url     : https://prove2.me/theorems/72d3568c-ae65-4f6a-936d-8837265e0caa
-- title:
--   Local fixed-point carrier at $5$
-- statement:
--   Selects the local Galois group at $5$, its restriction map to the global Galois group, and inertia, then defines the subgroup $M_5$ of points fixed by the restricted local action and the selected kernel $V$. This is the literal carrier on which the local Kummer operators and divisibility condition are formulated.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25
import Definitions.Def_ExtEndgame_ProductionDatum
noncomputable section
namespace N25

def q5 : Nat.Primes := ⟨5, by decide⟩
abbrev G5 : Type := ExtCitation.primeLocalGaloisGroup q5
noncomputable def r5 : G5 →* Gal := ExtCitation.primeLocalToGlobal q5
noncomputable def I5 : Subgroup G5 :=
  ((ExtCitation.primeLocalPlace q5).inertiaSubgroupIn ℚ).comap r5

/-- The literal subgroup fixed by the supplied local restriction. -/
def M5 : AddSubgroup J where
  carrier := {x | ∀ τ : G5, r5 τ • x = x}
  zero_mem' := by intro τ; exact smul_zero _
  add_mem' := by intro x y hx hy τ; rw [smul_add, hx τ, hy τ]
  neg_mem' := by intro x hx τ; rw [smul_neg, hx τ]

def V : AddSubgroup J := piEnd.ker
end N25


