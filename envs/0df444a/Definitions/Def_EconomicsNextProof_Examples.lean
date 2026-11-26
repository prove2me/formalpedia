-- Prove2me | Definitions.Def_EconomicsNextProof_Examples
-- name    : EconomicsNextProof_Examples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:27:48.595165+00:00
-- url     : https://prove2.me/theorems/ac36fc5b-414c-5b0e-a4bb-cd7e6abd6a7e
-- title:
--   Examples
-- statement:
--   Definitions and structural lemmas for Examples, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/falmagne-block-marschak-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Falmagne-Block-Marschak random-utility characterization of stochastic choice rules development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Falmagne.Examples
open Finset EconomicsNextProof
def regularCounterexampleQ (A : Finset (Fin 4)) (x : Fin 4) : ℚ :=
  if x ∉ A then 0 else
    if (0 : Fin 4) ∈ A ∧ 3 ≤ A.card then
      if x = 0 then 0 else 1 / ((A.card - 1 : ℕ) : ℚ)
    else 1 / (A.card : ℚ)
noncomputable def regularCounterexample (A : Finset (Fin 4)) (x : Fin 4) : ℝ :=
  regularCounterexampleQ A x
def singletonRanking : List (Fin 1) := [0]
noncomputable def singletonLaw : RankingLaw (Fin 1) := Finsupp.single singletonRanking 1
def forwardRanking : List (Fin 4) := [0, 1, 2, 3]
def reverseRanking : List (Fin 4) := [3, 2, 1, 0]
noncomputable def mixtureLaw : RankingLaw (Fin 4) :=
  Finsupp.single forwardRanking (1 / 2) + Finsupp.single reverseRanking (1 / 2)
noncomputable def mixtureChoice (A : Finset (Fin 4)) (x : Fin 4) : ℝ :=
  (1 / 2) * rankingChoice forwardRanking A x +
  (1 / 2) * rankingChoice reverseRanking A x
end Falmagne.Examples


