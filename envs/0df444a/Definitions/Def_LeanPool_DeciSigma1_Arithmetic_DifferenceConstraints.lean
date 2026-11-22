-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
-- name    : LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:33:32.697409+00:00
-- url     : https://prove2.me/theorems/3db97168-f8f2-48b1-be50-725efdd28c38
-- title:
--   Difference Constraints
-- statement:
--   Definitions and structural lemmas for Difference Constraints, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/DifferenceConstraints.lean

module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Arithmetic
structure DifferenceSystem (ι : Type) where
  /-- The weight of the constraint from `i` to `j`, if any. -/
  edgeWeight : ι → ι → Option ℤ
namespace DifferenceSystem
variable {ι : Type} (D : DifferenceSystem ι)
def Sat (x : ι → ℤ) : Prop := ∀ i j c, D.edgeWeight i j = some c → x i + c ≤ x j
def IsWalk (p : List ι) : Prop := p.IsChain (fun u v => (D.edgeWeight u v).isSome)
instance (p : List ι) : Decidable (D.IsWalk p) :=
  inferInstanceAs (Decidable (p.IsChain _))
def weight : List ι → ℤ
  | i :: j :: p => (D.edgeWeight i j).getD 0 + weight (j :: p)
  | _ => 0
def HasPositiveCycle :
    Prop := ∃ (i : ι) (p : List ι), D.IsWalk (i :: p ++ [i]) ∧ 0 < D.weight (i :: p ++ [i])
variable {D}
def maxNonnegativeWeight [Fintype ι] (D : DifferenceSystem ι) : ℕ :=
  Finset.univ.sup (fun ij : ι × ι => ((D.edgeWeight ij.1 ij.2).getD 0).toNat)
def IsTight (D : DifferenceSystem ι) (x : ι → ℤ) (u v : ι) :
    Prop := ∃ c, D.edgeWeight u v = some c ∧ x u + c = x v
def ofFinset [DecidableEq ι] (E : Finset (ι × ι × ℤ)) : DifferenceSystem ι :=
  ⟨fun i j => ((E.filter (fun e => e.1 = i ∧ e.2.1 = j)).image (fun e => e.2.2)).max⟩
end DifferenceSystem
end DeciSigma1.Arithmetic


