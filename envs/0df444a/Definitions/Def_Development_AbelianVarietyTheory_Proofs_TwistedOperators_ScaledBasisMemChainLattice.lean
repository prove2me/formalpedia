-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:22.270194+00:00
-- url     : https://prove2.me/theorems/456513e2-2104-402d-ad3e-531d3a5225ec
-- title:
--   Scaled Basis Mem Chain Lattice
-- statement:
--   Definitions and structural lemmas for Scaled Basis Mem Chain Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
namespace GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def colMat (n' : Type) (y : Fin c → (n ⊕ Fin c → k)) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => Sum.elim (fun _ => 0) (fun j : Fin (c + 1) => Fin.cases 0 (fun i => y i r) j) s
open Classical in

def col (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (i : Fin c) : n ⊕ Fin c → k :=
  fun r => if h : Free (n' := n') 1 (r, Sum.inr i.succ) then e ⟨_, h⟩ else 0
def uncol (n' : Type) (y : Fin c → (n ⊕ Fin c → k)) :
    {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k := fun rs => colMat n' y rs.1.1 rs.1.2
section
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
theorem col_add (e e' : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) :
    col (e + e') = col e + col e' := by
  ext i r
  simp only [col, Pi.add_apply]
  split_ifs <;> simp
theorem col_smul (a : k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) :
    col (a • e) = a • col e := by
  ext i r
  simp only [col, Pi.smul_apply]
  split_ifs <;> simp
end
section
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
end
section
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [DecidableEq n']
end
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
open Classical in

def volFree (ν : Measure k) (n n' : Type) [Fintype n] [Fintype n'] (c : ℕ) :
    Measure ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) := Measure.pi fun _ => ν
omit [MeasurableSpace k] [BorelSpace k] in

def perLat (ϖ : 𝒪[k]) (n' : Type) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) :
    AddSubgroup ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) where
  carrier := {e | ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) • col e i ∈ chainLat ϖ c L}
  add_mem' he he' i := by
    rw [col_add, Pi.add_apply, smul_add]
    exact add_mem (he i) (he' i)
  zero_mem' i := by
    have : col (0 : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) i = 0 := by
      ext r
      simp [col]
    rw [this, smul_zero]
    exact zero_mem _
  neg_mem' {e} he i := by
    rw [← neg_one_smul k e, col_smul, neg_one_smul, Pi.neg_apply, smul_neg]
    exact neg_mem (he i)
end GlobalTheory.RootEx.UnfoldShape


