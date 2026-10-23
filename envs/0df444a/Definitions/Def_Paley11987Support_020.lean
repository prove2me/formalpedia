-- Prove2me | Definitions.Def_Paley11987Support_020
-- name    : Paley11987Support_020
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T01:03:20.556951+00:00
-- url     : https://prove2.me/theorems/ece2cda9-9eff-45aa-83c5-5dc8fe575e9a
-- title:
--   Five conditional Boolean profile bounds
-- statement:
--   Defines $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$ and the A, B, M, P and D predicates bounding the relevant false-flip, true-flip and union sets under specified level-value conditions.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module BooleanTransferProfiles.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferProfiles, SHA256 bc14ac4bbbe4f5e0d8eb018044436f01405f35254722715745b6d3796d3bee91

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Paley11987Support_000
import Definitions.Def_Paley11987Support_001
import Definitions.Def_Paley11987Support_002
import Definitions.Def_Paley11987Support_003
import Definitions.Def_Paley11987Support_004
import Definitions.Def_Paley11987Support_005
import Definitions.Def_Paley11987Support_006
import Definitions.Def_Paley11987Support_007
import Definitions.Def_Paley11987Support_008
import Definitions.Def_Paley11987Support_009
import Definitions.Def_Paley11987Support_010
import Definitions.Def_Paley11987Support_011
import Definitions.Def_Paley11987Support_012
import Definitions.Def_Paley11987Support_013
import Definitions.Def_Paley11987Support_014
import Definitions.Def_Paley11987Support_015
import Definitions.Def_Paley11987Support_016
import Definitions.Def_Paley11987Support_017
import Definitions.Def_Paley11987Support_018
import Definitions.Def_Paley11987Support_019

set_option autoImplicit false
set_option Elab.async false
section z30

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity205 Sensitivity2075

namespace ZT

variable {I : Type} [Fintype I]

def flipsTo (f : (I → Bool) → Bool) (b : Bool) (x : I → Bool) : Finset I :=
  Finset.univ.filter fun a => f (flip x {a}) = b



def ABound {h : ℕ} (F : Fin h → (I → Bool) → Bool) (i j : Fin h) (v : ℕ) : Prop :=
  ∀ x, F i x = false → (flipsTo (F j) true x).card ≤ v

def BBound {h : ℕ} (F : Fin h → (I → Bool) → Bool) (i j : Fin h) (v : ℕ) : Prop :=
  ∀ x, F j x = true → (flipsTo (F i) false x).card ≤ v

def MBound {h : ℕ} (F : Fin h → (I → Bool) → Bool) (i j k : Fin h) (v : ℕ) : Prop :=
  ∀ x, F j x = true → F k x = false → (flipsTo (F i) false x).card ≤ v

def PBound {h : ℕ} (F : Fin h → (I → Bool) → Bool) (i j k : Fin h) (v : ℕ) : Prop :=
  ∀ x, F i x = true → F j x = false → (flipsTo (F k) true x).card ≤ v

def DBound {h : ℕ} (F : Fin h → (I → Bool) → Bool) (i j k l : Fin h) (v : ℕ) : Prop :=
  ∀ x, F j x = true → F k x = false →
    ((flipsTo (F i) false x) ∪ (flipsTo (F l) true x)).card ≤ v













end ZT
end
end z30


