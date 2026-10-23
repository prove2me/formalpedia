-- Prove2me | Definitions.Def_Paley11987Support_036
-- name    : Paley11987Support_036
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T01:50:08.342159+00:00
-- url     : https://prove2.me/theorems/052aa293-90cb-40a2-bdc9-aae1c29af2e8
-- title:
--   Scaled profiles and transition certificates
-- statement:
--   Defines the scaled five-profile bounds, their raw-step counterparts, and the finite transition-certificate structure. A certificate compares each raw coefficient with the corresponding coefficient of the next table.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module FiniteProfile11987Semantics.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module FiniteProfile11987Semantics, SHA256 b5c1264581343f592604905d2a70bd18dee9b0037d226df057697a01948097d9

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
import Definitions.Def_Paley11987Support_020
import Definitions.Def_Paley11987Support_021
import Definitions.Def_Paley11987Support_022
import Definitions.Def_Paley11987Support_023
import Definitions.Def_Paley11987Support_024
import Definitions.Def_Paley11987Support_025
import Definitions.Def_Paley11987Support_026
import Definitions.Def_Paley11987Support_027
import Definitions.Def_Paley11987Support_028
import Definitions.Def_Paley11987Support_029
import Definitions.Def_Paley11987Support_030
import Definitions.Def_Paley11987Support_031
import Definitions.Def_Paley11987Support_032
import Definitions.Def_Paley11987Support_033
import Definitions.Def_Paley11987Support_034
import Definitions.Def_Paley11987Support_035

namespace CompactConditionalProfiles
end CompactConditionalProfiles
namespace CompactFiniteProfile
end CompactFiniteProfile
namespace CompactFiniteProfileClosures
end CompactFiniteProfileClosures
namespace SensitivityOrdinaryGuard
end SensitivityOrdinaryGuard

set_option autoImplicit false
set_option Elab.async false
section z55

noncomputable section
open OAI.Paper320 ZT CompactFiniteProfileClosures

namespace ZP
variable {I : Type} [Fintype I]

structure ScaledBounds (F : Fin 20 → (I → Bool) → Bool) (v : Profile) (c : ℕ) : Prop where
  a : ∀ (i j : Fin 20), i ≤ j → ABound F i j (c*A v i j)
  b : ∀ (i j : Fin 20), i ≤ j → BBound F i j (c*B v i j)
  m : ∀ (i j : Fin 20), i ≤ j → ∀ hn : j.val+1 < 20,
    MBound F i j ⟨j.val+1,hn⟩ (c*M v i j)
  p : ∀ (j l : Fin 20), j < l → ∀ hn : j.val+1 < 20,
    PBound F j ⟨j.val+1,hn⟩ l (c*P v j l)
  d : ∀ (i j l : Fin 20), i ≤ j → j < l → ∀ hn : j.val+1 < 20,
    DBound F i j ⟨j.val+1,hn⟩ l (c*D v i j l)

structure RawStepBounds (G : Fin 20 → (I → Bool) → Bool)
    (v : Profile) (r : Recipe) (c : ℕ) : Prop where
  a : ∀ (i j : Fin 20), i ≤ j → ABound G i j (c*rawA v r i j)
  b : ∀ (i j : Fin 20), i ≤ j → BBound G i j (c*rawB v r i j)
  m : ∀ (i j : Fin 20), i ≤ j → ∀ hn : j.val+1 < 20,
    MBound G i j ⟨j.val+1,hn⟩ (c*rawM v r i j)
  p : ∀ (j l : Fin 20), j < l → ∀ hn : j.val+1 < 20,
    PBound G j ⟨j.val+1,hn⟩ l (c*rawP v r j l)
  d : ∀ (i j l : Fin 20), i ≤ j → j < l → ∀ hn : j.val+1 < 20,
    DBound G i j ⟨j.val+1,hn⟩ l (c*rawD v r i j l)

structure TransitionCertificate (v : Profile) (r : Recipe) (w : Profile) : Prop where
  a : ∀ (i j : Fin 20), i ≤ j → rawA v r i j ≤ A w i j
  b : ∀ (i j : Fin 20), i ≤ j → rawB v r i j ≤ B w i j
  m : ∀ (i j : Fin 20), i ≤ j → j.val+1 < 20 → rawM v r i j ≤ M w i j
  p : ∀ (j l : Fin 20), j < l → rawP v r j l ≤ P w j l
  d : ∀ (i j l : Fin 20), i ≤ j → j < l → rawD v r i j l ≤ D w i j l

 

 

 

end ZP
end
end z55


