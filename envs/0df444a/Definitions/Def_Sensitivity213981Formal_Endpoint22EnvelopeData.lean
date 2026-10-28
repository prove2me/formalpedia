-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22EnvelopeData
-- name    : Sensitivity213981Formal_Endpoint22EnvelopeData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:57:49.809617+00:00
-- url     : https://prove2.me/theorems/2ecdfe8f-8763-4b47-b86e-f4340a2b1bec
-- title:
--   Endpoint22 Envelope Data — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Envelope Data in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxNumeric.Endpoint22.mask1003`, `ThreeBoundMinmaxNumeric.Endpoint22.values1003`, `ThreeBoundMinmaxNumeric.Endpoint22.bound1003`, `ThreeBoundMinmaxNumeric.Endpoint22.deny1003`, `ThreeBoundMinmaxNumeric.Endpoint22.mask1004`, `ThreeBoundMinmaxNumeric.Endpoint22.values1004`, `ThreeBoundMinmaxNumeric.Endpoint22.mask1000`, `ThreeBoundMinmaxNumeric.Endpoint22.bound1004`, `ThreeBoundMinmaxNumeric.Endpoint22.deny1004`, `ThreeBoundMinmaxNumeric.Endpoint22.mask1100`, `ThreeBoundMinmaxNumeric.Endpoint22.values1100`, `ThreeBoundMinmaxNumeric.Endpoint22.values1000`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22EnvelopeData.lean, lines 1–114.

import Definitions.Def_Sensitivity213981Formal_Endpoint22DenyData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCoefficientDominance
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
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

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundEndpoint22Records ThreeBoundRankAnnotated
open ThreeBoundRankCached
def mask1000 : Array Bool := #[true,true,false,false,false,true,false,false,true,false,false]
def values1000 : CostValues := {
  heads := #[32053908449396,919308706993249,1777838346131595,32053908449396,919308706993249,1761605751986597,0,0,0,0,0,0,0,0,0,0,858529639138346,869541955373478,0,0,0,0,0,0,32053908449396,874556593363044,1717059278276692,0,0,0,0,0,0]
  guard := 903076112848251
  converted := 858529639138346
  negative := #[16232594144999,16232594144999] }
def bound1000 : ℕ := 5625701733004770
def deny1000 : ℕ := 1168516387072










def mask1003 : Array Bool := #[true,true,true,false,false,true,true,false,true,true,false]
def values1003 : CostValues := {
  heads := #[101998401308453508,2924817141562939732,5656227632448335995,101998401308453508,2924817141562939732,5604594321610500474,66503656323592,2873183830725104211,2908177251892161161,0,0,0,0,0,0,0,2731410490885396263,2766403912052453213,0,34993421167056950,69986842334113900,0,0,0,101998401308453508,2782409691539623017,5462820981770792526,71658609138597058,2731410490885396263,2766403912052453213,0,0,0]
  guard := 2873183830725104211
  converted := 2731410490885396263
  negative := #[51633310837835521,51633310837835521,66503656323592] }
def bound1003 : ℕ := 18533629053572807275
def deny1003 : ℕ := 1099780132864














def mask1004 : Array Bool := #[true,true,true,false,false,true,false,false,false,true,false]
def values1004 : CostValues := {
  heads := #[51633310837835521,2924817141562939732,5656227632448335995,101998401308453508,2924817141562939732,5604594321610500474,66503656323592,2873183830725104211,2908177251892161161,0,0,0,0,0,0,0,2731410490885396263,2766403912052453213,0,0,0,0,0,0,0,0,0,983400988644543,2731410490885396263,2766403912052453213,0,0,0]
  guard := 2873183830725104211
  converted := 2731410490885396263
  negative := #[51633310837835521,51633310837835521,66503656323592] }
def bound1004 : ℕ := 17898681025332959691
def deny1004 : ℕ := 1104091877376










def mask1100 : Array Bool := #[true,true,true,true,false,true,false,true,true,true,true]
def values1100 : CostValues := {
  heads := #[1712,96960,187521,1712,96960,187501,1700,96303,186250,1691,95252,96412,0,0,0,0,93326,186652,0,0,0,0,1191,2381,3382,92248,181122,3359,95004,182048,3381,89947,91120]
  guard := 95252
  converted := 93326
  negative := #[1712,1712,1700,3] }
def bound1100 : ℕ := 1000000
def deny1100 : ℕ := 16842752






































end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal


