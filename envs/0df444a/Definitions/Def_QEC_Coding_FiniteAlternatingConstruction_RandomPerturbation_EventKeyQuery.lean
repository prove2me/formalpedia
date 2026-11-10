-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:02:04.284008+00:00
-- url     : https://prove2.me/theorems/b94705da-ac62-45ce-93a0-d53b61f5cb3e
-- title:
--   Event Key Query
-- statement:
--   Definitions and structural lemmas for Event Key Query, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
noncomputable def triangleInputList (P : TannerSquarePresentation) : List (Triangle P) :=
  List.ofFn (Fintype.equivFin (Triangle P)).symm
def mapQuery {A B : Type*} (q : A → B × ℕ) : List A → List B × ℕ
  | [] => ([],0)
  | a::L => let qa := q a; let rest := mapQuery q L
            (qa.1::rest.1,qa.2+rest.2+1)
def lexLEQuery : List ℕ → List ℕ → Bool × ℕ
  | [], _ => (true,1)
  | _::_, [] => (false,1)
  | a::L, b::M => if a < b then (true,1) else if b < a then (false,2) else
      let q := lexLEQuery L M
      (q.1,q.2+2)
noncomputable def eventKeyQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : List ℕ × ℕ :=
  let raw := mapQuery (fun t => indexQuery t (triangleInputList P)) e.val.toList
  let sorted := sortQuery (fun a b : ℕ => (decide (a ≤ b),1)) raw.1
  (sorted.1,raw.2+sorted.2)
noncomputable def eventCompareQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e f : Event P J radius) : Bool × ℕ :=
  let E := eventKeyQuery P J radius e
  let F := eventKeyQuery P J radius f
  let q := lexLEQuery E.1 F.1
  (q.1,E.2+F.2+q.2)
end QEC.Coding.BDL26RandomPerturbation


