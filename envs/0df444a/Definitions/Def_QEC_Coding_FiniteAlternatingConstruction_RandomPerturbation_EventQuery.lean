-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:00:12.532998+00:00
-- url     : https://prove2.me/theorems/b155e49c-b4a3-468e-95e5-16096c6d65af
-- title:
--   Event Query
-- statement:
--   Definitions and structural lemmas for Event Query, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventQuery.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
def listAllQuery {A : Type*} (q : A → Bool × ℕ) : List A → Bool × ℕ
  | [] => (true,0)
  | a::L => let qa := q a; let rest := listAllQuery q L
            (qa.1 && rest.1,qa.2+rest.2+1)
def listAnyQuery {A : Type*} (q : A → Bool × ℕ) : List A → Bool × ℕ
  | [] => (false,0)
  | a::L => let qa := q a; let rest := listAnyQuery q L
            (qa.1 || rest.1,qa.2+rest.2+1)
noncomputable def eventQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius)
    (p : eventSupport P J radius e → Space) : Bool × ℕ :=
  listAnyQuery (fun g : Grid K =>
    listAllQuery (fun a : e.val =>
      triangleQuery (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i))+
        p (eventVertex P J radius e a i)) (eventCenter P J radius lambda K e g) 2)
      (Finset.univ.toList : List e.val))
    (Finset.univ.toList : List (Grid K))
end QEC.Coding.BDL26RandomPerturbation


