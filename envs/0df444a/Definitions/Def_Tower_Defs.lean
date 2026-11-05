-- Prove2me | Definitions.Def_Tower_Defs
-- name    : Tower_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:17:06.403227+00:00
-- url     : https://prove2.me/theorems/72f5c03b-9a09-45fb-92f5-fbf5f23e7f1c
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_CombRunsStatement
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace QueryMachines.Tower
open Groundwork
section selfCall
variable {Q A α β : Type} (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β)
def rstep : List M.σ → List M.σ
  | [] => []
  | s :: rest =>
    match M.out s with
    | some b =>
      match rest with
      | [] => [s]
      | s' :: rest' => M.resume s' (Sum.inr b) :: rest'
    | none =>
      match M.ask s with
      | some (Sum.inr a') => M.init a' :: s :: rest
      | some (Sum.inl _) => s :: rest
      | none => M.step s :: rest
def rask : List M.σ → Option Q
  | [] => none
  | s :: _ =>
    match M.out s, M.ask s with
    | none, some (Sum.inl x) => some x
    | _, _ => none
def rresume : List M.σ → A → List M.σ
  | [], _ => []
  | s :: rest, a => M.resume s (Sum.inl a) :: rest
def rout : List M.σ → Option β
  | [s] => M.out s
  | _ => none
def selfCall : QueryMachine Q A α β where
  σ := List M.σ
  init a := [M.init a]
  step := rstep M
  out := rout M
  ask := rask M
  resume := rresume M
end selfCall
open Classical in
/-- How the queries of M on the input a are to be answered: a query that is not a call by O; a call
of a', if a' is a good input of smaller depth than a, by `val a'`. Any other call has no answer. -/
noncomputable def callOracle {Q A α β : Type} (O : Q → Option A) (Good : α → Prop) (val : α → β) (dep : α → ℕ) (a : α) : Q ⊕ α → Option (A ⊕ β)
  | Sum.inl x => (O x).map Sum.inl
  | Sum.inr a' => if Good a' ∧ dep a' < dep a then some (Sum.inr (val a')) else none
def SelfCallPoly : Prop := ∀ (Q A α β : Type) [Enc Q] [Enc A] [Enc α] [Enc β] (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β), M.PolyTimeSteps → (selfCall M).PolyTimeSteps
def SelfCallRuns : Prop := ∀ (Q A α β : Type) (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β) (O : Q → Option A) (w : Q → ℕ) (Good : α → Prop) (val : α → β) (dep T : α → ℕ) (S : ℕ),
  (∀ a, Good a → M.Within (callOracle O Good val dep a) (Sum.elim w fun a' => T a' + 2) a (T a) S (val a)) →
  ∀ a, Good a → (selfCall M).Within O w a (T a) ((dep a + 1) * (S + 1) + 1) (val a)
section tower
variable {Ctx Q G A : Type} [HasSize Ctx]
abbrev NIn (Ctx Q : Type) : Type := (List Ctx × Ctx) ⊕ (Ctx × List Ctx × Q)
def upQuery (env : List Ctx) : Q ⊕ G → (Q ⊕ G) ⊕ NIn Ctx Q
  | Sum.inl q =>
    match env with
    | [] => Sum.inl (Sum.inl q)
    | c :: env' => Sum.inr (Sum.inr (c, env', q))
  | Sum.inr g => Sum.inl (Sum.inr g)
variable (Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A) (Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A)
def nest : QueryMachine ((Q ⊕ G) ⊕ NIn Ctx Q) (A ⊕ A) (NIn Ctx Q) A where
  σ := (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)
  init x :=
    match x with
    | Sum.inl (env, c) => Sum.inl (env, Sol.init c)
    | Sum.inr (c, env, q) => Sum.inr (env, Inn.init (c, q))
  step s :=
    match s with
    | Sum.inl (env, s) => Sum.inl (env, Sol.step s)
    | Sum.inr (env, i) => Sum.inr (env, Inn.step i)
  out s :=
    match s with
    | Sum.inl (_, s) => Sol.out s
    | Sum.inr (_, i) => Inn.out i
  ask s :=
    match s with
    | Sum.inl (env, s) =>
      match Sol.ask s with
      | some (Sum.inl c') => some (Sum.inr (Sum.inl (c' :: env, c')))
      | some (Sum.inr x) => some (upQuery env x)
      | none => none
    | Sum.inr (env, i) => (Inn.ask i).map (upQuery env)
  resume s r :=
    match s with
    | Sum.inl (env, s) => Sum.inl (env, Sol.resume s (r.elim id id))
    | Sum.inr (env, i) => Sum.inr (env, Inn.resume i (r.elim id id))
def tower : QueryMachine (Q ⊕ G) A Ctx A where
  σ := List (nest Sol Inn).σ
  init c := [(nest Sol Inn).init (Sum.inl ([], c))]
  step := rstep (nest Sol Inn)
  out := rout (nest Sol Inn)
  ask := rask (nest Sol Inn)
  resume := rresume (nest Sol Inn)
end tower
structure Spec (Ctx Q A : Type) where
  lev : Ctx → ℕ
  Good : Ctx → (Q → Option A) → Prop
  val : Ctx → (Q → Option A) → A
  Child : Ctx → (Q → Option A) → Ctx → Prop
  tab : Ctx → (Q → Option A) → Q → Option A
open Classical in
/-- How the queries of the solver on (c, f) are to be answered: a call of a permitted c' by the
value of c' with its tables; a query to the tables by f; a query of the second kind by gl. A call
that is not permitted has no answer. -/
noncomputable def Spec.oracle {Ctx Q G A : Type} (P : Spec Ctx Q A) (gl : G → Option A) (c : Ctx) (f : Q → Option A) : Ctx ⊕ (Q ⊕ G) → Option A
  | Sum.inl c' => if P.Child c f c' then some (P.val c' (P.tab c' f)) else none
  | Sum.inr (Sum.inl q) => f q
  | Sum.inr (Sum.inr g) => gl g
structure Spec.Meets {Ctx Q G A : Type} [HasSize Ctx] (P : Spec Ctx Q A) (gl : G → Option A) (wg : G → ℕ) (Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A) (Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A)
    (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (SS SI SC : ℕ) : Prop where
  /-- a call goes one level down -/
  child_lev : ∀ c f c', P.Good c f → P.Child c f c' → P.lev c' + 1 = P.lev c
  /-- to a well-formed instance -/
  child_good : ∀ c f c', P.Good c f → P.Child c f c' → P.Good c' (P.tab c' f)
  /-- with a small context -/
  child_size : ∀ c f c', P.Good c f → P.Child c f c' → size c' ≤ SC
  /-- the solver, with its calls and queries answered as specified, returns the value -/
  sol : ∀ c f, P.Good c f → ∀ tc tq : ℕ, Sol.Within (P.oracle gl c f) (Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) wg)) c (TS (P.lev c) tc tq) SS (P.val c f)
  /-- the procedure, with the caller's tables, returns the entries of the callee's tables -/
  inn : ∀ c f c', P.Good c f → P.Child c f c' → ∀ q a, P.tab c' f q = some a → ∀ tq : ℕ, Inn.Within (Sum.elim f gl) (Sum.elim (fun _ => tq) wg) (c', q) (TI (P.lev c') tq) SI a
def cost (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, t => TS 0 0 t
  | l + 1, t => TS (l + 1) (cost TS TI l (TI l t + 2) + 2) t
def towerSize (l SS SI SC : ℕ) : ℕ := (2 * l + 2) * (l * (SC + 1) + SS + SI + 3) + 1
def TowerPoly : Prop := ∀ (Ctx Q G A : Type) [HasSize Ctx] [Enc Ctx] [Carried Ctx] [Enc Q] [Enc G] [Enc A] (Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A) (Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A),
  Sol.PolyTimeSteps → Inn.PolyTimeSteps → (tower Sol Inn).PolyTimeSteps
def TowerRuns : Prop := ∀ (Ctx Q G A : Type) [HasSize Ctx] (P : Spec Ctx Q A) (gl : G → Option A) (wg : G → ℕ) (Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A) (Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A)
  (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (SS SI SC : ℕ), P.Meets gl wg Sol Inn TS TI SS SI SC →
  ∀ c f, P.Good c f → ∀ tq : ℕ, (tower Sol Inn).Within (Sum.elim f gl) (Sum.elim (fun _ => tq) wg) c (cost TS TI (P.lev c) tq) (towerSize (P.lev c) SS SI SC) (P.val c f)
def shapeS (own calls qs : ℕ → ℕ) (l tc tq : ℕ) : ℕ := own l + calls l * tc + qs l * tq
def shapeI (own' q' : ℕ → ℕ) (l tq : ℕ) : ℕ := own' l + q' l * tq
def CostShape : Prop := ∀ (own calls qs own' q' : ℕ → ℕ) (l t : ℕ),
  cost (shapeS own calls qs) (shapeI own' q') (l + 1) t =
    own (l + 1) + calls (l + 1) * (cost (shapeS own calls qs) (shapeI own' q') l (own' l + q' l * t + 2) + 2) + qs (l + 1) * t
def CostSlowDown : Prop := ∀ (own calls qs own' q' : ℕ → ℕ) (l x y : ℕ), 1 ≤ x →
  cost (shapeS own calls qs) (shapeI own' q') l (x * y) ≤ x * cost (shapeS own calls qs) (shapeI own' q') l y
end QueryMachines.Tower


