-- Prove2me | Definitions.Def_PaddedDescent_F_MarkNet
-- name    : PaddedDescent_F_MarkNet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:03:49.344799+00:00
-- url     : https://prove2.me/theorems/290a739e-c684-449d-9550-689284741581
-- title:
--   Mark Net
-- statement:
--   Definitions and structural lemmas for Mark Net, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkNet.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkMath
import Definitions.Def_PaddedDescent_F_Data
import Definitions.Def_StepMachines_Prog_GridDefs
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace PaddedDescent.F.Mark
open Groundwork Groundwork.Prog Groundwork.Prog.Count
def qv (g n : ℕ) : ℕ := (n + g - 1) / g
def cls (Ls : List Fml) : List (ℕ × Cl) := (List.range Ls.length).flatMap fun i => (Ls.getD i []).map fun C => (i, C)
def clAt (Ls : List Fml) (e : ℕ) : ℕ × Cl := (cls Ls).getD e (0, [])
def tchB (g n : ℕ) (Ls : List Fml) (a e : ℕ) : Bool := (clAt Ls e).2.any fun l => l.1 / qv g n == a
def tch (g n : ℕ) (Ls : List Fml) (a : ℕ) : List ℕ := (List.range (cls Ls).length).filter (tchB g n Ls a)
def linkB (g n : ℕ) (Ls : List Fml) (e a b : ℕ) : Bool :=
  decide (a < b) && tchB g n Ls a e && tchB g n Ls b e &&
    (List.range g).all fun c => !(decide (a < c) && decide (c < b) && tchB g n Ls c e)
def ownB (g n : ℕ) (Ls : List Fml) (e a : ℕ) : Bool :=
  tchB g n Ls a e && (List.range g).all fun c => !(decide (c < a) && tchB g n Ls c e)
def tst (g n : ℕ) (Ls : List Fml) (a b i : ℕ) : List ℕ :=
  (List.range (cls Ls).length).filter fun e => (clAt Ls e).1 == i && linkB g n Ls e (min a b) (max a b)
def mark (g n : ℕ) (Ls : List Fml) (a : ℕ) (z : List Bool) (e : ℕ) : Bool := z.getD (qv g n + (tch g n Ls a).idxOf e) false
def str (g n : ℕ) (Ls : List Fml) (a b i : ℕ) (z : List Bool) : List Bool := (tst g n Ls a b i).map (mark g n Ls a z)
def enc (β b : ℕ) (x : List Bool) : List Bool :=
  (List.range ((x.length + b - 1) / b)).flatMap fun o =>
    ((List.range b).filter fun p => x.getD (o * b + p) false).map (fun _ => true) ++
      false :: ((List.range b).filter fun p => x.getD (o * b + p) false).flatMap (toWord β)
def mu (g : ℕ) (Ls : List Fml) (y a b i : ℕ) : ℕ := digit (cls Ls).length y ((min a b * g + max a b) * Ls.length + i)
def mcap (g n β b : ℕ) (Ls : List Fml) (y a a' : ℕ) : ℕ :=
  ((List.range Ls.length).map fun i => mu g Ls y a a' i * (1 + β) + ((tst g n Ls a a' i).length + b - 1) / b).sum
def mlab (g n β b : ℕ) (Ls : List Fml) (a a' : ℕ) (z : List Bool) : List Bool :=
  (List.range Ls.length).flatMap fun i => enc β b (str g n Ls a a' i z)
def mW (g n : ℕ) (Ls : List Fml) (y a : ℕ) (z : List Bool) : ℤ :=
  if ((List.range (qv g n)).all fun r => decide (a * qv g n + r < n) || !(z.getD r false)) &&
      ((tch g n Ls a).all fun e => !(mark g n Ls a z e) ||
        (clAt Ls e).2.all fun l => !(l.1 / qv g n == a) || (z.getD (l.1 % qv g n) false != l.2)) &&
      ((List.range Ls.length).all fun i =>
        ((tch g n Ls a).filter fun e => (clAt Ls e).1 == i && ownB g n Ls e a && mark g n Ls a z e).length == mu g Ls y a a i) &&
      ((List.range g).all fun a' => a' == a || (List.range Ls.length).all fun i => (str g n Ls a a' i z).count true == mu g Ls y a a' i)
  then (-1) ^ ((tch g n Ls a).filter fun e => decide (1 ≤ (clAt Ls e).1) && ownB g n Ls e a && mark g n Ls a z e).length
  else 0
abbrev MCtx := (U × U × U × U) × (List Fml × ℕ)
def markF : FNet MCtx where
  n c a := qv c.1.1.length c.1.2.1.length + (tch c.1.1.length c.1.2.1.length c.2.1 a).length
  cap c a a' := mcap c.1.1.length c.1.2.1.length c.1.2.2.1.length c.1.2.2.2.length c.2.1 c.2.2 a a'
  W x := mW x.1.1.1.length x.1.1.2.1.length x.1.2.1 x.1.2.2 x.2.1 x.2.2
  f x := if mlab x.1.1.1.length x.1.1.2.1.length x.1.1.2.2.1.length x.1.1.2.2.2.length x.1.2.1 x.2.1.1 x.2.1.2 x.2.2.1 == x.2.2.2 then 1 else 0
def markN (g : ℕ) (c : MCtx) : Network (Fin g) (List Bool) (List Bool) where
  S a := words (markF.n c a.val)
  W a z := markF.W (c, (a.val, z))
  Θ a b := words (markF.cap c a.val b.val)
  f a b z θ := markF.f (c, ((a.val, b.val), (z, θ)))
  c a b := markF.cap c a.val b.val
def adm (k g n w : ℕ) (Ls : List Fml) (y : ℕ) : Bool :=
  (List.range Ls.length).all fun i =>
    decide (((List.range g).map fun a => mu g Ls y a a i).sum ≤ w) &&
    decide (((List.range g).map fun a => ((List.range a).map fun a' => mu g Ls y a' a i).sum).sum ≤ (k - 1) * w) &&
    (List.range g).all fun a => (List.range g).all fun a' =>
      if a' < a then digit (cls Ls).length y ((a * g + a') * Ls.length + i) == 0
      else a' == a || decide (mu g Ls y a a' i ≤ (tst g n Ls a a' i).length)
def WfL (k n : ℕ) (Ls : List Fml) : Prop := ∀ L ∈ Ls, ∀ C ∈ L, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n
def vset (σ : ℕ → Bool) (Ls : List Fml) : Finset ℕ := (Finset.range (cls Ls).length).filter fun e => vio σ (clAt Ls e).2 = true
def layP (Ls : List Fml) (P : Finset ℕ) (i : ℕ) : Finset ℕ := P.filter fun e => (clAt Ls e).1 = i
def oc (g n : ℕ) (Ls : List Fml) (P : Finset ℕ) (a i : ℕ) : ℕ := (P.filter fun e => (clAt Ls e).1 = i ∧ ownB g n Ls e a = true).card
def pw (g n : ℕ) (Ls : List Fml) (P : Finset ℕ) (a b i : ℕ) : ℕ := (P.filter fun e => e ∈ tst g n Ls a b i).card
def sgnP (Ls : List Fml) (P : Finset ℕ) : ℤ := (-1) ^ (P.filter fun e => 1 ≤ (clAt Ls e).1).card
def Match (g n : ℕ) (Ls : List Fml) (y : ℕ) (P : Finset ℕ) : Prop :=
  ∀ i < Ls.length, ∀ a < g, oc g n Ls P a i = mu g Ls y a a i ∧ ∀ b < g, b ≠ a → pw g n Ls P a b i = mu g Ls y a b i
def nProf (g M R₁ : ℕ) : ℕ := (M + 1) ^ (g * g * R₁)
end PaddedDescent.F.Mark


