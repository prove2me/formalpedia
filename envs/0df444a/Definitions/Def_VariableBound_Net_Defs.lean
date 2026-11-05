-- Prove2me | Definitions.Def_VariableBound_Net_Defs
-- name    : VariableBound_Net_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:01:11.792225+00:00
-- url     : https://prove2.me/theorems/8464cda2-436b-479b-9970-c1e160d02223
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Params
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_VariableBound_Search_Defs
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_r_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_contains
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.contains
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
namespace VariableBound.Net
open Groundwork Groundwork.Prog Groundwork.Prog.Count PaddedDescent.F ClauseBound.Alg
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
open ClauseBound.ParityChecks (Vof LD)
abbrev Dat := Fml × List (List ℕ)
def objs (D : Dat) : List (ℕ × ℕ × ℕ) :=
  ((List.range D.1.length).map fun e => (0, e, 0)) ++ (List.range D.2.length).flatMap fun j => (D.2.getD j []).map fun e => (1, e, j)
def obAt (D : Dat) (o : ℕ) : ℕ × ℕ × ℕ := (objs D).getD o (0, D.1.length, 0)
def clOf (D : Dat) (o : ℕ) : Cl := D.1.getD (obAt D o).2.1 []
def home (g j : ℕ) : ℕ := j % g
def tchB (g n : ℕ) (D : Dat) (a o : ℕ) : Bool :=
  ((clOf D o).any fun l => l.1 / qv g n == a) || ((obAt D o).1 == 1 && home g (obAt D o).2.2 == a)
def tch (g n : ℕ) (D : Dat) (a : ℕ) : List ℕ := (List.range (objs D).length).filter (tchB g n D a)
def linkB (g n : ℕ) (D : Dat) (o a b : ℕ) : Bool :=
  decide (a < b) && tchB g n D a o && tchB g n D b o &&
    (List.range g).all fun c => !(decide (a < c) && decide (c < b) && tchB g n D c o)
def ownB (g n : ℕ) (D : Dat) (o a : ℕ) : Bool :=
  tchB g n D a o && (List.range g).all fun c => !(decide (c < a) && tchB g n D c o)
def tst (g n : ℕ) (D : Dat) (a b κ : ℕ) : List ℕ :=
  (List.range (objs D).length).filter fun o => (obAt D o).1 == κ && linkB g n D o (min a b) (max a b)
def mark (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) (o : ℕ) : Bool := z.getD (qv g n + (tch g n D a).idxOf o) false
def str (g n : ℕ) (D : Dat) (a b κ : ℕ) (z : List Bool) : List Bool := (tst g n D a b κ).map (mark g n D a z)
def rank : List Bool → ℕ
  | [] => 0
  | b :: x => (bif b then x.length.choose (x.count true + 1) else 0) + rank x
def cw (t μ : ℕ) : ℕ := Nat.clog 2 (t.choose μ)
def mu (g : ℕ) (D : Dat) (y a b κ : ℕ) : ℕ := digit (objs D).length y ((min a b * g + max a b) * 2 + κ)
def capD (g n : ℕ) (D : Dat) (y a b : ℕ) : ℕ := ((List.range 2).map fun κ => cw (tst g n D a b κ).length (mu g D y a b κ)).sum
def labD (g n : ℕ) (D : Dat) (y a b : ℕ) (z : List Bool) : List Bool :=
  (List.range 2).flatMap fun κ => toWord (cw (tst g n D a b κ).length (mu g D y a b κ)) (rank (str g n D a b κ z))
def qj (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) (j : ℕ) : ℕ :=
  ((tch g n D a).filter fun o => (obAt D o).1 == 1 && (obAt D o).2.2 == j && mark g n D a z o).length
def okD (g n : ℕ) (D : Dat) (y a : ℕ) (z : List Bool) : Bool :=
  ((List.range (qv g n)).all fun r => decide (a * qv g n + r < n) || !(z.getD r false)) &&
    ((tch g n D a).all fun o => !(mark g n D a z o) ||
      (clOf D o).all fun l => !(l.1 / qv g n == a) || (z.getD (l.1 % qv g n) false != l.2)) &&
    ((List.range 2).all fun κ =>
      ((tch g n D a).filter fun o => (obAt D o).1 == κ && ownB g n D o a && mark g n D a z o).length == mu g D y a a κ) &&
    ((List.range g).all fun b => b == a || (List.range 2).all fun κ => (str g n D a b κ z).count true == mu g D y a b κ)
def WD (g n : ℕ) (D : Dat) (y : ℕ) (fl : Bool) (a : ℕ) (z : List Bool) : ℤ :=
  if okD g n D y a z then
    (((List.range D.2.length).filter fun j => home g j == a).map fun j => ParityChecks.sig (qj g n D a z j)).prod *
      (bif fl then (-1) ^ ((tch g n D a).filter fun o => (obAt D o).1 == 0 && ownB g n D o a && mark g n D a z o).length else 1)
  else 0
abbrev DCtx := (U × U) × (Dat × (ℕ × Bool))
def netD : FNet DCtx where
  n c a := qv c.1.1.length c.1.2.length + (tch c.1.1.length c.1.2.length c.2.1 a).length
  cap c a b := capD c.1.1.length c.1.2.length c.2.1 c.2.2.1 a b
  W x := WD x.1.1.1.length x.1.1.2.length x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2.1 x.2.2
  f x := if labD x.1.1.1.length x.1.1.2.length x.1.2.1 x.1.2.2.1 x.2.1.1 x.2.1.2 x.2.2.1 == x.2.2.2 then 1 else 0
def netDN (g : ℕ) (c : DCtx) : Network (Fin g) (List Bool) (List Bool) where
  S a := words (netD.n c a.val)
  W a z := netD.W (c, (a.val, z))
  Θ a b := words (netD.cap c a.val b.val)
  f a b z θ := netD.f (c, ((a.val, b.val), (z, θ)))
  c a b := netD.cap c a.val b.val
def rep (n : ℕ) : U := List.replicate n ()
def ctx (g n : ℕ) (D : Dat) (y : ℕ) (fl : Bool) : DCtx := ((rep g, rep n), (D, (y, fl)))
def tot (g : ℕ) (D : Dat) (y κ : ℕ) : ℕ := ((List.range g).map fun a => mu g D y a a κ).sum
def totP (g : ℕ) (D : Dat) (y κ : ℕ) : ℕ := ((List.range g).map fun b => ((List.range b).map fun a => mu g D y a b κ).sum).sum
def admD (k g n nb M : ℕ) (D : Dat) (fl : Bool) (y : ℕ) : Bool :=
  (bif fl then decide (tot g D y 0 ≤ nb) else tot g D y 0 == nb + 1) && decide (tot g D y 1 ≤ M) &&
    (List.range 2).all fun κ =>
      decide (totP g D y κ ≤ (k - 1 + κ) * tot g D y κ) &&
      (List.range g).all fun a => (List.range g).all fun b =>
        if b < a then digit (objs D).length y ((a * g + b) * 2 + κ) == 0
        else b == a || decide (mu g D y a b κ ≤ (tst g n D a b κ).length)
def nPr (g : ℕ) (D : Dat) : ℕ := nProf g (objs D).length 2
def WfD (k n : ℕ) (D : Dat) : Prop := WfL k n [D.1] ∧ ∀ L ∈ D.2, L.Nodup ∧ ∀ e ∈ L, e < D.1.length
def vset (σ : ℕ → Bool) (D : Dat) : Finset ℕ := (Finset.range (objs D).length).filter fun o => vio σ (clOf D o) = true
def kP (D : Dat) (P : Finset ℕ) (κ : ℕ) : Finset ℕ := P.filter fun o => (obAt D o).1 = κ
def chP (D : Dat) (P : Finset ℕ) (j : ℕ) : Finset ℕ := P.filter fun o => (obAt D o).1 = 1 ∧ (obAt D o).2.2 = j
def oc (g n : ℕ) (D : Dat) (P : Finset ℕ) (a κ : ℕ) : ℕ := (P.filter fun o => (obAt D o).1 = κ ∧ ownB g n D o a = true).card
def pw (g n : ℕ) (D : Dat) (P : Finset ℕ) (a b κ : ℕ) : ℕ := (P.filter fun o => o ∈ tst g n D a b κ).card
def wt (D : Dat) (fl : Bool) (P : Finset ℕ) : ℤ :=
  (∏ j ∈ Finset.range D.2.length, ParityChecks.sig (chP D P j).card) * (bif fl then (-1) ^ (kP D P 0).card else 1)
def Match (g n : ℕ) (D : Dat) (y : ℕ) (P : Finset ℕ) : Prop :=
  ∀ κ < 2, ∀ a < g, oc g n D P a κ = mu g D y a a κ ∧ ∀ b < g, b ≠ a → pw g n D P a b κ = mu g D y a b κ
def Lim (nb M : ℕ) (D : Dat) (fl : Bool) (P : Finset ℕ) : Prop :=
  (if fl = true then (kP D P 0).card ≤ nb else (kP D P 0).card = nb + 1) ∧ (kP D P 1).card ≤ M
def chks (D : Dat) : List (Finset (Fin D.1.length)) := chksD D.1.length D.2
def rhsXF {X E : Type} [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) (M : ℕ) (fl : Bool) : ℤ :=
  bif fl then ∑ ξ, ∑ S₀ ∈ (V ξ).powerset with S₀.card ≤ nb, (-1) ^ S₀.card * ∑ S ∈ AppVariables.tup V L M ξ, ∏ j, ParityChecks.sig (S j).card
  else ∑ ξ, ∑ _S₀ ∈ (V ξ).powerset with _S₀.card = nb + 1, ∑ S ∈ AppVariables.tup V L M ξ, ∏ j, ParityChecks.sig (S j).card
def rhsD (n nb M : ℕ) (D : Dat) (fl : Bool) : ℤ := rhsXF (Vof (n := n) D.1) nb (chks D) M fl
def colD (D : Dat) (e : ℕ) : ℕ := (D.2.filter fun L => L.contains e).length
def StChks : Prop := ∀ (k n : ℕ) (D : Dat), WfD k n D →
  (chks D).length = D.2.length ∧ (∀ j, ((chks D).getD j ∅).card = (D.2.getD j []).length) ∧ ∀ e : Fin D.1.length, AppVariables.load (chks D) e = colD D e.val
structure StLab : Prop where
  len : ∀ (g n : ℕ) (D : Dat) (y a b : ℕ) (z : List Bool), (labD g n D y a b z).length = capD g n D y a b
  inj : ∀ (g n : ℕ) (D : Dat) (y a b : ℕ) (z z' : List Bool),
    (∀ κ < 2, (str g n D a b κ z).count true = mu g D y a b κ) → (∀ κ < 2, (str g n D b a κ z').count true = mu g D y a b κ) →
    (labD g n D y a b z = labD g n D y b a z' ↔ ∀ κ < 2, str g n D a b κ z = str g n D b a κ z')
def StPresents : Prop := ∀ c : DCtx, netD.toP.Presents c (netDN c.1.1.length c) 0 0
def StVal : Prop := ∀ (k g n : ℕ) (D : Dat) (y : ℕ) (fl : Bool), 0 < g → WfD k n D →
  (netDN g (ctx g n D y fl)).value =
    ∑ σ : Fin n → Bool, ∑ P ∈ (vset (Mark.ext σ) D).powerset, by classical exact if Match g n D y P then wt D fl P else 0
def StProf : Prop := ∀ (k g n nb M : ℕ) (D : Dat) (fl : Bool) (P : Finset ℕ), 0 < g → WfD k n D → P ⊆ Finset.range (objs D).length →
  (∑ y ∈ Finset.range (nPr g D), by classical exact if admD k g n nb M D fl y = true ∧ Match g n D y P then (1 : ℤ) else 0) =
    (by classical exact if Lim nb M D fl P then 1 else 0 : ℤ)
def StNPr : Prop := ∀ (g : ℕ) (D : Dat) (s : ℕ), (∀ L ∈ D.2, L.length ≤ s) →
  (objs D).length ≤ D.2.length * s + D.1.length ∧ nPr g D ≤ ((objs D).length + 1) ^ (2 * (g ^ 2 + g))
def StTuples : Prop := ∀ (k n nb M : ℕ) (D : Dat) (fl : Bool), WfD k n D →
  (∑ σ : Fin n → Bool, ∑ P ∈ (vset (Mark.ext σ) D).powerset, by classical exact if Lim nb M D fl P then wt D fl P else 0) = rhsD n nb M D fl
def StTotal : Prop := ∀ (k g n nb M : ℕ) (D : Dat) (fl : Bool), 0 < g → WfD k n D →
  ∑ y ∈ Finset.range (nPr g D), (if admD k g n nb M D fl y = true then (netDN g (ctx g n D y fl)).value else 0) = rhsD n nb M D fl
structure Setting (k n Δ nb M : ℕ) (D : Dat) : Prop where
  wf : WfD k n D
  two : 2 ≤ Δ
  occ_le : ∀ v, (occ D.1 v).length ≤ Δ
  m_le : D.1.length ≤ Δ * n
  isNb : AppVariables.IsNb n Δ nb
  lt_m : nb < D.1.length
  r_le : D.2.length ≤ M
  one_le : 1 ≤ M
  row : ∀ L ∈ D.2, nb * L.length ≤ 16 * D.1.length
def StU : Prop := ∀ (k g n Δ nb M : ℕ) (D : Dat) (fl : Bool) (y : ℕ), 0 < g → Setting k n Δ nb M D → admD k g n nb M D fl y = true →
  ((netDN g (ctx g n D y fl)).U : ℝ) ≤
    6 * (k - 1 : ℕ) * (n + lg (2 * Δ)) + 2 * k * M * lg (96 * Δ * lg (2 * Δ)) + 2 * g ^ 2
def StUPrinted : Prop := ∀ (k g n Δ nb M : ℕ) (D : Dat) (fl : Bool) (y : ℕ), 0 < g → Setting k n Δ nb M D → M ≤ 14 * n → admD k g n nb M D fl y = true →
  ((netDN g (ctx g n D y fl)).U : ℝ) ≤ 6 * k * (n + lg (2 * Δ)) + 28 * k * n * lg (96 * Δ * lg (2 * Δ)) + 2 * g ^ 2
def UbD (k K n Δ : ℕ) : ℕ := 6 * k * (n + LD Δ) + 28 * k * n * Nat.clog 2 (96 * Δ * LD Δ) + 2 * (3 * K ^ 8) ^ 2
def P0 (g n Δ tb rb : ℕ) (sb : ℚ) : ℚ := (qv g n : ℚ) * (1 + Δ * (tb + 3)) + (qv g rb : ℚ) * sb
def PD (g n Δ tb rb : ℕ) (sb : ℚ) : ℕ := ⌈2 * P0 g n Δ tb rb sb⌉₊
def BD (k M : ℕ) : ℕ := (k + 1) * M + 1
def StSized : Prop := ∀ (k g n Δ nb M tb rb : ℕ) (sb : ℚ) (D : Dat) (fl : Bool) (y : ℕ), 0 < g → 0 ≤ sb → WfD k n D → (∀ v, (occ D.1 v).length ≤ Δ) →
  D.2.length ≤ rb → (∀ L ∈ D.2, (L.length : ℚ) ≤ sb) → (∀ e < D.1.length, colD D e ≤ tb + 2) → admD k g n nb M D fl y = true →
  (netDN g (ctx g n D y fl)).Sized (PD g n Δ tb rb sb) (BD k M)
def StP : Prop := ∀ (g n Δ tb rb : ℕ) (sb : ℚ), 0 < g → 0 ≤ sb → rb ≤ 10 * n →
  ((g * PD g n Δ tb rb sb : ℕ) : ℚ) ≤ 2 * (n + g) * (1 + Δ * (tb + 3)) + 2 * (10 * n + g) * sb + g
def tbMax (n Δ : ℕ) : ℕ := Nat.clog 2 (Δ * n) + 33 * LD Δ + 1
def sbMax (Δ : ℕ) : ℕ := 32 * Δ * LD Δ
def PbD (K n Δ : ℕ) : ℕ := PD (3 * K ^ 8) n Δ (tbMax n Δ) (10 * n) (sbMax Δ)
def BbD (k n : ℕ) : ℕ := BD k (14 * n)
structure Fit (k n Δ nb M : ℕ) (D : Dat) : Prop where
  wf : WfD k n D
  two : 2 ≤ Δ
  occ_le : ∀ v, (occ D.1 v).length ≤ Δ
  m_le : D.1.length ≤ Δ * n
  isNb : AppVariables.IsNb n Δ nb
  M_le : M ≤ 14 * n
  r_le : D.2.length ≤ 10 * n
  col : ∀ e < D.1.length, colD D e ≤ tbMax n Δ + 2
  big : nb < D.1.length → D.2.length ≤ M ∧ 1 ≤ M ∧ ∀ L ∈ D.2, nb * L.length ≤ 16 * D.1.length
  small : D.1.length ≤ nb → D.2 = []
def StTbMax : Prop := ∀ n Δ m tb : ℕ, 1 ≤ m → m ≤ Δ * n → (tb : ℝ) ≤ lg m + 33 * lg (2 * Δ) + 1 → tb ≤ tbMax n Δ
def StFit : Prop := ∀ (k n Δ nb rb tb M : ℕ) (ψ : Fml) (L : List (List ℕ)), WfL k n [ψ] → 2 ≤ Δ → (∀ v, (occ ψ v).length ≤ Δ) → ψ.length ≤ Δ * n → AppVariables.IsNb n Δ nb → M ≤ 14 * n →
  (nb < ψ.length → StructD ψ.length nb rb tb L → rb ≤ 10 * n → rb ≤ M → 1 ≤ M → tb ≤ tbMax n Δ → Fit k n Δ nb M (ψ, L)) ∧ (ψ.length ≤ nb → Fit k n Δ nb M (ψ, []))
def StSize : Prop := ∀ (k K n Δ nb M : ℕ) (D : Dat) (fl : Bool) (y : ℕ), 0 < K → Fit k n Δ nb M D → admD k (3 * K ^ 8) n nb M D fl y = true →
  (netDN (3 * K ^ 8) (ctx (3 * K ^ 8) n D y fl)).Sized (PbD K n Δ) (BbD k n) ∧ (netDN (3 * K ^ 8) (ctx (3 * K ^ 8) n D y fl)).U ≤ UbD k K n Δ
def objMax (n Δ : ℕ) : ℕ := 10 * n * sbMax Δ + Δ * n
def nPrMax (K n Δ : ℕ) : ℕ := nProf (3 * K ^ 8) (objMax n Δ) 2
def StNPrMax : Prop := ∀ (k K n Δ nb M : ℕ) (D : Dat), Fit k n Δ nb M D → nPr (3 * K ^ 8) D ≤ nPrMax K n Δ
def StBounds : Prop := ∀ (k K n Δ : ℕ), 1 ≤ n → 2 ≤ Δ →
  UbD k K n Δ ≤ 140 * k * n * LD Δ + 2 * (3 * K ^ 8) ^ 2 ∧
  3 * K ^ 8 * PbD K n Δ ≤ 2 * (n + 3 * K ^ 8) * (1 + Δ * (tbMax n Δ + 3)) + 2 * (10 * n + 3 * K ^ 8) * sbMax Δ + 3 * K ^ 8
def StSmall : Prop := ∀ (k g n Δ nb M : ℕ) (ψ : Fml) (fl : Bool) (y : ℕ), 0 < g → WfD k n (ψ, []) → (∀ v, (occ ψ v).length ≤ Δ) → ψ.length ≤ nb →
  admD k g n nb M (ψ, []) fl y = true →
  (netDN g (ctx g n (ψ, []) y fl)).Sized (2 * (qv g n * (1 + Δ))) 1 ∧ (netDN g (ctx g n (ψ, []) y fl)).U ≤ 2 * (k - 1) * nb
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
def evD (k : ℕ) (pad : U) (i : Idx) (n Δ nb M : ℕ) (fl : Bool) (D : Dat) : ℤ :=
  sumF (nPr (3 * S.K i ^ 8) D) pad fun y =>
    bif admD k (3 * S.K i ^ 8) n nb M D fl y then valS S pad i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) netD (ctx (3 * S.K i ^ 8) n D y fl) else 0
def evX (k : ℕ) (pad : U) (i : Idx) (n Δ nb M β : ℕ) (D : Dat) : ℤ := evD S k pad i n Δ nb M false D % 2 ^ β
def evF (k : ℕ) (pad : U) (i : Idx) (n Δ nb M : ℕ) (D : Dat) : ℤ := evD S k pad i n Δ nb M true D % 2 ^ (n + 1)
end
def StEvD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (k : ℕ) (pad : U) (i : Idx) (n Δ nb M : ℕ) (fl : Bool) (D : Dat),
  ok i → 2 ≤ S.K i → Fit k n Δ nb M D → nPr (3 * S.K i ^ 8) D ≤ pad.length → 2 ^ needNet S i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) (BbD k n) ≤ pad.length →
  evD S k pad i n Δ nb M fl D = rhsD n nb M D fl
def StEvXF : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (k : ℕ) (pad : U) (i : Idx) (n Δ nb M : ℕ) (D : Dat),
  ok i → 2 ≤ S.K i → Fit k n Δ nb M D → nPr (3 * S.K i ^ 8) D ≤ pad.length → 2 ^ needNet S i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) (BbD k n) ≤ pad.length →
  AppVariables.beta n D.1.length nb - 1 + D.2.length ≤ M → n + D.2.length ≤ M →
  evX S k pad i n Δ nb M (AppVariables.beta n D.1.length nb) D = AppVariables.Xsum (Vof (n := n) D.1) nb (chks D) ∧
    (AppVariables.Xsum (Vof (n := n) D.1) nb (chks D) = 0 → evF S k pad i n Δ nb M D = AppVariables.Fsum (Vof (n := n) D.1) nb (chks D))
structure StCertRank : Prop where
  choose : ∀ (α : Type) [Enc α] (t μ : α → ℕ), Unary t → Unary μ → PolyT fun x => (t x).choose (μ x)
  rank : PolyT rank
  cw : ∀ (α : Type) [Enc α] (t μ : α → ℕ), Unary t → PolyT μ → Unary fun x => cw (t x) (μ x)
def StCertNet : Prop := FKeeps netD
def StCertAdm : Prop := ∀ (α : Type) [Enc α] (k g n nb M y : α → ℕ) (D : α → Dat) (fl : α → Bool),
  PolyT k → Unary g → PolyT n → PolyT nb → PolyT M → PolyT D → PolyT fl → PolyT y → PolyT fun x => admD (k x) (g x) (n x) (nb x) (M x) (D x) (fl x) (y x)
def StCertEvD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (α : Type) [Enc α] (k n Δ nb M : α → ℕ) (pad : α → U) (i : α → Idx) (fl : α → Bool) (D : α → Dat),
  Unary k → Unary n → Unary Δ → PolyT nb → PolyT M → PolyT pad → PolyT i → PolyT fl → PolyT D →
  PolyT fun x => evD S (k x) (pad x) (i x) (n x) (Δ x) (nb x) (M x) (fl x) (D x)
end VariableBound.Net


