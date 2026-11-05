-- Prove2me | Definitions.Def_PaddedDescent_F_Prog
-- name    : PaddedDescent_F_Prog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:05:01.06366+00:00
-- url     : https://prove2.me/theorems/294ad1a9-7a21-4b3b-96e5-f217265ac5c6
-- title:
--   Prog
-- statement:
--   Definitions and structural lemmas for Prog, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Prog.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Data
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_SparsifyWidthK_Defs
import Definitions.Def_SparsifyWidthK_DefsProg
import Definitions.Def_PaddedDescent_F_MarkNet
import Theorems.Thm_Groundwork_BitCut_expand
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
namespace PaddedDescent.F
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count Groundwork.Grid
def termF {C : Type} (pad : U) (K g : ℕ) (F : FNet C) (u : (X0 C × ℕ) × ℕ) : ℤ :=
  bif isOne K g u then 1
  else bif isW g u then F.W (qW K g F.toP u)
  else bif isPsi K g u then sumF (nLab g F.toP u) pad fun y => F.f (qP1 K g F.toP (u, y)) * F.f (qP2 K g F.toP (u, y))
  else F.f (qF K g F.toP u)
def mergedF {C : Type} (pad : U) (K g : ℕ) (F : FNet C) (u : X0 C) : ℤ :=
  bif validB K g F.toP u then sumF (nStates K g F.toP u) pad fun y => prodL (g * g) fun i => termF pad K g F ((u, y), i)
  else 0
def rebalF {C : Type} (pad : U) (K g : ℕ) (F : FNet C) (c : C) : Option PInst :=
  ((rng pad (K ^ g)).find? fun x => goodB K g F.toP (c, x)).map fun x =>
    (List.replicate (betaC K g F.toP c) (), tabulate pad K (betaC K g F.toP c) fun q => mergedF pad K g F ((c, x), q))
def goodG {C : Type} (K g : ℕ) (Np : PNet C) (β : ℕ) (cx : C × ℕ) : Bool :=
  ((List.range K).all fun G => decide (K * (members K g cx.2 G).length < 2 * g)) &&
  (List.range K).all fun G => (List.range K).all fun G' => G == G' || decide (lbLen K g Np cx.1 cx.2 G G' ≤ β)
def rebalG {C : Type} (pad : U) (K g β : ℕ) (F : FNet C) (c : C) : Option PInst :=
  ((rng pad (K ^ g)).find? fun x => goodG K g F.toP β (c, x)).map fun x =>
    (List.replicate β (), tabulate pad K β fun q => mergedF pad K g F ((c, x), q))
def botF (pad : U) (tr : Bool) (i : ℕ) (x y w : List Bool) : ℤ :=
  sumF (2 ^ x.length) pad fun s =>
    if (toWord x.length s).count true = i then prodL x.length (fun k => botTerm tr x y w s k) else 0
def cutF (pad : U) (tr top : Bool) (i : ℕ) (x y w : List Bool) : ℤ :=
  if validW x.length (sideCnt tr x.length i) w = true then
    if top = true then prodL x.length (topTerm tr x y w) else botF pad tr i x y w
  else 0
def itemF (pad : U) (g : ℕ) (tr : Bool) (n y a b : ℕ) (z θ : List Bool) (i i' : ℕ) : ℤ :=
  cutF pad tr (decide (a < b)) (rectDig g tr n y (tri (min a b) (max a b)) (tri i i'))
    (he g n z i (node g tr b i')) (he g n z i' (node g tr b i)) (sideChunk g tr n y a b θ (tri i i'))
abbrev SideCtx := (U × U × Bool) × (U × ℕ × Tab)
def sideWF (g : ℕ) (tr : Bool) (ℓ y : ℕ) (T : Tab) (q : WQ) : ℤ :=
  bif sideChk g tr (fun n : ℕ => n) ((ℓ, y), q) then
    prodL g fun i => look T (node g tr q.1 i, (List.range (g * g)).map (sideLabels g tr ℓ q.1 q.2 i))
  else 0
def sideFF (pad : U) (g : ℕ) (tr : Bool) (ℓ y : ℕ) (q : FQ) : ℤ :=
  bif sideEdges g tr (fun n : ℕ => n) ((ℓ, y), q) then
    prodL (g * g) fun j => if j / g < j % g then itemF pad g tr ℓ y q.1.1 q.1.2 q.2.1 q.2.2 (j / g) (j % g) else 1
  else 0
def sideF : FNet SideCtx where
  n c _ := c.1.2.1.length ^ 3 * c.2.1.length
  cap c a b := sideCap c.1.2.1.length c.1.2.2 c.2.1.length c.2.2.1 a b
  W x := sideWF x.1.1.2.1.length x.1.1.2.2 x.1.2.1.length x.1.2.2.1 x.1.2.2.2 x.2
  f x := sideFF x.1.1.1 x.1.1.2.1.length x.1.1.2.2 x.1.2.1.length x.1.2.2.1 x.2
def sideCtx (pad : U) (gu : U) (I : PInst) (y : ℕ) : SideCtx :=
  ((pad, gu, decide (priceCol gu.length I.1.length y < priceRow gu.length I.1.length y)), (I.1, y, I.2))
def capM (g lam : ℕ) : ℕ := g * lam + 2 * g ^ 2 * lam
def Ubar (g lam : ℕ) : ℕ := g ^ 2 * (g - 1) * lam + (717 * g ^ 4 * lam) / 800 + g ^ 4 / 2 + 1
def lamNext (K g lam : ℕ) : ℕ := (Dcol * Ubar g lam + 3 * g ^ 2 * capM g lam) / (Dcol * K ^ 2) + 1
def childF (pad : U) (L : Lvl) (I : PInst) (y : ℕ) : Option PInst :=
  rebalG pad L.1.length L.2.length (lamNext L.1.length L.2.length I.1.length) sideF (sideCtx pad L.2 I y)
def expand (pad : U) (L : Lvl) (I : PInst) : List PInst :=
  (rng pad ((I.1.length + 1) ^ nRect L.2.length)).filterMap (childF pad L I)
def descend (pad : U) (sched : List Lvl) (I : PInst) : List PInst :=
  sched.foldl (fun w L => cap pad [] (w.flatMap (expand pad L))) (cap pad [] [I])
def bruteF (pad : U) (K : ℕ) (I : PInst) : ℤ :=
  sumF (2 ^ (K * (K - 1) / 2 * I.1.length)) pad fun y =>
    prodL K fun v => look I.2 (query0 K I.1.length [] (toWord (K * (K - 1) / 2 * I.1.length) y) v)
def gU (Ku : U) : U := List.replicate (3 * Ku.length ^ 8) ()
def mulU (Ku Lu : U) : U := List.replicate (Ku.length * Lu.length) ()
def sqU (gu : U) : U := List.replicate (gu.length * gu.length) ()
def schedF (pad : U) (t : ℕ) : List Lvl × U × U :=
  (List.replicate t ()).foldl
    (fun st _ => cap pad ([], [], []) ((st.2.1, mulU st.2.1 st.2.2) :: st.1, sqU (mulU st.2.1 st.2.2), st.2.2 ++ st.2.2))
    (cap pad ([], [], []) ([], List.replicate 256 (), List.replicate (Lseq 0) ()))
def valF {C : Type} (pad : U) (S : List Lvl × U) (F : FNet C) (c : C) : ℤ :=
  (rebalF pad S.2.length (gU S.2).length F c).elim 0 fun I => ((descend pad S.1 I).map (bruteF pad 256)).sum
def evalF (k : ℕ) (pad : U) (S : List Lvl × U) (p : U × U × U × U) (Ls : List Fml) : ℤ :=
  sumF (Mark.nProf (gU S.2).length (Mark.cls Ls).length Ls.length) pad fun y =>
    bif Mark.adm k (gU S.2).length p.1.length p.2.1.length Ls y then valF pad S Mark.markF ((gU S.2, p.1, p.2.2.1, p.2.2.2), (Ls, y)) else 0
def layersF (k : ℕ) (pad : U) (S : List Lvl × U) (p : U × U × U × U) (R : ℕ) (ψ : Fml) : List Fml :=
  ψ.foldl (fun Ls C => cap pad [] (Mark.placeE (evalF k pad S p) p.2.1.length Ls C)) (cap pad [] (List.replicate (R + 1) []))
def countM (k : ℕ) (pad : U) (S : List Lvl × U) (p : U × U × U × U) (R : ℕ) (ψ : Fml) : ℤ :=
  evalF k pad S p ([] :: layersF k pad S p R ψ)
def markPar (n s : ℕ) : U × U × U × U :=
  (List.replicate n (), List.replicate (capOf n) (), List.replicate (betaOf s) (), List.replicate (2 ^ betaOf s) ())
def walkF (k : ℕ) (pad : U) (τ : ℕ) (test : Sparsify.PFml → Bool) (r : Sparsify.PFml) : Bool :=
  (pad.foldl (fun st _ => cap pad ([], false) (Sparsify.roundB (WidthK.Prog.stepK (WidthK.theta τ) k) test st))
    (cap pad ([], false) ([r], false))).2
def A (p : List Bool × U) : Bool :=
  bif hasNil (decF p.1) then false
  else walkF 3 p.2 (tauOf (sOf (Decode.dec p.1).1))
    (fun ψ => decide (0 < countM 3 p.2
      ((schedF p.2 (depthOf (sOf (Decode.dec p.1).1))).1, (schedF p.2 (depthOf (sOf (Decode.dec p.1).1))).2.1)
      (markPar (Decode.dec p.1).1 (sOf (Decode.dec p.1).1)) (layersOf (sOf (Decode.dec p.1).1)) ψ))
    (Sparsify.rootP (decF p.1))
def Pn (g lam : ℕ) : ℕ := 2 * g ^ 3 * lam
def bNext (K g lam B : ℕ) : ℕ :=
  Pn g lam * (2 * g / K) + (g * B + g ^ 2 * lam) * (2 * g / K + 2 * g / K * (2 * g / K)) * K
def instLen (K lam B : ℕ) : ℕ := 4 * lam + K * (2 ^ ((K - 1) * lam) * (3 * B + 10) + 4) + 10
structure Bud (F K g lam : ℕ) : Prop where
  pat : (lam + 1) ^ nRect g ≤ F
  col : K ^ g ≤ F
  st : 2 ^ (Pn g lam * (2 * g / K)) ≤ F
  lab : 2 ^ Pn g lam ≤ F
  tab : 2 ^ ((K - 1) * lamNext K g lam) ≤ F
def Fits (F : ℕ) : ℕ → ℕ → ℕ → ℕ → List Lvl → Prop
  | Kup, Λ, B, cnt, [] => cnt * instLen Kup Λ B + 2 ≤ F ∧ 2 ^ (Kup * (Kup - 1) / 2 * Λ) ≤ F
  | Kup, Λ, B, cnt, L :: r =>
      cnt * instLen Kup Λ B + 2 ≤ F ∧ Bud F L.1.length L.2.length Λ ∧
        Fits F L.1.length (lamNext L.1.length L.2.length Λ) (bNext L.1.length L.2.length Λ B) (cnt * (Λ + 1) ^ nRect L.2.length) r
def ColOK (K g : ℕ) : Prop := ∃ m, 4 * Dcol ^ 2 * m * K ≤ g ∧ (g + 2) * K < 2 ^ m
def Chain : ℕ → List Lvl → Prop
  | Kup, [] => Kup = 256
  | Kup, L :: r => Kup = L.2.length * L.2.length ∧ 2 ≤ L.1.length ∧ ColOK L.1.length L.2.length ∧ Chain L.1.length r
def schedL : ℕ → List Lvl
  | 0 => []
  | j + 1 => (List.replicate (Kseq j) (), List.replicate (gseq j) ()) :: schedL j
def schedLen (t : ℕ) : ℕ := (t + 1) * (8 * Kseq t + 8) + 4 * Lseq t + 8
def lamG (K g Ub P : ℕ) : ℕ := (K ^ 3 + K * Ub + g * P) / K ^ 3
structure NetFits (F : ℕ) (S : List Lvl × U) (Ub P : ℕ) : Prop where
  chain : Chain S.2.length S.1
  two_le : 2 ≤ S.2.length
  col : S.2.length ^ (3 * S.2.length ^ 8) ≤ F
  st : 2 ^ (P * (2 * (3 * S.2.length ^ 8) / S.2.length)) ≤ F
  lab : 2 ^ P ≤ F
  tab : 2 ^ ((S.2.length - 1) * lamG S.2.length (3 * S.2.length ^ 8) Ub P) ≤ F
  fits : Fits F S.2.length (lamG S.2.length (3 * S.2.length ^ 8) Ub P) (P * (2 * (3 * S.2.length ^ 8) / S.2.length)) 1 S.1
def Ub (k g n w β R₁ : ℕ) : ℕ := 2 * R₁ * ((k - 1) * w * (1 + β) + (k - 1) * (n + 1) + g ^ 2)
def Pb (g n β Δ : ℕ) : ℕ := 2 * (2 + β) * Mark.qv g n * (Δ + 4)
def layLen (k n m R : ℕ) : ℕ := m * (k * (3 * n + 5) + 10) + 4 * (R + 1) + 2
structure MarkFits (k F : ℕ) (S : List Lvl × U) (n β b R Δ m : ℕ) : Prop where
  net : NetFits F S (Ub k (3 * S.2.length ^ 8) n (n + 2) β (R + 2)) (Pb (3 * S.2.length ^ 8) n β Δ)
  prof : Mark.nProf (3 * S.2.length ^ 8) m (R + 2) ≤ F
  lay : layLen k n m R ≤ F
  last : 2 ^ R * m + 5 * 3 ^ R ≤ 3 ^ R * (n + 2)
  b_pos : 0 < b
  b_le : b ≤ 2 ^ β
  m_le : m ≤ b * (n + 1)
def stackLen (k τ n m : ℕ) : ℕ := (WidthK.bsum τ k * n + 1) * (2 ^ k * m * (k * (3 * n + 5) + 10) + 4) + 8
def inLen (k n : ℕ) : ℕ := (k * 2 ^ k + 1) * (n + 2) ^ (k + 1)
end PaddedDescent.F


