-- Prove2me | Definitions.Def_StepMachines_Prog_NetProg
-- name    : StepMachines_Prog_NetProg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:56:59.953276+00:00
-- url     : https://prove2.me/theorems/7dcf6c81-ef10-49e7-87be-afad6f566983
-- title:
--   Net Prog
-- statement:
--   Definitions and structural lemmas for Net Prog, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetProg.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_ColouringNet
set_option autoImplicit false
section
namespace Groundwork.Prog
open Finset Stepped
namespace NetE
variable {C : Type} (K g : ℕ) (Np : PNet C)
@[expose] public def col (x a : ℕ) : ℕ := x / K ^ a % K
@[expose] public def members (x G : ℕ) : List ℕ := (List.range g).filter fun a => col K x a == G
@[expose] public def stLens (c : C) (x G : ℕ) : List ℕ := (members K g x G).map (Np.n c)
@[expose] public def stLen (c : C) (x G : ℕ) : ℕ := (stLens K g Np c x G).sum
@[expose] public def zAt (c : C) (x G : ℕ) (z : List Bool) (a : ℕ) : List Bool :=
  (chunks (stLens K g Np c x G) z).getD ((members K g x G).idxOf a) []
@[expose] public def prs (x G G' : ℕ) : List (ℕ × ℕ) :=
  (members K g x G).flatMap fun a => (members K g x G').map fun b => (a, b)
@[expose] public def lbLens (c : C) (x G G' : ℕ) : List ℕ := (prs K g x G G').map fun p => Np.cap c p.1 p.2
@[expose] public def lbLen (c : C) (x G G' : ℕ) : ℕ := (lbLens K g Np c x G G').sum
@[expose] public def lAt (c : C) (x G G' : ℕ) (θ : List Bool) (p : ℕ × ℕ) : List Bool :=
  (chunks (lbLens K g Np c x G G') θ).getD ((prs K g x G G').idxOf p) []
@[expose] public def rowSum (c : C) (a : ℕ) : ℕ := (((List.range g).filter fun b => b != a).map (Np.cap c a)).sum
@[expose] public def Uc (c : C) : ℕ := ((List.range g).map (rowSum g Np c)).sum
@[expose] public def Pc (c : C) : ℕ := ((List.range g).map (rowSum g Np c)).foldr max 0
@[expose] public def betaC (c : C) : ℕ := Colouring.beta K g (Uc g Np c) (Pc g Np c)
@[expose] public def goodB (cx : C × ℕ) : Bool :=
  ((List.range K).all fun G => decide (K * (members K g cx.2 G).length < 2 * g)) &&
  (List.range K).all fun G => (List.range K).all fun G' =>
    G == G' || decide (lbLen K g Np cx.1 cx.2 G G' ≤ betaC K g Np cx.1)
public abbrev X0 (C : Type) : Type := (C × ℕ) × IQ
@[expose] public def validB (u : X0 C) : Bool :=
  (List.range K).all fun G' => G' == u.2.1 ||
    (((u.2.2.getD G' []).drop (lbLen K g Np u.1.1 u.1.2 (min u.2.1 G') (max u.2.1 G'))).all fun b => !b)
@[expose] public def nStates (u : X0 C) : ℕ := 2 ^ stLen K g Np u.1.1 u.1.2 u.2.1
@[expose] public def zOf (u : X0 C × ℕ) : List Bool := toWord (stLen K g Np u.1.1.1 u.1.1.2 u.1.2.1) u.2
@[expose] public def zA (u : X0 C × ℕ) (a : ℕ) : List Bool :=
  zAt K g Np u.1.1.1 u.1.1.2 u.1.2.1 (zOf K g Np u) a
@[expose] public def labOf (u : X0 C) (a b : ℕ) : List Bool :=
  if u.2.1 < col K u.1.2 b then lAt K g Np u.1.1 u.1.2 u.2.1 (col K u.1.2 b) (u.2.2.getD (col K u.1.2 b) []) (a, b)
  else lAt K g Np u.1.1 u.1.2 (col K u.1.2 b) u.2.1 (u.2.2.getD (col K u.1.2 b) []) (b, a)
@[expose] public def isOne (u : (X0 C × ℕ) × ℕ) : Bool :=
  col K u.1.1.1.2 (u.2 / g) != u.1.1.2.1 ||
    (col K u.1.1.1.2 (u.2 % g) == u.1.1.2.1 && decide (u.2 % g < u.2 / g))
@[expose] public def isW (u : (X0 C × ℕ) × ℕ) : Bool := u.2 / g == u.2 % g
@[expose] public def isPsi (u : (X0 C × ℕ) × ℕ) : Bool := col K u.1.1.1.2 (u.2 % g) == u.1.1.2.1
@[expose] public def qW (u : (X0 C × ℕ) × ℕ) : C × WQ := (u.1.1.1.1, (u.2 / g, zA K g Np u.1 (u.2 / g)))
@[expose] public def qF (u : (X0 C × ℕ) × ℕ) : C × FQ :=
  (u.1.1.1.1, ((u.2 / g, u.2 % g), (zA K g Np u.1 (u.2 / g), labOf K g Np u.1.1 (u.2 / g) (u.2 % g))))
@[expose] public def nLab (u : (X0 C × ℕ) × ℕ) : ℕ := 2 ^ Np.cap u.1.1.1.1 (u.2 / g) (u.2 % g)
@[expose] public def qP1 (u : ((X0 C × ℕ) × ℕ) × ℕ) : C × FQ :=
  (u.1.1.1.1.1, ((u.1.2 / g, u.1.2 % g),
    (zA K g Np u.1.1 (u.1.2 / g), toWord (Np.cap u.1.1.1.1.1 (u.1.2 / g) (u.1.2 % g)) u.2)))
@[expose] public def qP2 (u : ((X0 C × ℕ) × ℕ) × ℕ) : C × FQ :=
  (u.1.1.1.1.1, ((u.1.2 % g, u.1.2 / g),
    (zA K g Np u.1.1 (u.1.2 % g), toWord (Np.cap u.1.1.1.1.1 (u.1.2 / g) (u.1.2 % g)) u.2)))
@[expose] public def nPairs (_ : X0 C × ℕ) : ℕ := g * g
@[expose] public def nCol (_ : C) : ℕ := K ^ g
@[expose] public def zeroOf (_ : C) : ℤ := 0
variable [HasSize C]
@[expose] public def psiM : Stepped ((X0 C × ℕ) × ℕ) ℤ :=
  sumRange (nLab g Np) (mul2 (mapIn (qP1 K g Np) Np.f) (mapIn (qP2 K g Np) Np.f))
@[expose] public def termM : Stepped ((X0 C × ℕ) × ℕ) ℤ :=
  ite (isOne K g) (const 1) (ite (isW g) (mapIn (qW K g Np) Np.W)
    (ite (isPsi K g) (psiM K g Np) (mapIn (qF K g Np) Np.f)))
@[expose] public def mergedM : Stepped (X0 C) ℤ :=
  ite (validB K g Np) (sumRange (nStates K g Np) (prodRange (nPairs g) (termM K g Np))) (const 0)
omit [HasSize C]
@[expose] public def valW {g : ℕ} (N : Network (Fin g) (List Bool) (List Bool)) (a : ℕ) (z : List Bool) : ℤ :=
  if h : a < g then N.W ⟨a, h⟩ z else 0
@[expose] public def valF {g : ℕ} (N : Network (Fin g) (List Bool) (List Bool)) (a b : ℕ) (z θ : List Bool) : ℤ :=
  if h : a < g ∧ b < g then N.f ⟨a, h.1⟩ ⟨b, h.2⟩ z θ else 0
@[expose] public def termVal (N : Network (Fin g) (List Bool) (List Bool)) (u : (X0 C × ℕ) × ℕ) : ℤ :=
  if isOne K g u then 1
  else if isW g u then valW N (u.2 / g) (zA K g Np u.1 (u.2 / g))
  else if isPsi K g u then
    ∑ y ∈ range (nLab g Np u),
      valF N (u.2 / g) (u.2 % g) (zA K g Np u.1 (u.2 / g)) (toWord (Np.cap u.1.1.1.1 (u.2 / g) (u.2 % g)) y) *
      valF N (u.2 % g) (u.2 / g) (zA K g Np u.1 (u.2 % g)) (toWord (Np.cap u.1.1.1.1 (u.2 / g) (u.2 % g)) y)
  else valF N (u.2 / g) (u.2 % g) (zA K g Np u.1 (u.2 / g)) (labOf K g Np u.1.1 (u.2 / g) (u.2 % g))
@[expose] public def mergedVal (N : Network (Fin g) (List Bool) (List Bool)) (u : X0 C) : ℤ :=
  if validB K g Np u then ∑ y ∈ range (nStates K g Np u), ∏ i ∈ range (g * g), termVal K g Np N ((u, y), i) else 0
end NetE
end Groundwork.Prog


