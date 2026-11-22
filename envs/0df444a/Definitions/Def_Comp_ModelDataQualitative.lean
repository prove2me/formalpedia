-- Prove2me | Definitions.Def_Comp_ModelDataQualitative
-- name    : Comp_ModelDataQualitative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:36:59.669925+00:00
-- url     : https://prove2.me/theorems/d925677f-0ca7-4b6d-a634-75381b98d836
-- title:
--   Model Data Qualitative
-- statement:
--   Definitions and structural lemmas for Model Data Qualitative, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
namespace Comp
namespace ModelData
variable (d : ModelData)
def pre1Of (hs : d.Shape) (x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s => ∃ a1, ∀ a2, d.supportOf hs s a1 a2 ⊆ x
def gStepOf (hs : d.Shape) (safe x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  d.pre1Of hs x ∩ safe
def gRegion (hs : d.Shape) (safe : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.gStepOf hs safe) Finset.univ
def PadSat1 (hs : d.Shape) (s : Fin d.nStates) (v : Finset (Fin d.nAct1)) : Prop :=
  ∀ a1, a1 ∈ v ↔ d.padFin1 hs s a1 ∈ v
def PadSat2 (hs : d.Shape) (s : Fin d.nStates) (v : Finset (Fin d.nAct2)) : Prop :=
  ∀ a2, a2 ∈ v ↔ d.padFin2 hs s a2 ∈ v
def aTr (hs : d.Shape) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) : Finset (Fin d.nAct1) :=
  (d.enabled1 hs s).filter fun a1 =>
    ∀ a2 ∈ d.enabled2 hs s, a2 ∈ v2 ∨ d.supportOf hs s a1 a2 ⊆ y
def bTr (hs : d.Shape) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) : Finset (Fin d.nAct2) :=
  (d.enabled2 hs s).filter fun a2 => ∃ a1 ∈ v1, (d.supportOf hs s a1 a2 ∩ x).Nonempty
def lStepTr (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (w : Finset (Fin d.nAct1)) : Finset (Fin d.nAct1) :=
  d.aTr hs (d.bTr hs w x s) y s
def apre1Tr (hs : d.Shape) (x y : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s => d.bTr hs (d.aTr hs ∅ y s) x s = d.enabled2 hs s
def lpre1Tr (hs : d.Shape) (w : Fin d.nStates → Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s => d.bTr hs (w s) x s = d.enabled2 hs s
def aOf (hs : d.Shape) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) : Finset (Fin d.nAct1) :=
  Finset.univ.filter fun a1 => ∀ a2, a2 ∈ v2 ∨ d.supportOf hs s a1 a2 ⊆ y
def bOf (hs : d.Shape) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) : Finset (Fin d.nAct2) :=
  Finset.univ.filter fun a2 => ∃ a1 ∈ v1, (d.supportOf hs s a1 a2 ∩ x).Nonempty
def lStepOf (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (w : Finset (Fin d.nAct1)) : Finset (Fin d.nAct1) :=
  d.aOf hs (d.bOf hs w x s) y s
def apre1Of (hs : d.Shape) (x y : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s => d.bOf hs (d.aOf hs ∅ y s) x s = Finset.univ
def afStepOf (hs : d.Shape) (b y x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  d.apre1Of hs x y ∪ b
def afInnerOf (hs : d.Shape) (b y : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.afStepOf hs b y) ∅
def afRegion (hs : d.Shape) (b : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.afInnerOf hs b) Finset.univ
def lpre1Of (hs : d.Shape) (w : Fin d.nStates → Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  Finset.univ.filter fun s => d.bOf hs (w s) x s = Finset.univ
def midOf (hs : d.Shape) (k : ℕ) (b y x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  d.lpre1Of hs (fun s => (d.lStepOf hs x y s)^[k] ∅) x ∪ b
def lwOf (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    Finset (Fin d.nAct1) :=
  fixFrom (d.lStepOf hs x y s) ∅
def lmidOf (hs : d.Shape) (b y x : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  d.lpre1Of hs (d.lwOf hs x y) x ∪ b
def lfInnerOf (hs : d.Shape) (b y : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.lmidOf hs b y) ∅
def lfRegion (hs : d.Shape) (b : Finset (Fin d.nStates)) : Finset (Fin d.nStates) :=
  fixFrom (d.lfInnerOf hs b) Finset.univ
end ModelData
end Comp


