-- Prove2me | Definitions.Def_TunnellMap_KernelGenerator
-- name    : TunnellMap_KernelGenerator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:29:03.693726+00:00
-- url     : https://prove2.me/theorems/245bec2f-0bb6-5ebc-be1b-b662de572069
-- title:
--   Kernel Generator
-- statement:
--   Definitions and structural lemmas for Kernel Generator, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
namespace TunnellMap
open OrderedGenerator
def intIccL (lo hi : ℤ) : List ℤ :=
  if lo ≤ hi then (List.range ((hi - lo).toNat + 1)).map (fun k : ℕ => lo + (k : ℤ)) else []
def qValuesL (n A : ℤ) : List ℤ :=
  (intIccL (-n) n).filter fun q => decide (q ≠ 0 ∧ Odd q ∧ q ^ 2 * A < n)
def bLowerK (n : ℤ) {p : Triple} (F : OrthogonalFrame p) (A q : ℤ) : ℤ :=
  -((-(q * A * K F - isqrtK (alpha F * M n A q))) / n)
def bUpperK (n : ℤ) {p : Triple} (F : OrthogonalFrame p) (A q : ℤ) : ℤ :=
  (q * A * K F + isqrtK (alpha F * M n A q)) / n
def bValuesL (n : ℤ) {p : Triple} (F : OrthogonalFrame p) (A q : ℤ) : List ℤ :=
  intIccL (bLowerK n F A q) (bUpperK n F A q)
def rootValuesL {p : Triple} (F : OrthogonalFrame p) (A q b : ℤ) : List ℤ :=
  let D := F.halfDiscriminant A q b
  let c := beta F * b + q * A * delta F
  let s := isqrtK D
  (if s = 0 then [0] else [-s, s]).filter fun u => decide (u ^ 2 = D ∧ alpha F ∣ -c + u)
namespace BlockGen
variable {n : ℤ} {p : Triple}
def blockIndexListK (n : ℤ) (F : OrthogonalFrame p) (h : ℤ) : List GeneratorIndex :=
  (qValuesL n h).flatMap fun q =>
    (bValuesL n F h q).flatMap fun b =>
      (rootValuesL F h q b).map fun u => ⟨h, q, b, u⟩
variable {s : BResidual n}
def blockRecordsK (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (h : ℤ) : List IncidentRecord :=
  isortB recordLe ((blockIndexListK n F h).filterMap (emit s F))
def blocksFromK (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) : ℕ → ℤ → List IncidentRecord
  | 0, _ => []
  | fuel + 1, h =>
      if h ≤ hMax n then blockRecordsK s F h ++ blocksFromK s F fuel (h + 1) else []
def advanceKAux (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    ℕ → GenState → Option (IncidentRecord × GenState)
  | _, ⟨h, r :: rest⟩ => some (r, ⟨h, rest⟩)
  | 0, ⟨_, []⟩ => none
  | fuel + 1, ⟨h, []⟩ =>
      if h ≤ hMax n then advanceKAux s F fuel ⟨h + 1, blockRecordsK s F h⟩ else none
def advanceK (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (st : GenState) :
    Option (IncidentRecord × GenState) :=
  advanceKAux s F (hMax n + 1 - st.nextBlock).toNat st
end BlockGen
def lgReduceAuxK : ℕ → Triple → Triple → Triple × Triple
  | 0, u, v => (u, lgNext u v)
  | fuel + 1, u, v =>
      if dot (lgNext u v) (lgNext u v) < dot u u then
        lgReduceAuxK fuel (lgNext u v) (negTriple u)
      else (u, lgNext u v)
theorem lgReduceAuxK_eq :
    ∀ (fuel : ℕ) (u v : Triple), (dot u u).toNat ≤ fuel →
      lgReduceAuxK fuel u v = lgReduceAux u v := by
  intro fuel
  induction fuel with
  | zero =>
      intro u v hfuel
      have hnn := dot_self_nonneg u
      have hzero : dot u u = 0 := by omega
      have hlt : ¬ dot (lgNext u v) (lgNext u v) < dot u u := by
        have := dot_self_nonneg (lgNext u v); omega
      rw [lgReduceAuxK, lgReduceAux, dif_neg hlt]
  | succ fuel ih =>
      intro u v hfuel
      rw [lgReduceAuxK, lgReduceAux]
      by_cases h : dot (lgNext u v) (lgNext u v) < dot u u
      · rw [if_pos h, dif_pos h]
        refine ih _ _ ?_
        have := dot_self_nonneg (lgNext u v)
        omega
      · rw [if_neg h, dif_neg h]
def lgReduceK (u v : Triple) : Triple × Triple :=
  lgSelect (lgReduceAuxK (dot u u).toNat u v)
theorem lgReduceK_eq (u v : Triple) : lgReduceK u v = lgReduce u v := by
  rw [lgReduceK, lgReduce, lgReduceAuxK_eq _ u v le_rfl]
def reduceFrameK {p : Triple} (F : OrthogonalFrame p) : OrthogonalFrame p where
  e₁ := (lgReduceK F.e₁ F.e₂).1
  e₂ := (lgReduceK F.e₁ F.e₂).2
  z := F.z
  cross_eq := by rw [lgReduceK_eq, lgReduce_cross]; exact F.cross_eq
  bezout := F.bezout
end TunnellMap


