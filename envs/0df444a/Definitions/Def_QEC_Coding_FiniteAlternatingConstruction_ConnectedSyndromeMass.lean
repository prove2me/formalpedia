-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
-- name    : QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:25:00.409674+00:00
-- url     : https://prove2.me/theorems/1ae7ff6f-10b6-454b-b21c-683cf81a39e1
-- title:
--   Connected Syndrome Mass
-- statement:
--   Definitions and structural lemmas for Connected Syndrome Mass, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26ConnectedSyndromeMass
open Classical BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26BoundedValence
open BDL26LocalSyndromeWeights BDL26ReplacementSupport MultiscaleDecoder
open scoped BigOperators Classical
universe u
def OwnerCarrier (S : OddScale) : ℕ → Type
  | 0 => PEmpty.{1}
  | 1 => PEmpty.{1}
  | n+2 => if (n+2)%2=1 then RX2 (state S (n+1)).presentation S
      else RZZ (state S (n+1)).presentation S
noncomputable instance ownerCarrierFintype (S : OddScale) (i : ℕ) : Fintype (OwnerCarrier S i) := by
  cases i with
  | zero => exact inferInstanceAs (Fintype PEmpty.{1})
  | succ i => cases i with
    | zero => exact inferInstanceAs (Fintype PEmpty.{1})
    | succ n =>
      change Fintype (if (n+2)%2=1 then RX2 (state S (n+1)).presentation S
        else RZZ (state S (n+1)).presentation S)
      by_cases h : (n+2)%2=1
      · rw [if_pos h]
        infer_instance
      · rw [if_neg h]
        infer_instance
def owner (S : OddScale) : (i : ℕ) → OwnerCarrier S i → GraphVertex S i
  | 0, c => PEmpty.elim c
  | 1, c => PEmpty.elim c
  | n+2, c =>
      if h : (n+2)%2=1 then
        rxSyndromeOwner (state S (n+1)).presentation S
          (cast (show OwnerCarrier S (n+2)=RX2 (state S (n+1)).presentation S from
            if_pos h) c)
      else Vertex.z (rzSyndromeOwner (state S (n+1)).presentation S
        (cast (show OwnerCarrier S (n+2)=RZZ (state S (n+1)).presentation S from
          if_neg h) c))
abbrev OwnerFiber (S : OddScale) (i : ℕ) (u : GraphVertex S i) :=
  {c : OwnerCarrier S i // owner S i c=u}
def extend (S : OddScale) (i : ℕ) (u : GraphVertex S i)
    (x : Word Bit (OwnerFiber S i u)) : Word Bit (OwnerCarrier S i) :=
  fiberExtend (owner S i) u x
def localWords (S : OddScale) (i : ℕ) (u : GraphVertex S i) :
    Finset (Word Bit (OwnerFiber S i u)) := Finset.univ.filter (fun x => x≠0)
def factor (S : OddScale) (i : ℕ) (u : GraphVertex S i) (t : ℝ) : ℝ :=
  fiberFactor (owner S i) u (localWords S i u) t
theorem owner_rz_apply (S : OddScale) (n : ℕ) (h : (n+2)%2≠1)
    (c : OwnerCarrier S (n+2)) :
    owner S (n+2) c = Vertex.z (rzSyndromeOwner (state S (n+1)).presentation S
      (cast (show OwnerCarrier S (n+2)=RZZ (state S (n+1)).presentation S from
        if_neg h) c)) := by
  change @Eq (Vertex (state S (n+1)).presentation)
    (if h' : (n+2)%2=1 then
      rxSyndromeOwner (state S (n+1)).presentation S
        (cast (show OwnerCarrier S (n+2)=RX2 (state S (n+1)).presentation S from
          if_pos h') c)
     else Vertex.z (rzSyndromeOwner (state S (n+1)).presentation S
        (cast (show OwnerCarrier S (n+2)=RZZ (state S (n+1)).presentation S from
          if_neg h') c)))
    (Vertex.z (rzSyndromeOwner (state S (n+1)).presentation S
      (cast (show OwnerCarrier S (n+2)=RZZ (state S (n+1)).presentation S from
        if_neg h) c)))
  exact dif_neg h
def rzFiberEquiv (S : OddScale) (n : ℕ) (h : (n+2)%2≠1)
    (z : (state S (n+1)).presentation.Z) :
    OwnerFiber S (n+2) (Vertex.z z) ≃ RZFiber (state S (n+1)).presentation S z := by
  let e : OwnerCarrier S (n+2) ≃ RZZ (state S (n+1)).presentation S :=
    Equiv.cast (show OwnerCarrier S (n+2)=RZZ (state S (n+1)).presentation S from if_neg h)
  have he (c : OwnerCarrier S (n+2)) :
      owner S (n+2) c=Vertex.z (rzSyndromeOwner (state S (n+1)).presentation S (e c)) :=
    owner_rz_apply S n h c
  refine {
    toFun := fun c => ⟨e c.val,Vertex.z.inj ((he c.val).symm.trans c.property)⟩
    invFun := fun c => ⟨e.symm c.val,?_⟩
    left_inv := fun c => Subtype.ext (e.symm_apply_apply c.val)
    right_inv := fun c => Subtype.ext (e.apply_symm_apply c.val) }
  rw [he,e.apply_symm_apply]
  exact congrArg Vertex.z c.property
def envelope (S : OddScale) (t : ℝ) : ℝ := (1+Real.exp (-t))^(14*S.ell^2)-1
def alphabet (S : OddScale) : ℝ := QEC.Locality.WeightedConnectedSetMass.alpha (14*S.ell^2+8)
def ratio (S : OddScale) (t : ℝ) : ℝ := alphabet S*envelope S t
abbrev Node (S : OddScale) (depth : ℕ) := (decodingGraph S depth).Node
def structural (S : OddScale) (depth : ℕ) : Finset (Node S depth) :=
  Finset.univ.filter (fun v => v.1.val<2)
def slice (S : OddScale) (depth : ℕ) (i : LevelIndex depth) : Finset (Node S depth) :=
  Finset.univ.filter (fun v => v.1=i)
def sliceEquiv (S : OddScale) (depth : ℕ) (i : LevelIndex depth) :
    {v : Node S depth // v.1=i} ≃ GraphVertex S i.val where
  toFun := fun v => v.property ▸ v.val.2
  invFun := fun w => ⟨⟨i,w⟩,rfl⟩
  left_inv := by rintro ⟨⟨j,w⟩,h⟩; cases h; rfl
  right_inv := by intro w; rfl
def vertexTags (P : TannerSquarePresentation) : Vertex P ≃ P.X ⊕ (P.Q ⊕ P.Z) where
  toFun := fun v => match v with
    | .x x => Sum.inl x
    | .q q => Sum.inr (Sum.inl q)
    | .z z => Sum.inr (Sum.inr z)
  invFun := fun v => match v with
    | .inl x => Vertex.x x
    | .inr (.inl q) => Vertex.q q
    | .inr (.inr z) => Vertex.z z
  left_inv := by intro v; cases v <;> rfl
  right_inv := by rintro (x | (q | z)) <;> rfl
def actualMass (S : OddScale) (depth m : ℕ) (t : ℝ) : ℝ :=
  QEC.Locality.WeightedConnectedSetMass.occupiedMass (BDL26ConnectedSetCounting.graph S depth)
    (BDL26ConnectedSetCounting.levelTwoAnchors S depth) (structural S depth) m
    (fun v => factor S v.1.val v.2 t)
end QEC.Coding.BDL26ConnectedSyndromeMass


