-- Prove2me | Definitions.Def_DetDLP_M89_S1_Queries
-- name    : DetDLP_M89_S1_Queries
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:06:13.950847+00:00
-- url     : https://prove2.me/theorems/7df188b0-d523-4247-9c9a-a48396cb1734
-- title:
--   Exact prefix-count queries for Stage I
-- statement:
--   A tagged query requests the curve cardinality, one of the four seed-prefix moments, a one-element prefix count, or a two-tuple decomposition prefix count. The count is a natural number specified on the exact framed input. A single uniform count machine must return its canonical singleton-list encoding within Stage I time and polynomial space.
-- source:
--   Deterministic Discrete Logarithms in Subexponential Time from Boolean Tensor Contraction, Sections 3.1–3.2, proof of Theorem 3.1.

import Definitions.Def_DetDLP_M89_S1_Prefix
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false
namespace DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Public input consists of a tag, the field or curve, and a list of payload words. -/
def queryWord (tag : ℕ) (base : List Bool) (payload : List (List Bool)) : List Bool :=
  Encoding.encodeList id (countWord tag :: base :: payload)

def digitWord (b n : ℕ) := List.ofFn (fun i : Fin b => n.testBit i.rev.val)

def ecWord {p : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)} (b : ℕ) : E.toAffine.Point → List Bool
  | .zero => true :: (digitWord b 0 ++ digitWord b 0)
  | .some x y _ => false :: (digitWord b x.val ++ digitWord b y.val)

def tupleWord {G : Type} {m : ℕ} (enc : G → List Bool) (ab : (Fin m → G) × (Fin m → G)) :=
  (List.finRange m).flatMap (fun i => enc (ab.1 i) ++ enc (ab.2 i))

/-- The four moments in order are completion mass, size, squared size and collision energy. -/
def moment {α : Type} [Fintype α] {L : ℕ} (bits : α → Fin L → Bool) (W C : α → ℕ)
    (j : Fin 4) (η : List Bool) : ℕ :=
  ∑ s ∈ Finset.univ.filter (fun s => (List.ofFn (bits s)).take η.length = η),
    if j = 0 then 1 else if j = 1 then W s else if j = 2 then (W s)^2 else C s

def elemCount {G : Type} (D : Finset G) (enc : G → List Bool) (η : List Bool) :=
  (D.filter (fun x => (enc x).take η.length = η)).card

noncomputable def pairCount {G : Type} [Fintype G] {m : ℕ} (D : Fin m → Finset G)
    (enc : G → List Bool) (rel : ((Fin m → G) × (Fin m → G)) → Prop) (η : List Bool) : ℕ := by
  classical
  exact (Finset.univ.filter (fun ab => (∀ i, ab.1 i ∈ D i ∧ ab.2 i ∈ D i) ∧
    (tupleWord enc ab).take η.length = η ∧ rel ab)).card

/-- Semantic specification of the words on which the query machine must return an exact answer.
Fields $T$ and $S$ are explicit: the scalar program does not select the seed. -/
inductive Query : List Bool → ℕ → ℕ → Prop
  | ecOrder (p : ℕ) [Fact p.Prime] (hp : 3 < p) (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] :
      Query (queryWord 0 (encodeCurveInput p E) []) (bitLen p) (@Fintype.card _ (ecPointFintype E))
  | fpMoment (p : ℕ) [Fact p.Prime] (j : Fin 4) (T : ℕ) (hT : T ≤ p) (η : List Bool)
      (hlen : η.length ≤ blockCount (bitLen p)*2*bitLen p) :
      Query (queryWord 1 (countWord p) [countWord j.val,countWord T,η]) (bitLen p) (let m := blockCount (bitLen p); let D := fun S : FpSeed p m => fpFactorBlock (p := p) T S; moment fpBits (fun S => productSize (D S)) (fun S => collisionEnergyMul (D S)) j η)
  | ecMoment (p : ℕ) [Fact p.Prime] (hp : 3 < p) (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
      (j : Fin 4) (T : ℕ) (hT : T ≤ p) (η : List Bool) (hlen : η.length ≤ blockCount (bitLen p)*4*bitLen p) :
      Query (queryWord 2 (encodeCurveInput p E) [countWord j.val,countWord T,η]) (bitLen p) (letI := ecPointFintype E; let m := blockCount (bitLen p); let D := fun S : ECSeed p m => ecFactorBlock E T S; moment ecBits (fun S => productSize (D S)) (fun S => collisionEnergyAdd (D S)) j η)
  | fpElem (p : ℕ) [Fact p.Prime] (T : ℕ) (hT : T ≤ p) (S : FpSeed p (blockCount (bitLen p)))
      (i : Fin (blockCount (bitLen p))) (η : List Bool) (hlen : η.length ≤ bitLen p) :
      Query (queryWord 3 (countWord p) [countWord T,List.ofFn (fpBits S),countWord i.val,η]) (bitLen p)
        (elemCount (fpFactorBlock (p := p) T S i) (fun x => digitWord (bitLen p) (x : ZMod p).val) η)
  | ecElem (p : ℕ) [Fact p.Prime] (hp : 3 < p) (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
      (T : ℕ) (hT : T ≤ p) (S : ECSeed p (blockCount (bitLen p))) (i : Fin (blockCount (bitLen p)))
      (η : List Bool) (hlen : η.length ≤ 2*bitLen p+1) :
      Query (queryWord 4 (encodeCurveInput p E) [countWord T,List.ofFn (ecBits S),countWord i.val,η]) (bitLen p)
        (elemCount (ecFactorBlock E T S i) (ecWord (bitLen p)) η)
  | fpPair (p : ℕ) [Fact p.Prime] (T : ℕ) (hT : T ≤ p) (S : FpSeed p (blockCount (bitLen p)))
      (X : (ZMod p)ˣ) (η : List Bool) (hlen : η.length ≤ 2*blockCount (bitLen p)*bitLen p) :
      Query (queryWord 5 (countWord p) [countWord T,List.ofFn (fpBits S),countWord (X : ZMod p).val,η]) (bitLen p)
        (pairCount (fpFactorBlock (p := p) T S) (fun a => digitWord (bitLen p) (a : ZMod p).val)
          (fun ab => (∏ i, (ab.1 i * ab.2 i)) = X) η)
  | ecPair (p : ℕ) [Fact p.Prime] (hp : 3 < p) (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
      (T : ℕ) (hT : T ≤ p) (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point)
      (η : List Bool) (hlen : η.length ≤ 2*blockCount (bitLen p)*(2*bitLen p+1)) :
      Query (queryWord 6 (encodeCurveInput p E) [countWord T,List.ofFn (ecBits S),encodeNatListBin (pointCoords X),η]) (bitLen p)
        (letI := ecPointFintype E; pairCount (ecFactorBlock E T S) (ecWord (bitLen p)) (fun ab => (∑ i, (ab.1 i + ab.2 i)) = X) η)

abbrev CountOracle := ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (K : ℕ),
  ∀ w b n, Query w b n → RunsWithin M o w (encodeNatListBin [n]) (mainSpaceBound K b) (polyBound K b)

end DetDLP.M89S1


