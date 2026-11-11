-- Prove2me | Definitions.Def_TDHamSim_QueryOptimal_Dyadic
-- name    : TDHamSim_QueryOptimal_Dyadic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:19:31.591601+00:00
-- url     : https://prove2.me/theorems/e44f741f-de2b-46a2-ad57-e33ff716dd86
-- title:
--   Dyadic basis changes and physical flag-register encoding
-- statement:
--   The matrices $\operatorname{Rot}(r)$, $M_{\rm in}(r)$ and $M_{\rm out}(r)$ follow the ordered bases of §6.1. The time-register basis changes apply their controlled single-bit rotations in descending bit order. Plane rotations define $C_J$ independently of those basis changes.
--
--   $$\Phi_P=I_{\rm pub}\oplus iI_{\rm priv}.$$
--
--   The private-space lifts, remaining rotation, and phase are explicitly represented. The direct-sum model is embedded into the flag-register model with identity on unused public states. Time bits are read least significant first. The controlled HAM-T matrix acts on a control bit, time bits, block ancillas, and system bits, preserving the source query convention.
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), (60)–(72), pp.25–28; Convention 1, p.14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Reuse

namespace TDHamSim.QueryOptimal

/-- Two-dimensional rotations, in the ordered basis printed in §6.1. -/
noncomputable def rot (r : ℝ) : Mat Bool :=
  fun x y => if x = y then r else if x then Real.sqrt (1 - r^2) else -Real.sqrt (1 - r^2)
noncomputable def mix (out : Bool) (r : ℝ) : Mat Bool :=
  fun x y => ((Real.sqrt (1 + r^2))⁻¹ : ℝ) *
    (if out then if x then if y then -1 else r else if y then r else 1
     else if x then if y then -r else 1 else if y then 1 else r)
noncomputable def timeMix (m ℓ : ℕ) (M : Mat Bool) : Mat (Fin (2^m)) :=
  fun x y => if x.val / 2^(ℓ+1) = y.val / 2^(ℓ+1) ∧
      x.val % 2^ℓ = 0 ∧ y.val % 2^ℓ = 0 then
      M (x.val.testBit ℓ) (y.val.testBit ℓ)
    else if x = y then 1 else 0
noncomputable def timeW (m : ℕ) (out : Bool) (c : ℝ) : Mat (Fin (2^m)) :=
  ((List.range m).reverse.map fun ℓ => timeMix m ℓ (mix out (c^(2^ℓ)))).foldl
    (fun acc U => U * acc) 1
noncomputable def planeRot (J : ℕ) (j : Fin J) (r : ℝ) : Mat (Sum Unit (Fin J))
  | Sum.inl _, Sum.inl _ => r
  | Sum.inl _, Sum.inr y => if y = j then -Real.sqrt (1-r^2) else 0
  | Sum.inr x, Sum.inl _ => if x = j then Real.sqrt (1-r^2) else 0
  | Sum.inr x, Sum.inr y => if x = y then if x = j then r else 1 else 0
noncomputable def rotationProduct (J : ℕ) (c : ℝ) : Mat (Sum Unit (Fin J)) :=
  (List.ofFn fun j : Fin J => planeRot J j c).foldl (fun acc U => U * acc) 1
noncomputable def liftedW (m : ℕ) (out : Bool) (c : ℝ) : Mat (Sum Unit (Fin (2^m))) :=
  Matrix.fromBlocks 1 0 0 (timeW m out c)
noncomputable def dyadicW (m a n : ℕ) (out : Bool) (c : ℝ) : Mat (Space (2^m) a n)
  | Sum.inl x, Sum.inl y => if x = y then 1 else 0
  | Sum.inr x, Sum.inr y =>
      if x.2.2 = y.2.2 then
        if x.2.1 = (fun _ => false) ∧ y.2.1 = (fun _ => false) then timeW m out c x.1 y.1
        else if x = y then 1 else 0
      else 0
  | _, _ => 0
noncomputable def totalRot (m a n : ℕ) (r : ℝ) : Mat (Space (2^m) a n) :=
  let j : Fin (2^m) := ⟨0, pow_pos (by decide) _⟩
  Matrix.fromBlocks ((r : ℂ) • 1)
    ((-Real.sqrt (1-r^2) : ℝ) •
      (fun x y => if y.1 = j then (iota a n).conjTranspose x y.2 else 0))
    ((Real.sqrt (1-r^2) : ℝ) •
      (fun x y => if x.1 = j then iota a n x.2 y else 0))
    (fun x y => (1 : Mat (Priv (2^m) a n)) x y +
      if x.1 = j ∧ y.1 = j then (r - 1) * ancProj a n x.2 y.2 else 0)
noncomputable def privatePhase (J a n : ℕ) : Mat (Space J a n) :=
  Matrix.fromBlocks 1 0 0 (Complex.I • 1)

/-- Paper uses the least significant time qubit first; reverse the published MSB convention. -/
def timeIndex (m : ℕ) (x : Bits m) : Fin (2^m) :=
  QAlgorithms.bitsEquivFin m (fun i => x i.rev)
def slice {N : ℕ} (off len : ℕ) (h : off + len ≤ N) (x : Bits N) : Bits len :=
  fun i => x ⟨off + i.val, by omega⟩
def decode (m a n : ℕ) (x : Bits (1+m+a+n)) : Option (Space (2^m) a n) :=
  let t := slice 1 m (by omega) x
  let u := slice (1+m) a (by omega) x
  let v := slice (1+m+a) n (by omega) x
  if x ⟨0, by omega⟩ then some (Sum.inr (timeIndex m t, u, v))
  else if t = (fun _ => false) ∧ u = (fun _ => false) then some (Sum.inl v) else none

/-- Convention 1: identity on the unused public register states. -/
noncomputable def physical (m a n : ℕ) (U : Mat (Space (2^m) a n)) : Mat (Bits (1+m+a+n)) :=
  fun x y => match decode m a n x, decode m a n y with
    | some u, some v => U u v
    | none, none => if x = y then 1 else 0
    | _, _ => 0

/-- Controlled HAM-T on one control, m time, a block-ancilla and n system wires. -/
noncomputable def controlledHAMT {m a n : ℕ} (O : Fin (2^m) → Mat (Bits a × Bits n)) :
    Mat (Bits (1+m+a+n)) :=
  fun x y =>
    if x ⟨0, by omega⟩ = y ⟨0, by omega⟩ then
      if x ⟨0, by omega⟩ then
        hamT O (timeIndex m (slice 1 m (by omega) x), slice (1+m) a (by omega) x,
          slice (1+m+a) n (by omega) x)
          (timeIndex m (slice 1 m (by omega) y), slice (1+m) a (by omega) y,
          slice (1+m+a) n (by omega) y)
      else if x = y then 1 else 0
    else 0

end TDHamSim.QueryOptimal


