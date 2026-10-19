-- Prove2me | Definitions.Def_QAlgorithms_Defs_ExpanderCodeDecoding
-- name    : QAlgorithms_Defs_ExpanderCodeDecoding
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:27:51.748268+00:00
-- url     : https://prove2.me/theorems/13697572-9ba0-427d-8f89-603df5bbae47
-- title:
--   ExpanderCodeDecoding
-- statement:
--   ExpanderCodeDecoding
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ExpanderCodeDecoding.lean

import Definitions.Def_QAlgorithms_Defs_ExpanderCodeGraphs
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.ExpanderCodes

/-- Binary X/Z pair; Y has two ones at the same coordinate; 1504.00822 p.6. -/
abbrev Error (Q : Type*) := (Q → ZMod 2) × (Q → ZMod 2)

/-- Union support weight, counting Y once; 1504.00822 p.7. -/
def errorWeight {Q : Type*} [Fintype Q] (e : Error Q) : ℕ :=
  (Finset.univ.filter fun q => e.1 q ≠ 0 ∨ e.2 q ≠ 0).card

/-- Entire error-dependent decoder input; 1504.00822 pp.2,6. -/
def syndrome {nA nB : ℕ} (G : BipartiteData nA nB)
    (e : Error ((Fin nA × Fin nA) ⊕ (Fin nB × Fin nB))) :=
  ((checks G).1.mulVec e.1, (checks G).2.mulVec e.2)

/-- Recovery modulo opposite row spaces; none is failure; 1504.00822 pp.6–7. -/
def DecodingSuccess {nA nB : ℕ} (G : BipartiteData nA nB)
    (e : Error ((Fin nA × Fin nA) ⊕ (Fin nB × Fin nB)))
    (out : Option (Error ((Fin nA × Fin nA) ⊕ (Fin nB × Fin nB)))) : Prop :=
  ∃ c, out = some c ∧ c.1+e.1 ∈ FieldCodes.rowSpace (checks G).2 ∧
    c.2+e.2 ∈ FieldCodes.rowSpace (checks G).1

/-- Actual generator row supports; 1504.00822 p.7 (5)–(6).
Using the rows fixes the coordinate-name typo in printed (6). -/
def generatorSupports {R Q : Type*} [Fintype R] [Fintype Q]
    (H : Matrix R Q (ZMod 2)) : Finset (Finset Q) :=
  Finset.univ.image fun r => Finset.univ.filter fun q => H r q ≠ 0

/-- Binary flip indicator; 1504.00822 p.7. -/
def flipVector {Q : Type*} (F : Finset Q) : Q → ZMod 2 :=
  fun q => if q ∈ F then 1 else 0

/-- Nonempty improving generator subsets; 1504.00822 pp.7–8. -/
def improvingFlips {R Q : Type*} [Fintype R] [Fintype Q]
    (H : Matrix R Q (ZMod 2)) (gens : Finset (Finset Q)) (s : R → ZMod 2) :
    Finset (Finset Q) :=
  (gens.biUnion Finset.powerset).filter fun F =>
    F.Nonempty ∧ hammingNorm (s+H.mulVec (flipVector F)) < hammingNorm s

/-- Maximum ratio with a fixed binary-mask tie order; 1504.00822 pp.7–8. -/
def chooseFlip {R Q : Type*} [Fintype R] [Fintype Q]
    (H : Matrix R Q (ZMod 2)) (gens : Finset (Finset Q)) (s : R → ZMod 2) :
    Option (Finset Q) := by
  classical
  let score := fun F : Finset Q =>
    (((hammingNorm s : ℝ) - hammingNorm (s+H.mulVec (flipVector F)))/F.card,
      ∑ q ∈ F, 2 ^ ((Fintype.equivFin Q) q : ℕ))
  exact ((improvingFlips H gens s).toList.mergeSort
    (fun F F' => decide ((score F').1 < (score F).1 ∨
      ((score F').1 = (score F).1 ∧ (score F').2 ≤ (score F).2)))).head?

/-- Fuelled small-set-flip; initial syndrome weight suffices by strict decrease;
1504.00822 pp.7–8. Fuel exhaustion with nonzero syndrome signifies failure. -/
def smallSetFlipLoop {R Q : Type*} [Fintype R] [Fintype Q]
    (H : Matrix R Q (ZMod 2)) (gens : Finset (Finset Q)) :
    ℕ → (R → ZMod 2) → (Q → ZMod 2) → Option (Q → ZMod 2)
  | 0, s, c => if s = 0 then some c else none
  | fuel+1, s, c => if s = 0 then some c else
      match chooseFlip H gens s with
      | none => none
      | some F => smallSetFlipLoop H gens fuel (s+H.mulVec (flipVector F)) (c+flipVector F)

/-- Both independently decoded components; 1504.00822 pp.7–8. -/
def smallSetFlip {nA nB : ℕ} (G : BipartiteData nA nB)
    (s : ((Fin nA × Fin nB) → ZMod 2) × ((Fin nB × Fin nA) → ZMod 2)) :
    Option (Error ((Fin nA × Fin nA) ⊕ (Fin nB × Fin nB))) := do
  let x ← smallSetFlipLoop (checks G).1 (generatorSupports (checks G).2)
    (hammingNorm s.1) s.1 0
  let z ← smallSetFlipLoop (checks G).2 (generatorSupports (checks G).1)
    (hammingNorm s.2) s.2 0
  pure (x,z)

example : errorWeight ((fun _ : Fin 1 => 1), (fun _ => 1)) = 1 := by decide

example {R Q : Type*} [Fintype R] [Fintype Q]
    (H : Matrix R Q (ZMod 2)) (gens : Finset (Finset Q)) (c : Q → ZMod 2) :
    smallSetFlipLoop H gens 0 0 c = some c := by simp [smallSetFlipLoop]

end QAlgorithms.ExpanderCodes


