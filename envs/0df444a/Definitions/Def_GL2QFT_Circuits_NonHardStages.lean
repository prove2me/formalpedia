-- Prove2me | Definitions.Def_GL2QFT_Circuits_NonHardStages
-- name    : GL2QFT_Circuits_NonHardStages
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:59:46.937796+00:00
-- url     : https://prove2.me/theorems/9709e1a1-31ba-45b9-b060-6d0c62a664f7
-- title:
--   Routing and closed-form $2\times2$ stages for the non-hard total A-matrix
-- statement:
--   This module stages the non-hard part of the total induction matrix following equations (128)–(139). A source label is first retained while a clean two-level register is initialized. A coherent direct sum of closed-form two-level matrices then applies either a phase, the determinant–Steinberg rotation, or the mixed-block Gauss phase. Finally, the source label and two-level output are routed to the determinant, Steinberg, or canonically ordered principal-series output label.
--
--   The prescribed first columns are exactly the columns displayed in equations (128)–(139). The second columns use the standard unitary completion, so they do not affect the staged map on the initialized input register. The intermediate code is the ordinary ten-field input code followed by one clean wire.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.4, equations (128)–(139), pp.45–46 (PDF pp.46–47), and the routing paragraph of the proof of Theorem 6.14, p.47 (PDF p.48).

import Definitions.Def_GL2QFT_Circuits_Leaves

set_option autoImplicit false
noncomputable section

open Classical

namespace GL2QFT
namespace Circuits

open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms

/-- The output irrep selected by a non-hard source with character parameters `a,b`.
For `a = b`, the two output rows are Steinberg and determinant; otherwise they coincide at the
canonically ordered principal-series label. -/
def nonHardOutIrr (D : FieldData) (a b : D.Lab) (second : Bool) : D.Irr :=
  if a = b then
    if second then .inl a else .inr (.inl a)
  else if h : a.val < b.val then
    .inr (.inr (.inl ⟨(a, b), h⟩))
  else if h : b.val < a.val then
    .inr (.inr (.inl ⟨(b, a), h⟩))
  else
    .inr (.inl a)

/-- The output row assigned to a non-hard source and the local two-level output bit. -/
def nonHardOutCore (D : FieldData) (x : InRegNonHard D) (second : Bool) : OutReg D :=
  match x.1.1.1, x.1.1.2.2.2 with
  | .inl ab, .inl cd => (.inl ab, nonHardOutIrr D ab.1 ab.2 second, .inl cd)
  | .inl ab, .inr γ => (.inl ab, nonHardOutIrr D ab.1 ab.2 second, .inr γ)
  | .inr γ, .inl ab => (.inr γ, nonHardOutIrr D ab.1 ab.2 second, .inl ab)
  | .inr γ, .inr δ => (.inr γ, .inr (.inl 0), .inr δ)

/-- The output routing map, landing in the non-hard output register. -/
def nonHardOut (D : FieldData) (x : InRegNonHard D) (second : Bool) : OutRegNonHard D :=
  ⟨nonHardOutCore D x second, by
    have hx := x.2
    rcases x with ⟨⟨⟨l, κ, ω, lt⟩, hv⟩, hn⟩
    cases l with
    | inl ab =>
        cases lt with
        | inl cd => simp [isHardOut, nonHardOutCore]
        | inr γ => simp [isHardOut, nonHardOutCore]
    | inr γ =>
        cases lt with
        | inl ab => simp [isHardOut, nonHardOutCore]
        | inr δ => simp [isHardIn] at hn⟩

/-- Extra clean two-level register used for the local closed-form gates. -/
abbrev NonHardMid (D : FieldData) := InRegNonHard D × Bool

/-- Code of the non-hard source register together with its clean local two-level register. -/
def nonHardMidCode (D : FieldData) : NonHardMid D → Qubits (10 * D.labW + 1) :=
  appendCode (fun x : InRegNonHard D => inCodeA D x.1)
    (fun b : Bool => fun (_ : Fin 1) => b)

/-- Reversible input routing: retain the source label and initialize the local two-level register. -/
def nonHardPrepare (D : FieldData) : Matrix (NonHardMid D) (InRegNonHard D) ℂ :=
  permMat (fun x => (x, false))

/-- A two-level matrix with prescribed first column `(a,b)` and its standard completion. -/
def nonHardU2OfColumn (a b : ℂ) : Matrix Bool Bool ℂ
  | false, false => a
  | true, false => b
  | false, true => -star b
  | true, true => star a

/-- The diagonal determinant--Steinberg rotation column, with its unitary completion. -/
def nonHardDiagU2 (D : FieldData) (a : D.Lab) (ω : Bool) : Matrix Bool Bool ℂ :=
  let c : ℂ := Real.sqrt (D.q / (D.q + 1 : ℝ))
  let s : ℂ := Real.sqrt (1 / (D.q + 1 : ℝ))
  if ω then nonHardU2OfColumn (-(D.chi a (-1) * s)) (D.chi a (-1) * c)
  else nonHardU2OfColumn c s

/-- The phase on a mixed one-dimensional/two-dimensional non-hard block. -/
def nonHardMixedPhase (D : FieldData) (ab : D.Lab × D.Lab) : ℂ :=
  if ab.1 = ab.2 then D.chi ab.1 (-1)
  else if ab.1.val < ab.2.val then 1
  else zeta D ab.2 ab.1

/-- The closed-form local gate for a non-hard source. -/
def nonHardU2 (D : FieldData) (x : InRegNonHard D) : Matrix Bool Bool ℂ :=
  match x.1.1.1, x.1.1.2.2.2 with
  | .inl ab, .inl _ =>
      if ab.1 = ab.2 then nonHardDiagU2 D ab.1 x.1.1.2.2.1
      else nonHardU2OfColumn 1 0
  | .inl ab, .inr _ => nonHardU2OfColumn (nonHardMixedPhase D ab) 0
  | .inr _, .inl ab => nonHardU2OfColumn (nonHardMixedPhase D ab) 0
  | .inr _, .inr _ => nonHardU2OfColumn 1 0

/-- Coherent direct sum of the local one- and two-dimensional closed-form gates. -/
def nonHardLocal (D : FieldData) : Matrix (NonHardMid D) (NonHardMid D) ℂ :=
  subMat (nonHardU2 D)

/-- Output routing from the source labels and local two-level output to the ordinary A-register. -/
def nonHardFinish (D : FieldData) : Matrix (OutRegNonHard D) (NonHardMid D) ℂ :=
  permMat (fun p => nonHardOut D p.1 p.2)

end Circuits
end GL2QFT


