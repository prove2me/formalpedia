-- Prove2me | Definitions.Def_Freiman_middleCover
-- name    : Freiman_middleCover
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:36:26.863201+00:00
-- url     : https://prove2.me/theorems/f727cb68-2f4d-4683-b9c4-0438dd4bab43
-- title:
--   Exact middle-interval cover geometry
-- statement:
--   Exact Part III cover convention: physical outward prefixes, full-width normalization retaining ties, separate equal/mixed parity endpoints, the nine subdivision rows, J family, exact scalar thresholds, and compatible physical-prefix paths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex

import Mathlib.Data.Nat.Fib.Basic
import Definitions.Def_Freiman_prefixEval
import Definitions.Def_Freiman_symbolicMarkovSpectrum

namespace Freiman

structure MiddleCore where
  left : List ℕ+
  right : List ℕ+
  deriving DecidableEq

noncomputable def middleAlpha : ℝ := (Real.sqrt 21 - 3) / 6
noncomputable def middleBeta : ℝ := (Real.sqrt 21 - 3) / 2
noncomputable def middleRho : ℝ := Real.sqrt 3 - 1
noncomputable def middleZeta : ℝ := (Real.sqrt 13 - 3) / 2
noncomputable def middleWidth (w : List ℕ+) : ℝ :=
  |prefixEval w middleBeta - prefixEval w middleAlpha|
noncomputable def middleCD (w : List ℕ+) : ℝ × ℝ :=
  w.foldl (fun z a => (z.2, z.1 + ((a : ℕ) : ℝ) * z.2)) (0, 1)
noncomputable def middleParameter (w : List ℕ+) : ℝ :=
  (middleCD w).1 / (middleCD w).2
noncomputable def middleNormalized (c : MiddleCore) : MiddleCore :=
  if middleWidth c.right ≤ middleWidth c.left then c else ⟨c.right, c.left⟩
noncomputable def middleChild (c : MiddleCore) (u v : List ℕ+) : MiddleCore :=
  if middleWidth c.right ≤ middleWidth c.left then ⟨c.left ++ u, c.right ++ v⟩
  else ⟨c.left ++ v, c.right ++ u⟩
noncomputable def middleE3 (c : MiddleCore) : ℝ :=
  if middleWidth (c.left ++ [3]) ≤ (7 / 5 : ℝ) * middleWidth (c.right ++ [3])
  then 4 + prefixEval (c.left ++ [3]) middleRho + prefixEval (c.right ++ [2]) middleBeta
  else 4 + prefixEval c.left middleAlpha + prefixEval (c.right ++ [3]) middleRho
noncomputable def middleE13 (c : MiddleCore) : ℝ :=
  if middleWidth (c.left ++ [1, 3]) ≤ (7 / 5 : ℝ) * middleWidth (c.right ++ [1, 3])
  then 4 + prefixEval (c.left ++ [1, 3]) middleRho + prefixEval (c.right ++ [1, 2]) middleBeta
  else 4 + prefixEval c.left middleBeta + prefixEval (c.right ++ [1, 3]) middleRho
noncomputable def middleEqualBounds (c : MiddleCore) : ℝ × ℝ :=
  let d := middleNormalized c
  if d.left.length % 2 = 0 then (middleE3 d, middleE13 d)
  else (middleE13 d, middleE3 d)
noncomputable def middleBounds (c : MiddleCore) : ℝ × ℝ :=
  let d := middleNormalized c
  if d.left.length % 2 = d.right.length % 2 then middleEqualBounds d
  else
    let b01 := middleEqualBounds ⟨d.left, d.right ++ [1]⟩
    let b10 := middleEqualBounds ⟨d.left ++ [1], d.right⟩
    if d.left.length % 2 = 0 then (b01.1, b10.2) else (b10.1, b01.2)
noncomputable def middleCover (c : MiddleCore) : Set ℝ :=
  Set.Icc (middleBounds c).1 (middleBounds c).2
noncomputable def middleGood (c : MiddleCore) : Prop :=
  (middleCover (middleChild c [1] []) ∩ middleCover (middleChild c [2] [])).Nonempty
noncomputable def middleRegular (c : MiddleCore) : Prop :=
  middleParameter c.left ∈ Set.Icc (1 / 4 : ℝ) (4 / 5) ∧
  middleParameter c.right ∈ Set.Icc (1 / 4 : ℝ) (4 / 5) ∧
  0 < middleWidth c.left ∧ 0 < middleWidth c.right
noncomputable def middleRatio (c : MiddleCore) : ℝ :=
  middleWidth (middleNormalized c).left / middleWidth (middleNormalized c).right
noncomputable def middleQ (c : MiddleCore) : ℝ :=
  let d := middleNormalized c
  (middleCD d.left).2 ^ 2 / (middleCD d.right).2 ^ 2
noncomputable def middleThreshold (c : MiddleCore) (coef : ℝ)
    (x₁ x₂ y₁ y₂ : ℝ) : ℝ :=
  let d := middleNormalized c
  let p := middleParameter d.left
  let s := middleParameter d.right
  coef * ((1 + s * y₁) * (1 + s * y₂)) / ((1 + p * x₁) * (1 + p * x₂))
noncomputable def middleA (c : MiddleCore) (coef : ℝ) : ℝ :=
  middleThreshold c coef (prefixEval [2,3] middleRho) (prefixEval [1,1,3] middleRho)
    (prefixEval [1,1,2] middleBeta) middleBeta
noncomputable def middleB (c : MiddleCore) (coef : ℝ) : ℝ :=
  middleThreshold c coef (prefixEval [3,1,2] middleBeta) (prefixEval [3] middleAlpha)
    (prefixEval [2,3] middleRho) (prefixEval [1,1,3] middleRho)
noncomputable def middleShort (c : MiddleCore) (n : ℕ) : Prop :=
  let d := middleNormalized c
  middleWidth (d.left ++ List.replicate n 3) ≤
    (7 / 5 : ℝ) * middleWidth (d.right ++ List.replicate n 3)

def middleDigits123 (w : List ℕ+) : Prop := ∀ a ∈ w, (a : ℕ) ≤ 3

def middleProper (c d : MiddleCore) : Prop :=
  ∃ u v : List ℕ+, middleDigits123 u ∧ middleDigits123 v ∧
    d.left = c.left ++ u ∧ d.right = c.right ++ v ∧ 0 < u.length + v.length

def middleCompatible (c : MiddleCore) (a : ℤ → ℕ+) : Prop :=
  a 0 = 4 ∧
  (∀ n : ℕ, n < c.left.length → a (-(n : ℤ) - 1) = c.left.getD n 1) ∧
  (∀ n : ℕ, n < c.right.length → a ((n : ℤ) + 1) = c.right.getD n 1) ∧
  (∀ n : ℕ, c.left.length ≤ n → (a (-(n : ℤ) - 1) : ℕ) ≤ 3) ∧
  (∀ n : ℕ, c.right.length ≤ n → (a ((n : ℤ) + 1) : ℕ) ≤ 3)

noncomputable def middleRealized (c : MiddleCore) (t : ℝ) : Prop :=
  ∃ a : ℤ → ℕ+, middleCompatible c a ∧ localValue a 0 = t
noncomputable def middleJ (c : MiddleCore) (k : ℕ) : MiddleCore :=
  middleChild c (List.replicate k 3) (List.replicate k 3)
noncomputable def middleLimitValue (c : MiddleCore) : ℝ :=
  4 + prefixEval c.left middleZeta + prefixEval c.right middleZeta

inductive MiddleRow
  | mixedA | mixedB | mixedC | equalIShort | equalIJ | equalIIa
  | equalIIbNormal | equalIIbShort | equalIIbJ
  deriving DecidableEq

def middleEssentialJ : MiddleRow → Bool
  | .equalIJ | .equalIIbJ => true
  | _ => false
noncomputable def middleRowChildren (c : MiddleCore) : MiddleRow → List MiddleCore
  | .mixedA => [middleChild c [] [1], middleChild c [1] []]
  | .mixedB | .equalIIa => [middleChild c [3] [], middleChild c [2] [], middleChild c [1] []]
  | .mixedC => [middleChild c [3] [1], middleChild c [2] [], middleChild c [1] []]
  | .equalIShort | .equalIJ =>
      [middleChild c [3] [2], middleChild c [2] [3], middleChild c [2] [2], middleChild c [] [1]]
  | .equalIIbNormal =>
      [middleJ c 1, middleChild c [3] [2], middleChild c [2] [], middleChild c [1] []]
  | .equalIIbShort | .equalIIbJ =>
      [middleChild c [3] [2], middleChild c [2] [], middleChild c [1] []]
noncomputable def middleRowCondition (c : MiddleCore) (r : MiddleRow) : Prop :=
  let d := middleNormalized c
  let same := d.left.length % 2 = d.right.length % 2
  match r with
  | .mixedA => ¬same ∧ middleA c (55 / 100) < middleQ c
  | .mixedB => ¬same ∧ middleQ c ≤ middleA c (55 / 100) ∧ middleQ c < middleB c (328 / 1000)
  | .mixedC => ¬same ∧ middleQ c ≤ middleA c (55 / 100) ∧ middleB c (328 / 1000) ≤ middleQ c
  | .equalIShort => same ∧ middleA c (549 / 1000) < middleQ c ∧ middleShort c 1
  | .equalIJ => same ∧ middleA c (549 / 1000) < middleQ c ∧ ¬middleShort c 1
  | .equalIIa => same ∧ middleQ c ≤ middleA c (549 / 1000) ∧ middleQ c < middleB c (313 / 1000)
  | .equalIIbNormal => same ∧ middleQ c ≤ middleA c (549 / 1000) ∧
      middleB c (313 / 1000) ≤ middleQ c ∧ ¬middleShort c 2
  | .equalIIbShort => same ∧ middleQ c ≤ middleA c (549 / 1000) ∧
      middleB c (313 / 1000) ≤ middleQ c ∧ middleShort c 2 ∧ middleShort c 1
  | .equalIIbJ => same ∧ middleQ c ≤ middleA c (549 / 1000) ∧
      middleB c (313 / 1000) ≤ middleQ c ∧ middleShort c 2 ∧ ¬middleShort c 1

noncomputable def middleUnion (cs : List MiddleCore) : Set ℝ :=
  {t | ∃ d ∈ cs, t ∈ middleCover d}
noncomputable def middleContacts (cs : List MiddleCore) : Prop :=
  (∀ c ∈ cs, (middleCover c).Nonempty) ∧
  ∀ i : ℕ, i + 1 < cs.length →
    (middleCover (cs.getD i ⟨[],[]⟩) ∩ middleCover (cs.getD (i + 1) ⟨[],[]⟩)).Nonempty
noncomputable def middleOuter (c : MiddleCore) (cs : List MiddleCore) : Prop :=
  (∃ d ∈ cs, (middleBounds d).1 ≤ (middleBounds c).1) ∧
  (∃ d ∈ cs, (middleBounds c).2 ≤ (middleBounds d).2)
noncomputable def middleJSpan (c : MiddleCore) : Set ℝ :=
  Set.Icc (min (middleBounds (middleJ c 1)).1 (middleBounds (middleJ c 2)).1)
    (max (middleBounds (middleJ c 1)).2 (middleBounds (middleJ c 2)).2)
noncomputable def middleJAnchors (c : MiddleCore) (cs : List MiddleCore) : Prop :=
  (∃ d ∈ cs, (middleCover (middleJ c 2) ∩ middleCover d).Nonempty) ∧
  (((middleBounds (middleJ c 1)).1 ≤ (middleBounds c).1 ∧
      ∃ d ∈ cs, (middleBounds c).2 ≤ (middleBounds d).2) ∨
    ((middleBounds c).2 ≤ (middleBounds (middleJ c 1)).2 ∧
      ∃ d ∈ cs, (middleBounds d).1 ≤ (middleBounds c).1))
noncomputable def middlePath (c : MiddleCore) (t : ℝ) (p : ℕ → MiddleCore) : Prop :=
  p 0 = c ∧ ∀ n : ℕ, middleRegular (p n) ∧ middleGood (p n) ∧
    t ∈ middleCover (p n) ∧ middleProper (p n) (p (n + 1))

noncomputable def middleScalarThreshold (p s coef x₁ x₂ y₁ y₂ : ℝ) : ℝ :=
  coef * ((1 + s * y₁) * (1 + s * y₂)) / ((1 + p * x₁) * (1 + p * x₂))
noncomputable def middleScalarA (p s coef : ℝ) : ℝ :=
  middleScalarThreshold p s coef (prefixEval [2,3] middleRho) (prefixEval [1,1,3] middleRho)
    (prefixEval [1,1,2] middleBeta) middleBeta
noncomputable def middleScalarB (p s coef : ℝ) : ℝ :=
  middleScalarThreshold p s coef (prefixEval [3,1,2] middleBeta) (prefixEval [3] middleAlpha)
    (prefixEval [2,3] middleRho) (prefixEval [1,1,3] middleRho)
noncomputable def middleHStar (p s : ℝ) : ℝ :=
  middleScalarThreshold p s (5 / 7) middleAlpha (prefixEval [3] middleAlpha)
    middleAlpha (prefixEval [3] middleAlpha)
noncomputable def middleH (p s x y : ℝ) : ℝ :=
  ((1 + s*x)*(1+s*y))/((1+p*x)*(1+p*y))
noncomputable def middleMixedK (p s : ℝ) : ℝ :=
  ((1+s+middleAlpha)*(1+s+middleBeta))/((3+p+middleAlpha)*(3+p+middleBeta))
noncomputable def middleJA : ℝ := prefixEval [3] middleRho
noncomputable def middleJB : ℝ := prefixEval [3,3,1,3] middleRho
noncomputable def middleJC : ℝ := prefixEval [2] middleBeta
noncomputable def middleJD : ℝ := prefixEval [3,3,1,2] middleBeta
noncomputable def middleJR : ℝ := (middleJB-middleJA)/(middleJC-middleJD)
noncomputable def middleJThreshold (p s : ℝ) (k : ℕ) : ℝ :=
  let w : List ℕ+ := List.replicate k 3
  let r := finiteCF w
  middleJR * ((1+r*middleJC)*(1+r*middleJD))/((1+r*middleJA)*(1+r*middleJB)) *
    ((1+s*prefixEval w middleJC)*(1+s*prefixEval w middleJD)) /
    ((1+p*prefixEval w middleJA)*(1+p*prefixEval w middleJB))

noncomputable def middleGapFraction (p : ℝ) : ℝ :=
  let u := prefixEval [2] middleAlpha
  let v := prefixEval [1] middleBeta
  (v-u)/(middleBeta-middleAlpha) *
    ((1+p*middleAlpha)*(1+p*middleBeta))/((1+p*u)*(1+p*v))

end Freiman


