-- Prove2me | Definitions.Def_FixedPolyominoSquare_SquareCounting_WangModel
-- name    : FixedPolyominoSquare_SquareCounting_WangModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:46.107192+00:00
-- url     : https://prove2.me/theorems/a934f517-ace4-4314-bd58-7440bbd62b61
-- title:
--   Finite Wang types and open rectangle counts
-- statement:
--   A finite Wang system $W$ has numbered tile types, horizontal colours and vertical colours. Each tile type carries west, east, south and north colours; the map from a type to its four colours need not be injective. An assignment gives one tile type to each cell of a finite region, matching only the colours on internal adjacent edges.
--
--   $$a_{\rm rect}(w,h)=|\operatorname{OpenTilings}_W(\mathrm{Rect}_{w,h})|,\qquad a_{\rm square}(n)=a_{\rm rect}(n,n).$$
--
--   The counts are cardinalities obtained by filtering all assignments on the finite cell subtype. No boundary conditions or simulated-computation restrictions are imposed. The associated binary Wang-count function is $a_{\rm square}(n)$ on canonical positive $n$, and zero otherwise; its value at the code of zero therefore differs from the geometric square-count function.
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), p. 3, Section 2; p. 22, Section 8

import Mathlib
import Definitions.Def_FixedPolyominoSquare_SquareCounting_PolyominoModel

namespace FixedPolyominoSquare.SquareCounting

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Types are indexed independently of their four colours. -/
structure WangSystem where
  types : ℕ
  horizontal : ℕ
  vertical : ℕ
  west : Fin types → Fin horizontal
  east : Fin types → Fin horizontal
  south : Fin types → Fin vertical
  north : Fin types → Fin vertical

abbrev WangAssignment (W : WangSystem) (Ω : Region) := Ω → Fin W.types

def WangMatches (W : WangSystem) (Ω : Region) (f : WangAssignment W Ω) : Prop :=
  (∀ a b : Ω, b.val = a.val + (1, 0) → W.east (f a) = W.west (f b)) ∧
  (∀ a b : Ω, b.val = a.val + (0, 1) → W.north (f a) = W.south (f b))

def WangTilings (W : WangSystem) (Ω : Region) :=
  {f : WangAssignment W Ω // WangMatches W Ω f}

def wangCount (W : WangSystem) (Ω : Region) : ℕ :=
  (Finset.univ.filter (WangMatches W Ω)).card

def aRect (W : WangSystem) (w h : ℕ) : ℕ := wangCount W (rect w h)

def aSquare (W : WangSystem) (n : ℕ) : ℕ := aRect W n n

def Gwang (W : WangSystem) (z : Bits) : ℕ :=
  match decode z with
  | some n => if 1 ≤ n then aSquare W n else 0
  | none => 0

end
end FixedPolyominoSquare.SquareCounting


