-- Prove2me | Definitions.Def_OAIQ259US002
-- name    : OAIQ259US002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:07:14.584623+00:00
-- url     : https://prove2.me/theorems/3a91a8a3-eba9-4bde-878d-56fad74cffdf
-- title:
--   Definitions bundle OAIQ259US002 of the split of OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 571 declarations of OpenAI's Lean: 570 definitions and 1 instance. The definitions and types are `OAI.UniversalTensorSquare.degreeQs112`, `OAI.UniversalTensorSquare.degreeQs118`, `OAI.UniversalTensorSquare.degreeQs12`, `OAI.UniversalTensorSquare.degreeQs14`, `OAI.UniversalTensorSquare.degreeQs151`, `OAI.UniversalTensorSquare.degreeQs16`, `OAI.UniversalTensorSquare.degreeQs17`, `OAI.UniversalTensorSquare.degreeQs18`, `OAI.UniversalTensorSquare.degreeQs19`, `OAI.UniversalTensorSquare.degreeQs20`, `OAI.UniversalTensorSquare.degreeQs22`, `OAI.UniversalTensorSquare.degreeQs23`, `OAI.UniversalTensorSquare.degreeQs24`, `OAI.UniversalTensorSquare.degreeQs25`, `OAI.UniversalTensorSquare.degreeQs26`, `OAI.UniversalTensorSquare.degreeQs27`, `OAI.UniversalTensorSquare.degreeQs29`, `OAI.UniversalTensorSquare.degreeQs30`, `OAI.UniversalTensorSquare.degreeQs31`, `OAI.UniversalTensorSquare.degreeQs32`, `OAI.UniversalTensorSquare.degreeQs33`, `OAI.UniversalTensorSquare.degreeQs34`, `OAI.UniversalTensorSquare.degreeQs35`, `OAI.UniversalTensorSquare.degreeQs37`, `OAI.UniversalTensorSquare.degreeQs38`, `OAI.UniversalTensorSquare.degreeQs39`, `OAI.UniversalTensorSquare.degreeQs40`, `OAI.UniversalTensorSquare.degreeQs41`, `OAI.UniversalTensorSquare.degreeQs42`, `OAI.UniversalTensorSquare.degreeQs43`, `OAI.UniversalTensorSquare.degreeQs44`, `OAI.UniversalTensorSquare.degreeQs46`, `OAI.UniversalTensorSquare.degreeQs47`, `OAI.UniversalTensorSquare.degreeQs48`, `OAI.UniversalTensorSquare.degreeQs49`, `OAI.UniversalTensorSquare.degreeQs50`, `OAI.UniversalTensorSquare.degreeQs51`, `OAI.UniversalTensorSquare.degreeQs52`, `OAI.UniversalTensorSquare.degreeQs53`, `OAI.UniversalTensorSquare.degreeQs54` and 530 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `UniversalSquare_Band_BandAllocation`, `UniversalSquare_Capacity_RefinedCapacity`, `UniversalSquare_Capacity_RefinedExhaustion`, `UniversalSquare_Finite_DegreeEight`, `UniversalSquare_Finite_DegreeFive`, `UniversalSquare_Finite_DegreePlans116`, `UniversalSquare_Finite_DegreePlans118`, `UniversalSquare_Finite_DegreePlans14`, `UniversalSquare_Finite_DegreePlans16`, `UniversalSquare_Finite_DegreePlans18`, `UniversalSquare_Finite_DegreePlans19`, `UniversalSquare_Finite_DegreePlans20`, `UniversalSquare_Finite_DegreePlans22`, `UniversalSquare_Finite_DegreePlans24`, `UniversalSquare_Finite_DegreePlans26`, `UniversalSquare_Finite_DegreePlans31`, `UniversalSquare_Finite_DegreePlans35`, `UniversalSquare_Finite_DegreePlans37`, `UniversalSquare_Finite_DegreePlans39`, `UniversalSquare_Finite_DegreePlans41`, `UniversalSquare_Finite_DegreePlans43`, `UniversalSquare_Finite_DegreePlans58`, `UniversalSquare_Finite_DegreePlans62`, `UniversalSquare_Finite_DegreePlans64`, `UniversalSquare_Finite_DegreePlans89`, `UniversalSquare_Finite_DegreeSeven`, `UniversalSquare_Finite_EightSplitCertificate`, `UniversalSquare_Finite_NumericalDegree112`, `UniversalSquare_Finite_NumericalDegree12`, `UniversalSquare_Finite_NumericalDegree151`, `UniversalSquare_Finite_NumericalDegree17`, `UniversalSquare_Finite_NumericalDegree23`, `UniversalSquare_Finite_NumericalDegree25`, `UniversalSquare_Finite_NumericalDegree27`, `UniversalSquare_Finite_NumericalDegree29`, `UniversalSquare_Finite_NumericalDegree30`, `UniversalSquare_Finite_NumericalDegree32`, `UniversalSquare_Finite_NumericalDegree33`, `UniversalSquare_Finite_NumericalDegree34`, `UniversalSquare_Finite_NumericalDegree38`, `UniversalSquare_Finite_NumericalDegree40`, `UniversalSquare_Finite_NumericalDegree42`, `UniversalSquare_Finite_NumericalDegree44`, `UniversalSquare_Finite_NumericalDegree46`, `UniversalSquare_Finite_NumericalDegree47`, `UniversalSquare_Finite_NumericalDegree48`, `UniversalSquare_Finite_NumericalDegree49`, `UniversalSquare_Finite_NumericalDegree50`, `UniversalSquare_Finite_NumericalDegree51`, `UniversalSquare_Finite_NumericalDegree52`, `UniversalSquare_Finite_NumericalDegree53`, `UniversalSquare_Finite_NumericalDegree54`, `UniversalSquare_Finite_NumericalDegree56`, `UniversalSquare_Finite_NumericalDegree57`, `UniversalSquare_Finite_NumericalDegree59`, `UniversalSquare_Finite_NumericalDegree60`, `UniversalSquare_Finite_NumericalDegree61`, `UniversalSquare_Finite_NumericalDegree63`, `UniversalSquare_Semigroup_SemigroupLeaves1`, `UniversalSquare_Semigroup_SemigroupLeaves2`, `UniversalSquare_Semigroup_SemigroupLeaves3`, `UniversalSquare_Semigroup_SemigroupLeaves4`, `UniversalSquare_Semigroup_SemigroupLeaves5`, `UniversalSquare_Support_ConstrainedDiagrams`, `UniversalSquare_Support_ExceptionalFourteen`, `UniversalSquare_Support_FiniteDiagrams`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ259US008`, `OAIQ259US009`, `OAIQ259US010` and `OAIQ259US012`; the statement `OAI.UniversalTensorSquare.degreeCones151`.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Allocation. -/

section

noncomputable section
namespace UniversalTensorSquare

def prefixFill (f : ℕ → ℕ) (r i : ℕ) : ℕ :=
  min (f i) (r - ∑ j ∈ Finset.range i, f j)

def extraCapacity (μ : YoungDiagram) (d q i : ℕ) : ℕ :=
  if i < q then (μ.colLen i-d)/2 else 0

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RefinedCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined Capacity. -/

section

noncomputable section
namespace UniversalTensorSquare

def endpointBound (i U H : ℕ) : ℕ :=
  if i = 1 then U else min (U/i) ((U-H)/(i-1))

def refinedArea (i j U V X Y H W : ℕ) : ℕ :=
  if j ≤ X ∧ i ≤ Y then
    max (U+V-(min i W + min j H - 1)) (U+V-i*j+(X-j)*(Y-i))
  else U+V-(min i W + min j H - 1)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RefinedExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare

def minHeight (n : ℕ) (B : List (ℕ × ℕ)) : ℕ :=
  B.foldr (fun p h => if p.2 < n then max (p.1+1) h else h) 1

def impossibleBounds (n : ℕ) (A B : List (ℕ × ℕ)) : Prop :=
  (∃ p ∈ A, p.2 < minHeight n B) ∨
  (∃ q ∈ B, q.2 < minHeight n A) ∨
  ∃ p ∈ A, ∃ q ∈ B,
    refinedArea p.1 q.1 p.2 q.2
      (endpointBound p.1 p.2 (minHeight n B))
      (endpointBound q.1 q.2 (minHeight n A))
      (minHeight n B) (minHeight n A) < n

instance instDecidableImpossibleBounds (n : ℕ) (A B : List (ℕ × ℕ)) : Decidable (impossibleBounds n A B) :=
  inferInstanceAs (Decidable ((∃ p ∈ A, p.2 < minHeight n B) ∨
    (∃ q ∈ B, q.2 < minHeight n A) ∨
    ∃ p ∈ A, ∃ q ∈ B, refinedArea p.1 q.1 p.2 q.2
      (endpointBound p.1 p.2 (minHeight n B))
      (endpointBound q.1 q.2 (minHeight n A))
      (minHeight n B) (minHeight n A) < n))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_FiniteDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Diagrams. -/

section

namespace UniversalTensorSquare

def diagramOfCols (rs : List ℕ) (hs : rs.SortedGE) : YoungDiagram :=
  (YoungDiagram.ofRowLens rs hs).transpose

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ConstrainedDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constrained Diagrams. -/

section

namespace UniversalTensorSquare

def firstBound (n : ℕ) (B : List (ℕ × ℕ)) : ℕ :=
  B.foldr (fun p h => if 0 < p.1 then min p.2 h else h) n

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_EightSplitCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eight Split Certificate. -/

section

namespace UniversalTensorSquare

def eightPlaceB10 : Equiv.Perm (Fin 8) := Equiv.swap 0 3 * (Equiv.swap 1 7 * (Equiv.swap 3 6 * (Equiv.swap 1 4 * (Equiv.swap 0 5))))

def eightPlaceT10 : Equiv.Perm (Fin 8) := Equiv.swap 2 5 * (Equiv.swap 2 4 * (Equiv.swap 1 6 * (Equiv.swap 0 7)))

def eightFlag10 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,2,1),(0,3,3),(1,0,0),(1,1,0),(2,1,1),(3,0,2)] : List (ℕ × ℕ × ℕ)) then 1 else 0

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeEight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Eight. -/

section

namespace UniversalTensorSquare

def eightWitness : YoungDiagram := diagramOfCols [4,2,1,1] (by decide)

def eightPlaceB0 : Equiv.Perm (Fin 8) := Equiv.swap 5 4 * (Equiv.swap 4 7 * (Equiv.swap 1 6 * (Equiv.swap 1 3 * (Equiv.swap 0 2))))

def eightPlaceT0 : Equiv.Perm (Fin 8) := Equiv.swap 0 7 * (Equiv.swap 0 1 * (Equiv.swap 0 3 * (Equiv.swap 1 5 * (Equiv.swap 0 2))))

def eightFlag0 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,0,2),(0,1,1),(0,1,3),(0,2,1),(0,3,0)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def eightPlaceB1 : Equiv.Perm (Fin 8) := Equiv.swap 5 3 * (Equiv.swap 5 6 * (Equiv.swap 3 0 * (Equiv.swap 2 4 * (Equiv.swap 0 7 * (Equiv.swap 0 1)))))

def eightPlaceT1 : Equiv.Perm (Fin 8) := Equiv.swap 5 6 * (Equiv.swap 2 4 * (Equiv.swap 0 3))

def eightFlag1 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,1),(0,3,3),(1,2,2)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def eightPlaceB2 : Equiv.Perm (Fin 8) := Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 3 5 * (Equiv.swap 2 0 * (Equiv.swap 0 6))))

def eightPlaceT2 : Equiv.Perm (Fin 8) := Equiv.swap 2 5 * (Equiv.swap 5 7 * (Equiv.swap 0 4 * (Equiv.swap 2 1 * (Equiv.swap 1 6 * (Equiv.swap 0 3)))))

def eightFlag2 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,1),(0,1,0),(0,2,3),(0,3,2),(1,0,0)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def eightPlaceB3 : Equiv.Perm (Fin 8) := Equiv.swap 6 1 * (Equiv.swap 3 0 * (Equiv.swap 1 7 * (Equiv.swap 1 2 * (Equiv.swap 0 5))))

def eightPlaceT3 : Equiv.Perm (Fin 8) := Equiv.swap 1 7 * (Equiv.swap 1 6 * (Equiv.swap 1 0 * (Equiv.swap 0 5)))

def eightFlag3 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,1),(0,2,3),(0,3,1),(1,1,0),(2,0,2)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def eightPlaceB4 : Equiv.Perm (Fin 8) := Equiv.swap 4 1 * (Equiv.swap 4 6 * (Equiv.swap 4 5 * (Equiv.swap 1 0 * (Equiv.swap 0 7 * (Equiv.swap 1 3 * (Equiv.swap 0 2))))))

def eightPlaceT4 : Equiv.Perm (Fin 8) := Equiv.swap 1 0 * (Equiv.swap 1 3 * (Equiv.swap 1 5 * (Equiv.swap 3 6 * (Equiv.swap 1 4 * (Equiv.swap 1 2 * (Equiv.swap 0 7))))))

def eightFlag4 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,1),(0,1,3),(1,0,1),(1,2,0),(1,3,2)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def eightPlaceB5 : Equiv.Perm (Fin 8) := Equiv.swap 5 4 * (Equiv.swap 4 0 * (Equiv.swap 3 6 * (Equiv.swap 0 7 * (Equiv.swap 0 2))))

def eightPlaceT5 : Equiv.Perm (Fin 8) := Equiv.swap 6 1 * (Equiv.swap 1 3 * (Equiv.swap 3 2 * (Equiv.swap 2 7 * (Equiv.swap 1 5 * (Equiv.swap 0 4)))))

def eightFlag5 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,2,3),(0,3,2),(1,0,1),(1,1,0),(2,1,1)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def eightPlaceB6 : Equiv.Perm (Fin 8) := Equiv.swap 1 6 * (Equiv.swap 3 0 * (Equiv.swap 3 4 * (Equiv.swap 1 5 * (Equiv.swap 0 7))))

def eightPlaceT6 : Equiv.Perm (Fin 8) := Equiv.swap 3 6 * (Equiv.swap 3 5 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 4))))

def eightFlag6 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,1),(1,0,3),(2,2,0),(3,3,2)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def eightPlaceB7 : Equiv.Perm (Fin 8) := Equiv.swap 6 3 * (Equiv.swap 3 0 * (Equiv.swap 0 7 * (Equiv.swap 0 2)))

def eightPlaceT7 : Equiv.Perm (Fin 8) := Equiv.swap 6 4 * (Equiv.swap 4 3 * (Equiv.swap 4 5 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 0 7 * (Equiv.swap 0 1))))))

def eightFlag7 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,3,3),(1,0,2),(1,1,1),(1,2,0)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def eightPlaceB8 : Equiv.Perm (Fin 8) := Equiv.swap 0 4 * (Equiv.swap 4 1 * (Equiv.swap 1 7 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 6)))))

def eightPlaceT8 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 3 * (Equiv.swap 3 5 * (Equiv.swap 1 6 * (Equiv.swap 1 0 * (Equiv.swap 0 2)))))

def eightFlag8 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,1),(1,0,3),(1,2,0),(1,3,1),(2,1,2)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def eightPlaceB9 : Equiv.Perm (Fin 8) := Equiv.swap 5 0 * (Equiv.swap 0 7 * (Equiv.swap 2 6 * (Equiv.swap 0 4 * (Equiv.swap 0 1))))

def eightPlaceT9 : Equiv.Perm (Fin 8) := Equiv.swap 5 1 * (Equiv.swap 2 3 * (Equiv.swap 1 0 * (Equiv.swap 0 6)))

def eightFlag9 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,1),(0,2,0),(0,3,2),(1,1,0),(2,0,0),(2,0,3)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def eightPlaceB11 : Equiv.Perm (Fin 8) := Equiv.swap 2 7 * (Equiv.swap 2 4 * (Equiv.swap 4 3 * (Equiv.swap 3 6 * (Equiv.swap 2 5))))

def eightPlaceT11 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 1 * (Equiv.swap 1 2 * (Equiv.swap 2 5 * (Equiv.swap 1 3))))

def eightFlag11 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,1,0),(0,2,3),(1,0,0),(1,3,2),(2,0,1)] : List (ℕ × ℕ × ℕ)) then 1 else 0

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeFive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Five. -/

section

namespace UniversalTensorSquare

def fiveWitness : YoungDiagram := diagramOfCols [3,1,1] (by decide)

def hookPlacement : Equiv.Perm (Fin 5) := Equiv.swap 1 3 * Equiv.swap 2 4

def flag5 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(1,1,0),(2,2,0),(3,0,1),(4,0,2)] : List (ℕ × ℕ × ℕ))
  then 1 else 0

def flag41 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(1,1,1),(2,2,0),(3,0,2)] : List (ℕ × ℕ × ℕ))
  then 1 else 0

def flag32 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,2),(0,1,1),(1,0,0),(2,2,0)] : List (ℕ × ℕ × ℕ))
  then 1 else 0

def flag311 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,1),(1,2,0),(2,0,2)] : List (ℕ × ℕ × ℕ))
  then 1 else 0

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 116. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows116_0 : List ℕ := [12,11,11,11,11,11,5,5,5,4,4,4,4,4,3,3,3,3,2]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 118. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows118_0 : List ℕ := [12,11,11,11,11,10,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

def degreeQs118 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 14. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows14_0 : List ℕ := [3,3,2,2,2,2]

def degreeQs14 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 16. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows16_0 : List ℕ := [4,3,3,3,3]

def degreeQs16 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 18. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows18_0 : List ℕ := [4,3,3,3,3,2]

def degreeQs18 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 19. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows19_0 : List ℕ := [3,3,3,3,3,2,2]

def degreeQs19 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 20. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows20_0 : List ℕ := [6,4,4,3,3]

def degreeQs20 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 22. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows22_0 : List ℕ := [5,4,4,3,3,3]

def degreeQs22 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 24. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows24_0 : List ℕ := [8,4,4,4,4]

def degreeQs24 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 26. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows26_0 : List ℕ := [6,5,4,4,4,3]

def degreeQs26 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 31. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows31_0 : List ℕ := [5,5,5,4,4,4,4]

def degreeRows31_1 : List ℕ := [6,5,5,4,4,2,2,2,1]

def degreeQs31 : List (List ℕ) := [degreeRows31_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 35. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows35_0 : List ℕ := [6,5,5,5,5,5,4]

def degreeRows35_1 : List ℕ := [8,5,5,5,5,2,2,2,1]

def degreeQs35 : List (List ℕ) := [degreeRows35_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 37. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows37_0 : List ℕ := [6,5,5,5,5,4,2,2,2,1]

def degreeQs37 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 39. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows39_0 : List ℕ := [7,6,6,6,5,5,4]

def degreeRows39_1 : List ℕ := [10,6,6,5,5,2,2,2,1]

def degreeQs39 : List (List ℕ) := [degreeRows39_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 41. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows41_0 : List ℕ := [7,6,6,5,5,5,2,2,2,1]

def degreeQs41 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 43. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows43_0 : List ℕ := [8,7,6,6,6,6,4]

def degreeRows43_1 : List ℕ := [12,6,6,6,6,2,2,2,1]

def degreeQs43 : List (List ℕ) := [degreeRows43_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 58. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows58_0 : List ℕ := [8,7,7,7,7,7,4,3,3,3,2]

def degreeRows58_1 : List ℕ := [12,7,7,7,7,3,3,3,2,2,2,2,1]

def degreeQs58 : List (List ℕ) := [degreeRows58_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 62. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows62_0 : List ℕ := [9,8,8,8,7,7,4,3,3,3,2]

def degreeRows62_1 : List ℕ := [14,8,8,7,7,3,3,3,2,2,2,2,1]

def degreeQs62 : List (List ℕ) := [degreeRows62_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 64. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows64_0 : List ℕ := [9,8,8,7,7,7,3,3,3,2,2,2,2,1]

def degreeQs64 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 89. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows89_0 : List ℕ := [11,10,10,10,9,9,4,4,4,4,3,3,3,3,2]

def degreeRows89_1 : List ℕ := [18,10,10,9,9,4,4,4,3,3,3,3,2,2,2,2,1]

def degreeQs89 : List (List ℕ) := [degreeRows89_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeSeven
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Seven. -/

section

namespace UniversalTensorSquare

def sevenWitness : YoungDiagram := diagramOfCols [4,1,1,1] (by decide)

def sevenPlaceB0 : Equiv.Perm (Fin 7) := Equiv.swap 5 6 * (Equiv.swap 2 1 * (Equiv.swap 2 3 * (Equiv.swap 1 4)))

def sevenPlaceT0 : Equiv.Perm (Fin 7) := Equiv.swap 1 2 * (Equiv.swap 2 6 * (Equiv.swap 1 0 * (Equiv.swap 0 4)))

def sevenFlag0 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,3),(0,2,2),(0,3,1)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def sevenPlaceB1 : Equiv.Perm (Fin 7) := Equiv.swap 4 1 * (Equiv.swap 1 5 * (Equiv.swap 1 0 * (Equiv.swap 0 2)))

def sevenPlaceT1 : Equiv.Perm (Fin 7) := Equiv.swap 3 6 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 0 5))))

def sevenFlag1 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,0,2),(0,2,3),(0,3,0),(1,1,1)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def sevenPlaceB2 : Equiv.Perm (Fin 7) := Equiv.swap 4 2 * (Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 0 5)))

def sevenPlaceT2 : Equiv.Perm (Fin 7) := Equiv.swap 4 2 * (Equiv.swap 2 5 * (Equiv.swap 2 3 * (Equiv.swap 0 1)))

def sevenFlag2 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,2),(1,2,1),(1,3,3)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def sevenPlaceB3 : Equiv.Perm (Fin 7) := Equiv.swap 3 6 * (Equiv.swap 3 5 * (Equiv.swap 3 4 * (Equiv.swap 1 2)))

def sevenPlaceT3 : Equiv.Perm (Fin 7) := Equiv.swap 2 6 * (Equiv.swap 2 3 * (Equiv.swap 3 0 * (Equiv.swap 2 4 * (Equiv.swap 0 5))))

def sevenFlag3 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,0,3),(0,2,3),(0,3,1),(1,0,2),(2,1,0)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def sevenPlaceB4 : Equiv.Perm (Fin 7) := Equiv.swap 2 0 * (Equiv.swap 2 1 * (Equiv.swap 2 3 * (Equiv.swap 1 5 * (Equiv.swap 0 6))))

def sevenPlaceT4 : Equiv.Perm (Fin 7) := Equiv.swap 4 5 * (Equiv.swap 3 6 * (Equiv.swap 0 2 * (Equiv.swap 0 1)))

def sevenFlag4 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,1),(0,1,2),(0,2,0),(0,3,3),(1,0,0)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def sevenPlaceB5 : Equiv.Perm (Fin 7) := Equiv.swap 2 6 * (Equiv.swap 2 5 * (Equiv.swap 1 4 * (Equiv.swap 0 3)))

def sevenPlaceT5 : Equiv.Perm (Fin 7) := Equiv.swap 4 0 * (Equiv.swap 1 2 * (Equiv.swap 0 5))

def sevenFlag5 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,2,2),(0,3,1),(1,1,3),(1,3,0),(2,0,1)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def sevenPlaceB6 : Equiv.Perm (Fin 7) := Equiv.swap 5 3 * (Equiv.swap 3 6 * (Equiv.swap 3 0 * (Equiv.swap 0 4 * (Equiv.swap 0 2))))

def sevenPlaceT6 : Equiv.Perm (Fin 7) := Equiv.swap 2 4 * (Equiv.swap 2 3 * (Equiv.swap 0 5))

def sevenFlag6 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,0,2),(0,1,1),(1,0,2),(2,3,0),(3,2,3)] : List (ℕ × ℕ × ℕ)) then 1 else 0

def sevenPlaceB7 : Equiv.Perm (Fin 7) := Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 2 6 * (Equiv.swap 0 5)))

def sevenPlaceT7 : Equiv.Perm (Fin 7) := Equiv.swap 4 6 * (Equiv.swap 1 5 * (Equiv.swap 1 3 * (Equiv.swap 1 0 * (Equiv.swap 0 2))))

def sevenFlag7 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,0,2),(0,0,3),(1,0,3),(1,2,1),(1,3,2),(2,1,0)] : List (ℕ × ℕ × ℕ)) then 1 else 0

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 112. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows112_0 : List ℕ := [11,11,11,10,10,10,5,5,5,4,4,4,4,4,3,3,3,3,2]

def degreeRows112_1 : List ℕ := [18,11,11,10,10,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

def degreeQs112 : List (List ℕ) := [degreeRows112_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 12. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows12_0 : List ℕ := [3,3,2,2,2]

def degreeRows12_1 : List ℕ := [5,2,2,1,1,1]

def degreeQs12 : List (List ℕ) := [degreeRows12_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 151. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows151_0 : List ℕ := [14,13,13,13,13,13,6,6,6,5,5,5,5,4,4,4,4,4,3,3,3,3,2]

def degreeRows151_1 : List ℕ := [24,13,13,13,13,6,6,6,5,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

def degreeQs151 : List (List ℕ) := [degreeRows151_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 17. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows17_0 : List ℕ := [3,3,3,3,2,1,1,1]

def degreeQs17 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 23. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows23_0 : List ℕ := [4,4,3,3,2,2,2,2,1]

def degreeRows23_1 : List ℕ := [7,3,2,2,2,2,2,1,1,1]

def degreeQs23 : List (List ℕ) := [degreeRows23_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 25. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows25_0 : List ℕ := [4,3,3,3,3,2,2,2,2,1]

def degreeQs25 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 27. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows27_0 : List ℕ := [4,4,4,4,4,2,2,2,1]

def degreeQs27 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 29. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows29_0 : List ℕ := [4,4,4,4,3,3,2,2,2,1]

def degreeQs29 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 30. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows30_0 : List ℕ := [4,4,4,4,3,2,2,2,2,1,1,1]

def degreeQs30 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 32. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows32_0 : List ℕ := [4,4,4,3,3,3,3,2,2,2,2]

def degreeQs32 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 33. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows33_0 : List ℕ := [5,5,4,4,4,4,2,2,2,1]

def degreeQs33 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 34. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows34_0 : List ℕ := [5,5,4,4,4,3,3,2,2,2]

def degreeQs34 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 38. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows38_0 : List ℕ := [5,5,4,4,3,3,3,2,2,2,2,2,1]

def degreeRows38_1 : List ℕ := [9,4,3,3,3,3,2,2,2,2,2,1,1,1]

def degreeQs38 : List (List ℕ) := [degreeRows38_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 40. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows40_0 : List ℕ := [5,4,4,4,3,3,3,3,2,2,2,2,2,1]

def degreeQs40 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 42. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows42_0 : List ℕ := [5,5,5,5,4,3,3,3,2,2,2,2,1]

def degreeQs42 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 44. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows44_0 : List ℕ := [5,5,5,4,4,3,3,3,3,2,2,2,2,1]

def degreeQs44 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 46. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows46_0 : List ℕ := [6,6,5,5,5,4,4,3,3,3,2]

def degreeRows46_1 : List ℕ := [6,6,6,5,5,3,3,3,2,2,2,2,1]

def degreeQs46 : List (List ℕ) := [degreeRows46_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 47. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows47_0 : List ℕ := [5,5,5,5,4,3,3,3,3,2,2,2,2,1,1,1]

def degreeQs47 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 48. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows48_0 : List ℕ := [6,5,5,5,5,4,3,3,3,2,2,2,2,1]

def degreeQs48 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 49. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows49_0 : List ℕ := [5,5,5,4,4,3,3,3,3,3,3,2,2,2,2]

def degreeQs49 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 50. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows50_0 : List ℕ := [6,6,6,6,6,5,4,3,3,3,2]

def degreeRows50_1 : List ℕ := [8,6,6,6,6,3,3,3,2,2,2,2,1]

def degreeQs50 : List (List ℕ) := [degreeRows50_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 51. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows51_0 : List ℕ := [6,6,5,5,4,4,3,3,3,3,3,2,2,2]

def degreeQs51 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 52. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows52_0 : List ℕ := [6,6,6,6,5,5,3,3,3,2,2,2,2,1]

def degreeQs52 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 53. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows53_0 : List ℕ := [6,5,5,5,4,4,3,3,3,3,3,3,2,2,2]

def degreeQs53 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 54. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows54_0 : List ℕ := [7,7,7,6,6,6,4,3,3,3,2]

def degreeRows54_1 : List ℕ := [10,7,7,6,6,3,3,3,2,2,2,2,1]

def degreeQs54 : List (List ℕ) := [degreeRows54_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 56. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows56_0 : List ℕ := [7,7,6,6,6,6,3,3,3,2,2,2,2,1]

def degreeQs56 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 57. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows57_0 : List ℕ := [6,6,5,5,4,4,4,3,3,3,3,2,2,2,2,2,1]

def degreeRows57_1 : List ℕ := [11,5,4,4,4,4,3,3,3,3,2,2,2,2,2,1,1,1]

def degreeQs57 : List (List ℕ) := [degreeRows57_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 59. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows59_0 : List ℕ := [6,5,5,5,4,4,4,3,3,3,3,3,2,2,2,2,2,1]

def degreeQs59 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 60. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows60_0 : List ℕ := [8,7,7,7,7,6,3,3,3,2,2,2,2,1]

def degreeQs60 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 61. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows61_0 : List ℕ := [6,6,6,6,4,4,4,4,3,3,3,3,2,2,2,2,1]

def degreeQs61 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 63. -/

section

noncomputable section
namespace UniversalTensorSquare
def degreeRows63_0 : List ℕ := [6,6,6,5,4,4,4,4,3,3,3,3,3,2,2,2,2,1]

def degreeQs63 : List (List ℕ) := []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 1. -/

section

noncomputable section
namespace UniversalTensorSquare

def sgB10 : Equiv.Perm (Fin 4) := Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 3))
def sgT10 : Equiv.Perm (Fin 4) := Equiv.swap 1 3 * (Equiv.swap 1 0 * (Equiv.swap 0 2))
def sgFlag10 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(0,1,0)}

def sgB17 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * (Equiv.swap 0 1)
def sgFlag17 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,0,1),(1,1,0)}

def sgB67 : Equiv.Perm (Fin 6) := Equiv.swap 1 2 * (Equiv.swap 1 0 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 4))))
def sgFlag67 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(3,0,1),(1,0,2),(0,1,0),(1,2,0)}

def sgB68 : Equiv.Perm (Fin 6) := Equiv.swap 2 5 * (Equiv.swap 0 1)
def sgFlag68 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(2,0,2),(2,1,0),(0,2,0)}

def sgB71 : Equiv.Perm (Fin 6) := Equiv.swap 1 5 * (Equiv.swap 1 4 * (Equiv.swap 0 3))
def sgFlag71 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,0,1),(1,1,0),(0,2,2)}

def sgB88 : Equiv.Perm (Fin 6) := Equiv.swap 2 0 * (Equiv.swap 1 5 * (Equiv.swap 0 3))
def sgFlag88 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(1,0,1),(3,0,2),(1,1,0),(0,2,0)}

def sgB89 : Equiv.Perm (Fin 6) := Equiv.swap 2 1 * (Equiv.swap 2 4 * (Equiv.swap 1 5))
def sgFlag89 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(0,0,1),(1,0,2),(0,1,0),(1,2,0)}

def sgB92 : Equiv.Perm (Fin 6) := Equiv.swap 4 2 * (Equiv.swap 2 0 * (Equiv.swap 2 1 * (Equiv.swap 1 3 * (Equiv.swap 0 5))))
def sgFlag92 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,0,2),(1,1,0),(1,2,1)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB143 : Equiv.Perm (Fin 7) := Equiv.swap 0 6 * (Equiv.swap 3 2 * (Equiv.swap 2 5 * (Equiv.swap 0 4)))
def sgT143 : Equiv.Perm (Fin 7) := Equiv.swap 1 5 * (Equiv.swap 1 3 * (Equiv.swap 1 2))
def sgFlag143 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(0,0,2),(4,1,0),(2,1,1),(3,2,0)}

def sgB144 : Equiv.Perm (Fin 7) := Equiv.swap 5 1 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 1 6 * (Equiv.swap 0 4))))
def sgT144 : Equiv.Perm (Fin 7) := Equiv.swap 0 5 * (Equiv.swap 1 6 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 4))))
def sgFlag144 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(2,0,2),(1,1,0),(2,1,0),(3,2,0)}

def sgB154 : Equiv.Perm (Fin 7) := Equiv.swap 4 5 * (Equiv.swap 0 2 * (Equiv.swap 2 6 * (Equiv.swap 0 3)))
def sgT154 : Equiv.Perm (Fin 7) := Equiv.swap 1 2 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 5)))
def sgFlag154 : Finset (ℕ × ℕ × ℕ) := {(5,0,0),(1,0,1),(3,0,2),(0,1,0),(2,1,0),(4,1,1),(0,2,1)}

def sgB155 : Equiv.Perm (Fin 7) := Equiv.swap 3 2 * (Equiv.swap 2 6 * (Equiv.swap 0 4 * (Equiv.swap 0 1)))
def sgT155 : Equiv.Perm (Fin 7) := Equiv.swap 4 2 * (Equiv.swap 2 5 * (Equiv.swap 2 0 * (Equiv.swap 0 3)))
def sgFlag155 : Finset (ℕ × ℕ × ℕ) := {(4,0,0),(3,0,1),(0,0,2),(1,1,0),(2,1,0),(1,1,1),(0,2,1)}

def sgB156 : Equiv.Perm (Fin 7) := Equiv.swap 4 0 * (Equiv.swap 4 1 * (Equiv.swap 1 5 * (Equiv.swap 0 6)))
def sgT156 : Equiv.Perm (Fin 7) := Equiv.swap 3 1 * (Equiv.swap 1 4)
def sgFlag156 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(0,1,0),(2,1,1),(3,1,1),(2,2,2)}

def sgB157 : Equiv.Perm (Fin 7) := Equiv.swap 2 6 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 2 3 * (Equiv.swap 0 5))))
def sgFlag157 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(0,1,0),(4,1,1),(2,1,2),(3,2,0)}

def sgB158 : Equiv.Perm (Fin 7) := Equiv.swap 5 4 * (Equiv.swap 4 3 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 0 6 * (Equiv.swap 0 1)))))
def sgT158 : Equiv.Perm (Fin 7) := Equiv.swap 3 5 * (Equiv.swap 1 6 * (Equiv.swap 1 2))
def sgFlag158 : Finset (ℕ × ℕ × ℕ) := {(0,0,1),(3,0,1),(1,0,2),(0,1,0),(1,1,0),(2,1,1),(0,2,0)}

def sgB160 : Equiv.Perm (Fin 7) := Equiv.swap 4 6 * (Equiv.swap 2 3 * (Equiv.swap 1 5))
def sgFlag160 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(1,0,2),(1,1,0),(0,1,1),(0,2,0)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB163 : Equiv.Perm (Fin 7) := Equiv.swap 2 1 * (Equiv.swap 1 6 * (Equiv.swap 0 5))
def sgFlag163 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,1,1),(1,1,2),(1,2,1)}

def sgB165 : Equiv.Perm (Fin 7) := Equiv.swap 3 6 * (Equiv.swap 2 5 * (Equiv.swap 1 4))
def sgFlag165 : Finset (ℕ × ℕ × ℕ) := {(4,0,0),(3,0,1),(5,0,2),(1,1,0),(0,1,1),(2,1,1),(0,2,0)}

def sgB166 : Equiv.Perm (Fin 7) := Equiv.swap 5 4 * (Equiv.swap 4 6 * (Equiv.swap 2 0 * (Equiv.swap 0 3 * (Equiv.swap 0 1))))
def sgFlag166 : Finset (ℕ × ℕ × ℕ) := {(1,0,1),(4,0,2),(0,1,0),(3,1,1),(2,2,0)}

def sgB167 : Equiv.Perm (Fin 7) := Equiv.swap 3 1 * (Equiv.swap 1 6 * (Equiv.swap 0 2))
def sgFlag167 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,1),(3,0,2),(2,1,0),(1,1,1),(0,2,0)}

def sgB168 : Equiv.Perm (Fin 7) := Equiv.swap 1 0 * (Equiv.swap 1 4 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 5))))
def sgFlag168 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(3,0,1),(0,1,0),(1,1,1),(4,1,2),(2,2,0)}

def sgB169 : Equiv.Perm (Fin 7) := Equiv.swap 2 1 * (Equiv.swap 1 6 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 4))))
def sgFlag169 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(0,1,0),(2,1,1),(0,1,2),(3,2,0)}

def sgB171 : Equiv.Perm (Fin 7) := Equiv.swap 4 2 * (Equiv.swap 4 0 * (Equiv.swap 2 1 * (Equiv.swap 1 6 * (Equiv.swap 0 5))))
def sgFlag171 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(0,0,2),(0,1,0),(1,1,1),(0,2,1)}

def sgB174 : Equiv.Perm (Fin 7) := Equiv.swap 1 4 * (Equiv.swap 4 6 * (Equiv.swap 1 5 * (Equiv.swap 1 2)))
def sgFlag174 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(1,1,1),(1,1,2),(0,2,0)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB194 : Equiv.Perm (Fin 7) := Equiv.swap 1 3 * (Equiv.swap 3 5 * (Equiv.swap 2 6 * (Equiv.swap 1 4)))
def sgFlag194 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,1),(0,0,2),(0,1,0),(4,1,1),(2,2,0)}

def sgB195 : Equiv.Perm (Fin 7) := Equiv.swap 2 1 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 1 6 * (Equiv.swap 0 5))))
def sgFlag195 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(3,0,1),(1,0,2),(0,1,0),(2,1,0),(2,2,1)}

def sgB271 : Equiv.Perm (Fin 8) := Equiv.swap 5 4 * (Equiv.swap 4 7 * (Equiv.swap 2 6 * (Equiv.swap 0 1)))
def sgFlag271 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(0,0,1),(1,0,1),(2,0,2),(0,1,0),(2,1,0),(1,2,0)}

def sgB275 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 1 * (Equiv.swap 1 6 * (Equiv.swap 1 3 * (Equiv.swap 1 0 * (Equiv.swap 0 2)))))
def sgFlag275 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(2,0,1),(1,0,2),(0,1,0),(0,1,1),(0,2,0)}

def sgB285 : Equiv.Perm (Fin 8) := Equiv.swap 1 2 * (Equiv.swap 1 4 * (Equiv.swap 2 5 * (Equiv.swap 1 0 * (Equiv.swap 0 3))))
def sgFlag285 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(4,1,0),(3,1,1),(2,1,2),(5,2,0)}

def sgB286 : Equiv.Perm (Fin 8) := Equiv.swap 4 5 * (Equiv.swap 1 6 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 7))))
def sgFlag286 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(0,0,1),(4,1,0),(1,1,1),(2,1,2),(3,2,0)}

def sgB287 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 2 0 * (Equiv.swap 1 6 * (Equiv.swap 0 3)))
def sgFlag287 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,0,2),(3,1,0),(0,1,1),(2,1,1),(3,2,0)}

def sgB295 : Equiv.Perm (Fin 8) := Equiv.swap 4 6 * (Equiv.swap 2 7 * (Equiv.swap 0 3))
def sgFlag295 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,0,2),(3,1,0),(4,1,1),(0,2,0),(5,2,2)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB296 : Equiv.Perm (Fin 8) := Equiv.swap 4 0 * (Equiv.swap 3 1 * (Equiv.swap 0 7 * (Equiv.swap 1 5 * (Equiv.swap 0 2))))
def sgFlag296 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(1,0,1),(4,0,1),(2,0,2),(1,1,0),(3,1,2),(0,2,0)}

def sgB297 : Equiv.Perm (Fin 8) := Equiv.swap 1 6 * (Equiv.swap 0 4 * (Equiv.swap 0 3 * (Equiv.swap 1 5 * (Equiv.swap 0 2))))
def sgFlag297 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,1),(3,0,2),(0,1,0),(1,1,2),(1,2,0),(3,2,0)}

def sgB300 : Equiv.Perm (Fin 8) := Equiv.swap 1 0 * (Equiv.swap 0 6 * (Equiv.swap 1 4 * (Equiv.swap 0 2)))
def sgFlag300 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,0,2),(3,1,0),(1,1,1),(0,2,0),(0,2,2)}

def sgB301 : Equiv.Perm (Fin 8) := Equiv.swap 1 3 * (Equiv.swap 3 6 * (Equiv.swap 1 5 * (Equiv.swap 1 2)))
def sgFlag301 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(0,0,1),(1,1,1),(1,1,2),(1,2,0),(0,2,2)}

def sgB309 : Equiv.Perm (Fin 8) := Equiv.swap 4 2 * (Equiv.swap 4 3 * (Equiv.swap 4 0 * (Equiv.swap 3 6 * (Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 0 5))))))
def sgFlag309 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(1,0,2),(2,1,0),(0,1,1),(2,2,0),(4,2,1)}

def sgB310 : Equiv.Perm (Fin 8) := Equiv.swap 2 7 * (Equiv.swap 2 5 * (Equiv.swap 3 1 * (Equiv.swap 2 4 * (Equiv.swap 1 0 * (Equiv.swap 0 6)))))
def sgFlag310 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(2,1,0),(3,1,2),(0,2,1),(2,2,1)}

def sgB311 : Equiv.Perm (Fin 8) := Equiv.swap 1 0 * (Equiv.swap 0 2 * (Equiv.swap 3 7 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 0 4)))))
def sgFlag311 : Finset (ℕ × ℕ × ℕ) := {(0,0,1),(1,1,0),(0,1,2),(1,1,2),(1,2,0)}

def sgB313 : Equiv.Perm (Fin 8) := Equiv.swap 5 2 * (Equiv.swap 2 3 * (Equiv.swap 3 0 * (Equiv.swap 2 4 * (Equiv.swap 0 6 * (Equiv.swap 0 1)))))
def sgFlag313 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(5,0,2),(4,0,3),(3,1,0),(1,2,0),(2,3,0)}

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 2. -/

section

noncomputable section
namespace UniversalTensorSquare

def sgB314 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 2 * (Equiv.swap 2 6 * (Equiv.swap 2 0 * (Equiv.swap 1 5 * (Equiv.swap 0 3)))))
def sgFlag314 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,1),(2,0,2),(0,0,3),(2,1,0),(0,2,0),(4,3,0)}

def sgB315 : Equiv.Perm (Fin 8) := Equiv.swap 5 2 * (Equiv.swap 5 6 * (Equiv.swap 2 1 * (Equiv.swap 2 4 * (Equiv.swap 1 7 * (Equiv.swap 0 3)))))
def sgFlag315 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(1,0,1),(0,0,2),(2,0,3),(1,1,0),(0,2,0),(2,3,0)}

def sgB319 : Equiv.Perm (Fin 8) := Equiv.swap 1 4 * (Equiv.swap 1 0 * (Equiv.swap 4 3 * (Equiv.swap 3 7 * (Equiv.swap 1 5 * (Equiv.swap 1 2 * (Equiv.swap 0 6))))))
def sgFlag319 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,0),(0,0,1),(1,0,3),(1,1,2),(0,2,0),(3,3,0)}

def sgB320 : Equiv.Perm (Fin 8) := Equiv.swap 5 0 * (Equiv.swap 3 7 * (Equiv.swap 2 4 * (Equiv.swap 0 6)))
def sgFlag320 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,2),(0,0,3),(0,1,1),(2,2,0),(0,3,0)}

def sgB324 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 2 * (Equiv.swap 2 1 * (Equiv.swap 1 5 * (Equiv.swap 0 6))))
def sgFlag324 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,0,2),(1,1,0),(0,2,1),(1,3,3)}

def sgB348 : Equiv.Perm (Fin 8) := Equiv.swap 5 3 * (Equiv.swap 5 6 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 0 * (Equiv.swap 0 7)))))
def sgFlag348 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(4,0,1),(2,0,2),(5,1,1),(1,1,2),(0,2,0)}

def sgB349 : Equiv.Perm (Fin 8) := Equiv.swap 2 6 * (Equiv.swap 2 4 * (Equiv.swap 2 3 * (Equiv.swap 1 0 * (Equiv.swap 0 5))))
def sgFlag349 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,1),(0,0,2),(1,0,2),(2,1,0),(0,2,0),(3,2,1)}

def sgB350 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 6 * (Equiv.swap 2 3 * (Equiv.swap 0 1)))
def sgFlag350 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(1,0,2),(3,1,0),(0,2,0),(0,2,2)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB352 : Equiv.Perm (Fin 8) := Equiv.swap 4 0 * (Equiv.swap 3 1 * (Equiv.swap 1 5 * (Equiv.swap 1 2 * (Equiv.swap 0 6))))
def sgFlag352 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(1,1,0),(0,1,2),(3,2,0),(2,2,2)}

def sgB353 : Equiv.Perm (Fin 8) := Equiv.swap 3 6 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 5))))
def sgFlag353 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,2),(1,1,0),(0,1,1),(2,2,0),(2,2,1)}

def sgB356 : Equiv.Perm (Fin 8) := Equiv.swap 4 2 * (Equiv.swap 4 5 * (Equiv.swap 0 1 * (Equiv.swap 2 7 * (Equiv.swap 1 6 * (Equiv.swap 0 3)))))
def sgFlag356 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(2,0,2),(0,1,0),(3,1,0),(5,1,1),(4,2,0)}

def sgB357 : Equiv.Perm (Fin 8) := Equiv.swap 1 3 * (Equiv.swap 3 7 * (Equiv.swap 3 2 * (Equiv.swap 2 5 * (Equiv.swap 1 0 * (Equiv.swap 0 6)))))
def sgFlag357 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(1,0,1),(4,0,1),(1,0,2),(2,1,0),(0,1,1),(0,2,0)}

def sgB358 : Equiv.Perm (Fin 8) := Equiv.swap 2 4 * (Equiv.swap 4 6 * (Equiv.swap 2 0 * (Equiv.swap 1 7 * (Equiv.swap 0 5))))
def sgFlag358 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(3,1,0),(0,1,1),(3,1,2),(0,2,0)}

def sgB371 : Equiv.Perm (Fin 8) := Equiv.swap 1 2 * (Equiv.swap 2 7 * (Equiv.swap 2 5 * (Equiv.swap 2 4 * (Equiv.swap 1 6 * (Equiv.swap 0 3)))))
def sgFlag371 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,1),(3,0,2),(0,0,3),(2,1,0),(0,2,0),(5,3,0)}

def sgB372 : Equiv.Perm (Fin 8) := Equiv.swap 5 6 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 0 4 * (Equiv.swap 0 1))))
def sgFlag372 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(0,0,1),(3,0,2),(1,0,3),(4,1,0),(0,2,0),(2,3,0)}

def sgB373 : Equiv.Perm (Fin 8) := Equiv.swap 6 2 * (Equiv.swap 2 7 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 3))))
def sgFlag373 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(3,0,0),(1,0,1),(0,0,2),(2,0,3),(1,1,0),(0,2,0),(3,3,0)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB377 : Equiv.Perm (Fin 8) := Equiv.swap 1 4 * (Equiv.swap 4 2 * (Equiv.swap 4 5 * (Equiv.swap 2 7 * (Equiv.swap 2 3 * (Equiv.swap 1 0 * (Equiv.swap 0 6))))))
def sgFlag377 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,1),(1,0,2),(0,1,0),(1,2,3),(3,3,0)}

def sgB378 : Equiv.Perm (Fin 8) := Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 0 4))))
def sgFlag378 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(2,0,2),(1,1,0),(2,2,0),(1,3,3)}

def sgB383 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 3 * (Equiv.swap 4 0 * (Equiv.swap 3 1 * (Equiv.swap 1 6 * (Equiv.swap 1 2 * (Equiv.swap 0 5))))))
def sgFlag383 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,3),(1,1,2),(1,2,0),(1,3,1)}

def sgB390 : Equiv.Perm (Fin 8) := Equiv.swap 3 1 * (Equiv.swap 4 0 * (Equiv.swap 3 5 * (Equiv.swap 0 6 * (Equiv.swap 1 7 * (Equiv.swap 0 2)))))
def sgFlag390 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,1),(2,0,2),(1,1,0),(2,2,0)}

def sgB394 : Equiv.Perm (Fin 8) := Equiv.swap 5 4 * (Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 0 6 * (Equiv.swap 0 2))))
def sgFlag394 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,1),(3,0,2),(0,1,0),(1,1,1),(1,2,0)}

def sgB480 : Equiv.Perm (Fin 9) := Equiv.swap 3 8 * (Equiv.swap 2 0 * (Equiv.swap 3 5 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))
def sgFlag480 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(5,0,0),(2,0,1),(1,1,0),(4,1,1),(3,1,2),(0,2,1)}

def sgB481 : Equiv.Perm (Fin 9) := Equiv.swap 0 1 * (Equiv.swap 1 7 * (Equiv.swap 1 4 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 6)))))
def sgFlag481 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(0,0,1),(1,1,0),(3,1,1),(1,1,2),(4,2,0)}

def sgB482 : Equiv.Perm (Fin 9) := Equiv.swap 4 2 * (Equiv.swap 4 7 * (Equiv.swap 2 8 * (Equiv.swap 4 6 * (Equiv.swap 2 5 * (Equiv.swap 0 3 * (Equiv.swap 0 1))))))
def sgFlag482 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(0,0,1),(2,0,2),(0,1,0),(4,1,0),(1,1,1),(2,1,1),(1,2,0)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB483 : Equiv.Perm (Fin 9) := Equiv.swap 7 8 * (Equiv.swap 3 5 * (Equiv.swap 3 1 * (Equiv.swap 1 4 * (Equiv.swap 0 2))))
def sgFlag483 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(2,0,1),(1,0,2),(1,1,0),(0,1,1),(3,1,1),(4,2,0)}

def sgB484 : Equiv.Perm (Fin 9) := Equiv.swap 6 5 * (Equiv.swap 6 2 * (Equiv.swap 5 8 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 0 7 * (Equiv.swap 0 1))))))
def sgFlag484 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,1,0),(1,1,1),(0,1,2),(2,2,1)}

def sgB487 : Equiv.Perm (Fin 9) := Equiv.swap 2 5 * (Equiv.swap 5 8 * (Equiv.swap 1 4 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 6)))))
def sgFlag487 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(0,0,1),(1,1,0),(1,1,1),(2,1,2),(0,2,0)}

def sgB489 : Equiv.Perm (Fin 9) := Equiv.swap 7 0 * (Equiv.swap 0 4 * (Equiv.swap 0 6 * (Equiv.swap 4 3 * (Equiv.swap 3 2 * (Equiv.swap 2 8 * (Equiv.swap 0 5))))))
def sgFlag489 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(3,0,1),(0,0,2),(5,1,0),(1,1,1),(2,2,0)}

def sgB490 : Equiv.Perm (Fin 9) := Equiv.swap 2 8 * (Equiv.swap 0 1 * (Equiv.swap 3 5 * (Equiv.swap 2 7 * (Equiv.swap 1 6 * (Equiv.swap 0 4)))))
def sgFlag490 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(1,0,1),(2,0,2),(3,1,0),(3,1,1),(0,2,0)}

def sgB495 : Equiv.Perm (Fin 9) := Equiv.swap 2 0 * (Equiv.swap 3 5 * (Equiv.swap 2 7 * (Equiv.swap 1 4 * (Equiv.swap 0 8))))
def sgFlag495 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(2,0,2),(0,1,1),(1,1,1),(0,2,0)}

def sgB496 : Equiv.Perm (Fin 9) := Equiv.swap 2 5 * (Equiv.swap 5 8 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))
def sgFlag496 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,0),(0,0,2),(2,1,1),(1,2,0)}

def sgB511 : Equiv.Perm (Fin 9) := Equiv.swap 3 6 * (Equiv.swap 6 2 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 2 8 * (Equiv.swap 1 5)))))
def sgFlag511 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(2,0,1),(6,0,2),(5,1,0),(0,1,1),(1,1,2),(0,2,0),(4,2,1)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB513 : Equiv.Perm (Fin 9) := Equiv.swap 1 8 * (Equiv.swap 1 6 * (Equiv.swap 4 7 * (Equiv.swap 1 5 * (Equiv.swap 1 0 * (Equiv.swap 0 2)))))
def sgFlag513 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,1),(0,0,2),(4,1,0),(0,1,1),(2,2,0),(1,2,2)}

def sgB535 : Equiv.Perm (Fin 9) := Equiv.swap 6 5 * (Equiv.swap 5 1 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 1 8 * (Equiv.swap 0 2)))))
def sgFlag535 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(0,0,1),(6,0,2),(2,0,3),(4,1,0),(5,1,1),(0,2,0),(1,3,0)}

def sgB536 : Equiv.Perm (Fin 9) := Equiv.swap 6 3 * (Equiv.swap 0 8 * (Equiv.swap 0 5 * (Equiv.swap 3 1 * (Equiv.swap 0 4 * (Equiv.swap 1 7 * (Equiv.swap 0 2))))))
def sgFlag536 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(2,0,2),(4,0,3),(0,1,0),(5,1,0),(3,2,0),(2,3,1)}

def sgB537 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 2 7 * (Equiv.swap 2 0 * (Equiv.swap 2 5 * (Equiv.swap 2 4 * (Equiv.swap 1 8 * (Equiv.swap 0 6))))))
def sgFlag537 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(1,0,1),(4,0,1),(1,0,2),(0,1,0),(3,1,0),(0,2,0),(3,3,3)}

def sgB541 : Equiv.Perm (Fin 9) := Equiv.swap 2 5 * (Equiv.swap 2 7 * (Equiv.swap 5 0 * (Equiv.swap 2 6 * (Equiv.swap 2 4 * (Equiv.swap 1 3 * (Equiv.swap 0 8))))))
def sgFlag541 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(3,0,2),(0,1,0),(0,1,3),(2,2,0),(4,3,1)}

def sgB548 : Equiv.Perm (Fin 9) := Equiv.swap 3 2 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 8 * (Equiv.swap 0 6)))))
def sgFlag548 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(7,0,0),(2,0,1),(1,0,3),(4,1,0),(6,1,1),(5,1,2),(0,2,1),(3,3,0)}

def sgB549 : Equiv.Perm (Fin 9) := Equiv.swap 0 8 * (Equiv.swap 3 2 * (Equiv.swap 3 5 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 6 * (Equiv.swap 0 7))))))
def sgFlag549 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(1,0,1),(6,0,3),(0,1,0),(5,1,0),(4,1,2),(0,2,1),(3,3,0)}

def sgB550 : Equiv.Perm (Fin 9) := Equiv.swap 1 4 * (Equiv.swap 4 8 * (Equiv.swap 4 6 * (Equiv.swap 4 2 * (Equiv.swap 1 0 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 7)))))))
def sgFlag550 : Finset (ℕ × ℕ × ℕ) := {(5,0,0),(2,0,1),(4,0,2),(0,1,0),(3,1,0),(1,1,3),(0,2,1),(1,3,0)}

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 3. -/

section

noncomputable section
namespace UniversalTensorSquare

def sgB551 : Equiv.Perm (Fin 9) := Equiv.swap 6 2 * (Equiv.swap 4 8 * (Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 0 5))))))
def sgFlag551 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(3,0,1),(1,0,2),(2,0,3),(0,1,0),(2,1,0),(0,1,1),(4,2,1),(1,3,0)}

def sgB552 : Equiv.Perm (Fin 9) := Equiv.swap 0 2 * (Equiv.swap 0 1 * (Equiv.swap 1 7 * (Equiv.swap 2 8 * (Equiv.swap 2 4 * (Equiv.swap 1 5 * (Equiv.swap 0 6))))))
def sgFlag552 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(0,1,1),(4,1,1),(0,1,2),(2,2,0),(3,3,3)}

def sgB553 : Equiv.Perm (Fin 9) := Equiv.swap 7 0 * (Equiv.swap 4 1 * (Equiv.swap 1 2 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 8)))))
def sgFlag553 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(0,1,0),(3,1,0),(2,1,3),(1,2,1),(2,3,2)}

def sgB559 : Equiv.Perm (Fin 9) := Equiv.swap 0 4 * (Equiv.swap 5 3 * (Equiv.swap 4 2 * (Equiv.swap 3 8 * (Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 0 6))))))
def sgFlag559 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(1,0,2),(1,1,0),(0,1,1),(0,1,3),(2,2,1),(1,3,0)}

def sgB561 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 1 8 * (Equiv.swap 2 4 * (Equiv.swap 4 0 * (Equiv.swap 1 6 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 7)))))))
def sgFlag561 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,0),(0,0,1),(6,0,2),(2,1,0),(7,1,1),(5,1,3),(1,2,1),(3,3,0)}

def sgB562 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 1 8 * (Equiv.swap 1 5 * (Equiv.swap 2 6 * (Equiv.swap 2 3 * (Equiv.swap 1 4)))))
def sgFlag562 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(5,0,1),(1,0,2),(1,1,0),(4,1,0),(3,1,1),(2,2,3),(6,3,0)}

def sgB563 : Equiv.Perm (Fin 9) := Equiv.swap 3 8 * (Equiv.swap 3 5 * (Equiv.swap 5 2 * (Equiv.swap 2 7 * (Equiv.swap 3 0 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))))
def sgFlag563 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(1,0,1),(3,0,3),(0,1,0),(4,1,2),(2,2,1),(5,3,0)}

def sgB564 : Equiv.Perm (Fin 9) := Equiv.swap 5 8 * (Equiv.swap 3 2 * (Equiv.swap 3 0 * (Equiv.swap 2 6 * (Equiv.swap 1 7 * (Equiv.swap 0 4)))))
def sgFlag564 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(3,0,2),(0,0,3),(1,1,0),(2,1,1),(3,2,0),(4,3,0)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB565 : Equiv.Perm (Fin 9) := Equiv.swap 1 0 * (Equiv.swap 0 8 * (Equiv.swap 1 7 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 6)))))
def sgFlag565 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(5,0,0),(3,0,1),(6,1,0),(4,1,2),(0,1,3),(1,2,1),(2,3,1)}

def sgB569 : Equiv.Perm (Fin 9) := Equiv.swap 0 3 * (Equiv.swap 3 8 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 5 * (Equiv.swap 0 7)))))
def sgFlag569 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(0,0,2),(2,1,0),(4,1,1),(0,1,3),(1,2,1),(3,3,0)}

def sgB570 : Equiv.Perm (Fin 9) := Equiv.swap 4 1 * (Equiv.swap 3 7 * (Equiv.swap 1 5 * (Equiv.swap 1 2 * (Equiv.swap 0 8))))
def sgFlag570 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(0,0,1),(3,1,0),(1,1,2),(0,1,3),(0,2,1),(2,3,1)}

def sgB575 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 1 8 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 1 5 * (Equiv.swap 0 6)))))
def sgFlag575 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,0,2),(0,1,0),(0,1,1),(1,2,0),(1,3,3)}

def sgB577 : Equiv.Perm (Fin 9) := Equiv.swap 6 5 * (Equiv.swap 5 3 * (Equiv.swap 3 0 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 0 8 * (Equiv.swap 0 1))))))
def sgFlag577 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(1,0,1),(1,0,2),(2,0,2),(0,1,0),(4,1,1),(5,2,0),(6,2,1)}

def sgB578 : Equiv.Perm (Fin 9) := Equiv.swap 3 8 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 6 * (Equiv.swap 0 5))))
def sgFlag578 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,1),(2,0,2),(2,1,1),(3,1,1),(1,1,2),(1,2,0),(3,2,0)}

def sgB579 : Equiv.Perm (Fin 9) := Equiv.swap 6 4 * (Equiv.swap 4 7 * (Equiv.swap 4 5 * (Equiv.swap 2 1 * (Equiv.swap 2 0 * (Equiv.swap 1 8 * (Equiv.swap 0 3))))))
def sgFlag579 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(5,0,0),(1,0,1),(4,0,1),(0,1,0),(1,1,1),(2,1,1),(2,1,2),(3,2,0)}

def sgB580 : Equiv.Perm (Fin 9) := Equiv.swap 5 6 * (Equiv.swap 4 0 * (Equiv.swap 0 7 * (Equiv.swap 0 3 * (Equiv.swap 1 8 * (Equiv.swap 0 2)))))
def sgFlag580 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(0,0,1),(4,0,2),(2,1,0),(1,1,1),(3,2,0)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB581 : Equiv.Perm (Fin 9) := Equiv.swap 2 7 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 0 4)))
def sgFlag581 : Finset (ℕ × ℕ × ℕ) := {(5,0,0),(1,0,1),(2,0,1),(4,0,2),(0,1,0),(3,1,0),(0,1,1),(1,2,1)}

def sgB582 : Equiv.Perm (Fin 9) := Equiv.swap 2 4 * (Equiv.swap 5 1 * (Equiv.swap 4 3 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 1 8 * (Equiv.swap 0 6))))))
def sgFlag582 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(0,0,1),(3,0,2),(1,1,0),(4,1,0),(1,1,1),(2,1,1),(0,2,0)}

def sgB583 : Equiv.Perm (Fin 9) := Equiv.swap 4 8 * (Equiv.swap 4 5 * (Equiv.swap 5 0 * (Equiv.swap 4 6 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 7))))))
def sgFlag583 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(0,0,1),(1,1,0),(1,1,1),(2,1,1),(3,1,2),(0,2,0)}

def sgB584 : Equiv.Perm (Fin 9) := Equiv.swap 7 5 * (Equiv.swap 5 4 * (Equiv.swap 5 2 * (Equiv.swap 4 8 * (Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 0 6))))))
def sgFlag584 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(2,0,2),(2,1,0),(1,1,1),(0,2,1)}

def sgB614 : Equiv.Perm (Fin 9) := Equiv.swap 5 3 * (Equiv.swap 5 4 * (Equiv.swap 4 2 * (Equiv.swap 3 1 * (Equiv.swap 2 0 * (Equiv.swap 1 8 * (Equiv.swap 0 7))))))
def sgFlag614 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(6,0,1),(5,0,2),(2,0,3),(1,1,0),(4,1,0),(1,2,0),(3,3,1)}

def sgB615 : Equiv.Perm (Fin 9) := Equiv.swap 0 5 * (Equiv.swap 0 7 * (Equiv.swap 5 8 * (Equiv.swap 0 6 * (Equiv.swap 2 4 * (Equiv.swap 0 3)))))
def sgFlag615 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(4,0,1),(5,0,2),(1,0,3),(1,1,0),(2,1,1),(2,2,0),(0,3,0)}

def sgB616 : Equiv.Perm (Fin 9) := Equiv.swap 2 7 * (Equiv.swap 5 8 * (Equiv.swap 2 1 * (Equiv.swap 2 4 * (Equiv.swap 2 0 * (Equiv.swap 1 6 * (Equiv.swap 0 3))))))
def sgFlag616 : Finset (ℕ × ℕ × ℕ) := {(4,0,0),(0,0,1),(2,0,2),(1,0,3),(1,1,0),(3,1,0),(2,2,0),(3,3,0)}

def sgB621 : Equiv.Perm (Fin 9) := Equiv.swap 3 8 * (Equiv.swap 3 1 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 1 6 * (Equiv.swap 0 5)))))
def sgFlag621 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,0),(0,0,1),(1,0,1),(3,0,3),(1,1,0),(2,1,0),(1,2,0),(0,3,2)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB636 : Equiv.Perm (Fin 9) := Equiv.swap 5 1 * (Equiv.swap 5 7 * (Equiv.swap 5 6 * (Equiv.swap 1 0 * (Equiv.swap 0 8 * (Equiv.swap 1 4 * (Equiv.swap 0 2))))))
def sgFlag636 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(3,0,1),(2,0,2),(0,1,0),(4,1,1),(1,2,0),(5,2,0)}

def sgB637 : Equiv.Perm (Fin 9) := Equiv.swap 4 2 * (Equiv.swap 5 7 * (Equiv.swap 4 1 * (Equiv.swap 2 0 * (Equiv.swap 1 6 * (Equiv.swap 0 8)))))
def sgFlag637 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(3,0,1),(0,0,2),(3,0,2),(1,1,0),(0,1,1),(2,2,0)}

def sgB640 : Equiv.Perm (Fin 9) := Equiv.swap 5 8 * (Equiv.swap 5 3 * (Equiv.swap 5 1 * (Equiv.swap 3 7 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 1 0 * (Equiv.swap 0 6)))))))
def sgFlag640 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,2),(1,1,0),(0,2,1),(3,2,1)}

def sgB641 : Equiv.Perm (Fin 9) := Equiv.swap 4 1 * (Equiv.swap 1 8 * (Equiv.swap 4 2 * (Equiv.swap 2 6 * (Equiv.swap 2 3 * (Equiv.swap 1 5)))))
def sgFlag641 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,1,2),(0,2,0),(2,2,0)}

def sgB759 : Equiv.Perm (Fin 10) := Equiv.swap 4 9 * (Equiv.swap 4 0 * (Equiv.swap 4 1 * (Equiv.swap 0 7 * (Equiv.swap 0 3 * (Equiv.swap 1 5 * (Equiv.swap 0 2))))))
def sgFlag759 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(4,0,0),(4,0,1),(0,0,2),(1,1,0),(1,1,1),(2,1,1),(0,2,0)}

def sgB765 : Equiv.Perm (Fin 10) := Equiv.swap 2 1 * (Equiv.swap 2 7 * (Equiv.swap 5 9 * (Equiv.swap 2 3 * (Equiv.swap 3 6 * (Equiv.swap 2 4 * (Equiv.swap 1 0 * (Equiv.swap 0 8)))))))
def sgFlag765 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(4,0,1),(0,0,2),(0,1,0),(1,1,0),(3,2,0),(5,2,1)}

def sgB767 : Equiv.Perm (Fin 10) := Equiv.swap 6 5 * (Equiv.swap 6 1 * (Equiv.swap 5 3 * (Equiv.swap 3 0 * (Equiv.swap 0 9 * (Equiv.swap 1 7 * (Equiv.swap 0 2))))))
def sgFlag767 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(1,0,1),(3,0,2),(1,1,0),(2,1,1),(0,2,0),(1,2,0)}

def sgB768 : Equiv.Perm (Fin 10) := Equiv.swap 4 6 * (Equiv.swap 6 2 * (Equiv.swap 6 7 * (Equiv.swap 2 0 * (Equiv.swap 4 1 * (Equiv.swap 2 5 * (Equiv.swap 2 3 * (Equiv.swap 1 8 * (Equiv.swap 0 9))))))))
def sgFlag768 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(3,0,0),(1,0,1),(0,0,2),(2,1,0),(0,1,1),(1,2,0)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB790 : Equiv.Perm (Fin 10) := Equiv.swap 3 6 * (Equiv.swap 6 4 * (Equiv.swap 5 0 * (Equiv.swap 4 2 * (Equiv.swap 3 7 * (Equiv.swap 2 8 * (Equiv.swap 0 9))))))
def sgFlag790 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(3,0,0),(1,0,1),(2,0,1),(4,0,2),(5,1,0),(1,1,1),(6,1,2),(0,2,0)}

def sgB791 : Equiv.Perm (Fin 10) := Equiv.swap 3 0 * (Equiv.swap 0 9 * (Equiv.swap 3 1 * (Equiv.swap 0 7 * (Equiv.swap 3 2 * (Equiv.swap 2 6 * (Equiv.swap 1 8 * (Equiv.swap 0 4)))))))
def sgFlag791 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(2,0,1),(5,0,1),(4,0,2),(1,1,0),(2,1,0),(0,1,1),(1,2,0),(0,2,2)}

def sgB792 : Equiv.Perm (Fin 10) := Equiv.swap 3 8 * (Equiv.swap 6 4 * (Equiv.swap 4 0 * (Equiv.swap 4 5 * (Equiv.swap 3 7 * (Equiv.swap 0 9 * (Equiv.swap 0 2))))))
def sgFlag792 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(4,0,1),(2,0,2),(4,1,0),(2,1,1),(3,1,2),(0,2,0),(3,2,0)}

def sgB796 : Equiv.Perm (Fin 10) := Equiv.swap 2 5 * (Equiv.swap 5 3 * (Equiv.swap 4 1 * (Equiv.swap 3 7 * (Equiv.swap 2 6 * (Equiv.swap 1 9 * (Equiv.swap 0 8))))))
def sgFlag796 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(4,0,2),(0,1,1),(3,1,1),(4,1,2),(2,2,0)}

def sgB808 : Equiv.Perm (Fin 10) := Equiv.swap 4 3 * (Equiv.swap 3 2 * (Equiv.swap 4 7 * (Equiv.swap 4 5 * (Equiv.swap 3 0 * (Equiv.swap 2 9 * (Equiv.swap 1 8 * (Equiv.swap 0 6)))))))
def sgFlag808 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(2,0,1),(5,0,1),(2,0,2),(3,0,3),(1,1,0),(4,1,0),(0,2,0),(1,3,0)}

def sgB809 : Equiv.Perm (Fin 10) := Equiv.swap 1 5 * (Equiv.swap 5 9 * (Equiv.swap 2 7 * (Equiv.swap 2 4 * (Equiv.swap 1 6 * (Equiv.swap 0 3)))))
def sgFlag809 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(4,0,0),(0,0,1),(1,0,2),(2,0,3),(1,1,0),(4,1,0),(3,2,0),(2,3,0)}

def sgB814 : Equiv.Perm (Fin 10) := Equiv.swap 3 1 * (Equiv.swap 3 4 * (Equiv.swap 2 9 * (Equiv.swap 1 0 * (Equiv.swap 0 6))))
def sgFlag814 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(1,0,2),(4,0,3),(3,1,0),(1,1,1),(2,2,0),(5,3,0)}

def sgB816 : Equiv.Perm (Fin 10) := Equiv.swap 8 0 * (Equiv.swap 4 7 * (Equiv.swap 4 3 * (Equiv.swap 3 5 * (Equiv.swap 2 6 * (Equiv.swap 0 9 * (Equiv.swap 0 1))))))
def sgFlag816 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(2,0,1),(0,0,2),(1,0,3),(0,1,0),(1,1,0),(2,2,0),(1,3,1)}

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 4. -/

section

noncomputable section
namespace UniversalTensorSquare

def sgB826 : Equiv.Perm (Fin 10) := Equiv.swap 7 5 * (Equiv.swap 5 4 * (Equiv.swap 4 1 * (Equiv.swap 3 8 * (Equiv.swap 1 9 * (Equiv.swap 1 0 * (Equiv.swap 0 2))))))
def sgFlag826 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(2,0,1),(5,0,2),(3,0,3),(1,1,0),(4,1,0),(6,1,1),(1,2,0),(7,3,0)}

def sgB827 : Equiv.Perm (Fin 10) := Equiv.swap 8 1 * (Equiv.swap 1 5 * (Equiv.swap 5 3 * (Equiv.swap 5 6 * (Equiv.swap 1 0 * (Equiv.swap 3 9 * (Equiv.swap 1 4 * (Equiv.swap 1 2 * (Equiv.swap 0 7))))))))
def sgFlag827 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(6,0,3),(2,1,0),(3,1,1),(4,1,2),(2,2,0),(5,3,0)}

def sgB828 : Equiv.Perm (Fin 10) := Equiv.swap 1 5 * (Equiv.swap 6 2 * (Equiv.swap 5 0 * (Equiv.swap 1 7 * (Equiv.swap 1 4 * (Equiv.swap 2 9 * (Equiv.swap 1 3 * (Equiv.swap 0 8)))))))
def sgFlag828 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(4,0,2),(2,1,0),(3,1,1),(3,1,3),(5,2,0),(2,3,0)}

def sgB829 : Equiv.Perm (Fin 10) := Equiv.swap 7 4 * (Equiv.swap 4 2 * (Equiv.swap 3 6 * (Equiv.swap 2 9 * (Equiv.swap 0 1))))
def sgFlag829 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(2,0,1),(4,0,2),(1,0,3),(3,1,0),(2,1,1),(1,2,0),(4,3,0)}

def sgB832 : Equiv.Perm (Fin 10) := Equiv.swap 4 5 * (Equiv.swap 5 2 * (Equiv.swap 4 6 * (Equiv.swap 3 8 * (Equiv.swap 2 0 * (Equiv.swap 0 9 * (Equiv.swap 0 1))))))
def sgFlag832 : Finset (ℕ × ℕ × ℕ) := {(6,0,0),(0,0,1),(1,0,1),(0,0,3),(2,1,0),(2,1,1),(3,1,1),(4,1,2),(5,2,0),(1,3,0)}

def sgB833 : Equiv.Perm (Fin 10) := Equiv.swap 2 4 * (Equiv.swap 2 7 * (Equiv.swap 4 8 * (Equiv.swap 3 5 * (Equiv.swap 2 6 * (Equiv.swap 0 1)))))
def sgFlag833 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(1,0,1),(0,0,2),(0,1,0),(3,1,0),(5,1,1),(3,1,3),(4,2,0),(2,3,1)}

def sgB834 : Equiv.Perm (Fin 10) := Equiv.swap 3 5 * (Equiv.swap 3 4 * (Equiv.swap 5 9 * (Equiv.swap 4 2 * (Equiv.swap 3 6 * (Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 0 8)))))))
def sgFlag834 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(3,0,1),(0,0,2),(1,1,0),(4,1,1),(2,1,3),(0,2,1),(3,3,0)}

def sgB835 : Equiv.Perm (Fin 10) := Equiv.swap 2 9 * (Equiv.swap 5 0 * (Equiv.swap 5 6 * (Equiv.swap 1 4 * (Equiv.swap 2 8 * (Equiv.swap 1 3 * (Equiv.swap 0 7))))))
def sgFlag835 : Finset (ℕ × ℕ × ℕ) := {(4,0,0),(0,0,1),(3,0,1),(1,1,0),(6,1,1),(2,1,2),(7,1,3),(0,2,0),(5,3,0)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB836 : Equiv.Perm (Fin 10) := Equiv.swap 4 7 * (Equiv.swap 3 0 * (Equiv.swap 4 6 * (Equiv.swap 3 1 * (Equiv.swap 1 5 * (Equiv.swap 1 2 * (Equiv.swap 0 8))))))
def sgFlag836 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(5,0,1),(2,0,3),(0,1,0),(1,1,1),(3,1,2),(4,2,1),(0,3,1)}

def sgB837 : Equiv.Perm (Fin 10) := Equiv.swap 0 1 * (Equiv.swap 0 7 * (Equiv.swap 0 6 * (Equiv.swap 0 2 * (Equiv.swap 2 5 * (Equiv.swap 2 3 * (Equiv.swap 1 8 * (Equiv.swap 0 4)))))))
def sgFlag837 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,1),(1,0,2),(2,1,0),(3,1,0),(1,1,1),(2,2,3),(0,3,1)}

def sgB838 : Equiv.Perm (Fin 10) := Equiv.swap 2 5 * (Equiv.swap 5 1 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 2 8 * (Equiv.swap 1 9)))))
def sgFlag838 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(6,0,1),(7,0,2),(1,0,3),(5,1,0),(0,1,1),(1,2,0),(4,2,2),(3,3,0)}

def sgB839 : Equiv.Perm (Fin 10) := Equiv.swap 6 9 * (Equiv.swap 6 0 * (Equiv.swap 1 8 * (Equiv.swap 1 3 * (Equiv.swap 3 5 * (Equiv.swap 1 4 * (Equiv.swap 1 2 * (Equiv.swap 0 7)))))))
def sgFlag839 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(2,0,2),(1,0,3),(3,1,0),(5,1,2),(2,2,0),(6,2,0),(4,3,1)}

def sgB840 : Equiv.Perm (Fin 10) := Equiv.swap 2 9 * (Equiv.swap 2 3 * (Equiv.swap 2 7 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 3 5 * (Equiv.swap 2 0 * (Equiv.swap 0 4)))))))
def sgFlag840 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(0,0,2),(4,0,3),(5,1,0),(1,1,1),(2,2,0),(1,3,1)}

def sgB841 : Equiv.Perm (Fin 10) := Equiv.swap 6 1 * (Equiv.swap 6 4 * (Equiv.swap 4 0 * (Equiv.swap 4 5 * (Equiv.swap 0 7 * (Equiv.swap 0 3 * (Equiv.swap 1 8 * (Equiv.swap 0 2)))))))
def sgFlag841 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,1),(3,0,2),(1,1,0),(2,2,0),(2,2,3),(0,3,0)}

def sgB846 : Equiv.Perm (Fin 10) := Equiv.swap 1 5 * (Equiv.swap 5 9 * (Equiv.swap 5 7 * (Equiv.swap 1 8 * (Equiv.swap 2 0 * (Equiv.swap 2 3 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))))
def sgFlag846 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(0,0,1),(1,0,1),(1,0,2),(1,1,0),(4,1,0),(5,2,2),(0,2,3),(2,3,0)}

def sgB847 : Equiv.Perm (Fin 10) := Equiv.swap 8 0 * (Equiv.swap 0 5 * (Equiv.swap 5 4 * (Equiv.swap 4 9 * (Equiv.swap 1 7 * (Equiv.swap 1 3 * (Equiv.swap 0 6))))))
def sgFlag847 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(2,0,1),(0,0,2),(3,1,0),(1,1,3),(0,2,1),(2,2,2),(0,3,0)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB873 : Equiv.Perm (Fin 10) := Equiv.swap 1 9 * (Equiv.swap 6 4 * (Equiv.swap 4 7 * (Equiv.swap 4 0 * (Equiv.swap 0 5 * (Equiv.swap 1 8 * (Equiv.swap 0 2))))))
def sgFlag873 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(1,0,1),(6,0,1),(7,0,2),(0,1,0),(2,1,0),(3,1,2),(4,2,0),(0,2,1),(5,2,2)}

def sgB874 : Equiv.Perm (Fin 10) := Equiv.swap 0 3 * (Equiv.swap 0 8 * (Equiv.swap 0 7 * (Equiv.swap 3 9 * (Equiv.swap 2 6 * (Equiv.swap 0 4 * (Equiv.swap 0 1))))))
def sgFlag874 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(3,0,0),(6,0,1),(1,0,2),(1,1,1),(5,1,1),(2,1,2),(0,2,0),(4,2,2)}

def sgB875 : Equiv.Perm (Fin 10) := Equiv.swap 6 5 * (Equiv.swap 6 2 * (Equiv.swap 6 7 * (Equiv.swap 5 4 * (Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 2 8 * (Equiv.swap 0 9 * (Equiv.swap 0 1))))))))
def sgFlag875 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(1,0,1),(2,0,1),(0,1,0),(5,1,2),(2,2,1),(3,2,2)}

def sgB876 : Equiv.Perm (Fin 10) := Equiv.swap 4 7 * (Equiv.swap 7 6 * (Equiv.swap 6 2 * (Equiv.swap 4 8 * (Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 2 9 * (Equiv.swap 0 5 * (Equiv.swap 0 1))))))))
def sgFlag876 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(0,0,1),(3,0,1),(6,0,2),(0,1,0),(5,1,2),(1,2,0),(7,2,1),(4,2,2)}

def sgB877 : Equiv.Perm (Fin 10) := Equiv.swap 7 9 * (Equiv.swap 7 8 * (Equiv.swap 0 4 * (Equiv.swap 1 6 * (Equiv.swap 1 2 * (Equiv.swap 0 3)))))
def sgFlag877 : Finset (ℕ × ℕ × ℕ) := {(5,0,0),(1,0,1),(0,0,3),(3,1,0),(0,1,1),(4,1,1),(2,1,2),(6,2,0),(2,3,0)}

def sgB878 : Equiv.Perm (Fin 10) := Equiv.swap 3 9 * (Equiv.swap 5 7 * (Equiv.swap 1 8 * (Equiv.swap 3 6 * (Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 4))))))
def sgFlag878 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(0,0,1),(3,1,1),(2,1,2),(5,1,3),(2,2,0),(1,3,0)}

def sgB879 : Equiv.Perm (Fin 10) := Equiv.swap 7 8 * (Equiv.swap 4 2 * (Equiv.swap 3 6 * (Equiv.swap 2 0 * (Equiv.swap 1 9 * (Equiv.swap 0 5)))))
def sgFlag879 : Finset (ℕ × ℕ × ℕ) := {(2,0,1),(0,0,2),(3,0,3),(4,1,0),(1,1,1),(3,1,1),(0,2,0),(1,3,0)}

def sgB880 : Equiv.Perm (Fin 10) := Equiv.swap 6 2 * (Equiv.swap 5 0 * (Equiv.swap 2 1 * (Equiv.swap 0 7 * (Equiv.swap 2 4 * (Equiv.swap 1 9 * (Equiv.swap 0 3))))))
def sgFlag880 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(3,0,1),(6,0,2),(5,0,3),(0,1,0),(0,1,1),(1,1,1),(4,2,0),(7,3,1)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB881 : Equiv.Perm (Fin 10) := Equiv.swap 0 2 * (Equiv.swap 1 8 * (Equiv.swap 1 6 * (Equiv.swap 1 5 * (Equiv.swap 2 9 * (Equiv.swap 1 3 * (Equiv.swap 0 7))))))

def sgB884 : Equiv.Perm (Fin 10) := Equiv.swap 6 2 * (Equiv.swap 2 0 * (Equiv.swap 2 5 * (Equiv.swap 2 3 * (Equiv.swap 1 8 * (Equiv.swap 0 7)))))

def sgB885 : Equiv.Perm (Fin 10) := Equiv.swap 1 9 * (Equiv.swap 6 0 * (Equiv.swap 4 2 * (Equiv.swap 1 7 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 8))))))

def sgB886 : Equiv.Perm (Fin 10) := Equiv.swap 2 0 * (Equiv.swap 0 9 * (Equiv.swap 2 7 * (Equiv.swap 2 5 * (Equiv.swap 0 6))))

def sgB887 : Equiv.Perm (Fin 10) := Equiv.swap 6 1 * (Equiv.swap 6 4 * (Equiv.swap 4 3 * (Equiv.swap 3 7 * (Equiv.swap 2 8 * (Equiv.swap 1 9)))))

def sgB889 : Equiv.Perm (Fin 10) := Equiv.swap 1 3 * (Equiv.swap 3 2 * (Equiv.swap 2 9 * (Equiv.swap 4 5 * (Equiv.swap 3 7 * (Equiv.swap 2 6 * (Equiv.swap 1 0 * (Equiv.swap 0 8)))))))

def sgB890 : Equiv.Perm (Fin 10) := Equiv.swap 1 2 * (Equiv.swap 5 3 * (Equiv.swap 4 0 * (Equiv.swap 3 8 * (Equiv.swap 2 9 * (Equiv.swap 1 6 * (Equiv.swap 0 7))))))

def sgB891 : Equiv.Perm (Fin 10) := Equiv.swap 4 6 * (Equiv.swap 6 3 * (Equiv.swap 4 8 * (Equiv.swap 3 9 * (Equiv.swap 1 5 * (Equiv.swap 0 2)))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB892 : Equiv.Perm (Fin 10) := Equiv.swap 2 1 * (Equiv.swap 2 3 * (Equiv.swap 1 4 * (Equiv.swap 4 9 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 0 7)))))))

def sgB897 : Equiv.Perm (Fin 10) := Equiv.swap 5 4 * (Equiv.swap 5 2 * (Equiv.swap 5 0 * (Equiv.swap 4 9 * (Equiv.swap 0 1 * (Equiv.swap 2 8 * (Equiv.swap 1 7 * (Equiv.swap 0 3)))))))

def sgB898 : Equiv.Perm (Fin 10) := Equiv.swap 2 6 * (Equiv.swap 6 0 * (Equiv.swap 0 9 * (Equiv.swap 1 5 * (Equiv.swap 2 7 * (Equiv.swap 1 3 * (Equiv.swap 0 4))))))

def sgB899 : Equiv.Perm (Fin 10) := Equiv.swap 1 5 * (Equiv.swap 1 0 * (Equiv.swap 1 3 * (Equiv.swap 5 4 * (Equiv.swap 4 2 * (Equiv.swap 3 7 * (Equiv.swap 2 9 * (Equiv.swap 1 6 * (Equiv.swap 0 8))))))))

def sgB902 : Equiv.Perm (Fin 10) := Equiv.swap 0 1 * (Equiv.swap 0 7 * (Equiv.swap 0 6 * (Equiv.swap 4 2 * (Equiv.swap 2 9 * (Equiv.swap 2 3 * (Equiv.swap 1 8 * (Equiv.swap 0 5)))))))

def sgB903 : Equiv.Perm (Fin 10) := Equiv.swap 3 9 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 8 * (Equiv.swap 1 7 * (Equiv.swap 0 6)))))

def sgB909 : Equiv.Perm (Fin 10) := Equiv.swap 6 5 * (Equiv.swap 5 8 * (Equiv.swap 1 9 * (Equiv.swap 1 4 * (Equiv.swap 0 7))))

def sgB915 : Equiv.Perm (Fin 10) := Equiv.swap 1 4 * (Equiv.swap 4 7 * (Equiv.swap 4 3 * (Equiv.swap 3 5 * (Equiv.swap 2 8 * (Equiv.swap 1 0 * (Equiv.swap 0 6))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 5. -/

section

noncomputable section
namespace UniversalTensorSquare

def sgB922 : Equiv.Perm (Fin 10) := Equiv.swap 8 0 * (Equiv.swap 0 9 * (Equiv.swap 3 7 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 1 5 * (Equiv.swap 0 6))))))

def sgB932 : Equiv.Perm (Fin 10) := Equiv.swap 3 7 * (Equiv.swap 7 1 * (Equiv.swap 3 2 * (Equiv.swap 3 6 * (Equiv.swap 1 9 * (Equiv.swap 3 5 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 8))))))))

def sgB939 : Equiv.Perm (Fin 10) := Equiv.swap 1 7 * (Equiv.swap 7 3 * (Equiv.swap 3 9 * (Equiv.swap 1 0 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 0 8))))))))

def sgB940 : Equiv.Perm (Fin 10) := Equiv.swap 6 4 * (Equiv.swap 2 9 * (Equiv.swap 4 8 * (Equiv.swap 1 7 * (Equiv.swap 2 5 * (Equiv.swap 1 3)))))

def sgB941 : Equiv.Perm (Fin 10) := Equiv.swap 6 4 * (Equiv.swap 4 0 * (Equiv.swap 3 8 * (Equiv.swap 1 9 * (Equiv.swap 0 7))))

def sgB942 : Equiv.Perm (Fin 10) := Equiv.swap 1 9 * (Equiv.swap 5 0 * (Equiv.swap 1 8 * (Equiv.swap 2 7 * (Equiv.swap 1 3 * (Equiv.swap 0 6)))))

def sgB943 : Equiv.Perm (Fin 10) := Equiv.swap 2 5 * (Equiv.swap 5 9 * (Equiv.swap 2 8 * (Equiv.swap 5 3 * (Equiv.swap 3 1 * (Equiv.swap 2 0 * (Equiv.swap 1 7 * (Equiv.swap 0 6)))))))

def sgB948 : Equiv.Perm (Fin 10) := Equiv.swap 4 9 * (Equiv.swap 4 8 * (Equiv.swap 5 3 * (Equiv.swap 4 0 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 0 6)))))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB949 : Equiv.Perm (Fin 10) := Equiv.swap 7 5 * (Equiv.swap 5 9 * (Equiv.swap 5 6 * (Equiv.swap 2 0 * (Equiv.swap 0 4 * (Equiv.swap 0 1)))))

def sgB950 : Equiv.Perm (Fin 10) := Equiv.swap 5 8 * (Equiv.swap 4 9 * (Equiv.swap 3 6 * (Equiv.swap 0 2 * (Equiv.swap 0 1))))

def sgB951 : Equiv.Perm (Fin 10) := Equiv.swap 7 2 * (Equiv.swap 5 3 * (Equiv.swap 2 8 * (Equiv.swap 3 1 * (Equiv.swap 2 0 * (Equiv.swap 1 9 * (Equiv.swap 0 4))))))

def sgB958 : Equiv.Perm (Fin 10) := Equiv.swap 3 0 * (Equiv.swap 3 7 * (Equiv.swap 0 9 * (Equiv.swap 3 6 * (Equiv.swap 0 4 * (Equiv.swap 1 8 * (Equiv.swap 0 2))))))

def sgB959 : Equiv.Perm (Fin 10) := Equiv.swap 7 4 * (Equiv.swap 2 6 * (Equiv.swap 4 3 * (Equiv.swap 3 8 * (Equiv.swap 2 0 * (Equiv.swap 0 5 * (Equiv.swap 0 1))))))

def sgB960 : Equiv.Perm (Fin 10) := Equiv.swap 8 7 * (Equiv.swap 7 1 * (Equiv.swap 1 9 * (Equiv.swap 3 4 * (Equiv.swap 1 6 * (Equiv.swap 0 2)))))

def sgB961 : Equiv.Perm (Fin 10) := Equiv.swap 5 3 * (Equiv.swap 5 4 * (Equiv.swap 4 1 * (Equiv.swap 3 8 * (Equiv.swap 1 6 * (Equiv.swap 0 9)))))

def sgB964 : Equiv.Perm (Fin 10) := Equiv.swap 0 4 * (Equiv.swap 5 9 * (Equiv.swap 4 2 * (Equiv.swap 2 8 * (Equiv.swap 1 3 * (Equiv.swap 0 6)))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB975 : Equiv.Perm (Fin 10) := Equiv.swap 5 8 * (Equiv.swap 5 2 * (Equiv.swap 4 1 * (Equiv.swap 2 7 * (Equiv.swap 2 3 * (Equiv.swap 1 6)))))

def sgB976 : Equiv.Perm (Fin 10) := Equiv.swap 7 1 * (Equiv.swap 5 9 * (Equiv.swap 5 2 * (Equiv.swap 2 3 * (Equiv.swap 3 6 * (Equiv.swap 2 0 * (Equiv.swap 1 8 * (Equiv.swap 0 4)))))))

def sgB977 : Equiv.Perm (Fin 10) := Equiv.swap 7 6 * (Equiv.swap 7 1 * (Equiv.swap 6 9 * (Equiv.swap 1 0 * (Equiv.swap 1 3 * (Equiv.swap 3 5 * (Equiv.swap 0 8 * (Equiv.swap 1 4 * (Equiv.swap 0 2))))))))

def sgB982 : Equiv.Perm (Fin 10) := Equiv.swap 1 8 * (Equiv.swap 2 0 * (Equiv.swap 2 3 * (Equiv.swap 3 6 * (Equiv.swap 3 4 * (Equiv.swap 2 5 * (Equiv.swap 1 7 * (Equiv.swap 0 9)))))))

def sgB998 : Equiv.Perm (Fin 10) := Equiv.swap 2 5 * (Equiv.swap 5 4 * (Equiv.swap 4 9 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 1 7)))))

def sgB999 : Equiv.Perm (Fin 10) := Equiv.swap 6 3 * (Equiv.swap 2 1 * (Equiv.swap 4 0 * (Equiv.swap 3 8 * (Equiv.swap 2 5 * (Equiv.swap 1 7 * (Equiv.swap 0 9))))))

def sgB1000 : Equiv.Perm (Fin 10) := Equiv.swap 0 5 * (Equiv.swap 1 3 * (Equiv.swap 5 9 * (Equiv.swap 1 6 * (Equiv.swap 3 8 * (Equiv.swap 1 4 * (Equiv.swap 0 7))))))
def sgFlag1000 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(2,0,3),(5,0,5),(3,1,4),(2,2,2),(0,3,0),(3,4,0),(4,5,0)}

def sgB1001 : Equiv.Perm (Fin 10) := Equiv.swap 8 2 * (Equiv.swap 2 4 * (Equiv.swap 4 9 * (Equiv.swap 3 6 * (Equiv.swap 2 5 * (Equiv.swap 0 1)))))
def sgFlag1001 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(0,0,1),(3,0,2),(2,0,3),(4,0,4),(2,1,0),(0,2,0),(1,3,0),(3,4,0)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB1006 : Equiv.Perm (Fin 10) := Equiv.swap 0 6 * (Equiv.swap 6 1 * (Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 2 5 * (Equiv.swap 1 9 * (Equiv.swap 0 8)))))))
def sgFlag1006 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,0),(1,0,1),(0,0,2),(4,0,3),(5,1,0),(3,2,0),(1,3,4),(0,4,0)}

def sgB1007 : Equiv.Perm (Fin 10) := Equiv.swap 2 4 * (Equiv.swap 5 3 * (Equiv.swap 4 9 * (Equiv.swap 3 7 * (Equiv.swap 2 8))))
def sgFlag1007 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(2,0,2),(0,0,3),(3,0,4),(0,1,1),(0,2,0),(2,3,0),(1,4,0)}

def sgB1008 : Equiv.Perm (Fin 10) := Equiv.swap 1 2 * (Equiv.swap 3 6 * (Equiv.swap 3 4 * (Equiv.swap 2 9 * (Equiv.swap 1 8 * (Equiv.swap 0 5)))))
def sgFlag1008 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(3,0,0),(2,0,1),(0,0,2),(1,0,3),(2,1,0),(3,2,0),(1,3,4),(0,4,0)}

def sgB1015 : Equiv.Perm (Fin 10) := Equiv.swap 6 0 * (Equiv.swap 5 1 * (Equiv.swap 4 8 * (Equiv.swap 1 9 * (Equiv.swap 1 3 * (Equiv.swap 0 7)))))
def sgFlag1015 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(3,0,0),(0,0,1),(1,0,4),(1,1,3),(0,2,2),(0,3,0),(2,4,0)}

def sgB1016 : Equiv.Perm (Fin 10) := Equiv.swap 3 2 * (Equiv.swap 3 5 * (Equiv.swap 5 0 * (Equiv.swap 2 9 * (Equiv.swap 3 6 * (Equiv.swap 2 4 * (Equiv.swap 0 8))))))
def sgFlag1016 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,2),(1,0,3),(1,1,1),(1,2,4),(1,3,0),(2,4,0)}

def sgB1023 : Equiv.Perm (Fin 10) := Equiv.swap 7 1 * (Equiv.swap 7 0 * (Equiv.swap 0 8 * (Equiv.swap 1 9 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))
def sgFlag1023 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(1,1,4),(1,2,2),(0,3,3),(1,4,0)}

def sgB1032 : Equiv.Perm (Fin 10) := Equiv.swap 8 5 * (Equiv.swap 5 2 * (Equiv.swap 5 0 * (Equiv.swap 1 7 * (Equiv.swap 0 6 * (Equiv.swap 2 9 * (Equiv.swap 1 4 * (Equiv.swap 0 3)))))))
def sgFlag1032 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(3,0,1),(5,0,1),(3,0,2),(0,0,3),(1,1,0),(2,1,0),(2,2,0),(0,3,0)}

def sgB1033 : Equiv.Perm (Fin 10) := Equiv.swap 8 5 * (Equiv.swap 1 7 * (Equiv.swap 5 9 * (Equiv.swap 1 2 * (Equiv.swap 2 6 * (Equiv.swap 1 4 * (Equiv.swap 0 3))))))
def sgFlag1033 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(4,0,0),(1,0,1),(4,0,1),(1,0,2),(3,0,3),(0,1,0),(3,1,0),(0,2,0),(2,3,0)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare

def sgB1038 : Equiv.Perm (Fin 10) := Equiv.swap 8 5 * (Equiv.swap 5 2 * (Equiv.swap 2 3 * (Equiv.swap 5 7 * (Equiv.swap 3 9 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 0 6))))))))
def sgFlag1038 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,0),(0,0,1),(4,0,2),(0,0,3),(1,1,0),(3,2,1),(5,3,0)}

def sgB1040 : Equiv.Perm (Fin 10) := Equiv.swap 8 1 * (Equiv.swap 1 5 * (Equiv.swap 5 9 * (Equiv.swap 1 7 * (Equiv.swap 0 6 * (Equiv.swap 1 3 * (Equiv.swap 0 2))))))
def sgFlag1040 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(1,0,1),(2,0,2),(2,1,0),(3,1,3),(0,2,0),(1,3,0)}

def sgB1063 : Equiv.Perm (Fin 10) := Equiv.swap 7 2 * (Equiv.swap 2 1 * (Equiv.swap 2 6 * (Equiv.swap 4 3 * (Equiv.swap 3 9 * (Equiv.swap 2 5 * (Equiv.swap 1 8))))))
def sgFlag1063 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(3,0,1),(4,0,2),(0,1,0),(5,2,0),(2,2,2)}

def sgB1064 : Equiv.Perm (Fin 10) := Equiv.swap 5 7 * (Equiv.swap 7 9 * (Equiv.swap 5 8 * (Equiv.swap 0 4 * (Equiv.swap 1 6 * (Equiv.swap 0 3)))))
def sgFlag1064 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(0,0,1),(3,0,2),(1,1,0),(2,1,0),(0,2,0),(2,2,2)}

def sgB1065 : Equiv.Perm (Fin 10) := Equiv.swap 3 4 * (Equiv.swap 3 0 * (Equiv.swap 5 9 * (Equiv.swap 4 1 * (Equiv.swap 3 2 * (Equiv.swap 2 6 * (Equiv.swap 1 8 * (Equiv.swap 0 7)))))))
def sgFlag1065 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(3,0,0),(1,0,1),(2,0,2),(0,1,0),(0,1,1),(1,2,0)}

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ExceptionalFourteen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional Fourteen. -/

section

noncomputable section
namespace UniversalTensorSquare

def exceptionalRows71 : List ℕ := [7,7,7,6,6,5,4,4,4,3,3,3,3,2,2,2,2,1]

def exceptionalRows73 : List ℕ := [8,8,7,7,7,6,4,4,4,4,3,3,3,3,2]

def exceptionalRows75 : List ℕ := [8,7,7,7,7,6,4,4,4,3,3,3,3,2,2,2,2,1]

def exceptionalRows77 : List ℕ := [8,8,8,8,8,7,4,4,4,4,3,3,3,3,2]

def exceptionalRows79 : List ℕ := [8,8,8,8,7,7,4,4,4,3,3,3,3,2,2,2,2,1]

def exceptionalRows81 : List ℕ := [9,9,9,8,8,8,4,4,4,4,3,3,3,3,2]

def exceptionalRows83 : List ℕ := [9,9,8,8,8,8,4,4,4,3,3,3,3,2,2,2,2,1]

def exceptionalRows85 : List ℕ := [10,9,9,9,9,9,4,4,4,4,3,3,3,3,2]

def exceptionalRows87 : List ℕ := [10,9,9,9,9,8,4,4,4,3,3,3,3,2,2,2,2,1]

def exceptionalRows106 : List ℕ := [10,9,9,9,9,8,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

def exceptionalRows108 : List ℕ := [10,10,10,10,10,9,5,5,5,4,4,4,4,4,3,3,3,3,2]

def exceptionalRows110 : List ℕ := [10,10,10,10,9,9,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

def exceptionalRows114 : List ℕ := [11,11,10,10,10,10,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

def exceptionalRows149 : List ℕ := [13,13,12,12,12,12,6,6,6,5,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

end UniversalTensorSquare
end
end

end OAI
end


