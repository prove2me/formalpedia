-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_Supplement_TranslationPacking
-- name    : BeyondConvexity_APTAS_Supplement_TranslationPacking
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:11:57.518962+00:00
-- url     : https://prove2.me/theorems/a2c4caf5-33bb-4057-899e-841747ca6a10
-- title:
--   Exact dimensional translation packing and real optimum
-- statement:
--   A packing assigns each input occurrence a bin index and a vector in $\mathbb R^d$. Feasibility requires every translated closed region to lie in its assigned exact unit hypercube and every two distinct occurrences assigned to the same bin to have disjoint interiors. Boundary contact is permitted. Rational output uses rational vectors, interpreted exactly in Euclidean space.
--
--   $$\operatorname{OPT}_d(I)=\min\{m\in\mathbb N:I\text{ has such a packing in }m\text{ bins using real translations}\}.$$
--
--   Valid normalized inputs fit one occurrence per bin, so this minimum exists. Empty input has optimum zero and a zero-bin empty packing. The total definition returns zero when no packing exists, outside the promised input domain. Output encoding includes the bin count and every occurrence's bin and rational translation. This is actual region feasibility, with no bounding-box substitution, rotation or enlargement.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), Section 2, printed p.5 / PDF p.6; Section 7 and Theorem 2, printed p.16 / PDF p.17

import Definitions.Def_BeyondConvexity_APTAS_Supplement_PolyhedralRegion

noncomputable section

open Classical

namespace BeyondConvexity.APTAS.Supplement

/-- The ith entry assigns the ith labeled input occurrence. -/
structure TranslationPacking (d : ℕ) (F : Type) where
  bins : ℕ
  placements : List (ℕ × (Fin d → F))

def Feasible {d : ℕ} (I : Instance d) (p : TranslationPacking d ℝ) : Prop :=
  p.placements.length = I.length ∧
  (∀ i : Fin I.length, ∃ b v, p.placements[i.val]? = some (b, v) ∧
    b < p.bins ∧ translate (WithLp.toLp 2 v) (I.get i).region ⊆ unitCube d) ∧
  ∀ (i j : Fin I.length), i ≠ j → ∀ b v w,
    p.placements[i.val]? = some (b, v) → p.placements[j.val]? = some (b, w) →
      Disjoint (interior (translate (WithLp.toLp 2 v) (I.get i).region))
        (interior (translate (WithLp.toLp 2 w) (I.get j).region))

def realizePacking {d : ℕ} (p : TranslationPacking d ℚ) : TranslationPacking d ℝ :=
  ⟨p.bins, p.placements.map fun bv => (bv.1, fun i => (bv.2 i : ℝ))⟩

def RationalPacking {d : ℕ} (I : Instance d) (p : TranslationPacking d ℚ) : Prop :=
  Feasible I (realizePacking p)

def Packable {d : ℕ} (I : Instance d) (m : ℕ) : Prop :=
  ∃ p : TranslationPacking d ℝ, p.bins = m ∧ Feasible I p

/-- Minimum over real translations. Valid normalized inputs can always be packed
one object per bin. Off that domain, the explicit fallback is zero. -/
def OPT {d : ℕ} (I : Instance d) : ℕ :=
  if h : ∃ m, Packable I m then Nat.find h else 0

open RSListDecodingCapacity.AllRates (encNat encList)

def encPacking {d : ℕ} (p : TranslationPacking d ℚ) : List Bool :=
  encNat p.bins ++ encList (fun bv => encNat bv.1 ++ encPoint bv.2) p.placements

end BeyondConvexity.APTAS.Supplement


