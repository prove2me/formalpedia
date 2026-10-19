-- Prove2me | Definitions.Def_QAlgorithms_Defs_NoisyTannerData
-- name    : QAlgorithms_Defs_NoisyTannerData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:43.847236+00:00
-- url     : https://prove2.me/theorems/cea07f0e-78a0-41b0-89b8-af1e60373d96
-- title:
--   NoisyTannerData
-- statement:
--   NoisyTannerData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\NoisyTannerData.lean

import Definitions.Def_QAlgorithms_Defs_TannerDecoder
import Definitions.Def_QAlgorithms_Defs_FieldCodeGeometry
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.NoisyTanner

/-- One-sided second-largest-eigenvalue condition with multiplicity;
2306.12470 pp.5,7. No lower bound on negative eigenvalues is imposed. -/
def OneSidedRamanujan {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (M : Matrix I I ℝ) (degree : ℕ) : Prop :=
  0 < degree ∧ M.IsHermitian ∧ ∀ k : Fin (Fintype.card I),
    (k.val + 1 < Fintype.card I) → ascEigenvalues M k ≤ 2*Real.sqrt ((degree : ℝ)-1)

/-- Quantum Tanner public data and standing local-code assumptions;
2306.12470 pp.5–7,12. No total-no-conjugacy condition is added. -/
structure CodeData (G : Type*) [Group G] [Fintype G] [DecidableEq G] where
  A : Finset G
  B : Finset G
  degree : ℕ
  degree_pos : 0 < degree
  cardA : A.card = degree
  cardB : B.card = degree
  inverseA : ∀ a ∈ A, a⁻¹ ∈ A
  inverseB : ∀ b ∈ B, b⁻¹ ∈ B
  generatesA : Subgroup.closure (A : Set G) = ⊤
  generatesB : Subgroup.closure (B : Set G) = ⊤
  CA : Submodule (ZMod 2) (A → ZMod 2)
  CB : Submodule (ZMod 2) (B → ZMod 2)
  rate : ℝ
  relativeDistance : ℝ
  kappa : ℝ
  rate_range : 0 < rate ∧ rate < 1
  distance_range : 0 < relativeDistance ∧ relativeDistance < 1
  kappa_range : 0 < kappa ∧ kappa < 1
  dimensionA : (Module.finrank (ZMod 2) CA : ℝ) = rate*degree
  dimensionB : (Module.finrank (ZMod 2) CB : ℝ) = (1-rate)*degree
  distanceA : HasMinDistAtLeast CA (relativeDistance*degree)
  distanceB : HasMinDistAtLeast CB (relativeDistance*degree)
  distanceDualA : HasMinDistAtLeast (codeDual CA) (relativeDistance*degree)
  distanceDualB : HasMinDistAtLeast (codeDual CB) (relativeDistance*degree)
  expansion : IsProductExpanding CA CB degree kappa
  expansionDual : IsProductExpanding (codeDual CA) (codeDual CB) degree kappa
  spectralA : OneSidedRamanujan (leftCayleyAdj A) degree
  spectralB : OneSidedRamanujan (rightCayleyAdj B) degree

/-- Attained reduced error weight modulo X stabilizers; 2306.12470 pp.8,12. -/
def reducedWeight {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (C : CodeData G) (e : G × C.A × C.B → ZMod 2) : ℕ :=
  (Finset.univ : Finset (qtSigmaXSpan C.CA C.CB)).inf'
    (Finset.univ_nonempty_iff.mpr ⟨0⟩)
    (fun s => hammingNorm (e+(s : G × C.A × C.B → ZMod 2)))

/-- Labelled local generating lists for the Z and X check spaces;
2306.12470 pp.6,12. Redundant checks remain individually labelled. -/
structure CheckPresentation {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (C : CodeData G) where
  zCount : ℕ
  xCount : ℕ
  zLocal : Fin zCount → C.A × C.B → ZMod 2
  xLocal : Fin xCount → C.A × C.B → ZMod 2
  zGenerates : Submodule.span (ZMod 2) (Set.range zLocal) =
    tensorCode (codeDual C.CA) (codeDual C.CB)
  xGenerates : Submodule.span (ZMod 2) (Set.range xLocal) = tensorCode C.CA C.CB

/-- Vertex-labelled Z-check syndrome matrix; 2306.12470 pp.6,12. -/
def CheckPresentation.zMatrix {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {C : CodeData G} (H : CheckPresentation C) :
    Matrix ({v : G × (Bool × Bool) // v.2.1 ≠ v.2.2} × Fin H.zCount)
      (G × C.A × C.B) (ZMod 2) :=
  Matrix.of fun vk => qtPush vk.1.val (H.zLocal vk.2)

/-- Arbitrary labelled measurement corruption added to the actual syndrome;
2306.12470 pp.7,12. No consistency or probability assumption is imposed. -/
def noisySyndrome {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {C : CodeData G} (H : CheckPresentation C) (e : G × C.A × C.B → ZMod 2)
    (D : {v : G × (Bool × Bool) // v.2.1 ≠ v.2.2} × Fin H.zCount → ZMod 2) :=
  H.zMatrix.mulVec e + D

/-- Number of vertices with a nonzero entire check-error block;
2306.12470 pp.8,12. Multiple flipped bits at one vertex count once. -/
def syndromeVertexWeight {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {C : CodeData G} (H : CheckPresentation C)
    (D : {v : G × (Bool × Bool) // v.2.1 ≠ v.2.2} × Fin H.zCount → ZMod 2) : ℕ :=
  (Finset.univ.filter fun v => ∃ j, D (v,j) ≠ 0).card

example {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {C : CodeData G} (H : CheckPresentation C) : syndromeVertexWeight H 0 = 0 := by
  simp [syndromeVertexWeight]

example {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I] (M : Matrix I I ℝ) :
    ¬ OneSidedRamanujan M 0 := by simp [OneSidedRamanujan]


end QAlgorithms.NoisyTanner


