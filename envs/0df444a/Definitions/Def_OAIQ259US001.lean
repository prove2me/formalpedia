-- Prove2me | Definitions.Def_OAIQ259US001
-- name    : OAIQ259US001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:07:28.727198+00:00
-- url     : https://prove2.me/theorems/62e86fe0-5eb3-48b5-a59d-310779d9f6f8
-- title:
--   Definitions bundle OAIQ259US001 of the split of OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 452 declarations of OpenAI's Lean: 332 definitions, 6 inductive types or structures, 8 instances and 106 theorems. The definitions and types are `OAI.Saxl.Balance.PackingPlan`, `OAI.Saxl.Balance.PackingPlan.Valid`, `OAI.Saxl.Balance.PackingPlan.bands`, `OAI.Saxl.Balance.PackingPlan.columns`, `OAI.Saxl.Balance.PackingPlan.marks`, `OAI.Saxl.Balance.PackingPlan.parts`, `OAI.Saxl.Balance.appendShortCells`, `OAI.Saxl.Balance.appendShortMap`, `OAI.Saxl.Balance.balanceParts`, `OAI.Saxl.Balance.balanceWords`, `OAI.Saxl.Balance.bandStarts`, `OAI.Saxl.Balance.bandUpper`, `OAI.Saxl.Balance.bigParts`, `OAI.Saxl.Balance.bigUpper`, `OAI.Saxl.Balance.markIf`, `OAI.Saxl.Balance.neighborLetter`, `OAI.Saxl.Balance.oneIf`, `OAI.Saxl.Balance.pairAtOutputTwo`, `OAI.Saxl.Balance.pairColumns`, `OAI.Saxl.Balance.pairMarks`, `OAI.Saxl.Balance.pairParts`, `OAI.Saxl.Balance.pairUpper`, `OAI.Saxl.Balance.reverseShortColumn`, `OAI.Saxl.Balance.reverseShortColumns`, `OAI.Saxl.Balance.shortColumns`, `OAI.Saxl.Balance.shortMarks`, `OAI.Saxl.Balance.shortParts`, `OAI.Saxl.Balance.twoPathLetter`, `OAI.Saxl.Band.D`, `OAI.Saxl.Band.Mat`, `OAI.Saxl.Band.Q`, `OAI.Saxl.Band.Qinv`, `OAI.Saxl.Band.ScaledBasis`, `OAI.Saxl.Band.basis`, `OAI.Saxl.Band.basisCoordinates`, `OAI.Saxl.Band.blocks`, `OAI.Saxl.Band.conjugation`, `OAI.Saxl.Band.conjugationEquiv`, `OAI.Saxl.Band.extendFourBasis`, `OAI.Saxl.Band.matrixBasisEquiv` and 298 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `Saxl_BandFactorization`, `Saxl_BandMatrices`, `Saxl_BandPairing`, `Saxl_Basic`, `Saxl_ColumnContraction`, `Saxl_CyclicSector`, `Saxl_CyclicTensor`, `Saxl_DominatedSupport`, `Saxl_HorizontalRemoval`, `Saxl_PathAlternation`, `Saxl_PathContraction`, `Saxl_PieriRestriction`, `Saxl_Polytabloid`, `Saxl_RepeatedProjection`, `Saxl_ShapeRigidity`, `Saxl_SizedStrips`, `Saxl_SpechtClassification`, `Saxl_SpechtSubmodule`, `Saxl_StripExtension`, `Saxl_StripReduction`, `Saxl_YoungRule`, `UniversalSquare_Balance_BalanceAssembly`, `UniversalSquare_Balance_BalanceBlocks`, `UniversalSquare_Balance_BalanceProjection`, `UniversalSquare_Balance_BalancedColumns`, `UniversalSquare_Balance_BalancedPairs`, `UniversalSquare_Balance_EmptyPacking`, `UniversalSquare_Balance_PackingPlans`, `UniversalSquare_Balance_WordPackingGeometry`, `UniversalSquare_Band_BandAllocation`, `UniversalSquare_Band_BandGluing`, `UniversalSquare_Band_BandGroups`, `UniversalSquare_Band_BandLetters`, `UniversalSquare_Band_BandPath`, `UniversalSquare_Band_BandPositions`, `UniversalSquare_Band_BandSplit`, `UniversalSquare_Band_CommonPath`, `UniversalSquare_Band_OddPath`, `UniversalSquare_Band_OddStrip`, `UniversalSquare_Band_OneExtra`, `UniversalSquare_Band_PathGeometry`, `UniversalSquare_Band_TwoPathGeometry`, `UniversalSquare_Capacity_Capacity`, `UniversalSquare_Capacity_Intermediate`, `UniversalSquare_Capacity_NumericBands`, `UniversalSquare_Capacity_RefinedExhaustion`, `UniversalSquare_Capacity_RegionExhaustion`, `UniversalSquare_Contraction_ChoiceContractions`, `UniversalSquare_Contraction_ColumnCertificates`, `UniversalSquare_Contraction_CompactDomainsCore`, `UniversalSquare_Contraction_DomainContractions`, `UniversalSquare_Contraction_DomainSolver`, `UniversalSquare_Contraction_PairForms`, `UniversalSquare_Contraction_PolynomialDetection`, `UniversalSquare_Contraction_RowCertificates`, `UniversalSquare_Contraction_SingletonForms`, `UniversalSquare_Contraction_SymmetricPairs`, `UniversalSquare_Contraction_VectorDomainsCore`, `UniversalSquare_Finite_DegreePlans116`, `UniversalSquare_Finite_DegreeRegionData116`, `UniversalSquare_Finite_DegreeRegionData118`, `UniversalSquare_Finite_DegreeRegionData14`, `UniversalSquare_Finite_DegreeRegionData16`, `UniversalSquare_Finite_DegreeRegionData18`, `UniversalSquare_Finite_DegreeRegionData19`, `UniversalSquare_Finite_DegreeRegionData20`, `UniversalSquare_Finite_DegreeRegionData22`, `UniversalSquare_Finite_DegreeRegionData24`, `UniversalSquare_Finite_DegreeRegionData26`, `UniversalSquare_Finite_DegreeRegionData31`, `UniversalSquare_Finite_DegreeRegionData35`, `UniversalSquare_Finite_DegreeUnionData116`, `UniversalSquare_Finite_DegreeUnionData118`, `UniversalSquare_Finite_DegreeUnionData14`, `UniversalSquare_Finite_DegreeUnionData16`, `UniversalSquare_Finite_DegreeUnionData18`, `UniversalSquare_Finite_DegreeUnionData19`, `UniversalSquare_Finite_DegreeUnionData20`, `UniversalSquare_Finite_DegreeUnionData22`, `UniversalSquare_Finite_DegreeUnionData24`, `UniversalSquare_Finite_DegreeUnionData26`, `UniversalSquare_Finite_DegreeUnionData31`, `UniversalSquare_Finite_DegreeUnionData35`, `UniversalSquare_Specht_AlternateColumns`, `UniversalSquare_Specht_ColumnRestriction`, `UniversalSquare_Specht_ColumnTensorSplit`, `UniversalSquare_Specht_FinitePieri`, `UniversalSquare_Specht_MarkedTriangle`, `UniversalSquare_Specht_NoMixedColumns`, `UniversalSquare_Specht_RepeatedColumns`, `UniversalSquare_Specht_ShortColumns`, `UniversalSquare_Specht_StandardColumns`, `UniversalSquare_Specht_ThreeRowColumns`, `UniversalSquare_Specht_ThreeRowDensity`, `UniversalSquare_Specht_ThreeRowGenerator`, `UniversalSquare_Specht_ThreeRowLocal`, `UniversalSquare_Specht_ThreeRowMasks`, `UniversalSquare_Specht_ThreeRowTensors`, `UniversalSquare_Specht_ZeroColumns`, `UniversalSquare_Support_Candidate`, `UniversalSquare_Support_ConstrainedRows`, `UniversalSquare_Support_DualTransfer`, `UniversalSquare_Support_FiniteDiagrams`, `UniversalSquare_Support_Neighboring`, `UniversalSquare_Support_NumericalSupport`, `UniversalSquare_Support_PairRun`, `UniversalSquare_Support_PairSwap`, `UniversalSquare_Support_PartWords`, `UniversalSquare_Support_ResidualTrees`, `UniversalSquare_Support_RowChecker`, `UniversalSquare_Support_RowSquareTools`, `UniversalSquare_Support_SingletonPairs`, `UniversalSquare_Support_SubdiagramSupport`, `UniversalSquare_Support_UnionRowChecker`, `UniversalSquare_Support_WordContents`, `UniversalSquare_Support_WordRelabel`.
--
--   **Imports.** It imports the published bundle `Def_UniversalTensorSquares`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ259US006`, `OAIQ259US007`, `OAIQ259US008`, `OAIQ259US009`, `OAIQ259US010`, `OAIQ259US011`, `OAIQ259US012`, `OAIQ259US013`, `OAIQ259US014`, `OAIQ259US015`, `OAIQ259US016`, `OAIQ259US017`, `OAIQ259US018`, `OAIQ259US019` and `OAIQ259US020`; the statements `OAI.Saxl.Columns.two_path_cyclic_support_placed`, `OAI_Saxl_dominated_support`, `OAI.Saxl.dominated_support_uts` and `OAI.UniversalTensorSquare.packingPlan_pos`.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_UniversalTensorSquares

section
-- module Solutions.OAIQ259_US.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/
theorem column_perm_rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : columnGroup t) (hg : rowWord t ∘ (g : Equiv.Perm (Fin n)) = rowWord t) :
    g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply t.injective
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Fin.val (congrFun hg i)
  · exact g.property i

/- The coefficient of the canonical row word in its polytabloid is one. -/
theorem polytabloid_rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t (rowWord t) = 1 := by
  classical
  unfold polytabloid
  simp only [Finset.sum_apply, Pi.smul_apply, wordRep, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  rw [Finset.sum_eq_single (1 : columnGroup t)]
  · simp
  · intro b hb hb1
    have hn : rowWord t ∘ (b : Equiv.Perm (Fin n)) ≠ rowWord t :=
      fun h => hb1 (column_perm_rowWord t b h)
    simp [hn]
  · simp


end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_Polytabloid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- A finite set is the unique maximizer of its strictly signed separator.
Used below for the Ferrers equality case in the Specht submodule theorem. -/
lemma finset_eq_of_signed_sum {X : Type uX} [DecidableEq X]
    (A B : Finset X) (w : X → ℤ)
    (hp : ∀ x ∈ B, 0 < w x) (hn : ∀ x ∉ B, w x < 0)
    (he : ∑ x ∈ A, w x = ∑ x ∈ B, w x) : A = B := by
  classical
  let f := fun x => if x ∈ A then w x else 0
  let g := fun x => if x ∈ B then w x else 0
  have hle : ∀ x ∈ A ∪ B, f x ≤ g x := by
    intro x hx
    dsimp [f, g]
    split_ifs with ha hb hb
    · rfl
    · exact (hn x hb).le
    · exact (hp x hb).le
    · rfl
  have hs : ∑ x ∈ A ∪ B, f x = ∑ x ∈ A ∪ B, g x := by
    simpa [f, g, ← Finset.sum_filter] using he
  have hh := (Finset.sum_eq_sum_iff_of_le hle).mp hs
  ext x
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B
  · simp [ha, hb]
  · have hx := hh x (Finset.mem_union_left B ha)
    have hneg := hn x hb
    simp [f, g, ha, hb] at hx
    omega
  · have hx := hh x (Finset.mem_union_right A hb)
    have hpos := hp x hb
    simp [f, g, ha, hb] at hx
    omega
  · simp [ha, hb]

/- A column-injective rearrangement of the canonical row word has precisely
Ferrers support. This is the equality-of-margins argument, without using
unproved Specht or Young-rule inputs. -/
lemma ferrers_rearrangement {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n))
    (hinj : Function.Injective (fun i => ((t (g i)).val.1, (t i).val.2))) :
    ∀ i, ((t (g i)).val.1, (t i).val.2) ∈ μ := by
  classical
  let f : Fin n → ℕ × ℕ := fun i => ((t (g i)).val.1, (t i).val.2)
  let w : ℕ × ℕ → ℤ := fun c => 2 * (μ.rowLen c.1 : ℤ) - 2 * c.2 - 1
  have ht : Function.Injective (fun i : Fin n => (t i).val) :=
    Subtype.val_injective.comp t.injective
  have himage : Finset.univ.image (fun i : Fin n => (t i).val) = μ.cells := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (t i).property
    · intro hx
      exact ⟨t.symm ⟨x, hx⟩, by simp⟩
  have he : ∑ x ∈ Finset.univ.image f, w x = ∑ x ∈ μ.cells, w x := by
    rw [← himage, Finset.sum_image (fun _ _ _ _ h => hinj h),
      Finset.sum_image (fun _ _ _ _ h => ht h)]
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Equiv.sum_comp g (fun i => (μ.rowLen (t i).val.1 : ℤ))]
  have heq := finset_eq_of_signed_sum (Finset.univ.image f) μ.cells w
    (fun c hc => by
      have h := YoungDiagram.mem_iff_lt_rowLen.mp hc
      dsimp [w]
      omega)
    (fun c hc => by
      have h : μ.rowLen c.1 ≤ c.2 :=
        le_of_not_gt (fun h => hc (YoungDiagram.mem_iff_lt_rowLen.mpr h))
      dsimp [w]
      omega) he
  intro i
  exact (le_of_eq heq) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/- The complex-valued sign character. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SpechtSubmodule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV

namespace Saxl

def tabloidSub {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :=
  cyclic (wordRep n (μ.colLen 0)) (Pi.single (rowWord t) 1)

def subrepAmbient {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (U : Subrepresentation ρ)
    (S : Subrepresentation U.toRepresentation) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.map U.toSubmodule.subtype
  apply_mem_toSubmodule g x hx := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨U.toRepresentation g y, S.apply_mem_toSubmodule g hy, rfl⟩

/- The complex polytabloid module is irreducible. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

def pathCellsEquiv (h : ℕ) : Fin (2*(h+1)+1) ≃
    {c : ℕ × ℕ // h ≤ c.1+c.2 ∧ c.1+c.2 < h+2} where
  toFun k := ⟨(h+1-(k.val+1)/2,k.val/2), by have := k.isLt; omega⟩
  invFun c := ⟨h+1-c.val.1+c.val.2, by have := c.property; omega⟩
  left_inv k := by apply Fin.ext; dsimp; have := k.isLt; omega
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> have := c.property <;> omega

/- The exact path order, starting at the bottom row singleton and ending
at the rightmost column singleton. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PathAlternation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl.PathLayer

def tag {r : ℕ} (i : Fin (2*r+1)) : ℕ := (i.val+1)/2

def base {r : ℕ} (i : Fin (2*r+1)) : Fin 2 := if i.val=0 then 0 else ⟨(i.val+1)%2, Nat.mod_lt _ (by omega)⟩

def appendPair (r : ℕ) : Fin (2*(r+1)+1) ≃ Fin (2*r+1) ⊕ Fin 2 :=
  (finCongr (by omega : 2*(r+1)+1 = (2*r+1)+2)).trans finSumFinEquiv.symm

@[simp] lemma appendPair_left (r : ℕ) (i : Fin (2*r+1)) :
    ((appendPair r).symm (Sum.inl i)).val = i.val := rfl
@[simp] lemma appendPair_right (r : ℕ) (i : Fin 2) :
    ((appendPair r).symm (Sum.inr i)).val = 2*r+1+i.val := rfl

def J : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;-1,0]

end Saxl.PathLayer

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uA

namespace Saxl.Band
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def basis (i : ℕ) : Mat :=
  match i with
  | 0 => 1
  | 1 => !![1, 0; 0, -1]
  | 2 => !![0, 1; 1, 0]
  | _ => !![0, 1; -1, 0]

def D (q : ℕ) (X : Mat) : Mat := if q % 2 = 0 then X.adjugate else X

def segment (r p : ℕ) : Mat :=
  ∑ π : Equiv.Perm (Fin r),
    ((((Equiv.Perm.sign π) : ℤ) : ℂ)) •
      (List.ofFn (fun j : Fin r => D (p + j.val) (basis (π j).val))).prod

/- Consecutive segments with the original global position parities. -/
def blocks : ℕ → List ℕ → Mat
  | _, [] => 1
  | p, r :: rs => segment r p * blocks (p + r) rs

/- Enumeration of the finite symmetric group for the four small matrix calculations. -/

def ScaledBasis (X : Mat) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∃ i : Fin 4, X = c • basis i.val

def Q : Mat := !![1, 1; 1, 2]
def Qinv : Mat := !![2, -1; -1, 1]

lemma Q_mul_Qinv : Q * Qinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two])

lemma Qinv_mul_Q : Qinv * Q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two])

end Saxl.Band

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PathContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Path
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Letter := Fin 4

def parts (x : Letter) : Fin 2 × Fin 2 := finProdFinEquiv.symm x
def J : Mat := !![0, 1; -1, 0]

def leftPos {r : ℕ} (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val, by omega⟩
def midPos {r : ℕ} (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val + 1, by omega⟩
def rightPos {r : ℕ} (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val + 2, by omega⟩

/- EXACT coefficients of the path-ordered alternating band: the two endpoint
singletons carry letter 0, and row/column pairs have coefficients J. Here r=m-1. -/
def bandWord (r : ℕ) (w : Fin (2 * r + 1) → Letter) : ℂ :=
  (if (parts (w 0)).1 = 0 then 1 else 0) *
  (if (parts (w (Fin.last (2 * r)))).2 = 0 then 1 else 0) *
  ∏ i : Fin r, J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
    J (parts (w (midPos i))).1 (parts (w (rightPos i))).1

/- Ordinary pure position tensor pairing, with no conjugation. -/
def pureWord {n : ℕ} (X : Fin n → Mat) (w : Fin n → Letter) : ℂ :=
  ∏ i, X i (parts (w i)).1 (parts (w i)).2

def entry (a : Letter) : Mat := Matrix.single (parts a).1 (parts a).2 1

def DL (q : ℕ) : Mat →ₗ[ℂ] Mat where
  toFun := Band.D q
  map_add' X Y := by
    by_cases h : q % 2 = 0
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Band.D, h, Matrix.adjugate_fin_two, add_comm]
    · simp [Band.D, h]
  map_smul' c X := by
    by_cases h : q % 2 = 0
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Band.D, h, Matrix.adjugate_fin_two]
    · simp [Band.D, h]

def chainML (n p : ℕ) : MultilinearMap ℂ (fun _ : Fin n => Mat) Mat :=
  (MultilinearMap.mkPiAlgebraFin ℂ n Mat).compLinearMap (fun i => DL (p + i.val))

end Saxl.Path

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_ColumnContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/
def segments : ℕ → List ℕ → (ℕ → Band.Mat) → Band.Mat
  | _, [], _ => 1
  | p, r :: rs, N =>
      (∑ π : Equiv.Perm (Fin r), (((Equiv.Perm.sign π : ℤ) : ℂ)) •
        (List.ofFn fun i : Fin r => Band.D (p + i.val) (N (π i).val)).prod) *
      segments (p+r) rs N

/- Factorization over independent column permutations, without commuting factors. -/

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Band

def conjugation : Mat →ₗ[ℂ] Mat where
  toFun X := Q * X * Qinv
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

end Saxl.Band

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

/- Explicit finite-group induction on a linear map. -/
def averagedMap {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) (f : X →ₗ[ℂ] Y) :
    Representation.IntertwiningMap ρ σ where
  toLinearMap := ∑ g : G, (σ g).comp (f.comp (ρ g⁻¹))
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
    rw [map_sum]
    apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
    apply Finset.sum_congr rfl
    intro g hg
    change σ (h*g) (f (ρ (h*g)⁻¹ (ρ h x))) = σ h (σ g (f (ρ g⁻¹ x)))
    simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
    have he : ρ h⁻¹ (ρ h x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [he]

open scoped MonoidAlgebra

end Saxl

namespace Saxl

def wordSector {n d : ℕ} (D : Fin n → Prop) (A : Fin d → Prop)
    (w : Fin n → Fin d) : Prop := ∀ i, A (w i) ↔ D i

/- Concrete sector averaging produces a constituent of the full cyclic
module from an equivariant map on its coordinate sector. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_ShapeRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uV uW

namespace Saxl

def rowMoment (μ : YoungDiagram) : ℤ := ∑ c ∈ μ.cells, (c.1 : ℤ)

lemma finset_signed_sum_le {X : Type uX} [DecidableEq X]
    (A B : Finset X) (w : X → ℤ)
    (hp : ∀ x ∈ B, 0 ≤ w x) (hn : ∀ x ∉ B, w x ≤ 0) :
    ∑ x ∈ A, w x ≤ ∑ x ∈ B, w x := by
  classical
  have hle : ∀ x ∈ A ∪ B,
      (if x ∈ A then w x else 0) ≤ (if x ∈ B then w x else 0) := by
    intro x hx
    split_ifs with ha hb hb
    · rfl
    · exact hn x hb
    · exact hp x hb
    · rfl
  simpa [← Finset.sum_filter] using Finset.sum_le_sum hle

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SpechtClassification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV uG

namespace Saxl

/- Rows enumerate exactly the actual cells, including the empty diagram. -/
def rowCellEquiv (μ : YoungDiagram) : μ.cells ≃ (i : Fin (μ.colLen 0)) × Fin (μ.rowLen i) where
  toFun c := ⟨⟨c.val.1, YoungDiagram.mem_iff_lt_colLen.mp
      (μ.up_left_mem le_rfl (Nat.zero_le _) c.property)⟩,
    ⟨c.val.2, YoungDiagram.mem_iff_lt_rowLen.mp c.property⟩⟩
  invFun c := ⟨(c.1.val, c.2.val), YoungDiagram.mem_iff_lt_rowLen.mpr c.2.isLt⟩
  left_inv c := Subtype.ext rfl
  right_inv c := by rcases c with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; rfl

lemma card_eq_sum_rowLens (μ : YoungDiagram) : μ.card = μ.rowLens.sum := by
  classical
  have h := Fintype.card_congr (rowCellEquiv μ)
  simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_fin] at h
  change μ.card = ∑ x : Fin (μ.colLen 0), μ.rowLen x at h
  rw [h, YoungDiagram.rowLens]
  rw [← List.sum_toFinset _ List.nodup_range]
  have he : (List.range (μ.colLen 0)).toFinset = Finset.range (μ.colLen 0) := by
    ext i; simp
  rw [he]
  exact Fin.sum_univ_eq_sum_range μ.rowLen (μ.colLen 0)

/- Conversion from Mathlib's partition type to its Young diagram. -/
def partitionDiagram {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

lemma partitionDiagram_rowLens {n : ℕ} (p : Nat.Partition n) :
    (partitionDiagram p).rowLens = p.parts.sort (· ≥ ·) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro a ha
  exact p.parts_pos (by simpa only [← Multiset.mem_coe, Multiset.sort_eq] using ha)

lemma partitionDiagram_card {n : ℕ} (p : Nat.Partition n) : (partitionDiagram p).card = n := by
  rw [card_eq_sum_rowLens, partitionDiagram_rowLens, ← Multiset.sum_coe,
    Multiset.sort_eq, p.parts_sum]

lemma partitionDiagram_injective {n : ℕ} :
    Function.Injective (partitionDiagram (n := n)) := by
  intro p q h
  apply Nat.Partition.ext
  have he := congrArg (fun μ => (μ.rowLens : Multiset ℕ)) h
  simpa only [partitionDiagram_rowLens, Multiset.sort_eq] using he

def permPartition {n : ℕ} (g : Equiv.Perm (Fin n)) : Nat.Partition n :=
  ⟨g.partition.parts, g.partition.parts_pos, g.partition.parts_sum.trans (Fintype.card_fin n)⟩

lemma isConj_of_permPartition_eq {n : ℕ} {g h : Equiv.Perm (Fin n)}
    (hh : permPartition g = permPartition h) : IsConj g h := by
  apply Equiv.Perm.partition_eq_of_isConj.mpr
  have hp := congrArg (fun p : Nat.Partition n => p.parts) hh
  exact Nat.Partition.ext hp

/- Class functions on the symmetric group, indexed by cycle type. -/
def classFunctions (n : ℕ) : Submodule ℂ (Equiv.Perm (Fin n) → ℂ) where
  carrier := {f | ∀ g h, permPartition g = permPartition h → f g = f h}
  zero_mem' := by
    change ∀ g h, permPartition g = permPartition h → (0 : Equiv.Perm (Fin n) → ℂ) g = 0
    intro g h hh; rfl
  add_mem' := by intro f h hf hh g k hk; simp only [Pi.add_apply, hf g k hk, hh g k hk]
  smul_mem' := by intro c f hf g k hk; simp only [Pi.smul_apply, hf g k hk]

/- Select one representative where a cycle partition is realized; unused
coordinates are zero. This gives an injection even without surjectivity of
cycle-type realization. -/
def classEvaluation (n : ℕ) : (classFunctions n) →ₗ[ℂ] (Nat.Partition n → ℂ) where
  toFun f p := if h : ∃ g : Equiv.Perm (Fin n), permPartition g = p then f.val h.choose else 0
  map_add' f h := by
    ext p
    simp only [Pi.add_apply, Submodule.coe_add]
    split_ifs <;> simp
  map_smul' c f := by
    ext p
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply]
    split_ifs <;> simp

lemma classEvaluation_injective (n : ℕ) : Function.Injective (classEvaluation n) := by
  intro f h he
  apply Subtype.ext
  funext g
  have hh := congrFun he (permPartition g)
  have hex : ∃ k : Equiv.Perm (Fin n), permPartition k = permPartition g := ⟨g, rfl⟩
  change (if hc : ∃ k : Equiv.Perm (Fin n), permPartition k = permPartition g then
    f.val hc.choose else 0) = (if hc : ∃ k : Equiv.Perm (Fin n), permPartition k = permPartition g then
    h.val hc.choose else 0) at hh
  rw [dite_eq_left hex, dite_eq_left hex] at hh
  exact (f.property _ _ hex.choose_spec).symm.trans (hh.trans (h.property _ _ hex.choose_spec))

lemma classFunctions_finrank_le (n : ℕ) :
    Module.finrank ℂ (classFunctions n) ≤ Fintype.card (Nat.Partition n) := by
  have h := LinearMap.finrank_le_finrank_of_injective (classEvaluation_injective n)
  simpa using h

lemma char_mem_classFunctions {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    ρ.character ∈ classFunctions n := by
  intro g h he
  obtain ⟨k, rfl⟩ := isConj_iff.mp (isConj_of_permPartition_eq he)
  exact (Representation.char_conj ρ g k).symm

/- Character of the actual Specht module as an actual class function. -/
def charFunctional {G : Type uG} [Group G] [Fintype G] (y : G → ℂ) : (G → ℂ) →ₗ[ℂ] ℂ where
  toFun x := (Nat.card G : ℂ)⁻¹ * ∑ g, x g * y g⁻¹
  map_add' x z := by simp [Finset.sum_add_distrib, add_mul, mul_add]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc, mul_left_comm]

lemma complex_card_ne_zero (G : Type uG) [Group G] [Fintype G] : (Nat.card G : ℂ) ≠ 0 := by
  exact_mod_cast Nat.card_pos.ne'

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PieriRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A horizontal strip removes at most one cell in each column. -/
def HorizontalStrip (ν μ : YoungDiagram) : Prop :=
  ν ≤ μ ∧ ∀ x ∈ μ, x ∉ ν → ∀ y ∈ μ, y ∉ ν → x.2 = y.2 → x = y

/- Position embedding induced by inclusion of the actual Young diagrams. -/

lemma colLen_mono {ν μ : YoungDiagram} (h : ν ≤ μ) (j : ℕ) :
    ν.colLen j ≤ μ.colLen j := by
  by_contra hn
  have hm : (μ.colLen j, j) ∈ ν := YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_not_ge hn)
  exact (lt_irrefl _) (YoungDiagram.mem_iff_lt_colLen.mp (h hm))

def rowLetterInclusion {ν μ : YoungDiagram} (h : ν ≤ μ) : Fin (ν.colLen 0) ↪ Fin (μ.colLen 0) :=
  Fin.castLEEmb (colLen_mono h 0)

/- Restrict letters on a specified position set, and sum over all other letters.
This is precisely contraction with the all-ones functional at deleted positions. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_StripExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

def restrictPerm {a n : ℕ} (i : Fin a ↪ Fin n) (g : Equiv.Perm (Fin n))
    (hg : ∀ x, g x ∈ Set.range i ↔ x ∈ Set.range i) : Equiv.Perm (Fin a) :=
  (Equiv.ofInjective i i.injective).trans ((g.subtypePerm hg).trans
    (Equiv.ofInjective i i.injective).symm)

def extendColor {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ) : Fin n → ℕ :=
  fun x => if h : x ∈ Set.range i then c ((Equiv.ofInjective i i.injective).symm ⟨x,h⟩) else q

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SizedStrips
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

inductive SizedStripChain : List ℕ → YoungDiagram → YoungDiagram → Prop
  | nil (μ) : SizedStripChain [] μ μ
  | snoc {bs ν η μ b} : SizedStripChain bs ν η → HorizontalStrip η μ →
      η.card + b = μ.card → SizedStripChain (bs ++ [b]) ν μ

lemma SizedStripChain.le {bs ν μ} (hs : SizedStripChain bs ν μ) : ν ≤ μ := by
  induction hs with
  | nil => exact le_rfl
  | snoc hs hh hc ih => exact ih.trans hh.1

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_HorizontalRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
def rowPrefix (μ : YoungDiagram) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, μ.rowLen i

def Dominates (μ ν : YoungDiagram) : Prop := ∀ k, rowPrefix ν k ≤ rowPrefix μ k

lemma rowLen_zero_of_height_le (μ : YoungDiagram) {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  have hm := YoungDiagram.mem_iff_lt_rowLen.mpr h
  have hh := YoungDiagram.mem_iff_lt_colLen.mp hm
  omega

lemma rowPrefix_eq_card (μ : YoungDiagram) {k : ℕ} (hk : μ.colLen 0 ≤ k) :
    rowPrefix μ k = μ.card := by
  have he : μ.card = ∑ i : Fin (μ.colLen 0), μ.rowLen i := by
    have hh := Fintype.card_congr (rowCellEquiv μ)
    simpa using hh
  rw [he, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hk)
  intro i hik hin
  exact rowLen_zero_of_height_le μ (by simpa using hin)

/- Tallest-column bottom deletion, expressed by interlacing rows. -/
def stripRow (μ : YoungDiagram) (t i : ℕ) := μ.rowLen i - t + min t (μ.rowLen (i+1))

lemma stripRow_antitone (μ : YoungDiagram) (t : ℕ) : Antitone (stripRow μ t) := by
  intro i j hij
  exact Nat.add_le_add (Nat.sub_le_sub_right (μ.rowLen_anti i j hij) t)
    (min_le_min_left t (μ.rowLen_anti (i+1) (j+1) (by omega)))

def stripRemove (μ : YoungDiagram) (t : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun x => x.2 < stripRow μ t x.1)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨μ.up_left_mem hxy.1 hxy.2 hy.1,
      lt_of_le_of_lt hxy.2 (lt_of_lt_of_le hy.2 (stripRow_antitone μ t hxy.1))⟩

def rowTruncate (μ : YoungDiagram) (k : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun x => x.1 < k)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨μ.up_left_mem hxy.1 hxy.2 hy.1, lt_of_le_of_lt hxy.1 hy.2⟩

@[simp] lemma mem_rowTruncate {μ : YoungDiagram} {k i j : ℕ} :
    (i,j) ∈ rowTruncate μ k ↔ (i,j) ∈ μ ∧ i < k := by
  change (i,j) ∈ μ.cells.filter (fun x => x.1 < k) ↔ (i,j) ∈ μ.cells ∧ i < k
  exact Finset.mem_filter

lemma rowTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (rowTruncate μ k).rowLen i = if i < k then μ.rowLen i else 0 := by
  have hh : ∀ j, j < (rowTruncate μ k).rowLen i ↔ j < if i < k then μ.rowLen i else 0 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_rowTruncate, YoungDiagram.mem_iff_lt_rowLen]
    split_ifs <;> simp_all
  have h₁ := hh ((rowTruncate μ k).rowLen i)
  have h₂ := hh (if i < k then μ.rowLen i else 0)
  omega

lemma rowTruncate_height (μ : YoungDiagram) (k : ℕ) : (rowTruncate μ k).colLen 0 ≤ k := by
  by_contra h
  have hm : (k,0) ∈ rowTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  exact Nat.lt_irrefl k (mem_rowTruncate.mp hm).2

lemma rowTruncate_prefix (μ : YoungDiagram) (k q : ℕ) (hq : q ≤ k) :
    rowPrefix (rowTruncate μ k) q = rowPrefix μ q := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [rowTruncate_rowLen, ite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hi) hq)]

lemma rowTruncate_card (μ : YoungDiagram) (k : ℕ) :
    (rowTruncate μ k).card = rowPrefix μ k := by
  rw [← rowPrefix_eq_card _ (rowTruncate_height μ k), rowTruncate_prefix _ _ _ le_rfl]

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_YoungRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Horizontal-strip chains recording the exact ordered strip sizes. -/
def rowWeights (θ : YoungDiagram) : ℕ → List ℕ
  | 0 => []
  | k+1 => rowWeights θ k ++ [θ.rowLen k]



lemma rowWeights_length (θ : YoungDiagram) (k : ℕ) : (rowWeights θ k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rowWeights, List.length_append, List.length_singleton, ih]

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY

namespace Saxl

def equivOfSubrepEq {G : Type uG} {X : Type uX} [Group G] [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ G X} (S T : Subrepresentation ρ) (h : S = T) :
    Representation.Equiv S.toRepresentation T.toRepresentation := by
  subst T
  exact Representation.Equiv.refl _

/- Positive Young rule as a concrete orbit map (including reordered contents). -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_RepeatedProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

lemma weighted_perm_sum {X : Type uX} [Fintype X] (t a : X → ℝ)
    (g : Equiv.Perm X) (hg : ∀ i, t (g i) = t i) :
    ∑ i, t i * a (g i) = ∑ i, t i * a i := by
  simpa only [hg] using Equiv.sum_comp g (fun i => t i * a i)

/- The strict square-moment equality used in the dominance projection.
The labels may be real; the application uses actual nonnegative integer letters. -/
theorem pair_sum_rigidity {X : Type uX} [Fintype X]
    (a t c : X → ℝ) (ω g h k : Equiv.Perm X)
    (hω : ∀ i, t (ω i) = t i) (hcomp : ∀ i, a i + a (ω i) = t i)
    (hg : ∀ i, t (g i) = t i) (hh : ∀ i, t (h i) = t i)
    (hc : ∀ i, c i = a (g i) + a (h i)) (hk : ∀ i, c i = t (k i)) : c = t := by
  have hbase : 2 * (∑ i, t i * a i) = ∑ i, t i ^ 2 := by
    have he := weighted_perm_sum t a ω hω
    have hs : (∑ i, t i * a i) + (∑ i, t i * a (ω i)) = ∑ i, t i ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_add, hcomp i, pow_two]
    linarith
  have hcross : ∑ i, t i * c i = ∑ i, t i ^ 2 := by
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib, weighted_perm_sum t a g hg, weighted_perm_sum t a h hh]
    linarith
  have hsquare : ∑ i, c i ^ 2 = ∑ i, t i ^ 2 := by
    simp only [hk]
    exact Equiv.sum_comp k (fun i => t i ^ 2)
  have hsum : ∑ i, (c i - t i) ^ 2 = 0 := by
    calc
      (∑ i, (c i - t i) ^ 2) = (∑ i, c i ^ 2) - 2 * (∑ i, t i * c i) +
          (∑ i, t i ^ 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hsquare, hcross]; ring
  funext i
  have hz : (c i - t i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j-t j))).mp hsum i
      (Finset.mem_univ i)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

end Saxl

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/

def wordOrbit {n d : ℕ} (t : Fin n → Fin d) (c : Fin n → Fin d) : Prop :=
  ∃ g : Equiv.Perm (Fin n), c = t ∘ g

lemma wordOrbit_perm {n d : ℕ} (t c : Fin n → Fin d) (g : Equiv.Perm (Fin n)) :
    wordOrbit t (c ∘ g) ↔ wordOrbit t c := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h*g⁻¹, ?_⟩
    funext i
    have he := congrFun hh (g⁻¹ i)
    simpa using he
  · rintro ⟨h, rfl⟩
    exact ⟨h*g, rfl⟩

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_DominatedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

lemma transpose_card (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  change ((Equiv.prodComm ℕ ℕ).finsetCongr μ.cells).card = μ.cells.card
  simp only [Equiv.finsetCongr_apply, Finset.card_map]

def colTruncate (μ : YoungDiagram) (k : ℕ) := (rowTruncate μ.transpose k).transpose

open scoped MonoidAlgebra

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_StripReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
inductive StripChain : ℕ → YoungDiagram → YoungDiagram → Prop
  | nil (μ) : StripChain 0 μ μ
  | snoc {q ν η μ} : StripChain q ν η → HorizontalStrip η μ → η ≠ μ → StripChain (q+1) ν μ


end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OddPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Odd Path. -/

section

noncomputable section
namespace Saxl.Band

def basisCoordinates : Mat →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun X := ![(X 0 0 + X 1 1)/2, (X 0 0 - X 1 1)/2,
    (X 0 1 + X 1 0)/2, (X 0 1 - X 1 0)/2]
  map_add' X Y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c X := by
    ext i
    fin_cases i <;> simp <;> ring

def matrixBasisEquiv : (Fin 4 → ℂ) ≃ₗ[ℂ] Mat where
  toFun c := ∑ i : Fin 4, c i • basis i.val
  invFun := basisCoordinates
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c d := by simp [smul_smul, Finset.smul_sum]
  left_inv c := by
    ext i
    fin_cases i <;>
      simp [basisCoordinates, Fin.sum_univ_succ, basis] <;> ring
  right_inv X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [basisCoordinates, Fin.sum_univ_succ, basis] <;> ring

def conjugationEquiv : Mat ≃ₗ[ℂ] Mat where
  toLinearMap := conjugation
  invFun X := Qinv * X * Q
  left_inv X := by
    change Qinv * (Q * X * Qinv) * Q = X
    simp only [mul_assoc, Qinv_mul_Q, mul_one]
    rw [← mul_assoc Qinv Q X, Qinv_mul_Q, one_mul]
  right_inv X := by
    change Q * (Qinv * X * Q) * Qinv = X
    simp only [mul_assoc, Q_mul_Qinv, mul_one]
    rw [← mul_assoc Q Qinv X, Q_mul_Qinv, one_mul]

def pathBasis : Module.Basis (Fin 4) ℂ Mat :=
  (Pi.basisFun ℂ (Fin 4)).map (matrixBasisEquiv.trans conjugationEquiv)

end Saxl.Band

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_RepeatedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma paired_relation_iff_free {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : ∀ g h : H, a ∘ g.val = a ∘ h.val → g = h)
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    (∀ i, (a (g.val i)).val + (a (h.val i)).val = (t i).val) ↔ h = ω*g := by
  constructor
  · intro hh
    apply ha
    funext i
    apply Fin.ext
    have he := hω (g.val i)
    rw [ht g i] at he
    exact Nat.add_left_cancel ((hh i).trans he.symm)
  · rintro rfl i
    have he := hω (g.val i)
    rw [ht g i] at he
    exact he

def columnReversalCell (α : YoungDiagram) (x : α.cells) : α.cells :=
  ⟨(α.colLen x.val.2 - 1 - x.val.1, x.val.2), by
    have hx : x.val.1 < α.colLen x.val.2 := YoungDiagram.mem_iff_lt_colLen.mp x.property
    apply YoungDiagram.mem_iff_lt_colLen.mpr
    omega⟩

lemma columnReversalCell_involutive (α : YoungDiagram) :
    Function.Involutive (columnReversalCell α) := by
  intro x
  have hx : x.val.1 < α.colLen x.val.2 := YoungDiagram.mem_iff_lt_colLen.mp x.property
  apply Subtype.ext
  apply Prod.ext
  · change α.colLen x.val.2 - 1 - (α.colLen x.val.2 - 1 - x.val.1) = x.val.1
    omega
  · rfl

def columnReversalEquiv (α : YoungDiagram) : Equiv.Perm α.cells :=
  ⟨columnReversalCell α, columnReversalCell α,
    columnReversalCell_involutive α, columnReversalCell_involutive α⟩

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_PolynomialDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def jointContent {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    (Fin d × Fin e) →₀ ℕ := ∑ i, Finsupp.single (a i, b i) 1

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ZeroColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero Columns. -/

section

noncomputable section
namespace Saxl.Columns

def positiveSorted (rs : List ℕ) : List ℕ :=
  (↑(rs.filter (fun a => 0 < a)) : Multiset ℕ).sort (· ≥ ·)

lemma positiveSorted_perm (rs : List ℕ) :
    (rs.filter (fun a => 0 < a)).Perm (positiveSorted rs) := by
  apply Multiset.coe_eq_coe.mp
  simp only [positiveSorted, Multiset.sort_eq]

lemma positiveSorted_sorted (rs : List ℕ) : (positiveSorted rs).SortedGE :=
  (Multiset.pairwise_sort _ _).sortedGE

lemma positiveSorted_pos (rs : List ℕ) (a : ℕ) (ha : a ∈ positiveSorted rs) : 0 < a := by
  have hm := (positiveSorted_perm rs).mem_iff.mpr ha
  exact of_decide_eq_true (List.mem_filter.mp hm).2

def columnShape (rs : List ℕ) : YoungDiagram :=
  (YoungDiagram.ofRowLens (positiveSorted rs) (positiveSorted_sorted rs)).transpose

lemma columnShape_cols (rs : List ℕ) :
    (columnShape rs).transpose.rowLens = positiveSorted rs := by
  simp only [columnShape, YoungDiagram.transpose_transpose]
  exact YoungDiagram.rowLens_ofRowLens_eq_self (positiveSorted_pos rs)

def rowFiberEquiv (μ : YoungDiagram) (i : ℕ) :
    {c : μ.cells // c.val.1 = i} ≃ Fin (μ.rowLen i) where
  toFun c := ⟨c.val.val.2,YoungDiagram.mem_iff_lt_rowLen.mp (by
    have hc : (c.val.val.1,c.val.val.2) ∈ μ := c.val.property
    rwa [c.property] at hc)⟩
  invFun j := ⟨⟨(i,j.val),YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩,rfl⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext c.property.symm rfl
  right_inv j := by rfl

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SymmetricPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def halfRows (μ : YoungDiagram) : YoungDiagram where
  cells := μ.cells.filter (fun c => 2*c.2+1 < μ.rowLen c.1)
  isLowerSet := by
    intro x y hxy hy
    obtain ⟨hym,hy⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_filter.mpr ⟨μ.up_left_mem hxy.1 hxy.2 hym, ?_⟩
    have hm := μ.rowLen_anti _ _ hxy.1
    have hj := hxy.2
    omega

lemma mem_halfRows (μ : YoungDiagram) (i j : ℕ) :
    (i,j) ∈ halfRows μ ↔ 2*j+1 < μ.rowLen i := by
  change (i,j) ∈ μ.cells.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega),h⟩⟩

lemma halfRows_height (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i)) :
    (halfRows μ).colLen 0 = μ.colLen 0 := by
  have hh : ∀ i, i < (halfRows μ).colLen 0 ↔ i < μ.colLen 0 := by
    intro i
    rw [← YoungDiagram.mem_iff_lt_colLen, ← YoungDiagram.mem_iff_lt_colLen,
      mem_halfRows, YoungDiagram.mem_iff_lt_rowLen]
    obtain ⟨k,hk⟩ := he i
    omega
  have h₁ := hh ((halfRows μ).colLen 0)
  have h₂ := hh (μ.colLen 0)
  omega

def pairedCells (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i)) :
    (halfRows μ).cells ⊕ (halfRows μ).cells ≃ μ.cells where
  toFun := Sum.elim
    (fun c => ⟨(c.val.1,2*c.val.2), YoungDiagram.mem_iff_lt_rowLen.mpr (by
      have h : 2*c.val.2+1 < μ.rowLen c.val.1 := (mem_halfRows μ _ _).mp c.property
      change 2*c.val.2 < μ.rowLen c.val.1
      omega)⟩)
    (fun c => ⟨(c.val.1,2*c.val.2+1), YoungDiagram.mem_iff_lt_rowLen.mpr
      ((mem_halfRows μ _ _).mp c.property)⟩)
  invFun c :=
    if h : c.val.2 % 2 = 0 then Sum.inl ⟨(c.val.1,c.val.2/2), (mem_halfRows μ _ _).mpr (by
      have hc : c.val.2 < μ.rowLen c.val.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.property
      obtain ⟨k,hk⟩ := he c.val.1
      change 2*(c.val.2/2)+1 < μ.rowLen c.val.1
      omega)⟩
    else Sum.inr ⟨(c.val.1,c.val.2/2), (mem_halfRows μ _ _).mpr (by
      have hc : c.val.2 < μ.rowLen c.val.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.property
      change 2*(c.val.2/2)+1 < μ.rowLen c.val.1
      omega)⟩
  left_inv c := by
    cases c with
    | inl c => simp
    | inr c =>
      simp
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change (2*c.val.2+1)/2 = c.val.2
        omega
  right_inv c := by
    dsimp only
    split_ifs with h
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · change 2*(c.val.2/2) = c.val.2
        change c.val.2 % 2 = 0 at h
        omega
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · change 2*(c.val.2/2)+1 = c.val.2
        change c.val.2 % 2 ≠ 0 at h
        omega

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_AlternateColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Alternate Columns. -/

section

noncomputable section
namespace Saxl

def ceilRows (μ : YoungDiagram) : YoungDiagram where
  cells := μ.cells.filter (fun c => 2*c.2 < μ.rowLen c.1)
  isLowerSet := by
    intro x y hxy hy
    obtain ⟨hym,hy⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_filter.mpr ⟨μ.up_left_mem hxy.1 hxy.2 hym, ?_⟩
    have hm := μ.rowLen_anti _ _ hxy.1
    have hj := hxy.2
    omega

lemma mem_ceilRows (μ : YoungDiagram) (i j : ℕ) :
    (i,j) ∈ ceilRows μ ↔ 2*j < μ.rowLen i := by
  change (i,j) ∈ μ.cells.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega),h⟩⟩

lemma ceilRows_height (μ : YoungDiagram) : (ceilRows μ).colLen 0 = μ.colLen 0 := by
  have hh : ∀ i, i < (ceilRows μ).colLen 0 ↔ i < μ.colLen 0 := by
    intro i
    rw [← YoungDiagram.mem_iff_lt_colLen, mem_ceilRows]
    norm_num only [mul_zero]
    rw [← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]
  have h₁ := hh ((ceilRows μ).colLen 0)
  have h₂ := hh (μ.colLen 0)
  omega

lemma halfRows_le_ceilRows (μ : YoungDiagram) : halfRows μ ≤ ceilRows μ := by
  intro c hc
  have hl := (mem_halfRows μ c.1 c.2).mp hc
  exact (mem_ceilRows μ c.1 c.2).mpr (by omega)

def alternateCells (μ : YoungDiagram) :
    (ceilRows μ).cells ⊕ (halfRows μ).cells ≃ μ.cells where
  toFun := Sum.elim
    (fun c => ⟨(c.val.1,2*c.val.2), YoungDiagram.mem_iff_lt_rowLen.mpr
      ((mem_ceilRows μ _ _).mp c.property)⟩)
    (fun c => ⟨(c.val.1,2*c.val.2+1), YoungDiagram.mem_iff_lt_rowLen.mpr
      ((mem_halfRows μ _ _).mp c.property)⟩)
  invFun c :=
    if h : c.val.2 % 2 = 0 then Sum.inl ⟨(c.val.1,c.val.2/2), (mem_ceilRows μ _ _).mpr (by
      have hc : c.val.2 < μ.rowLen c.val.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.property
      change 2*(c.val.2/2) < μ.rowLen c.val.1
      omega)⟩
    else Sum.inr ⟨(c.val.1,c.val.2/2), (mem_halfRows μ _ _).mpr (by
      have hc : c.val.2 < μ.rowLen c.val.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.property
      change 2*(c.val.2/2)+1 < μ.rowLen c.val.1
      omega)⟩
  left_inv c := by
    cases c with
    | inl c => simp
    | inr c =>
      simp
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change (2*c.val.2+1)/2 = c.val.2
        omega
  right_inv c := by
    dsimp only
    split_ifs with h
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · change 2*(c.val.2/2) = c.val.2
        change c.val.2 % 2 = 0 at h
        omega
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · change 2*(c.val.2/2)+1 = c.val.2
        change c.val.2 % 2 ≠ 0 at h
        omega

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SingletonPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton Pairs. -/

section

noncomputable section
namespace Saxl

lemma odd_row_lt_height {μ : YoungDiagram} {k : ℕ} (hk : Odd (μ.rowLen k)) :
    k < μ.colLen 0 := by
  apply YoungDiagram.mem_iff_lt_colLen.mp
  apply YoungDiagram.mem_iff_lt_rowLen.mpr
  obtain ⟨q,hq⟩ := hk
  omega

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_StandardColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Standard Columns. -/

section

noncomputable section
namespace Saxl.FlagColumns
open Columns

def standard (d : ℕ) (i : ℕ) (a : Fin d) : ℂ := if i = a.val then 1 else 0

def appendPositions (rs ss : List ℕ) : Fin (rs ++ ss).sum ≃ Fin rs.sum ⊕ Fin ss.sum :=
  (finCongr (show (rs ++ ss).sum = rs.sum + ss.sum from List.sum_append)).trans finSumFinEquiv.symm

@[simp] lemma appendPositions_left_val (rs ss : List ℕ) (i : Fin rs.sum) :
    ((appendPositions rs ss).symm (Sum.inl i)).val = i.val := rfl

@[simp] lemma appendPositions_right_val (rs ss : List ℕ) (i : Fin ss.sum) :
    ((appendPositions rs ss).symm (Sum.inr i)).val = rs.sum+i.val := rfl

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_PairForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Forms. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def shortPairForm : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,1; 0,0,-1,0; 0,-1,0,0; 1,0,0,0]

def shortPairCongruence : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,Complex.I,0,0; 0,0,1,Complex.I; 0,0,-1,Complex.I; 1,-Complex.I,0,0]

def outputTwoForm : Matrix (Fin 2) (Fin 2) ℂ := !![0,1; 1,0]

def outputTwoCongruence : Matrix (Fin 2) (Fin 2) ℂ := !![1,Complex.I; 1,-Complex.I]

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SingletonForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton Forms. -/

section

noncomputable section
namespace Saxl

def pairSingletonEquiv {n a m : ℕ} (e : Fin n ≃ Fin a ⊕ Fin 1)
    (p : Fin a ≃ Fin m ⊕ Fin m) : Fin n ≃ Fin (m+1) ⊕ Fin m :=
  e.trans ((Equiv.sumCongr p (Equiv.refl _)).trans
    ((Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _)
      (Equiv.sumComm _ _)).trans ((Equiv.sumAssoc _ _ _).symm.trans
        (Equiv.sumCongr finSumFinEquiv (Equiv.refl _))))))

@[simp] lemma pairSingletonEquiv_left {n a m : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m) (k : Fin m) :
    (pairSingletonEquiv e p).symm (Sum.inl k.castSucc) =
      e.symm (Sum.inl (p.symm (Sum.inl k))) := by
  change (pairSingletonEquiv e p).symm (Sum.inl (Fin.castAdd 1 k)) = _
  simp [pairSingletonEquiv]

@[simp] lemma pairSingletonEquiv_right {n a m : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m) (k : Fin m) :
    (pairSingletonEquiv e p).symm (Sum.inr k) =
      e.symm (Sum.inl (p.symm (Sum.inr k))) := by
  simp [pairSingletonEquiv]

@[simp] lemma pairSingletonEquiv_last {n a m : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m) :
    (pairSingletonEquiv e p).symm (Sum.inl (Fin.last m)) = e.symm (Sum.inr 0) := by
  have hh : Fin.last m = Fin.natAdd m (0 : Fin 1) := Fin.ext (by simp)
  rw [hh]
  simp [pairSingletonEquiv]

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ShortColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short Columns. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl.ShortColumns

def shape (b δ : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens [b+δ,b] (by apply List.Pairwise.sortedGE; simp)

lemma mem_shape (b δ i j : ℕ) :
    (i,j) ∈ shape b δ ↔ (i = 0 ∧ j < b+δ) ∨ (i = 1 ∧ j < b) := by
  simp only [shape, YoungDiagram.mem_ofRowLens, List.length_cons, List.length_nil]
  constructor
  · rintro ⟨h,hj⟩
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> simp_all
  · rintro (⟨rfl,h⟩ | ⟨rfl,h⟩) <;> simp_all

lemma height_le (b δ : ℕ) : (shape b δ).colLen 0 ≤ 2 := by
  by_contra h
  have hm : (2,0) ∈ shape b δ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  simp only [mem_shape] at hm
  omega

def oddSplit (b : ℕ) : Fin (2*b+1) ≃ Fin (2*b) ⊕ Fin 1 :=
  (finCongr (by omega : 2*b+1 = 1+2*b)).trans <|
  (finSumFinEquiv : Fin 1 ⊕ Fin (2*b) ≃ Fin (1+2*b)).symm.trans
    (Equiv.sumComm _ _)

@[simp] lemma oddSplit_left (b : ℕ) (i : Fin (2*b)) :
    ((oddSplit b).symm (Sum.inl i)).val = i.val+1 := by
  change 1+i.val = i.val+1
  omega

@[simp] lemma oddSplit_right (b : ℕ) :
    (oddSplit b).symm (Sum.inr (0 : Fin 1)) = 0 := rfl

def pairSplit (b : ℕ) : Fin (2*b) ≃ Fin b ⊕ Fin b where
  toFun i := if h : i.val % 2 = 0 then Sum.inl ⟨i.val/2, by omega⟩
    else Sum.inr ⟨i.val/2, by omega⟩
  invFun := Sum.elim (fun i => ⟨2*i.val,by omega⟩) (fun i => ⟨2*i.val+1,by omega⟩)
  left_inv i := by
    dsimp only
    split_ifs <;> apply Fin.ext <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> omega
  right_inv i := by
    cases i with
    | inl i => simp
    | inr i =>
      simp
      apply Fin.ext
      dsimp only
      omega

@[simp] lemma pairSplit_left (b : ℕ) (i : Fin b) :
    ((pairSplit b).symm (Sum.inl i)).val = 2*i.val := rfl

@[simp] lemma pairSplit_right (b : ℕ) (i : Fin b) :
    ((pairSplit b).symm (Sum.inr i)).val = 2*i.val+1 := rfl

def appendEven (b : ℕ) : Fin (2*(b+1)) ≃ Fin (2*b) ⊕ Fin 2 :=
  (finCongr (by omega : 2*(b+1) = 2*b+2)).trans finSumFinEquiv.symm

@[simp] lemma appendEven_left (b : ℕ) (i : Fin (2*b)) :
    ((appendEven b).symm (Sum.inl i)).val = i.val := rfl
@[simp] lemma appendEven_right (b : ℕ) (i : Fin 2) :
    ((appendEven b).symm (Sum.inr i)).val = 2*b+i.val := rfl

end Saxl.ShortColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_PairSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Swap. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def tensorCommIntertwiner {G X Y : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) :
    (ρ.tprod σ).Equiv (σ.tprod ρ) where
  __ := TensorProduct.comm ℂ X Y
  isIntertwining' g := by
    ext x y
    rfl

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OneExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One Extra. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

namespace ShortColumns

def RowParity (δ : ℕ) (μ : YoungDiagram) : Prop :=
  if δ = 0 then ∀ i, Even (μ.rowLen i)
  else ∃ k, Odd (μ.rowLen k) ∧ ∀ l, l ≠ k → Even (μ.rowLen l)

end ShortColumns
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_DualTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual Transfer. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def intertwiningDual {G X Y : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X}
    {σ : Representation ℂ G Y} (f : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap σ.dual ρ.dual where
  toLinearMap := f.toLinearMap.dualMap
  isIntertwining' g := by
    ext l x
    change l (σ g⁻¹ (f x)) = l (f (ρ g⁻¹ x))
    rw [f.isIntertwining]

def intertwiningFlip {G X Y : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X}
    {σ : Representation ℂ G Y} (f : Representation.IntertwiningMap ρ σ.dual) :
    Representation.IntertwiningMap σ ρ.dual where
  toLinearMap := f.toLinearMap.flip
  isIntertwining' g := by
    ext y x
    change f x (σ g y) = f (ρ g⁻¹ x) y
    have h := congrArg (fun l : Module.Dual ℂ Y => l y) (LinearMap.congr_fun (f.isIntertwining' (g⁻¹)) x)
    change f (ρ g⁻¹ x) y = f x (σ (g⁻¹)⁻¹ y) at h
    rw [inv_inv] at h
    exact h.symm

def tensorDualEquiv {G X Y : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [Module.Finite ℂ X] [Module.Finite ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) :
    (ρ.dual.tprod σ.dual).Equiv (ρ.tprod σ).dual where
  toLinearEquiv := TensorProduct.dualDistribEquiv ℂ X Y
  isIntertwining' g := by
    ext l m x y
    rfl

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Projection. -/

section

noncomputable section
namespace Saxl.Balance

def balanceWords {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (w : Fin n → Fin d) : Prop :=
  (∀ i, A (w i)) ∧ ∀ k,
    (Finset.univ.filter (fun i => label (w i) = k)).card =
      (Finset.univ.filter (fun i => c i = k)).card ∧
    ∑ i ∈ Finset.univ.filter (fun i => label (w i) = k), z (w i) = σ k

lemma perm_filter_card {X : Type*} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X) (p : X → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun x => p (g x))).card = (Finset.univ.filter p).card := by
  classical
  apply Finset.card_bij (fun x _ => g x)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy hxy
    exact g.injective hxy
  · intro y hy
    refine ⟨g.symm y, ?_, g.apply_symm_apply y⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
      using (Finset.mem_filter.mp hy).2

lemma perm_filter_sum {X : Type*} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X) (p : X → Prop) [DecidablePred p] (f : X → ℤ) :
    ∑ i ∈ Finset.univ.filter (fun i => p (g i)), f (g i) =
      ∑ i ∈ Finset.univ.filter p, f i := by
  simpa only [Finset.sum_filter] using
    Equiv.sum_comp g (fun i => if p i then f i else 0)

lemma balanceWords_invariant {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (g : Equiv.Perm (Fin n)) (w : Fin n → Fin d) :
    balanceWords c A label z σ (w ∘ g) ↔ balanceWords c A label z σ w := by
  classical
  unfold balanceWords
  have hc (k) := perm_filter_card g (fun i => label (w i) = k)
  have hs (k) := perm_filter_sum g (fun i => label (w i) = k) (fun i => z (w i))
  simp only [Function.comp_apply, hc, hs]
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨fun i => by simpa using h (g.symm i),hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨fun i => h (g i),hc⟩

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_Neighboring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Neighboring. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl
namespace Balance

def reverseShortColumn (r j : ℕ) : ℕ := if j = r then r else r-1-j

lemma reverseShortColumn_invol (r j : ℕ) (hj : j ≤ r) :
    reverseShortColumn r (reverseShortColumn r j) = j := by
  unfold reverseShortColumn
  split_ifs <;> omega

def reverseShortColumns (r : ℕ) : (ShortColumns.shape r 1).cells ≃
    (ShortColumns.shape r 1).cells where
  toFun c := ⟨(c.val.1, reverseShortColumn r c.val.2), by
    have hc := (ShortColumns.mem_shape r 1 c.val.1 c.val.2).mp c.property
    change (c.val.1 = 0 ∧ c.val.2 < r+1) ∨ (c.val.1 = 1 ∧ c.val.2 < r) at hc
    apply (ShortColumns.mem_shape r 1 _ _).mpr
    unfold reverseShortColumn
    split_ifs <;> omega⟩
  invFun c := ⟨(c.val.1, reverseShortColumn r c.val.2), by
    have hc := (ShortColumns.mem_shape r 1 c.val.1 c.val.2).mp c.property
    change (c.val.1 = 0 ∧ c.val.2 < r+1) ∨ (c.val.1 = 1 ∧ c.val.2 < r) at hc
    apply (ShortColumns.mem_shape r 1 _ _).mpr
    unfold reverseShortColumn
    split_ifs <;> omega⟩
  left_inv c := by
    have hc := (ShortColumns.mem_shape r 1 c.val.1 c.val.2).mp c.property
    change (c.val.1 = 0 ∧ c.val.2 < r+1) ∨ (c.val.1 = 1 ∧ c.val.2 < r) at hc
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact reverseShortColumn_invol r c.val.2 (by omega)
  right_inv c := by
    have hc := (ShortColumns.mem_shape r 1 c.val.1 c.val.2).mp c.property
    change (c.val.1 = 0 ∧ c.val.2 < r+1) ∨ (c.val.1 = 1 ∧ c.val.2 < r) at hc
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact reverseShortColumn_invol r c.val.2 (by omega)

def neighborLetter (r : ℕ) : Fin ((ShortColumns.shape r 1).transpose.transpose.colLen 0) → Fin 2 :=
  (Fin.castLE (ShortColumns.height_le r 1)) ∘ Fin.cast
    (congrArg (fun ν : YoungDiagram => ν.colLen 0)
      (YoungDiagram.transpose_transpose (ShortColumns.shape r 1)))

end Balance
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_WordRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Relabel. -/

section

noncomputable section
namespace Saxl
open scoped TensorProduct

def pairLetterMap {a b c d : ℕ} (f : Fin a → Fin c) (g : Fin b → Fin d) :
    Fin (a*b) → Fin (c*d) := fun x => finProdFinEquiv (f (finProdFinEquiv.symm x).1,
      g (finProdFinEquiv.symm x).2)

lemma pairLetterMap_injective {a b c d : ℕ} (f : Fin a → Fin c) (g : Fin b → Fin d)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (pairLetterMap f g) :=
  finProdFinEquiv.injective.comp ((hf.prodMap hg).comp finProdFinEquiv.symm.injective)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_WordContents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Contents. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

def wordContent {n d : ℕ} (w : Fin n → Fin d) (j : Fin d) : ℕ :=
  (Finset.univ.filter (fun i => w i = j)).card

lemma wordContent_lift_equiv {n d e : ℕ} (q : Fin d ≃ Fin e)
    (w : Fin n → Fin d) (j : Fin e) :
    wordContent (q ∘ w) j = wordContent w (q.symm j) := by
  classical
  unfold wordContent
  congr 1
  apply Finset.filter_congr
  intro i _
  change q (w i) = j ↔ w i = q.symm j
  exact q.eq_symm_apply.symm

def appendLetters (ps qs : List ℕ) : Fin (ps ++ qs).length ≃ Fin ps.length ⊕ Fin qs.length :=
  (finCongr (List.length_append (as := ps) (bs := qs))).trans finSumFinEquiv.symm

lemma get_appendLetters (ps qs : List ℕ) (j : Fin (ps ++ qs).length) :
    (ps ++ qs).get j = Sum.elim ps.get qs.get (appendLetters ps qs j) := by
  obtain ⟨j,rfl⟩ := (appendLetters ps qs).symm.surjective j
  rcases j with j | j
  · simp only [Equiv.apply_symm_apply, Sum.elim_inl]
    change (ps ++ qs)[j.val] = ps[j.val]
    exact List.getElem_append_left j.isLt
  · simp only [Equiv.apply_symm_apply, Sum.elim_inr]
    change (ps ++ qs)[ps.length+j.val] = qs[j.val]
    rw [List.getElem_append_right (by omega)]
    simp

lemma list_get_fiber_card (ps : List ℕ) (k : ℕ) :
    Fintype.card {i : Fin ps.length // ps.get i = k} = ps.count k := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter]
  induction ps with
  | nil => simp
  | cons p ps ih =>
    change (∑ i : Fin (ps.length+1), if (p::ps).get i = k then (1:ℕ) else 0) = _
    rw [Fin.sum_univ_succ]
    change (if p = k then 1 else 0) + (∑ i : Fin ps.length, if ps.get i = k then 1 else 0) = _
    rw [ih]
    simp [List.count_cons, Nat.add_comm]

theorem list_get_equiv {ps qs : List ℕ} (h : ps.Perm qs) :
    ∃ q : Fin ps.length ≃ Fin qs.length, ∀ i, qs.get (q i) = ps.get i := by
  classical
  let f (k : ℕ) : {i : Fin ps.length // ps.get i = k} ≃
      {i : Fin qs.length // qs.get i = k} :=
    Fintype.equivOfCardEq (by rw [list_get_fiber_card,list_get_fiber_card,h.count_eq])
  let q := (Equiv.sigmaFiberEquiv ps.get).symm.trans
    ((Equiv.sigmaCongrRight f).trans (Equiv.sigmaFiberEquiv qs.get))
  exact ⟨q,fun i => (f (ps.get i) ⟨i,rfl⟩).property⟩

lemma columnShape_rows_permutation (ps : List ℕ) (hp : ∀ p ∈ ps, 0 < p) :
    ps.Perm (Columns.columnShape ps).transpose.rowLens := by
  rw [Columns.columnShape_cols]
  have he : ps.filter (fun p => 0 < p) = ps := by
    apply List.filter_eq_self.mpr
    intro p h
    simpa using hp p h
  simpa only [he] using Columns.positiveSorted_perm ps

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_PartWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Part Words. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

theorem exists_word_of_parts (ps : List ℕ) {n : ℕ} (hn : ps.sum = n) :
    ∃ w : Fin n → Fin ps.length, ∀ j, wordContent w j = ps.get j := by
  classical
  have hc : Fintype.card (Σ j : Fin ps.length, Fin (ps.get j)) = n := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [← List.sum_ofFn, List.ofFn_get, hn]
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨fun i => (e.symm i).1, fun j => ?_⟩
  rw [wordContent,Finset.card_filter,← Equiv.sum_comp e,Fintype.sum_sigma]
  simp

def balancedParts (n k : ℕ) : List ℕ :=
  List.ofFn (fun j : Fin k => n/k + if j.val < n%k then 1 else 0)

@[simp] lemma balancedParts_length (n k : ℕ) : (balancedParts n k).length = k :=
  List.length_ofFn

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPackingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing Geometry. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

lemma replicate_sorted (m k : ℕ) : (List.replicate m k).SortedGE :=
  List.Pairwise.sortedGE (List.pairwise_replicate.mpr (Or.inr le_rfl))

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_EmptyPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Empty Packing. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

def oneIf (x ε : ℕ) : List ℕ := if ε = 0 then [] else [x]

def markIf (x ε : ℕ) : Finset ℕ := if ε = 0 then ∅ else {x}

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalancedPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balanced Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

lemma short_height_ge_two (m : ℕ) (hm : 1 ≤ m) :
    2 ≤ (ShortColumns.shape m 0).colLen 0 := by
  have hc : (1,0) ∈ ShortColumns.shape m 0 :=
    (ShortColumns.mem_shape m 0 1 0).mpr (Or.inr ⟨rfl, by omega⟩)
  have hh := YoungDiagram.mem_iff_lt_colLen.mp hc
  omega

def pairAtOutputTwo (m : ℕ) (hm : 1 ≤ m) (i : Fin 2) :
    Fin ((ShortColumns.shape m 0).colLen 0 * (ShortColumns.shape m 0).colLen 0) :=
  finProdFinEquiv (Fin.castLE (short_height_ge_two m hm) i,
    Fin.castLE (short_height_ge_two m hm) (Fin.rev i))

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OddStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Odd Strip. -/

section

noncomputable section

namespace Saxl.Balance

lemma card_of_height_two (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ 2) :
    μ.card = μ.rowLen 0 + μ.rowLen 1 := by
  rw [← rowPrefix_eq_card μ hμ]
  simp [rowPrefix, Finset.sum_range_succ]

lemma short_rowLen (b δ i : ℕ) :
    (ShortColumns.shape b δ).rowLen i = if i = 0 then b+δ else if i = 1 then b else 0 := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, ShortColumns.mem_shape]
  split_ifs <;> simp_all

lemma short_card (b δ : ℕ) :
    (ShortColumns.shape b δ).card = 2*b+δ := by
  rw [card_of_height_two _ (ShortColumns.height_le b δ)]
  simp [short_rowLen]
  omega

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_Candidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate. -/

section

noncomputable section
namespace UniversalTensorSquare

def rectangle (a b : ℕ) : YoungDiagram where
  cells := Finset.range a ×ˢ Finset.range b
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hy ⊢
    exact ⟨lt_of_le_of_lt hxy.1 hy.1, lt_of_le_of_lt hxy.2 hy.2⟩

@[simp] lemma mem_rectangle {a b i j : ℕ} :
    (i, j) ∈ rectangle a b ↔ i < a ∧ j < b := by
  change (i, j) ∈ Finset.range a ×ˢ Finset.range b ↔ _
  simp

def candidateArm (M b δ : ℕ) : YoungDiagram :=
  rectangle 1 (M + b + δ) ⊔ rectangle 2 (M - 1 + b)

def armExtras (M b δ : ℕ) : Finset (ℕ × ℕ) :=
  {0} ×ˢ Finset.Ico M (M + b + δ) ∪
    {1} ×ˢ Finset.Ico (M - 1) (M - 1 + b)

lemma mem_armExtras {M b δ i j : ℕ} :
    (i, j) ∈ armExtras M b δ ↔
      (i = 0 ∧ M ≤ j ∧ j < M + b + δ) ∨
      (i = 1 ∧ M - 1 ≤ j ∧ j < M - 1 + b) := by
  simp only [armExtras, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_Ico]

lemma armExtras_card (M b δ : ℕ) : (armExtras M b δ).card = 2 * b + δ := by
  unfold armExtras
  rw [Finset.card_union_of_disjoint]
  · simp only [Finset.card_product, Finset.card_singleton, Nat.card_Ico, one_mul]
    omega
  · apply Finset.disjoint_left.mpr
    rintro ⟨i, j⟩ hi hj
    simp only [Finset.mem_product, Finset.mem_singleton] at hi hj
    omega

lemma armExtras_disjoint_transpose (M b δ : ℕ) (hM : 3 ≤ M) :
    Disjoint (armExtras M b δ)
      ((armExtras M b δ).map (Equiv.prodComm ℕ ℕ).toEmbedding) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨i, j⟩ hi hj
  simp only [Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk] at hj
  simp only [mem_armExtras] at hi hj
  omega

def candidateLengths (M b δ i : ℕ) : ℕ :=
  if i = 0 then M + b + δ else
  if i = 1 then M - 1 + b else
  if i < M - 2 then M - i else
  if i < M - 1 + b then 2 else
  if i < M + b + δ then 1 else 0

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_MarkedTriangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked Triangle. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl

def candidateMark (M b j : ℕ) : Prop :=
  (2 ≤ j ∧ j < M - 1) ∨ j = M + b - 1

end UniversalTensorSquare

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SubdiagramSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdiagram Support. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def diagonalCut (μ : YoungDiagram) (k : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun c => c.1+c.2 < k)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨μ.isLowerSet hxy hy.1, (Nat.add_le_add hxy.1 hxy.2).trans_lt hy.2⟩

@[simp] lemma mem_diagonalCut (μ : YoungDiagram) (k : ℕ) (c : ℕ × ℕ) :
    c ∈ diagonalCut μ k ↔ c ∈ μ ∧ c.1+c.2 < k := Finset.mem_filter

@[simp] lemma diagonalCut_zero (μ : YoungDiagram) : diagonalCut μ 0 = ⊥ := by
  ext c
  simp

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_TwoPathGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Path Geometry. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

def appendShortMap (p r q : ℕ) (hq : p+r=q) :
    (ShortColumns.shape p 1).cells ⊕ (ShortColumns.shape r 1).cells →
      (ShortColumns.shape q 2).cells :=
  Sum.elim
    (fun c => ⟨(c.val.1, if c.val.2 = p then q else c.val.2), by
      have hc := (ShortColumns.mem_shape p 1 c.val.1 c.val.2).mp c.property
      apply (ShortColumns.mem_shape q 2 _ _).mpr
      split_ifs <;> omega⟩)
    (fun c => ⟨(c.val.1, if c.val.2 = r then q+1 else p+c.val.2), by
      have hc := (ShortColumns.mem_shape r 1 c.val.1 c.val.2).mp c.property
      apply (ShortColumns.mem_shape q 2 _ _).mpr
      split_ifs <;> omega⟩)

lemma appendShortMap_injective (p r q : ℕ) (hq : p+r=q) :
    Function.Injective (appendShortMap p r q hq) := by
  intro x y he
  have hh := congrArg Subtype.val he
  cases x with
  | inl x =>
    have hx := (ShortColumns.mem_shape p 1 x.val.1 x.val.2).mp x.property
    cases y with
    | inl y =>
      have hy := (ShortColumns.mem_shape p 1 y.val.1 y.val.2).mp y.property
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Prod.ext
      · simpa only [appendShortMap, Sum.elim_inl, Sum.elim_inr] using congrArg Prod.fst hh
      · have ht := congrArg Prod.snd hh
        change (if x.val.2 = p then q else x.val.2) =
          (if y.val.2 = p then q else y.val.2) at ht
        split_ifs at ht <;> omega
    | inr y =>
      have hy := (ShortColumns.mem_shape r 1 y.val.1 y.val.2).mp y.property
      have ht := congrArg Prod.snd hh
      change (if x.val.2 = p then q else x.val.2) =
        (if y.val.2 = r then q+1 else p+y.val.2) at ht
      split_ifs at ht <;> omega
  | inr x =>
    have hx := (ShortColumns.mem_shape r 1 x.val.1 x.val.2).mp x.property
    cases y with
    | inl y =>
      have hy := (ShortColumns.mem_shape p 1 y.val.1 y.val.2).mp y.property
      have ht := congrArg Prod.snd hh
      change (if x.val.2 = r then q+1 else p+x.val.2) =
        (if y.val.2 = p then q else y.val.2) at ht
      split_ifs at ht <;> omega
    | inr y =>
      have hy := (ShortColumns.mem_shape r 1 y.val.1 y.val.2).mp y.property
      apply congrArg Sum.inr
      apply Subtype.ext
      apply Prod.ext
      · simpa only [appendShortMap, Sum.elim_inl, Sum.elim_inr] using congrArg Prod.fst hh
      · have ht := congrArg Prod.snd hh
        change (if x.val.2 = r then q+1 else p+x.val.2) =
          (if y.val.2 = r then q+1 else p+y.val.2) at ht
        split_ifs at ht <;> omega

def appendShortCells (p r q : ℕ) (hq : p+r=q) :
    (ShortColumns.shape p 1).cells ⊕ (ShortColumns.shape r 1).cells ≃
      (ShortColumns.shape q 2).cells :=
  Equiv.ofBijective (appendShortMap p r q hq)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨appendShortMap_injective p r q hq, by
        rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe]
        change (ShortColumns.shape p 1).card + (ShortColumns.shape r 1).card =
          (ShortColumns.shape q 2).card
        rw [short_card, short_card, short_card]
        omega⟩)

@[simp] lemma appendShortCells_left (p r q : ℕ) (hq : p+r=q)
    (c : (ShortColumns.shape p 1).cells) :
    (appendShortCells p r q hq (Sum.inl c)).val =
      (c.val.1, if c.val.2 = p then q else c.val.2) := rfl

@[simp] lemma appendShortCells_right (p r q : ℕ) (hq : p+r=q)
    (c : (ShortColumns.shape r 1).cells) :
    (appendShortCells p r q hq (Sum.inr c)).val =
      (c.val.1, if c.val.2 = r then q+1 else p+c.val.2) := rfl

def twoPathLetter (q : ℕ) :
    Fin ((ShortColumns.shape q 2).transpose.transpose.colLen 0) → Fin 2 :=
  (Fin.castLE (ShortColumns.height_le q 2)) ∘ Fin.cast
    (congrArg (fun ν : YoungDiagram => ν.colLen 0)
      (YoungDiagram.transpose_transpose (ShortColumns.shape q 2)))

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Blocks. -/

section

noncomputable section
namespace Saxl.Balance

def bigParts (q δ : ℕ) : List ℕ := balancedParts (2*q+1+3*δ) 4 ++ oneIf 1 (1-δ)

def bigUpper (q δ : ℕ) : ℕ := if δ = 0 then q+1 else 2*q+3

def shortColumns (m τ : ℕ) : List ℕ := List.replicate m 2 ++ oneIf 3 τ

def shortParts (m τ : ℕ) : List ℕ := if τ = 0 then [2*m] else balancedParts (2*m+3) 2

def shortMarks (τ : ℕ) : Finset ℕ := if τ = 0 then {2} else {2,3}

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_PairRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Run. -/

section

noncomputable section
namespace Saxl.Balance

def pairColumns (a m : ℕ) : List ℕ :=
  (List.range m).flatMap (fun j => [a+2*j+1,a+2*j])

def pairParts (a m : ℕ) : List ℕ :=
  (List.range m).flatMap (fun j => balancedParts (2*(a+2*j)+1) 4)

def pairMarks (a m : ℕ) : Finset ℕ :=
  (Finset.range m).image (fun j => a+2*j)

lemma mem_pairMarks {a m k : ℕ} :
    k ∈ pairMarks a m ↔ ∃ j < m, k = a+2*j := by
  simp only [pairMarks,Finset.mem_image,Finset.mem_range]
  constructor <;> rintro ⟨j,hj,he⟩ <;> exact ⟨j,hj,he.symm⟩

lemma pairMarks_bound {a m k : ℕ} (hk : k ∈ pairMarks a m) :
    a ≤ k ∧ k+1 < a+2*m := by
  obtain ⟨j,hj,rfl⟩ := mem_pairMarks.mp hk
  omega

lemma pairMarks_separated {a m k l : ℕ} (hk : k ∈ pairMarks a m)
    (hl : l ∈ pairMarks a m) (h : k < l) : k+1 < l := by
  obtain ⟨i,hi,rfl⟩ := mem_pairMarks.mp hk
  obtain ⟨j,hj,rfl⟩ := mem_pairMarks.mp hl
  omega

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Assembly. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

def balanceParts (M b δ τ ε m : ℕ) : List ℕ :=
  ((bigParts (M-1+b) δ ++ shortParts (b+1) τ) ++
    pairParts (3+τ+ε) m) ++ oneIf (3+τ) ε

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalancedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balanced Columns. -/

section

noncomputable section
namespace Saxl.Columns

def doubled {α : Type*} (xs : List α) : List α := xs.flatMap (fun x => [x,x])

@[simp] lemma doubled_nil {α : Type*} : doubled ([] : List α) = [] := rfl
@[simp] lemma doubled_cons {α : Type*} (x : α) (xs : List α) :
    doubled (x::xs) = x::x::doubled xs := rfl

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_Capacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Capacity. -/

section

noncomputable section

namespace UniversalTensorSquare

open Saxl

def colPrefix (μ : YoungDiagram) (i : ℕ) : ℕ := rowPrefix μ.transpose i

def bandCapacity (μ : YoungDiagram) (d q : ℕ) : ℕ :=
  ∑ k ∈ Finset.range q, (μ.colLen k - d) / 2

def BandTest (M r : ℕ) (μ : YoungDiagram) : Prop :=
  ∃ d, 1 ≤ d ∧ d ≤ 4 ∧ ∃ q, q ≤ 8 ∧
    2*M-1 ≤ rowPrefix μ d ∧ d*q+7+d ≤ 2*M-1 ∧ r ≤ bandCapacity μ d q

end UniversalTensorSquare
end
end

end OAI
end

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
open Saxl

def columnCut (μ : YoungDiagram) (f : ℕ → ℕ) (hf : Antitone f) : YoungDiagram where
  cells := μ.cells.filter (fun c => c.1 < f c.2)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨μ.isLowerSet hxy hy.1, hxy.1.trans_lt (hy.2.trans_le (hf hxy.2))⟩

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_PathGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Path Geometry. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def candidatePathCell (M b δ : ℕ) (q : Fin (2*M-1)) : ℕ × ℕ :=
  if q.val = 0 then (M+b+δ-1,0) else
  if q.val = 2*M-2 then (0,M+b+δ-1) else
    (M-1-(q.val+1)/2, q.val/2)

def attachmentNE (M b δ : ℕ) : Finset (ℕ × ℕ) :=
  {0} ×ˢ Finset.Ico (M-1) (M+b+δ-1) ∪
    {1} ×ˢ Finset.Ico (M-1) (M+b-1)

lemma mem_attachmentNE {M b δ i j : ℕ} :
    (i,j) ∈ attachmentNE M b δ ↔
      (i = 0 ∧ M-1 ≤ j ∧ j < M+b+δ-1) ∨
      (i = 1 ∧ M-1 ≤ j ∧ j < M+b-1) := by
  simp only [attachmentNE, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_Ico]

lemma candidatePathCell_injective (M b δ : ℕ) (hM : 4 ≤ M) :
    Function.Injective (candidatePathCell M b δ) := by
  intro q t he
  have hq := q.isLt
  have ht := t.isLt
  apply Fin.ext
  unfold candidatePathCell at he
  split_ifs at he <;> simp only [Prod.mk.injEq] at he <;> omega

lemma pathCell_not_attachment (M b δ : ℕ) (hM : 4 ≤ M) (q : Fin (2*M-1)) :
    candidatePathCell M b δ q ∉ attachmentNE M b δ ∧
      (candidatePathCell M b δ q).swap ∉ attachmentNE M b δ := by
  have hq := q.isLt
  unfold candidatePathCell
  split_ifs <;> simp only [Prod.swap_prod_mk, mem_attachmentNE] <;> omega

lemma attachment_disjoint_transpose (M b δ : ℕ) (hM : 4 ≤ M) :
    Disjoint (attachmentNE M b δ)
      ((attachmentNE M b δ).map (Equiv.prodComm ℕ ℕ).toEmbedding) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨i,j⟩ hi hj
  simp only [Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk, mem_attachmentNE] at hi hj
  omega

lemma candidatePathCell_odd (M b δ : ℕ) (hM : 4 ≤ M) (i j : ℕ)
    (hs : i+j = M-2) :
    ∃ q : Fin (2*M-1), candidatePathCell M b δ q = (i,j) := by
  refine ⟨⟨2*j+1,by omega⟩, ?_⟩
  simp only [candidatePathCell]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  apply Prod.ext <;> dsimp only <;> omega

lemma candidatePathCell_even (M b δ : ℕ) (hM : 4 ≤ M) (i j : ℕ)
    (hs : i+j = M-1) (hi : 0 < i) (hj : 0 < j) :
    ∃ q : Fin (2*M-1), candidatePathCell M b δ q = (i,j) := by
  refine ⟨⟨2*j,by omega⟩, ?_⟩
  simp only [candidatePathCell]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  apply Prod.ext <;> dsimp only <;> omega

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandPositions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Positions. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def candidateNECell (M : ℕ) {b δ : ℕ} (x : (ShortColumns.shape b δ).cells) : ℕ × ℕ :=
  (x.val.1,M-1+x.val.2)

lemma candidateNECell_mem {M b δ : ℕ} (hM : 4 ≤ M)
    (x : (ShortColumns.shape b δ).cells) : candidateNECell M x ∈ attachmentNE M b δ := by
  have hx := (ShortColumns.mem_shape b δ x.val.1 x.val.2).mp x.property
  change (x.val.1,M-1+x.val.2) ∈ attachmentNE M b δ
  rw [mem_attachmentNE]
  omega

lemma candidateNECell_injective (M b δ : ℕ) :
    Function.Injective (candidateNECell M (b := b) (δ := δ)) := by
  intro x y h
  apply Subtype.ext
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  apply Prod.ext
  · exact h₁
  change M-1+x.val.2 = M-1+y.val.2 at h₂
  omega

lemma candidateNECell_surjective {M b δ : ℕ} (hM : 4 ≤ M) (i j : ℕ)
    (hx : (i,j) ∈ attachmentNE M b δ) :
    ∃ x : (ShortColumns.shape b δ).cells, candidateNECell M x = (i,j) := by
  rw [mem_attachmentNE] at hx
  have hs : (i,j-(M-1)) ∈ ShortColumns.shape b δ := by
    rw [ShortColumns.mem_shape]
    omega
  refine ⟨⟨(i,j-(M-1)),hs⟩, ?_⟩
  apply Prod.ext
  · rfl
  change M-1 + (j-(M-1)) = j
  omega

abbrev CandidateBandParts (M b δ : ℕ) :=
  Fin (2*M-1) ⊕ (ShortColumns.shape b δ).cells ⊕ (ShortColumns.shape b δ).cells

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Split. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def candidateExtraSplit (r : ℕ) : Fin (2*r) ≃ Fin r ⊕ Fin r :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Groups. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def candidatePartsSwap {M b δ : ℕ} : CandidateBandParts M b δ → CandidateBandParts M b δ
  | .inl q => .inl q.rev
  | .inr (.inl x) => .inr (.inr x)
  | .inr (.inr x) => .inr (.inl x)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandLetters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Letters. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma shortColumns_width (b δ : ℕ) : (ShortColumns.shape b δ).transpose.colLen 0 = b+δ := by
  rw [YoungDiagram.colLen_transpose]
  have H (j : ℕ) : j < (ShortColumns.shape b δ).rowLen 0 ↔ j < b+δ := by
    rw [← YoungDiagram.mem_iff_lt_rowLen, ShortColumns.mem_shape]
    simp only [true_and, zero_ne_one, false_and, or_false]
  have h₁ := H (b+δ)
  have h₂ := H ((ShortColumns.shape b δ).rowLen 0)
  omega

def bandSmallLetter {D : ℕ} (hD : 2 ≤ D) : Fin 2 → Fin D := Fin.castLE hD

def bandExtraLetter {M b δ D : ℕ} (hD : M+b+δ ≤ D) :
    Fin ((ShortColumns.shape b δ).transpose.colLen 0) → Fin D :=
  fun c => ⟨if c.val < b then M-1+c.val else M+c.val, by
    have hc := c.isLt
    have hc' : c.val < b+δ := by simpa only [shortColumns_width] using hc
    split_ifs <;> omega⟩

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ColumnTensorSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Tensor Split. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.FlagColumns

def splitCons {a b A B n : ℕ} (e : Fin n ≃ Fin A ⊕ Fin B) :
    Fin ((a + b) + n) ≃ Fin (a + A) ⊕ Fin (b + B) :=
  (finSumFinEquiv.symm.trans ((finSumFinEquiv.symm).sumCongr e)).trans
    ((Equiv.sumSumSumComm (Fin a) (Fin b) (Fin A) (Fin B)).trans
      (finSumFinEquiv.sumCongr finSumFinEquiv))

def splitPositions : (ps : List (ℕ × ℕ)) →
    Fin (ps.map (fun p => p.1 + p.2)).sum ≃
      Fin (ps.map Prod.fst).sum ⊕ Fin (ps.map Prod.snd).sum
  | [] => show Fin 0 ≃ Fin 0 ⊕ Fin 0 from Equiv.equivOfIsEmpty _ _
  | (_,_)::ps => splitCons (splitPositions ps)

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ColumnRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Restriction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.FlagColumns
open Columns

def coordinateFlag {h d : ℕ} (ι : Fin h → Fin d) : ℕ → Fin d → ℂ :=
  fun i => if hi : i < h then Pi.single (ι ⟨i,hi⟩) 1 else 0

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Path. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl
open scoped TensorProduct

def candidatePathEquiv {M : ℕ} (hM : 4 ≤ M) : Fin (2*(M-1)+1) ≃ Fin (2*M-1) :=
  finCongr (by omega)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_CommonPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common Path. -/

section

noncomputable section
namespace Saxl.Band

def extendFourBasis (N : Module.Basis (Fin 4) ℂ Mat) (i : ℕ) : Mat :=
  if h : i < 4 then N ⟨i,h⟩ else N 3

end Saxl.Band
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_NoMixedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! No Mixed Columns. -/

section

noncomputable section
namespace Saxl.FlagColumns
open Columns

def joinedFlag {D : ℕ} (d : ℕ) (N Q : ℕ → Fin D → ℂ) : ℕ → Fin D → ℂ :=
  fun i => if i < d then N i else Q (i-d)

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Gluing. -/

section

noncomputable section
namespace Saxl.FlagColumns

def columnsAway (K : ℕ) : List (ℕ × ℕ) → ℕ → Prop
  | [], _ => True
  | (a,b)::ps, o => (b ≠ 0 → 4 ≤ o ∧ o+a+4 ≤ K) ∧ columnsAway K ps (o+a)

end Saxl.FlagColumns
namespace Saxl

def joinedPositionEquiv {n m a b A B : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B) : Fin n ≃ Fin m :=
  e.trans ((p.sumCongr q).trans f.symm)

end Saxl

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_Intermediate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intermediate. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def testWidth (M f : ℕ) : ℕ := min 8 ((2*M-8-f)/f)

def exceptionalPair (M r : ℕ) : Prop :=
  (M = 10 ∧ 8 ≤ r ∧ r ≤ 17) ∨ (M = 12 ∧ 14 ≤ r ∧ r ≤ 20) ∨
    (M = 14 ∧ 22 ≤ r ∧ r ≤ 23)

def admissibleR (M r : ℕ) : Prop := 0 < r ∧
  (if M % 2 = 1 then 2*r ≤ M-1 else 2*r ≤ 3*M+4) ∧ ¬exceptionalPair M r

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
open Saxl

def RowBounds (μ : YoungDiagram) (B : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ B, 0 < p.1 ∧ rowPrefix μ p.1 ≤ p.2

def coreImpossible (K d : ℕ) (A : List (ℕ × ℕ)) : Prop :=
    ∃ p ∈ A, d ≤ p.1 ∧ p.2 < K

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_NumericBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric Bands. -/

section

noncomputable section
namespace Saxl.Balance

def bandStarts (es : List (ℕ × ℕ)) : Finset ℕ := (es.map Prod.fst).toFinset

def bandUpper (es : List (ℕ × ℕ)) (k : ℕ) : ℕ :=
  es.toFinset.sup (fun e => if e.1 = k then e.2 else 0)

lemma mem_bandStarts {es : List (ℕ × ℕ)} {k : ℕ} :
    k ∈ bandStarts es ↔ ∃ e ∈ es, e.1 = k := by simp [bandStarts]

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ConstrainedRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constrained Rows. -/

section

namespace UniversalTensorSquare

def clippedSum (rs : List ℕ) (k : ℕ) : ℕ := (rs.map (min k)).sum

def ListRowBounds (rs : List ℕ) (B : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ B, (rs.take p.1).sum ≤ p.2

def ListColBounds (rs : List ℕ) (A : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ A, clippedSum rs p.1 ≤ p.2

def clipBudget (A : List (ℕ × ℕ)) (a : ℕ) : List (ℕ × ℕ) :=
  A.map fun p => (p.1, p.2-min p.1 a)

def rowBudget (B : List (ℕ × ℕ)) (a : ℕ) : List (ℕ × ℕ) :=
  B.filterMap fun p => if 1 < p.1 then some (p.1-1,p.2-a) else none

def rejectedRows (fuel n upper : ℕ) (A B : List (ℕ × ℕ)) : Prop :=
  n < fuel ∨ fuel*upper < n ∨
  (∃ p ∈ A, 0 < p.1 ∧ p.2 < fuel) ∨ (∃ p ∈ B, fuel ≤ p.1 ∧ p.2 < n) ∨
  (∃ p ∈ A, p.2*upper < n*min p.1 upper) ∨
  (∃ p ∈ B, p.2*fuel < n*min p.1 fuel)

instance instDecidableRejectedRows (fuel n upper : ℕ) (A B : List (ℕ × ℕ)) : Decidable (rejectedRows fuel n upper A B) := by
  unfold rejectedRows; infer_instance

def allowedRow (a : ℕ) (A B : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ A, min p.1 a ≤ p.2) ∧ (∀ p ∈ B, 0 < p.1 → a ≤ p.2)

instance instDecidableAllowedRow (a : ℕ) (A B : List (ℕ × ℕ)) : Decidable (allowedRow a A B) := by
  unfold allowedRow; infer_instance

def constrainedRows : ℕ → ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → List (List ℕ)
  | fuel,n,upper,A,B =>
    if rejectedRows fuel n upper A B then [] else
      match fuel with
      | 0 => if n = 0 then [[]] else []
      | k+1 => (List.range' 1 (min n upper)).flatMap fun a =>
          if allowedRow a A B ∧ n ≤ (k+1)*a then
            (constrainedRows k (n-a) a (clipBudget A a) (rowBudget B a)).map (List.cons a)
          else []

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_RowCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Certificates. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def rowDiagram (rs : List ℕ) : YoungDiagram := (columnShape rs).transpose

def GoodRows (rs : List ℕ) : Prop := rs.SortedGE ∧ ∀ a ∈ rs, 0 < a
instance instDecidableGoodRows (rs : List ℕ) : Decidable (GoodRows rs) := by unfold GoodRows; infer_instance

def RowsStrip (rs ss : List ℕ) : Prop :=
  GoodRows rs ∧ GoodRows ss ∧ ∀ i ∈ List.range (max rs.length ss.length),
    rs[i]?.getD 0 ≤ ss[i]?.getD 0 ∧ ss[i+1]?.getD 0 ≤ rs[i]?.getD 0
instance instDecidableRowsStrip (rs ss : List ℕ) : Decidable (RowsStrip rs ss) := by
  unfold RowsStrip; infer_instance

def ChainValid : List ℕ → List (List ℕ) → List ℕ → Prop
  | rs,[],ss => rs=ss
  | rs,us::cs,ss => RowsStrip rs us ∧ rs.sum ≤ us.sum ∧ ChainValid us cs ss

def RowsDom (rs ss : List ℕ) : Prop :=
  ∀ k ∈ List.range (ss.length+1), (ss.take k).sum ≤ (rs.take k).sum
instance instDecidableRowsDom (rs ss : List ℕ) : Decidable (RowsDom rs ss) := by unfold RowsDom; infer_instance

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Density. -/

section

noncomputable section
open scoped Topology

namespace Saxl.ThreeRow

abbrev Parameters := Fin 13 → ℂ
abbrev Coordinates := Fin 12 → ℂ

def idx (k : Fin 4) (i : Fin 3) : Fin 13 := ⟨3*k.val+i.val, by omega⟩

def gram (z : Parameters) (i j : Fin 3) : ℂ :=
  z 12 * (z (idx 2 i) * z (idx 3 j) + z (idx 2 j) * z (idx 3 i)) -
    (z (idx 0 i) * z (idx 1 j) + z (idx 0 j) * z (idx 1 i))

def parameterMap (z : Parameters) : Coordinates :=
  ![gram z 0 0, gram z 0 1, gram z 0 2, gram z 1 1, gram z 1 2, gram z 2 2,
    z 6, z 7, z 8, z 9, z 10, z 11]

def basePoint : Parameters := ![1,0,0,0,1,0,0,0,1,0,0,1,1]

abbrev proj (i : Fin 13) : Parameters →L[ℂ] ℂ := ContinuousLinearMap.proj i

def gramDeriv (z : Parameters) (i j : Fin 3) : Parameters →L[ℂ] ℂ :=
  (z 12) •
    (z (idx 2 i) • proj (idx 3 j) + z (idx 3 j) • proj (idx 2 i) +
     (z (idx 2 j) • proj (idx 3 i) + z (idx 3 i) • proj (idx 2 j))) +
    (z (idx 2 i) * z (idx 3 j) + z (idx 2 j) * z (idx 3 i)) • proj 12 -
    (z (idx 0 i) • proj (idx 1 j) + z (idx 1 j) • proj (idx 0 i) +
     (z (idx 0 j) • proj (idx 1 i) + z (idx 1 i) • proj (idx 0 j)))

def parameterDeriv (z : Parameters) : Parameters →L[ℂ] Coordinates :=
  ContinuousLinearMap.pi
    ![gramDeriv z 0 0, gramDeriv z 0 1, gramDeriv z 0 2, gramDeriv z 1 1,
      gramDeriv z 1 2, gramDeriv z 2 2, proj 6, proj 7, proj 8, proj 9, proj 10, proj 11]

def differentialLift (w : Coordinates) : Parameters :=
  ![-w 1, -w 3/2, w 7+w 10-w 4, -w 0/2, 0, w 6+w 9-w 2,
    w 6, w 7, w 8, w 9, w 10, w 11, w 5/2-w 8-w 11]

end Saxl.ThreeRow
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowTensors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Tensors. -/

section

noncomputable section
namespace Saxl.ThreeRow

def symmetricIndex : Fin 3 → Fin 3 → Fin 12 := !![0,1,2; 1,3,4; 2,4,5]

def matrixCoord (w : Coordinates) (i j : Fin 3) := w (symmetricIndex i j)
def xCoord (w : Coordinates) (i : Fin 3) := w ⟨6+i.val, by omega⟩
def yCoord (w : Coordinates) (i : Fin 3) := w ⟨9+i.val, by omega⟩

def packCoordinates (Q : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) : Coordinates :=
  ![Q 0 0,Q 0 1,Q 0 2,Q 1 1,Q 1 2,Q 2 2,x 0,x 1,x 2,y 0,y 1,y 2]

end Saxl.ThreeRow
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Generator. -/

section

noncomputable section
namespace Saxl.ThreeRow

def sixPairForm : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0,1,0,0,0,0; 1,0,0,0,0,0; 0,0,0,-1,0,0;
     0,0,-1,0,0,0; 0,0,0,0,0,0; 0,0,0,0,0,0]

def tripleColors : Fin 3 → Fin 6 := ![4,5,1]

def densityMap (z : Parameters) : Fin 6 → Fin 3 → ℂ :=
  ![ (fun i => z (idx 2 i)), (fun i => z 12 * z (idx 3 i)),
     (fun i => z (idx 0 i)), (fun i => z (idx 1 i)),
     (fun i => z 12 * z (idx 3 i)), (fun i => z 12 * z (idx 3 i)) ]

end Saxl.ThreeRow
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.ThreeRow
open FlagColumns Columns Balance

def pairCoords : Fin 6 → Fin 3 × Fin 3 := ![(0,0),(1,1),(0,1),(1,0),(0,2),(2,0)]

def pairLetters : Fin 6 → Fin 9 := fun a => finProdFinEquiv (pairCoords a)

end Saxl.ThreeRow
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Local. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.ThreeRow
open FlagColumns Columns Balance

def twos (m : ℕ) : List ℕ := List.replicate m 2

def ones (s : ℕ) : List ℕ := List.replicate s 1

def pairPositions (m : ℕ) : Fin (twos m).sum ≃ Fin m ⊕ Fin m :=
  (finCongr (by simp [twos,Nat.mul_comm])).trans (ShortColumns.pairSplit m)

@[simp] lemma pairPositions_left_val (m : ℕ) (i : Fin m) :
    ((pairPositions m).symm (Sum.inl i)).val = 2*i.val := rfl

@[simp] lemma pairPositions_right_val (m : ℕ) (i : Fin m) :
    ((pairPositions m).symm (Sum.inr i)).val = 2*i.val+1 := rfl

def columns (m s : ℕ) : List ℕ := (twos m ++ ones s) ++ [3]

def shortSplit (m s : ℕ) : Fin (twos m ++ ones s).sum ≃ Fin (twos m).sum ⊕ Fin s :=
  (appendPositions (twos m) (ones s)).trans
    (Equiv.sumCongr (Equiv.refl _) (finCongr (by simp [ones])))

def tripleSplit (m s : ℕ) : Fin (columns m s).sum ≃ Fin (twos m ++ ones s).sum ⊕ Fin 3 :=
  (appendPositions (twos m ++ ones s) [3]).trans
    (Equiv.sumCongr (Equiv.refl _) (finCongr (by simp)))

end Saxl.ThreeRow
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

def partitionLists : ℕ → ℕ → ℕ → Finset (List ℕ)
  | 0, n, _ => if n = 0 then {[]} else ∅
  | k+1, n, b => (if n = 0 then {[]} else ∅) ∪
      (Finset.Icc 1 (min n b)).biUnion fun a =>
        (partitionLists k (n-a) a).image (List.cons a)

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Masks. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

structure ThreeRowEntry where
  core : List ℕ
  middle : List ℕ
  final : List ℕ
  deriving DecidableEq

namespace ThreeRowEntry

def Valid (m s : ℕ) (c : ThreeRowEntry) : Prop :=
  c.core.length ≤ 3 ∧ c.final.length ≤ 3 ∧
  c.core.sum = 2*m ∧ c.middle.sum = 2*m+s ∧ c.final.sum = 2*m+s+3 ∧
  (∀ x ∈ c.core, x % 2 = 0) ∧ RowsStrip c.core c.middle ∧ RowsStrip c.middle c.final
instance instDecidableValid (m s : ℕ) (c : ThreeRowEntry) : Decidable (c.Valid m s) := by
  unfold Valid; infer_instance

end ThreeRowEntry

def ThreeRowMask (m s : ℕ) (ps : List ℕ) (cs : List ThreeRowEntry) : Prop :=
  GoodRows ps ∧ ps.length ≤ 3 ∧ ps.sum = 2*m+s+3 ∧
  (∀ c ∈ cs, c.Valid m s) ∧
  ∀ rs ∈ partitionLists 3 (2*m+s+3) (2*m+s+3), RowsDom rs ps →
    rs ∈ cs.map ThreeRowEntry.final
instance instDecidableThreeRowMask (m s : ℕ) (ps : List ℕ) (cs : List ThreeRowEntry) : Decidable (ThreeRowMask m s ps cs) := by
  unfold ThreeRowMask; infer_instance

end UniversalTensorSquare

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_PackingPlans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packing Plans. -/

section

noncomputable section
namespace Saxl.Balance
open Columns FlagColumns

inductive PackingPlan where
  | empty
  | neighbor (r : ℕ) (parts : List ℕ)
  | repeated (m k : ℕ)
  | twosOdd (m x : ℕ) (parts : List ℕ)
  | twoPaths (q : ℕ) (parts : List ℕ)
  | threeRows (m s : ℕ) (parts : List ℕ) (strips : List UniversalTensorSquare.ThreeRowEntry)
  | join (p q : PackingPlan)
  deriving DecidableEq

namespace PackingPlan

def columns : PackingPlan → List ℕ
  | .empty => []
  | .neighbor r _ => [r+1,r]
  | .repeated m k => List.replicate m k
  | .twosOdd m x _ => List.replicate m 2 ++ [x]
  | .twoPaths q _ => [q+2,q] ++ List.replicate 2 1
  | .threeRows m s _ _ => ThreeRow.columns m s
  | .join p q => p.columns ++ q.columns

def parts : PackingPlan → List ℕ
  | .empty => []
  | .neighbor _ ps => ps
  | .repeated m k => [m*k]
  | .twosOdd _ _ ps => ps
  | .twoPaths _ ps => ps
  | .threeRows _ _ ps _ => ps
  | .join p q => p.parts ++ q.parts

def bands : PackingPlan → List (ℕ × ℕ)
  | .empty => []
  | .neighbor r _ => [(r,r+1)]
  | .repeated _ k => [(k,k)]
  | .twosOdd _ x _ => [(2,2),(x,x)]
  | .twoPaths q _ => [(q,2*q+3),(1,1)]
  | .threeRows _ _ _ _ => [(1,3)]
  | .join p q => p.bands ++ q.bands

def marks (p : PackingPlan) : Finset ℕ := bandStarts p.bands

def Valid : PackingPlan → ℕ → Prop
  | .empty,_ => True
  | .neighbor r ps,d => 0 < r ∧ r+1 ≤ d ∧ ps.sum = 2*r+1 ∧ ps.length ≤ 4
  | .repeated m k,d => 0 < m ∧ 0 < k ∧ k ≤ d
  | .twosOdd m x ps,d => 1 ≤ m ∧ Odd x ∧ x ≤ 2*m ∧ 2 ≤ d ∧ x ≤ d ∧
      ps.sum = 2*m+x ∧ ps.length ≤ 2
  | .twoPaths q ps,d => 3 ≤ q ∧ q+2 ≤ d ∧ ps.sum = 2*q+4 ∧ ps.length ≤ 4
  | .threeRows m s ps cs,d => 3 ≤ d ∧ UniversalTensorSquare.ThreeRowMask m s ps cs
  | .join p q,d => p.Valid d ∧ q.Valid d ∧ Disjoint p.marks q.marks

instance instDecidableValid (p : PackingPlan) (d : ℕ) : Decidable (p.Valid d) := by
  induction p with
  | empty => exact isTrue True.intro
  | neighbor r ps => unfold Valid; infer_instance
  | repeated m k => unfold Valid; infer_instance
  | twosOdd m x ps => unfold Valid; infer_instance
  | twoPaths q ps => unfold Valid; infer_instance
  | threeRows m s ps cs => unfold Valid; infer_instance
  | join p q ip iq => unfold Valid; infer_instance

end PackingPlan
end Saxl.Balance

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_ColumnCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Certificates. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

namespace Columns

def pairFlag {d a b : ℕ} (L : ℕ → ℕ → ℕ → ℤ) : Fin d → Fin (a*b) → ℂ :=
  fun r c => (L r.val (finProdFinEquiv.symm c).1.val (finProdFinEquiv.symm c).2.val : ℂ)

end Columns
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_DomainContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domain Contractions. -/

section

open scoped BigOperators
namespace Saxl.Columns

def Domains : List ℕ → Type
  | [] => Unit
  | r :: rs => Finset (Equiv.Perm (Fin r)) × Domains rs

def Domains.full : (rs : List ℕ) → Domains rs
  | [] => ()
  | _ :: rs => (Finset.univ, full rs)

def Domains.vanished : {rs : List ℕ} → Domains rs → Bool
  | [], _ => false
  | _ :: _, (s,D) => decide (s = ∅) || vanished D

def Domains.mass : {rs : List ℕ} → Domains rs → ℤ
  | [], _ => 1
  | _ :: _, (s,D) => (∑ π ∈ s, (Equiv.Perm.sign π : ℤ)) * mass D

end Saxl.Columns
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_DomainSolver
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domain Solver. -/

section

open scoped BigOperators
namespace Saxl.Columns

def bringBest {α : Type*} (score : α → ℕ) : List α → List α
  | [] => []
  | c :: cs => match bringBest score cs with
    | [] => [c]
    | d :: ds => if score c ≤ score d then c :: d :: ds else d :: c :: ds

end Saxl.Columns
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_VectorDomainsCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vector Domains Core. -/

section

open scoped BigOperators
namespace Saxl.Columns

def permVector {n : ℕ} (π : Equiv.Perm (Fin n)) : List ℕ := List.ofFn (fun i => (π i).val)

def vectorSign (n : ℕ) (rs : List ℕ) : ℤ :=
  ∏ x ∈ Equiv.Perm.finPairsLT n,
    if rs[x.1.val]?.getD 0 ≤ rs[x.2.val]?.getD 0 then -1 else 1

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_CompactDomainsCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Domains Core. -/

section

open scoped BigOperators
namespace Saxl.Columns

abbrev CompactDomain (n : ℕ) := Option (Equiv.Perm (Fin n) × Finset (Fin n))

def CompactDomain.describe {n : ℕ} : CompactDomain n → Finset (Equiv.Perm (Fin n))
  | none => ∅
  | some (π,s) => Finset.univ.filter (fun σ => ∀ i, i ∉ s → σ i = π i)

def CompactDomain.full (n : ℕ) : CompactDomain n := some (1,Finset.univ)

def CompactDomain.atValue {n : ℕ} : CompactDomain n → Fin n → ℕ → CompactDomain n
  | none, _, _ => none
  | some (π,s), i, j =>
    if hj : j < n then
      let k := π.symm ⟨j,hj⟩
      if i ∈ s then
        if k ∈ s then some (π * Equiv.swap i k,s.erase i) else none
      else if (π i).val = j then some (π,s) else none
    else none

def CompactDomain.vanished {n : ℕ} (D : CompactDomain n) : Bool := D.isNone

def CompactDomain.mass {n : ℕ} : CompactDomain n → ℤ
  | none => 0
  | some (π,s) => if s.card ≤ 1 then vectorSign n (permVector π) else 0

def CompactDomains : List ℕ → Type
  | [] => Unit
  | r :: rs => CompactDomain r × CompactDomains rs

def CompactDomains.full : (rs : List ℕ) → CompactDomains rs
  | [] => ()
  | r :: rs => (CompactDomain.full r,full rs)

def CompactDomains.describe : {rs : List ℕ} → CompactDomains rs → Domains rs
  | [], _ => ()
  | _ :: _, (s,D) => (s.describe,describe D)

def CompactDomains.vanished : {rs : List ℕ} → CompactDomains rs → Bool
  | [], _ => false
  | _ :: _, (s,D) => s.vanished || vanished D

def CompactDomains.mass : {rs : List ℕ} → CompactDomains rs → ℤ
  | [], _ => 1
  | _ :: _, (s,D) => s.mass * mass D

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_FinitePieri
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Pieri. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl.Balance
open FlagColumns Columns

def pairUpper (q δ : ℕ) : ℕ := if δ = 1 then q+1 else 2*q+3

end Saxl.Balance

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_NumericalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Support. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def transposeRows (rs : List ℕ) : List ℕ :=
  (List.range (rs.headD 0)).map fun j => rs.countP (fun a => decide (j < a))

def RowsBand (M r : ℕ) (rs : List ℕ) : Prop :=
  ∃ k ∈ List.range 4,
    let d := k+1
    let q := testWidth M d
    d*q+7+d ≤ 2*M-1 ∧ 2*M-1 ≤ (rs.take d).sum ∧
      r ≤ ((List.range q).map fun j => (rs.countP (fun a => decide (j < a))-d)/2).sum

def ResidualProperty (M r : ℕ) (qs : List (List ℕ)) (ls : List (List ℕ))
    (rs : List ℕ) : Prop :=
  RowsBand M r rs ∨ RowsBand M r (transposeRows rs) ∨
    (∃ q ∈ qs, RowsDom rs q ∨ RowsDom (transposeRows rs) q) ∨
    rs ∈ ls ∨ transposeRows rs ∈ ls

end UniversalTensorSquare

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_RowSquareTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Square Tools. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def RowJoin (p q x y a b : List ℕ) : Prop :=
  GoodRows p ∧ GoodRows q ∧ GoodRows x ∧ GoodRows y ∧ GoodRows a ∧ GoodRows b ∧
  ((transposeRows x ++ transposeRows y).Perm (transposeRows p) ∨
    (transposeRows x ++ transposeRows y).Perm p) ∧
  ((transposeRows a ++ transposeRows b).Perm (transposeRows q) ∨
    (transposeRows p = p ∧ (transposeRows a ++ transposeRows b).Perm q))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RegionExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Region Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def boundsEntail (A B : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ B, 0 < p.1 ∧ ∃ q ∈ A, p.1 ≤ q.1 ∧ q.2 ≤ p.2

abbrev PrefixRegion := List (ℕ × ℕ) × List (ℕ × ℕ)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_ChoiceContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choice Contractions. -/

section

open scoped BigOperators
namespace Saxl.Columns

inductive EdgeChoices where
  | fallback
  | node (index : ℕ) (next : (ℕ × ℕ × ℕ) → EdgeChoices)

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ResidualTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residual Trees. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

inductive RowTree where
  | empty
  | node (key : List ℕ) (left right : RowTree)
  deriving DecidableEq

namespace RowTree

def find (rs : List ℕ) : RowTree → Bool
  | .empty => false
  | .node key l r => if rs = key then true else if compare rs key = Ordering.lt
      then l.find rs else r.find rs

def All (P : List ℕ → Prop) : RowTree → Prop
  | .empty => True
  | .node key l r => P key ∧ l.All P ∧ r.All P

end RowTree

def TreeResidual (M r : ℕ) (qs : List (List ℕ)) (t : RowTree) (rs : List ℕ) : Prop :=
  ResidualProperty M r qs [] rs ∨ t.find rs = true ∨ t.find (transposeRows rs) = true

end UniversalTensorSquare
end
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
open Saxl Saxl.Balance Saxl.Columns

def degreeRows116_1 : List ℕ := [20,11,11,11,11,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion116_0 : PrefixRegion := ([(2,22),(3,51),(4,52)], [(2,22),(3,51),(4,52)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion118_0 : PrefixRegion := ([(2,22),(3,53),(4,54)], [(2,22),(3,53),(4,54)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion14_0 : PrefixRegion := ([(5,11)], [(6,13)])
def degreeRegion14_2 : PrefixRegion := ([(6,13)], [(6,13)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion16_0 : PrefixRegion := ([(3,9)], [(5,15)])
def degreeRegion16_1 : PrefixRegion := ([(4,12)], [(4,12)])
def degreeRegion16_2 : PrefixRegion := ([(4,12)], [(5,15)])
def degreeRegion16_5 : PrefixRegion := ([(5,15)], [(5,15)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion18_0 : PrefixRegion := ([(3,9)], [(6,17)])
def degreeRegion18_1 : PrefixRegion := ([(4,12)], [(5,15)])
def degreeRegion18_2 : PrefixRegion := ([(4,12)], [(6,17)])
def degreeRegion18_4 : PrefixRegion := ([(5,15)], [(5,15)])
def degreeRegion18_5 : PrefixRegion := ([(5,15)], [(6,17)])
def degreeRegion18_9 : PrefixRegion := ([(6,17)], [(6,17)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion19_0 : PrefixRegion := ([(1,8),(5,14)], [(1,8),(5,14)])
def degreeRegion19_1 : PrefixRegion := ([(1,8),(7,18)], [(1,8),(7,18)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion20_0 : PrefixRegion := ([(1,5)], [(1,5)])
def degreeRegion20_1 : PrefixRegion := ([(1,5)], [(2,9)])
def degreeRegion20_2 : PrefixRegion := ([(1,5)], [(3,13)])
def degreeRegion20_3 : PrefixRegion := ([(1,5)], [(4,16)])
def degreeRegion20_5 : PrefixRegion := ([(2,9)], [(4,16)])
def degreeRegion20_6 : PrefixRegion := ([(2,9)], [(5,19)])
def degreeRegion20_8 : PrefixRegion := ([(3,13)], [(3,13)])
def degreeRegion20_9 : PrefixRegion := ([(3,13)], [(4,16)])
def degreeRegion20_10 : PrefixRegion := ([(3,13)], [(5,19)])
def degreeRegion20_14 : PrefixRegion := ([(4,16)], [(4,16)])
def degreeRegion20_15 : PrefixRegion := ([(4,16)], [(5,19)])
def degreeRegion20_19 : PrefixRegion := ([(5,19)], [(5,19)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion22_0 : PrefixRegion := ([(2,8)], [(6,21)])
def degreeRegion22_1 : PrefixRegion := ([(3,12)], [(5,18)])
def degreeRegion22_2 : PrefixRegion := ([(3,12)], [(6,21)])
def degreeRegion22_3 : PrefixRegion := ([(4,15)], [(4,15)])
def degreeRegion22_4 : PrefixRegion := ([(4,15)], [(5,18)])
def degreeRegion22_5 : PrefixRegion := ([(4,15)], [(6,21)])
def degreeRegion22_8 : PrefixRegion := ([(5,18)], [(5,18)])
def degreeRegion22_9 : PrefixRegion := ([(5,18)], [(6,21)])
def degreeRegion22_14 : PrefixRegion := ([(6,21)], [(6,21)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion24_0 : PrefixRegion := ([(1,7)], [(1,7)])
def degreeRegion24_1 : PrefixRegion := ([(1,7)], [(2,11)])
def degreeRegion24_2 : PrefixRegion := ([(1,7)], [(3,15)])
def degreeRegion24_3 : PrefixRegion := ([(1,7)], [(4,19)])
def degreeRegion24_4 : PrefixRegion := ([(1,7)], [(5,23)])
def degreeRegion24_6 : PrefixRegion := ([(2,11)], [(2,11)])
def degreeRegion24_7 : PrefixRegion := ([(2,11)], [(3,15)])
def degreeRegion24_8 : PrefixRegion := ([(2,11)], [(4,19)])
def degreeRegion24_9 : PrefixRegion := ([(2,11)], [(5,23)])
def degreeRegion24_12 : PrefixRegion := ([(3,15)], [(3,15)])
def degreeRegion24_13 : PrefixRegion := ([(3,15)], [(4,19)])
def degreeRegion24_14 : PrefixRegion := ([(3,15)], [(5,23)])
def degreeRegion24_18 : PrefixRegion := ([(4,19)], [(4,19)])
def degreeRegion24_19 : PrefixRegion := ([(4,19)], [(5,23)])
def degreeRegion24_24 : PrefixRegion := ([(5,23)], [(5,23)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion26_0 : PrefixRegion := ([(2,10)], [(5,22)])
def degreeRegion26_1 : PrefixRegion := ([(2,10)], [(6,25)])
def degreeRegion26_2 : PrefixRegion := ([(3,14)], [(4,18)])
def degreeRegion26_3 : PrefixRegion := ([(3,14)], [(5,22)])
def degreeRegion26_4 : PrefixRegion := ([(3,14)], [(6,25)])
def degreeRegion26_6 : PrefixRegion := ([(4,18)], [(4,18)])
def degreeRegion26_7 : PrefixRegion := ([(4,18)], [(5,22)])
def degreeRegion26_8 : PrefixRegion := ([(4,18)], [(6,25)])
def degreeRegion26_12 : PrefixRegion := ([(5,22)], [(5,22)])
def degreeRegion26_13 : PrefixRegion := ([(5,22)], [(6,25)])
def degreeRegion26_18 : PrefixRegion := ([(6,25)], [(6,25)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion31_0 : PrefixRegion := ([(1,10),(3,14)], [(1,11),(6,26)])
def degreeRegion31_1 : PrefixRegion := ([(1,10),(3,14)], [(1,11),(7,30)])
def degreeRegion31_2 : PrefixRegion := ([(1,10),(4,18)], [(1,10),(5,22)])
def degreeRegion31_3 : PrefixRegion := ([(1,10),(4,18)], [(1,10),(6,26)])
def degreeRegion31_4 : PrefixRegion := ([(1,10),(4,18)], [(1,10),(7,30)])
def degreeRegion31_6 : PrefixRegion := ([(1,10),(5,22)], [(1,10),(5,22)])
def degreeRegion31_7 : PrefixRegion := ([(1,10),(5,22)], [(1,10),(6,26)])
def degreeRegion31_8 : PrefixRegion := ([(1,10),(5,22)], [(1,10),(7,30)])
def degreeRegion31_11 : PrefixRegion := ([(1,10),(6,26)], [(1,10),(6,26)])
def degreeRegion31_12 : PrefixRegion := ([(1,10),(6,26)], [(1,10),(7,30)])
def degreeRegion31_16 : PrefixRegion := ([(1,10),(7,30)], [(1,10),(7,30)])
def degreeRegion31_19 : PrefixRegion := ([(2,10),(3,14)], [(7,30)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion35_0 : PrefixRegion := ([(1,10),(3,15)], [(1,15),(6,30)])
def degreeRegion35_1 : PrefixRegion := ([(1,10),(3,15)], [(1,15),(7,34)])
def degreeRegion35_2 : PrefixRegion := ([(1,10),(3,18),(4,20)], [(1,15),(5,25)])
def degreeRegion35_3 : PrefixRegion := ([(1,10),(3,18),(4,20)], [(1,15),(6,30)])
def degreeRegion35_4 : PrefixRegion := ([(1,10),(3,18),(4,20)], [(1,15),(7,34)])
def degreeRegion35_5 : PrefixRegion := ([(1,10),(3,18),(5,25)], [(1,15),(5,25)])
def degreeRegion35_6 : PrefixRegion := ([(1,10),(3,18),(5,25)], [(1,15),(6,30)])
def degreeRegion35_7 : PrefixRegion := ([(1,10),(3,18),(5,25)], [(1,15),(7,34)])
def degreeRegion35_8 : PrefixRegion := ([(1,10),(3,18),(6,30)], [(1,15),(5,25)])
def degreeRegion35_9 : PrefixRegion := ([(1,10),(3,18),(6,30)], [(1,15),(6,30)])
def degreeRegion35_10 : PrefixRegion := ([(1,10),(3,18),(6,30)], [(1,15),(7,34)])
def degreeRegion35_11 : PrefixRegion := ([(1,10),(3,18),(7,34)], [(1,15),(5,25)])
def degreeRegion35_12 : PrefixRegion := ([(1,10),(3,18),(7,34)], [(1,15),(6,30)])
def degreeRegion35_13 : PrefixRegion := ([(1,10),(3,18),(7,34)], [(1,15),(7,34)])
def degreeRegion35_14 : PrefixRegion := ([(1,10),(4,20)], [(1,10),(5,25)])
def degreeRegion35_15 : PrefixRegion := ([(1,10),(4,20)], [(1,10),(6,30)])
def degreeRegion35_16 : PrefixRegion := ([(1,10),(4,20)], [(1,10),(7,34)])
def degreeRegion35_18 : PrefixRegion := ([(1,10),(5,25)], [(1,10),(5,25)])
def degreeRegion35_19 : PrefixRegion := ([(1,10),(5,25)], [(1,10),(6,30)])
def degreeRegion35_20 : PrefixRegion := ([(1,10),(5,25)], [(1,10),(7,34)])
def degreeRegion35_23 : PrefixRegion := ([(1,10),(6,30)], [(1,10),(6,30)])
def degreeRegion35_24 : PrefixRegion := ([(1,10),(6,30)], [(1,10),(7,34)])
def degreeRegion35_28 : PrefixRegion := ([(1,10),(7,34)], [(1,10),(7,34)])
def degreeRegion35_29 : PrefixRegion := ([(1,15),(3,18),(5,25)], [(1,15),(3,18),(5,25)])
def degreeRegion35_44 : PrefixRegion := ([(2,10),(3,18)], [(7,34)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 116. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions116 : List PrefixRegion := [degreeRegion116_0]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 118. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions118 : List PrefixRegion := [degreeRegion118_0]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 14. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions14 : List PrefixRegion := [degreeRegion14_0,degreeRegion14_2]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 16. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions16 : List PrefixRegion := [degreeRegion16_0,degreeRegion16_1,degreeRegion16_2,degreeRegion16_5]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 18. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions18 : List PrefixRegion := [degreeRegion18_0,degreeRegion18_1,degreeRegion18_2,degreeRegion18_4,degreeRegion18_5,degreeRegion18_9]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 19. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions19 : List PrefixRegion := [degreeRegion19_0,degreeRegion19_1]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 20. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions20 : List PrefixRegion := [degreeRegion20_0,degreeRegion20_1,degreeRegion20_2,degreeRegion20_3,degreeRegion20_5,degreeRegion20_6,degreeRegion20_8,degreeRegion20_9,degreeRegion20_10,degreeRegion20_14,degreeRegion20_15,degreeRegion20_19]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 22. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions22 : List PrefixRegion := [degreeRegion22_0,degreeRegion22_1,degreeRegion22_2,degreeRegion22_3,degreeRegion22_4,degreeRegion22_5,degreeRegion22_8,degreeRegion22_9,degreeRegion22_14]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 24. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions24 : List PrefixRegion := [degreeRegion24_0,degreeRegion24_1,degreeRegion24_2,degreeRegion24_3,degreeRegion24_4,degreeRegion24_6,degreeRegion24_7,degreeRegion24_8,degreeRegion24_9,degreeRegion24_12,degreeRegion24_13,degreeRegion24_14,degreeRegion24_18,degreeRegion24_19,degreeRegion24_24]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 26. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions26 : List PrefixRegion := [degreeRegion26_0,degreeRegion26_1,degreeRegion26_2,degreeRegion26_3,degreeRegion26_4,degreeRegion26_6,degreeRegion26_7,degreeRegion26_8,degreeRegion26_12,degreeRegion26_13,degreeRegion26_18]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 31. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions31 : List PrefixRegion := [degreeRegion31_0,degreeRegion31_1,degreeRegion31_2,degreeRegion31_3,degreeRegion31_4,degreeRegion31_6,degreeRegion31_7,degreeRegion31_8,degreeRegion31_11,degreeRegion31_12,degreeRegion31_16,degreeRegion31_19]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 35. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions35 : List PrefixRegion := [degreeRegion35_0,degreeRegion35_1,degreeRegion35_2,degreeRegion35_3,degreeRegion35_4,degreeRegion35_5,degreeRegion35_6,degreeRegion35_7,degreeRegion35_8,degreeRegion35_9,degreeRegion35_10,degreeRegion35_11,degreeRegion35_12,degreeRegion35_13,degreeRegion35_14,degreeRegion35_15,degreeRegion35_16,degreeRegion35_18,degreeRegion35_19,degreeRegion35_20,degreeRegion35_23,degreeRegion35_24,degreeRegion35_28,degreeRegion35_29,degreeRegion35_44]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_RowChecker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Checker. -/

section

namespace UniversalTensorSquare

def quickRejected (fuel n upper : ℕ) (A B : List (ℕ × ℕ)) : Bool :=
  decide (n < fuel) || decide (fuel*upper < n) ||
    A.any (fun p => decide (0 < p.1) && decide (p.2 < fuel)) ||
    B.any (fun p => decide (fuel ≤ p.1) && decide (p.2 < n)) ||
    A.any (fun p => decide (p.2*upper < n*min p.1 upper)) ||
    B.any (fun p => decide (p.2*fuel < n*min p.1 fuel))

def quickAllowed (a : ℕ) (A B : List (ℕ × ℕ)) : Bool :=
  A.all (fun p => decide (min p.1 a ≤ p.2)) &&
    B.all (fun p => decide (p.1 = 0) || decide (a ≤ p.2))

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_UnionRowChecker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Union Row Checker. -/

section

namespace UniversalTensorSquare

def liveRegions (fuel n upper : ℕ) (regions : List PrefixRegion) : List PrefixRegion :=
  regions.filter fun R => !quickRejected fuel n upper R.1 R.2

def nextRegions (a : ℕ) (regions : List PrefixRegion) : List PrefixRegion :=
  regions.filterMap fun R => if quickAllowed a R.1 R.2 then
    some (clipBudget R.1 a,rowBudget R.2 a) else none

def checkRegionPrefixes (P : List ℕ → Bool) : ℕ → ℕ → ℕ →
    List PrefixRegion → List ℕ → Bool
  | fuel,n,upper,regions,pref =>
    let alive := liveRegions fuel n upper regions
    if alive.isEmpty then true else
      match fuel with
      | 0 => if n = 0 then P pref.reverse else true
      | k+1 =>
          let lo := max 1 (n/(k+1))
          (List.range' lo (min n upper+1-lo)).all fun a =>
            if n ≤ (k+1)*a then
              checkRegionPrefixes P k (n-a) a (nextRegions a alive) (a::pref)
            else true

end UniversalTensorSquare
end

end OAI
end


