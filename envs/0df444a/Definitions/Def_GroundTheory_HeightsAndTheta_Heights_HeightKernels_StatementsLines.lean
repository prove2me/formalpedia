-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:10.265295+00:00
-- url     : https://prove2.me/theorems/3727e14e-fc82-45bd-919d-4cbc07f66643
-- title:
--   Statements Lines
-- statement:
--   Definitions and structural lemmas for Statements Lines, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsLines.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder
noncomputable section
def stdLattice (K : Type*) [Field K] (k : ℕ) : Submodule (𝓞 K) (Fin k → K) :=
  Submodule.span (𝓞 K) (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K))
def idealIndex {K : Type*} [Field K] (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ :=
  genIndex (I : Submodule (𝓞 K) K).toAddSubgroup (1 : Submodule (𝓞 K) K).toAddSubgroup
def coordProj {K : Type*} [Field K] {n m k : ℕ} (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) :
    (Fin n → K) →ₗ[K] (Fin k → K) :=
  LinearMap.funLeft K K Sum.inr ∘ₗ B.equivFun.toLinearMap
def stdSumBasis (K : Type*) [Field K] (m k : ℕ) : Module.Basis (Fin m ⊕ Fin k) K (Fin (m + k) → K) :=
  (Pi.basisFun K (Fin (m + k))).reindex finSumFinEquiv.symm
def LinesLatticeBasis.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (ι : Type) [Fintype ι],
    Fintype.card ι = Module.finrank ℚ V → ∀ M : Submodule ℤ V, Submodule.IsLattice ℚ M →
      ∃ b : Module.Basis ι ℚ V, M = Submodule.span ℤ (Set.range b)
def LinesGenIndexDet.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (ι : Type) [Fintype ι]
    [DecidableEq ι] (bA bB : Module.Basis ι ℚ V) (A B : AddSubgroup V),
    A = AddSubgroup.closure (Set.range bA) → B = AddSubgroup.closure (Set.range bB) →
      genIndex A B = |((bA.det bB : ℚ) : ℝ)|
def LinesIsLattice.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (M : Submodule (𝓞 K) (ι → K)),
    (M.restrictScalars ℤ).FG → Submodule.span K (M : Set (ι → K)) = ⊤ →
      Submodule.IsLattice ℚ (M.restrictScalars ℤ)
def LinesGenIndexTrans.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (A B C : Submodule ℤ V),
    Submodule.IsLattice ℚ A → Submodule.IsLattice ℚ B → Submodule.IsLattice ℚ C →
      0 < genIndex A.toAddSubgroup B.toAddSubgroup ∧
        genIndex A.toAddSubgroup B.toAddSubgroup * genIndex B.toAddSubgroup C.toAddSubgroup =
          genIndex A.toAddSubgroup C.toAddSubgroup
def LinesGenIndexMono.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (A A' B : Submodule ℤ V),
    Submodule.IsLattice ℚ A → Submodule.IsLattice ℚ A' → Submodule.IsLattice ℚ B → A ≤ A' →
      genIndex A.toAddSubgroup B.toAddSubgroup ≤ genIndex A'.toAddSubgroup B.toAddSubgroup
def LinesGenIndexPi.Statement : Prop :=
  ∀ (η : Type) [Fintype η] (G : Type) [AddCommGroup G] (A B : η → AddSubgroup G),
    genIndex (AddSubgroup.pi Set.univ A) (AddSubgroup.pi Set.univ B) = ∏ i, genIndex (A i) (B i)
def LinesStdPi.Statement : Prop :=
  ∀ (K : Type) [Field K] (k : ℕ),
    (stdLattice K k).toAddSubgroup =
      AddSubgroup.pi Set.univ fun _ : Fin k => (1 : Submodule (𝓞 K) K).toAddSubgroup
def LinesStdIndexDet.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℕ) (V : Matrix (Fin k) (Fin k) K), V.det ≠ 0 →
    genIndex (stdLattice K k).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).toAddSubgroup =
      |((Algebra.norm ℚ V.det : ℚ) : ℝ)|
def LinesIdealIndexPos.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K), I ≠ 0 → 0 < idealIndex I
def LinesProductFormula.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : K), x ≠ 0 →
    ∑ σ : K →+* ℂ, Real.log ‖σ x‖ = Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)|
def LinesIdealLatticeFG.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K),
    (∀ x, a x ≠ 0) →
      (idealLattice a).FG ∧ Submodule.span K (idealLattice a : Set (Fin n → K)) = ⊤
def LinesIdealStdIndex.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℕ) (a : Fin k → FractionalIdeal (𝓞 K)⁰ K),
    genIndex (idealLattice a).toAddSubgroup (stdLattice K k).toAddSubgroup = ∏ j, idealIndex (a j)
def LinesGramChange.Statement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (ι : Type)
    [Fintype ι] (u : ι → Fin n → K) (P : Matrix ι ι K),
    gramAt h σ (fun a => ∑ b, P b a • u b) = (P.map σ)ᴴ * gramAt h σ u * P.map σ
def LinesGramPosDef.Statement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (ι : Type)
    [Fintype ι] (u : ι → Fin n → K), h.PosDef → LinearIndependent K u → (gramAt h σ u).PosDef
def LinesGramDetChange.Statement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (ι : Type)
    [Fintype ι] [DecidableEq ι] (B : Module.Basis ι K (Fin n → K)) (u : ι → Fin n → K),
    (gramAt h σ u).det =
      star (σ (B.toMatrix u).det) * σ (B.toMatrix u).det * (gramAt h σ (⇑B)).det
def LinesFischer.Statement : Prop :=
  ∀ (m k : Type) [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (M : Matrix (m ⊕ k) (m ⊕ k) ℂ), M.PosDef →
      M.det.re ≤ M.toBlocks₁₁.det.re * M.toBlocks₂₂.det.re
def LinesDiagGram.Statement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (d : Fin n → ℝ) (σ : K →+* ℂ) (k : ℕ) (τ : Fin k → Fin n),
    Function.Injective τ →
      gramAt (Matrix.diagonal fun x => (d x : ℂ)) σ (fun j => (Pi.single (τ j) 1 : Fin n → K)) =
        Matrix.diagonal fun j => (d (τ j) : ℂ)
def LinesGramFischerBound.Statement : Prop :=
  ∀ (K : Type) [Field K] (n m k : ℕ) (d : Fin n → ℝ) (σ : K →+* ℂ) (b : Fin m → Fin n → K)
    (τ : Fin k → Fin n), (∀ x, 0 < d x) → Function.Injective τ →
    LinearIndependent K (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K)) →
      (gramAt (Matrix.diagonal fun x => (d x : ℂ)) σ
          (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K))).det.re ≤
        (gramAt (Matrix.diagonal fun x => (d x : ℂ)) σ b).det.re * ∏ j, d (τ j)
def LinesExtendBasis.Statement : Prop :=
  ∀ (K : Type) [Field K] (n m k : ℕ) (b : Fin m → Fin n → K), LinearIndependent K b → m + k = n →
    ∃ τ : Fin k → Fin n, Function.Injective τ ∧
      LinearIndependent K (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K))
def LinesCoordDet.Statement : Prop :=
  ∀ (K : Type) [Field K] (n m k : ℕ) (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K))
    (b : Fin m → Fin n → K) (c : Fin k → Fin n → K),
    (∀ i, B (Sum.inl i) = b i) → LinearIndependent K (Sum.elim b c) →
      (B.toMatrix (Sum.elim b c)).det = (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det ∧
        (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det ≠ 0
def LinesCoordImage.Statement : Prop :=
  ∀ (K : Type) [Field K] (n m k : ℕ) (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K))
    (b : Fin m → Fin n → K) (c : Fin k → Fin n → K) (j : Fin k),
    coordProj B (c j) = (B.toMatrix (Sum.elim b c)).toBlocks₂₂ *ᵥ (Pi.single j 1 : Fin k → K)
def LinesQuotIndex.Statement : Prop :=
  ∀ (K : Type) [Field K] (n m k : ℕ) (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K))
    (L : Submodule (𝓞 K) (Fin n → K)) (c : Fin k → Fin n → K),
    genIndex (L ⊔ (Submodule.span K (Set.range fun i => B (Sum.inl i))).restrictScalars
          (𝓞 K)).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range c) ⊔
          (Submodule.span K (Set.range fun i => B (Sum.inl i))).restrictScalars
            (𝓞 K)).toAddSubgroup =
      genIndex (L.map ((coordProj B).restrictScalars (𝓞 K))).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c))).toAddSubgroup
def LinesProjLattice.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n m k : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (τ : Fin k → Fin n),
    (∀ x, a x ≠ 0) → (∀ j, B (Sum.inr j) = Pi.single (τ j) 1) → Function.Injective τ →
      (((idealLattice a).map ((coordProj B).restrictScalars (𝓞 K))).restrictScalars ℤ).FG ∧
      Submodule.span K (((idealLattice a).map ((coordProj B).restrictScalars (𝓞 K)) :
          Submodule (𝓞 K) (Fin k → K)) : Set (Fin k → K)) = ⊤ ∧
      idealLattice (fun j => a (τ j)) ≤ (idealLattice a).map ((coordProj B).restrictScalars (𝓞 K))
def LinesQuotIndexSplit.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n m k : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (τ : Fin k → Fin n), (∀ x, a x ≠ 0) → (∀ i, B (Sum.inl i) = b i) →
    (∀ j, B (Sum.inr j) = Pi.single (τ j) 1) → Function.Injective τ →
    LinearIndependent K (Sum.elim b c) →
      genIndex (idealLattice a ⊔ (Submodule.span K (Set.range b)).restrictScalars
            (𝓞 K)).toAddSubgroup
          (Submodule.span (𝓞 K) (Set.range c) ⊔
            (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)).toAddSubgroup =
        genIndex ((idealLattice a).map ((coordProj B).restrictScalars (𝓞 K))).toAddSubgroup
            (stdLattice K k).toAddSubgroup *
          |((Algebra.norm ℚ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det : ℚ) : ℝ)|
def LinesProjIndexLower.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n m k : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (τ : Fin k → Fin n),
    (∀ x, a x ≠ 0) → (∀ j, B (Sum.inr j) = Pi.single (τ j) 1) → Function.Injective τ →
      ∏ j, idealIndex (a (τ j)) ≤
        genIndex ((idealLattice a).map ((coordProj B).restrictScalars (𝓞 K))).toAddSubgroup
          (stdLattice K k).toAddSubgroup
def LinesLineDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ) (x : Fin n),
    subDegree (idealLattice a) (diagMetric d) (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K)) =
      Real.log (idealIndex (a x)) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (d σ x)
def LinesQuotIndexLog.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n m k : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (τ : Fin k → Fin n), (∀ x, a x ≠ 0) → (∀ i, B (Sum.inl i) = b i) →
    (∀ j, B (Sum.inr j) = Pi.single (τ j) 1) → Function.Injective τ →
    LinearIndependent K (Sum.elim b c) →
      ∑ j, Real.log (idealIndex (a (τ j))) +
          ∑ σ : K →+* ℂ, Real.log ‖σ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det‖ ≤
        Real.log (genIndex
          (idealLattice a ⊔ (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)).toAddSubgroup
          (Submodule.span (𝓞 K) (Set.range c) ⊔
            (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)).toAddSubgroup)
def LinesQuotGramLog.Statement : Prop :=
  ∀ (K : Type) [Field K] (n m k : ℕ) (d : Fin n → ℝ) (σ : K →+* ℂ)
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (τ : Fin k → Fin n), (∀ x, 0 < d x) → (∀ i, B (Sum.inl i) = b i) →
    (∀ j, B (Sum.inr j) = Pi.single (τ j) 1) → Function.Injective τ →
    LinearIndependent K (Sum.elim b c) →
      Real.log (gramAt (Matrix.diagonal fun x => (d x : ℂ)) σ (Sum.elim b c)).det.re -
          Real.log (gramAt (Matrix.diagonal fun x => (d x : ℂ)) σ b).det.re ≤
        ∑ j, Real.log (d (τ j)) + 2 * Real.log ‖σ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det‖
def LinesQuotDegreeBound.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ), (∀ x, a x ≠ 0) → (∀ σ x, 0 < d σ x) →
    ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K),
      LinearIndependent K (Sum.elim b c) → m + k = n →
      ∃ τ : Fin k → Fin n, Function.Injective τ ∧
        ∑ j, (Real.log (idealIndex (a (τ j))) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (d σ (τ j))) ≤
          quotDegree (idealLattice a) (diagMetric d) b c
theorem stdSumBasis_inl (K : Type*) [Field K] (m k : ℕ) (i : Fin m) :
    stdSumBasis K m k (Sum.inl i) = Pi.single (Fin.castAdd k i) 1 := by
  simp [stdSumBasis]
theorem stdSumBasis_inr (K : Type*) [Field K] (m k : ℕ) (j : Fin k) :
    stdSumBasis K m k (Sum.inr j) = Pi.single (Fin.natAdd m j) 1 := by
  simp [stdSumBasis]
theorem stdSumBasis_elim (K : Type*) [Field K] (m k : ℕ) :
    Sum.elim (fun i => stdSumBasis K m k (Sum.inl i)) (fun j => stdSumBasis K m k (Sum.inr j)) =
      ⇑(stdSumBasis K m k) := by
  funext x; cases x <;> rfl
theorem stdLattice_isLattice_example :
    Submodule.IsLattice ℚ ((stdLattice ℚ 1).restrictScalars ℤ) where
  fg := (Submodule.fg_span (Set.finite_range _)).restrictScalars
  span_eq_top := by
    rw [eq_top_iff]
    intro v _
    have h1 : (Pi.single 0 1 : Fin 1 → ℚ) ∈
        Submodule.span ℚ (((stdLattice ℚ 1).restrictScalars ℤ : Submodule ℤ (Fin 1 → ℚ)) :
          Set (Fin 1 → ℚ)) :=
      Submodule.subset_span (Submodule.subset_span ⟨0, rfl⟩)
    have hv : v = v 0 • (Pi.single 0 1 : Fin 1 → ℚ) := by
      funext i; fin_cases i; simp
    rw [hv]; exact Submodule.smul_mem _ _ h1
example : Fintype.card (Fin 1) = Module.finrank ℚ (Fin 1 → ℚ) ∧
    ((stdLattice ℚ 1).restrictScalars ℤ).FG ∧
    Submodule.span ℚ ((stdLattice ℚ 1 : Submodule (𝓞 ℚ) (Fin 1 → ℚ)) : Set (Fin 1 → ℚ)) = ⊤ ∧
    Submodule.IsLattice ℚ ((stdLattice ℚ 1).restrictScalars ℤ) ∧
    (stdLattice ℚ 1).restrictScalars ℤ ≤ (stdLattice ℚ 1).restrictScalars ℤ :=
  ⟨by simp, stdLattice_isLattice_example.fg, stdLattice_isLattice_example.span_eq_top,
    stdLattice_isLattice_example, le_rfl⟩
example : ∃ A B : AddSubgroup (Fin 2 → ℚ),
    A = AddSubgroup.closure (Set.range (Pi.basisFun ℚ (Fin 2))) ∧
    B = AddSubgroup.closure (Set.range ((Pi.basisFun ℚ (Fin 2)).map (LinearEquiv.smulOfNeZero ℚ _
      (2 : ℚ) two_ne_zero))) :=
  ⟨_, _, rfl, rfl⟩
example : (Matrix.diagonal fun _ : Fin 2 => (2 : ℚ)).det ≠ 0 ∧
    (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ) ≠ 0 ∧ (2 : ℚ) ≠ 0 ∧
    ∀ x : Fin 2, (fun _ => (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ)) x ≠ 0 :=
  ⟨by simp [Matrix.det_diagonal], one_ne_zero, two_ne_zero, fun _ => one_ne_zero⟩
example : (1 : Matrix (Fin 2) (Fin 2) ℂ).PosDef ∧ LinearIndependent ℚ (Pi.basisFun ℚ (Fin 2)) ∧
    (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ).PosDef ∧
    Function.Injective (Fin.natAdd 1 : Fin 1 → Fin (1 + 1)) :=
  ⟨Matrix.PosDef.one, (Pi.basisFun ℚ (Fin 2)).linearIndependent, Matrix.PosDef.one,
    Fin.natAdd_injective _ _⟩
example :
    let B := stdSumBasis ℚ 1 1
    let b : Fin 1 → Fin (1 + 1) → ℚ := fun i => Pi.single (Fin.castAdd 1 i) 1
    let c : Fin 1 → Fin (1 + 1) → ℚ := fun j => Pi.single (Fin.natAdd 1 j) 1
    let τ : Fin 1 → Fin (1 + 1) := Fin.natAdd 1
    LinearIndependent ℚ b ∧ 1 + 1 = 1 + 1 ∧ (∀ _ : Fin (1 + 1), (0 : ℝ) < 1) ∧
    (∀ x : Fin (1 + 1), (fun _ => (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ)) x ≠ 0) ∧
    (∀ i, B (Sum.inl i) = b i) ∧ (∀ j, B (Sum.inr j) = Pi.single (τ j) 1) ∧
    Function.Injective τ ∧ LinearIndependent ℚ (Sum.elim b c) ∧
    LinearIndependent ℚ (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin (1 + 1) → ℚ)) := by
  intro B b c τ
  have hB : LinearIndependent ℚ (Sum.elim b c) := by
    have h := (stdSumBasis ℚ 1 1).linearIndependent
    rw [← stdSumBasis_elim] at h
    simpa only [stdSumBasis_inl, stdSumBasis_inr] using h
  exact ⟨hB.comp Sum.inl Sum.inl_injective, rfl, fun _ => one_pos, fun _ => one_ne_zero,
    fun i => stdSumBasis_inl ℚ 1 1 i, fun j => stdSumBasis_inr ℚ 1 1 j,
    Fin.natAdd_injective _ _, hB, hB⟩
example : (∀ x : Fin 2, (fun _ => (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ)) x ≠ 0) ∧
    (∀ (σ : ℚ →+* ℂ) (x : Fin 2), (0 : ℝ) < (fun _ _ => (1 : ℝ)) σ x) ∧
    LinearIndependent ℚ (Sum.elim (fun i : Fin 1 => (Pi.single (Fin.castAdd 1 i) 1 : Fin (1 + 1) → ℚ))
      fun j : Fin 1 => (Pi.single (Fin.natAdd 1 j) 1 : Fin (1 + 1) → ℚ)) ∧ 1 + 1 = 2 := by
  refine ⟨fun _ => one_ne_zero, fun _ _ => one_pos, ?_, rfl⟩
  have h := (stdSumBasis ℚ 1 1).linearIndependent
  rw [← stdSumBasis_elim] at h
  simpa only [stdSumBasis_inl, stdSumBasis_inr] using h
end
end GroundTheory.Heights₂.Heights


