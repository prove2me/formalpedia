-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
-- name    : GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:35.279744+00:00
-- url     : https://prove2.me/theorems/1167df6e-1400-4c71-9392-f28ee4632f19
-- title:
--   Statements Cusp
-- statement:
--   Definitions and structural lemmas for Statements Cusp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/StatementsCusp.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Period
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
open Matrix
noncomputable section
def leadMinor {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (i : ℕ) : ℝ :=
  (Matrix.of fun a b : Fin i =>
    if h : (a : ℕ) < d ∧ (b : ℕ) < d then S ⟨a, h.1⟩ ⟨b, h.2⟩ else 0).det
def pivot {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (i : ℕ) : ℝ :=
  leadMinor S (i + 1) / leadMinor S i
def intGram {d k : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (N : Matrix (Fin d) (Fin k) ℤ) :
    Matrix (Fin k) (Fin k) ℝ :=
  (N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)
def LeadMinorLeading.Statement : Prop :=
  ∀ (d : ℕ) (S : Matrix (Fin d) (Fin d) ℝ) (m : ℕ) (h : m ≤ d) (j : ℕ), j ≤ m →
    leadMinor (S.submatrix (Fin.castLE h) (Fin.castLE h)) j = leadMinor S j
def LeadMinorBasic.Statement : Prop :=
  ∀ (d : ℕ) (S : Matrix (Fin d) (Fin d) ℝ), leadMinor S 0 = 1 ∧ leadMinor S d = S.det ∧
    (S.PosDef → ∀ i, i ≤ d → 0 < leadMinor S i)
def PivotInvDiag.Statement : Prop :=
  ∀ (d : ℕ) (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ), S.PosDef →
    S⁻¹ (Fin.last d) (Fin.last d) * pivot S d = 1
def PivotLast.Statement : Prop :=
  ∀ (d : ℕ) (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ), S.PosDef → ∀ x : Fin (d + 1) → ℝ,
    x (Fin.last d) ^ 2 * pivot S d ≤ MCSchur.qf S x
def PivotBounds.Statement : Prop :=
  ∀ (d : ℕ) (S : Matrix (Fin d) (Fin d) ℝ), S.PosDef → ∀ i : Fin d,
    pivot S i ≤ S i i ∧
      ∀ ε : ℝ, 0 < ε → (∀ y : Fin d → ℝ, ε * y i ^ 2 ≤ MCSchur.qf S y) → ε ≤ pivot S i
def UnimodularLast.Statement : Prop :=
  ∀ (k : ℕ) (ρ : Fin (k + 1) → ℤ), ρ ≠ 0 → ∃ U : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ,
    IsUnit U.det ∧ (∀ j : Fin k, (ρ ᵥ* U) (Fin.castSucc j) = 0) ∧ (ρ ᵥ* U) (Fin.last k) ≠ 0
def SchurDetBound.Statement : Prop :=
  ∀ (k : ℕ) (G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ), Gᵀ = G →
    0 < (G.submatrix Fin.castSucc Fin.castSucc).det → ∀ t : ℝ,
    (∀ v : Fin (k + 1) → ℝ, v (Fin.last k) = 1 → t ≤ MCSchur.qf G v) →
    t * (G.submatrix Fin.castSucc Fin.castSucc).det ≤ G.det
def IntGramQf.Statement : Prop :=
  ∀ (d k : ℕ) (S : Matrix (Fin d) (Fin d) ℝ) (N : Matrix (Fin d) (Fin k) ℤ) (z : Fin k → ℝ),
    MCSchur.qf (intGram S N) z = MCSchur.qf S (N.map (Int.cast : ℤ → ℝ) *ᵥ z)
def IntGramUnimodular.Statement : Prop :=
  ∀ (d k : ℕ) (S : Matrix (Fin d) (Fin d) ℝ) (N : Matrix (Fin d) (Fin k) ℤ)
    (U : Matrix (Fin k) (Fin k) ℤ), IsUnit U.det → (intGram S (N * U)).det = (intGram S N).det
def IntGramDropLast.Statement : Prop :=
  ∀ (d k : ℕ) (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (N : Matrix (Fin (d + 1)) (Fin k) ℤ),
    (∀ j, N (Fin.last d) j = 0) →
      intGram S N = intGram (S.submatrix Fin.castSucc Fin.castSucc) (N.submatrix Fin.castSucc id)
def IntGramSubLast.Statement : Prop :=
  ∀ (d k : ℕ) (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (M : Matrix (Fin (d + 1)) (Fin (k + 1)) ℤ),
    (∀ j : Fin k, M (Fin.last d) (Fin.castSucc j) = 0) →
      (intGram S M).submatrix Fin.castSucc Fin.castSucc =
        intGram (S.submatrix Fin.castSucc Fin.castSucc) (M.submatrix Fin.castSucc Fin.castSucc)
def GramPivotProduct.Statement : Prop :=
  ∀ (d : ℕ) (S : Matrix (Fin d) (Fin d) ℝ), S.PosDef → ∀ (k : ℕ) (N : Matrix (Fin d) (Fin k) ℤ),
    (∀ c : Fin k → ℤ, N *ᵥ c = 0 → c = 0) →
      ∃ P : Finset ℕ, (∀ i ∈ P, i < d) ∧ ∏ i ∈ P, pivot S i ≤ (intGram S N).det
def PivotProductBound.Statement : Prop :=
  ∀ (d r : ℕ) (S : Matrix (Fin d) (Fin d) ℝ), S.PosDef → r ≤ d → ∀ α ε : ℝ, 0 < ε →
    (∀ i, i < r → pivot S i ≤ α) → (∀ i, r ≤ i → i < d → ε ≤ pivot S i) →
    ∀ P : Finset ℕ, (∀ i ∈ P, i < d) →
      min 1 ε ^ d * (max 1 α)⁻¹ ^ r * leadMinor S r ≤ ∏ i ∈ P, pivot S i
def periodBasis {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Fin (g + g) → Fin g → ℂ :=
  Fin.append (fun k => Pi.single k 1) (fun k => τ *ᵥ Pi.single k 1)
def periodGram {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin (g + g)) (Fin (g + g)) ℝ :=
  Matrix.of fun i j => hermPair (τ.map Complex.im)⁻¹ (periodBasis τ i) (periodBasis τ j)
def PeriodHermValue.Statement : Prop :=
  ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), IsUnit (τ.map Complex.im).det → ∀ α β : Fin g → ℝ,
    hermValue (τ.map Complex.im)⁻¹ ((fun k => (α k : ℂ)) + τ *ᵥ fun k => (β k : ℂ)) =
      MCSchur.qf (τ.map Complex.im)⁻¹ (α + τ.map Complex.re *ᵥ β) +
        MCSchur.qf (τ.map Complex.im) β
def PeriodGramPosDef.Statement : Prop :=
  ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), (τ.map Complex.im).PosDef →
    (periodGram τ).PosDef ∧ ∀ x : Fin (g + g) → ℝ,
      MCSchur.qf (periodGram τ) x =
        MCSchur.qf (τ.map Complex.im)⁻¹
            ((fun k => x (Fin.castAdd g k)) + τ.map Complex.re *ᵥ fun k => x (Fin.natAdd g k)) +
          MCSchur.qf (τ.map Complex.im) (fun k => x (Fin.natAdd g k))
def PeriodLatticeCovolume.Statement : Prop :=
  ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (v : Fin k → Fin g → ℂ),
    (∀ j, v j ∈ periodLattice τ) → LinearIndependent ℤ v →
      ∃ N : Matrix (Fin (g + g)) (Fin k) ℤ,
        (∀ j, v j = ∑ i, (N i j : ℂ) • periodBasis τ i) ∧
        (∀ c : Fin k → ℤ, N *ᵥ c = 0 → c = 0) ∧
        covolume (τ.map Complex.im) v = Real.sqrt (intGram (periodGram τ) N).det
def LeadingCovolume.Statement : Prop :=
  ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (r : ℕ) (h : r ≤ g),
    covolume (τ.map Complex.im) (fun j : Fin r => Pi.single (Fin.castLE h j) (1 : ℂ)) =
      Real.sqrt (leadMinor (periodGram τ) r)
def ChartPeriodImPos.Statement : Prop :=
  ∀ (D : PeriodChartData) (z : Fin D.n → ℂ), z ∈ D.Ustar → ∀ ℓ : Fin D.a → ℂ,
    (∀ j, Complex.exp (ℓ j) = cuspCoord D.a_le z j) →
      ((D.period z ℓ).map Complex.im).PosDef ∧
        ∀ x : Fin D.g → ℝ, D.c * ∑ k, x k ^ 2 ≤ MCSchur.qf ((D.period z ℓ).map Complex.im) x
def ChartLowerBlockBound.Statement : Prop :=
  ∀ (D : PeriodChartData) (T : ToricBlock D), ∃ M : ℝ, 0 < M ∧ ∀ p ∈ D.K, ∀ ℓ : Fin D.a → ℂ,
    ∀ i l : Fin D.g, T.r ≤ i.val → ‖D.period p.1 ℓ i l‖ ≤ M
def CuspShortVectors.Statement : Prop :=
  ∀ (D : PeriodChartData) (T : ToricBlock D), ∃ c₁ : ℝ, 0 < c₁ ∧
    ∀ p ∈ D.K, p.1 ∈ D.Ustar → ∀ ℓ : Fin D.a → ℂ,
      (∀ j, Complex.exp (ℓ j) = cuspCoord D.a_le p.1 j) →
      ∀ a n : Fin D.g → ℤ, (n ≠ 0 ∨ ∃ k : Fin D.g, T.r ≤ k.val ∧ a k ≠ 0) →
        c₁ ≤ metricLength ((D.period p.1 ℓ).map Complex.im)
          (intVecC a + D.period p.1 ℓ *ᵥ intVecC n)
def CuspLeadingMinima.Statement : Prop :=
  ∀ (D : PeriodChartData) (T : ToricBlock D), ∀ p ∈ D.K, p.1 ∈ D.Ustar → ∀ ℓ : Fin D.a → ℂ,
    (∀ j, Complex.exp (ℓ j) = cuspCoord D.a_le p.1 j) →
      ∃ v : Fin T.r → Fin D.g → ℂ, (∀ j, v j ∈ leadingLattice D.g T.r) ∧ LinearIndependent ℤ v ∧
        ∀ j, metricLength ((D.period p.1 ℓ).map Complex.im) (v j) ≤ D.c ^ (-(1 / 2 : ℝ))
def CuspCoordinateBound.Statement : Prop :=
  ∀ (D : PeriodChartData) (T : ToricBlock D), ∃ ε : ℝ, 0 < ε ∧
    ∀ p ∈ D.K, p.1 ∈ D.Ustar → ∀ ℓ : Fin D.a → ℂ,
      (∀ j, Complex.exp (ℓ j) = cuspCoord D.a_le p.1 j) →
      ∀ (y : Fin (D.g + D.g) → ℝ) (i : Fin (D.g + D.g)), T.r ≤ i.val →
        ε * y i ^ 2 ≤ MCSchur.qf (periodGram (D.period p.1 ℓ)) y
def CuspCovolume.Statement : Prop :=
  ∀ (D : PeriodChartData) (T : ToricBlock D), ∃ c₂ : ℝ, 0 < c₂ ∧
    ∀ p ∈ D.K, p.1 ∈ D.Ustar → ∀ ℓ : Fin D.a → ℂ,
      (∀ j, Complex.exp (ℓ j) = cuspCoord D.a_le p.1 j) →
      ∀ (k : ℕ) (v : Fin k → Fin D.g → ℂ), (∀ j, v j ∈ periodLattice (D.period p.1 ℓ)) →
        LinearIndependent ℤ v →
        c₂ * covolume ((D.period p.1 ℓ).map Complex.im)
            (fun j : Fin T.r => Pi.single (Fin.castLE T.r_le j) (1 : ℂ)) ≤
          covolume ((D.period p.1 ℓ).map Complex.im) v
end
end GroundTheory.Heights₂.Heights


