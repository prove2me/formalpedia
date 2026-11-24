-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:46.467642+00:00
-- url     : https://prove2.me/theorems/0adca0dc-8bcb-4421-8a96-46289ebd5bce
-- title:
--   Statements Mahler
-- statement:
--   Definitions and structural lemmas for Statements Mahler, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
def nrmGroups (h : HermNorm n) (k : ℕ) (u : Fin k × Fin n → ℂ) : Fin k × Fin n → ℂ :=
  fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij
def consGroup {k : ℕ} (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ) : Fin (k + 1) × Fin n → ℂ :=
  fun ij => Fin.cases (motive := fun _ => ℂ) (v ij.2) (fun i => w (i, ij.2)) ij.1
def IsAdmissible (Z : ProjCycle ℂ n) (u : Fin n → ℂ) : Prop :=
  ∀ W ∈ Z.support, linForm u ∉ W
def mahlerDefect (h : HermNorm n) (e : ℕ) (Z : ProjCycle ℂ n)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ) : ℝ :=
  mahler h e (specFirst f u) - cycleIntegral h Z e (fsLog h u)
structure IsChowCycleData (Z : ProjCycle ℂ n) (e δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    Prop where

  prime : ∀ W ∈ Z.support, IsProjPrime W

  chow : IsChowFormCycle Z (e + 1) f

  homog : IsMultiHomog δ f
def MahlerSectionDim (e : ℕ) : Prop :=
  ∀ (n δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (u : Fin n → ℂ), IsChowCycleData Z e δ f → IsAdmissible Z u →
      mahler h e (specFirst f u) =
        mahler h (e + 1) f + δ * (harmonic (n - 1) : ℝ) / 2 + cycleIntegral h Z e (fsLog h u)
def DefectConstDim (e : ℕ) : Prop :=
  ∀ (n δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (u u' : Fin n → ℂ), IsChowCycleData Z e δ f → IsAdmissible Z u → IsAdmissible Z u' →
      mahlerDefect h e Z f u = mahlerDefect h e Z f u'
def MahlerSectionOfConst.Statement : Prop :=
  ∀ e : ℕ, DefectConstDim e → MahlerSectionDim e
def DefectConstZero.Statement : Prop :=
  DefectConstDim 0
def DefectConstStep.Statement : Prop :=
  ∀ e : ℕ, MahlerSectionDim e → DefectConstDim (e + 1)
def DefectAverage.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsChowCycleData Z e δ f →
      IntegrableOn (fun v => mahlerDefect h e Z f (nrmv h v)) (ballH h) ∧
        ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) = mahler h (e + 1) f + δ * (harmonic (n - 1) : ℝ) / 2
def AdmissibleAE.Statement : Prop :=
  ∀ (n : ℕ) (Z : ProjCycle ℂ n), (∀ W ∈ Z.support, IsRelevant W) → ∀ᵐ u : Fin n → ℂ, IsAdmissible Z u
def AdmissibleAENrm.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n), (∀ W ∈ Z.support, IsRelevant W) →
    ∀ᵐ v ∂(volume.restrict (ballH h)), IsAdmissible Z (nrmv h v)
def BallVolume.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n), 0 < volume (ballH h) ∧ volume (ballH h) < ⊤
def MahlerAverageSplit.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), f ≠ 0 → IsMultiHomog δ f →
    IntegrableOn (fun v => mahler h e (specFirst f (nrmv h v))) (ballH h) ∧
      mahler h (e + 1) f = ⨍ v in ballH h, mahler h e (specFirst f (nrmv h v))
def MahlerIntegrand.Statement : Prop :=
  ∀ (n k δ : ℕ) (h : HermNorm n) (f : MvPolynomial (Fin k × Fin n) ℂ), f ≠ 0 → IsMultiHomog δ f →
    IntegrableOn (fun u => Real.log ‖eval (nrmGroups h k u) f‖) (ballProd h k)
def SphereMeanFubini.Statement : Prop :=
  ∀ (n k : ℕ) (h : HermNorm n) (G : (Fin (k + 1) × Fin n → ℂ) → ℝ),
    IntegrableOn (fun u => G (nrmGroups h (k + 1) u)) (ballProd h (k + 1)) →
      IntegrableOn (fun v => sphereMean h k (fun w => G (consGroup (nrmv h v) w))) (ballH h) ∧
        sphereMean h (k + 1) G = ⨍ v in ballH h, sphereMean h k (fun w => G (consGroup (nrmv h v) w))
def EvalSpecFirst.Statement : Prop :=
  ∀ (n k : ℕ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ),
    eval w (specFirst f v) = eval (consGroup v w) f
def CycleAverage.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsChowCycleData Z e δ f →
      IntegrableOn (fun v => cycleIntegral h Z e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, cycleIntegral h Z e (fsLog h (nrmv h v)) = -(δ * (harmonic (n - 1) : ℝ)) / 2
def ConeAverage.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g →
      IntegrableOn (fun v => coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, coneIntegral h W e (fsLog h (nrmv h v)) = -(δ * (harmonic (n - 1) : ℝ)) / 2
def ConeFubini.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (μ : Measure (EuclideanSpace ℂ (Fin n))) [IsFiniteMeasure μ]
    (F : (Fin n → ℂ) → EuclideanSpace ℂ (Fin n) → ℝ) (c M : ℝ),
    Measurable (Function.uncurry F) →
    (∀ᵐ y ∂μ, IntegrableOn (fun v => F v y) (ballH h) ∧ ∫ v in ballH h, |F v y| ≤ M ∧
      ⨍ v in ballH h, F v y = c) →
      IntegrableOn (fun v => ∫ y, F v y ∂μ) (ballH h) ∧
        ⨍ v in ballH h, ∫ y, F v y ∂μ = c * (μ Set.univ).toReal
def FsLogAverage.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)), y ≠ 0 →
    IntegrableOn (fun v => fsLog h (nrmv h v) (h.pointOf y)) (ballH h) ∧
      ∫ v in ballH h, |fsLog h (nrmv h v) (h.pointOf y)| =
        (harmonic (n - 1) : ℝ) / 2 * (volume (ballH h)).toReal ∧
      ⨍ v in ballH h, fsLog h (nrmv h v) (h.pointOf y) = -(harmonic (n - 1) : ℝ) / 2
def FsLogPointOf.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (v : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)),
    fsLog h (nrmv h v) (h.pointOf y) =
      fsLog (HermNorm.std n) (nrmv (HermNorm.std n) (h.mat *ᵥ v)) (fun i => y i)
def BallAverageLinear.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (φ : (Fin n → ℂ) → ℝ),
    (IntegrableOn (fun v => φ (h.mat *ᵥ v)) (ballH h) ↔ IntegrableOn φ (ballH (HermNorm.std n))) ∧
      ⨍ v in ballH h, φ (h.mat *ᵥ v) = ⨍ w in ballH (HermNorm.std n), φ w
def SphereMeanLinearBall.Statement : Prop :=
  ∀ (n : ℕ) (y : Fin n → ℂ), y ≠ 0 →
    IntegrableOn (fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y) (ballH (HermNorm.std n)) ∧
      (∀ w, fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y ≤ 0) ∧
      ⨍ w in ballH (HermNorm.std n), fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y =
        -(harmonic (n - 1) : ℝ) / 2
def FsLogMeasurable.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n),
    Measurable (fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => fsLog h (nrmv h p.1) (h.pointOf p.2))
def ChowDegreePos.Statement : Prop :=
  ∀ (n k δ : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin k × Fin n) ℂ),
    0 < k → IsProjPrime W → IsChowForm W k g → IsMultiHomog δ g → 1 ≤ δ
def DefectSymm.Statement : Prop :=
  ∀ e : ℕ, MahlerSectionDim e →
    ∀ (n δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℂ)
      (u u' : Fin n → ℂ), IsChowCycleData Z (e + 1) δ f → IsAdmissible Z u → IsAdmissible Z u' →
      IsAdmissible (cycleSection Z u) u' → IsAdmissible (cycleSection Z u') u →
        mahlerDefect h (e + 1) Z f u = mahlerDefect h (e + 1) Z f u'
def CycleSectionData.Statement : Prop :=
  ∀ (n e δ : ℕ) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsChowCycleData Z (e + 1) δ f → IsAdmissible Z u → IsChowCycleData (cycleSection Z u) e δ (specFirst f u)
def DivCyclePrime.Statement : Prop :=
  ∀ (n : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    IsProjPrime W → ∀ W' ∈ (divCycle W u).support, IsProjPrime W'
def SpecFirstHomog.Statement : Prop :=
  ∀ (n k δ : ℕ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsMultiHomog δ f → IsMultiHomog δ (specFirst f u)
def SupportCycleSection.Statement : Prop :=
  ∀ (n : ℕ) (Z : ProjCycle ℂ n) (u : Fin n → ℂ),
    (∀ W ∈ Z.support, (divCycle W u).support ⊆ (cycleSection Z u).support) ∧
      ∀ W' ∈ (cycleSection Z u).support, ∃ W ∈ Z.support, W' ∈ (divCycle W u).support
def CycleIntegralSection.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (u : Fin n → ℂ) (e : ℕ) (g : (Fin n → ℂ) → ℝ),
    cycleIntegral h (cycleSection Z u) e g = ∑ W ∈ Z.support, (Z W : ℝ) * cycleIntegral h (divCycle W u) e g
def ChowFormAssoc.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (g g' : MvPolynomial (Fin k × Fin n) F), IsChowForm I k g → IsChowForm I k g' →
      ∃ c : F, c ≠ 0 ∧ g' = C c * g
def ChowFormCycleAdd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Z₁ Z₂ : ProjCycle F n) (f₁ f₂ : MvPolynomial (Fin k × Fin n) F),
    IsChowFormCycle Z₁ k f₁ → IsChowFormCycle Z₂ k f₂ → IsChowFormCycle (Z₁ + Z₂) k (f₁ * f₂)
def ChowFormCycleSmul.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k m : ℕ) (Z : ProjCycle F n) (f : MvPolynomial (Fin k × Fin n) F),
    IsChowFormCycle Z k f → IsChowFormCycle (m • Z) k (f ^ m)
def CycleSectionChow.Statement : Prop :=
  ∀ (n e : ℕ) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    (∀ W ∈ Z.support, IsProjPrime W) → IsChowFormCycle Z (e + 1) f → IsAdmissible Z u →
      IsChowFormCycle (cycleSection Z u) e (specFirst f u)
def SpecFirstRename.Statement : Prop :=
  ∀ (n k : ℕ) (f : MvPolynomial (Fin (k + 1 + 1) × Fin n) ℂ) (u u' : Fin n → ℂ),
    specFirst (specFirst (rename (Prod.map (Equiv.swap 0 1) id) f) u) u' = specFirst (specFirst f u') u
def ChowCycleSwap.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Z : ProjCycle F n) (f : MvPolynomial (Fin k × Fin n) F),
    IsChowFormCycle Z k f → ∀ τ : Equiv.Perm (Fin k), ∃ c : F, c ^ 2 = 1 ∧ rename (Prod.map τ id) f = C c * f
def SpecFirstSwapMahler.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℂ)
    (u u' : Fin n → ℂ), IsChowFormCycle Z (e + 1 + 1) f →
      mahler h e (specFirst (specFirst f u) u') = mahler h e (specFirst (specFirst f u') u)
def ProperSymm.Statement : Prop :=
  ∀ (n : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ),
    IsProjPrime W → linForm u ∉ W → linForm u' ∉ W → IsAdmissible (divCycle W u) u' →
      IsAdmissible (divCycle W u') u
def ProperSymmCycle.Statement : Prop :=
  ∀ (n : ℕ) (Z : ProjCycle ℂ n) (u u' : Fin n → ℂ),
    (∀ W ∈ Z.support, IsProjPrime W) → IsAdmissible Z u → IsAdmissible Z u' →
      IsAdmissible (cycleSection Z u) u' → IsAdmissible (cycleSection Z u') u
def PointLine.Statement : Prop :=
  ∀ (n : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin 1 × Fin n) ℂ),
    IsProjPrime W → IsChowForm W 1 g →
      ∃ y : Fin n → ℂ, y ≠ 0 ∧ (∀ x : Fin n → ℂ, (∀ q ∈ W, eval x q = 0) ↔ ∃ t : ℂ, x = t • y) ∧
        ∀ q : MvPolynomial (Fin n) ℂ, q ∈ W ↔ ∀ t : ℂ, eval (t • y) q = 0
def PointChowForm.Statement : Prop :=
  ∀ (n : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin 1 × Fin n) ℂ) (y : Fin n → ℂ),
    IsChowForm W 1 g → y ≠ 0 → (∀ x : Fin n → ℂ, (∀ q ∈ W, eval x q = 0) ↔ ∃ t : ℂ, x = t • y) →
      ∃ c : ℂ, c ≠ 0 ∧ g = C c * ∑ j, C (y j) * X ((0 : Fin 1), j)
def ConeIntegralLine.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (y : Fin n → ℂ),
    (∀ x : Fin n → ℂ, (∀ q ∈ W, eval x q = 0) ↔ ∃ t : ℂ, x = t • y) →
    ∀ φ : (Fin n → ℂ) → ℝ, (∀ t : ℂ, t ≠ 0 → φ (t • y) = φ y) →
      coneIntegral h W 0 φ = φ y * coneIntegral h W 0 (fun _ => 1)
def FsLogSmul.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (u y : Fin n → ℂ) (t : ℂ), t ≠ 0 → fsLog h u (t • y) = fsLog h u y
def MahlerZeroSpec.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (f : MvPolynomial (Fin 1 × Fin n) ℂ) (u : Fin n → ℂ),
    mahler h 0 (specFirst f u) = Real.log ‖eval (fun ij => u ij.2) f‖
def DefectPoint.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin 1 × Fin n) ℂ),
    IsProjPrime W → IsChowForm W 1 g → ∃ K : ℝ, ∀ u : Fin n → ℂ, linForm u ∉ W →
      eval (fun ij => u ij.2) g ≠ 0 ∧
        Real.log ‖eval (fun ij => u ij.2) g‖ - coneIntegral h W 0 (fsLog h u) = K
namespace MahlerInhabit
def coord (a : Fin 2) : Fin 2 → ℂ := fun j => if j = a then 1 else 0
end MahlerInhabit
end
end GroundTheory.Heights₂.Heights


