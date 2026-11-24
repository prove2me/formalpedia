-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:12.360893+00:00
-- url     : https://prove2.me/theorems/cac3fb2c-41ed-4178-b2ee-c3fa83d3f89a
-- title:
--   Is Smooth Herm Fubini Study O1
-- statement:
--   Definitions and structural lemmas for Is Smooth Herm Fubini Study O1, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermFubiniStudyO1.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
section Objects
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (ι) in

abbrev Family := Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ
def coneSet : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
def AllSmooth {n : ℕ} (L : Fin n → HermLine ι) : Prop := ∀ j, IsSmoothHerm (L j)
def degs {n : ℕ} (L : Fin n → HermLine ι) : Fin n → K → ℤ := fun j => (L j).a
def pots {n : ℕ} (L : Fin n → HermLine ι) : Fin n → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => Real.log ((L j).h z)
def IsSec (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) : Prop :=
  ∃ a : K → ℕ, IsMultiHomog s a ∧ (∀ k, (a k : ℤ) = A.a k) ∧ s ∉ P
open Classical in

def horizPart (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) : ℝ :=
  ∑ W ∈ (divSupp_finite P s).toFinset.filter (fun W => IsHorizontal W),
    (multAt (P ⊔ Ideal.span {s}) W : ℝ) * I W n L
open Classical in

def vertPart (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) : ℝ :=
  ∑ V ∈ (divSupp_finite P s).toFinset.filter (fun V => ¬ IsHorizontal V),
    (multAt (P ⊔ Ideal.span {s}) V : ℝ) * (geoNum n V (degs L) : ℝ) * Real.log (charOf V)
def intPart (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) : ℝ :=
  ptsIntegral P (pots L) (logNorm A s)
def rhsR (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι)
    (s : MRing ι) : ℝ :=
  horizPart I P L s + vertPart P L s - intPart P L A s
def logNormQ (A : HermLine ι) (f g : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z)
def rhsRQ (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι)
    (f g : MRing ι) : ℝ :=
  horizPart I P L f - horizPart I P L g + (vertPart P L f - vertPart P L g) -
    ptsIntegral P (pots L) (logNormQ A f g)
def IsFamilyOn (I : Family ι) (good : ℕ → Prop) : Prop :=
  (∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)),
      good n → IsArithVar P n → AllSmooth L → I P n (L ∘ σ) = I P n L) ∧
  (∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (j : Fin n) (A B : HermLine ι),
      good n → IsArithVar P n → AllSmooth L → IsSmoothHerm A → IsSmoothHerm B →
      I P n (Function.update L j (A.tensor B)) =
        I P n (Function.update L j A) + I P n (Function.update L j B)) ∧
  (∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin (n + 1) → HermLine ι) (s : MRing ι),
      good (n + 1) → IsArithVar P (n + 1) → AllSmooth L → IsSec P (L (Fin.last n)) s →
      I P (n + 1) L = rhsR I P (Fin.init L) (L (Fin.last n)) s)
def IsFamily (I : Family ι) : Prop := IsFamilyOn I fun _ => True
def expLine (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) : HermLine ι where
  a := 0
  h z := Real.exp (u z / 2)
  pos _ _ := Real.exp_pos _
  smul c z hc := by simp [hu c z hc]
def IsClosedPt (x : Ideal (MRing ι)) : Prop :=
  IsMultiProjPrime x ∧ ringKrullDim (MRing ι ⧸ x) = ((Fintype.card K : ℕ) : WithBot ℕ∞)
end Objects
def ThmIExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ∃ I : Family ι, IsFamily I
def ThmIUnique.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I J : Family ι),
    IsFamily I → IsFamily J → ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι),
      IsArithVar P n → AllSmooth L → I P n L = J P n L
def R1.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 →
    (∀ (I J : Family ι) (A : HermLine ι) (s s' : MRing ι), IsSmoothHerm A → IsSec P A s → IsSec P A s' →
        rhsR I P ![] A s = rhsR J P ![] A s') ∧
    (∀ (I : Family ι) (A B : HermLine ι) (s t : MRing ι), IsSmoothHerm A → IsSmoothHerm B →
        IsSec P A s → IsSec P B t →
        rhsR I P ![] (A.tensor B) (s * t) = rhsR I P ![] A s + rhsR I P ![] B t)
def Swap.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι) (n : ℕ),
    IsFamilyOn I (· < n + 2) →
    ∀ (P : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A B : HermLine ι) (s s' : MRing ι),
      IsArithVar P (n + 2) → AllSmooth L → IsSmoothHerm A → IsSmoothHerm B →
      IsSec P A s → IsSec P B s' → Disjoint (divSupp P s) (divSupp P s') →
      rhsR I P (Fin.snoc L B) A s = rhsR I P (Fin.snoc L A) B s'
def Choice.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ),
    IsArithVar P d → ∀ (m : ℕ) (W x : Fin m → Ideal (MRing ι)),
      (∀ i, IsMultiProjPrime (W i) ∧ P ≤ W i) → (∀ i, W i ≤ x i ∧ IsClosedPt (x i)) →
      ∀ (a : K → ℤ) (b : K → ℕ), (∀ j, 1 ≤ b j) → ∃ k₀ : ℕ, ∀ k ≥ k₀,
        (∀ j, 0 ≤ a j + k * b j) ∧
        (∃ s : MRing ι, IsMultiHomog s (fun j => (a j + k * b j).toNat) ∧ ∀ i, s ∉ x i) ∧
        (∃ s : MRing ι, IsMultiHomog s (fun j => k * b j) ∧ ∀ i, s ∉ x i)
def ArithmeticIntersectionSecond.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι), IsFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (u : ((Σ k, ι k) → ℂ) → ℝ)
      (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z),
      IsArithVar P (n + 1) → AllSmooth L → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u coneSet →
      I P (n + 1) (Fin.snoc L (expLine u hu)) = (1 / 2) * ptsIntegral P (pots L) u
def InductiveIntersectionFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι), IsFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (f g : MRing ι)
      (α β : K → ℕ), IsArithVar P (n + 1) → AllSmooth L → IsSmoothHerm A →
      IsMultiHomog f α → IsMultiHomog g β → (∀ k, (α k : ℤ) - β k = A.a k) → f ∉ P → g ∉ P →
      (∀ W, IsHorizontal W → divCycle P f W = divCycle P g W) →
      (∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ =
        ‖eval z (map (Int.castRingHom ℂ) g)‖ * A.h z) →
      I P (n + 1) (Fin.snoc L A) = vertPart P L f - vertPart P L g
def ArithmeticIntersectionFifth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι), IsFamily I →
    ∀ (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι), IsArithVar P 1 → IsSmoothHerm A →
      IsSec P A s → I P 1 ![A] = vertPart P ![] s - intPart P ![] A s
def Conservation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (p : ℕ), IsArithVar P (n + 1) → AllSmooth L → p.Prime →
    ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
        (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (degs L) : ℝ) =
      ptsIntegral P (pots L) (fun _ => 1)
def RationalSections.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι), IsFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (f g : MRing ι)
      (α β : K → ℕ), IsArithVar P (n + 1) → AllSmooth L → IsSmoothHerm A →
      IsMultiHomog f α → IsMultiHomog g β → (∀ k, (α k : ℤ) - β k = A.a k) → f ∉ P → g ∉ P →
      I P (n + 1) (Fin.snoc L A) = rhsRQ I P L A f g
section Inhabitants
abbrev GlobalTheory (n : ℕ) : Unit → Type := fun _ => Fin n
abbrev Xb (n : ℕ) (i : Fin n) : MRing (GlobalTheory n) := X ⟨(), i⟩
def fsO1 (n : ℕ) : HermLine (GlobalTheory n) := HermLine.sqMetric fun _ => 1
def triv (n : ℕ) : HermLine (GlobalTheory n) := HermLine.sqMetric fun _ => 0
example : Family (GlobalTheory 2) := fun _ _ _ => 0
def halfLine : HermLine (GlobalTheory 1) := expLine (fun _ => 2 * Real.log 2) fun _ _ _ => rfl
end Inhabitants
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


