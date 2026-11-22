-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementG
-- name    : Formalism_HermitianCurvature_StatementG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:50.216063+00:00
-- url     : https://prove2.me/theorems/523fb9f9-3f3f-4679-afb4-221f11af8326
-- title:
--   Statement G
-- statement:
--   Definitions and structural lemmas for Statement G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementG.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.G
open Matrix MeasureTheory Filter Topology
noncomputable section
def psi (β w : ℂ) : ℂ := Complex.exp (Complex.I * (((β * w).re : ℝ) : ℂ))
def mu (β : ℂ) : Measure ℂ := Real.toNNReal (‖β‖ / (2 * Real.pi)) • (volume : Measure ℂ)
def muPi (β : ℂ) (ι : Type) [Fintype ι] : Measure (ι → ℂ) := Measure.pi (fun _ : ι => mu β)
abbrev UT (d : ℕ) : Type := {p : Fin d × Fin d // p.1 < p.2}
def strictUpper {d : ℕ} (v : UT d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => if h : i < j then v ⟨(i, j), h⟩ else 0
def upper {d : ℕ} (v : UT d → ℂ) : Matrix (Fin d) (Fin d) ℂ := 1 + strictUpper v
def IsUpperUni {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, j < i → u i j = 0
def IsLowerUni {d : ℕ} (l : Matrix (Fin d) (Fin d) ℂ) : Prop := IsUpperUni lᵀ
def IsStrictUpper {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : Prop := ∀ i j, j ≤ i → X i j = 0
def wMat (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => if j = i.rev then 1 else 0
def blk {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A (Matrix.of fun i (_ : Fin 1) => b i) (Matrix.of fun (_ : Fin 1) j => a j)
      (Matrix.of fun (_ _ : Fin 1) => e))
def ptLong (d : ℕ) (z : ℂ) : Matrix (Fin d) (Fin d) ℂ := z • wMat d
def ptBlock (n : ℕ) (t c : ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := blk (t • wMat n) 0 0 c
def lowRow {n : ℕ} (a : Fin n → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := blk 1 0 a 1
def superSum {n : ℕ} (u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℂ := ∑ i : Fin n, u i.castSucc i.succ
def subSum {n : ℕ} (l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℂ := ∑ i : Fin n, l i.succ i.castSucc
abbrev Mat (s : ℕ) : Type := Fin s → Fin s → ℂ
def detM {s : ℕ} (Z : Mat s) : ℂ := Matrix.det (Matrix.of Z)
section Orbital
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
def OmLong (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V) (z : ℂ) : V :=
  ∫ v : UT (n + 1) → ℂ, psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v) ∂(muPi β (UT (n + 1)))
abbrev BlockCoord (n : ℕ) : Type := (Fin n → ℂ) × (UT n → ℂ) × (Fin n → ℂ)
def muBlock (β : ℂ) (n : ℕ) : Measure (BlockCoord n) :=
  (muPi β (Fin n)).prod ((muPi β (UT n)).prod (muPi β (Fin n)))
def blockIntegrand (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V) (t c : ℂ) (p : BlockCoord n) : V :=
  (psi β (subSum (lowRow p.1)) * psi β (superSum (blk (upper p.2.1) p.2.2 0 1))) •
    Φ (lowRow p.1 * ptBlock n t c * blk (upper p.2.1) p.2.2 0 1)
def OmBlock (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V) (t c : ℂ) : V :=
  ∫ p : BlockCoord n, blockIntegrand β n Φ t c p ∂(muBlock β n)
def DerivBound {s : ℕ} (k : ℕ) (Kd : Set ℂ) (bd : Mat s → ℝ) (Φ : Mat s → V) : Prop :=
  ∀ Z : Mat s, detM Z ∈ Kd → ContDiffAt ℝ k Φ Z ∧ ∀ j ≤ k, ‖iteratedFDeriv ℝ j Φ Z‖ ≤ bd Z
end Orbital
def rootSet (s : ℕ) (a : ℂ) : Finset ℂ := (Polynomial.nthRoots s a).toFinset
def detSet (n : ℕ) (Kc : Set ℂ) : Set ℂ := (fun D => (wMat n).det * D) '' Kc
section Main
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
def mainTerm (β : ℂ) (m : ℕ) (ph : ℂ → ℂ) (Φ : Mat (m + 1 + 1) → V) (t D : ℂ) : V :=
  ((m : ℂ) + 2)⁻¹ • ∑ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D),
    (((‖z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * ph z * psi β (((m : ℂ) + 2) * z / t)) • OmLong β (m + 1) Φ z
def remainder (β : ℂ) (m : ℕ) (ph : ℂ → ℂ) (Φ : Mat (m + 1 + 1) → V) (t c : ℂ) : V :=
  ((‖t‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) • OmBlock β (m + 1) Φ t c - mainTerm β m ph Φ t (c * t ^ (m + 1))
end Main
def Germ : Prop :=
  ∃ C : ℕ, ∀ (m : ℕ) (β : ℂ), β ≠ 0 → ∃ ph : ℂ → ℂ, (∀ z, ‖ph z‖ = 1) ∧
    ∀ A : ℝ, (C : ℝ) * ((m : ℝ) + 2) ^ 3 ≤ A → ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∀ K ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V),
      DerivBound (C * (m + 2) ^ 2) (detSet (m + 1) Kc) (fun Z => K * ‖Z‖ ^ (-A)) Φ →
      ∀ t c : ℂ, t ≠ 0 → ‖t‖ < δ → c * t ^ (m + 1) ∈ Kc → ‖remainder β m ph Φ t c‖ ≤ ε
def GermRate : Prop :=
  ∃ C₁ C₂ : ℕ, ∀ (m : ℕ) (β : ℂ), β ≠ 0 → ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∃ Cst : ℝ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
      (Φ : Mat (m + 1 + 1) → V) (A K : ℝ) (k : ℕ),
      (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 ≤ A → C₂ * (m + 2) ^ 2 ≤ k →
      DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      ∀ t c : ℂ, t ≠ 0 → c * t ^ (m + 1) ∈ Kc → ‖remainder β m (fun _ => 1) Φ t c‖ ≤ Cst * K * ‖t‖
def GermOfRate : Prop := GermRate → Germ
def PsiChar : Prop :=
  ∀ β x y : ℂ, psi β (x + y) = psi β x * psi β y ∧ ‖psi β x‖ = 1 ∧ psi β 0 = 1
def PsiNormalisations : Prop :=
  ∀ w : ℂ, psi (4 * Real.pi) w = Complex.exp (2 * Real.pi * Complex.I * (w + (starRingEnd ℂ) w)) ∧
    psi (-2 * Complex.I) w = Complex.exp (w - (starRingEnd ℂ) w)
def SelfDual : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ (f : SchwartzMap ℂ ℂ) (w : ℂ),
    ∫ ξ : ℂ, (∫ x : ℂ, f x * psi β (ξ * x) ∂(mu β)) * psi β (w * ξ) ∂(mu β) = f (-w)
def SelfDualUnique : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ κ : NNReal,
    (∀ (f : SchwartzMap ℂ ℂ) (w : ℂ),
      ∫ ξ : ℂ, (∫ x : ℂ, f x * psi β (ξ * x) ∂(κ • (volume : Measure ℂ))) * psi β (w * ξ)
        ∂(κ • (volume : Measure ℂ)) = f (-w)) →
    κ = Real.toNNReal (‖β‖ / (2 * Real.pi))
def AffineChange : Prop :=
  ∀ β α γ : ℂ, α ≠ 0 →
    Measure.map (fun ρ : ℂ => α * ρ + γ) (mu β) = Real.toNNReal ((‖α‖ ^ 2)⁻¹) • mu β
def ScalePi : Prop :=
  ∀ (β z : ℂ) (ι : Type) [Fintype ι], z ≠ 0 →
    Measure.map (fun v : ι → ℂ => z • v) (muPi β ι) =
      Real.toNNReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) • muPi β ι
def CharAdditive : Prop :=
  ∀ (n : ℕ) (p q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    (IsUpperUni p → IsUpperUni q → superSum (p * q) = superSum p + superSum q) ∧
    (IsLowerUni p → IsLowerUni q → subSum (p * q) = subSum p + subSum q)
def StabLong : Prop :=
  ∀ (n : ℕ) (z : ℂ), z ≠ 0 → ∀ l u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsLowerUni l → IsUpperUni u →
    (l * ptLong (n + 1) z * u = ptLong (n + 1) z ↔ l = wMat (n + 1) * u⁻¹ * wMat (n + 1)) ∧
    (l * ptLong (n + 1) z * u = ptLong (n + 1) z → subSum l + superSum u = 0)
def SectionLong : Prop :=
  ∀ (n : ℕ) (z : ℂ), z ≠ 0 → ∀ l u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsLowerUni l → IsUpperUni u →
    ∃! v : UT (n + 1) → ℂ, ∃ k k' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsLowerUni k ∧ IsUpperUni k' ∧
      k * ptLong (n + 1) z * k' = ptLong (n + 1) z ∧ l * k = 1 ∧ k' * u = upper v
def StabBlock : Prop :=
  ∀ (n : ℕ) (t c : ℂ), t ≠ 0 → ∀ l u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsLowerUni l → IsUpperUni u →
    (l * ptBlock n t c * u = ptBlock n t c ↔
      ∃ k : Matrix (Fin n) (Fin n) ℂ, IsUpperUni k ∧ u = blk k 0 0 1 ∧
        l = blk (wMat n * k⁻¹ * wMat n) 0 0 1) ∧
    (l * ptBlock n t c * u = ptBlock n t c → subSum l + superSum u = 0)
def SectionBlock : Prop :=
  ∀ (n : ℕ) (t c : ℂ), t ≠ 0 → ∀ l u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsLowerUni l → IsUpperUni u →
    ∃! p : BlockCoord n, ∃ k k' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsLowerUni k ∧ IsUpperUni k' ∧
      k * ptBlock n t c * k' = ptBlock n t c ∧ l * k = lowRow p.1 ∧ k' * u = blk (upper p.2.1) p.2.2 0 1
def coordU {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) : UT d → ℂ := fun p => M p.1.1 p.1.2
def quotMap (n : ℕ) (q : (UT n → ℂ) × BlockCoord n) : (UT (n + 1) → ℂ) × (UT (n + 1) → ℂ) :=
  (coordU (lowRow q.2.1 * blk (wMat n * (upper q.1)⁻¹ * wMat n) 0 0 1)ᵀ,
   coordU (blk (upper q.1) 0 0 1 * blk (upper q.2.2.1) q.2.2.2 0 1))
def QuotientMeasure : Prop :=
  ∀ (n : ℕ) (β : ℂ), MeasurePreserving (quotMap n) ((muPi β (UT n)).prod (muBlock β n))
    ((muPi β (UT (n + 1))).prod (muPi β (UT (n + 1))))
def DetOrbit : Prop :=
  (∀ (n : ℕ) (t c : ℂ) (p : BlockCoord n),
    (lowRow p.1 * ptBlock n t c * blk (upper p.2.1) p.2.2 0 1).det = (wMat n).det * (c * t ^ n)) ∧
  (∀ (d : ℕ) (z : ℂ) (v : UT d → ℂ), (ptLong d z * upper v).det = (wMat d).det * z ^ d)
def DetMatch : Prop :=
  ∀ n : ℕ, (wMat (n + 1)).det = (-1) ^ n * (wMat n).det ∧ (wMat n).det ≠ 0
def Xof {n : ℕ} (t : ℂ) (v : UT n → ℂ) : Matrix (Fin n) (Fin n) ℂ := t • strictUpper v
def rhoOf {n : ℕ} (t : ℂ) (a : Fin n → ℂ) (v : UT n → ℂ) : Fin n → ℂ := t • (a ᵥ* (wMat n * upper v))
def Mcoord {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  blk (wMat n * (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X)) (wMat n *ᵥ B) ρ σ
def xOf {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B : Fin n → ℂ) : Fin n → ℂ :=
  fun k => blk X B 0 0 k.castSucc k.succ
def EntriesM : Prop :=
  ∀ (n : ℕ) (t c : ℂ) (p : BlockCoord n),
    lowRow p.1 * ptBlock n t c * blk (upper p.2.1) p.2.2 0 1 =
      Mcoord t (Xof t p.2.1) (t • p.2.2) (rhoOf t p.1 p.2.1) (c + p.1 ⬝ᵥ (wMat n *ᵥ (t • p.2.2)))
def ShapeM : Prop :=
  ∀ (m : ℕ) (t σ : ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B ρ : Fin (m + 1) → ℂ), IsStrictUpper X →
    (∀ i j : Fin (m + 2), (i : ℕ) + j < m → Mcoord t X B ρ σ i j = 0) ∧
    (∀ i j : Fin (m + 2), (i : ℕ) + j = m → Mcoord t X B ρ σ i j = t) ∧
    (∀ k : Fin (m + 1), Mcoord t X B ρ σ k.rev.castSucc k.succ = xOf X B k) ∧
    Mcoord t X B ρ σ (Fin.last (m + 1)) 0 = ρ 0 ∧
    Mcoord t X B ρ σ (Fin.last (m + 1)) (Fin.last (m + 1)) = σ
def PhaseFormula : Prop :=
  ∀ (m : ℕ) (t : ℂ), t ≠ 0 → ∀ p : BlockCoord (m + 1),
    subSum (lowRow p.1) + superSum (blk (upper p.2.1) p.2.2 0 1) =
      (rhoOf t p.1 p.2.1 0 + ∑ k, xOf (Xof t p.2.1) (t • p.2.2) k) / t
def coordMap (n : ℕ) (t : ℂ) (p : BlockCoord n) : BlockCoord n := (rhoOf t p.1 p.2.1, t • p.2.1, t • p.2.2)
def Jacobian : Prop :=
  ∀ (n : ℕ) (β t : ℂ), t ≠ 0 →
    Measure.map (coordMap n t) (muBlock β n) = Real.toNNReal ((‖t‖ ^ (n * (n + 3)))⁻¹) • muBlock β n
def CornerRelation : Prop :=
  ∀ (n : ℕ) (t c : ℂ) (a b : Fin n → ℂ) (v : UT n → ℂ),
    t ^ n * (c + a ⬝ᵥ (wMat n *ᵥ (t • b))) =
      c * t ^ n + ∑ j ∈ Finset.range n, (rhoOf t a v ⬝ᵥ ((-(Xof t v)) ^ j *ᵥ (t • b))) * t ^ (n - 1 - j)
def Cof {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ) (t : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), ((-X) ^ j *ᵥ B) 0 * t ^ (m - j)
def R0 {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ) (ρ' : Fin m → ℂ) (t : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), (∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ) * t ^ (m - j)
def CornerSplit : Prop :=
  ∀ (m : ℕ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ) (ρ₁ : ℂ) (ρ' : Fin m → ℂ) (t : ℂ),
    ∑ j ∈ Finset.range (m + 1),
        ((Fin.cons ρ₁ ρ' : Fin (m + 1) → ℂ) ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (m + 1 - 1 - j) =
      Cof X B t * ρ₁ + R0 X B ρ' t
def CofLead : Prop :=
  ∀ (m : ℕ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ) (ρ' : Fin m → ℂ), IsStrictUpper X →
    Cof X B 0 = (-1) ^ m * ∏ k, xOf X B k ∧ R0 X B ρ' 0 = 0
def rho1 {m : ℕ} (D σ : ℂ) (ρ' : Fin m → ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ)
    (t : ℂ) : ℂ :=
  (t ^ (m + 1) * σ - D - R0 X B ρ' t) / Cof X B t
def Rho1Limit : Prop :=
  ∀ (m : ℕ) (D σ : ℂ) (ρ' : Fin m → ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ),
    IsStrictUpper X → rho1 D σ ρ' X B 0 = (-1) ^ (m + 3) * D / ∏ k, xOf X B k
abbrev RedCoord (m : ℕ) : Type := ℂ × (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ)
def muRed (β : ℂ) (m : ℕ) : Measure (RedCoord m) :=
  (mu β).prod ((muPi β (Fin m)).prod ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1)))))
def OmReduced : Prop :=
  ∀ (m : ℕ) (β t c : ℂ), t ≠ 0 →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V),
      Integrable (blockIntegrand β (m + 1) Φ t c) (muBlock β (m + 1)) →
      ((‖t‖ ^ ((m + 1) * (m + 2)) : ℝ) : ℂ) • OmBlock β (m + 1) Φ t c =
        ∫ q : RedCoord m,
          (psi β ((rho1 (c * t ^ (m + 1)) q.1 q.2.1 (strictUpper q.2.2.1) q.2.2.2 t +
                ∑ k, xOf (strictUpper q.2.2.1) q.2.2.2 k) / t) *
              (((‖Cof (strictUpper q.2.2.1) q.2.2.2 t‖ ^ 2)⁻¹ : ℝ) : ℂ)) •
            Φ (Mcoord t (strictUpper q.2.2.1) q.2.2.2
              (Fin.cons (rho1 (c * t ^ (m + 1)) q.1 q.2.1 (strictUpper q.2.2.1) q.2.2.2 t) q.2.1) q.1)
          ∂(muRed β m)
def g0 {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) : ℂ := ∑ k, x k + D' / ∏ k, x k
def dg0 {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (k : Fin n) : ℂ := 1 - D' / (∏ k, x k) / x k
def hess {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (i j : Fin n) : ℂ :=
  (if i = j then 2 else 1) * D' / ((∏ k, x k) * x i * x j)
def PhaseFunctionDeriv : Prop :=
  ∀ (n : ℕ) (D' : ℂ) (x : Fin n → ℂ), (∀ k, x k ≠ 0) →
    (∀ k, HasDerivAt (fun ξ => g0 D' (Function.update x k ξ)) (dg0 D' x k) (x k)) ∧
    (∀ i j, HasDerivAt (fun ξ => dg0 D' (Function.update x j ξ) i) (hess D' x i j) (x j))
def PhaseFunctionCritical : Prop :=
  ∀ (m : ℕ) (D' : ℂ), D' ≠ 0 →
    (∀ x : Fin (m + 1) → ℂ, (∀ k, x k ≠ 0) →
      ((∀ k, dg0 D' x k = 0) ↔ ∃ z : ℂ, z ^ (m + 2) = D' ∧ x = fun _ => z)) ∧
    (∀ z : ℂ, z ^ (m + 2) = D' → g0 D' (fun _ : Fin (m + 1) => z) = ((m : ℂ) + 2) * z)
def GradSmall : Prop :=
  ∃ C : ℝ, ∀ (m : ℕ) (D' : ℂ), D' ≠ 0 → ∀ x : Fin (m + 1) → ℂ, (∀ k, x k ≠ 0) →
    ∀ η : ℝ, 0 < η → η ≤ 1 / (4 * ((m : ℝ) + 2)) → (∀ k, ‖dg0 D' x k‖ < η) →
    ∃ z : ℂ, z ^ (m + 2) = D' ∧ ∀ k, ‖x k - z‖ ≤ C * η * ‖z‖
def GradLower : Prop :=
  ∀ (m : ℕ) (Kc : Set ℂ), IsCompact Kc → (0 : ℂ) ∉ Kc → ∀ δ : ℝ, 0 < δ → ∃ cδ : ℝ, 0 < cδ ∧
    ∀ D' ∈ Kc, ∀ x : Fin (m + 1) → ℂ, (∀ k, x k ≠ 0) →
      (∀ z : ℂ, z ^ (m + 2) = D' → δ ≤ ‖x - fun _ => z‖) → ∃ k, cδ ≤ ‖dg0 D' x k‖
def HessCrit : Prop :=
  ∀ (m : ℕ) (z : ℂ), z ≠ 0 →
    (Matrix.of (hess (z ^ (m + 2)) (fun _ : Fin (m + 1) => z)) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      z⁻¹ • (1 + Matrix.of fun _ _ => (1 : ℂ))
def HessDet : Prop :=
  ∀ (m : ℕ) (z : ℂ),
    (z⁻¹ • (1 + Matrix.of fun _ _ => (1 : ℂ)) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det =
      ((m : ℂ) + 2) * z⁻¹ ^ (m + 1)
def GaussOneDamped : Prop :=
  ∀ (β a : ℂ) (δ : ℝ), 0 < δ →
    ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (a * w ^ 2 / 2) ∂(mu β) =
      ((‖β‖ / Real.sqrt (4 * δ ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2) : ℝ) : ℂ)
def GaussOne : Prop :=
  ∀ β a : ℂ, β ≠ 0 → a ≠ 0 →
    Tendsto (fun δ : ℝ => ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (a * w ^ 2 / 2) ∂(mu β))
      (𝓝[>] 0) (𝓝 (((‖a‖)⁻¹ : ℝ) : ℂ))
def gaussInt (β : ℂ) (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ) (t : ℂ) (δ : ℝ) : ℂ :=
  ∫ x : Fin d → ℂ, ((Real.exp (-δ * ∑ k, ‖x k‖ ^ 2) : ℝ) : ℂ) * psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) ∂(muPi β (Fin d))
def GaussMulti : Prop :=
  ∀ (d : ℕ) (β t : ℂ) (H : Matrix (Fin d) (Fin d) ℂ), β ≠ 0 → t ≠ 0 → H.IsSymm → H.det ≠ 0 →
    Tendsto (gaussInt β d H t) (𝓝[>] 0) (𝓝 ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ))
def GaussHess : Prop :=
  ∀ (m : ℕ) (β t z : ℂ), β ≠ 0 → t ≠ 0 → z ≠ 0 →
    Tendsto (gaussInt β (m + 1) (z⁻¹ • (1 + Matrix.of fun _ _ => (1 : ℂ))) t) (𝓝[>] 0)
      (𝓝 ((‖t‖ ^ (m + 1) * ‖z‖ ^ (m + 1) / ((m : ℝ) + 2) : ℝ) : ℂ))
def Takagi : Prop :=
  ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.IsSymm →
    ∃ W ∈ Matrix.unitaryGroup (Fin d) ℂ, ∃ σ : Fin d → ℝ, (∀ i, 0 ≤ σ i) ∧
      H = W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) * Wᵀ
def UnitaryInvariant : Prop :=
  ∀ (d : ℕ) (β : ℂ), ∀ W ∈ Matrix.unitaryGroup (Fin d) ℂ,
    MeasurePreserving (fun x : Fin d → ℂ => W *ᵥ x) (muPi β (Fin d)) (muPi β (Fin d))
def GaussMultiOfOne : Prop := Takagi → UnitaryInvariant → GaussOneDamped → GaussMulti
def GaussHessOfMulti : Prop := GaussMulti → HessDet → GaussHess
def CornerEntryCritical : Prop :=
  ∀ (m : ℕ) (z D σ : ℂ) (ρ' : Fin m → ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ),
    z ≠ 0 → z ^ (m + 2) = (-1) ^ (m + 3) * D → IsStrictUpper X → (∀ k, xOf X B k = z) →
    rho1 D σ ρ' X B 0 = z ∧
    HasDerivAt (fun t => rho1 D σ ρ' X B t)
      (superSum (wMat (m + 2) * Mcoord 0 X B (Fin.cons z ρ') σ) / z) 0
def LimitShape : Prop :=
  ∀ (m : ℕ) (z σ : ℂ) (ρ' : Fin m → ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ),
    IsStrictUpper X → (∀ k, xOf X B k = z) →
    IsStrictUpper (wMat (m + 2) * Mcoord 0 X B (Fin.cons z ρ') σ - z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ))
def LimitMatrix : Prop :=
  ∀ (n : ℕ) (z : ℂ), z ≠ 0 → ∀ y : UT (n + 1) → ℂ,
    wMat (n + 1) * (z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + strictUpper y) =
        ptLong (n + 1) z * upper (z⁻¹ • y) ∧
      superSum (upper (z⁻¹ • y)) = superSum (strictUpper y) / z
def LimitIntegral : Prop :=
  ∀ (n : ℕ) (β z : ℂ), z ≠ 0 →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (n + 1) → V),
      ∫ y : UT (n + 1) → ℂ, psi β (superSum (strictUpper y) / z) •
          Φ (wMat (n + 1) * (z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + strictUpper y))
          ∂(muPi β (UT (n + 1))) =
        ((‖z‖ ^ ((n + 1) * n) : ℝ) : ℂ) • OmLong β n Φ z
def OmConverges : Prop :=
  ∀ (m : ℕ) (β : ℂ) (A K : ℝ), (((m : ℝ) + 1) * ((m : ℝ) + 4)) < A →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V) (t c : ℂ),
      t ≠ 0 → c ≠ 0 →
      DerivBound 0 {(wMat (m + 1)).det * (c * t ^ (m + 1))} (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      Integrable (blockIntegrand β (m + 1) Φ t c) (muBlock β (m + 1)) ∧
      ∀ z : ℂ, z ^ (m + 2) = (-1) ^ (m + 3) * (c * t ^ (m + 1)) →
        Integrable (fun v : UT (m + 1 + 1) → ℂ =>
          psi β (superSum (upper v)) • Φ (ptLong (m + 1 + 1) z * upper v)) (muPi β (UT (m + 1 + 1)))
def RootSetSpec : Prop :=
  ∀ (s : ℕ) (a : ℂ), 0 < s → (∀ z, z ∈ rootSet s a ↔ z ^ s = a) ∧ (a ≠ 0 → (rootSet s a).card = s)
def CofLower : Prop :=
  ∀ (m : ℕ) (Kc : Set ℂ), IsCompact Kc → (0 : ℂ) ∉ Kc → ∃ t₀ c₀ : ℝ, 0 < t₀ ∧ 0 < c₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (2 * ((m : ℝ) + 2)) → ∀ D ∈ Kc, ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ t₀ →
    ∀ (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ) (ρ₁ : ℂ) (ρ' : Fin m → ℂ) (σ : ℂ),
      IsStrictUpper X → (∀ i j, ‖X i j‖ ≤ ‖t‖ ^ (-ε)) → (∀ i, ‖B i‖ ≤ ‖t‖ ^ (-ε)) → ‖ρ₁‖ ≤ ‖t‖ ^ (-ε) →
      (∀ k, ‖ρ' k‖ ≤ ‖t‖ ^ (-ε)) → ‖σ‖ ≤ ‖t‖ ^ (-ε) →
      t ^ (m + 1) * σ = D + Cof X B t * ρ₁ + R0 X B ρ' t →
      c₀ * ‖t‖ ^ ε ≤ ‖Cof X B t‖
def LeadingConstant : Prop :=
  ∀ (m : ℕ) (τ ζ : ℝ), 0 < τ → 0 < ζ →
    (τ ^ ((m + 1) * (m + 2)))⁻¹ * (τ ^ (m + 1) * ζ ^ (m + 1) / ((m : ℝ) + 2)) * (ζ ^ (2 * (m + 1)))⁻¹ *
        ζ ^ ((m + 2) * (m + 1)) =
      (τ ^ ((m + 1) ^ 2))⁻¹ * (((m : ℝ) + 2)⁻¹ * ζ ^ ((m + 1) ^ 2))
def DimCount : Prop :=
  ∀ n : ℕ, 2 * Fintype.card (UT n) = n * (n - 1) ∧
    n + Fintype.card (UT n) + n = Fintype.card (UT (n + 1)) + n
def quotMapLong (d : ℕ) (q : (UT d → ℂ) × (UT d → ℂ)) : (UT d → ℂ) × (UT d → ℂ) :=
  (coordU (wMat d * (upper q.1)⁻¹ * wMat d)ᵀ, coordU (upper q.1 * upper q.2))
def QuotientMeasureLong : Prop :=
  ∀ (d : ℕ) (β : ℂ), MeasurePreserving (quotMapLong d) ((muPi β (UT d)).prod (muPi β (UT d)))
    ((muPi β (UT d)).prod (muPi β (UT d)))
def StabInvariant : Prop :=
  ∀ (n : ℕ) (β : ℂ) (g l u k k' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    ((∃ z : ℂ, z ≠ 0 ∧ g = ptLong (n + 1) z) ∨ ∃ t c : ℂ, t ≠ 0 ∧ g = ptBlock n t c) →
    IsLowerUni l → IsUpperUni u → IsLowerUni k → IsUpperUni k' → k * g * k' = g →
    l * k * g * (k' * u) = l * g * u ∧
      psi β (subSum (l * k)) * psi β (superSum (k' * u)) = psi β (subSum l) * psi β (superSum u)
def CofLowerR : Prop :=
  ∀ (m : ℕ) (Kc : Set ℂ), IsCompact Kc → (0 : ℂ) ∉ Kc → ∀ R : ℝ, 0 < R → ∃ t₀ c₀ : ℝ, 0 < t₀ ∧ 0 < c₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (2 * ((m : ℝ) + 2)) → ∀ D ∈ Kc, ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ t₀ →
    ∀ (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ) (ρ₁ : ℂ) (ρ' : Fin m → ℂ) (σ : ℂ),
      IsStrictUpper X → (∀ i j, ‖X i j‖ ≤ R * ‖t‖ ^ (-ε)) → (∀ i, ‖B i‖ ≤ R * ‖t‖ ^ (-ε)) →
      ‖ρ₁‖ ≤ R * ‖t‖ ^ (-ε) → (∀ k, ‖ρ' k‖ ≤ R * ‖t‖ ^ (-ε)) → ‖σ‖ ≤ R * ‖t‖ ^ (-ε) →
      t ^ (m + 1) * σ = D + Cof X B t * ρ₁ + R0 X B ρ' t →
      c₀ * ‖t‖ ^ ε ≤ ‖Cof X B t‖
abbrev XY (m : ℕ) : Type := (Fin (m + 1) → ℂ) × (UT (m + 2) → ℂ)
def muXY (β : ℂ) (m : ℕ) : Measure (XY m) := (muPi β (Fin (m + 1))).prod (muPi β (UT (m + 2)))
def triXY {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  Matrix.diagonal (Fin.cons 0 x : Fin (m + 2) → ℂ) + strictUpper y
def redOf (m : ℕ) (p : XY m) : RedCoord m :=
  (triXY p.1 p.2 0 (Fin.last (m + 1)), fun k => triXY p.1 p.2 0 k.succ.castSucc,
    fun q => triXY p.1 p.2 q.1.1.succ q.1.2.castSucc, fun i => triXY p.1 p.2 i.succ (Fin.last (m + 1)))
def subShift (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => if (j : ℕ) + 1 = i then 1 else 0
def SplitXY : Prop :=
  ∀ (m : ℕ) (β : ℂ), Function.Bijective (redOf m) ∧ MeasurePreserving (redOf m) (muXY β m) (muRed β m)
def SplitXYMatrix : Prop :=
  ∀ (m : ℕ) (t ρ₁ : ℂ) (p : XY m),
    (∀ k, xOf (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 k = p.1 k) ∧
    wMat (m + 2) * Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
        (Fin.cons ρ₁ (redOf m p).2.1) (redOf m p).1 =
      t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ p.1 : Fin (m + 2) → ℂ) + strictUpper p.2
def LimitCoords : Prop :=
  ∀ (m : ℕ) (z : ℂ) (y : UT (m + 2) → ℂ), ∃! q : RedCoord m,
    (∀ k, xOf (strictUpper q.2.2.1) q.2.2.2 k = z) ∧
    wMat (m + 2) * Mcoord 0 (strictUpper q.2.2.1) q.2.2.2 (Fin.cons z q.2.1) q.1 =
      z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y
def LimitCoordsXY : Prop :=
  ∀ (m : ℕ) (z : ℂ) (y : UT (m + 2) → ℂ),
    wMat (m + 2) * Mcoord 0 (strictUpper (redOf m (fun _ => z, y)).2.2.1) (redOf m (fun _ => z, y)).2.2.2
        (Fin.cons z (redOf m (fun _ => z, y)).2.1) (redOf m (fun _ => z, y)).1 =
      z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y
def chi0 (r : ℝ) : ℝ := Real.smoothTransition (2 - r)
def cutM {s : ℕ} (τ : ℝ) (Z : Mat s) : ℝ := ∏ i, ∏ j, chi0 (‖Z i j‖ ^ 2 / τ ^ 2)
def critCut {n : ℕ} (δ : ℝ) (z : ℂ) (x : Fin n → ℂ) : ℝ := ∏ k, chi0 (‖x k - z‖ ^ 2 / δ ^ 2)
def Chi0Spec : Prop :=
  (∀ r : ℝ, r ≤ 1 → chi0 r = 1) ∧ (∀ r : ℝ, 2 ≤ r → chi0 r = 0) ∧ (∀ r : ℝ, 0 ≤ chi0 r ∧ chi0 r ≤ 1) ∧
    ∀ k : ℕ, ContDiff ℝ k chi0
def CutMSpec : Prop :=
  ∀ s : ℕ,
    (∀ (τ : ℝ) (Z : Mat s), 0 < τ → 0 ≤ cutM τ Z ∧ cutM τ Z ≤ 1 ∧ (‖Z‖ ≤ τ → cutM τ Z = 1) ∧
      (2 * τ ≤ ‖Z‖ → cutM τ Z = 0)) ∧
    ∀ k : ℕ, ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → ContDiff ℝ k (cutM (s := s) τ) ∧
      ∀ j ≤ k, ∀ Z : Mat s, ‖iteratedFDeriv ℝ j (cutM τ) Z‖ ≤ C * (τ ^ j)⁻¹
def CritCutSpec : Prop :=
  ∀ (m : ℕ) (δ : ℝ), 0 < δ →
    (∀ (z : ℂ) (x : Fin (m + 1) → ℂ), 0 ≤ critCut δ z x ∧ critCut δ z x ≤ 1 ∧
      (‖x - fun _ => z‖ ≤ δ → critCut δ z x = 1) ∧ (2 * δ ≤ ‖x - fun _ => z‖ → critCut δ z x = 0)) ∧
    (∀ k : ℕ, ∃ C : ℝ, ∀ z : ℂ, ContDiff ℝ k (critCut (n := m + 1) δ z) ∧
      ∀ j ≤ k, ∀ x : Fin (m + 1) → ℂ, ‖iteratedFDeriv ℝ j (critCut δ z) x‖ ≤ C) ∧
    ∀ (z z' : ℂ) (x : Fin (m + 1) → ℂ), z ^ (m + 2) = z' ^ (m + 2) → z ≠ z' →
      100 * ((m : ℝ) + 2) * δ ≤ ‖z‖ → critCut δ z x ≠ 0 → critCut δ z' x = 0
section Cut
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
def cutPhi {s : ℕ} (τ : ℝ) (Φ : Mat s → V) : Mat s → V := fun Z => ((cutM τ Z : ℝ) : ℂ) • Φ Z
def cutPhiC {s : ℕ} (τ : ℝ) (Φ : Mat s → V) : Mat s → V := fun Z => ((1 - cutM τ Z : ℝ) : ℂ) • Φ Z
end Cut
def CutPhiBound : Prop :=
  ∀ s k : ℕ, ∃ C : ℝ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Φ : Mat s → V) (Kd : Set ℂ)
    (bd : Mat s → ℝ) (τ : ℝ), 1 ≤ τ → DerivBound k Kd bd Φ →
    DerivBound k Kd (fun Z => C * bd Z) (cutPhi τ Φ) ∧ DerivBound k Kd (fun Z => C * bd Z) (cutPhiC τ Φ)
def orbM (n : ℕ) (t c : ℂ) (p : BlockCoord n) : Mat (n + 1) :=
  lowRow p.1 * ptBlock n t c * blk (upper p.2.1) p.2.2 0 1
def TailBound : Prop :=
  ∀ (m : ℕ) (β : ℂ), ∃ Cst : ℝ,
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V)
      (A K τ : ℝ) (t c : ℂ), ((m : ℝ) + 1) * ((m : ℝ) + 4) + 1 ≤ A → 0 < τ → t ≠ 0 →
      DerivBound 0 {(wMat (m + 1)).det * (c * t ^ (m + 1))} (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      (∀ p : BlockCoord (m + 1), ‖orbM (m + 1) t c p‖ < τ → Φ (orbM (m + 1) t c p) = 0) →
      ‖OmBlock β (m + 1) Φ t c‖ ≤
        Cst * K * (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * (max 1 τ) ^ (((m : ℝ) + 1) * ((m : ℝ) + 4) - A)
def TailStep : Prop :=
  ∀ (m : ℕ) (β : ℂ), ∃ Cst : ℝ,
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V)
      (A K ε : ℝ) (t c : ℂ), 0 < ε → ε ≤ 1 →
      ((m : ℝ) + 1) * ((m : ℝ) + 4) + (3 * (m : ℝ) + 4) / ε ≤ A → t ≠ 0 → ‖t‖ ≤ 1 →
      DerivBound 0 {(wMat (m + 1)).det * (c * t ^ (m + 1))} (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      ‖((‖t‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) • OmBlock β (m + 1) (cutPhiC (‖t‖ ^ (-ε)) Φ) t c‖ ≤ Cst * K * ‖t‖
def TailStepOfBound : Prop := TailBound → CutMSpec → CutPhiBound → TailStep
def GermLargeT : Prop :=
  ∀ (m : ℕ) (β : ℂ) (Kc : Set ℂ), IsCompact Kc → (0 : ℂ) ∉ Kc → ∀ t₀ : ℝ, 0 < t₀ → ∃ Cst : ℝ,
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V)
      (A K : ℝ), ((m : ℝ) + 1) * ((m : ℝ) + 4) + 1 ≤ A →
      DerivBound 0 (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      ∀ t c : ℂ, t₀ ≤ ‖t‖ → c * t ^ (m + 1) ∈ Kc → ‖remainder β m (fun _ => 1) Φ t c‖ ≤ Cst * K * ‖t‖
def rhoXY (m : ℕ) (D t : ℂ) (p : XY m) : ℂ :=
  rho1 D (redOf m p).1 (redOf m p).2.1 (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 t
def cofXY (m : ℕ) (t : ℂ) (p : XY m) : ℂ := Cof (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 t
def MXY (m : ℕ) (D t : ℂ) (p : XY m) : Mat (m + 1 + 1) :=
  Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 (Fin.cons (rhoXY m D t p) (redOf m p).2.1)
    (redOf m p).1
def gRem (m : ℕ) (D t : ℂ) (p : XY m) : ℂ := (rhoXY m D t p - (-1) ^ (m + 3) * D / ∏ k, p.1 k) / t
section Amp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
def redIntegrand (β : ℂ) (m : ℕ) (Φ : Mat (m + 1 + 1) → V) (D t : ℂ) (q : RedCoord m) : V :=
  (psi β ((rho1 D q.1 q.2.1 (strictUpper q.2.2.1) q.2.2.2 t + ∑ k, xOf (strictUpper q.2.2.1) q.2.2.2 k) / t) *
      (((‖Cof (strictUpper q.2.2.1) q.2.2.2 t‖ ^ 2)⁻¹ : ℝ) : ℂ)) •
    Φ (Mcoord t (strictUpper q.2.2.1) q.2.2.2 (Fin.cons (rho1 D q.1 q.2.1 (strictUpper q.2.2.1) q.2.2.2 t) q.2.1)
      q.1)
def amp (β : ℂ) (m : ℕ) (Φ : Mat (m + 1 + 1) → V) (D t : ℂ) (p : XY m) : V :=
  (psi β (gRem m D t p) * (((‖cofXY m t p‖ ^ 2)⁻¹ : ℝ) : ℂ)) • Φ (MXY m D t p)
def ampIn (β : ℂ) (m : ℕ) (ε : ℝ) (Φ : Mat (m + 1 + 1) → V) (D t : ℂ) (p : XY m) : V :=
  amp β m (cutPhi (‖t‖ ^ (-ε)) Φ) D t p
def oscIn (β : ℂ) (m : ℕ) (ε : ℝ) (Φ : Mat (m + 1 + 1) → V) (D t : ℂ) (p : XY m) : V :=
  psi β (g0 ((-1) ^ (m + 3) * D) p.1 / t) • ampIn β m ε Φ D t p
end Amp
def AmpEq : Prop :=
  ∀ (m : ℕ) (β D t : ℂ), t ≠ 0 → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Φ : Mat (m + 1 + 1) → V) (p : XY m),
    psi β (g0 ((-1) ^ (m + 3) * D) p.1 / t) • amp β m Φ D t p = redIntegrand β m Φ D t (redOf m p)
def DetMXY : Prop :=
  ∀ (m : ℕ) (D t : ℂ) (p : XY m), cofXY m t p ≠ 0 → detM (MXY m D t p) = (wMat (m + 1)).det * D
def RedIntegrable : Prop :=
  ∀ (m : ℕ) (β t c : ℂ), t ≠ 0 →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V),
      Integrable (blockIntegrand β (m + 1) Φ t c) (muBlock β (m + 1)) →
      Integrable (redIntegrand β m Φ (c * t ^ (m + 1)) t) (muRed β m)
def InnerXY : Prop :=
  ∀ (m : ℕ) (β t c : ℂ), t ≠ 0 →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V),
      Integrable (blockIntegrand β (m + 1) Φ t c) (muBlock β (m + 1)) →
      Integrable (fun p : XY m =>
        psi β (g0 ((-1) ^ (m + 3) * (c * t ^ (m + 1))) p.1 / t) • amp β m Φ (c * t ^ (m + 1)) t p) (muXY β m) ∧
      ((‖t‖ ^ ((m + 1) * (m + 2)) : ℝ) : ℂ) • OmBlock β (m + 1) Φ t c =
        ∫ p : XY m, psi β (g0 ((-1) ^ (m + 3) * (c * t ^ (m + 1))) p.1 / t) • amp β m Φ (c * t ^ (m + 1)) t p
          ∂(muXY β m)
def InnerXYOfReduced : Prop := OmReduced → RedIntegrable → SplitXY → AmpEq → InnerXY
def ProdLower : Prop :=
  ∀ (m : ℕ) (Kc : Set ℂ), IsCompact Kc → (0 : ℂ) ∉ Kc → ∀ R : ℝ, 0 < R → ∃ t₀ c₀ : ℝ, 0 < t₀ ∧ 0 < c₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (2 * ((m : ℝ) + 2)) → ∀ D ∈ Kc, ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ t₀ →
    ∀ (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ) (ρ₁ : ℂ) (ρ' : Fin m → ℂ) (σ : ℂ),
      IsStrictUpper X → (∀ i j, ‖X i j‖ ≤ R * ‖t‖ ^ (-ε)) → (∀ i, ‖B i‖ ≤ R * ‖t‖ ^ (-ε)) →
      ‖ρ₁‖ ≤ R * ‖t‖ ^ (-ε) → (∀ k, ‖ρ' k‖ ≤ R * ‖t‖ ^ (-ε)) → ‖σ‖ ≤ R * ‖t‖ ^ (-ε) →
      t ^ (m + 1) * σ = D + Cof X B t * ρ₁ + R0 X B ρ' t →
      c₀ * ‖t‖ ^ ε ≤ ‖∏ k, xOf X B k‖ ∧ ∀ k, c₀ * ‖t‖ ^ (((m : ℝ) + 2) * ε) ≤ ‖xOf X B k‖
def SmallDelta (m : ℕ) (Kc : Set ℂ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ D ∈ Kc, ∀ z : ℂ, z ^ (m + 2) = (-1) ^ (m + 3) * D → 100 * ((m : ℝ) + 2) * δ ≤ ‖z‖
def SmallDeltaExists : Prop :=
  ∀ (m : ℕ) (Kc : Set ℂ), IsCompact Kc → (0 : ℂ) ∉ Kc → ∃ δ : ℝ, SmallDelta m Kc δ
def farCut (m : ℕ) (δ : ℝ) (D : ℂ) (x : Fin (m + 1) → ℂ) : ℝ :=
  1 - ∑ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D), critCut δ z x
def wirt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ} (k : Fin d) (b : (Fin d → ℂ) → V)
    (x : Fin d → ℂ) : V :=
  (1 / 2 : ℂ) • (fderiv ℝ b x (Pi.single k 1) - Complex.I • fderiv ℝ b x (Pi.single k Complex.I))
def WirtingerIBP : Prop :=
  ∀ (d : ℕ) (β t : ℂ) (Ω : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ), t ≠ 0 → IsOpen Ω → DifferentiableOn ℂ g Ω →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b : (Fin d → ℂ) → V) (k : Fin d),
      ContDiff ℝ 1 b → HasCompactSupport b → tsupport b ⊆ Ω →
      ∫ x : Fin d → ℂ, psi β (g x / t) • wirt k b x ∂(muPi β (Fin d)) =
        -∫ x : Fin d → ℂ, (Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) * psi β (g x / t)) • b x
          ∂(muPi β (Fin d))
def NonStatPhase : Prop :=
  ∀ (d q : ℕ) (β : ℂ), β ≠ 0 → ∃ C : ℝ,
    ∀ (Ω : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ) (η P S : ℝ), IsOpen Ω → DifferentiableOn ℂ g Ω →
      0 < η → 0 < P → (∀ x ∈ Ω, η ≤ ‖fderiv ℂ g x‖) →
      (∀ x ∈ Ω, ∀ j : ℕ, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℂ (j + 1) g x‖ ≤ ‖fderiv ℂ g x‖ * P ^ j) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (a : (Fin d → ℂ) → V),
        ContDiff ℝ q a → HasCompactSupport a → tsupport a ⊆ Ω →
        (∀ j ≤ q, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S * P ^ j) →
        ∀ t : ℂ, t ≠ 0 →
          ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d))‖ ≤
            C * S * (‖t‖ * P / η) ^ q * (muPi β (Fin d) (tsupport a)).toReal
def PhaseFunctionRelativeDeriv : Prop :=
  ∀ m : ℕ,
    (∀ (D' : ℂ) (x : Fin (m + 1) → ℂ), (∀ k, x k ≠ 0) →
      ‖dg0 D' x‖ ≤ ‖fderiv ℂ (g0 D') x‖ ∧ ‖fderiv ℂ (g0 D') x‖ ≤ ((m : ℝ) + 1) * ‖dg0 D' x‖) ∧
    ∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, ∀ (D' : ℂ) (x : Fin (m + 1) → ℂ) (r : ℝ), 0 < r → (∀ k, r ≤ ‖x k‖) →
      ‖iteratedFDeriv ℂ (j + 1) (g0 D') x‖ ≤ C * (1 + ‖dg0 D' x‖) * (r ^ j)⁻¹
def AmpBoundFar : Prop :=
  ∃ C₉ : ℕ, ∀ (m : ℕ) (β : ℂ) (Kc : Set ℂ), IsCompact Kc → (0 : ℂ) ∉ Kc → ∀ δ ε : ℝ, SmallDelta m Kc δ →
    0 < ε → ε ≤ 1 / (2 * ((m : ℝ) + 2)) → ∀ q : ℕ, ∃ Cst t₀ c₀ : ℝ, 0 < t₀ ∧ 0 < c₀ ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V)
      (A K : ℝ) (k : ℕ), 0 ≤ A → q ≤ k →
      DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      ∀ t D : ℂ, t ≠ 0 → ‖t‖ ≤ t₀ → D ∈ Kc → ∀ y : UT (m + 2) → ℂ,
        ContDiff ℝ q (fun x : Fin (m + 1) → ℂ => ((farCut m δ D x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) ∧
        (∀ x : Fin (m + 1) → ℂ, ((farCut m δ D x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y) ≠ 0 →
          ‖y‖ ≤ 2 * ‖t‖ ^ (-ε) ∧ (∀ k, ‖x k‖ ≤ 2 * ‖t‖ ^ (-ε) ∧ c₀ * ‖t‖ ^ (((m : ℝ) + 2) * ε) ≤ ‖x k‖) ∧
          ∀ z : ℂ, z ^ (m + 2) = (-1) ^ (m + 3) * D → δ ≤ ‖x - fun _ => z‖) ∧
        ∀ j ≤ q, ∀ x : Fin (m + 1) → ℂ,
          ‖iteratedFDeriv ℝ j
              (fun x : Fin (m + 1) → ℂ => ((farCut m δ D x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) x‖ ≤
            Cst * K * ‖t‖ ^ (-(ε * ((C₉ : ℝ) * ((m : ℝ) + 2) * ((j : ℝ) + 1))))
def NonStatStep : Prop :=
  ∃ C₀ C₂ : ℕ, 0 < C₀ ∧ ∀ (m : ℕ) (β : ℂ), β ≠ 0 → ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∀ δ ε : ℝ, SmallDelta m Kc δ → 0 < ε → ε ≤ 1 / ((C₀ : ℝ) * ((m : ℝ) + 2)) → ∃ Cst t₀ : ℝ, 0 < t₀ ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V)
      (A K : ℝ) (k : ℕ), ((m : ℝ) + 1) * ((m : ℝ) + 4) + 1 ≤ A → C₂ * (m + 2) ^ 2 ≤ k →
      DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      ∀ t c : ℂ, t ≠ 0 → ‖t‖ ≤ t₀ → c * t ^ (m + 1) ∈ Kc →
        ‖∫ p : XY m, ((farCut m δ (c * t ^ (m + 1)) p.1 : ℝ) : ℂ) • oscIn β m ε Φ (c * t ^ (m + 1)) t p
            ∂(muXY β m)‖ ≤ Cst * K * ‖t‖ ^ (m + 2)
def NonStatStepOfParts : Prop :=
  NonStatPhase → GradLower → PhaseFunctionDeriv → PhaseFunctionRelativeDeriv → CritCutSpec → AmpBoundFar → OmConverges → CutPhiBound →
    InnerXY → NonStatStep
def StationaryPhase : Prop :=
  ∀ (d : ℕ) (β : ℂ), β ≠ 0 → ∀ r Λ : ℝ, 0 < r → 0 < Λ → ∃ C : ℝ,
    ∀ (x₀ : Fin d → ℂ) (g : (Fin d → ℂ) → ℂ) (dg : (Fin d → ℂ) → Fin d → ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
      DifferentiableOn ℂ g (Metric.ball x₀ (2 * r)) → (∀ x ∈ Metric.ball x₀ (2 * r), ‖g x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball x₀ (2 * r), ∀ k, HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k)) →
      (∀ k, dg x₀ k = 0) →
      (∀ i j, HasDerivAt (fun ξ => dg (Function.update x₀ j ξ) i) (H i j) (x₀ j)) →
      (∀ x ∈ Metric.closedBall x₀ r, ‖x - x₀‖ ≤ Λ * ‖dg x‖) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (a : (Fin d → ℂ) → V) (S : ℝ),
        ContDiff ℝ (2 * d + 2 : ℕ) a → Function.support a ⊆ Metric.closedBall x₀ r →
        (∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        ∀ t : ℂ, t ≠ 0 →
          ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) -
              (psi β (g x₀ / t) * ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • a x₀‖ ≤ C * S * ‖t‖ ^ (d + 1)
def PhaseFunctionNearCritical : Prop :=
  ∀ (m : ℕ) (δ Rz : ℝ), 0 < δ → ∃ Λ : ℝ, 0 < Λ ∧ ∀ z : ℂ, 100 * ((m : ℝ) + 2) * δ ≤ ‖z‖ → ‖z‖ ≤ Rz →
    (∀ x ∈ Metric.ball (fun _ : Fin (m + 1) => z) (2 * (2 * δ)), (∀ k, x k ≠ 0) ∧ ‖g0 (z ^ (m + 2)) x‖ ≤ Λ) ∧
    DifferentiableOn ℂ (g0 (z ^ (m + 2))) (Metric.ball (fun _ : Fin (m + 1) => z) (2 * (2 * δ))) ∧
    ∀ x ∈ Metric.closedBall (fun _ : Fin (m + 1) => z) (2 * δ),
      ‖x - fun _ => z‖ ≤ Λ * ‖dg0 (z ^ (m + 2)) x‖
def AmpBoundCrit : Prop :=
  ∃ E : ℕ, ∀ (m : ℕ) (β : ℂ) (Kc : Set ℂ), IsCompact Kc → (0 : ℂ) ∉ Kc → ∀ δ ε : ℝ, SmallDelta m Kc δ →
    0 < ε → ε ≤ 1 / (2 * ((m : ℝ) + 2)) → ∃ Cst t₀ : ℝ, 0 < t₀ ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V)
      (A K : ℝ) (k : ℕ), 0 ≤ A → 2 * (m + 1) + 2 ≤ k →
      DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      ∀ t D z : ℂ, t ≠ 0 → ‖t‖ ≤ t₀ → D ∈ Kc → z ^ (m + 2) = (-1) ^ (m + 3) * D → ∀ y : UT (m + 2) → ℂ,
        ContDiff ℝ (2 * (m + 1) + 2 : ℕ)
          (fun x : Fin (m + 1) → ℂ => ((critCut δ z x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) ∧
        ∀ j ≤ 2 * (m + 1) + 2, ∀ x : Fin (m + 1) → ℂ,
          ‖iteratedFDeriv ℝ j
              (fun x : Fin (m + 1) → ℂ => ((critCut δ z x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) x‖ ≤
            Cst * K * (1 + ‖y‖) ^ (E * (m + 2) ^ 2) * (max 1 ‖y‖) ^ (-A)
def AmpCritContinuous : Prop :=
  ∀ (m : ℕ) (β : ℂ) (Kc : Set ℂ), IsCompact Kc → (0 : ℂ) ∉ Kc → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (2 * ((m : ℝ) + 2)) →
    ∃ t₀ : ℝ, 0 < t₀ ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V)
      (bd : Mat (m + 1 + 1) → ℝ), DerivBound 0 (detSet (m + 1) Kc) bd Φ →
      ∀ t D z : ℂ, t ≠ 0 → ‖t‖ ≤ t₀ → D ∈ Kc → z ^ (m + 2) = (-1) ^ (m + 3) * D →
        Continuous (fun y : UT (m + 2) → ℂ => ampIn β m ε Φ D t (fun _ => z, y))
def MajorantY : Prop :=
  ∀ (m E' : ℕ) (β : ℂ), ∃ C : ℝ, ∀ A : ℝ, (E' : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) + 1 ≤ A →
    Integrable (fun y : UT (m + 2) → ℂ => (1 + ‖y‖) ^ E' * (max 1 ‖y‖) ^ (-A)) (muPi β (UT (m + 2))) ∧
    ∫ y : UT (m + 2) → ℂ, (1 + ‖y‖) ^ E' * (max 1 ‖y‖) ^ (-A) ∂(muPi β (UT (m + 2))) ≤ C ∧
    ∀ τ : ℝ, 1 ≤ τ →
      ∫ y in {y : UT (m + 2) → ℂ | τ ≤ ‖y‖}, (1 + ‖y‖) ^ E' * (max 1 ‖y‖) ^ (-A) ∂(muPi β (UT (m + 2))) ≤
        C * τ ^ ((E' : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) - A)
def StatStep : Prop :=
  ∃ E : ℕ, ∀ (m : ℕ) (β : ℂ), β ≠ 0 → ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∀ δ ε : ℝ, SmallDelta m Kc δ → 0 < ε → ε ≤ 1 / (2 * ((m : ℝ) + 2)) → ∃ Cst t₀ : ℝ, 0 < t₀ ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V)
      (A K : ℝ) (k : ℕ), (E : ℝ) * ((m : ℝ) + 2) ^ 2 ≤ A → 2 * (m + 1) + 2 ≤ k →
      DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      ∀ t c z : ℂ, t ≠ 0 → ‖t‖ ≤ t₀ → c * t ^ (m + 1) ∈ Kc → z ^ (m + 2) = (-1) ^ (m + 3) * (c * t ^ (m + 1)) →
        ‖∫ p : XY m, ((critCut δ z p.1 : ℝ) : ℂ) • oscIn β m ε Φ (c * t ^ (m + 1)) t p ∂(muXY β m) -
            (psi β (((m : ℂ) + 2) * z / t) * ((‖t‖ ^ (m + 1) * ‖z‖ ^ (m + 1) / ((m : ℝ) + 2) : ℝ) : ℂ)) •
              ∫ y : UT (m + 2) → ℂ, ampIn β m ε Φ (c * t ^ (m + 1)) t (fun _ => z, y) ∂(muPi β (UT (m + 2)))‖ ≤
          Cst * K * ‖t‖ ^ (m + 2)
def StatStepOfParts : Prop :=
  StationaryPhase → PhaseFunctionDeriv → PhaseFunctionCritical → HessCrit → HessDet → PhaseFunctionNearCritical → CritCutSpec → AmpBoundCrit →
    AmpCritContinuous → MajorantY → OmConverges → CutPhiBound → InnerXY → StatStep
def AmpLimit : Prop :=
  ∃ E : ℕ, ∀ (m : ℕ) (β : ℂ) (Kc : Set ℂ), IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (2 * ((m : ℝ) + 2)) → ∃ Cst t₀ : ℝ, 0 < t₀ ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ : Mat (m + 1 + 1) → V)
      (A K : ℝ) (k : ℕ), (E : ℝ) * ((m : ℝ) + 2) ^ 2 + 3 * ((m : ℝ) + 2) / ε ≤ A → 1 ≤ k →
      DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ →
      ∀ t D z : ℂ, t ≠ 0 → ‖t‖ ≤ t₀ → D ∈ Kc → z ^ (m + 2) = (-1) ^ (m + 3) * D →
        ‖∫ y : UT (m + 2) → ℂ, ampIn β m ε Φ D t (fun _ => z, y) ∂(muPi β (UT (m + 2))) -
            (((‖z‖ ^ (2 * (m + 1)))⁻¹ : ℝ) : ℂ) •
              ∫ y : UT (m + 2) → ℂ, psi β (superSum (strictUpper y) / z) •
                Φ (wMat (m + 2) * (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y))
                ∂(muPi β (UT (m + 2)))‖ ≤ Cst * K * ‖t‖
def GermRateOfSteps : Prop :=
  OmConverges → CutPhiBound → CritCutSpec → SmallDeltaExists → RootSetSpec → TailStep → InnerXY → NonStatStep →
    StatStep → AmpLimit → LimitIntegral → LeadingConstant → GermLargeT → GermRate
end
end Formalism.FourierDecayAlt.G


