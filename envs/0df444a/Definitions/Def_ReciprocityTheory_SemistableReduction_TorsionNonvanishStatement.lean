-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
-- name    : ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:11.148928+00:00
-- url     : https://prove2.me/theorems/e18a3283-478a-431f-9013-1887d5ced046
-- title:
--   Torsion Nonvanish Statement
-- statement:
--   Definitions and structural lemmas for Torsion Nonvanish Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorsionNonvanishStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
def triChar {p : ℕ} (a : Fin p → ℕ) (b : Matrix (Fin p) (Fin p) ℂ) : ℂ :=
  ∏ i, b i i ^ a i
def IsTriEquivariant {p : ℕ} (a : Fin p → ℕ) (P : Matrix (Fin p) (Fin p) ℂ → ℂ) : Prop :=
  ∀ x b : Matrix (Fin p) (Fin p) ℂ, x.det ≠ 0 → b.det ≠ 0 → b.BlockTriangular id →
    P (x * b) = triChar a b * P x
def colNormSq {p : ℕ} (x : Matrix (Fin p) (Fin p) ℂ) (j : Fin p) : ℝ :=
  ∑ i, ‖x i j‖ ^ 2
def LemmaHStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : ι → ℕ) (a : ∀ s, Fin (p s) → ℕ)
    (P : (∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) → ℂ) (C R : ℝ),
    (∀ (x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (s : ι) (b : Matrix (Fin (p s)) (Fin (p s)) ℂ),
      (∀ t, (x t).det ≠ 0) → b.det ≠ 0 → b.BlockTriangular id →
      P (Function.update x s (x s * b)) = triChar (a s) b * P x) →
    (∀ k : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ,
      (∀ s, k s ∈ Matrix.unitaryGroup (Fin (p s)) ℂ) → ‖P k‖ ≤ C) → 0 ≤ R →
    ∀ x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ, (∀ s, (x s).det ≠ 0) →
      (∀ s j, colNormSq (x s) j ≤ R ^ 2) → ‖P x‖ ≤ C * R ^ (∑ s, ∑ i, a s i)
def BalancedSchwarzStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Set E) (g : E → ℂ) (M : ℝ),
    IsOpen s → Balanced ℂ s → DifferentiableOn ℂ g s → (∀ w ∈ s, ‖g w‖ ≤ M) →
    ∀ z ∈ s, ‖g z - g 0‖ ≤ (M + ‖g 0‖) * gauge s z
def TorsionNonvanishStatement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (θ : V → ℂ) (Λ : AddSubgroup V) (ρ : ℝ) (n : ℕ),
    Differentiable ℂ θ → (∃ z, θ z ≠ 0) →
    (∀ l ∈ Λ, ∀ z, ‖θ (z + l)‖ * Real.exp (-(Real.pi / 2) * ‖z + l‖ ^ 2) =
      ‖θ z‖ * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) →
    (∀ v : V, ∃ l ∈ Λ, ‖v - l‖ ≤ ρ) → 5 * ρ < n →
    ∃ l ∈ Λ, θ ((n : ℂ)⁻¹ • l) ≠ 0
def sgn (p : ℕ) {r : ℕ} (k : Fin r) : ℂ := if (k : ℕ) < p then 1 else -1
def jForm (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) : ℂ :=
  ∑ k, sgn p k * (conj (x k) * y k)
def normSq {r : ℕ} (u : Fin r → ℂ) : ℝ := ∑ k, ‖u k‖ ^ 2
def posSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ℝ :=
  ∑ k : Fin r, if (k : ℕ) < p then ‖u k‖ ^ 2 else 0
def negSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ℝ :=
  ∑ k : Fin r, if (k : ℕ) < p then 0 else ‖u k‖ ^ 2
def approxR (r : ℕ) (μ ρ : ℝ) : ℝ := 4 * Real.sqrt r * μ / ρ
def ApproxGraphStatement : Prop :=
  ∀ (r p : ℕ) (μ ρ : ℝ) (X : Fin r → Fin r → ℂ), p ≤ r → 0 < μ → 0 < ρ → ρ ≤ 1 →
    (∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2) →
    (∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j))) ∧
    (∀ y : Fin r → ℂ, (∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) → y ≠ 0 →
      (jForm p y y).re < 0) ∧
    (∀ v y : Fin r → ℂ, (∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) →
      v - y ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p}) →
      ‖jForm p y y‖ ≤ 2 * normSq v)
structure HermForm (K : Type) [Field K] [NumberField K] (r : ℕ) where

  c : K →+* K
  c_invol : ∀ x, c (c x) = x
  c_emb : ∀ (σ : K →+* ℂ) (x : K), σ (c x) = conj (σ x)

  G : Matrix (Fin r) (Fin r) K
  G_herm : ∀ a b, c (G a b) = G b a
def HermForm.h {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (x y : Fin r → K) : K :=
  ∑ a, ∑ b, S.c (x a) * S.G a b * y b
def embVec {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ) (x : Fin r → K) : Fin r → ℂ := fun a => σ (x a)
def IsIntegralElt {K : Type} [Field K] [NumberField K] (x : K) : Prop := ∃ z : 𝓞 K, (z : K) = x
def IsLattice {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin r → K)) = ⊤
def IsIntegralOn {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, IsIntegralElt (S.h x y)
def IsSelfDual {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  IsIntegralOn S L ∧ ∀ x, (∀ y ∈ L, IsIntegralElt (S.h x y)) → x ∈ L
def majSq {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (v : Fin r → K) : ℝ :=
  ∑ i, normSq (Q i *ᵥ embVec (σ i) v)
def ApproxStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [Nonempty ι] (r p : ℕ)
    (S : HermForm K r) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (v : Fin r → Fin r → K) (μ ρ : ℝ),
    p ≤ r → 0 < μ → 0 < ρ → ρ ≤ 1 → (∀ i, (Q i).det ≠ 0) →
    (∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y)) →
    IsIntegralOn S L →
    (∀ w : ι → Fin r → ℂ, ∃ l ∈ L, ∑ i, normSq (Q i *ᵥ embVec (σ i) l - w i) ≤ μ ^ 2) →
    (∀ j, v j ∈ L) → LinearIndependent K v → (∀ j, majSq σ Q (v j) ≤ μ ^ 2) →
    ∃ la : Fin r → Fin r → K, (∀ j, la j ∈ L) ∧ LinearIndependent K la ∧
      (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → S.h (la j) (la k) = 0) ∧
      (∀ i (w : Fin r → ℂ), (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
        negSq p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j)) ≤
          (ρ / 3) ^ 2 * posSq p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j)) ∧
        (w ≠ 0 → 0 < (jForm p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))
          (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))).re)) ∧
      (∀ i (w : Fin r → ℂ), (∀ j : Fin r, (j : ℕ) < p → w j = 0) → w ≠ 0 →
        (jForm p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))
          (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))).re < 0) ∧
      (∀ i (j : Fin r), (j : ℕ) < p → ‖σ i (S.h (la j) (la j))‖ ≤ (2 * approxR r μ ρ) ^ 2) ∧
      (∀ i (j : Fin r), p ≤ (j : ℕ) →
        ‖σ i (S.h (la j) (la j))‖ ≤ (2 * approxR r μ ρ) ^ (4 * p) * (2 * μ ^ 2))
def OnePolyGrowthStatement : Prop :=
  ∀ (f : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (k : ℕ), B.Finite → DifferentiableOn ℂ f Bᶜ →
    (∀ t ∉ B, ‖f t‖ ≤ A * (1 + ‖t‖) ^ k) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ t ∉ B, f t = P.eval t
def IsHoloGL {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ (fun y : Fin p → Fin p → ℂ => P (Matrix.of y)) {y | (Matrix.of y).det ≠ 0}
def IsBW {p : ℕ} (a : Fin p → ℕ) (P : Matrix (Fin p) (Fin p) ℂ → ℂ) : Prop :=
  IsHoloGL P ∧ IsTriEquivariant a P ∧ ∀ x : Matrix (Fin p) (Fin p) ℂ, x.det = 0 → P x = 0
def leadMinor {p : ℕ} (x : Matrix (Fin p) (Fin p) ℂ) (i : Fin p) : ℂ :=
  (Matrix.of fun a b : Fin (i + 1) => x (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)).det
def nextExp {p : ℕ} (a : Fin p → ℕ) (i : Fin p) : ℕ :=
  if h : (i : ℕ) + 1 < p then a ⟨i + 1, h⟩ else 0
def minorProd {p : ℕ} (a : Fin p → ℕ) (x : Matrix (Fin p) (Fin p) ℂ) : ℂ :=
  if x.det = 0 then 0 else ∏ i, leadMinor x i ^ (a i - nextExp a i)
def BWPolyStatement : Prop :=
  ∀ (p : ℕ) (a : Fin p → ℕ) (P : Matrix (Fin p) (Fin p) ℂ → ℂ), IsHoloGL P →
    IsTriEquivariant a P →
    ∃ F : MvPolynomial (Fin p × Fin p) ℂ, F.IsHomogeneous (∑ i, a i) ∧
      ∀ x : Matrix (Fin p) (Fin p) ℂ, x.det ≠ 0 → P x = MvPolynomial.eval (fun ij => x ij.1 ij.2) F
def BWIrredStatement : Prop :=
  ∀ (p : ℕ) (a : Fin p → ℕ),
    (Antitone a → IsBW a (minorProd a)) ∧
    ∀ S : Submodule ℂ (Matrix (Fin p) (Fin p) ℂ → ℂ), (∀ P ∈ S, IsBW a P) →
      (∀ g : Matrix (Fin p) (Fin p) ℂ, g.det ≠ 0 → ∀ P ∈ S, (fun x => P (g * x)) ∈ S) →
      S ≠ ⊥ → ∀ P, IsBW a P → P ∈ S
end ReciprocityTheory.MultiplicativeHeights


