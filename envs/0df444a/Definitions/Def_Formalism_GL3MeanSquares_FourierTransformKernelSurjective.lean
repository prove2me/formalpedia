-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
-- name    : Formalism_GL3MeanSquares_FourierTransformKernelSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:29.698855+00:00
-- url     : https://prove2.me/theorems/2b9edfb3-2a83-49a4-9a35-8aae9846c192
-- title:
--   Fourier Transform Kernel Surjective
-- statement:
--   Definitions and structural lemmas for Fourier Transform Kernel Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/FourierTransformKernelSurjective.lean

import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_GaussOperatorProductFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.LocalLatticeBases
open Finset Matrix
def SumZeroLatticeSpanning : Prop :=
  ∀ n : ℕ,
    (∀ v : Fin (n + 1) → ℤ, ∑ i, v i = 0 →
      v = ∑ i : Fin n, v i.castSucc • (Pi.single i.castSucc (1 : ℤ) - Pi.single (Fin.last n) 1)) ∧
    (Matrix.of fun i j : Fin n =>
        ((Pi.single i.castSucc (1 : ℚ) - Pi.single (Fin.last n) 1 : Fin (n + 1) → ℚ) ⬝ᵥ
          (Pi.single j.castSucc (1 : ℚ) - Pi.single (Fin.last n) 1))).det = n + 1
def SlopeTensorProductAdditive : Prop :=
  ∀ (a b : Type) [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] [Nonempty a] [Nonempty b]
    (A : Matrix a a ℝ) (B : Matrix b b ℝ), 0 < A.det → 0 < B.det →
    -Real.log (Matrix.kroneckerMap (· * ·) A B).det / ((Fintype.card a : ℝ) * Fintype.card b) =
      -Real.log A.det / Fintype.card a + -Real.log B.det / Fintype.card b
def LemmaB'_avg : Prop :=
  ∀ (k n : ℕ) (S : Finset (Fin k → ℕ)) (mult : (Fin k → ℕ) → ℕ),
    (∀ σ : Equiv.Perm (Fin k), ∀ w ∈ S, w ∘ σ ∈ S) →
    (∀ σ : Equiv.Perm (Fin k), ∀ w, mult (w ∘ σ) = mult w) →
    (∀ w ∈ S, ∑ i, w i = n) →
    ∀ j : Fin k, k * ∑ w ∈ S, mult w * w j = n * ∑ w ∈ S, mult w
def LemmaB'_twist : Prop :=
  ∀ (k : ℕ) (lam : Fin (k + 2) → ℚ) (a W b' : ℚ),
    lam 0 = a → (∀ i : Fin (k + 2), i ≠ 0 → |lam i| ≤ W) → lam (Fin.last (k + 1)) = -b' →
    (∑ i, (lam i + b')) / (k + 2 : ℚ) ≤ a / (k + 2 : ℚ) + 2 * W
def compF {q n n' : ℕ} (fW : Fin n' → ZMod q) (x : Matrix (Fin n') (Fin n) ℤ) : Fin n → ZMod q :=
  fun j => ∑ i, fW i * (x i j : ZMod q)
def SupportCosetStructure : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n n' : ℕ) (fW : Fin n' → ZMod q) (f : Fin n → ZMod q), fW ≠ 0 →
    ∃ x0 : Matrix (Fin n') (Fin n) ℤ,
      (∀ x : Matrix (Fin n') (Fin n) ℤ, compF fW x = f ↔ compF fW (x - x0) = 0) ∧
      compF fW ((q : ℤ) • x0) = 0 ∧
      (∀ x : Matrix (Fin n') (Fin n) ℤ, compF fW x = f →
        ∀ l : Fin n → ℤ, (∑ j, f j * (l j : ZMod q)) = 0 →
          (∑ i, fW i * ((x.mulVec l) i : ZMod q)) = 0)
def LinearFormIntegralityOnSupport : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n n' : ℕ) (fW : Fin n' → ZMod q) (f : Fin n → ZMod q),
    (∀ x : Matrix (Fin n') (Fin n) ℤ, compF fW x = f →
      ∀ l : Fin n → ℤ, (∑ j, f j * (l j : ZMod q)) = 0 →
      ∀ η : Fin n' → ℚ, (∀ μ : Fin n' → ℤ, (∑ i, fW i * (μ i : ZMod q)) = 0 →
          (∑ i, η i * μ i) ∈ Set.range (Int.cast : ℤ → ℚ)) →
        (∑ i, η i * ((x.mulVec l) i : ℚ)) ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
    (2 ≤ n → fW ≠ 0 → f ≠ 0 →
      ∃ (x : Matrix (Fin n') (Fin n) ℤ) (l : Fin n → ℤ) (η : Fin n' → ℚ),
        (∑ j, f j * (l j : ZMod q)) = 0 ∧
        (∀ μ : Fin n' → ℤ, (∑ i, fW i * (μ i : ZMod q)) = 0 →
          (∑ i, η i * μ i) ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
        (∑ i, η i * ((x.mulVec l) i : ℚ)) ∉ Set.range (Int.cast : ℤ → ℚ))
def ExponentLossPerEmbedding : Prop :=
  ∀ (ι : Type) (Ψ : Finset ι) (nonTopP : ι → Prop) [DecidablePred nonTopP]
    (W nu : ι → ℝ) (C N t : ℝ),
    (∀ τ ∈ Ψ, 0 ≤ W τ) → 0 ≤ t → t ≤ N →
    (∀ τ ∈ Ψ, nonTopP τ → nu τ ≤ 2 * W τ + t) →
    ∑ τ ∈ Ψ, (2 * W τ + C * N + if nonTopP τ then nu τ else 0) ≤
      4 * (∑ τ ∈ Ψ, W τ) + (C + 1) * Ψ.card * N
def IndicatorKernelSum : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n n' : ℕ) (fW : Fin n' → ℤ) (x0 : Fin n → ℤ)
    (x : Matrix (Fin n') (Fin n) ℚ),
    (fun j => (x0 j : ZMod q)) ≠ 0 →
    let e1 : Fin n → ℚ := fun j => (x0 j : ℚ) / q
    let intMat : Prop := ∀ i j, x i j ∈ Set.range (Int.cast : ℤ → ℚ)
    let rhs : Prop := intMat ∧ ∃ z : ℤ,
      (∑ i, (fW i : ℚ) * (x.mulVec (fun j => (x0 j : ℚ))) i) = z ∧ (z : ZMod q) = 1
    let UKcond : (Fin n' → ZMod q) → Prop := fun xW =>
      (∑ i, (fW i : ZMod q) * xW i) = 1 ∧ intMat ∧
      (∀ i, (x.mulVec e1) i - ((xW i).val : ℚ) / q ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
      (∀ (l : Fin n → ℤ) (c : ℤ), ∃ (μ : Fin n' → ℤ) (d : ℤ), ∀ i,
        (x.mulVec (fun j => (l j : ℚ) + c * e1 j)) i = μ i + d * ((xW i).val : ℚ) / q)
    let KUcond : (Fin n → ZMod q) → Prop := fun f =>
      (∑ j, f j * (x0 j : ZMod q)) = 1 ∧ intMat ∧
      (∀ j, ∃ z : ℤ, (∑ i, (fW i : ℚ) * x i j) = z ∧ (z : ZMod q) = f j)
    Nat.card {xW // UKcond xW} = Nat.card {f // KUcond f} ∧
    (rhs → Nat.card {f // KUcond f} = 1) ∧ (¬ rhs → Nat.card {f // KUcond f} = 0)
def NonintegralMatrixPreservesThirdOverlattice : Prop :=
  let x : Matrix (Fin 1) (Fin 2) ℚ := !![1, 1/3]
  let e1 : Fin 2 → ℚ := ![1/3, 0]
  (∀ (l : Fin 2 → ℤ) (c : ℤ), ∃ (μ : Fin 1 → ℤ) (d : ℤ), ∀ i,
      (x.mulVec (fun j => (l j : ℚ) + c * e1 j)) i = μ i + d * (1 : ℚ) / 3) ∧
  (∀ i, (x.mulVec e1) i - (1 : ℚ) / 3 ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
  ¬ (∀ i j, x i j ∈ Set.range (Int.cast : ℤ → ℚ))
def SupportVolumeIndex : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n n' : ℕ),
    (∀ x0 : Fin n → ZMod q, x0 ≠ 0 →
      Nat.card {x : Matrix (Fin n') (Fin n) (ZMod q) // x.mulVec x0 = 0} * q ^ n' = q ^ (n' * n)) ∧
    (∀ fW : Fin n' → ZMod q, fW ≠ 0 →
      Nat.card {x : Matrix (Fin n') (Fin n) (ZMod q) // Matrix.vecMul fW x = 0} * q ^ n =
        q ^ (n' * n))
def OddHalfShiftSignDichotomyBound : Prop :=
  ∀ (t : ℤ), Odd t → 0 ≤ t → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) →
    ∀ (vchar W C N : ℝ), |vchar| ≤ 2 * W + C * N →
      (((t : ℝ) + 1) / 2 + ε * (((t : ℝ) + 1) / 2) = 0 ∨
        ((t : ℝ) + 1) / 2 + ε * (((t : ℝ) + 1) / 2) = t + 1) ∧
      |((t : ℝ) + 1) / 2 + ε * (((t : ℝ) + 1) / 2) + vchar| ≤ t + 1 + 2 * W + C * N
def kerK {q n n' : ℕ} [NeZero q] (w : Matrix (Fin n') (Fin n) (ZMod q) → ℂ)
    (ph : (Fin n → ZMod q) → ℂ) (fW : Fin n' → ZMod q) : ℂ :=
  ∑ x, w x * ∑ f, if Matrix.vecMul fW x = f then ph f else 0
def HeckeKernelScalarInvariance : Prop :=
  ∀ (q : ℕ) [NeZero q] (n n' : ℕ) (w : Matrix (Fin n') (Fin n) (ZMod q) → ℂ)
    (ph : (Fin n → ZMod q) → ℂ) (c : (ZMod q)ˣ) (fW : Fin n' → ZMod q),
    kerK w (fun f => ph ((c : ZMod q) • f)) fW = kerK w ph ((c : ZMod q) • fW)
def chainK (R : Type) [CommRing R] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (K : ∀ j, M j →ₗ[R] M (j + 1)) : ∀ j, M 0 →ₗ[R] M j
  | 0 => LinearMap.id
  | j + 1 => (K j).comp (chainK R M K j)
def chainUK (R : Type) [CommRing R] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (U : ∀ j, Module.End R (M j)) (K : ∀ j, M j →ₗ[R] M (j + 1)) : ∀ j, M 0 →ₗ[R] M j
  | 0 => LinearMap.id
  | j + 1 => ((U (j + 1)).comp (K j)).comp (chainUK R M U K j)
def HeckeProductCommutation : Prop :=
  ∀ (R : Type) [CommRing R] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (U : ∀ j, Module.End R (M j)) (K : ∀ j, M j →ₗ[R] M (j + 1)) (c : ℕ → Rˣ),
    (∀ j, (U (j + 1)).comp (K j) = (c j : R) • (K j).comp (U j)) →
    ∀ m : ℕ, (chainK R M K m).comp ((U 0) ^ m) =
      ((∏ j ∈ range m, (c j)⁻¹ ^ (m - j) : Rˣ) : R) • chainUK R M U K m
def LengthQuotientPowerInjective : Prop :=
  ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (U : Module.End R M),
    Function.Injective U → ∀ m : ℕ,
      Module.length R (M ⧸ LinearMap.range (U ^ m)) = m • Module.length R (M ⧸ LinearMap.range U)
def LengthQuotientTwistFormula : Prop :=
  ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (T : R),
    (∀ x : M, T • x = 0 → x = 0) → ∀ (N : Submodule R M) (c : ℕ),
      Module.length R (M ⧸ N.map ((T ^ c) • (LinearMap.id : M →ₗ[R] M))) =
        Module.length R (M ⧸ N) +
          c • Module.length R (N ⧸ LinearMap.range (T • (LinearMap.id : Module.End R N)))
def ConsecutiveRatioPowerBound : Prop :=
  ∀ q f N : ℕ, 2 ≤ N → 1 ≤ f → 2 * f * N + 1 < q →
    (((q : ℝ) - 1) / ((q : ℝ) - 2)) ^ f ≤ 1 + 2 * (f : ℝ) / q
def ExponentTotalBound : Prop :=
  ∀ (ι : Type) (Ψ TT VV : Finset ι) (W bp : ι → ℝ) (m t f N C1 C2 e1 : ℝ),
    VV ⊆ TT → 1 ≤ m → 0 ≤ t → t + 1 ≤ N → 0 ≤ f → 0 ≤ C1 → 0 ≤ C2 →
    (∀ τ ∈ Ψ, 0 ≤ W τ) → (∀ τ ∈ TT, 0 ≤ bp τ) → (∀ τ ∈ VV, W τ ≤ 2 * bp τ) →
    e1 ≤ 4 * (∑ τ ∈ Ψ, W τ) + C1 * f * N →
    m * e1 + (∑ τ ∈ VV, (t + 1 + 2 * W τ + C2 * N)) * (m * (m + 1) / 2) ≤
      (C1 + C2 + 9) * m * ((∑ τ ∈ Ψ, W τ) + f * m * N + m * ∑ τ ∈ TT, (bp τ + N))
def KroneckerRootOfUnity : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (α : K), IsIntegral ℤ α → α ≠ 0 →
    (∀ σ : K →+* ℂ, ‖σ α‖ ≤ 1) →
    (∀ ζ : K, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → ζ = 1 ∨ ζ = -1) →
    α = 1 ∨ α = -1
def InterlacingDegreeDifference : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ),
    (∀ i : Fin n, sg i ≤ lam i.castSucc ∧ lam i.succ ≤ sg i) →
    (∑ i, lam i - ∑ i, sg i ≤ lam 0) ∧ (lam (Fin.last n) ≤ ∑ i, lam i - ∑ i, sg i) ∧
    (∀ (h : 0 < n) (W : ℤ), sg ⟨0, h⟩ ≤ W → -W ≤ lam (Fin.last n) →
      lam 0 - 2 * W ≤ ∑ i, lam i - ∑ i, sg i)
def Uc {F : Type} [Field F] {n : ℕ} (fL : (Fin n → F) →ₗ[F] F) (e : Fin n → F) (c : F) :
    Submodule F ((Fin n → F) × F) :=
  (LinearMap.ker fL).map (LinearMap.inl F (Fin n → F) F) ⊔ Submodule.span F {((-c) • e, (1 : F))}
noncomputable def fjCount {F : Type} [Field F] {n g : ℕ} (fL : (Fin n → F) →ₗ[F] F)
    (e : Fin n → F) (x' : ((Fin n → F) × F) →ₗ[F] (Fin (n + g) → F)) (c : F) : ℕ :=
  Nat.card {fW : Fin (n + g) → F // (∀ l ∈ LinearMap.ker fL, fW ⬝ᵥ x' (l, 0) = 0) ∧
    fW ⬝ᵥ x' (e, 0) = 1 ∧ fW ⬝ᵥ x' (0, 1) = c}
def KernelDimensionCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n g : ℕ), 1 ≤ g →
    ∀ (fL : (Fin n → F) →ₗ[F] F) (e : Fin n → F), fL e = 1 →
    ∀ (x' : ((Fin n → F) × F) →ₗ[F] (Fin (n + g) → F)) (c : F),
      (fjCount fL e x' c : ℤ) * ((Fintype.card F : ℤ) - 1) =
        (Fintype.card F : ℤ) ^ (g + Module.finrank F (Uc fL e c ⊓ LinearMap.ker x' :
          Submodule F ((Fin n → F) × F))) -
        (Fintype.card F : ℤ) ^ (g - 1 + Module.finrank F (LinearMap.ker x'))
def CharacterSumCancellation : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n g : ℕ), 1 ≤ g →
    ∀ (fL : (Fin n → F) →ₗ[F] F) (e : Fin n → F), fL e = 1 →
    ∀ (x' : ((Fin n → F) × F) →ₗ[F] (Fin (n + g) → F)) (ψ : AddChar F ℂ), ψ ≠ 1 →
      ∑ c : F, ψ c * (fjCount fL e x' c : ℂ) =
        (Fintype.card F : ℂ) ^ g * ∑ e' : Fin n → F, ψ (fL e') * (if x' (-e', 1) = 0 then 1 else 0)
def PrimitiveOrbitFunctionalUnique : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (f g e : Fin n → F), f ⬝ᵥ e = 1 →
    (((∀ l, f ⬝ᵥ l = 0 → g ⬝ᵥ l = 0) ∧ g ⬝ᵥ e = 1) ↔ g = f)
def FourierCommutesHeckeScalar : Prop :=
  ∀ (R : Type) [CommRing R] (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] (U D G : Module.End R M) (U' D' G' : Module.End R M') (K : M →ₗ[R] M')
    (c a a' : R),
    U' ∘ₗ K = c • (K ∘ₗ U) → D' ∘ₗ U' = a' • LinearMap.id → U ∘ₗ D = a • LinearMap.id →
    K ∘ₗ G = G' ∘ₗ K →
    a' • (K ∘ₗ D ∘ₗ G) = (c * a) • (D' ∘ₗ G' ∘ₗ K)
def FourierTransformKernelSurjective : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ ψv : (Fin r → k) → ℂ, (∀ x, x ≠ 0 → Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmV ψv x = 0) →
      ∃ φ : (Fin r → k) → ℂ, (∀ f, f ≠ 0 → Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP φ f = 0) ∧
        ∀ x, x ≠ 0 → Formalism.LogVandermondeBounds.product_first_zeroth_parts.opFF ψ φ x = ψv x
def QuotientLengthEmbeddingBound : Prop :=
  ∀ (R : Type) [Ring R] (M : Type) [AddCommGroup M] [Module R M] (A N : Submodule R M),
    Module.length R (A ⧸ N.comap A.subtype) ≤ Module.length R (M ⧸ N)
def Joint_coef : Prop :=
  ∀ (ι : Type) (TT : Finset ι) (a W : ι → ℝ)
    (L k m f q e logP muM0 muRam muN EP E0 Eprice : ℝ),
    0 < L → 2 ≤ k → 0 ≤ m → 0 ≤ f → 0 < q → (∀ τ ∈ TT, 0 ≤ a τ ∧ 4 * a τ < q) →
    (∀ τ ∈ TT, 0 ≤ W τ) →
    logP ≤ -(∑ τ ∈ TT, a τ) * L + EP →
    -muM0 ≤ (∑ τ ∈ TT, a τ) / k * L + E0 →
    muM0 - muRam ≤ f →
    muRam - muN + 2 * e * L ≤
      (∑ τ ∈ TT, m * (a τ / k + 3 * W τ + k) * (1 + 2 * f / q)) * L + Eprice →
    logP - muN + 2 * e * L ≤
      -(1 - (m + 1) / k) * (∑ τ ∈ TT, a τ) * L +
        (∑ τ ∈ TT, (m * (3 * W τ + k) * (1 + 2 * f / q) + m * f / (2 * k))) * L +
        (EP + E0 + f + Eprice)
end Formalism.HermitianLattices.LocalLatticeBases


