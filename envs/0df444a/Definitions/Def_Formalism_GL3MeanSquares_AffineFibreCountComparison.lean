-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
-- name    : Formalism_GL3MeanSquares_AffineFibreCountComparison
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:18.662964+00:00
-- url     : https://prove2.me/theorems/d3dc790d-948f-4141-912b-d34c809b7dda
-- title:
--   Affine Fibre Count Comparison
-- statement:
--   Definitions and structural lemmas for Affine Fibre Count Comparison, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/AffineFibreCountComparison.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Finset Matrix ComplexConjugate
def AffineHyperplaneTermCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (r : ℕ) (f : Fin r → F), f ≠ 0 →
    (univ.filter (fun x : Fin r → F => Formalism.LogVandermondeBounds.product_first_zeroth_parts.pair f x = 1)).card * Fintype.card F =
      Fintype.card F ^ r ∧
    (univ.filter (fun g : Fin r → F => Formalism.LogVandermondeBounds.product_first_zeroth_parts.pair g f = 1)).card * Fintype.card F =
      Fintype.card F ^ r
def TraceOperatorIdentityAllRanks : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (r : ℕ) (R : Type) [CommRing R], 1 ≤ r →
    (∀ (ψ : (Fin r → F) → R) (x : Fin r → F), x ≠ 0 →
      (Fintype.card F : R) * Formalism.LogVandermondeBounds.product_first_zeroth_parts.opD (Formalism.LogVandermondeBounds.product_first_zeroth_parts.opU ψ) x =
        (Fintype.card F : R) ^ r * ψ x - (Fintype.card F : R) ^ (r - 1) * Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmV ψ x
          + (Fintype.card F : R) ^ (r - 1) * Formalism.LogVandermondeBounds.product_first_zeroth_parts.trV ψ) ∧
    (∀ (φ : (Fin r → F) → R) (f : Fin r → F), f ≠ 0 →
      (Fintype.card F : R) * Formalism.LogVandermondeBounds.product_first_zeroth_parts.opU (Formalism.LogVandermondeBounds.product_first_zeroth_parts.opD φ) f =
        (Fintype.card F : R) ^ r * φ f - (Fintype.card F : R) ^ (r - 1) * Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP φ f
          + (Fintype.card F : R) ^ (r - 1) * Formalism.LogVandermondeBounds.product_first_zeroth_parts.trP φ)
def Fubini_orbits : Prop :=
  ∀ (Γ P Q V : Type) [Group Γ] [MulAction Γ P] [MulAction Γ Q] [AddCommGroup V] [Module ℚ V]
    (pr : P → Q) (fib : Q → Finset P) (Ψ : P → V) (RP : Finset P) (RQ : Finset Q),
    (∀ (γ : Γ) (p : P), pr (γ • p) = γ • pr p) → (∀ p y, p ∈ fib y ↔ pr p = y) →
    (∀ (γ : Γ) (p : P), Ψ (γ • p) = Ψ p) →
    (∀ y : Q, Finite (MulAction.stabilizer Γ y)) →
    (∀ p : P, ∃! r, r ∈ RP ∧ r ∈ MulAction.orbit Γ p) →
    (∀ y : Q, ∃! r, r ∈ RQ ∧ r ∈ MulAction.orbit Γ y) →
    ∑ p ∈ RP, ((Nat.card (MulAction.stabilizer Γ p) : ℚ))⁻¹ • Ψ p =
      ∑ y ∈ RQ, ((Nat.card (MulAction.stabilizer Γ y) : ℚ))⁻¹ • ∑ p ∈ fib y, Ψ p
def Count_orbits : Prop :=
  ∀ (Γ A B V : Type) [Group Γ] [MulAction Γ A] [MulAction Γ B] [AddCommGroup V] [Module ℚ V]
    (up : A → Finset B) (down : B → Finset A) (G : A → B → V) (RA : Finset A) (RB : Finset B),
    (∀ a b, b ∈ up a ↔ a ∈ down b) → (∀ (γ : Γ) a b, b ∈ up a → γ • b ∈ up (γ • a)) →
    (∀ (γ : Γ) a b, b ∈ up a → G (γ • a) (γ • b) = G a b) →
    (∀ a : A, Finite (MulAction.stabilizer Γ a)) → (∀ b : B, Finite (MulAction.stabilizer Γ b)) →
    (∀ a : A, ∃! r, r ∈ RA ∧ r ∈ MulAction.orbit Γ a) →
    (∀ b : B, ∃! r, r ∈ RB ∧ r ∈ MulAction.orbit Γ b) →
    ∑ a ∈ RA, ((Nat.card (MulAction.stabilizer Γ a) : ℚ))⁻¹ • ∑ b ∈ up a, G a b =
      ∑ b ∈ RB, ((Nat.card (MulAction.stabilizer Γ b) : ℚ))⁻¹ • ∑ a ∈ down b, G a b
def PowerCountAndLogSlopeIdentity : Prop :=
  (∀ f n : ℕ, f * n ^ (f - 1) * n + n ^ f = (f + 1) * n ^ f) ∧
  (∀ (q f : ℕ) (lcv w : ℝ), 3 ≤ q → 1 ≤ f → 0 < w →
    -(((q : ℝ) - 2) ^ f * lcv + f * ((q : ℝ) - 2) ^ (f - 1) * Real.log ((q : ℝ) - 1) * w) /
        (((q : ℝ) - 2) ^ f * w) =
      -(((q : ℝ) - 1) ^ f * lcv) / (((q : ℝ) - 1) ^ f * w) -
        f * Real.log ((q : ℝ) - 1) / ((q : ℝ) - 2))
def LemmaB'_length : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (ι : Type) [Fintype ι] (deg : ι → ℕ),
      Module.length R ((ι → R) ⧸
        (Submodule.pi Set.univ (fun i => Ideal.span {ϖ ^ deg i}) : Submodule R (ι → R))) =
        ((∑ i, deg i : ℕ) : ℕ∞)
def LemmaC_sharp : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (M : Type) [AddCommGroup M] [Module R M] (P S B : Submodule R M) (U D : M →ₗ[R] M) (e b : ℕ),
      S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B → B.map U ≤ S → S.map D ≤ B →
      P.map U ≤ P → P.map D ≤ P → (∀ x : M, ϖ • x ∈ P → x ∈ P) →
      (∀ s ∈ S ⊓ P, U (D s) = ϖ ^ e • s) → Module.Free R S → Module.Finite R S →
      Module.length R ((S ⊓ P : Submodule R M) ⧸ ((S ⊓ P).map ((ϖ ^ b) • U)).comap (S ⊓ P).subtype) ≤
        Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) +
          (e * Module.finrank R (S ⊓ P : Submodule R M) : ℕ)
def UnitaryDeterminantModulus : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (c : ℝ),
    Uᴴ * U = (c : ℂ) • (1 : Matrix n n ℂ) → ‖U.det‖ ^ 2 = c ^ Fintype.card n
def Index_det : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (u : Matrix n n R), u.det ≠ 0 →
      Module.length R ((n → R) ⧸ LinearMap.range u.mulVecLin) = emultiplicity ϖ u.det
def DualHomLatticePairing : Prop :=
  ∀ (q n n' : ℕ) (fW : Fin n' → ZMod q) (B : Matrix (Fin n) (Fin n') ℚ),
    (∀ A : Matrix (Fin n') (Fin n) ℤ, Formalism.HermitianLattices.LocalLatticeBases.compF fW A = 0 →
      (B * A.map (Int.cast : ℤ → ℚ)).trace ∈ Set.range (Int.cast : ℤ → ℚ)) ↔
    (∀ μ : Fin n' → ℤ, (∑ i, fW i * (μ i : ZMod q)) = 0 →
      ∀ j, (B.mulVec (fun i => (μ i : ℚ))) j ∈ Set.range (Int.cast : ℤ → ℚ))
def CayleyTransformHermitian : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n], (2 : K) ≠ 0 →
    (∀ A : Matrix n n K, Aᴴ = -A → IsUnit (1 + A) →
      ((1 - A) * (1 + A)⁻¹)ᴴ * ((1 - A) * (1 + A)⁻¹) = 1 ∧ IsUnit (1 + (1 - A) * (1 + A)⁻¹) ∧
      (1 - (1 - A) * (1 + A)⁻¹) * (1 + (1 - A) * (1 + A)⁻¹)⁻¹ = A) ∧
    (∀ g : Matrix n n K, gᴴ * g = 1 → IsUnit (1 + g) →
      ((1 - g) * (1 + g)⁻¹)ᴴ = -((1 - g) * (1 + g)⁻¹) ∧ IsUnit (1 + (1 - g) * (1 + g)⁻¹) ∧
      (1 - (1 - g) * (1 + g)⁻¹) * (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = g)
def PiecewiseExponentSumBound : Prop :=
  ∀ (ι : Type) (Ψ : Finset ι) (top : ι → Prop) [DecidablePred top] (s nu W : ι → ℝ) (f nl : ℝ),
    (∀ τ ∈ Ψ, |s τ| ≤ W τ) → (∀ τ ∈ Ψ, ¬ top τ → nu τ ≤ 2 * W τ) →
    (f * nl - (∑ τ ∈ Ψ, s τ) + (∑ τ ∈ Ψ, if top τ then 0 else s τ - nu τ) =
      -(-(f * nl) + ∑ τ ∈ Ψ, if top τ then s τ else nu τ)) ∧
    (-(f * nl) + (∑ τ ∈ Ψ, if top τ then s τ else nu τ) ≤ -(f * nl) + 2 * ∑ τ ∈ Ψ, W τ)
def AffineFibreCountComparison : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n g : ℕ) (xb : (Fin n → F) →ₗ[F] (Fin (n + g) → F))
    (f : Fin n → F) (uW : Fin (n + g) → F),
    let rk := Module.finrank F (LinearMap.range xb)
    let A : ℤ := Nat.card {fW : Fin (n + g) → F // fW ⬝ᵥ uW = 1 ∧ ∀ l, fW ⬝ᵥ xb l = f ⬝ᵥ l}
    let B : ℤ := Nat.card {u : Fin n → F // f ⬝ᵥ u = 1 ∧ xb u = uW}
    let fker : Prop := ∀ l ∈ LinearMap.ker xb, f ⬝ᵥ l = 0
    (uW ∉ LinearMap.range xb → fker →
      A - (Fintype.card F : ℤ) ^ g * B = (Fintype.card F : ℤ) ^ (n + g - rk - 1)) ∧
    (uW ∈ LinearMap.range xb → ¬ fker →
      A - (Fintype.card F : ℤ) ^ g * B = -(Fintype.card F : ℤ) ^ (n + g - rk - 1)) ∧
    (uW ∈ LinearMap.range xb → fker → A - (Fintype.card F : ℤ) ^ g * B = 0) ∧
    (uW ∉ LinearMap.range xb → ¬ fker → A - (Fintype.card F : ℤ) ^ g * B = 0)
def InvariantKernelTraceVanishes : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (r : ℕ) (R : Type) [CommRing R]
    (k φ : (Fin r → F) → R),
    (∀ (c : Fˣ) (f : Fin r → F), k ((c : F) • f) = k f) →
    (∀ f, f ≠ 0 → Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP φ f = 0) →
    ∑ f ∈ univ.filter (fun f : Fin r → F => f ≠ 0), k f * φ f = 0
def HeckeSubmoduleInclusion : Prop :=
  ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (P S B : Submodule R M)
    (U : Module.End R M) (ϖ : R) (b m : ℕ),
    S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B → B.map U ≤ S → P.map U ≤ P →
    (S ⊓ P).map (((ϖ ^ b) • U) ^ m) ≤ S ⊓ P
def HeckeProductCommutationGeneral : Prop :=
  ∀ (R : Type) [CommRing R] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (U : ∀ j, Module.End R (M j)) (K : ∀ j, M j →ₗ[R] M (j + 1)) (c : ℕ → Rˣ),
    (∀ j, (U (j + 1)).comp (K j) = (c j : R) • (K j).comp (U j)) →
    ∀ n i : ℕ, i ≤ n → (Formalism.HermitianLattices.LocalLatticeBases.chainK R M K i).comp ((U 0) ^ n) =
      ((∏ j ∈ range i, (c j)⁻¹ ^ (n - j) : Rˣ) : R) •
        ((U i) ^ (n - i)).comp (Formalism.HermitianLattices.LocalLatticeBases.chainUK R M U K i)
def ConsecutiveRatioPowerSharpBound : Prop :=
  ∀ q f : ℕ, 1 ≤ f → 2 * f + 4 ≤ q → (1 + 1 / ((q : ℝ) - 2)) ^ f ≤ 1 + 2 * (f : ℝ) / q
def ExponentCostPerPlaceBound : Prop :=
  ∀ (Λ ι : Type) [DecidableEq Λ] (Pl Pi : Finset Λ) (wt idx : Λ → ℝ) (TT : Finset ι) (a W : ι → ℝ)
    (m k d dram f q L : ℝ),
    Pi ⊆ Pl → (∀ l ∈ Pl, 0 ≤ wt l) → ∑ l ∈ Pi, wt l = L → (∀ l ∈ Pl \ Pi, idx l = 0) →
    (∀ l ∈ Pi, idx l ≤ m * d * ∑ t ∈ TT, (a t / k + 2 * W t + k - 1)) →
    0 ≤ m → 1 ≤ k → 0 ≤ d → 0 < dram → (∀ t ∈ TT, 0 ≤ a t ∧ 0 ≤ W t) → d / dram ≤ 1 + 2 * f / q →
    (1 / dram) * ∑ l ∈ Pl, wt l * idx l ≤
      m * (∑ t ∈ TT, (a t / k + 2 * W t + k - 1)) * (1 + 2 * f / q) * L
def ExponentCostTotalBound : Prop :=
  ∀ (ι : Type) (Ψ TT : Finset ι) (a W : ι → ℝ) (amax bp m t f N k q C3 C4 e1 L : ℝ),
    TT ⊆ Ψ → (∀ τ ∈ Ψ, 0 ≤ W τ) → (∀ τ ∈ TT, a τ ≤ amax ∧ W τ ≤ 2 * bp) →
    1 ≤ m → 0 ≤ t → t + 1 ≤ N → 0 ≤ f → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ L → 1 ≤ k → 0 < q →
    e1 ≤ 4 * (∑ τ ∈ Ψ, W τ) + C3 * f * N →
    m * (∑ τ ∈ TT, (a τ / k + 2 * W τ + k - 1)) * (1 + 2 * f / q) * L +
        (2 * m * e1 + m * (m + 1) / 2 * ∑ τ ∈ TT, (t + 1 + 2 * W τ + C4 * N)) * L ≤
      (∑ τ ∈ TT, m * (amax / k + 3 * W τ + k) * (1 + 2 * f / q)) * L +
        max (max 8 (2 * C3)) (max 4 (1 + C4)) * m *
          ((∑ τ ∈ Ψ, W τ) + f * m * N + TT.card * m * (bp + N)) * L
def TriangularSumExponentBound : Prop :=
  ∀ (m : ℕ) (e1 SW f N t VV : ℝ), e1 ≤ 2 * SW + f * N →
    (∑ j ∈ range m, ((m : ℝ) - j) * (VV * (t + 1) / 2) = VV * (t + 1) * m * (m + 1) / 4) ∧
    ((m : ℝ) * e1 + ∑ j ∈ range m, ((m : ℝ) - j) * (VV * (t + 1) / 2) ≤
      m * (2 * SW + f * N) + VV * (t + 1) * m * (m + 1) / 4)
def ExponentLogProductBound : Prop :=
  ∀ (ι : Type) (Ψ TT : Finset ι) (W : ι → ℝ) (f N t m b C L logT : ℝ),
    TT ⊆ Ψ → (Ψ.card : ℝ) = f → (∀ τ ∈ Ψ, 0 ≤ W τ ∧ W τ ≤ 2 * b) → 0 ≤ N → N ≤ b → 1 ≤ t → 1 ≤ m →
    t * m ≤ b → 0 ≤ logT → logT ≤ C * m * L →
    let E : ℝ := 2 * (∑ τ ∈ Ψ, W τ) + f * N + TT.card * (t + 1) * (m + 1) / 4
    m * E = m * (2 * (∑ τ ∈ Ψ, W τ) + f * N) + TT.card * (t + 1) * m * (m + 1) / 4 ∧
    0 ≤ E * logT ∧ E * logT ≤ 6 * C * f * b * (m * L)
def DeterminantTwistExponentShift : Prop :=
  ∀ (ι : Type) (Ψ : Finset ι) (m : ℕ) (e : ℕ → ι → ℝ) (k t L : ℝ),
    let Nn : ℕ → ℝ := fun j => k + j * (t + 1)
    let s : ℕ → ι → ℝ := fun j τ => e j τ - Nn j / 2
    let s' : ℕ → ι → ℝ := fun j τ => e j τ - Nn (j + 1) / 2
    (∀ j τ, s j τ - s' j τ = (t + 1) / 2) ∧
    (L * (∑ j ∈ range m, ∑ τ ∈ Ψ, s j τ) + L * (∑ j ∈ range m, ∑ τ ∈ Ψ, (s' j τ - s j τ)) =
      L * (∑ j ∈ range m, ∑ τ ∈ Ψ, s j τ) - L * m * Ψ.card * (t + 1) / 2)
def HermitianLengthEquation : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cc : E →+* E),
    (∀ (σ : E →+* ℂ) (x : E), σ (cc x) = conj (σ x)) →
    ∀ (α b : E) (T : ℕ), 1 < T → IsIntegral ℤ α → IsIntegral ℤ b →
      (∀ σ : E →+* ℂ, ∃ r : ℝ, 0 ≤ r ∧ σ α = r) → (T : E) * α + b * cc b = 1 →
      α = 0 ∧ ∃ n : ℕ, 0 < n ∧ b ^ n = 1
def RootOfUnityCongruenceOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (P : Ideal (NumberField.RingOfIntegers K)) (T n : ℕ)
    (b : NumberField.RingOfIntegers K),
    T.Prime → P.IsPrime → (T : NumberField.RingOfIntegers K) ∈ P → 0 < n → b ^ n = 1 →
    b - 1 ∈ P → b ≠ 1 → T - 1 ≤ Module.finrank ℚ K
def InterlacingDegreeSharp : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 2) → ℤ) (sg : Fin (n + 1) → ℤ),
    (∀ i : Fin (n + 1), sg i ≤ lam i.castSucc ∧ lam i.succ ≤ sg i) →
    let nt : ℤ := (∑ i, lam i) - ∑ i, sg i
    let D0 : ℤ := ∑ i : Fin (n + 1), (sg i - lam i.succ)
    lam 0 - sg 0 + lam (Fin.last (n + 1)) ≤ nt ∧ nt ≤ lam 0 - sg 0 + lam 1 ∧ nt = lam 0 - D0 ∧
    0 ≤ D0 ∧ D0 ≤ sg 0 - lam (Fin.last (n + 1)) ∧
    (∀ W : ℤ, |sg 0| ≤ W → |lam 1| ≤ W → |lam (Fin.last (n + 1))| ≤ W →
      |nt - lam 0| ≤ 2 * W ∧
      (∀ a m t : ℤ, 0 ≤ m → 0 ≤ t + 1 → 2 * lam 0 = 2 * a - m * (t + 1) →
        2 * |nt - a| ≤ 4 * W + m * (t + 1)) ∧
      (|lam 0| ≤ W → |nt| ≤ 3 * W))
def EvaluationNormExponent : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) (w : ℤ) (T : ℝ), 0 < T →
    ((∑ i, (lam i + w)) - ∑ i, (sg i + w) = (∑ i, lam i) - (∑ i, sg i) + w) ∧
    T ^ w * T ^ (-((∑ i, (lam i + w)) - ∑ i, (sg i + w))) = T ^ (-((∑ i, lam i) - ∑ i, sg i))
def NormFormsInjectiveClasses : Prop :=
  ∀ (ClH ClG V V' : Type) [Fintype ClH] [Fintype ClG] [NormedAddCommGroup V]
    [NormedAddCommGroup V'] (io : ClH → ClG) (wH : ClH → ℝ) (wG : ClG → ℝ) (P : V → V') (C : ℝ)
    (φ : ClG → V),
    Function.Injective io → (∀ h, wH h = wG (io h)) → (∀ g, 0 ≤ wG g) → 0 ≤ C →
    (∀ v, ‖P v‖ ^ 2 ≤ C * ‖v‖ ^ 2) →
    ∑ h, wH h * ‖P (φ (io h))‖ ^ 2 ≤ C * ∑ g, wG g * ‖φ g‖ ^ 2
def IntegralPairingCosetCriterion : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n : ℕ) (f : Fin n → ZMod q) (e : Fin n → ℤ) (xz : Fin n → ℚ),
    (∑ j, f j * (e j : ZMod q)) = 1 →
    (((∀ l : Fin n → ℤ, (∑ j, f j * (l j : ZMod q)) = 0 →
        (∑ j, xz j * l j) ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
      (∃ z : ℤ, (q : ℚ) * ∑ j, xz j * e j = z ∧ (z : ZMod q) = 1)) ↔
    (∀ j, ∃ z : ℤ, (q : ℚ) * xz j = z ∧ (z : ZMod q) = f j))
def VacuumTensorDecomposition : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n n' : ℕ) (f : Fin n → ZMod q) (e : Fin n → ℤ)
    (x' : Matrix (Fin n') (Fin n) ℚ) (xz : Fin n → ℚ),
    (∑ j, f j * (e j : ZMod q)) = 1 →
    let x : Matrix (Fin (n' + 1)) (Fin n) ℚ := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => ℚ) ((q : ℚ) * xz j) (fun i' => x' i' j) i
    (((∀ i j, x i j ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
      (∀ j, ∃ z : ℤ, x (Fin.last n') j = z ∧ (z : ZMod q) = f j)) ↔
    ((∀ i j, x' i j ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
      (∀ l : Fin n → ℤ, (∑ j, f j * (l j : ZMod q)) = 0 →
        (∑ j, xz j * l j) ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
      (∃ z : ℤ, (q : ℚ) * ∑ j, xz j * e j = z ∧ (z : ZMod q) = 1)))
def Gl (q n : ℕ) (f : Fin n → ZMod q) (ε : ℤ) : Set ((Fin n → ℚ) × ℚ) :=
  {p | ∃ (w : Fin n → ℤ) (k : ℤ), (∀ j, p.1 j = w j) ∧ (q : ℚ) * p.2 = k ∧
    (k : ZMod q) = (ε : ZMod q) * ∑ j, f j * (w j : ZMod q)}
def OverlatticeUnitSigns : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n : ℕ) (f : Fin n → ZMod q) (e : Fin n → ℤ) (ε : ℤ),
    (∑ j, f j * (e j : ZMod q)) = 1 → (ε = 1 ∨ ε = -1) →
    (∀ p : (Fin n → ℚ) × ℚ, p ∈ Gl q n f ε ↔
      ∃ (l : Fin n → ℤ) (c : ℤ), (∑ j, f j * (l j : ZMod q)) = 0 ∧
        (∀ j, p.1 j = l j + c * e j) ∧ p.2 = c * ε / q) ∧
    ((0 : Fin n → ℚ), (1 : ℚ)) ∈ Gl q n f ε ∧
    (∀ w : Fin n → ℤ, ((fun j => (w j : ℚ)), (0 : ℚ)) ∈ Gl q n f ε ↔
      (∑ j, f j * (w j : ZMod q)) = 0) ∧
    (∀ s : ℚ, ((0 : Fin n → ℚ), s) ∈ Gl q n f ε ↔ s ∈ Set.range (Int.cast : ℤ → ℚ))
def OverlatticeThreeOrbits : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n : ℕ) (La : AddSubgroup ((Fin n → ℚ) × ℚ)),
    ((0 : Fin n → ℚ), (1 : ℚ)) ∈ La → (∀ p ∈ La, ∃ k : ℤ, (q : ℚ) * p.2 = k) →
    let P1 : Prop := ∀ p ∈ La, (p.1, (0 : ℚ)) ∈ La ∧ ∃ k : ℤ, p.2 = k
    let P2 : Prop := ((0 : Fin n → ℚ), ((q : ℚ))⁻¹) ∈ La ∧ ∀ p ∈ La, (p.1, (0 : ℚ)) ∈ La
    let P3 : Prop := ∃! f : (La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ)) →+ ZMod q,
      Function.Surjective f ∧ ∀ p : (Fin n → ℚ) × ℚ, p ∈ La ↔
        ∃ h : p.1 ∈ La.map (AddMonoidHom.fst (Fin n → ℚ) ℚ), ∃ k : ℤ, (q : ℚ) * p.2 = k ∧
          (k : ZMod q) = f ⟨p.1, h⟩
    (P1 ∨ P2 ∨ P3) ∧ ¬ (P1 ∧ P2) ∧ ¬ (P1 ∧ P3) ∧ ¬ (P2 ∧ P3)
def OverlatticeStabilizer : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n : ℕ) (f : Fin n → ZMod q) (ε : ℤ), IsUnit (ε : ZMod q) →
    ∀ k : (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ),
      (∀ p : (Fin n → ℚ) × ℚ, p ∈ Gl q n f ε ↔ (k p.1, p.2) ∈ Gl q n f ε) ↔
      ((∀ w : Fin n → ℚ, (∀ j, w j ∈ Set.range (Int.cast : ℤ → ℚ)) ↔
          (∀ j, k w j ∈ Set.range (Int.cast : ℤ → ℚ))) ∧
        (∀ w w' : Fin n → ℤ, k (fun j => (w j : ℚ)) = (fun j => (w' j : ℚ)) →
          (∑ j, f j * (w' j : ZMod q)) = ∑ j, f j * (w j : ZMod q)))
def PrimitiveVacuumIndicator : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n n' : ℕ) (fW : Fin n' → ZMod q) (ε : ℤ)
    (xW : Matrix (Fin n') (Fin n) ℚ) (xz : Fin n → ℚ),
    let vac : Prop := ∀ l : Fin n → ℤ,
      (xW.mulVec (fun j => (l j : ℚ)), ∑ j, xz j * (l j : ℚ)) ∈ Gl q n' fW ε
    (vac ↔ ∃ X : Matrix (Fin n') (Fin n) ℤ, xW = X.map (Int.cast : ℤ → ℚ) ∧
      ∀ j, ∃ z : ℤ, (q : ℚ) * xz j = z ∧ (z : ZMod q) = (ε : ZMod q) * Formalism.HermitianLattices.LocalLatticeBases.compF fW X j) ∧
    (∀ f : Fin n → ZMod q, (∀ j, ∃ z : ℤ, (q : ℚ) * xz j = z ∧ (z : ZMod q) = f j) →
      (vac ↔ ∃ X : Matrix (Fin n') (Fin n) ℤ, xW = X.map (Int.cast : ℤ → ℚ) ∧
        Formalism.HermitianLattices.LocalLatticeBases.compF (fun i => (ε : ZMod q) * fW i) X = f))
def KernelDimensionCountAllRanks : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n g : ℕ)
    (fL : (Fin n → F) →ₗ[F] F) (e : Fin n → F), fL e = 1 →
    ∀ (x' : ((Fin n → F) × F) →ₗ[F] (Fin (n + g) → F)) (c : F),
      let ka := Module.finrank F (LinearMap.ker x')
      let kc := Module.finrank F (Formalism.HermitianLattices.LocalLatticeBases.Uc fL e c ⊓ LinearMap.ker x' :
        Submodule F ((Fin n → F) × F))
      (ka = kc ∨ ka = kc + 1) ∧
      (kc = ka → Formalism.HermitianLattices.LocalLatticeBases.fjCount fL e x' c * Fintype.card F = Fintype.card F ^ (g + ka)) ∧
      (kc ≠ ka → Formalism.HermitianLattices.LocalLatticeBases.fjCount fL e x' c = 0)
def FourierFactorizationAllFunctions : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (r : ℕ) (ψ : AddChar F ℂ)
    (φ : (Fin r → F) → ℂ) (x : Fin r → F),
    Formalism.LogVandermondeBounds.product_first_zeroth_parts.opFF ψ φ x = Formalism.LogVandermondeBounds.product_first_zeroth_parts.opD (Formalism.LogVandermondeBounds.product_first_zeroth_parts.opGs ψ φ) x +
      ∑ f ∈ univ.filter (fun f : Fin r → F => f ≠ 0 ∧ Formalism.LogVandermondeBounds.product_first_zeroth_parts.pair f x = 0), φ f
def opFFstar {F : Type} [Field F] [Fintype F] [DecidableEq F] {r : ℕ} (ψ : AddChar F ℂ)
    (φ' : (Fin r → F) → ℂ) (f : Fin r → F) : ℂ :=
  ∑ x ∈ univ.filter (fun x : Fin r → F => x ≠ 0), ψ (-(Formalism.LogVandermondeBounds.product_first_zeroth_parts.pair f x)) * φ' x
def FourierAdjointUnitary : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (r : ℕ) (ψ : AddChar F ℂ), ψ ≠ 1 →
    (∀ φ φ' : (Fin r → F) → ℂ,
      ∑ x ∈ univ.filter (fun x : Fin r → F => x ≠ 0), conj (Formalism.LogVandermondeBounds.product_first_zeroth_parts.opFF ψ φ x) * φ' x =
        ∑ f ∈ univ.filter (fun f : Fin r → F => f ≠ 0), conj (φ f) * opFFstar ψ φ' f) ∧
    (∀ (φ : (Fin r → F) → ℂ) (f : Fin r → F), f ≠ 0 →
      opFFstar ψ (Formalism.LogVandermondeBounds.product_first_zeroth_parts.opFF ψ φ) f =
        (Fintype.card F : ℂ) ^ r * φ f - Formalism.LogVandermondeBounds.product_first_zeroth_parts.trP φ) ∧
    (∀ (φ' : (Fin r → F) → ℂ) (x : Fin r → F), x ≠ 0 →
      Formalism.LogVandermondeBounds.product_first_zeroth_parts.opFF ψ (opFFstar ψ φ') x =
        (Fintype.card F : ℂ) ^ r * φ' x - Formalism.LogVandermondeBounds.product_first_zeroth_parts.trV φ')
def FourierLiftCommutation : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n g : ℕ)
    (xb : (Fin n → F) →ₗ[F] (Fin (n + g) → F)) (ψ : AddChar F ℂ), ψ ≠ 1 →
    ∀ (f : Fin n → F) (eW : Fin (n + g) → F), f ≠ 0 → eW ≠ 0 →
      ∑ fW ∈ univ.filter (fun fW : Fin (n + g) → F => fW ≠ 0),
          ψ (fW ⬝ᵥ eW) * (if ∀ l, fW ⬝ᵥ xb l = f ⬝ᵥ l then (1 : ℂ) else 0) =
        (Fintype.card F : ℂ) ^ g * ∑ e' ∈ univ.filter (fun e' : Fin n → F => e' ≠ 0),
          ψ (f ⬝ᵥ e') * (if xb e' = eW then (1 : ℂ) else 0)
def LatticePreservingAutomorphisms : Prop :=
  ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (S : Submodule R M)
    (U D : Module.End R M) (a : R), IsUnit a → S.map U ≤ S → S.map D ≤ S →
    (∀ s ∈ S, U (D s) = a • s) → (∀ s ∈ S, D (U s) = a • s) → S.map U = S ∧ S.map D = S
def Std_isotropic : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (M A : Type) [AddCommGroup M] [Module R M]
    [AddCommGroup A] (e : M →+ M →+ A),
    (∀ (a : R) (x y : M), e (a • x) y = e x (star a • y)) →
    ∀ π : R, IsCoprime π (star π) → ∀ x y : M, π • x = 0 → π • y = 0 → e x y = 0
def Std_perfect : Prop :=
  ∀ (R : Type) [CommRing R] [StarRing R] (M A : Type) [AddCommGroup M] [Module R M]
    [AddCommGroup A] (e : M →+ M →+ A),
    (∀ (a : R) (x y : M), e (a • x) y = e x (star a • y)) →
    ∀ π : R, IsCoprime π (star π) →
      (∀ x : M, (π * star π) • x = 0 → (∀ y : M, (π * star π) • y = 0 → e x y = 0) → x = 0) →
      ∀ x : M, π • x = 0 → (∀ y : M, star π • y = 0 → e x y = 0) → x = 0
end Formalism.HermitianLattices.RamifiedLatticeOperators


