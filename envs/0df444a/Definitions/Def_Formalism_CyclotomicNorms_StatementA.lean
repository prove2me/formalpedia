-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_StatementA
-- name    : Formalism_CyclotomicNorms_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:09:36.870283+00:00
-- url     : https://prove2.me/theorems/92fa68a8-f729-4961-8217-d914cf31f6a2
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/StatementA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
namespace Formalism.CyclotomicNorms
abbrev wt (x : ℝ) : WithTop ℝ := (x : WithTop ℝ)
def Newton : Prop :=
  ∀ (L : Type) [Field L] (v : AddValuation L (WithTop ℝ)) (ℓ e : ℕ) (f : L[X]) (c : ℝ),
    ℓ.Prime → 0 < e → v (ℓ : L) = wt 1 →
    (∀ i, v (f.coeff i) = ⊤ ∨ ∃ n : ℕ, v (f.coeff i) = wt ((n : ℝ) / e)) →
    v (f.coeff 0) = wt c →
    ∃ X : Finset ℕ, (X.card : ℝ) ≤ e * c ∧
      ∀ j : ℕ, 1 ≤ j → j ∉ X → ∀ z : L, IsPrimitiveRoot z (ℓ ^ j) →
        v (f.eval (z - 1)) ≤ wt c
def GTPigeonhole : Prop :=
  ∀ (a : ℕ → ℝ) (V ε K₁ : ℝ) (X B : Finset ℕ) (k₀ N : ℕ),
    0 < ε → 1 ≤ k₀ → (∀ k, 0 ≤ a k) → B.card ≤ N → (∀ S : Finset ℕ, ∑ k ∈ S, a k ≤ V) →
    K₁ = (k₀ + X.card + N + 1) * Real.exp (2 * V / ε) + 1 →
    ∃ k : ℕ, k₀ ≤ k ∧ (k : ℝ) ≤ K₁ ∧ k ∉ X ∧ k ∉ B ∧ (k : ℝ) * a k ≤ ε / 2
def Substitution : Prop :=
  ∀ (k : Type) [CommRing k] (ℓ r s E : ℕ) (F : Fin s → MvPowerSeries (Fin r) k),
    2 ≤ ℓ → (∀ i, F i ≠ 0) →
    ∃ e : Fin r → ℕ, StrictMono e ∧ (∀ j, E ≤ e j) ∧
      ∀ i, (MvPowerSeries.subst (fun j => (PowerSeries.X : PowerSeries k) ^ (ℓ ^ e j)) (F i) :
        PowerSeries k) ≠ 0
def Evaluation : Prop :=
  ∀ (L : Type) [Field L] (v : AddValuation L (WithTop ℝ)) (ℓ e w j : ℕ) (F : L[X]) (z : L),
    ℓ.Prime → 0 < e → v (ℓ : L) = wt 1 →
    (∀ i, v (F.coeff i) = wt 0 ∨ wt (1 / e) ≤ v (F.coeff i)) →
    (∃ i ≤ w, v (F.coeff i) = wt 0) →
    IsPrimitiveRoot z (ℓ ^ j) → ((e * w : ℕ) : ℝ) < ((ℓ ^ j).totient : ℝ) →
    v (F.eval (z - 1)) ≤ wt ((w : ℝ) / ((ℓ ^ j).totient : ℝ))
abbrev TruncRing (O : Type) [CommRing O] (π : O) (n M : ℕ) : Type :=
  (O ⧸ Ideal.span {π ^ n})[X] ⧸ Ideal.span {(X : (O ⧸ Ideal.span {π ^ n})[X]) ^ (M + 1)}
abbrev truncMk (O : Type) [CommRing O] (π : O) (n M : ℕ) :
    (O ⧸ Ideal.span {π ^ n})[X] →+* TruncRing O π n M :=
  Ideal.Quotient.mk _
def Product : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O) (n m m₀ M : ℕ),
    Irreducible π → 1 ≤ n → m ≤ m₀ → n * m₀ ≤ M →
    ∀ (U : (TruncRing O π n M)ˣ) (D' : TruncRing O π n M) (g : (O ⧸ Ideal.span {π ^ n})[X]),
      g.coeff 0 ≠ 0 →
      (truncMk O π n M (X ^ m) * (U : TruncRing O π n M) +
          truncMk O π n M (C (Ideal.Quotient.mk _ π)) * D') * truncMk O π n M g ≠ 0
def genericGram {k La La' : Type} [Field k] [AddCommGroup La] [Module k La] [AddCommGroup La']
    [Module k La'] {R d : ℕ} (B : Fin R → La →ₗ[k] La' →ₗ[k] k) {S : Submodule k La}
    {S' : Submodule k La'} (b : Module.Basis (Fin d) k S) (b' : Module.Basis (Fin d) k S') :
    Matrix (Fin d) (Fin d) (MvPolynomial (Fin R) k) :=
  Matrix.of fun p q => ∑ i, MvPolynomial.X i * MvPolynomial.C (B i (b p) (b' q))
def GenericPairing : Prop :=
  ∀ (k La La' : Type) [Field k] [AddCommGroup La] [Module k La] [FiniteDimensional k La]
    [AddCommGroup La'] [Module k La'] [FiniteDimensional k La'] (R d : ℕ)
    (B : Fin R → La →ₗ[k] La' →ₗ[k] k), Submodule.span k (Set.range B) = ⊤ →
    ∀ (S : Submodule k La) (S' : Submodule k La') (b : Module.Basis (Fin d) k S)
      (b' : Module.Basis (Fin d) k S'),
      ((genericGram B b b').map
        (algebraMap (MvPolynomial (Fin R) k) (FractionRing (MvPolynomial (Fin R) k)))).det ≠ 0
def GenericAltRank : Prop :=
  ∀ (k La : Type) [Field k] [AddCommGroup La] [Module k La] [FiniteDimensional k La] (R d : ℕ)
    (B : Fin R → La →ₗ[k] La →ₗ[k] k), (∀ i x, B i x x = 0) →
    (∀ ω : La →ₗ[k] La →ₗ[k] k, (∀ x, ω x x = 0) → ω ∈ Submodule.span k (Set.range B)) →
    ∀ (S S' : Submodule k La) (b : Module.Basis (Fin d) k S) (b' : Module.Basis (Fin d) k S'),
      d - 1 ≤ ((genericGram B b b').map
        (algebraMap (MvPolynomial (Fin R) k) (FractionRing (MvPolynomial (Fin R) k)))).rank
def evalAt (k : Type) {M W : Type} [CommRing k] [AddMonoid M] [AddCommGroup W] [Module k W]
    (x : M) : (M →+ W) →ₗ[k] W where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def evalImage {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] {H : Subgroup G}
    (La : ∀ i, Submodule k (Additive H →+ W i)) (h : H) : ∀ i, La i →ₗ[k] W i :=
  fun i => (evalAt k (Additive.ofMul h)).comp (La i).subtype
def SpanHyp {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] (ρ : ∀ i, Representation k G (W i))
    (H : Subgroup G) (La : ∀ i, Submodule k (Additive H →+ W i)) : Prop :=
  H.Normal ∧
  (∀ i, FiniteDimensional k (W i) ∧ Nontrivial (W i) ∧
    Submodule.span k (Set.range (ρ i)) = ⊤) ∧
  (∀ i j, i ≠ j → ¬ ∃ T : W i ≃ₗ[k] W j, ∀ g x, T (ρ i g x) = ρ j g (T x)) ∧
  (∀ i, FiniteDimensional k (La i)) ∧
  (∀ i, ∀ lam ∈ La i, ∀ (g : G) (h : H) (hh : g * (h : G) * g⁻¹ ∈ H),
    lam (Additive.ofMul ⟨g * h * g⁻¹, hh⟩) = ρ i g (lam (Additive.ofMul h)))
def SpanImage : Prop :=
  ∀ (G k : Type) [Group G] [Field k] (a : ℕ) (W : Fin a → Type) [∀ i, AddCommGroup (W i)]
    [∀ i, Module k (W i)] (ρ : ∀ i, Representation k G (W i)) (H : Subgroup G)
    (La : ∀ i, Submodule k (Additive H →+ W i)), SpanHyp ρ H La →
    Submodule.span k (Set.range (evalImage La)) = ⊤
def SpanQuad : Prop :=
  ∀ (G k : Type) [Group G] [Field k] (a : ℕ) (W : Fin a → Type) [∀ i, AddCommGroup (W i)]
    [∀ i, Module k (W i)] (ρ : ∀ i, Representation k G (W i)) (H : Subgroup G)
    (La : ∀ i, Submodule k (Additive H →+ W i)) (BB : Type) [AddCommGroup BB] [Module k BB]
    (q : (∀ i, La i →ₗ[k] W i) → BB)
    (b : (∀ i, La i →ₗ[k] W i) →ₗ[k] (∀ i, La i →ₗ[k] W i) →ₗ[k] BB), SpanHyp ρ H La →
    (∀ h h' : H, q (evalImage La (h * h')) - q (evalImage La h) - q (evalImage La h') =
      b (evalImage La h) (evalImage La h')) →
    ∀ x y, b x y ∈ Submodule.span k (Set.range fun h : H => q (evalImage La h))
def coboundary {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W]
    (ρ : Representation R G W) (n : ℕ) (f : (Fin n → G) → W) : (Fin (n + 1) → G) → W :=
  fun g => ρ (g 0) (f fun i => g i.succ) +
    ∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
def CentralScalar : Prop :=
  ∀ (G R W : Type) [Group G] [TopologicalSpace G] [CommRing R] [AddCommGroup W] [Module R W]
    [TopologicalSpace W] [DiscreteTopology W] (ρ : Representation R G W) (z : G) (c : R),
    z ∈ Subgroup.center G → IsUnit (c - 1) → (∀ w, ρ z w = c • w) →
    (∀ w : W, (∀ g, ρ g w = w) → w = 0) ∧
    ∀ (n : ℕ) (f : (Fin (n + 1) → G) → W), Continuous f → coboundary ρ (n + 1) f = 0 →
      ∃ h : (Fin n → G) → W, Continuous h ∧ coboundary ρ n h = f
def Cycles : Prop :=
  ∀ (G k V P : Type) [Group G] [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Fintype P] (ρ : Representation k G V) (N : ℕ) (D I : P → Subgroup G)
    (χ : P → Fin N → G → k) (flag : P → Fin (N + 1) → Submodule k V),
    Module.finrank k V = N →
    (∀ v, I v ≤ D v) → (∀ v, ∀ d ∈ D v, ∀ x ∈ I v, d * x * d⁻¹ ∈ I v) →

    (∀ v (i : Fin (N + 1)), Module.finrank k (flag v i) = i) →
    (∀ v (i : Fin N), flag v i.castSucc ≤ flag v i.succ) →
    (∀ v i, ∀ x ∈ flag v i, ∀ y ∈ I v, ρ y x ∈ flag v i) →

    (∀ v (i : Fin N), ∀ x ∈ flag v i.succ, ∀ y ∈ I v,
      ρ y x - χ v i y • x ∈ flag v i.castSucc) →

    (∀ v (i j : Fin N), i ≠ j → ∃ y ∈ I v, χ v i y ≠ χ v j y) →
    (∀ v (i : Fin N), ∀ d ∈ D v, ∃ j : Fin N, ∀ y ∈ I v, χ v j y = χ v i (d⁻¹ * y * d)) →

    (∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ S : Finset (Fin N), S.card = a ∧
      ∀ i ∈ S, ∀ d ∈ D v, ∃ j ∈ S, ∀ y ∈ I v, χ v j y = χ v i (d⁻¹ * y * d)) →
    ∀ W : Submodule k V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤
def CentralTwoStep : Prop :=
  ∀ (H G : Type) [Group H] [CommGroup G] [Finite G] (π : H →* G), Function.Surjective π →
    IsPGroup 2 G → Nat.card π.ker = 2 → π.ker ≤ Subgroup.center H →
    ∀ D : Subgroup H, D.map π = ⊤ →
    (Function.Injective (π.comp D.subtype) ∨ (D = ⊤ ∧ ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)) →
    ∀ x y : H, x * y = y * x
def ElemAbelianRank : Prop :=
  ∀ (P : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    (X : Subgroup P) (a b c d : P),
    X = (commutator P).topologicalClosure →
    (Subgroup.closure ({a, b, c, d} : Set P)).topologicalClosure = ⊤ → a * b = b * a →
    X ≤ Subgroup.center P → (∀ x ∈ X, x ^ 2 = 1) →
    Finite X ∧ Nat.card X ≤ 2 ^ 5
def LengthBound : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Type) [CommRing R] [Algebra ℤ_[ℓ] R] [Module.Free ℤ_[ℓ] R]
    [Module.Finite ℤ_[ℓ] R] (y : R) (g : ℕ) (Y : Type) [AddCommGroup Y] [Module ℤ_[ℓ] Y],
    LinearMap.det (LinearMap.mulLeft ℤ_[ℓ] y) ≠ 0 →
    ∀ q : (Fin g → R ⧸ Ideal.span {y}) →ₗ[ℤ_[ℓ]] Y, Function.Surjective q →
      Module.length ℤ_[ℓ] Y ≤
        ((g * (LinearMap.det (LinearMap.mulLeft ℤ_[ℓ] y)).valuation : ℕ) : ℕ∞)
end Formalism.CyclotomicNorms


