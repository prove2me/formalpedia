-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_SchurOrthogonalityCompact
-- name    : Formalism_PadicSubsetSums_CentralIdempotents_SchurOrthogonalityCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:03.108362+00:00
-- url     : https://prove2.me/theorems/dd06e05b-abf1-4a6c-be1a-c52761e26b65
-- title:
--   Schur Orthogonality Compact
-- statement:
--   Definitions and structural lemmas for Schur Orthogonality Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/SchurOrthogonalityCompact.lean

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial MeasureTheory
open scoped TensorProduct NumberField ComplexConjugate
namespace Formalism.IrreducibleCountingLemmas.Z
def CharGlue : Prop :=
  ∀ (A : Type) [CommGroup A] (H₁ H₂ H₃ : Subgroup A) (χ₁ : H₁ →* Circle) (χ₂ : H₂ →* Circle)
    (χ₃ : H₃ →* Circle),
    (∀ (a : H₁) (u : H₂) (z : H₃), (a : A) * u * z = 1 → χ₁ a * χ₂ u * χ₃ z = 1) →
    ∃ χ : ↥(H₁ ⊔ H₂ ⊔ H₃) →* Circle, ∀ (a : H₁) (u : H₂) (z : H₃)
      (h : (a : A) * u * z ∈ H₁ ⊔ H₂ ⊔ H₃), χ ⟨(a : A) * u * z, h⟩ = χ₁ a * χ₂ u * χ₃ z
def HeckeCharExtends : Prop :=
  ∀ (A : Type) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (U D : Subgroup A)
    (χ : U →* Circle), IsOpen (U : Set A) → Continuous χ → (∀ u : U, (u : A) ∈ D → χ u = 1) →
    ∃ χ' : A →* Circle, Continuous χ' ∧ (∀ u : U, χ' (u : A) = χ u) ∧ ∀ d ∈ D, χ' d = 1
def JumpsDistinct : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℤ), Antitone a → StrictMono fun j : Fin n => (j : ℤ) - a j
def TwistParity : Prop :=
  ∀ (n n₁ d a x : ℤ), Even n → Even (x + (d - 1) - 2 * a - (n - 1)) →
    (Even (d - (n₁ - 1)) → Even (x - (n₁ - 1)) ∧ Even (n₁ - n + d - 1 - 2 * a)) ∧
    (Odd (d - (n₁ - 1)) → Even (x + 1 - (n₁ - 1)) ∧ Odd (n₁ - n + d - 1 - 2 * a)) ∧
    (1 - n₁) + (n₁ - n + d - 1 - 2 * a) = (1 - n) + (d - 1) - 2 * a
def DegreeOneSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ →
    P.inertiaDeg ℤ = 1 → P.ramificationIdx (𝓞 F) = 1 →
    ((P.under (𝓞 F)).primesOver (𝓞 E)).ncard = 2
def CharpolyDense : Prop :=
  ∀ (G : Type) [TopologicalSpace G] (R : Type) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] (n : ℕ) (r r' : G → Matrix (Fin n) (Fin n) R) (D : Set G),
    Continuous r → Continuous r' → Dense D → (∀ g ∈ D, (r g).charpoly = (r' g).charpoly) →
    ∀ g, (r g).charpoly = (r' g).charpoly
def CompactIntegralCharpoly : Prop :=
  ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] (G : Type) [Group G]
    [TopologicalSpace G] [CompactSpace G] (n : ℕ) (r : G →* Matrix (Fin n) (Fin n) K),
    Continuous r → ∀ (g : G) (j : ℕ), ‖(Matrix.charpolyRev (r g)).coeff j‖ ≤ 1
def G2primeJumps : Prop :=
  ∀ (n t c : ℕ) (e y : ℚ),
    ((((n : ℚ) - 1) / 2 - (y - 1 / 2)) - ((e + 1 / 2) + ((n : ℚ) - 1) / 2 - ((t : ℚ) - 1) / 2) =
      ((t : ℚ) - 1) / 2 - (y + e)) ∧
    ((((n : ℚ) - 1) / 2 + (y - 1 / 2)) - (-(e + 1 / 2) + ((n : ℚ) - 1) / 2 - ((t : ℚ) - 1) / 2) =
      ((t : ℚ) - 1) / 2 + (y + e)) ∧
    (((t : ℚ) - 1) / 2 - ((-e + ((t : ℚ) - 1) / 2 - c) + e) = c) ∧
    (((t : ℚ) - 1) / 2 + ((-e + ((t : ℚ) - 1) / 2 - c) + e) = (t : ℚ) - 1 - c) ∧
    (((t : ℚ) - 1) / 2 < e → 0 ≤ y →
      ((t : ℚ) - 1) / 2 - (y + e) < 0 ∧ (t : ℚ) - 1 < ((t : ℚ) - 1) / 2 + (y + e))
def weilGL {F : Type} [NormedField F] (r t : ℕ) (α β : Fˣ →* ℂ)
    (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) F → ℂ) (g : GL (Fin r) F) (h : GL (Fin r ⊕ Fin t) F)
    (x : Matrix (Fin r ⊕ Fin t) (Fin r) F) : ℂ :=
  α (Matrix.GeneralLinearGroup.det g) * β (Matrix.GeneralLinearGroup.det h) *
    ((‖(g : Matrix (Fin r) (Fin r) F).det‖ ^ (((r : ℝ) + t) / 2) *
      ‖(h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).det‖ ^ (-(r : ℝ) / 2) : ℝ) : ℂ) *
    Φ (((h⁻¹ : GL (Fin r ⊕ Fin t) F) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x *
      (g : Matrix (Fin r) (Fin r) F))
def topPoint (F : Type) [Zero F] [One F] (r t : ℕ) : Matrix (Fin r ⊕ Fin t) (Fin r) F :=
  Matrix.fromRows 1 0
def GJEquivariance : Prop :=
  ∀ (F : Type) [NormedField F] (r t : ℕ) [MeasurableSpace (GL (Fin r) F)]
    [MeasurableMul (GL (Fin r) F)] (μ : Measure (GL (Fin r) F)) [μ.IsMulLeftInvariant]
    (α β : Fˣ →* ℂ) (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) F → ℂ) (c : GL (Fin r) F → ℂ)
    (p h : GL (Fin r ⊕ Fin t) F) (a : GL (Fin r) F) (d : GL (Fin t) F)
    (b : Matrix (Fin r) (Fin t) F),
    (p : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) =
      Matrix.fromBlocks (a : Matrix (Fin r) (Fin r) F) b 0 (d : Matrix (Fin t) (Fin t) F) →
    ∫ g, weilGL r t α β Φ g (p * h) (topPoint F r t) * c g ∂μ =
      (α (Matrix.GeneralLinearGroup.det a) * β (Matrix.GeneralLinearGroup.det a) *
          ((‖(a : Matrix (Fin r) (Fin r) F).det‖ ^ ((t : ℝ) / 2) : ℝ) : ℂ)) *
        (β (Matrix.GeneralLinearGroup.det d) *
          ((‖(d : Matrix (Fin t) (Fin t) F).det‖ ^ (-(r : ℝ) / 2) : ℝ) : ℂ)) *
        ∫ g, weilGL r t α β Φ g h (topPoint F r t) * c (a * g) ∂μ
def congrSet {O F : Type} [CommRing O] [Field F] [Algebra O F] (I : Ideal O) {m n : Type}
    (x₀ : Matrix m n F) : Set (Matrix m n F) :=
  {u | ∃ y : Matrix m n O, (∀ i j, y i j ∈ I) ∧ u = x₀ + y.map (algebraMap O F)}
def CongruenceSupport : Prop :=
  ∀ (O F : Type) [CommRing O] [IsLocalRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    (I : Ideal O) (n k : ℕ) (h : GL (Fin n) F), I ≠ ⊤ →
    ((∃ u ∈ congrSet I (topPoint F n k), u * (h : Matrix (Fin n) (Fin n) F) ∈
        congrSet I (topPoint F n k)) ↔
      (h : Matrix (Fin n) (Fin n) F) ∈ congrSet I (1 : Matrix (Fin n) (Fin n) F)) ∧
    ((h : Matrix (Fin n) (Fin n) F) ∈ congrSet I (1 : Matrix (Fin n) (Fin n) F) →
      ∀ u, u ∈ congrSet I (topPoint F n k) ↔
        u * (h : Matrix (Fin n) (Fin n) F) ∈ congrSet I (topPoint F n k))
def locDatum {O : Type} [CommRing O] (r t : ℕ) (I : Ideal O) (J' : Subgroup (GL (Fin r) O))
    (ν : J' →* ℂ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) O) : ℂ :=
  open Classical in
  if h : (∃ k : J', ((k : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) = x.toRows₁) ∧
      ∀ i j, x.toRows₂ i j ∈ I then ν h.1.choose else 0
def LocDatumRight : Prop :=
  ∀ (O : Type) [CommRing O] (r t : ℕ) (I : Ideal O) (J' : Subgroup (GL (Fin r) O)) (ν : J' →* ℂ)
    (g : GL (Fin r) O) (x : Matrix (Fin r ⊕ Fin t) (Fin r) O),
    (∀ hg : g ∈ J', locDatum r t I J' ν (x * (g : Matrix (Fin r) (Fin r) O)) =
      ν ⟨g, hg⟩ * locDatum r t I J' ν x) ∧
    (g ∉ J' → locDatum r t I J' ν (x * (g : Matrix (Fin r) (Fin r) O)) *
      conj (locDatum r t I J' ν x) = 0)
def LocDatumLeft : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (r t : ℕ) (J' : Subgroup (GL (Fin r) O)) (ν : J' →* ℂ),
    (∀ (g : GL (Fin r) O), (∀ i j, ((g : Matrix (Fin r) (Fin r) O) - 1) i j ∈
      IsLocalRing.maximalIdeal O) → ∃ hg : g ∈ J', ν ⟨g, hg⟩ = 1) →
    ∀ (h : GL (Fin r ⊕ Fin t) O) (k : J') (b : Matrix (Fin r) (Fin t) O)
      (c : Matrix (Fin t) (Fin r) O) (d : Matrix (Fin t) (Fin t) O),
    (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) =
      Matrix.fromBlocks ((k : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) b c d →
    (∀ i j, c i j ∈ IsLocalRing.maximalIdeal O) →
    ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) O,
      locDatum r t (IsLocalRing.maximalIdeal O) J' ν
          ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * x) =
        ν k * locDatum r t (IsLocalRing.maximalIdeal O) J' ν x
def ConjCongruenceImage : Prop :=
  ∀ (O : Type) [CommRing O] (ϖ : O) (a : ℕ) (e : Fin a → ℕ) (y : Matrix (Fin a) (Fin a) O),
    (∀ i j, y i j ≠ 0 → e i < e j) →
    ∃ x : Matrix (Fin a) (Fin a) O, (∀ i j, ϖ ∣ (x - 1) i j) ∧
      Matrix.diagonal (fun i => ϖ ^ e i) * x = (1 + y) * Matrix.diagonal (fun i => ϖ ^ e i)
def IwasawaInvariants : Prop :=
  ∀ (G V : Type) [Group G] (P K₀ K₁ : Subgroup G) [MulAction P V],
    (∀ g : G, ∃ p ∈ P, ∃ k ∈ K₀, g = p * k) → K₁ ≤ K₀ → (∀ k ∈ K₀, ∀ u ∈ K₁, k * u * k⁻¹ ∈ K₁) →
    Set.BijOn (fun (f : G → V) (k : K₀) => f k)
      {f | (∀ (p : P) (g : G), f (p * g) = p • f g) ∧ ∀ g : G, ∀ u ∈ K₁, f (g * u) = f g}
      {φ | (∀ (p : P) (k k' : K₀), (k' : G) = p * k → φ k' = p • φ k) ∧
        ∀ k k' : K₀, (k : G)⁻¹ * k' ∈ K₁ → φ k' = φ k} ∧
    ∀ f : G → V, (∀ (p : P) (g : G), f (p * g) = p • f g) → (∀ g : G, ∀ u ∈ K₁, f (g * u) = f g) →
      ∀ p : P, (p : G) ∈ K₁ → ∀ k ∈ K₀, p • f k = f k
def SublatticeCount : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (n k : ℕ),
    Nat.card {L : Submodule O (Fin n → O) //
        Nat.card ((Fin n → O) ⧸ L) = Nat.card (IsLocalRing.ResidueField O) ^ k} =
      ∑ c ∈ Finset.Nat.antidiagonalTuple n k,
        ∏ i : Fin n, Nat.card (IsLocalRing.ResidueField O) ^ ((i : ℕ) * c i)
def SublatticeZeta : Prop :=
  ∀ (q : ℕ) (n : ℕ) (s : ℝ), 2 ≤ q → (n : ℝ) - 1 < s →
    HasSum (fun k : ℕ => ((∑ c ∈ Finset.Nat.antidiagonalTuple n k,
        ∏ i : Fin n, q ^ ((i : ℕ) * c i) : ℕ) : ℝ) * (q : ℝ) ^ (-(k : ℝ) * s))
      (∏ i : Fin n, (1 - (q : ℝ) ^ (((i : ℕ) : ℝ) - s))⁻¹)
def eulFactor (r t : ℕ) (q : ℝ) (z : Fin (2 * r) → ℂ) (ε : Fin r → ℂ) : ℂ :=
  (∏ k, (1 - z k)⁻¹) * ∏ i : Fin r, (1 - ε i * ((q ^ (-((t : ℝ) + (i : ℕ) + 1)) : ℝ) : ℂ))
def EulFull : Prop :=
  ∀ (ι : Type) (r t : ℕ) (q : ι → ℝ) (z : ι → Fin (2 * r) → ℂ) (ε : ι → Fin r → ℂ),
    Odd r → Odd t → r < t → (∀ v, 2 ≤ q v) → Summable (fun v => (q v) ^ (-2 : ℝ)) →
    (∀ v k, ‖z v k‖ ≤ (q v) ^ (-(((t : ℝ) - r + 2) / 2))) → (∀ v i, ε v i = 1 ∨ ε v i = -1) →
    (∀ v, eulFactor r t (q v) (z v) (ε v) ≠ 0) ∧
    Summable (fun v => ‖eulFactor r t (q v) (z v) (ε v) - 1‖) ∧
    Multipliable (fun v => eulFactor r t (q v) (z v) (ε v)) ∧
    (∏' v, eulFactor r t (q v) (z v) (ε v)) ≠ 0
def PrimeNormSummable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (s : ℝ), 1 < s →
    Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s))
def EulerSplitInert : Prop :=
  ∀ (σ ι : Type) (qs : σ → ℝ) (q : ι → ℝ) (ch : ι → ℂ) (s : ℂ), (∀ w, 2 ≤ qs w) → (∀ v, 2 ≤ q v) →
    (∀ v, ‖ch v‖ = 1) → 1 < s.re → Summable (fun w => (qs w) ^ (-s.re)) →
    Summable (fun v => (q v) ^ (-2 * s.re)) →
    (∏' w : σ ⊕ ι, (1 - Sum.elim (fun _ => (1 : ℂ)) ch w *
        ((Sum.elim qs (fun v => q v ^ 2) w : ℝ) : ℂ) ^ (-s))⁻¹) =
      (∏' w : σ ⊕ ι, (1 - ((Sum.elim qs (fun v => q v ^ 2) w : ℝ) : ℂ) ^ (-s))⁻¹) *
        ∏' v, inertFactor (q v) (ch v) s
def RealParameter : Prop :=
  ∀ (p q' t n : ℕ) (a : Fin p → ℤ) (b : Fin q' → ℤ), n = p + q' + t → Antitone a → Monotone b →
    (∀ i, 1 ≤ a i) → (∀ j, 1 ≤ b j) →
    (∀ i : Fin p, (a i : ℚ) + (n : ℚ) / 2 + (((p : ℚ) + 1) / 2 - ((i : ℕ) + 1)) - (q' : ℚ) / 2 =
      (a i : ℚ) + ((t : ℚ) + 1) / 2 + ((p : ℚ) - 1 - (i : ℕ))) ∧
    (∀ j : Fin q', -(b j : ℚ) - (n : ℚ) / 2 + (((q' : ℚ) + 1) / 2 - ((j : ℕ) + 1)) + (p : ℚ) / 2 =
      -(b j : ℚ) - ((t : ℚ) + 1) / 2 - (j : ℕ)) ∧
    StrictAnti (fun i : Fin p => (a i : ℚ) + ((t : ℚ) + 1) / 2 + ((p : ℚ) - 1 - (i : ℕ))) ∧
    StrictAnti (fun j : Fin q' => -(b j : ℚ) - ((t : ℚ) + 1) / 2 - (j : ℕ)) ∧
    (∀ i : Fin p, ((t : ℚ) + 3) / 2 ≤ (a i : ℚ) + ((t : ℚ) + 1) / 2 + ((p : ℚ) - 1 - (i : ℕ))) ∧
    (∀ j : Fin q', -(b j : ℚ) - ((t : ℚ) + 1) / 2 - (j : ℕ) ≤ -(((t : ℚ) + 3) / 2)) ∧
    (∀ i : Fin p, (a i : ℚ) + (((n : ℚ) - 1) / 2 - (i : ℕ)) - ((q' : ℚ) - p) / 2 =
      (a i : ℚ) + ((t : ℚ) + 1) / 2 + ((p : ℚ) - 1 - (i : ℕ))) ∧
    (∀ k : Fin t, (0 : ℚ) + (((n : ℚ) - 1) / 2 - (p + (k : ℕ))) - ((q' : ℚ) - p) / 2 =
      ((t : ℚ) - 1) / 2 - (k : ℕ)) ∧
    (∀ j : Fin q', -(b j : ℚ) + (((n : ℚ) - 1) / 2 - (p + t + (j : ℕ))) - ((q' : ℚ) - p) / 2 =
      -(b j : ℚ) - ((t : ℚ) + 1) / 2 - (j : ℕ))
def IsotypicScalar : Prop :=
  ∀ (M N : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N] (ι : Type) [Fintype ι]
    (Ms : ι → Submodule ℂ M) (θ : M →ₗ[ℂ] N) (lam : ι → ℂ), (⨆ s, Ms s) = ⊤ →
    (∀ s s', s ≠ s' → ∀ f ∈ Ms s, ∀ f' ∈ Ms s',
      inner ℂ f' f = 0 ∧ inner ℂ (θ f') (θ f) = 0) →
    (∀ s, ∀ f ∈ Ms s, ∀ f' ∈ Ms s, inner ℂ (θ f') (θ f) = lam s * inner ℂ f' f) →
    (∀ s, ∀ f ∈ Ms s, LinearMap.adjoint θ (θ f) = lam s • f) ∧
      ((∀ s, lam s ≠ 0) → Function.Injective θ)
def LamPositive : Prop :=
  ∀ (M N : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [NormedAddCommGroup N]
    [InnerProductSpace ℂ N] (θ : M →ₗ[ℂ] N) (f : M) (lam : ℂ), f ≠ 0 →
    inner ℂ (θ f) (θ f) = lam * inner ℂ f f → lam ≠ 0 → 0 < lam.re ∧ lam.im = 0
def TensorHomLine : Prop :=
  ∀ (k : Type) [Field k] (G₁ G₂ : Type) [Monoid G₁] [Monoid G₂] (A₁ A₂ B₁ B₂ : Type)
    [AddCommGroup A₁] [Module k A₁] [AddCommGroup A₂] [Module k A₂] [AddCommGroup B₁] [Module k B₁]
    [AddCommGroup B₂] [Module k B₂] (α₁ : Representation k G₁ A₁) (β₁ : Representation k G₁ B₁)
    (α₂ : Representation k G₂ A₂) (β₂ : Representation k G₂ B₂) (l₁ : A₁ →ₗ[k] B₁)
    (l₂ : A₂ →ₗ[k] B₂),
    (∀ l : A₁ →ₗ[k] B₁, (∀ g, l ∘ₗ α₁ g = β₁ g ∘ₗ l) → ∃ c : k, l = c • l₁) →
    (∀ l : A₂ →ₗ[k] B₂, (∀ g, l ∘ₗ α₂ g = β₂ g ∘ₗ l) → ∃ c : k, l = c • l₂) →
    ∀ l : A₁ ⊗[k] A₂ →ₗ[k] B₁ ⊗[k] B₂,
      (∀ g, l ∘ₗ TensorProduct.map (α₁ g) LinearMap.id =
        TensorProduct.map (β₁ g) LinearMap.id ∘ₗ l) →
      (∀ g, l ∘ₗ TensorProduct.map LinearMap.id (α₂ g) =
        TensorProduct.map LinearMap.id (β₂ g) ∘ₗ l) →
      ∃ c : k, l = c • TensorProduct.map l₁ l₂
def DirectedHomLine : Prop :=
  ∀ (k V W : Type) [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (ι : Type)
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (Vs : ι → Submodule k V)
    (H : Submodule k (V →ₗ[k] W)), Monotone Vs → (⨆ i, Vs i) = ⊤ →
    (∀ i, ∀ l ∈ H, ∀ l' ∈ H, l.domRestrict (Vs i) ≠ 0 →
      ∃ c : k, l'.domRestrict (Vs i) = c • l.domRestrict (Vs i)) →
    ∀ l ∈ H, ∀ l' ∈ H, l ≠ 0 → ∃ c : k, l' = c • l
def HomLineSimple : Prop :=
  ∀ (k R M Θ P : Type) [Field k] [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup Θ]
    [Module R Θ] [AddCommGroup P] [Module k P] [Module R P] [IsSemisimpleModule R Θ] [Nontrivial Θ]
    (π : M →ₗ[R] Θ), Function.Surjective π →
    (∀ S : Submodule R Θ, IsSimpleModule R S → Nonempty (S ≃ₗ[R] P)) →
    (∀ l l' : M →ₗ[R] P, l ≠ 0 → ∃ c : k, ∀ m, l' m = c • l m) → IsSimpleModule R Θ
def UnipotentTwistCharpoly : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A U : Module.End K V), Commute A U → IsNilpotent (U - 1) → (A * U).charpoly = A.charpoly
def WDEigenspace : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A U : Module.End K V) (c : K), Commute A U → IsNilpotent (U - 1) → A.IsSemisimple →
    (A * U).maxGenEigenspace c = A.eigenspace c
def GeneralizedEigenSplit : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (γ₀ γ : Module.End K V) (c : K) (t : ℕ) (s : K[X]), Commute γ₀ γ →
    γ₀.charpoly = s * (X - C c) ^ t → s.eval c ≠ 0 →
    IsCompl (LinearMap.ker (aeval γ₀ s)) (γ₀.maxGenEigenspace c) ∧
    Module.finrank K (γ₀.maxGenEigenspace c) = t ∧
    (∀ v ∈ LinearMap.ker (aeval γ₀ s),
      γ₀ v ∈ LinearMap.ker (aeval γ₀ s) ∧ γ v ∈ LinearMap.ker (aeval γ₀ s)) ∧
    ∀ v ∈ γ₀.maxGenEigenspace c, γ₀ v ∈ γ₀.maxGenEigenspace c ∧ γ v ∈ γ₀.maxGenEigenspace c
def TopGenPrimitive : Prop :=
  ∀ (Γ R : Type) [Group Γ] [TopologicalSpace Γ] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] (χ : Γ →* Rˣ) (γ₀ : Γ) (m : ℕ),
    Continuous (fun γ => ((χ γ : Rˣ) : R)) → Dense ((Subgroup.zpowers γ₀ : Subgroup Γ) : Set Γ) →
    orderOf χ = m → IsPrimitiveRoot ((χ γ₀ : Rˣ) : R) m
def CoprimeCohomologyVanish : Prop :=
  ∀ (k G : Type) [CommRing k] [Group G] [Finite G] (A : Rep k G), IsUnit ((Nat.card G : ℕ) : k) →
    ∀ j : ℕ, Subsingleton (groupCohomology A (j + 1))
def NormalCentreKills : Prop :=
  ∀ (k G : Type) [CommRing k] [Group G] (A : Rep k G) (N : Subgroup G) [N.Normal] (z : G), z ∈ N →
    (∀ u ∈ N, u * z = z * u) → Function.Bijective (fun a : A => A.ρ z a - a) →
    ∀ j : ℕ, Subsingleton (groupCohomology A j)
def IrreducibleOfResidual : Prop :=
  ∀ (O A L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Ring A] [Algebra O A]
    [AddCommGroup L] [Module O L] [Module A L] [IsScalarTower O A L] [Module.Finite O L] (ϖ : O),
    Irreducible ϖ →
    (∀ N : Submodule A L, (∀ x : L, ϖ • x ∈ N) → (∀ y ∈ N, ∃ x : L, y = ϖ • x) ∨ N = ⊤) →
    ∀ N : Submodule A L, (∀ x : L, ϖ • x ∈ N → x ∈ N) → N = ⊥ ∨ N = ⊤
def HermTraceNondeg : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] (i : ℕ) (T : Matrix (Fin i) (Fin i) E), (2 : E) ≠ 0 →
    T.IsHermitian → T ≠ 0 → ∃ b : Matrix (Fin i) (Fin i) E, b.IsHermitian ∧ (b * T).trace ≠ 0
def CharIntegralZero : Prop :=
  ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] (μ : Measure Z) [μ.IsHaarMeasure] (ψ : Z →* Circle),
    Continuous ψ → ψ ≠ 1 → ∫ b, ((ψ b : Circle) : ℂ) ∂μ = 0
def GramZeroAnisotropic : Prop :=
  ∀ (E V : Type) [Field E] [AddCommGroup V] [Module E V] (σ : E →+* E) (B : V →ₛₗ[σ] V →ₗ[E] E)
    (i : ℕ) (x : Fin i → V), (∀ u, B u u = 0 → u = 0) → (∀ a b, B (x a) (x b) = 0) → x = 0
def NoConstituentNoMap : Prop :=
  ∀ (R M P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [IsSemisimpleModule R M] [IsSimpleModule R P],
    (∀ S : Submodule R M, IsEmpty (S ≃ₗ[R] P)) → ∀ f : M →ₗ[R] P, f = 0
def IsotropicGraph : Prop :=
  ∀ (E V : Type) [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (σ : E →+* E)
    (B : V →ₛₗ[σ] V →ₗ[E] E) (Y : Submodule E (V × V)), (∀ u, B u u = 0 → u = 0) →
    Module.finrank E Y = Module.finrank E V →
    (∀ y ∈ Y, ∀ y' ∈ Y, B y.1 y'.1 - B y.2 y'.2 = 0) →
    ∃! γ : V ≃ₗ[E] V, (∀ u u', B (γ u) (γ u') = B u u') ∧ ∀ y : V × V, y ∈ Y ↔ y.1 = γ y.2
def ZonalProduct : Prop :=
  ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (K : Subgroup G) [CompactSpace K] [MeasurableSpace K]
    [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (π : G →* (H →L[ℂ] H)) (F : H),
    (∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y) → (∀ x, Continuous fun g => π g x) →
    ‖F‖ = 1 → (∀ k : K, π k F = F) → (∀ x, (∀ k : K, π k x = x) → ∃ c : ℂ, x = c • F) →
    ∀ a b : G, ∫ k : K, inner ℂ F (π (a * k * b) F) ∂μ = inner ℂ F (π a F) * inner ℂ F (π b F)
def RankOneDoubling : Prop :=
  ∀ x y : ℂ, x ≠ 0 → ‖x * y‖ < 1 → ‖x⁻¹ * y‖ < 1 →
    HasSum (fun a : ℤ => x ^ a * y ^ a.natAbs) ((1 - y ^ 2) / ((1 - x * y) * (1 - x⁻¹ * y)))
def SchurOrthogonalityCompact : Prop :=
  ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (τ : G →* (V →ₗ[ℂ] V)),
    (∀ g x y, inner ℂ (τ g x) (τ g y) = inner ℂ x y) → (∀ x, Continuous fun g => τ g x) →
    (∀ W : Submodule ℂ V, (∀ g, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤) →
    ∀ u₁ u₂ v₁ v₂ : V,
      (Module.finrank ℂ V : ℂ) * ∫ g, inner ℂ v₁ (τ g u₁) * conj (inner ℂ v₂ (τ g u₂)) ∂μ =
        ((μ Set.univ).toReal : ℂ) * (inner ℂ u₂ u₁ * inner ℂ v₁ v₂)
def BlockLFactor : Prop :=
  ∀ (t : ℕ) (q : ℝ) (μ s : ℂ), 1 < q → μ ≠ 0 →
    ((block q μ t).map fun β => (1 - β * μ⁻¹ * (q : ℂ) ^ (-(s + 1 / 2)))⁻¹).prod =
      ∏ k ∈ Finset.range t, (1 - (q : ℂ) ^ (-(s + (t : ℂ) / 2 - k)))⁻¹
def ZPoleOrder : Prop :=
  ∀ (t : ℕ) (ζ L d : ℂ → ℂ) (C : ℂ), 1 ≤ t → C ≠ 0 → meromorphicOrderAt ζ 1 = -1 →
    (∀ j : ℕ, 2 ≤ j → j ≤ t → AnalyticAt ℂ ζ (j : ℂ) ∧ ζ (j : ℂ) ≠ 0) →
    AnalyticAt ℂ L (((t : ℂ) + 1) / 2) → L (((t : ℂ) + 1) / 2) ≠ 0 →
    AnalyticAt ℂ d ((t : ℂ) / 2) → d ((t : ℂ) / 2) ≠ 0 →
    meromorphicOrderAt
      (fun s => C * L (s + 1 / 2) * (∏ k ∈ Finset.range t, ζ (s + (t : ℂ) / 2 - k)) / d s)
      ((t : ℂ) / 2) = -1
def ZNumerology2 : Prop :=
  ∀ (r t n r' m₀ : ℕ), 0 < r → r < t → n = r + t → r = m₀ + 2 * r' →
    (2 * n - r) + r = 2 * n ∧ m₀ + (r' + t) + r' = n ∧ (0 < r' → r - r' < n ∧ r' ≤ n) ∧
      ((2 * n - r) - (r' + t) < n ↔ 0 < r')
def DenseSpanNonzero : Prop :=
  ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] (J : S →ₗ[ℂ] ℂ) (D : Set S),
    Continuous J → Dense ((Submodule.span ℂ D : Submodule ℂ S) : Set S) → J ≠ 0 → ∃ x ∈ D, J x ≠ 0
def BaseChangeBijective : Prop :=
  ∀ (K C M N : Type) [Field K] [Field C] [Algebra K C] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (θ : M →ₗ[K] N),
    Function.Bijective (θ.baseChange C) → Function.Bijective θ
def BaseChangeIdentity : Prop :=
  ∀ (K C M N : Type) [Field K] [Field C] [Algebra K C] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (θ θ' : M →ₗ[K] N), θ.baseChange C = θ'.baseChange C → θ = θ'
def InverseOfBijectiveScalar : Prop :=
  ∀ (K M N : Type) [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (θ : M →ₗ[K] N) (θ' : N →ₗ[K] M) (lam : K), lam ≠ 0 → θ' ∘ₗ θ = lam • LinearMap.id →
    Function.Bijective θ → θ ∘ₗ θ' = lam • LinearMap.id ∧ Function.Bijective θ'
def HeckeEigenRational : Prop :=
  ∀ (K : Type) [Field K] (r n k : ℕ) (α : Fin r → K) (η s : K), η ≠ 0 → s ≠ 0 → 2 ≤ n →
    ((Finset.univ.val.map fun i => (α i)⁻¹).esymm k =
      (Finset.univ.val.map fun i => (α i)⁻¹ * η⁻¹ * s ^ (n - 1)).esymm k * (η * s⁻¹) ^ k *
        ((s ^ (n - 2))⁻¹) ^ k) ∧
    (Odd r → Even (k * (r - k))) ∧ (Even n → Even (k * (n - 2)))
def BCUnimodularDiag : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] [StarRing R],
    (∀ u : R, IsUnit u → star u = u → ∃ c : R, c * star c = u) →
    (∀ x : R, IsUnit x → ∃ c : R, IsUnit (c * x + star (c * x))) →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) R), H.IsHermitian → IsUnit H →
      ∃ g : Matrix (Fin n) (Fin n) R, IsUnit g ∧ g * H * g.conjTranspose = 1
def BCHyperbolicDet : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (a : ℕ) (M : Matrix (Fin a) (Fin a) K),
    (Matrix.fromBlocks 0 M M.conjTranspose 0).det = (-1) ^ a * (M.det * star M.det)
def BCSylvesterDet : Prop :=
  ∀ (R : Type) [CommRing R] (a b : ℕ) (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin b) (Fin b) R)
    (f : Matrix (Fin a) (Fin b) R →ₗ[R] Matrix (Fin a) (Fin b) R), (∀ ν, f ν = A * ν - ν * B) →
    LinearMap.det f = (aeval A B.charpoly).det
def BCOddDegree : Prop :=
  ∀ (k' : Type) [Field k'] [Fintype k'] (q d : ℕ) (σ : k' ≃+* k'), Fintype.card k' = q ^ (2 * d) →
    (∀ y, σ (σ y) = y) → (∀ y : k', y ^ (q ^ 2) = y → σ y = y ^ q) → Odd d
def BCGramTwistDet : Prop :=
  ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] (ι : Type) [Fintype ι] [DecidableEq ι]
    (w : Module.Basis ι K A) (h : A → A →ₗ[K] K) (x : A),
    (Matrix.of fun i j => h (w j) (x * w i)).det =
      Algebra.norm K x * (Matrix.of fun i j => h (w j) (w i)).det
def BCCayley : Prop :=
  ∀ (A : Type) [CommRing A] (σ : A →+* A) (γ ε : A), γ * σ γ = 1 → σ ε = -ε → IsUnit (γ + 1) →
    IsUnit ((2 : A) * ε) → ∀ X : A, X * (γ + 1) = ε * (γ - 1) →
      σ X = X ∧ (ε + X) * (γ + 1) = 2 * ε * γ ∧ (ε - X) * (γ + 1) = 2 * ε ∧ IsUnit (ε - X) ∧
        γ * (ε - X) = ε + X
def BCCayleyDifference : Prop :=
  ∀ (K : Type) [Field K] (ε g₁ g₂ : K), (2 : K) ≠ 0 → ε ≠ 0 → g₁ + 1 ≠ 0 → g₂ + 1 ≠ 0 →
    g₁ = (ε + ε * (g₁ - 1) * (g₁ + 1)⁻¹) * (ε - ε * (g₁ - 1) * (g₁ + 1)⁻¹)⁻¹ ∧
    ε * (g₁ - 1) * (g₁ + 1)⁻¹ - ε * (g₂ - 1) * (g₂ + 1)⁻¹ =
      2 * ε * (g₁ - g₂) / ((g₁ + 1) * (g₂ + 1))
def BCLatticeIndexDet : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (n : ℕ) (f : (Fin n → O) →ₗ[O] (Fin n → O)),
    LinearMap.det f ≠ 0 →
    Nat.card ((Fin n → O) ⧸ LinearMap.range f) = Nat.card (O ⧸ Ideal.span {LinearMap.det f})
def BCHankelFactor : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (γ : Matrix (Fin n) (Fin n) R) (u₀ u' : Fin n → R),
    (Matrix.of fun k l : Fin n => u' ⬝ᵥ (γ ^ ((k : ℕ) + (l : ℕ))).mulVec u₀).det =
      (Matrix.of fun k j : Fin n => (Matrix.vecMul u' (γ ^ (k : ℕ))) j).det *
        (Matrix.of fun j l : Fin n => ((γ ^ (l : ℕ)).mulVec u₀) j).det
def BCAlternatingSum : Prop :=
  ∀ k₀ k₁ : ℤ, k₀ ≤ k₁ →
    ∑ k ∈ Finset.Icc k₀ k₁, (-1 : ℚ) ^ k = ((-1 : ℚ) ^ k₀ + (-1 : ℚ) ^ k₁) / 2
def BCSignFourier : Prop :=
  ∀ (n : ℕ) (O : Finset (Fin n) → ℝ) (N : (Fin n → ℤˣ) → ℝ),
    (∀ x, N x = ∑ La : Finset (Fin n), (∏ i ∈ La, (((x i : ℤˣ) : ℤ) : ℝ)) * O La) →
    ∀ La : Finset (Fin n), ∑ x, (∏ i ∈ La, (((x i : ℤˣ) : ℤ) : ℝ)) * N x = 2 ^ n * O La
def BCIwahoriCharpoly : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (ϖ : O) (n : ℕ) (a : Fin n → ℕ)
    (z : Matrix (Fin n) (Fin n) O), ϖ ∈ IsLocalRing.maximalIdeal O → StrictAnti a →
    (∀ i, IsUnit (z i i)) → (∀ i j, j < i → z i j ∈ IsLocalRing.maximalIdeal O) →
    ∀ m : ℕ, m ≤ n → ∃ u : O, IsUnit u ∧
      (Matrix.diagonal (fun i => ϖ ^ a i) * z).charpoly.coeff (n - m) =
        ϖ ^ (∑ i ∈ Finset.univ.filter (fun i : Fin n => n - m ≤ (i : ℕ)), a i) * u
def BCConeIndependence : Prop :=
  ∀ (m : ℕ) (g : ℤ) (S : Finset (Fin m → ℂˣ)) (c : (Fin m → ℂˣ) → ℂ),
    (∀ l : Fin m → ℤ, (∀ i j, i < j → l j + g ≤ l i) → (∀ i, g ≤ l i) →
      ∑ y ∈ S, c y * ∏ i, ((y i : ℂˣ) : ℂ) ^ (l i) = 0) →
    ∀ y ∈ S, c y = 0
def BCCyclicVector : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (g : Module.End K V), g.charpoly.Separable → ∃ e : V, ∀ v : V, ∃ p : K[X], aeval g p e = v
def BCSignIndicator : Prop :=
  ∀ (c : ℕ) (ε : Fin c → ℤ), (∀ i, ε i = 1 ∨ ε i = -1) →
    ∑ Ka : Finset (Fin c), ∏ i ∈ Ka, ε i = if ∀ i, ε i = 1 then 2 ^ c else 0
def BCSignCharSum : Prop :=
  ∀ (n : ℕ) (Ka : Finset (Fin n)), Ka.Nonempty →
    ∑ x : Fin n → ℤˣ, ∏ i ∈ Ka, ((x i : ℤˣ) : ℤ) = 0
def bcPhi (R : Type) [Ring R] (a : ℕ) : Matrix (Fin a) (Fin a) R :=
  Matrix.of fun i j => if (i : ℕ) + (j : ℕ) + 1 = a then (-1) ^ (i : ℕ) else 0
def BCTwistedNorm : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (a : ℕ) (δ : Matrix (Fin a) (Fin a) K), IsUnit δ →
    (bcPhi K a).transpose = (-1 : K) ^ (a - 1) • bcPhi K a ∧ IsUnit (bcPhi K a) ∧
    (δ * bcPhi K a) * ((δ * bcPhi K a).conjTranspose)⁻¹ =
      (-1 : K) ^ (a - 1) • (δ * (bcPhi K a * (δ.conjTranspose)⁻¹ * (bcPhi K a)⁻¹))
def BCAsymmetryIsometry : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (a : ℕ) (S : Matrix (Fin a) (Fin a) K), IsUnit S →
    (∀ u : Matrix (Fin a) (Fin a) K, S * u = S.conjTranspose ↔ u = S⁻¹ * S.conjTranspose) ∧
    (S⁻¹ * S.conjTranspose).conjTranspose * S * (S⁻¹ * S.conjTranspose) = S
def BCTraceSwap : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (X Y : Module.End K V),
    LinearMap.trace K (TensorProduct K V V)
      (TensorProduct.map X Y ∘ₗ (TensorProduct.comm K V V).toLinearMap) = LinearMap.trace K V (X * Y)
def BCDiscResultant : Prop :=
  ∀ (K : Type) [Field K] (a b : ℕ) (α : Fin a → K) (β : Fin b → K), (∀ i, α i ≠ 0) →
    (∀ j, β j ≠ 0) →
    ∏ i, ∏ j, ((1 - α i / β j) * (1 - β j / α i)) =
      (-1) ^ (a * b) * (∏ i, ∏ j, (α i - β j)) ^ 2 / ((∏ i, α i) ^ b * (∏ j, β j) ^ a)
def BCNormOneCount : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (q : ℕ), Fintype.card k = q ^ 2 →
    Nat.card {c : k // c ^ (q + 1) = 1} = q + 1
def BCBetaZero : Prop :=
  ∀ (A : Type) [CommRing A] (σ : A →+* A) (γ c e s : A), γ * σ γ = 1 → c * σ c = 1 →
    IsUnit (γ + c) → IsUnit e → σ e * c = s * e →
    ∀ β : A, β * (γ + c) = e → IsUnit β ∧ σ β = s * γ * β
def BCOddCycleStable : Prop :=
  ∀ (B X : Type) (p : Equiv.Perm B) (θ : X → X) (s : B → X), (∀ x, θ (θ x) = x) →
    (∀ k, s (p k) = θ (s k)) →
    ∀ (k : B) (l : ℕ), Odd l → (p ^ l) k = k → θ (s k) = s k ∧ s (p k) = s k
def BCCentredSegments : Prop :=
  ∀ D : Multiset ℕ, (∀ d ∈ D, 1 ≤ d) → (expo D).Nodup →
    (∀ x ∈ expo D, ∀ y ∈ expo D, (2 : ℤ) ∣ x - y) → D.card ≤ 1
open scoped Classical in

def BCIsolation : Prop :=
  ∀ (H : Type) [Monoid H] (I J : Type) [Fintype I] [Fintype J] (χ : I → H →* ℂ) (χ' : J → H →* ℂ)
    (a : I → ℂ) (b : J → ℂ), (∀ f : H, ∑ i, a i * χ i f = ∑ j, b j * χ' j f) →
    ∀ c : H →* ℂ, ∑ i with χ i = c, a i = ∑ j with χ' j = c, b j
def BCTraceIndependence : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (ι : Type) [Fintype ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, Module A (V i)]
    [∀ i, IsScalarTower ℂ A (V i)] [∀ i, FiniteDimensional ℂ (V i)],
    (∀ i, IsSimpleModule A (V i)) → (∀ i j, Nonempty (V i ≃ₗ[A] V j) → i = j) →
    ∀ c : ι → ℂ,
      (∀ x : A, ∑ i, c i * LinearMap.trace ℂ (V i) (Algebra.lsmul ℂ ℂ (V i) x) = 0) → ∀ i, c i = 0
def BCOrthogonalDetPos : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.transpose * A = 1 →
    (∀ v : Fin n → ℝ, A.mulVec v = v → v = 0) → 0 < (1 - A).det
def BCParahoricMul : Prop :=
  ∀ (O : Type) [CommRing O] (U L : Ideal O) (n : ℕ) (x y : Matrix (Fin n) (Fin n) O),
    (∀ i j, i < j → x i j ∈ U) → (∀ i j, j < i → x i j ∈ L) → (∀ i j, i < j → y i j ∈ U) →
    (∀ i j, j < i → y i j ∈ L) →
    (∀ i j, i < j → (x * y) i j ∈ U) ∧ (∀ i j, j < i → (x * y) i j ∈ L) ∧
      ∀ i, (x * y) i i - x i i * y i i ∈ U * L
def BCIwahoriFactor : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (U L : Ideal O) (n : ℕ) (g : Matrix (Fin n) (Fin n) O),
    L ≤ IsLocalRing.maximalIdeal O → (∀ i, IsUnit (g i i)) → (∀ i j, i < j → g i j ∈ U) →
    (∀ i j, j < i → g i j ∈ L) →
    ∃ x d y : Matrix (Fin n) (Fin n) O, g = x * d * y ∧
      (∀ i, x i i = 1) ∧ (∀ i j, j < i → x i j = 0) ∧ (∀ i j, i < j → x i j ∈ U) ∧
      (∀ i j, i ≠ j → d i j = 0) ∧ (∀ i, IsUnit (d i i)) ∧ (∀ i, d i i - g i i ∈ U * L) ∧
      (∀ i, y i i = 1) ∧ (∀ i j, i < j → y i j = 0) ∧ (∀ i j, j < i → y i j ∈ L)
def BCSignedPermFix : Prop :=
  ∀ (m : ℕ) (l : Fin m → ℤ) (σ : Equiv.Perm (Fin m)) (ε : Fin m → ℤˣ), StrictAnti l →
    (∀ i, 0 < l i) → (∀ i, ((ε i : ℤˣ) : ℤ) * l (σ i) = l i) → σ = 1 ∧ ∀ i, ε i = 1
def BCPairValuation : Prop :=
  ∀ r s : ℤ, 0 < r → 0 < s →
    min r s + min r (-s) + min (-r) s + min (-r) (-s) = -2 * max r s ∧ min 0 s + min 0 (-s) = -s
def bcD {m : ℕ} (l : Fin m → ℤ) (S : Finset (Fin m)) (e : ℤ) : ℤ :=
  (∑ i ∈ S, ∑ j ∈ S, if i < j then 2 * (l i - l j) + 2 * (l i + l j) else 0) +
    2 * (1 + e) * ∑ i ∈ S, l i
def bcVR {m : ℕ} (l : Fin m → ℤ) (S : Finset (Fin m)) (ea eb : ℤ) : ℤ :=
  -2 * ∑ i ∈ S, ∑ j ∈ Sᶜ, max (l i) (l j) - ea * ∑ j ∈ Sᶜ, l j - eb * ∑ i ∈ S, l i
def BCModulusSum : Prop :=
  ∀ (m : ℕ) (e : ℤ) (l : Fin m → ℤ),
    bcD l Finset.univ e = 2 * ∑ i : Fin m, (2 * (m : ℤ) + e + 1 - 2 * ((i : ℤ) + 1)) * l i
def BCModulusRatio : Prop :=
  ∀ (m : ℕ) (l : Fin m → ℤ) (S : Finset (Fin m)) (ea eb : ℤ), Antitone l →
    bcD l Finset.univ (ea + eb) - bcD l S ea - bcD l Sᶜ eb = -2 * bcVR l S ea eb
def BCSignParity : Prop :=
  ∀ (m : ℕ) (l : Fin m → ℤ) (S : Finset (Fin m)) (ea eb ma mb : ℤ),
    (2 : ℤ) ∣ bcVR l S ea eb - ((2 * mb + eb) * ∑ i ∈ S, l i + (2 * ma + ea) * ∑ j ∈ Sᶜ, l j)
def BCHalfSplit : Prop :=
  ∀ l l' : ℤ, l' + 2 ≤ l → 2 ≤ l' →
    l' / 2 < l / 2 ∧ l' - l' / 2 < l - l / 2 ∧ 1 ≤ l' / 2 ∧ 1 ≤ l' - l' / 2
def BCTwistedTraceScalar : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S S' A : Module.End K V) (c : K), Commute S S' →
    IsNilpotent (S - algebraMap K (Module.End K V) c) →
    IsNilpotent (S' - algebraMap K (Module.End K V) c) → A * S = S' * A → A * S' = S * A →
    LinearMap.trace K V (S * A) = c * LinearMap.trace K V A
end Formalism.IrreducibleCountingLemmas.Z


