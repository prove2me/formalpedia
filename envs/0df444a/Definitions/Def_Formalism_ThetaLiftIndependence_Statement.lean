-- Prove2me | Definitions.Def_Formalism_ThetaLiftIndependence_Statement
-- name    : Formalism_ThetaLiftIndependence_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:59:13.300144+00:00
-- url     : https://prove2.me/theorems/faabc4a8-5814-466b-a41b-dd56131b173f
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/Statement.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.ThetaLiftIndependence
def kerOp {R ι κ : Type*} [CommSemiring R] [Fintype ι] (w : ι → R) (K : ι → κ → R)
    (f : ι → R) : κ → R :=
  fun j => ∑ i, w i * f i * K i j
def kerMul {R ι κ μ : Type*} [CommSemiring R] [Fintype κ] (w : κ → R) (K₁ : ι → κ → R)
    (K₂ : κ → μ → R) : ι → μ → R :=
  fun i k => ∑ j, K₁ i j * w j * K₂ j k
def wip {R ι : Type*} [CommSemiring R] [StarRing R] [Fintype ι] (w : ι → R) (f g : ι → R) : R :=
  ∑ i, w i * star (f i) * g i
def kerAdj {R ι κ : Type*} [CommSemiring R] [StarRing R] (K : ι → κ → R) : κ → ι → R :=
  fun j i => star (K i j)
def chainOp {R : Type*} [CommSemiring R] {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → R) : (m : ℕ) → (ι 0 → R) → (ι m → R)
  | 0, f => f
  | m + 1, f => kerOp (w m) (K m) (chainOp w K m f)
def KerAdjoint : Prop :=
  ∀ (R : Type) [CommSemiring R] [StarRing R] (ι κ : Type) [Fintype ι] [Fintype κ]
    (w : ι → R) (w' : κ → R) (K : ι → κ → R) (f : ι → R) (g : κ → R),
    (∀ i, star (w i) = w i) →
    wip w' (kerOp w K f) g = wip w f (kerOp w' (kerAdj K) g)
def KerComp : Prop :=
  ∀ (R : Type) [CommSemiring R] (ι κ μ : Type) [Fintype ι] [Fintype κ]
    (w₁ : ι → R) (w₂ : κ → R) (K₁ : ι → κ → R) (K₂ : κ → μ → R) (f : ι → R),
    kerOp w₂ K₂ (kerOp w₁ K₁ f) = kerOp w₁ (kerMul w₂ K₁ K₂) f
def ChainInt : Prop :=
  ∀ (R : Type) [CommRing R] (S : Subring R) (ι : ℕ → Type) [∀ j, Fintype (ι j)]
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → R) (D : ℕ → R),
    (∀ j i, D j * w j i ∈ S) → (∀ j a b, K j a b ∈ S) →
    ∀ f : ι 0 → R, (∀ i, f i ∈ S) → ∀ (m : ℕ) (y : ι m),
      (∏ j ∈ Finset.range m, D j) * chainOp w K m f y ∈ S
def kerOpM {R ι κ M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Fintype ι]
    (w : ι → R) (K : ι → κ → (M →ₗ[R] N)) (f : ι → M) : κ → N :=
  fun j => ∑ i, w i • K i j (f i)
def chainOpM {R : Type*} [CommSemiring R] {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {M : ℕ → Type*} [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → (M j →ₗ[R] M (j + 1))) :
    (m : ℕ) → (ι 0 → M 0) → (ι m → M m)
  | 0, f => f
  | m + 1, f => kerOpM (w m) (K m) (chainOpM w K m f)
def ChainIntM : Prop :=
  ∀ (R : Type) [CommRing R] (S : Subring R) (ι : ℕ → Type) [∀ j, Fintype (ι j)]
    (M : ℕ → Type) [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    (Λ : ∀ j, AddSubgroup (M j)) (w : ∀ j, ι j → R)
    (K : ∀ j, ι j → ι (j + 1) → (M j →ₗ[R] M (j + 1))) (D : ℕ → R),
    (∀ j, ∀ s ∈ S, ∀ x ∈ Λ j, s • x ∈ Λ j) →
    (∀ j i, D j * w j i ∈ S) → (∀ j a b, ∀ x ∈ Λ j, K j a b x ∈ Λ (j + 1)) →
    ∀ f : ι 0 → M 0, (∀ i, f i ∈ Λ 0) → ∀ (m : ℕ) (y : ι m),
      (∏ j ∈ Finset.range m, D j) • chainOpM w K m f y ∈ Λ m
def OrbitSum : Prop :=
  ∀ (H X : Type) [Group H] [Fintype H] [MulAction H X] [Fintype X] (k : Type) [Field k]
    [CharZero k] (F : X → k), (∀ (a : H) (x : X), F (a • x) = F x) →
    (Fintype.card H : k)⁻¹ * ∑ x, F x =
      ∑ᶠ o : MulAction.orbitRel.Quotient H X,
        (Nat.card (MulAction.stabilizer H (Quotient.out o)) : k)⁻¹ * F (Quotient.out o)
section Adelic
variable {G : Type} [Group G] {Γ K : Subgroup G}
def thetaLiftAMF {k W M : Type} [Field k] [AddCommGroup W] [Module k W] [AddCommGroup M]
    [Module k M] [Fintype (Formalism.UG.ClassSet Γ K)] (s : Formalism.UG.ClassSet Γ K → G)
    (θ : G → W →ₗ[k] M) (f : G → W) : M :=
  ∑ c, (Nat.card (Formalism.UG.stabAt Γ K (s c)) : k)⁻¹ • θ (s c) (f (s c))
end Adelic
def ClassSumIndep : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [Field k] (M : Type) [AddCommGroup M]
    [Module k M] [Fintype (Formalism.UG.ClassSet Γ K)] (F : G → M),
    (∀ (γ : Γ) (g : G) (κ : K), F ((γ : G) * g * κ) = F g) →
    ∀ s s' : Formalism.UG.ClassSet Γ K → G, (∀ c, DoubleCoset.mk Γ K (s c) = c) →
      (∀ c, DoubleCoset.mk Γ K (s' c) = c) →
      ∑ c, (Nat.card (Formalism.UG.stabAt Γ K (s c)) : k)⁻¹ • F (s c) =
        ∑ c, (Nat.card (Formalism.UG.stabAt Γ K (s' c)) : k)⁻¹ • F (s' c)
def ThetaLiftAMFIndep : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [Field k] (W M : Type) [AddCommGroup W]
    [Module k W] [AddCommGroup M] [Module k M] (ρ : Representation k Γ W)
    [Fintype (Formalism.UG.ClassSet Γ K)] (θ : G → W →ₗ[k] M),
    (∀ (γ : Γ) (g : G) (κ : K) (w : W), θ ((γ : G) * g * κ) (ρ γ w) = θ g w) →
    ∀ f ∈ Formalism.UG.AMF k Γ K ρ,
    ∀ s s' : Formalism.UG.ClassSet Γ K → G, (∀ c, DoubleCoset.mk Γ K (s c) = c) →
      (∀ c, DoubleCoset.mk Γ K (s' c) = c) →
      thetaLiftAMF s θ f = thetaLiftAMF s' θ f
def ThetaLiftAMFKIndep : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [Field k] (W M : Type) [AddCommGroup W]
    [Module k W] [AddCommGroup M] [Module k M] (ρK : Representation k K W)
    [Fintype (Formalism.UG.ClassSet Γ K)] (θ : G → W →ₗ[k] M),
    (∀ (γ : Γ) (g : G) (κ : K) (w : W), θ ((γ : G) * g * κ) (ρK κ⁻¹ w) = θ g w) →
    ∀ f ∈ Formalism.UG.AMFK k Γ K ρK,
    ∀ s s' : Formalism.UG.ClassSet Γ K → G, (∀ c, DoubleCoset.mk Γ K (s c) = c) →
      (∀ c, DoubleCoset.mk Γ K (s' c) = c) →
      thetaLiftAMF s θ f = thetaLiftAMF s' θ f
def orbLift (H : Type*) {X : Type*} [Group H] [MulAction H X] (s : Finset X) (f Θ : X → ℂ) : ℂ :=
  ∑ x ∈ s, ((Nat.card (MulAction.stabilizer H x) : ℕ) : ℂ)⁻¹ * f x * Θ x
def OrbLiftIndep : Prop :=
  ∀ (H X : Type) [Group H] [MulAction H X] (A : Set X), (∀ (a : H), ∀ x ∈ A, a • x ∈ A) →
    ∀ (f Θ : X → ℂ), (∀ (a : H) (x : X), f (a • x) = f x) → (∀ (a : H) (x : X), Θ (a • x) = Θ x) →
    ∀ s s' : Finset X,
      (∀ x ∈ s, x ∈ A) → (∀ x ∈ A, ∃! y, y ∈ s ∧ ∃ a : H, a • y = x) →
      (∀ x ∈ s', x ∈ A) → (∀ x ∈ A, ∃! y, y ∈ s' ∧ ∃ a : H, a • y = x) →
      orbLift H s f Θ = orbLift H s' f Θ
section Lat
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
def autL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) :
    Set (V ≃ₗ[K] V) :=
  {g | g ∈ Formalism.HermitianLatticesTheory.isom h ∧ Formalism.HermitianLatticesTheory.gmap g L = L}
def latWt (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) : ℂ :=
  ((Nat.card (autL h L) : ℕ) : ℂ)⁻¹
def IsClassReps (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (s : Finset (Submodule (NumberField.RingOfIntegers K) V)) : Prop :=
  (∀ M ∈ s, M ∈ Formalism.HermitianLatticesTheory.genus h L) ∧
    ∀ M ∈ Formalism.HermitianLatticesTheory.genus h L, ∃! N, N ∈ s ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g N = M
def latLift (h : V →ₗ⋆[K] V →ₗ[K] K) (s : Finset (Submodule (NumberField.RingOfIntegers K) V))
    (f Θ : Submodule (NumberField.RingOfIntegers K) V → ℂ) : ℂ :=
  ∑ L ∈ s, latWt h L * f L * Θ L
def thetaLift (h : V →ₗ⋆[K] V →ₗ[K] K) (s : Finset (Submodule (NumberField.RingOfIntegers K) V))
    (f : Submodule (NumberField.RingOfIntegers K) V → ℂ) (τ : ℂ) : ℂ :=
  latLift h s f (fun L => Formalism.HermitianLatticesTheory.thetaL h L 0 τ)
def latIp (h : V →ₗ⋆[K] V →ₗ[K] K) (s : Finset (Submodule (NumberField.RingOfIntegers K) V))
    (f g : Submodule (NumberField.RingOfIntegers K) V → ℂ) : ℂ :=
  ∑ L ∈ s, latWt h L * star (f L) * g L
end Lat
def LatLiftIndep : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (f Θ : Submodule (NumberField.RingOfIntegers K) V → ℂ),
    (∀ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ M, f (Formalism.HermitianLatticesTheory.gmap g M) = f M) →
    (∀ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ M, Θ (Formalism.HermitianLatticesTheory.gmap g M) = Θ M) →
    ∀ s s', IsClassReps h L s → IsClassReps h L s' → latLift h s f Θ = latLift h s' f Θ
def ThetaLiftIndep : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → ∀ (L : Submodule (NumberField.RingOfIntegers K) V)
    (f : Submodule (NumberField.RingOfIntegers K) V → ℂ),
    (∀ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ M, f (Formalism.HermitianLatticesTheory.gmap g M) = f M) →
    ∀ s s', IsClassReps h L s → IsClassReps h L s' → ∀ τ : ℂ, thetaLift h s f τ = thetaLift h s' f τ
def ClassRepsDefinite : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
      (∃ s, IsClassReps h L s) ∧
      (∀ M ∈ Formalism.HermitianLatticesTheory.genus h L, ∃ n : ℕ, 0 < n ∧ latWt h M = (n : ℂ)⁻¹) ∧
      (∃ D : ℕ, 0 < D ∧ ∀ M ∈ Formalism.HermitianLatticesTheory.genus h L, ∃ z : ℤ, (D : ℂ) * latWt h M = z)
def LatSeeSaw : Prop :=
  ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    [AddCommGroup V'] [Module K V'] [Module (NumberField.RingOfIntegers K) V']
    [IsScalarTower (NumberField.RingOfIntegers K) K V']
    (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K)
    (s : Finset (Submodule (NumberField.RingOfIntegers K) V))
    (s' : Finset (Submodule (NumberField.RingOfIntegers K) V'))
    (k : Submodule (NumberField.RingOfIntegers K) V → Submodule (NumberField.RingOfIntegers K) V' → ℂ)
    (f : Submodule (NumberField.RingOfIntegers K) V → ℂ)
    (g : Submodule (NumberField.RingOfIntegers K) V' → ℂ),
    latIp h' s' (fun L' => latLift h s f (fun L => k L L')) g =
      latIp h s f (fun L => latLift h' s' g (fun L' => star (k L L')))
def gaussOp {𝔽 V : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) : V →ₗ[ℂ] V :=
  ∑ c : 𝔽ˣ, ψ (c : 𝔽) • ρ c
def gaussOpDual {𝔽 V : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) : V →ₗ[ℂ] V :=
  ∑ c : 𝔽ˣ, ψ (-(c : 𝔽)) • ρ c⁻¹
def GaussOp : Prop :=
  ∀ (𝔽 V : Type) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)), ψ ≠ 1 →
    ∀ v : V, ∑ c : 𝔽ˣ, ρ c v = 0 →
      gaussOp ψ ρ (gaussOpDual ψ ρ v) = (Fintype.card 𝔽 : ℂ) • v ∧
      gaussOpDual ψ ρ (gaussOp ψ ρ v) = (Fintype.card 𝔽 : ℂ) • v
def FFRamCancel : Prop :=
  ∀ (𝔽 U : Type) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [AddCommGroup U] [Module 𝔽 U]
    [Fintype (Module.Dual 𝔽 U)] (φ : Module.Dual 𝔽 U → ℂ),
    (∀ f, ∑ c : 𝔽ˣ, φ ((c : 𝔽) • f) = 0) → ∀ e : U, ∑ f with f e = 0, φ f = 0
def FFPlancherel : Prop :=
  ∀ (𝔽 U : Type) [Field 𝔽] [Fintype 𝔽] [AddCommGroup U] [Module 𝔽 U] [Fintype U]
    [Fintype (Module.Dual 𝔽 U)] (ψ : AddChar 𝔽 ℂ), ψ ≠ 1 →
    ∀ φ φ' : Module.Dual 𝔽 U → ℂ,
      ∑ e : U, star (∑ f, ψ (f e) * φ f) * (∑ f, ψ (f e) * φ' f) =
        (Fintype.card U : ℂ) * ∑ f, star (φ f) * φ' f
def downChain {𝕜 : Type*} [CommSemiring 𝕜] {E : ℕ → Type*} [∀ j, AddCommMonoid (E j)]
    [∀ j, Module 𝕜 (E j)] (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) : (m : ℕ) → (E m →ₗ[𝕜] E 0)
  | 0 => LinearMap.id
  | m + 1 => (downChain T m).comp (T m)
def RallisHyp {𝕜 E F P : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (θ : E →ₗ[𝕜] F) (S : Submodule 𝕜 E)
    (Pset : Finset P) (c L : 𝕜) (Z : P → 𝕜) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, inner 𝕜 (θ x) (θ y) = c * L * (∏ v ∈ Pset, Z v) * inner 𝕜 x y
def RallisAdj : Prop :=
  ∀ (𝕜 E F P : Type) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (θ : E →ₗ[𝕜] F) (S : Submodule 𝕜 E) (Pset : Finset P) (c L : 𝕜) (Z : P → 𝕜),
    RallisHyp θ S Pset c L Z → (∀ x ∈ S, LinearMap.adjoint θ (θ x) ∈ S) →
    ∀ x ∈ S, LinearMap.adjoint θ (θ x) = (c * L * ∏ v ∈ Pset, Z v) • x
def ChainScalar : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (E : ℕ → Type) [∀ j, NormedAddCommGroup (E j)]
    [∀ j, InnerProductSpace 𝕜 (E j)] [∀ j, FiniteDimensional 𝕜 (E j)]
    (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (S : ∀ j, Submodule 𝕜 (E j)) (c : ℕ → 𝕜),
    (∀ j, ∀ x ∈ S j, T j (LinearMap.adjoint (T j) x) = c j • x) →
    (∀ j, ∀ x ∈ S j, LinearMap.adjoint (T j) x ∈ S (j + 1)) →
    ∀ (m : ℕ), ∀ x ∈ S 0,
      downChain T m (LinearMap.adjoint (downChain T m) x) = (∏ j ∈ Finset.range m, c j) • x
def RowsQuot : Prop :=
  ∀ (𝕜 E F : Type) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (ι : E →ₗ[𝕜] F), Function.Injective (ι ∘ₗ LinearMap.adjoint ι) →
    LinearMap.range ι = ⊤ ∧ (LinearMap.ker ι)ᗮ = LinearMap.range (LinearMap.adjoint ι) ∧
      Module.finrank 𝕜 (E ⧸ LinearMap.ker ι) = Module.finrank 𝕜 F
def DetBlocks : Prop :=
  ∀ (𝕜 E σ : Type) [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    [Fintype σ] [DecidableEq σ] (Es : σ → Submodule 𝕜 E), DirectSum.IsInternal Es →
    ∀ (A : E →ₗ[𝕜] E) (c : σ → 𝕜), (∀ s, ∀ x ∈ Es s, A x = c s • x) →
      LinearMap.det A = ∏ s, c s ^ Module.finrank 𝕜 (Es s)
def DetChain : Prop :=
  ∀ (𝕜 E σ : Type) [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    [Fintype σ] [DecidableEq σ] (m : ℕ) (W : Fin m → Type) [∀ j, AddCommGroup (W j)]
    [∀ j, Module 𝕜 (W j)] [∀ j, FiniteDimensional 𝕜 (W j)]
    (Es : σ → Submodule 𝕜 E) (Ws : ∀ j, σ → Submodule 𝕜 (W j)),
    DirectSum.IsInternal Es → (∀ j, DirectSum.IsInternal (Ws j)) →
    (∀ j s, Module.finrank 𝕜 (Ws j s) = Module.finrank 𝕜 (Es s)) →
    ∀ (κ : 𝕜) (lam : Fin m → σ → 𝕜) (A : E →ₗ[𝕜] E) (B : ∀ j, W j →ₗ[𝕜] W j),
      (∀ s, ∀ x ∈ Es s, A x = (κ * ∏ j, lam j s) • x) →
      (∀ j s, ∀ x ∈ Ws j s, B j x = lam j s • x) →
      LinearMap.det A = κ ^ Module.finrank 𝕜 E * ∏ j, LinearMap.det (B j)
def GaussOpAdj : Prop :=
  ∀ (𝔽 V : Type) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)),
    (∀ (c : 𝔽ˣ) (x y : V), inner ℂ (ρ c x) (ρ c y) = inner ℂ x y) →
    LinearMap.adjoint (gaussOp ψ ρ) = gaussOpDual ψ ρ
def DetSwap : Prop :=
  ∀ (𝕜 E F : Type) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F)
    (h₁ : ∀ x ∈ (LinearMap.ker T)ᗮ, (LinearMap.adjoint T ∘ₗ T) x ∈ (LinearMap.ker T)ᗮ)
    (h₂ : ∀ y ∈ (LinearMap.ker (LinearMap.adjoint T))ᗮ,
      (T ∘ₗ LinearMap.adjoint T) y ∈ (LinearMap.ker (LinearMap.adjoint T))ᗮ),
    LinearMap.det ((LinearMap.adjoint T ∘ₗ T).restrict h₁) =
      LinearMap.det ((T ∘ₗ LinearMap.adjoint T).restrict h₂)
def EigenSwap : Prop :=
  ∀ (𝕜 E F : Type) [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E)
    (μ : 𝕜), μ ≠ 0 →
    Module.finrank 𝕜 (Module.End.eigenspace (B ∘ₗ A) μ) =
      Module.finrank 𝕜 (Module.End.eigenspace (A ∘ₗ B) μ)
end Formalism.ThetaLiftIndependence


