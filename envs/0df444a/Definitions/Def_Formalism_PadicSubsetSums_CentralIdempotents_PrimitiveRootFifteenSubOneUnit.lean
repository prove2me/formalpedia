-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
-- name    : Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:06.095888+00:00
-- url     : https://prove2.me/theorems/766ce472-6570-487e-88dc-030ccdc75c61
-- title:
--   Primitive Root Fifteen Sub One Unit
-- statement:
--   Definitions and structural lemmas for Primitive Root Fifteen Sub One Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/PrimitiveRootFifteenSubOneUnit.lean

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
open Polynomial
namespace Formalism.IrreducibleCountingLemmas.Z
def UnitRatio : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E),
    (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
    (∀ ζ : E, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) → ζ = 1 ∨ ζ = -1) →
    ∀ x : E, x ≠ 0 → IsIntegral ℤ (x / c x) → c x = x ∨ c x = -x
def MinusPart : Prop :=
  ∀ (E : Type) [Field E] (c : E →+* E) (s x : E), s ≠ 0 → c s = -s → c x = -x → c (x / s) = x / s
def EtaTildeValue : Prop :=
  ∀ (f : ℕ) (d : ℝ) (z : ℂ), 4 ∣ f → 0 < d → z ^ 2 = -(d : ℂ) → (z / (‖z‖ : ℂ)) ^ f = 1
def CircleCharExtends : Prop :=
  ∀ (A : Type) [CommGroup A] (H : Subgroup A) (χ : H →* Circle),
    ∃ χ' : A →* Circle, ∀ h : H, χ' (h : A) = χ h
def IdealSqrt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (I J : Ideal R), I ^ 2 = J ^ 2 → I = J
def SatakeCharpoly : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (α : Fin n → R) (s : R),
    ∏ j, (1 - C (α j * s ^ (n - 1)) * X) =
      ∑ k ∈ Finset.range (n + 1),
        C ((-1) ^ k * s ^ (k * (k - 1)) *
          (s ^ (k * (n - k)) * (Finset.univ.val.map α).esymm k)) * X ^ k
def expo (D : Multiset ℕ) : Multiset ℤ :=
  D.bind fun d => (Multiset.range d).map fun a : ℕ => (d : ℤ) - 1 - 2 * (a : ℤ)
def SpehMultiplicity : Prop :=
  ∀ (D : Multiset ℕ) (d : ℕ), 1 ≤ d →
    (D.count d : ℤ) = ((expo D).count ((d : ℤ) - 1) : ℤ) - ((expo D).count ((d : ℤ) + 1) : ℤ)
def CharpolyCoeffClosure : Prop :=
  ∀ (G : Type) [TopologicalSpace G] (R : Type) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (X : Type) [Fintype X] (n : ℕ)
    (r : X → G → Matrix (Fin n) (Fin n) R) (T : Subring (X → R)) (D : Set G),
    (∀ x, Continuous (r x)) → IsClosed (T : Set (X → R)) → Dense D →
    (∀ g ∈ D, ∀ j : ℕ, (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T) →
    ∀ (g : G) (j : ℕ), (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T
def TClosed : Prop :=
  ∀ (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    (X : Type) [Fintype X] (T : Submodule O (X → O)), T.FG → IsClosed (T : Set (X → O))
def SameResidue : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [Fintype X] (T : Subalgebra O (X → O)),
    IsLocalRing T → ∀ a ∈ T, ∀ x y : X, IsLocalRing.residue O (a x) = IsLocalRing.residue O (a y)
def BrauerNesbitt : Prop :=
  ∀ (k : Type) [Field k] (G : Type) [Group G] (V W : Type) [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (τ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) τ.asModule →
    (∀ g, (ρ g).charpoly = (τ g).charpoly) →
    ∃ e : V ≃ₗ[k] W, ∀ g, e.toLinearMap ∘ₗ ρ g = τ g ∘ₗ e.toLinearMap
def BrauerNesbittAlg : Prop :=
  ∀ (k A V W : Type) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W],
    IsSemisimpleModule A V → IsSemisimpleModule A W →
    (∀ a : A, (Algebra.lsmul k k V a).charpoly = (Algebra.lsmul k k W a).charpoly) →
    Nonempty (V ≃ₗ[A] W)
def BCInjective : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (α β : Fin m → K) (C : Multiset K),
    (∀ i, α i ≠ 0) → (∀ i, β i ≠ 0) →
    Multiset.map α Finset.univ.val + Multiset.map (fun i => (α i)⁻¹) Finset.univ.val + C =
      Multiset.map β Finset.univ.val + Multiset.map (fun i => (β i)⁻¹) Finset.univ.val + C →
    ∃ σ : Equiv.Perm (Fin m), ∀ i, β (σ i) = α i ∨ β (σ i) = (α i)⁻¹
def G4primeNoFixed : Prop :=
  ∀ (r t : ℕ) (q : ℝ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (F : Module.End ℂ V) (c : ℂ), r < t → 1 < q →
    (∀ α : ℂ, F.HasEigenvalue α →
      q ^ (-(((r : ℝ) - 1) / 2)) ≤ ‖α‖ ∧ ‖α‖ ≤ q ^ (((r : ℝ) - 1) / 2)) →
    (‖c‖ = q ^ (((t : ℝ) - 1) / 2) ∨ ‖c‖ = q ^ (-(((t : ℝ) - 1) / 2)) ∨
      ‖c‖ = q ^ (((t : ℝ) + 1) / 2) ∨ ‖c‖ = q ^ (-(((t : ℝ) + 1) / 2))) →
    ∀ v : V, c • F v = v → v = 0
def HullBound : Prop :=
  ∀ (r : ℕ) (x : Fin r → ℝ),
    x ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin r) =>
      fun i : Fin r => ((r : ℝ) - 1) / 2 - ((σ i : ℕ) : ℝ)) →
    ∀ i, |x i| ≤ ((r : ℝ) - 1) / 2
def EulerConvergence : Prop :=
  ∀ (ι : Type) (r t : ℕ) (q : ι → ℝ) (α : ι → Fin r → ℂ),
    Odd r → Odd t → r < t → (∀ v, 2 ≤ q v) → Summable (fun v => (q v) ^ (-2 : ℝ)) →
    (∀ v i, ‖α v i‖ ≤ (q v) ^ (((r : ℝ) - 1) / 2)) →
    Summable (fun v => ‖(∏ i, (1 - α v i * (((q v) ^ (-(((t : ℝ) + 1) / 2)) : ℝ) : ℂ))⁻¹) - 1‖) ∧
    Multipliable (fun v => ∏ i, (1 - α v i * (((q v) ^ (-(((t : ℝ) + 1) / 2)) : ℝ) : ℂ))⁻¹) ∧
    (∏' v, ∏ i, (1 - α v i * (((q v) ^ (-(((t : ℝ) + 1) / 2)) : ℝ) : ℂ))⁻¹) ≠ 0
def block (q : ℝ) (μ : ℂ) (d : ℕ) : Multiset ℂ :=
  (Multiset.range d).map fun i : ℕ => μ * ((q ^ (((d : ℝ) - 1) / 2 - (i : ℝ)) : ℝ) : ℂ)
def ExponentClash : Prop :=
  ∀ (r t a : ℕ) (q : ℝ) (μ : ℂ) (A A' : Multiset ℂ), r < t → 1 ≤ a → 1 < q → ‖μ‖ = 1 →
    (∀ x ∈ A, ‖x‖ ≤ q ^ (((r : ℝ) - 1) / 2)) →
    A + block q μ t ≠ A' + block q μ (t + 2 * a)
def SizeCount : Prop :=
  ∀ (r t : ℕ) (q : ℝ) (μ : ℂ) (A : Multiset ℂ) (I : Type) [Fintype I] (d : I → ℕ)
    (B : I → Multiset ℂ), r < t → 1 < q → ‖μ‖ = 1 → (∀ x ∈ A, ‖x‖ ≤ q ^ (((r : ℝ) - 1) / 2)) →
    (∀ i, 1 ≤ d i) → (∀ i, B i ≠ 0) → (∀ i, ∀ β ∈ B i, ‖β‖ = 1) →
    A + block q μ t = ∑ i, (B i).bind (fun β => block q β (d i)) →
    ∃ i₀, d i₀ = t ∧ B i₀ = {μ} ∧ ∀ i, i ≠ i₀ → d i < t
def PoleRun : Prop :=
  ∀ (t d a : ℕ) (w₁ : ℤ) (J : Set ℤ), a < d → ((t : ℚ) + 1) / 2 = ((d : ℚ) + 1) / 2 - a →
    (t ≤ d ∧ d % 2 = t % 2) ∧
    ((∀ j : ℤ, |2 * j - (2 * w₁ + t - 1)| ≤ (d : ℤ) - 1 → j ∈ J) → w₁ - 1 ∉ J → d = t)
def GoodCuspidal : Prop :=
  ∀ (k : Type) [Field k] (P : Type) [Nonempty P] (r : ℕ) (f : P → k[X]) (I : Type) [Fintype I]
    (n d : I → ℕ) (h : P → I → k[X]),
    (∀ v, (f v).natDegree = r) → (∀ v, Squarefree (f v)) → (∀ v, f v = ∏ i, h v i ^ d i) →
    (∀ v i, (h v i).natDegree = n i) → (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ d i) →
    (¬ ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ r ∧ ∀ v, ∃ g : k[X], g ∣ f v ∧ g.natDegree = a) →
    (∀ i, d i = 1) ∧ Fintype.card I ≤ 1
def SplitEigenAnnihilator : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (A B : Submodule K V)
    (γ₀ γ : Module.End K V) (c : K), IsCompl A B → (∀ v ∈ A, γ₀ v = v) → (∀ v ∈ A, γ v = v) →
    (∀ v ∈ B, γ v = c • v) → (γ₀ - 1) * (γ - algebraMap K (Module.End K V) c) = 0
def UnitEvalOfMultiplicity : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (t : ℕ) (c : O) (s' : O[X]), s'.Monic →
    ((s' * (X - C c) ^ t).map (IsLocalRing.residue O)).rootMultiplicity (IsLocalRing.residue O c) = t →
    IsUnit (s'.eval c)
def ev {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (x : X) : T →+* O :=
  (Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom
def FactorOverLocalSubalgebra : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)),
    IsLocalRing T → ∀ (t : ℕ) (c : O) (F : T[X]) (s : X' → O[X]),
    (∀ x, F.map (ev T x) = s x * (X - C c) ^ t) → (∀ x, IsUnit ((s x).eval c)) →
    ∃ P : T[X], F = P * (X - C (algebraMap O T c)) ^ t ∧ IsUnit (P.eval (algebraMap O T c)) ∧
      ∀ x, P.map (ev T x) = s x
def CharpolyFactorAnnihilator : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A B : Submodule K V) (γ₀ γ : Module.End K V) (c cγ : K) (t : ℕ) (P : K[X]), IsCompl A B →
    (∀ v ∈ A, γ₀ v ∈ A) → (∀ v ∈ A, γ v ∈ A) → (∀ v ∈ B, γ₀ v = c • v) → (∀ v ∈ B, γ v = cγ • v) →
    Module.finrank K B = t → γ₀.charpoly = P * (X - C c) ^ t →
    (aeval γ₀ P) * (γ - algebraMap K (Module.End K V) cγ) = 0
def HomKilledOfUnitEval : Prop :=
  ∀ (T R Y M : Type) [CommRing T] [Ring R] [Algebra T R] [AddCommGroup Y] [Module R Y]
    [AddCommGroup M] [Module R M] [Module T M] [IsScalarTower T R M]
    (φ : Y →ₗ[R] M) (γ₀ : R) (P : T[X]) (c : T) (y : Y),
    (∀ m : M, γ₀ • m = c • m) → IsUnit (P.eval c) → (aeval γ₀ P) • y = 0 → φ y = 0
def PrimitiveRootFifteenSubOneUnit : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ζ : R), IsPrimitiveRoot ζ 15 → IsUnit (ζ - 1)
def TwistInvertible : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (γ₀ : Module.End k V) (c : k), c ≠ 0 → ¬ γ₀.HasEigenvalue c →
    Function.Bijective fun v : V => c⁻¹ • γ₀ v - v
def CentreKills : Prop :=
  ∀ (k G : Type) [CommRing k] [Group G] (A : Rep k G) (z : G), z ∈ Subgroup.center G →
    Function.Bijective (fun a : A => A.ρ z a - a) → ∀ j : ℕ, Subsingleton (groupCohomology A j)
def FirstCohomologyVanishesNormal : Prop :=
  ∀ (G M : Type) [Group G] [AddCommGroup M] [DistribMulAction G M] (N : Subgroup G) [N.Normal]
    (z : G), z ∈ N → (∀ u ∈ N, u * z = z * u) → Function.Bijective (fun m : M => z • m - m) →
    (∀ m : M, (∀ u ∈ N, u • m = m) → m = 0) ∧
    ∀ f : G → M, (∀ g h, f (g * h) = f g + g • f h) → ∃! m : M, ∀ g, f g = g • m - m
def SimpleInSum : Prop :=
  ∀ (R S : Type) [Ring R] [AddCommGroup S] [Module R S] [IsSimpleModule R S] (ι : Type) [Fintype ι]
    (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (f : S →ₗ[R] (∀ i, V i)),
    Function.Injective f → ∃ i, Function.Injective (LinearMap.proj i ∘ₗ f)
def SegmentNumerics : Prop :=
  ∀ (r t d n₁ j : ℕ) (A : Multiset ℕ), 1 < r → 2 ≤ t → j < d → (d : ℤ) - 1 - 2 * j = (t : ℤ) - 1 →
    A.sum = n₁ → (∀ a ∈ A, 1 ≤ a) → 1 ≤ n₁ → d • A ≤ r ::ₘ Multiset.replicate t 1 →
    n₁ = 1 ∧ d = t
def SingletonDecomposition : Prop :=
  ∀ (I : Type) [Fintype I] (d : I → ℕ) (A : I → Multiset ℕ) (r : ℕ), (∀ i, 1 ≤ d i) →
    (∀ i, A i ≠ 0) → ∑ i, d i • A i = {r} → Fintype.card I = 1 ∧ ∀ i, d i = 1 ∧ A i = {r}
def RunCount : Prop :=
  ∀ (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ), Antitone lam → 1 ≤ t → p + t ≤ n →
    (∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    (Finset.univ.filter fun i => c < lam i).card = p ∧
      (Finset.univ.filter fun i => lam i < c).card = n - p - t
def CuspCount : Prop :=
  ∀ (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ), Antitone lam → 1 ≤ t → p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    ∀ (c₀ : ℤ) (i : ℕ), 1 ≤ i →
      ¬ ((Finset.univ.filter fun j => c₀ < lam j).card + i ≤ p ∧
        (Finset.univ.filter fun j => lam j < c₀).card + i ≤ n - p - t)
def ZNumerology : Prop :=
  ∀ (r t n r' : ℕ), 0 < r → r < t → n = r + t → 2 * r' ≤ r →
    r + 2 * t = 2 * n - r ∧ r < 2 * n - r ∧ (((2 * n - r : ℕ) : ℚ) - n) / 2 = (t : ℚ) / 2 ∧
      r' + t ≤ n ∧ ∀ i : ℕ, 1 ≤ i → (t : ℚ) + 1 ≤ 2 * ((t : ℚ) / 2) + i
def SumSimpleLength : Prop :=
  ∀ (R A : Type) [Ring R] [AddCommGroup A] [Module R A] (ι : Type) [Fintype ι]
    (S : ι → Submodule R A), (∀ i, IsSimpleModule R (S i)) → (⨆ i, S i) = ⊤ →
    Module.length R A ≤ (Fintype.card ι : ℕ∞)
def SimpleOutside : Prop :=
  ∀ (R A : Type) [Ring R] [AddCommGroup A] [Module R A] [IsSemisimpleModule R A]
    (Th : Submodule R A), Th ≠ ⊤ → ∃ P : Submodule R A, IsSimpleModule R P ∧ Disjoint P Th
def ThetaAdjoint : Prop :=
  ∀ (M N : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N] (θ : M →ₗ[ℂ] N) (lam : ℂ),
    (∀ f f' : M, inner ℂ f' (LinearMap.adjoint θ (θ f)) = lam * inner ℂ f' f) →
    (LinearMap.adjoint θ ∘ₗ θ = lam • LinearMap.id) ∧ (lam ≠ 0 → Function.Injective θ) ∧
      ∀ F : N, (∀ f : M, inner ℂ (θ f) F = 0) ↔ LinearMap.adjoint θ F = 0
def InjDimBij : Prop :=
  ∀ (K M N : Type) [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [FiniteDimensional K M] [FiniteDimensional K N] (θ : M →ₗ[K] N) (θ' : N →ₗ[K] M) (lam : K),
    lam ≠ 0 → θ' ∘ₗ θ = lam • LinearMap.id → Module.finrank K N ≤ Module.finrank K M →
    Function.Bijective θ
def ZCount : Prop :=
  ∀ (K M N : Type) [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [FiniteDimensional K M] [FiniteDimensional K N] (I Zg : Type) [Fintype I] [Fintype Zg]
    (Ms : I → Submodule K M) (Nx : Zg → Submodule K N) (e : Zg ≃ I) (θ : M →ₗ[K] N),
    iSupIndep Ms → (⨆ s, Ms s) = ⊤ → iSupIndep Nx →
    (∀ x, Set.BijOn θ (Ms (e x) : Set M) (Nx x : Set N)) →
    LinearMap.range θ = ⨆ x, Nx x ∧ ∑ x, Module.finrank K (Nx x) = Module.finrank K M
def PermDetOnePlus : Prop :=
  ∀ (m : ℕ) (σ : Equiv.Perm (Fin m)),
    ((1 : Matrix (Fin m) (Fin m) ℚ) + σ.permMatrix ℚ).det ≠ 0 ↔ ∀ j ∈ σ.cycleType, Odd j
def ResultantConjugate : Prop :=
  ∀ (K : Type) [Field K] (c : K →+* K) (a b : ℕ) (α : Fin a → K) (β : Fin b → K)
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)),
    (∀ i, α i ≠ 0) → (∀ j, β j ≠ 0) →
    (∀ i, c (α i) = (α (σ i))⁻¹) → (∀ j, c (β j) = (β (τ j))⁻¹) →
    (∏ i, ∏ j, (α i - β j)) =
      (-1) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a * c (∏ i, ∏ j, (α i - β j))
def LaplaceRows : Prop :=
  ∀ (R : Type) [CommRing R] (a b : ℕ) (M : Matrix (Fin (a + b)) (Fin (a + b)) R),
    M.det = ∑ J : {J : Finset (Fin (a + b)) // J.card = a},
      (-1 : R) ^ (a * (a - 1) / 2 + ∑ j ∈ J.1, (j : ℕ)) *
        (M.submatrix (Fin.castAdd b) (J.1.orderEmbOfFin J.2)).det *
        (M.submatrix (Fin.natAdd a)
          ((J.1ᶜ).orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin, J.2]; omega))).det
def VandermondeSplit : Prop :=
  ∀ (R : Type) [CommRing R] (a b : ℕ) (z : Fin (a + b) → R),
    (Matrix.vandermonde z).det =
      (Matrix.vandermonde (z ∘ Fin.castAdd b)).det * (Matrix.vandermonde (z ∘ Fin.natAdd a)).det *
        ∏ i : Fin a, ∏ j : Fin b, (z (Fin.natAdd a j) - z (Fin.castAdd b i))
end Formalism.IrreducibleCountingLemmas.Z


