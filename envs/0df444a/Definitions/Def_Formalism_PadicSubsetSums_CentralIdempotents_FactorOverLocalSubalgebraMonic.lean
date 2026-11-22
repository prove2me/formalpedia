-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
-- name    : Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:05:52.630931+00:00
-- url     : https://prove2.me/theorems/30f60d02-9d2a-43f3-8758-56b4016b439f
-- title:
--   Factor Over Local Subalgebra Monic
-- statement:
--   Definitions and structural lemmas for Factor Over Local Subalgebra Monic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/FactorOverLocalSubalgebraMonic.lean

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
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
def OpenSubgroupContinuous : Prop :=
  ∀ (A : Type) [Group A] [TopologicalSpace A] [IsTopologicalGroup A] (U : Subgroup A)
    (χ : A →* Circle), IsOpen (U : Set A) → Continuous (fun u : U => χ (u : A)) → Continuous χ
def CircleCharExtendsOpen : Prop :=
  ∀ (A : Type) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (U : Subgroup A)
    (χ : U →* Circle), IsOpen (U : Set A) → Continuous χ →
    ∃ χ' : A →* Circle, Continuous χ' ∧ ∀ u : U, χ' (u : A) = χ u
def RunJumps : Prop :=
  ∀ (n p t : ℕ) (a : Fin n → ℤ) (c : ℤ), Antitone a → 1 ≤ t → p + t ≤ n →
    (∀ i : Fin n, a i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    (∀ j : Fin n, ((p : ℤ) - c ≤ (j : ℤ) - a j ∧ (j : ℤ) - a j < (p : ℤ) - c + t) ↔
      (p ≤ (j : ℕ) ∧ (j : ℕ) < p + t)) ∧
    (∀ k : ℕ, k < t → ∃ j : Fin n, (j : ℤ) - a j = (p : ℤ) - c + k) ∧
    ∀ j : Fin n, (j : ℤ) - a j ≠ (p : ℤ) - c - 1 ∧ (j : ℤ) - a j ≠ (p : ℤ) - c + t
def BlockIsRun : Prop :=
  ∀ (n p t : ℕ) (a : Fin n → ℤ) (c w : ℤ), Antitone a → p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, a i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    (∀ k : ℕ, k < t → ∃ j : Fin n, (j : ℤ) - a j = w + k) →
    w = (p : ℤ) - c ∧
    ∀ j : Fin n, (w ≤ (j : ℤ) - a j ∧ (j : ℤ) - a j < w + t) ↔ (p ≤ (j : ℕ) ∧ (j : ℕ) < p + t)
def ResidueCharpolyEq : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)),
    IsLocalRing T → ∀ (G : Type) (n : ℕ) (r : X' → G → Matrix (Fin n) (Fin n) O),
    (∀ (g : G) (j : ℕ), (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T) →
    ∀ (x y : X') (g : G),
      Matrix.charpolyRev ((r x g).map (IsLocalRing.residue O)) =
        Matrix.charpolyRev ((r y g).map (IsLocalRing.residue O)) ∧
      ((r x g).map (IsLocalRing.residue O)).charpoly =
        ((r y g).map (IsLocalRing.residue O)).charpoly
def BrauerNesbittCharZero : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (G : Type) [Group G] (V W : Type) [AddCommGroup V]
    [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (τ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) τ.asModule →
    (∀ g, (ρ g).charpoly = (τ g).charpoly) →
    ∃ e : V ≃ₗ[k] W, ∀ g, e.toLinearMap ∘ₗ ρ g = τ g ∘ₗ e.toLinearMap
def BrauerNesbittFinite : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (G : Type) [Group G] (V W : Type) [AddCommGroup V]
    [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (τ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) τ.asModule →
    (∀ g, (ρ g).charpoly = (τ g).charpoly) →
    ∃ e : V ≃ₗ[k] W, ∀ g, e.toLinearMap ∘ₗ ρ g = τ g ∘ₗ e.toLinearMap
def RootCoefficient : Prop :=
  ∀ m i : ℤ, 2 * ((m - i) + (m - 1) - (i - 1)) + 2 + 2 = 4 * (m - i + 1)
def RootSumUnitary : Prop :=
  ∀ (m : ℕ) (i : Fin m),
    ((∑ a : Fin m, ∑ b : Fin m, if a < b then
        (2 : ℤ) • ((Pi.single a 1 : Fin m → ℤ) - Pi.single b 1) +
          (2 : ℤ) • ((Pi.single a 1 : Fin m → ℤ) + Pi.single b 1) else 0) +
      ∑ a : Fin m, ((2 : ℤ) • (Pi.single a 1 : Fin m → ℤ) +
        (1 : ℤ) • ((2 : ℤ) • (Pi.single a 1 : Fin m → ℤ)))) i = 4 * ((m : ℤ) - (i : ℤ))
def HullBoundSigned : Prop :=
  ∀ (r m : ℕ) (x : Fin m → ℝ), r = 2 * m + 1 →
    x ∈ convexHull ℝ (Set.range fun p : Equiv.Perm (Fin m) × (Fin m → ℤˣ) =>
      fun i : Fin m => (((p.2 i : ℤˣ) : ℤ) : ℝ) * ((m : ℝ) - ((p.1 i : ℕ) : ℝ))) →
    ∀ i, |x i| ≤ ((r : ℝ) - 1) / 2
def InertParameterBound : Prop :=
  ∀ (r m : ℕ) (q : ℝ) (x : Fin m → ℝ) (α : Fin m → ℂ), r = 2 * m + 1 → 1 < q →
    (∀ i, ‖α i‖ = q ^ (x i)) →
    x ∈ convexHull ℝ (Set.range fun p : Equiv.Perm (Fin m) × (Fin m → ℤˣ) =>
      fun i : Fin m => (((p.2 i : ℤˣ) : ℤ) : ℝ) * ((m : ℝ) - ((p.1 i : ℕ) : ℝ))) →
    ∀ β ∈ Multiset.map α Finset.univ.val + Multiset.map (fun i => (α i)⁻¹) Finset.univ.val + {1},
      ‖β‖ ≤ q ^ (((r : ℝ) - 1) / 2)
def SemisimpleQuotientSimple : Prop :=
  ∀ (R M Q : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    [IsSemisimpleModule R Q] [Nontrivial Q] (π : M →ₗ[R] Q),
    (∀ N N' : Submodule R M, IsCoatom N → IsCoatom N' → N = N') → Function.Surjective π →
    IsSimpleModule R Q
def inertFactor (q : ℝ) (ch s : ℂ) : ℂ :=
  (1 - ((q ^ 2 : ℝ) : ℂ) ^ (-s)) / (1 - ch * ((q ^ 2 : ℝ) : ℂ) ^ (-s))
def InertEulerQuotient : Prop :=
  ∀ (ι : Type) (q : ι → ℝ) (ch : ι → ℂ) (s : ℂ), (∀ v, 2 ≤ q v) → (∀ v, ‖ch v‖ = 1) →
    1 / 2 < s.re → Summable (fun v => (q v) ^ (-2 * s.re)) →
    Summable (fun v => ‖inertFactor (q v) (ch v) s - 1‖) ∧
    Multipliable (fun v => inertFactor (q v) (ch v) s) ∧
    (∏' v, inertFactor (q v) (ch v) s) ≠ 0
def InertEulerHolomorphic : Prop :=
  ∀ (ι : Type) (q : ι → ℝ) (ch : ι → ℂ), (∀ v, 2 ≤ q v) → (∀ v, ‖ch v‖ = 1) →
    (∀ σ : ℝ, 1 / 2 < σ → Summable (fun v => (q v) ^ (-2 * σ))) →
    DifferentiableOn ℂ (fun s => ∏' v, inertFactor (q v) (ch v) s) {s : ℂ | 1 / 2 < s.re}
def PoleTransfer : Prop :=
  ∀ (L Z R : ℂ → ℂ), ContinuousAt R 1 → R 1 ≠ 0 → (∀ s : ℂ, 1 < s.re → L s = Z s * R s) →
    Filter.Tendsto (fun s => ‖Z s‖) (nhdsWithin 1 {s : ℂ | 1 < s.re}) Filter.atTop →
    Filter.Tendsto (fun s => ‖L s‖) (nhdsWithin 1 {s : ℂ | 1 < s.re}) Filter.atTop
def GoodCuspidalOne : Prop :=
  ∀ (k : Type) [Field k] (P : Type) [Nonempty P] (r : ℕ) (f : P → k[X]) (I : Type) [Fintype I]
    (n d : I → ℕ) (h : P → I → k[X]), 1 ≤ r →
    (∀ v, (f v).natDegree = r) → (∀ v, Squarefree (f v)) → (∀ v, f v = ∏ i, h v i ^ d i) →
    (∀ v i, (h v i).natDegree = n i) → (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ d i) →
    (¬ ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ r ∧ ∀ v, ∃ g : k[X], g ∣ f v ∧ g.natDegree = a) →
    Fintype.card I = 1 ∧ ∀ i, d i = 1 ∧ n i = r
def CharpolyOverSubalgebra : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O))
    (n : ℕ) (M : X' → Matrix (Fin n) (Fin n) O),
    (∀ j : ℕ, (fun x => (Matrix.charpolyRev (M x)).coeff j) ∈ T) →
    ∃ F : T[X], F.Monic ∧ ∀ x, F.map (ev T x) = (M x).charpoly
def FactorOverLocalSubalgebraMonic : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)),
    IsLocalRing T → ∀ (t : ℕ) (c : O) (F : T[X]) (s : X' → O[X]), F.Monic →
    (∀ x, F.map (ev T x) = s x * (X - C c) ^ t) → (∀ x, IsUnit ((s x).eval c)) →
    ∃ P : T[X], P.Monic ∧ F = P * (X - C (algebraMap O T c)) ^ t ∧
      IsUnit (P.eval (algebraMap O T c)) ∧ ∀ x, P.map (ev T x) = s x
def FactorAnnihilatorFamily : Prop :=
  ∀ (O K : Type) [CommRing O] [IsLocalRing O] [Field K] [Algebra O K],
    Function.Injective (algebraMap O K) →
    ∀ (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)), IsLocalRing T →
    ∀ (V : X' → Type) [∀ x, AddCommGroup (V x)] [∀ x, Module K (V x)]
      [∀ x, FiniteDimensional K (V x)] (A B : ∀ x, Submodule K (V x))
      (γ₀ γ : ∀ x, Module.End K (V x)) (c cγ : O) (t : ℕ) (F : T[X]),
    (∀ x, (F.map (ev T x)).map (algebraMap O K) = (γ₀ x).charpoly) →
    (∀ x, IsCompl (A x) (B x)) → (∀ x, ∀ v ∈ A x, γ₀ x v ∈ A x) → (∀ x, ∀ v ∈ A x, γ x v ∈ A x) →
    (∀ x, ∀ v ∈ B x, γ₀ x v = algebraMap O K c • v) →
    (∀ x, ∀ v ∈ B x, γ x v = algebraMap O K cγ • v) →
    (∀ x, Module.finrank K (B x) = t) →
    (∀ x, ((F.map (ev T x)).map (IsLocalRing.residue O)).rootMultiplicity
      (IsLocalRing.residue O c) = t) →
    ∃ P : T[X], P.Monic ∧ F = P * (X - C (algebraMap O T c)) ^ t ∧
      IsUnit (P.eval (algebraMap O T c)) ∧
      ∀ x, (aeval (γ₀ x) ((P.map (ev T x)).map (algebraMap O K))) *
        (γ x - algebraMap K (Module.End K (V x)) (algebraMap O K cγ)) = 0
def CuspValueCount : Prop :=
  ∀ (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ), p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    ∀ c₀ : ℤ, (Finset.univ.filter fun j => lam j = c₀).card ≤ t
def CuspValueCountDual : Prop :=
  ∀ (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ), p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    ∀ c₀ : ℤ, (Finset.univ.filter fun j : Fin n => -lam (Fin.rev j) = c₀).card ≤ t
def CuspCountSym : Prop :=
  ∀ (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ), p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    ∀ (c₀ : ℤ) (i : ℕ), 1 ≤ i →
      ¬ ((Finset.univ.filter fun j => c₀ < lam j).card +
        (Finset.univ.filter fun j => lam j < c₀).card + 2 * i ≤ n - t)
def CuspCountDual : Prop :=
  ∀ (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ), p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    ∀ (c₀ : ℤ) (i : ℕ), 1 ≤ i →
      ¬ ((Finset.univ.filter fun j => c₀ < lam j).card + i ≤ n - p - t ∧
        (Finset.univ.filter fun j => lam j < c₀).card + i ≤ p)
def CuspCentre : Prop :=
  ∀ (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ), p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    ∀ c₀ : ℤ, (Finset.univ.filter fun j => c₀ < lam j).card +
        (Finset.univ.filter fun j => lam j < c₀).card ≤ n - t → c₀ = c
def ZCountRange : Prop :=
  ∀ (K M N : Type) [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [FiniteDimensional K M] [FiniteDimensional K N] (I Zg : Type) [Fintype I] [Fintype Zg]
    (Ms : I → Submodule K M) (Nx : Zg → Submodule K N) (e : Zg ≃ I) (θ : M →ₗ[K] N),
    iSupIndep Ms → (⨆ s, Ms s) = ⊤ → iSupIndep Nx →
    (∀ x, Set.BijOn θ (Ms (e x) : Set M) (Nx x : Set N)) →
    Function.Injective θ ∧ (LinearMap.range θ = ⨆ x, Nx x) ∧
      Module.finrank K (LinearMap.range θ) = ∑ x, Module.finrank K (Nx x) ∧
      Module.finrank K (LinearMap.range θ) = Module.finrank K M
end Formalism.IrreducibleCountingLemmas.Z


