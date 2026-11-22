-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
-- name    : Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:16.423264+00:00
-- url     : https://prove2.me/theorems/d2962f0d-75b2-4015-b951-979b77d4ea3f
-- title:
--   Invariant Series Bidegree One One
-- statement:
--   Definitions and structural lemmas for Invariant Series Bidegree One One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/InvariantSeriesBidegreeOneOne.lean

import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_EvenOddPowerQuotientEqualityCases
import Definitions.Def_Formalism_FormalGroupWitt_ShiftSOneLetter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
def EqNormalisedGeneral : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] (Ψ : Finset (E →+* ℂ))
    (A : Type) [CommGroup A] (ι : unitary E →* A) (χ : A →* ℂˣ)
    (G G' Γ Γ' : Type) [Group G] [Group G'] [Group Γ] [Group Γ']
    (j : Γ →* G) (j' : Γ' →* G') (dt : G →* A) (dt' : G' →* A)
    (dr : Γ →* unitary E) (dr' : Γ' →* unitary E)
    (V : Type) [AddCommGroup V] [Module ℂ V]
    (pull : Γ → Γ' → V →ₗ[ℂ] V) (Th : G → G' → V) (M M' : ℕ),
    (∀ γ, dt (j γ) = ι (dr γ)) → (∀ γ', dt' (j' γ') = ι (dr' γ')) →
    (∀ z : unitary E, ((χ (ι z) : ℂˣ) : ℂ) = ∏ τ ∈ Ψ, (τ (z : E))⁻¹) →
    (∀ γ γ' g g', pull γ γ' (Th g g') =
      ((∏ τ ∈ Ψ, τ (star ((dr γ : unitary E) : E))) ^ M' *
        (∏ τ ∈ Ψ, τ ((dr' γ' : unitary E) : E)) ^ M) • Th (j γ * g) (j' γ' * g')) →
    ∀ (a b : ℤ) (γ : Γ) (γ' : Γ') (g : G) (g' : G'),
      pull γ γ' ((((χ (dt g)) ^ a * (χ (dt' g')) ^ b : ℂˣ) : ℂ) • Th g g') =
        ((∏ τ ∈ Ψ, τ ((dr γ : unitary E) : E)) ^ (a - (M' : ℤ)) *
          (∏ τ ∈ Ψ, τ ((dr' γ' : unitary E) : E)) ^ (b + (M : ℤ))) •
          ((((χ (dt (j γ * g))) ^ a * (χ (dt' (j' γ' * g'))) ^ b : ℂˣ) : ℂ) •
            Th (j γ * g) (j' γ' * g'))
def EqNormalised : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] (Ψ : Finset (E →+* ℂ))
    (A : Type) [CommGroup A] (ι : unitary E →* A) (χ : A →* ℂˣ)
    (G G' Γ Γ' : Type) [Group G] [Group G'] [Group Γ] [Group Γ']
    (j : Γ →* G) (j' : Γ' →* G') (dt : G →* A) (dt' : G' →* A)
    (dr : Γ →* unitary E) (dr' : Γ' →* unitary E)
    (V : Type) [AddCommGroup V] [Module ℂ V]
    (pull : Γ → Γ' → V →ₗ[ℂ] V) (Th : G → G' → V) (M M' : ℕ),
    (∀ γ, dt (j γ) = ι (dr γ)) → (∀ γ', dt' (j' γ') = ι (dr' γ')) →
    (∀ z : unitary E, ((χ (ι z) : ℂˣ) : ℂ) = ∏ τ ∈ Ψ, (τ (z : E))⁻¹) →
    (∀ γ γ' g g', pull γ γ' (Th g g') =
      ((∏ τ ∈ Ψ, τ (star ((dr γ : unitary E) : E))) ^ M' *
        (∏ τ ∈ Ψ, τ ((dr' γ' : unitary E) : E)) ^ M) • Th (j γ * g) (j' γ' * g')) →
    ∀ (γ : Γ) (γ' : Γ') (g : G) (g' : G'),
      pull γ γ' ((((χ (dt g)) ^ (M' : ℤ) * (χ (dt' g')) ^ (-(M : ℤ)) : ℂˣ) : ℂ) • Th g g') =
        (((χ (dt (j γ * g))) ^ (M' : ℤ) * (χ (dt' (j' γ' * g'))) ^ (-(M : ℤ)) : ℂˣ) : ℂ) •
            Th (j γ * g) (j' γ' * g')
def ChiExists : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] (Ψ : Finset (E →+* ℂ))
    (A : Type) [CommGroup A] (ι : unitary E →* A) (K : Subgroup A),
    (∀ τ ∈ Ψ, ∀ x : E, τ (star x) = (starRingEnd ℂ) (τ x)) →
    Even Ψ.card →
    (∀ z : unitary E, ι z ∈ K → (z : E) = 1 ∨ (z : E) = -1) →
    ∃ χ : A →* Circle, (∀ k ∈ K, χ k = 1) ∧
      ∀ z : unitary E, ((χ (ι z) : Circle) : ℂ) = ∏ τ ∈ Ψ, (τ (z : E))⁻¹
open Classical in

def OrbitHalf : Prop :=
  ∀ (Emb : Type) [Fintype Emb] (φ c : Equiv.Perm Emb) (κ : Emb → ZMod 2) (τ₀ : Emb),
    (∀ τ, κ (φ τ) = κ τ + 1) → (∀ τ, κ (c τ) = κ τ + 1) →
    Even (univ.filter (fun τ => φ.SameCycle τ₀ τ)).card ∧
    2 * ((univ.filter (fun τ => φ.SameCycle τ₀ τ)).filter (fun τ => κ τ = 0)).card =
      (univ.filter (fun τ => φ.SameCycle τ₀ τ)).card ∧
    2 * (((univ.filter (fun τ => φ.SameCycle τ₀ τ)).image c).filter (fun τ => κ τ = 0)).card =
      (univ.filter (fun τ => φ.SameCycle τ₀ τ)).card
open Classical in

def ChiUnitSplitInert : Prop :=
  ∀ (Emb : Type) [Fintype Emb] (φ c : Equiv.Perm Emb) (κ : Emb → ZMod 2) (τ₀ : Emb),
    (∀ τ, κ (φ τ) = κ τ + 1) → (∀ τ, κ (c τ) = κ τ + 1) →
    Disjoint (univ.filter (fun τ => φ.SameCycle τ₀ τ))
      ((univ.filter (fun τ => φ.SameCycle τ₀ τ)).image c) →
    ∀ (e : ℤ) (val : Emb → ℤ),
      (∀ τ ∈ univ.filter (fun τ => φ.SameCycle τ₀ τ), val τ = e) →
      (∀ τ ∈ (univ.filter (fun τ => φ.SameCycle τ₀ τ)).image c, val τ = -e) →
      (∀ τ, τ ∉ univ.filter (fun τ => φ.SameCycle τ₀ τ) →
        τ ∉ (univ.filter (fun τ => φ.SameCycle τ₀ τ)).image c → val τ = 0) →
      ∑ τ ∈ univ.filter (fun τ => κ τ = 0), val τ = 0
def LiftTypes : Prop :=
  ∀ (U A : Type) [CommGroup U] [CommGroup A] (ι : U →* A) (n : U →* ℂˣ) (χ m : A →* ℂˣ)
    (e M M' : ℤ),
    (∀ z, χ (ι z) = (n z)⁻¹) → (∀ z, m (ι z) = χ (ι z) ^ e) →
    (∀ z, (m * χ ^ (-M')) (ι z) = χ (ι z) ^ (e - M') ∧ (m * χ ^ (-M')) (ι z) = (n z) ^ (-(e - M'))) ∧
    (∀ z, (m⁻¹ * χ ^ M) (ι z) = χ (ι z) ^ (-(e - M)) ∧ (m⁻¹ * χ ^ M) (ι z) = (n z) ^ (e - M)) ∧
    ∀ lam lam' ν : ℤ, ν = lam + (e - M') → ν = lam' + (e - M) → lam' - lam = M - M'
def EpsTeich : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∃ ε : (WittVector p (AlgebraicClosure (ZMod p)))ˣ,
      (ε : WittVector p (AlgebraicClosure (ZMod p))) ^ (p ^ 2 - 1) = -1 ∧
      WittVector.frobenius (WittVector.frobenius
        (ε : WittVector p (AlgebraicClosure (ZMod p)))) = -(ε : WittVector p (AlgebraicClosure (ZMod p)))
def FrobSqSolvable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (η : (WittVector p (AlgebraicClosure (ZMod p)))ˣ),
    ∃ ε : (WittVector p (AlgebraicClosure (ZMod p)))ˣ,
      WittVector.frobenius (WittVector.frobenius
        (ε : WittVector p (AlgebraicClosure (ZMod p)))) =
        (η : WittVector p (AlgebraicClosure (ZMod p))) * ε
def TypeTwist : Prop :=
  ∀ (K : Type) [Field K] (τ : K →+* K) (q : ℕ) (hq : q ≠ 0) (ε η π : K),
    ε ≠ 0 → η ≠ 0 → π ≠ 0 → τ ε = η * ε →
    ∀ lam : MvPowerSeries Unit K,
      MvPowerSeries.C ε⁻¹ * lam - MvPowerSeries.C π⁻¹ *
          MvPowerSeries.expand q hq (MvPowerSeries.map τ (MvPowerSeries.C ε⁻¹ * lam)) =
        MvPowerSeries.C ε⁻¹ * (lam - MvPowerSeries.C (η * π)⁻¹ *
          MvPowerSeries.expand q hq (MvPowerSeries.map τ lam))
def EpsPow : Prop :=
  ∀ (A : Type) [CommRing A] (q : ℕ) (ε η : A), ε ^ q = η * ε → η ^ q = η →
    ∀ l : ℕ, ε ^ (q ^ l) = η ^ l * ε
def SeSign : Prop :=
  ∀ (A : Type) [CommRing A] (q : ℕ) (ε η : A), Odd q → ε ^ q = η * ε → η * η = 1 →
    ∀ (n : ℕ) (ζ : ZMod n → A) (e : ZMod n) (L : ℕ),
      ∑ l ∈ range L, (-η) ^ l * (ε * ζ (e - 2 * (l : ZMod n))) ^ (q ^ l) =
        ε * ∑ l ∈ range L, (-1) ^ l * ζ (e - 2 * (l : ZMod n)) ^ (q ^ l)
def SeInverse : Prop :=
  ∀ (A : Type) [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p] (n : ℕ) (ζ : ZMod n → A)
    (e : ZMod n) (L : ℕ),
    (∑ l ∈ range (L + 1), (-1) ^ l * ζ (e - 2 * (l : ZMod n)) ^ ((p ^ 2) ^ l)) +
      (∑ l ∈ range L, (-1) ^ l * ζ (e - 2 - 2 * (l : ZMod n)) ^ ((p ^ 2) ^ l)) ^ (p ^ 2) = ζ e
def VarpiLog : Prop :=
  ∀ (R : Type) [CommRing R] (p q : ℕ) (ϖ : R), 2 ≤ q → ϖ ^ (q - 1) = (p : R) →
    (∀ e : ℕ, ϖ ^ (q ^ e) = ϖ * (p : R) ^ (∑ i ∈ range e, q ^ i)) ∧
    (∀ e : ℕ, 2 ≤ e → e + 1 ≤ ∑ i ∈ range e, q ^ i)
def GcFunEq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : K →+* K) (c : K) (p : ℕ), p.Prime → σ (σ c) = c →
    ∀ a b : ℕ,
      (if p ∣ a ∧ p ∣ b then σ c * (coefA p (a / p) (b / p) : K) -
          σ (σ c) * (coefB p (a / p) (b / p) : K) else 0)
        - (p : K) * (c * (coefA p a b : K) - σ c * (coefB p a b : K))
      = (p : K) * (σ c * ((coefG p a : K) * (coefL p b : K)) -
          c * ((coefL p a : K) * (coefG p b : K)))
def DerivAB : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ a b : ℕ,
    (∃ z : ℤ, (a : ℚ) * coefL p a = z) ∧
    (∃ z : ℤ, (a : ℚ) * coefA p a b - (a : ℚ) * coefL p a * coefG p b = z) ∧
    (∃ z : ℤ, (a : ℚ) * coefB p a b = z)
def ClassAB : Prop :=
  ∀ (p a b : ℕ), p.Prime →
    (coefA p a b ≠ 0 → ((p : ℤ) ^ 2 - 1) ∣ (a : ℤ) - p * b) ∧
    (coefB p a b ≠ 0 → ((p : ℤ) ^ 2 - 1) ∣ (a : ℤ) - p * b) ∧
    (coefL p a * coefL p b ≠ 0 → ¬ ((p : ℤ) ^ 2 - 1) ∣ (a : ℤ) - p * b)
def g0 (p : ℕ) [Fact p.Prime] : MvPowerSeries (ZMod 1) ℚ_[p] :=
  (p : ℚ_[p])⁻¹ • MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero (Formalism.FG.shiftLog ℚ_[p] p 1 0)
def FormalGroupCocycleIntegral : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : ZMod 1 → MvPowerSeries (Fin 2 × ZMod 1) ℤ_[p]),
    Formalism.FG.IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i))
      (Formalism.FG.shiftLog ℚ_[p] p 1) →
    Formalism.G.IntegralMv (MvPowerSeries.subst
      (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (g0 p)
        - Formalism.FG.atXv (g0 p) - Formalism.FG.atYv (g0 p))
def LemmaEQp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (F : ZMod 1 → MvPowerSeries (Fin 2 × ZMod 1) ℤ_[p]),
    Formalism.FG.IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i))
      (Formalism.FG.shiftLog ℚ_[p] p 1) →
    ∀ f : MvPowerSeries (ZMod 1) ℚ_[p], MvPowerSeries.constantCoeff f = 0 →
      Formalism.G.IntegralMv (MvPowerSeries.subst
        (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) f
          - Formalism.FG.atXv f - Formalism.FG.atYv f) →
      ∃ x y : ℚ_[p], ‖x‖ ≤ 1 ∧
        Formalism.G.IntegralMv (f - x • g0 p - y • Formalism.FG.shiftLog ℚ_[p] p 1 0)
def LemmaEUnique : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (x y : ℚ_[p]),
    Formalism.G.IntegralMv (x • g0 p + y • Formalism.FG.shiftLog ℚ_[p] p 1 0) → x = 0 ∧ y = 0
def BinomPrimePower : Prop :=
  ∀ (p n : ℕ), p.Prime → 2 ≤ n →
    ((∀ k, 0 < k → k < n → p ∣ n.choose k) ↔ ∃ e, 1 ≤ e ∧ n = p ^ e) ∧
    (∀ e, 1 ≤ e → n = p ^ e → ¬ p ^ 2 ∣ n.choose (p ^ (e - 1)))
open Classical in

def DualBasisOrthogonality : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (ι : Type) [Fintype ι] [DecidableEq ι] (b b' : ι → L),
    Fintype.card ι = Module.finrank K L →
    (∀ r r', Algebra.trace K L (b r * b' r') = if r = r' then 1 else 0) →
    ∀ σ τ : L ≃ₐ[K] L, ∑ r, σ (b' r) * τ (b r) = if σ = τ then 1 else 0
def PowerCongruenceIffEqual : Prop :=
  ∀ (l d s s' : ℕ), 2 ≤ l → s < d → s' < d →
    ((l ^ d - 1 : ℕ) : ℤ) ∣ (l : ℤ) ^ s - (l : ℤ) ^ s' → s = s'
def InvariantSeriesBidegreeOneOne : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (l d : ℕ) [NeZero d], l.Prime → Even d → ∀ (ζ : Rˣ),
    IsPrimitiveRoot ζ (l ^ d - 1) → ∀ P : MvPowerSeries (ZMod d) R,
      MvPowerSeries.subst (fun s : ZMod d => MvPowerSeries.C
          ((ζ ^ ((if s.val % 2 = 0 then 1 else -1) * (l : ℤ) ^ s.val) : Rˣ) : R) *
          MvPowerSeries.X s) P = P →
      ∀ s s' : ZMod d, s.val % 2 = 0 → s'.val % 2 = 1 →
        MvPowerSeries.coeff (Finsupp.single s 1 + Finsupp.single s' 1) P = 0
def AverageProjector : Prop :=
  ∀ (K : Type) [Field K] (N : ℕ) (ζ : K), 0 < N → IsPrimitiveRoot ζ N → ∀ w : ℤ,
    ∑ k ∈ range N, (ζ ^ w) ^ k = if (N : ℤ) ∣ w then (N : K) else 0
def SumTwoUnits : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R],
    (∃ x y z : IsLocalRing.ResidueField R, x ≠ y ∧ y ≠ z ∧ x ≠ z) →
    ∀ a : R, ∃ u v : Rˣ, a = u + v
def cob {M Q : Type} [AddCommGroup M] [AddCommGroup Q] (φ : M → Q) (a b : M) : Q :=
  φ (a + b) - φ a - φ b
def CubeEliminate : Prop :=
  ∀ (M Q : Type) [AddCommGroup M] [AddCommGroup Q] (φ : M → Q),
    (∀ a b, φ (a + b) + φ (a - b) = 2 • φ a + 2 • φ b) →
    (∀ a b c, φ (a + b + c) + φ (a - b) + φ (b - c) + φ (c - a) = 3 • (φ a + φ b + φ c)) →
    (∀ a b c, φ (a + b + c) - φ (a + b) - φ (b + c) - φ (c + a) + φ a + φ b + φ c = 0) ∧
    ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b
def NormAllAlpha : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm tr : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) → (∀ α, algebraMap Z O (tr α) = star α + α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (z : Z) a b, cob φ a (algebraMap Z O z • b) = z • cob φ a b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ x : Q, x + x = 0 → x = 0) →
    ∀ (α α' : O) (u : M), φ ((2 : O) • u) = (4 : Z) • φ u →
      φ (α • u) = nm α • φ u → φ (α' • u) = nm α' • φ u →
      φ ((α + α') • u) = nm (α + α') • φ u
def UnitaryInvariance : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ (α : O) u, φ (α • u) = nm α • φ u) →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (δ : Matrix n n O), δ.conjTranspose * δ = 1 →
      ∀ u : n → M, ∑ i, φ (∑ j, δ i j • u j) = ∑ j, φ (u j)
def HyperbolicSplit : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ (α : O) u, φ (α • u) = nm α • φ u) →
    ∀ (n ι : Type) [Fintype n] [Fintype ι] [DecidableEq ι] (f f' : ι → n → O),
      (∀ e e', ∑ i, star (f e i) * f e' i = 0) → (∀ e e', ∑ i, star (f' e i) * f' e' i = 0) →
      (∀ e e', ∑ i, star (f e i) * f' e' i = if e = e' then 1 else 0) →
      ∀ t t' : ι → M,
        ∑ i, φ (∑ e, (f e i • t e + f' e i • t' e)) = ∑ e, cob φ (t e) (t' e)
def TildeAdjoint : Prop :=
  ∀ (O M Q : Type) [CommRing O] [StarRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]
    (β : M → M → Q),
    (∀ a a' b, β (a + a') b = β a b + β a' b) → (∀ a b b', β a (b + b') = β a b + β a b') →
    (∀ (α : O) a b, β (α • a) b = β a (star α • b)) →
    ∀ (ι : Type) [Fintype ι] (a : ι → ι → O) (x y : ι → M),
      ∑ r', β (∑ r, a r' r • x r) (y r') = ∑ r, β (x r) (∑ r', star (a r' r) • y r')
def ParallelogramZero : Prop :=
  ∀ (T : Type) [AddCommGroup T] [Fintype T] (m : T → ℝ),
    (∀ P Q, Q ≠ 0 → m (P + Q) + m (P - Q) - 2 * m P = 2 * m Q) → m 0 = 0 → ∀ Q, m Q = 0
def BimultDivisibleTorsion : Prop :=
  ∀ (B H : Type) [AddCommGroup B] [CommGroup H],
    (∀ y : B, ∃ n : ℕ, 0 < n ∧ n • y = 0) → (∀ (y : B) (n : ℕ), 0 < n → ∃ y', n • y' = y) →
    (∀ z : B → B → H, (∀ a a' b, z (a + a') b = z a b * z a' b) →
      (∀ a b b', z a (b + b') = z a b * z a b') → ∀ a b, z a b = 1) ∧
    (∀ c : B → H, (∀ a b, c (a + b) = c a * c b) → (∀ a, c (-a) = c a) → ∀ a, c a = 1)
def ArithFrobenius : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (x : WittVector p (AlgebraicClosure (ZMod p))),
    (p : WittVector p (AlgebraicClosure (ZMod p))) ∣ WittVector.frobenius x - x ^ p
def TeichFrobenius : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p] (x : k) (s : ℕ),
    (WittVector.frobenius)^[s] (WittVector.teichmuller p x) = (WittVector.teichmuller p x) ^ (p ^ s)
def wt (l d : ℕ) (s : ZMod d) : ℤ := (if s.val % 2 = 0 then 1 else -1) * (l : ℤ) ^ s.val
def HhWeight : Prop :=
  ∀ (l d : ℕ) [NeZero d], Even d → ∀ s : ZMod d,
    ((l : ℤ) ^ d - 1) ∣ (l : ℤ) * wt l d s + wt l d (s + 1)
def SeWeight : Prop :=
  ∀ (l d : ℕ) [NeZero d], Even d → ∀ (e : ZMod d) (k : ℕ),
    ((l : ℤ) ^ d - 1) ∣ ((l : ℤ) ^ 2) ^ k * wt l d (e - 2 * (k : ZMod d)) - wt l d e
def KroneckerCompare : Prop :=
  ∀ (h w d γ L1 L1' S : ℝ), 0 < h → 0 < w → 0 < d →
    L1 = 2 * Real.pi * h / (w * Real.sqrt d) →
    γ * L1 + L1' = (2 / (w * Real.sqrt d)) *
      (Real.pi * h * Real.log (2 / Real.sqrt d) + 2 * Real.pi * (h * (γ - Real.log 2) - S / 2)) →
    S / h = γ - Real.log (2 * Real.sqrt d) - L1' / L1
def PerArithmetic : Prop :=
  ∀ (d v γ Λ mη : ℝ), 0 < d → 0 < v → mη = γ - Real.log (2 * Real.sqrt d) - Λ →
    Real.log (4 * Real.pi) + mη = γ + Real.log (2 * Real.pi / Real.sqrt d) - Λ ∧
    Real.log (4 * Real.pi) + mη - Real.log (2 * v / Real.sqrt d) = γ + Real.log (Real.pi / v) - Λ
def EigenSublattice : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ι : Type) [Fintype ι] [DecidableEq ι] (a : ι → R),
    Function.Injective a → ∀ i : ι,
    (∏ j, (Polynomial.X - Polynomial.C (a j))) ∣
      (Polynomial.X - Polynomial.C (a i)) * ∏ j ∈ univ.erase i, (Polynomial.X - Polynomial.C (a j)) ∧
    (∀ f : Polynomial R, (∏ j, (Polynomial.X - Polynomial.C (a j))) ∣
        (Polynomial.X - Polynomial.C (a i)) * f →
      ∃ c : R, (∏ j, (Polynomial.X - Polynomial.C (a j))) ∣
        f - Polynomial.C c * ∏ j ∈ univ.erase i, (Polynomial.X - Polynomial.C (a j))) ∧
    Polynomial.eval (a i) (∏ j ∈ univ.erase i, (Polynomial.X - Polynomial.C (a j))) =
      Polynomial.eval (a i) (Polynomial.derivative (∏ j, (Polynomial.X - Polynomial.C (a j))))
def IntegerMeanLog : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : NumberField.RingOfIntegers K), x ≠ 0 →
    0 ≤ ∑ φ : K →+* ℂ, Real.log ‖φ (x : K)‖
def WeberRoot : Prop :=
  ∀ (x j : ℂ) (s : ℤ), (s = 16 ∨ s = -16) → IsIntegral ℤ j → (x - (s : ℂ)) ^ 3 = j * x →
    IsIntegral ℤ x ∧ x ≠ 0
def FourCopies : Prop :=
  ∀ d : ℚ, 0 < d → ∃ A : Matrix (Fin 4) (Fin 4) ℚ,
    A.transpose * A = d • (1 : Matrix (Fin 4) (Fin 4) ℚ)
def CayleySkew : Prop :=
  ∀ (E V : Type) [CommRing E] [StarRing E] [AddCommGroup V] (h : V → V → E) (g : V → V) (θ : E),
    (∀ x x' y, h (x + x') y = h x y + h x' y) → (∀ x y, h x y = star (h y x)) →
    (∀ x y, h (g x) (g y) = h x y) → θ + star θ = 1 →
    ∀ y y' : V,
      h y (y' - g y') + h (y - g y) y' = h (y - g y) (y' - g y') ∧
      (h y (y' - g y') - θ * h (y - g y) (y' - g y')) +
        star (h y' (y - g y) - θ * h (y' - g y') (y - g y)) = 0
def InertGaussSum : Prop :=
  ∀ (k k2 : Type) [Field k] [Fintype k] [Field k2] [Fintype k2] [Algebra k k2],
    Module.finrank k k2 = 2 → ∀ (ψ : AddChar k ℂ), ψ ≠ 1 → ∀ u : k, u ≠ 0 →
      ∑ x : k2, ψ (u * Algebra.norm k x) = -(Fintype.card k : ℂ)
def LagrangianGaussSum : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (ph : M → ℂ) (B : M → M → ℂ) (P : AddSubgroup M),
    (∀ x y, ph (x + y) = ph x * ph y * B x y) → (∀ x y z, B x (y + z) = B x y * B x z) →
    (∀ x ∈ P, ph x = 1) → (∀ x, (∀ y ∈ P, B x y = 1) → x ∈ P) →
    ∑ x, ph x = (Nat.card P : ℂ)
def NormConjInvariant : Prop :=
  ∀ (s : ℂ →+* ℂ) (q : ℕ) (r : ℂ), 0 < q → r ^ 2 = (q : ℂ) → ∀ (X : Type) [Fintype X] (Φ : X → ℂ),
    (∀ x, Φ x = 0 ∨ ∃ (ζ : ℂ) (n : ℕ) (k : ℤ), 0 < n ∧ ζ ^ n = 1 ∧ Φ x = ζ * r ^ k) →
    ∑ x, ‖s (Φ x)‖ ^ 2 = ∑ x, ‖Φ x‖ ^ 2
end Formalism.HermitianLattices.IntegralLatticeDensity


