-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
-- name    : Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:20.73018+00:00
-- url     : https://prove2.me/theorems/2c3b4eac-c7ac-4fd7-9e03-18aae19d901e
-- title:
--   Central Idempotent Integral
-- statement:
--   Definitions and structural lemmas for Central Idempotent Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/CentralIdempotentIntegral.lean

import Mathlib
import Definitions.Def_Formalism_ResultantValuation_KoszulSecondDifferential
import Definitions.Def_Formalism_ResultantValuation_BoundedCubic
import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_TWAbsUniform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial Formalism.CyclotomicNorms Formalism.ResultantValuation
noncomputable section
namespace Formalism.IrreducibleCountingLemmas.TW
def CentralIdempotentIntegral : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G]
    (e : MonoidAlgebra K G), e * e = e → (∀ x : MonoidAlgebra K G, e * x = x * e) →
    ∀ g : G, IsIntegral ℤ ((Fintype.card G : K) * e.coeff g)
def CutOperator : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K]
    [Algebra O K] [IsFractionRing O K] (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (ρ : Representation K G V) (Msup : Submodule O V) (U : Subgroup G) (ψU : U →* Kˣ)
    (e : MonoidAlgebra K G),
    (∀ g, ∀ v ∈ Msup, ρ g v ∈ Msup) → e * e = e → (∀ x : MonoidAlgebra K G, e * x = x * e) →
    ∀ v ∈ Msup, (∀ u : U, ρ u v = ((ψU u : Kˣ) : K) • v) →
      ρ.asAlgebraHom ((Fintype.card G : K) • e) v ∈ Msup ∧
      (∀ u : U, ρ u (ρ.asAlgebraHom ((Fintype.card G : K) • e) v) =
        ((ψU u : Kˣ) : K) • ρ.asAlgebraHom ((Fintype.card G : K) • e) v) ∧
      ρ.asAlgebraHom e (ρ.asAlgebraHom ((Fintype.card G : K) • e) v) =
        ρ.asAlgebraHom ((Fintype.card G : K) • e) v ∧
      (ρ.asAlgebraHom e v = v →
        ρ.asAlgebraHom ((Fintype.card G : K) • e) v = (Fintype.card G : K) • v) ∧
      ∀ T : V →ₗ[K] V, (∀ g w, T (ρ g w) = ρ g (T w)) →
        T (ρ.asAlgebraHom ((Fintype.card G : K) • e) v) =
          ρ.asAlgebraHom ((Fintype.card G : K) • e) (T v)
def IsLat (O K : Type) {V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V]
    [Module O V] [Module K V] (M : Submodule O V) : Prop :=
  M.FG ∧ Submodule.span K (M : Set V) = ⊤
def relLen {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (M N : Submodule O V) : ℕ∞ :=
  Module.length O (↥M ⧸ N.comap M.subtype)
def sIdx {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (M N : Submodule O V) : ℤ :=
  ((relLen M N).toNat : ℤ) - ((relLen N M).toNat : ℤ)
def scaleLat {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (c : O)
    (N : Submodule O V) : Submodule O V :=
  N.map (LinearMap.lsmul O V c)
def IndexAdditive : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] (M N P : Submodule O V),
    IsLat O K M → IsLat O K N → IsLat O K P →
    relLen M N ≠ ⊤ ∧ sIdx M N + sIdx N P = sIdx M P
def IndexDifference : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] (M M' N N' : Submodule O V),
    IsLat O K M → IsLat O K M' → IsLat O K N → IsLat O K N' →
    sIdx M N' - sIdx M N = sIdx M' N' - sIdx M' N
def IndexScale : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] (M N : Submodule O V) (ϖ : O) (u : Oˣ) (n : ℕ),
    IsLat O K M → IsLat O K N → Irreducible ϖ →
    sIdx M (scaleLat ((u : O) * ϖ ^ n) N) = sIdx M N + (Module.finrank K V : ℤ) * n
def IndexDet : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] (d : ℕ) (b : Module.Basis (Fin d) K V) (w : Fin d → V)
    (ϖ : O) (u : Oˣ) (n : ℤ), Irreducible ϖ →
    b.det w = algebraMap O K (u : O) * (algebraMap O K ϖ) ^ n →
    sIdx (Submodule.span O (Set.range b)) (Submodule.span O (Set.range w)) = n
def IndexMono : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] (M N N' : Submodule O V),
    IsLat O K M → IsLat O K N → IsLat O K N' → N ≤ N' → sIdx M N' ≤ sIdx M N
def ExportTransfer : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] (M B N N' : Submodule O V) (c : O) (e : ℕ) (ε : ℝ),
    IsLat O K M → IsLat O K B → IsLat O K N → IsLat O K N' → c ≠ 0 → 0 < e →
    (sIdx B (scaleLat c N') : ℝ) / e ≤ (sIdx B (scaleLat c N) : ℝ) / e + ε →
    (sIdx M N' : ℝ) / e ≤ (sIdx M N : ℝ) / e + ε
def LengthBaseChange : Prop :=
  ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ),
    Irreducible ϖ → Irreducible ϖ' → algebraMap O O' ϖ = (u : O') * ϖ' ^ e → 0 < e →
    ∀ (X : Type) [AddCommGroup X] [Module O X], Module.length O X ≠ ⊤ →
      Module.length O' (TensorProduct O O' X) = (e : ℕ∞) * Module.length O X
abbrev GLrt (F : Type) [Field F] (r t : ℕ) : Type := GL (Fin r ⊕ Fin t) F
def inP {F : Type} [Field F] {r t : ℕ} (g : GLrt F r t) : Prop :=
  (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₂₁ = 0
def inPm {F : Type} [Field F] {r t : ℕ} (g : GLrt F r t) : Prop :=
  (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₁₂ = 0
def inU {F : Type} [Field F] {r t : ℕ} (g : GLrt F r t) : Prop :=
  (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₂₁ = 0 ∧
  (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₁₁ = 1 ∧
  (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₂₂ = 1
def inUm {F : Type} [Field F] {r t : ℕ} (g : GLrt F r t) : Prop :=
  (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₁₂ = 0 ∧
  (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₁₁ = 1 ∧
  (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₂₂ = 1
open Classical in

def chiVal {F R : Type} [Field F] [CommRing R] {r t : ℕ} (ψ : Fˣ →* Rˣ) (g : GLrt F r t) : R :=
  if h : (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₂₂.det ≠ 0 then
    ((ψ (Units.mk0 _ h) : Rˣ) : R) else 0
open Classical in

def idemOf {F K : Type} [Field F] [Fintype F] [Field K] {r t : ℕ} (ψ : Fˣ →* Kˣ)
    (S : GLrt F r t → Prop) : MonoidAlgebra K (GLrt F r t) :=
  ((Nat.card {g : GLrt F r t // S g} : K))⁻¹ •
    ∑ᶠ p : {g : GLrt F r t // S g}, MonoidAlgebra.single (p : GLrt F r t) (chiVal ψ (p : GLrt F r t))⁻¹
def sumOf {F : Type} (R : Type) [Field F] [Fintype F] [CommRing R] {r t : ℕ}
    (S : GLrt F r t → Prop) : MonoidAlgebra R (GLrt F r t) :=
  ∑ᶠ p : {g : GLrt F r t // S g}, MonoidAlgebra.single (p : GLrt F r t) 1
def ParahoricHeckeLine : Prop :=
  ∀ (F K : Type) [Field F] [Fintype F] [Field K] [CharZero K] (r t : ℕ) (ψ : Fˣ →* Kˣ), ψ ≠ 1 →
    ∀ x : MonoidAlgebra K (GLrt F r t), ∃ c : K,
      idemOf ψ (inP (r := r) (t := t)) * x * idemOf ψ inP = c • idemOf ψ inP
def ParahoricProductAlg : Prop :=
  ∀ (F K : Type) [Field F] [Fintype F] [Field K] [CharZero K] (r t : ℕ) (ψ : Fˣ →* Kˣ), ψ ≠ 1 →
    sumOf K (inU (F := F) (r := r) (t := t)) * sumOf K inUm * idemOf ψ inP =
      ((Fintype.card F : K) ^ (r * t)) • idemOf ψ inP ∧
    sumOf K (inUm (F := F) (r := r) (t := t)) * sumOf K inU * idemOf ψ inPm =
      ((Fintype.card F : K) ^ (r * t)) • idemOf ψ inPm
def ParahoricProductModule : Prop :=
  ∀ (F O : Type) [Field F] [Fintype F] [CommRing O] [IsDomain O] [CharZero O] (r t : ℕ)
    (ψ : Fˣ →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] [NoZeroSMulDivisors O X]
    (ρ : Representation O (GLrt F r t) X), ψ ≠ 1 →
    (∀ v : X, (∀ p : GLrt F r t, inP p → ρ p v = chiVal ψ p • v) →
      ρ.asAlgebraHom (sumOf O inU) (ρ.asAlgebraHom (sumOf O inUm) v) =
        ((Fintype.card F : O) ^ (r * t)) • v) ∧
    (∀ v : X, (∀ p : GLrt F r t, inPm p → ρ p v = chiVal ψ p • v) →
      ρ.asAlgebraHom (sumOf O inUm) (ρ.asAlgebraHom (sumOf O inU) v) =
        ((Fintype.card F : O) ^ (r * t)) • v)
def PrimeToResidueUnit : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (l n : ℕ) (ζ : R), l.Prime →
    (l : R) ∈ IsLocalRing.maximalIdeal R → ¬ l ∣ n → ζ ^ n = 1 → ζ ≠ 1 → IsUnit (ζ - 1)
def OneDeltaUnits : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (l n : ℕ) (δ : Rˣ), l.Prime →
    (l : R) ∈ IsLocalRing.maximalIdeal R → orderOf δ = n → (n = 15 ∨ n = 5 ∨ n = 3) → ¬ l ∣ n →
    IsUnit ((δ : R) - 1) ∧ (l ≠ 2 → IsUnit ((δ : R) + 1)) ∧ IsUnit ((δ : R) - ((δ⁻¹ : Rˣ) : R))
def FifteenUnit : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (δ : Rˣ), orderOf δ = 15 → IsUnit ((δ : R) - 1)
def KillByUnit : Prop :=
  ∀ (R Y N : Type) [CommRing R] [AddCommGroup Y] [Module R Y] [AddCommGroup N] [Module R N]
    (γ : Module.End R Y) (φ : Y →ₗ[R] N) (c : R) (P : R[X]) (y : Y),
    (∀ y', φ (γ y') = c • φ y') → IsUnit (P.eval c) → Polynomial.aeval γ P y = 0 → φ y = 0
def FrobCoinvariantsZero : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (n : ℕ)
    (Fr : Matrix (Fin n) (Fin n) O), (Fr - 1).det ≠ 0 →
    ∀ x : Fin n → K, ∃ y : Fin n → K, ∀ i, ∃ a : O,
      ((Fr - 1).map (algebraMap O K)).mulVec y i - x i = algebraMap O K a
def UnitQuotientSign : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E ≃+* E),
    (∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x)) →
    (∀ (ζ : E) (n : ℕ), 0 < n → ζ ^ n = 1 → ζ = 1 ∨ ζ = -1) →
    ∀ u : (NumberField.RingOfIntegers E)ˣ,
      ((u : NumberField.RingOfIntegers E) : E) / c ((u : NumberField.RingOfIntegers E) : E) = 1 ∨
      ((u : NumberField.RingOfIntegers E) : E) / c ((u : NumberField.RingOfIntegers E) : E) = -1
def SahCentral : Prop :=
  ∀ (G R W : Type) [Group G] [TopologicalSpace G] [CommRing R] [AddCommGroup W] [Module R W]
    [TopologicalSpace W] [DiscreteTopology W] (ρ : Representation R G W) (z : G) (c : R),
    z ∈ Subgroup.center G → IsUnit (c - 1) → (∀ w, ρ z w = c • w) →
    (∀ w : W, (∀ g, ρ g w = w) → w = 0) ∧
    ∀ (n : ℕ) (f : (Fin (n + 1) → G) → W), Continuous f → coboundary ρ (n + 1) f = 0 →
      ∃ h : (Fin n → G) → W, Continuous h ∧ coboundary ρ n h = f
def KernelLengthDet : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (a : ℕ) (Φ : Matrix (Fin a) (Fin a) O) (ϖ : O) (u : Oˣ) (n : ℕ),
    Irreducible ϖ → Φ.det = (u : O) * ϖ ^ n →
    Module.length O (LinearMap.ker (LinearMap.rTensor
      (K ⧸ LinearMap.range (Algebra.linearMap O K)) (Matrix.toLin' Φ))) = (n : ℕ∞)
def KoszulLength : Prop :=
  ∀ (k : Type) [Field k] (n r : ℕ), 1 ≤ n → ∀ (u : (truncPoly k n)ˣ) (w : truncPoly k n),
    Module.length (truncPoly k n)
      (koszulFirstCohomology r (Ideal.Quotient.mk _ X * (u : truncPoly k n))
        (Ideal.Quotient.mk _ X * w)) = ((2 * r : ℕ) : ℕ∞)
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
def ResidualCore : Prop :=
  ∀ (k K' : Type) [Field k] [Field K'] [Algebra k K'] (m r d R : ℕ)
    (u t : Matrix (Fin R × Bool × Fin r) (Fin m) k) (us : Matrix (Fin R × Bool × Fin r) (Fin d) k)
    (s : Fin R → K') (bSel : Module.Basis (Fin d) k (LinearMap.ker (Matrix.toLin' t))),
    AlgebraicIndependent k s →
    (∀ (x : Fin m → k) (y : Fin d → k), ∑ P, (t.mulVec x) P * (us.mulVec y) P = 0) →
    Module.finrank K' (LinearMap.ker (Matrix.toLin' (t.map (algebraMap k K') -
        Matrix.diagonal (fun P : Fin R × Bool × Fin r => s P.1) * u.map (algebraMap k K')))) +
      (Matrix.of fun p q : Fin d => ∑ i, s i * algebraMap k K'
        (genB u us i (bSel p : Fin m → k) (Pi.single q 1))).rank ≤ d
def ResidualModule : Prop :=
  ∀ (K' : Type) [Field K'] (n a C : ℕ) (Φ : Matrix (Fin a) (Fin a) (TruncK K' n))
    (N : Submodule (TruncK K' n) (Fin a → TruncK K' n)),
    C < n → N ≤ LinearMap.ker (Matrix.toLin' Φ) →
    Module.finrank K' (LinearMap.ker (Matrix.toLin' Φ) ⧸ N.comap (LinearMap.ker (Matrix.toLin' Φ)).subtype)
      ≤ C →
    ((∀ x ∈ N, (Ideal.Quotient.mk _ X : TruncK K' n) • x = 0 → x = 0) →
      N = ⊥ ∧ Φ.det ∉ Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)}) ∧
    (1 ≤ a → Module.finrank K' ↥(N ⊓ LinearMap.ker
        ((Ideal.Quotient.mk _ X : TruncK K' n) • LinearMap.id :
          (Fin a → TruncK K' n) →ₗ[TruncK K' n] (Fin a → TruncK K' n))) ≤ 1 →
      (∃ x, N = Submodule.span (TruncK K' n) {x}) ∧
      ∃ i j : Fin a, ∃ a' : ℕ, ∃ h : a = a' + 1,
        (Matrix.submatrix Φ (fun p : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h i) p))
          (fun q : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h j) q))).det ∉
          Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)})
def ResidualAbs : Prop :=
  ∀ (k K' : Type) [Field k] [Field K'] [Algebra k K'] (m r d R n a C : ℕ)
    (u t : Matrix (Fin R × Bool × Fin r) (Fin m) k) (us : Matrix (Fin R × Bool × Fin r) (Fin d) k)
    (s : Fin R → K') (bSel : Module.Basis (Fin d) k (LinearMap.ker (Matrix.toLin' t)))
    (Φ : Matrix (Fin a) (Fin a) (TruncK K' n)) (N : Submodule (TruncK K' n) (Fin a → TruncK K' n))
    (ι : ↥(N ⊓ LinearMap.ker ((Ideal.Quotient.mk _ X : TruncK K' n) • LinearMap.id :
          (Fin a → TruncK K' n) →ₗ[TruncK K' n] (Fin a → TruncK K' n))) →ₗ[K']
      ↥(LinearMap.ker (Matrix.toLin' (t.map (algebraMap k K') -
        Matrix.diagonal (fun P : Fin R × Bool × Fin r => s P.1) * u.map (algebraMap k K'))))),
    AlgebraicIndependent k s →
    (∀ (x : Fin m → k) (y : Fin d → k), ∑ P, (t.mulVec x) P * (us.mulVec y) P = 0) →
    C < n → N ≤ LinearMap.ker (Matrix.toLin' Φ) →
    Module.finrank K' (LinearMap.ker (Matrix.toLin' Φ) ⧸ N.comap (LinearMap.ker (Matrix.toLin' Φ)).subtype)
      ≤ C →
    Function.Injective ι →
    (Submodule.span k (Set.range (gramB u t us bSel)) = ⊤ →
      N = ⊥ ∧ Φ.det ∉ Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)}) ∧
    (1 ≤ a → d - 1 ≤ (∑ i, s i • (gramB u t us bSel i).map (algebraMap k K')).rank →
      (∃ x, N = Submodule.span (TruncK K' n) {x}) ∧
      ∃ i j : Fin a, ∃ a' : ℕ, ∃ h : a = a' + 1,
        (Matrix.submatrix Φ (fun p : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h i) p))
          (fun q : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h j) q))).det ∉
          Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)})
def ResidualCoreSigned : Prop :=
  ∀ (k K' : Type) [Field k] [Field K'] [Algebra k K'] (m r d R : ℕ)
    (u t : Matrix (Fin R × Bool × Fin r) (Fin m) k) (us : Matrix (Fin R × Bool × Fin r) (Fin d) k)
    (cP : Fin R → kˣ)
    (s : Fin R → K') (bSel : Module.Basis (Fin d) k (LinearMap.ker (Matrix.toLin' t))),
    AlgebraicIndependent k s →
    (∀ (x : Fin m → k) (y : Fin d → k), ∑ i, (cP i : k) *
      (∑ ρ, (t.mulVec x) (i, true, ρ) * (us.mulVec y) (i, true, ρ) -
        ∑ ρ, (t.mulVec x) (i, false, ρ) * (us.mulVec y) (i, false, ρ)) = 0) →
    Module.finrank K' (LinearMap.ker (Matrix.toLin' (t.map (algebraMap k K') -
        Matrix.diagonal (fun P : Fin R × Bool × Fin r => s P.1) * u.map (algebraMap k K')))) +
      (Matrix.of fun p q : Fin d => ∑ i, s i * algebraMap k K' ((cP i : k) *
        (∑ ρ, (u.mulVec (bSel p : Fin m → k)) (i, true, ρ) * (us.mulVec (Pi.single q 1)) (i, true, ρ) -
          ∑ ρ, (u.mulVec (bSel p : Fin m → k)) (i, false, ρ) *
            (us.mulVec (Pi.single q 1)) (i, false, ρ)))).rank ≤ d
def JacobiAdjugate : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (A : Matrix (Fin n) (Fin n) R), A.det = 0 →
    ∀ k l : Fin n, A.adjugate k l • A.adjugate =
      Matrix.vecMulVec (fun i => A.adjugate i l) (fun j => A.adjugate k j)
def MinorDividesPower : Prop :=
  ∀ (R : Type) [CommRing R] (ϖ T P Q : R) (U : Rˣ) (n w : ℕ), ϖ ^ n = 0 →
    P = T ^ w * (U : R) + ϖ * Q → P ∣ T ^ (n * w)
def LinearFormRegular : Prop :=
  ∀ (R σ : Type) [CommRing R] [Fintype σ] (a : σ → R) (i : σ), IsUnit (a i) →
    ∀ f : MvPolynomial σ R, (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j) * f = 0 → f = 0
def NormElementResidual : Prop :=
  ∀ (B : Type) [CommRing B] (l M n q c : ℕ) (b : B), l.Prime → (l : B) = 0 → b ^ n = 0 →
    n + 1 ≤ l ^ M → q = 1 + c * l ^ M → ∑ j ∈ Finset.range q, (1 + b) ^ j = 1
def NormElementTwo : Prop :=
  ∀ (B : Type) [CommRing B] (M N q c : ℕ) (b : B), (4 : B) = 0 → 1 ≤ M → b ^ N = 0 →
    2 * N ≤ 2 ^ M → q = 1 + c * 2 ^ (M + 1) → ∑ j ∈ Finset.range q, (1 + b) ^ j = 1
def BurnsideLocal : Prop :=
  ∀ (AA G : Type) [CommRing AA] [IsLocalRing AA] [Group G] (r : ℕ)
    (ρ : G →* Matrix (Fin r) (Fin r) AA),
    Submodule.span (IsLocalRing.ResidueField AA)
      (Set.range fun g => (ρ g).map (IsLocalRing.residue AA)) = ⊤ →
    Submodule.span AA (Set.range ρ) = ⊤ ∧
    ∀ N : Submodule AA (Fin r → AA), (∀ g, ∀ x ∈ N, (ρ g).mulVec x ∈ N) →
      ∃ 𝔞 : Ideal AA, ∀ x, x ∈ N ↔ ∀ i, x i ∈ 𝔞
def GoursatMatrix : Prop :=
  ∀ (AA : Type) [CommRing AA] [IsLocalRing AA] (r : ℕ)
    (RR : Subalgebra AA (Matrix (Fin r) (Fin r) AA × Matrix (Fin r) (Fin r) AA)),
    (∀ α, ∃ β, (α, β) ∈ RR) → (∀ β, ∃ α, (α, β) ∈ RR) →
    ∃ (cc : Ideal AA) (U : GL (Fin r) (AA ⧸ cc)), ∀ p, p ∈ RR ↔
      p.2.map (Ideal.Quotient.mk cc) =
        (U : Matrix (Fin r) (Fin r) (AA ⧸ cc)) * p.1.map (Ideal.Quotient.mk cc) *
          ((U⁻¹ : GL (Fin r) (AA ⧸ cc)) : Matrix (Fin r) (Fin r) (AA ⧸ cc))
def FirstVariation : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M₀ N : Matrix (Fin n) (Fin n) R),
    ((M₀.map Polynomial.C + (Polynomial.X : R[X]) • N.map Polynomial.C).det).coeff 0 = M₀.det ∧
    ((M₀.map Polynomial.C + (Polynomial.X : R[X]) • N.map Polynomial.C).det).coeff 1 =
      (M₀.adjugate * N).trace
def LowDegreeGrowth : Prop :=
  ∀ (R σ : Type) [CommRing R] [Fintype σ] (a : σ → R) (i : σ) (a₀ f : MvPolynomial σ R) (d j : ℕ),
    IsUnit (a i) →
    a₀ - ∑ s, MvPolynomial.C (a s) * MvPolynomial.X s ∈ varIdeal R σ ^ 2 →
    f ∉ varIdeal R σ ^ (d + 1) → a₀ ^ j * f ∉ varIdeal R σ ^ (d + j + 1)
def TwoInConductor : Prop :=
  ∀ (AA : Type) [CommRing AA] [IsLocalRing AA] (cc : Ideal AA) (ε x : AA) (n : ℕ),
    (2 : AA) ∈ IsLocalRing.maximalIdeal AA → ε = -1 + 4 * x → Odd n → ε ^ n - 1 ∈ cc → (2 : AA) ∈ cc
def SocleTwo : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (u : Oˣ) (e₀ K' : ℕ),
    Irreducible ϖ → (2 : O) = (u : O) * ϖ ^ e₀ →
    (Polynomial.C (2 : O) * Polynomial.X ^ K' : O[X]) ∉
      Ideal.span {Polynomial.C (ϖ ^ (e₀ + 1)), (Polynomial.X : O[X]) ^ (K' + 1)}
def SubspaceMobius : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V],
    (∑ᶠ W : Submodule F V, (-1 : ℤ) ^ Module.finrank F W *
        (Fintype.card F : ℤ) ^ (Module.finrank F W).choose 2) =
      if Module.finrank F V = 0 then 1 else 0
open Classical in

def ComplementCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (r t : ℕ), Module.finrank F V = r + t → ∀ v : Fin r → V,
    Nat.card {U : Submodule F V //
        Module.finrank F U = t ∧ Submodule.span F (Set.range v) ⊔ U = ⊤} =
      if LinearIndependent F v then Fintype.card F ^ (r * t) else 0
def ParabolicConstant : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (r t : ℕ),
    (∏ i ∈ Finset.Icc 1 r, (1 - (Fintype.card F : ℝ) ^ (-(i : ℤ)))) *
        ((Nat.card (GL (Fin (r + t)) F) : ℝ) / (Nat.card (parabolicSet F r t) : ℝ)) *
        (∏ i ∈ Finset.Icc (t + 1) (r + t), (1 - (Fintype.card F : ℝ) ^ (-(i : ℤ))))⁻¹ =
      (Fintype.card F : ℝ) ^ (r * t)
def IdempotentRigid : Prop :=
  ∀ (R : Type) [CommRing R] (e e' : R), e * e = e → e' * e' = e' →
    e - e' ∈ Ideal.jacobson (⊥ : Ideal R) → e = e'
def HeckeDetFactors : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (d r : ℕ) (A : Fin (r + 1) → Matrix (Fin d) (Fin d) k),
    A 0 = 1 →
    ∃ (n : ℕ) (α : Fin n → k), n ≤ r * d ∧
      (∑ j : Fin (r + 1), (Polynomial.X : k[X]) ^ (j : ℕ) • (A j).map Polynomial.C).det =
        ∏ i, (1 - Polynomial.C (α i) * Polynomial.X)
def FactorUnitOrX : Prop :=
  ∀ (k R : Type) [Field k] [CommRing R] [Algebra k R] (X : R) (w : Rˣ) (α : k), IsNilpotent X →
    (w : R) = 1 + X →
    (α ≠ 1 → IsUnit (1 - algebraMap k R α * ((w⁻¹ : Rˣ) : R))) ∧
    (α = 1 → ∃ v : Rˣ, 1 - algebraMap k R α * ((w⁻¹ : Rˣ) : R) = X * (v : R))
def CharactersSeparate : Prop :=
  ∀ (L Δ : Type) [Field L] [IsAlgClosed L] [CharZero L] [CommGroup Δ] [Finite Δ]
    (x : MonoidAlgebra L Δ),
    (∀ ψ : Δ →* L, MonoidAlgebra.lift L L Δ ψ x = 0) → x = 0
def CMFactorUnit : Prop :=
  ∀ (K : Type) [Field K] (q ε X : K) (m : ℕ), q = 1 → ε ^ 2 = 1 → Odd m → X ^ m = 1 → X ≠ 1 →
    (1 - X * ε) * (1 - X⁻¹ * ε) + (q - 1) * ε ^ 2 ≠ 0
def LemmaSUB : Prop :=
  ∀ (k : Type) [CommRing k] (ℓ r s : ℕ) (F : Fin s → MvPowerSeries (Fin r) k) (B : List ℕ → ℕ),
    2 ≤ ℓ → (∀ i, F i ≠ 0) →
    ∃ e : Fin r → ℕ, StrictMono e ∧
      (∀ j : Fin r, B (List.ofFn fun i : Fin (j : ℕ) => e (Fin.castLE (Nat.le_of_lt j.isLt) i)) ≤ e j) ∧
      ∀ i, (MvPowerSeries.subst (fun j => (PowerSeries.X : PowerSeries k) ^ (ℓ ^ e j)) (F i) :
        PowerSeries k) ≠ 0
def LemmaLOW : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (n m₀ : ℕ)
    (D g : PowerSeries O),
    Irreducible ϖ →
    (PowerSeries.map (IsLocalRing.residue O) D).order ≤ (m₀ : ℕ∞) →
    PowerSeries.constantCoeff g ∉ Ideal.span {ϖ ^ n} →
    D * g ∉ Ideal.span {PowerSeries.C (ϖ ^ n), (PowerSeries.X : PowerSeries O) ^ (n * m₀ + 1)}
def LemmaGT : Prop :=
  ∀ (K L : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
    [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L]
    (ℓ e J M k₀ : ℕ) (h : Fin J → K[X]) (w : Fin J → ℕ) (vv : Fin J → ℝ) (ε : ℝ),
    ℓ.Prime → 0 < e → ‖(ℓ : K)‖ = (ℓ : ℝ)⁻¹ →
    (∀ x : K, x ≠ 0 → ∃ n : ℤ, vl ℓ x = n / e) →
    (∀ j i, ‖(h j).coeff i‖ ≤ 1) →
    (∀ j, w j ≤ M ∧ (h j).coeff (w j) ≠ 0 ∧ vl ℓ ((h j).coeff (w j)) ≤ vv j) →
    0 < ε → 1 ≤ k₀ → 2 * (J : ℝ) * M / ε ≤ ((ℓ ^ k₀).totient : ℝ) → (e : ℝ) * ε < k₀ →
    ∃ k : ℕ, k₀ ≤ k ∧
      (k : ℝ) ≤ (k₀ + J * M + 1) * Real.exp (2 * (∑ j, vv j) / ε) + 1 ∧
      ∃ ζ ∈ primitiveRoots (ℓ ^ k) L, ∃ εj : Fin J → ℝ, (∀ j, 0 ≤ εj j) ∧ ∑ j, εj j ≤ ε ∧
        ∀ j, ((h j).map (algebraMap K L)).eval (ζ - 1) ≠ 0 ∧
          vl ℓ (((h j).map (algebraMap K L)).eval (ζ - 1)) ≤ vv j + εj j
def BinomValuation : Prop :=
  ∀ l e i : ℕ, l.Prime → 1 ≤ i → i ≤ l ^ e →
    padicValNat l ((l ^ e).choose i) + padicValNat l i = e
def CyclotomicValuation : Prop :=
  ∀ (L : Type) [NormedField L] [IsUltrametricDist L] (ℓ k : ℕ) (ζ : L), ℓ.Prime → 1 ≤ k →
    ‖(ℓ : L)‖ = (ℓ : ℝ)⁻¹ → IsPrimitiveRoot ζ (ℓ ^ k) →
    vl ℓ (ζ - 1) = 1 / ((ℓ ^ k).totient : ℝ)
def TwistAssembly : Prop :=
  ∀ (K L : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
    [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L]
    (ℓ e e₀ R' D' m₁ t M₀ : ℕ) (O₀ O : Subring K) [IsDiscreteValuationRing O₀]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O₀)] (w₀ : O₀) (w : O)
    (Sig JJ : Type) [Fintype Sig] [Fintype JJ] (vv : JJ → ℝ)
    (F : ℕ → Sig → MvPolynomial (Fin R' ⊕ Fin R') O₀)
    (f : ℕ → JJ → MvPolynomial (Fin R' ⊕ Fin R') O) (D g : ℕ → JJ → MvPolynomial (Fin R') O),
    ℓ.Prime → 0 < e → 0 < e₀ → ‖(ℓ : K)‖ = (ℓ : ℝ)⁻¹ →
    (∀ x : K, x ≠ 0 → ∃ n : ℤ, vl ℓ x = n / e) →
    (∀ x : O₀, ‖(x : K)‖ ≤ 1) → (∀ x : O, ‖(x : K)‖ ≤ 1) →
    Irreducible w₀ → Irreducible w → vl ℓ (w₀ : K) = 1 / e₀ → vl ℓ (w : K) = 1 / e →
    (∀ j, ∃ n : ℕ, vv j = n / e) →

    (∀ M, M₀ ≤ M → ∀ s, F M s ∉
      Ideal.span {MvPolynomial.C ((ℓ : O₀) ^ (if ℓ = 2 then 1 else 0) * w₀)} +
        varIdeal O₀ (Fin R' ⊕ Fin R') ^ (D' + 1) + lamIdeal O₀ (Fin R' ⊕ Fin R') ℓ M) →

    (∀ M, M₀ ≤ M → ∀ j,
      MvPolynomial.bind₁ (Sum.elim MvPolynomial.X (fun _ => 0)) (f M j) - D M j * g M j ∈
        lamIdeal O (Fin R') ℓ M ∧
      ((MvPolynomial.constantCoeff (g M j) : O) : K) ≠ 0 ∧
      vl ℓ ((MvPolynomial.constantCoeff (g M j) : O) : K) = vv j ∧
      FewFactors ℓ M m₁ (D M j)) →
    ∀ ε : ℝ, 0 < ε →
      ∃ (M k : ℕ) (e'' e' : Fin R' → ℕ) (z : L), M₀ ≤ M ∧ k ≤ M ∧ (∀ i, e'' i < k ∧ e' i < k) ∧
        IsPrimitiveRoot z (ℓ ^ k) ∧ ∀ sg : Sig ⊕ JJ → ℤˣ,
        (∀ s, MvPolynomial.eval₂ ((algebraMap K L).comp O₀.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inl s))) (F M s) ≠ 0) ∧
        (∀ j, MvPolynomial.eval₂ ((algebraMap K L).comp O.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inr j))) (f M j) ≠ 0) ∧
        ∑ s, vl ℓ (MvPolynomial.eval₂ ((algebraMap K L).comp O₀.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inl s))) (F M s)) ≤
          (if ℓ = 2 then 1 else 0) * (Fintype.card Sig : ℝ) + ε ∧
        (∃ εj : JJ → ℝ, (∀ j, 0 ≤ εj j) ∧ ∑ j, εj j ≤ ε ∧
          ∀ j, vl ℓ (MvPolynomial.eval₂ ((algebraMap K L).comp O.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inr j))) (f M j)) ≤ vv j + εj j) ∧
        2 * (t : ℝ) * ∑ i, (vl ℓ (z ^ (ℓ ^ e'' i) - 1) + vl ℓ (z ^ (ℓ ^ e' i) - 1)) ≤ ε
def TwistAssemblyTermwise : Prop :=
  ∀ (K L : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
    [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L]
    (ℓ e e₀ R' D' m₁ t M₀ : ℕ) (O₀ O : Subring K) [IsDiscreteValuationRing O₀]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O₀)] (w₀ : O₀) (w : O)
    (Sig JJ : Type) [Fintype Sig] [Fintype JJ] (vv : JJ → ℝ)
    (F : ℕ → Sig → MvPolynomial (Fin R' ⊕ Fin R') O₀)
    (f : ℕ → JJ → MvPolynomial (Fin R' ⊕ Fin R') O) (D g : ℕ → JJ → MvPolynomial (Fin R') O),
    ℓ.Prime → 0 < e → 0 < e₀ → ‖(ℓ : K)‖ = (ℓ : ℝ)⁻¹ →
    (∀ x : K, x ≠ 0 → ∃ n : ℤ, vl ℓ x = n / e) →
    (∀ x : O₀, ‖(x : K)‖ ≤ 1) → (∀ x : O, ‖(x : K)‖ ≤ 1) →
    Irreducible w₀ → Irreducible w → vl ℓ (w₀ : K) = 1 / e₀ → vl ℓ (w : K) = 1 / e →
    (∀ j, ∃ n : ℕ, vv j = n / e) →

    (∀ M, M₀ ≤ M → ∀ s, F M s ∉
      Ideal.span {MvPolynomial.C ((ℓ : O₀) ^ (if ℓ = 2 then 1 else 0) * w₀)} +
        varIdeal O₀ (Fin R' ⊕ Fin R') ^ (D' + 1) + lamIdeal O₀ (Fin R' ⊕ Fin R') ℓ M) →

    (∀ M, M₀ ≤ M → ∀ j,
      MvPolynomial.bind₁ (Sum.elim MvPolynomial.X (fun _ => 0)) (f M j) - D M j * g M j ∈
        lamIdeal O (Fin R') ℓ M ∧
      ((MvPolynomial.constantCoeff (g M j) : O) : K) ≠ 0 ∧
      vl ℓ ((MvPolynomial.constantCoeff (g M j) : O) : K) = vv j ∧
      FewFactors ℓ M m₁ (D M j)) →
    ∀ ε : ℝ, 0 < ε →
      ∃ (M k : ℕ) (e'' e' : Fin R' → ℕ) (z : L), M₀ ≤ M ∧ k ≤ M ∧ (∀ i, e'' i < k ∧ e' i < k) ∧
        IsPrimitiveRoot z (ℓ ^ k) ∧ ∀ sg : Sig ⊕ JJ → ℤˣ,
        (∀ s, MvPolynomial.eval₂ ((algebraMap K L).comp O₀.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inl s))) (F M s) ≠ 0) ∧
        (∀ j, MvPolynomial.eval₂ ((algebraMap K L).comp O.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inr j))) (f M j) ≠ 0) ∧
        (∃ εs : Sig → ℝ, (∀ s, 0 ≤ εs s) ∧ ∑ s, εs s ≤ ε ∧
          ∀ s, vl ℓ (MvPolynomial.eval₂ ((algebraMap K L).comp O₀.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inl s))) (F M s)) ≤ (if ℓ = 2 then 1 else 0) + εs s) ∧
        (∃ εj : JJ → ℝ, (∀ j, 0 ≤ εj j) ∧ ∑ j, εj j ≤ ε ∧
          ∀ j, vl ℓ (MvPolynomial.eval₂ ((algebraMap K L).comp O.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inr j))) (f M j)) ≤ vv j + εj j) ∧
        2 * (t : ℝ) * ∑ i, (vl ℓ (z ^ (ℓ ^ e'' i) - 1) + vl ℓ (z ^ (ℓ ^ e' i) - 1)) ≤ ε
def HalfForm : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] (B : Y →+ Y →+ ℝ) (w wb : Y →+ Y), (∀ y y', B y y' = B y' y) →
    (∀ y y', B (w y) y' = B y (wb y')) → (∀ y, w y + wb y = y) →
    ∀ y, B y (w y) = B y y / 2 ∧ B (wb y) y = B y y / 2
def BoundedCubic : Prop :=
  ∀ (G : Type) [AddCommGroup G] (φ : G → ℝ), (∃ C : ℝ, ∀ x, |φ x| ≤ C) →
    (∃ c : ℝ, ∀ x y z, thirdDiff φ x y z = c) → ∀ x, φ x = φ 0
def BoundedSeriesIntegral : Prop :=
  ∀ (L : Type) [DenselyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (n : ℕ)
    (a : (Fin n →₀ ℕ) → L),
    (∀ x : Fin n → L, (∀ i, ‖x i‖ < 1) → Summable fun m : Fin n →₀ ℕ => a m * ∏ i, x i ^ m i) →
    (∀ x : Fin n → L, (∀ i, ‖x i‖ < 1) → ‖∑' m : Fin n →₀ ℕ, a m * ∏ i, x i ^ m i‖ ≤ 1) →
    ∀ m, ‖a m‖ ≤ 1
def SymmetricLift : Prop :=
  ∀ (K H A : Type) [Field K] [Group H] [CommGroup A] (j : Kˣ →* H) (π : H →* A) (ι : H ≃* H)
    (m : ℕ), Function.Injective j → Function.Surjective π → π.ker = j.range →
    (∀ c h, j c * h = h * j c) → (∀ h, ι (ι h) = h) → (∀ c, ι (j c) = j c) →
    (∀ h, π (ι h) = (π h)⁻¹) → Odd m → (∀ a : A, a ^ m = 1) →
    ∀ a : A, ∃! h : H, π h = a ∧ ι h = h⁻¹ ∧ h ^ m = 1
def UnitBallLattice : Prop :=
  ∀ (K V : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [NormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V] [FiniteDimensional K V]
    (ϖ : K), ‖ϖ‖ < 1 → (∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n) →
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      ∀ v : V, ‖v‖ ≤ 1 ↔ ∀ i, ‖b.repr v i‖ ≤ 1
end Formalism.IrreducibleCountingLemmas.TW


