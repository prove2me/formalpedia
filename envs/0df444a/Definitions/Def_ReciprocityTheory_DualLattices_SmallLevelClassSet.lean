-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
-- name    : ReciprocityTheory_DualLattices_SmallLevelClassSet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:49.920042+00:00
-- url     : https://prove2.me/theorems/f74c96e7-3c5c-4421-b790-6ee84f00f473
-- title:
--   Small Level Class Set
-- statement:
--   Definitions and structural lemmas for Small Level Class Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmallLevelClassSet.lean

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
open Polynomial Matrix
open scoped TensorProduct
namespace ReciprocityTheory.PGsh
def stdJ (D : Type*) [CommRing D] (g : ℕ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D :=
  Matrix.fromBlocks 0 (-1) 1 0
def ExistsPointLeviLogNormSqPos : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (g : ℕ)
    (E Φ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (c : D),
    Eᵀ = -E → (∀ i, E i i = 0) → IsUnit E.det → c ≠ 0 →
    Φᵀ * stdJ D g * Φ = c • E →
    let Ht : Matrix (Fin g) (Fin g ⊕ Fin g) D := Φ.submatrix Sum.inl id
    let Bt : Matrix (Fin g) (Fin g ⊕ Fin g) D := Φ.submatrix Sum.inr id
    let hb : Matrix (Fin g ⊕ Fin g) (Fin g) D := (Eᵀ)⁻¹ * Htᵀ
    let ι := algebraMap D (FractionRing D)
    (∀ f : Fin g → D, ∃ t : Fin g ⊕ Fin g → D, Ht *ᵥ t = c • f) ∧
    Ht * hb = 0 ∧ Bt * hb = c • (1 : Matrix (Fin g) (Fin g) D) ∧ hbᵀ * E * hb = 0 ∧
    (∀ t : Fin g ⊕ Fin g → FractionRing D, Ht.map ι *ᵥ t = 0 →
      ∃ x : Fin g → FractionRing D, hb.map ι *ᵥ x = t) ∧
    (∀ x : Fin g → FractionRing D, (∃ w : Fin g ⊕ Fin g → D, hb.map ι *ᵥ x = ι ∘ w) →
      ∃ y : Fin g → D, c • x = ι ∘ y)
abbrev extModR (R K V : Type*) [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] : Module R (ExteriorAlgebra K V) :=
  Module.compHom _ (algebraMap R K)
attribute [local instance] extModR
def detLat (R : Type*) {K V : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] [Module R V] (n : ℕ) (L : Submodule R V) : Submodule R (ExteriorAlgebra K V) :=
  Submodule.span R {w | ∃ v : Fin n → V, (∀ i, v i ∈ L) ∧ w = ExteriorAlgebra.ιMulti K n v}
def DeterminantLatticeStatement : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
    [IsScalarTower R K V] (e : ℕ) (a : Fin (e + 1) → R), Function.Injective a →
    ∀ x : Module.End K V,
      (List.ofFn fun s => x - algebraMap R K (a s) • (1 : Module.End K V)).prod = 0 →
    ∀ H Fil : Submodule R V,
      (∃ (r : ℕ) (bs : Module.Basis (Fin (e + 1) × Fin r) R H),
        ∀ j l, (bs (j, l) : V) = (x ^ (j : ℕ)) (bs (0, l))) →
      Submodule.span K (H : Set V) = ⊤ → Fil ≤ H → (∀ v ∈ Fil, x v ∈ Fil) →
      (∀ (c : R) (v : V), c ≠ 0 → v ∈ H → c • v ∈ Fil → v ∈ Fil) →
      let u : Module.End K V := x - algebraMap R K (a 0) • (1 : Module.End K V)
      let P0 : Module.End K V := (List.ofFn fun s : Fin e =>
        x - algebraMap R K (a s.succ) • (1 : Module.End K V)).prod
      let c0 : K := ∏ s : Fin e, (algebraMap R K (a 0) - algebraMap R K (a s.succ))
      let e0 : Module.End K V := c0⁻¹ • P0
      let Ps : Fin (e + 1) → Module.End K V := fun s => (List.ofFn fun t : Fin e =>
        x - algebraMap R K (a (s.succAbove t)) • (1 : Module.End K V)).prod
      let dimFil : Fin (e + 1) → ℕ := fun s =>
        Module.finrank K (Submodule.span K ((Fil.map ((Ps s).restrictScalars R) : Set V)))
      let y : R := ∏ s : Fin e, (a s.succ - a 0) ^ dimFil s.succ
      let H0 : Submodule R V := H ⊓ (LinearMap.ker u).restrictScalars R
      let Fil0 : Submodule R V := Fil.map (e0.restrictScalars R)
      let Lifts : Submodule R V := (H ⊓ Fil.comap (u.restrictScalars R)).map (e0.restrictScalars R)
      let n0 : ℕ := Module.finrank K (LinearMap.ker u)
      detLat R n0 H0 = Ideal.span {y} • Submodule.span R
          {w | ∃ (f : Fin (dimFil 0) → V) (l : Fin (n0 - dimFil 0) → V), (∀ i, f i ∈ Fil0) ∧
            (∀ j, l j ∈ Lifts) ∧
            w = ExteriorAlgebra.ιMulti K (dimFil 0) f * ExteriorAlgebra.ιMulti K (n0 - dimFil 0) l} ∧
        H0 = H.map (P0.restrictScalars R) ∧
        ∀ h ∈ H, e0 h = 0 ↔ h ∈ H.map (u.restrictScalars R)
def DualLatticeBaseIdentity : Prop :=
  ∀ (B : Type) [CommRing B] (F : B[X]),
    ∃ Rr : MvPolynomial (Fin 2) B,
      aeval (MvPolynomial.X 0) F - aeval (MvPolynomial.X 1) F =
        (MvPolynomial.X 0 - MvPolynomial.X 1) *
          (aeval (MvPolynomial.X 0) (derivative F) - (MvPolynomial.X 0 - MvPolynomial.X 1) * Rr)
def CommutingRootsStatement : Prop :=
  ∀ (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] (c : B), IsSMulRegular M c →
    ∀ (Xo Yo Rr : Module.End B M) (F : B[X]), Commute Xo Yo →
      aeval Xo F = 0 → aeval Yo F = 0 →
      (aeval Xo (derivative F) - (Xo - Yo) * Rr) * (Xo - Yo) = aeval Xo F - aeval Yo F →
      ∀ θ κ : M, (Xo - Yo) θ = c • κ →
        (Xo - Yo) (aeval Xo (derivative F) θ - c • Rr κ) = 0 ∧
        ∀ (D' : B[X]) (c₀ : B), aeval Xo (derivative F * D') = c₀ • (1 : Module.End B M) →
          c₀ • θ ∈ LinearMap.ker (Xo - Yo) ⊔ Ideal.span {c} • (⊤ : Submodule B M)
def EigenvectorLiftStatement : Prop :=
  ∀ (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] (c : B), IsSMulRegular M c →
    ∀ (al : Module.End B M) (s c' : B) (Ps Q : B[X]),
      aeval al ((X - C s) * Ps) = 0 → Ps - C (Ps.eval s) = (X - C s) * Q →
      c = Ps.eval s * c' →
      ∀ m w : M, (al - s • (1 : Module.End B M)) m = c • w →
        (al - s • (1 : Module.End B M)) (m + c' • aeval al Q w) = 0
def SaturatedDualStatement : Prop :=
  ∀ (B T : Type) [CommRing B] [IsDomain B] [ValuationRing B] [AddCommGroup T] [Module B T]
    [Module.Free B T] [Module.Finite B T] (p : B), p ≠ 0 →
    (∀ b : B, b ≠ 0 → ∃ m : ℕ, b ∣ p ^ m) →
    ∀ NN : Submodule B T, (∀ (b : B) (t : T), b ≠ 0 → b • t ∈ NN → t ∈ NN) →
    ∀ J : Submodule B (Module.Dual B T), J.FG → J ≤ NN.dualAnnihilator →
      (∀ φ ∈ NN.dualAnnihilator, ∃ b : B, b ≠ 0 ∧ b • φ ∈ J) →
    ∀ c₀ : B,
      (∀ (m : ℕ) (θ : T), (∀ φ ∈ J, φ θ ∈ Ideal.span {p ^ m}) →
        c₀ • θ ∈ NN ⊔ Ideal.span {p ^ m} • (⊤ : Submodule B T)) →
      ∀ φ ∈ NN.dualAnnihilator, c₀ • φ ∈ J
def EigenIntegralityStatement : Prop := DualLatticeBaseIdentity ∧ CommutingRootsStatement ∧ EigenvectorLiftStatement ∧ SaturatedDualStatement
def IsTateSeries {O : Type*} [CommRing O] (ϖ : O) {d : Type*} (g : MvPowerSeries d O) : Prop :=
  ∀ N : ℕ, {α : d →₀ ℕ | MvPowerSeries.coeff α g ∉ Ideal.span {ϖ ^ N}}.Finite
def newtonPoint {O : Type*} [CommRing O] (ϖ : O) (a d m : ℕ)
    (s : Fin m → MvPowerSeries (Fin d) O) : Fin d ⊕ Fin m → MvPowerSeries (Fin d) O
  | Sum.inl j => ϖ ^ a • MvPowerSeries.X j
  | Sum.inr i => s i
def newtonSystem {O : Type*} [CommRing O] (d m : ℕ) (b : Fin m → O)
    (Q : Fin m → MvPowerSeries (Fin d ⊕ Fin m) O) (i : Fin m) : MvPowerSeries (Fin d ⊕ Fin m) O :=
  b i • MvPowerSeries.X (Sum.inr i) + Q i
def NewtonLiftStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ϖ : O), Irreducible ϖ →
    ∀ (d m a c : ℕ) (b : Fin m → O) (Q : Fin m → MvPowerSeries (Fin d ⊕ Fin m) O),
      c < a → (∀ i, b i ∣ ϖ ^ c) →
      (∀ i (α : Fin d ⊕ Fin m →₀ ℕ), α.degree ≤ 1 → MvPowerSeries.coeff α (Q i) = 0) →
      ∃ s : Fin m → MvPowerSeries (Fin d) O,
        ((∀ i, IsTateSeries ϖ (s i)) ∧
          (∀ i α, MvPowerSeries.coeff α (s i) ∈ Ideal.span {ϖ ^ a}) ∧
          (∀ i, MvPowerSeries.constantCoeff (s i) = 0) ∧
          ∀ i, MvPowerSeries.subst (newtonPoint ϖ a d m s) (newtonSystem d m b Q i) = 0) ∧
        (∀ i (α : Fin d →₀ ℕ), α.degree ≤ 1 → MvPowerSeries.coeff α (s i) = 0) ∧
        ∀ s' : Fin m → MvPowerSeries (Fin d) O,
          (∀ i, IsTateSeries ϖ (s' i)) →
          (∀ i α, MvPowerSeries.coeff α (s' i) ∈ Ideal.span {ϖ ^ a}) →
          (∀ i, MvPowerSeries.constantCoeff (s' i) = 0) →
          (∀ i, MvPowerSeries.subst (newtonPoint ϖ a d m s') (newtonSystem d m b Q i) = 0) →
          s' = s
def NewtonVanishingStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (d m a c : ℕ) (b : Fin m → O) (Q : Fin m → MvPowerSeries (Fin d ⊕ Fin m) O),
      (∀ i, b i ∣ ϖ ^ c) →
      (∀ i (α : Fin d ⊕ Fin m →₀ ℕ), α.degree ≤ 1 → MvPowerSeries.coeff α (Q i) = 0) →
      ∀ s : Fin m → MvPowerSeries (Fin d) O, (∀ i, MvPowerSeries.constantCoeff (s i) = 0) →
        (∀ i, MvPowerSeries.subst (newtonPoint ϖ a d m s) (newtonSystem d m b Q i) = 0) →
      ∀ J : Ideal (MvPowerSeries (Fin d ⊕ Fin m) O), (∀ i, newtonSystem d m b Q i ∈ J) →
        (d : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin d ⊕ Fin m) (FractionRing O) ⧸
          J.map (MvPowerSeries.map (algebraMap O (FractionRing O)))) →
        ∀ g ∈ J, MvPowerSeries.subst (newtonPoint ϖ a d m s) g = 0
def NewtonStatement : Prop := NewtonLiftStatement ∧ NewtonVanishingStatement
def TruncatedPolynomialStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H] [HopfAlgebra k H]
    [FiniteDimensional k H] (d : ℕ) (x : Fin d → H),
    (∀ f ∈ RingHom.ker (Bialgebra.counitAlgHom k H), f ^ p = 0) →
    (∀ i, x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H)) →
    (∀ y ∈ RingHom.ker (Bialgebra.counitAlgHom k H), ∃ l : Fin d → k,
      y - ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2) →
    (∀ l : Fin d → k, ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2 → l = 0) →
    Function.Surjective (MvPolynomial.aeval (R := k) x) ∧
      RingHom.ker (MvPolynomial.aeval (R := k) x) =
        Ideal.span (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ p)
def GroupLikeTrivialStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H] [HopfAlgebra k H]
    [FiniteDimensional k H],
    (∀ f ∈ RingHom.ker (Bialgebra.counitAlgHom k H), f ^ p = 0) →
    ∀ (B : Type) [CommRing B] [Algebra k B] (χ : B ⊗[k] H),
      IsGroupLikeElem B χ →
      χ - 1 ∈ RingHom.ker (Bialgebra.counitAlgHom B (B ⊗[k] H)) ^ 2 → χ = 1
def HeightOneHopfStatement : Prop := TruncatedPolynomialStatement ∧ GroupLikeTrivialStatement
end ReciprocityTheory.PGsh


