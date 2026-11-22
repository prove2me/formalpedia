-- Prove2me | Definitions.Def_Formalism_GelfandTransference_Statement
-- name    : Formalism_GelfandTransference_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:40:38.083931+00:00
-- url     : https://prove2.me/theorems/6a19c9f4-2f22-4b87-9cbb-bab5ecaff8b7
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GelfandTransference/Statement.lean

import Mathlib
import Definitions.Def_Formalism_NormUnitaryBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
namespace Formalism.HadamardInequality
open Classical in

def FreeOrbits : Prop :=
  ∀ (G X : Type) [Group G] [Fintype G] [MulAction G X] [Fintype X] (Z : Subgroup G) (ε : ℝ),
    (∀ z ∈ Z, ∀ x : X, z • x = x) →
    (∑ g ∈ univ.filter (fun g : G => g ∉ Z), (Nat.card (MulAction.fixedBy X g) : ℝ)) ≤
      ε * Fintype.card X →
    (Nat.card (MulAction.orbitRel.Quotient G X) : ℝ) * Fintype.card G ≤
      ((Nat.card Z : ℝ) + ε) * Fintype.card X
def freeOrbits (G X : Type) [Group G] [MulAction G X] (Z : Subgroup G) : Type :=
  {ω : MulAction.orbitRel.Quotient G X //
    ∃ x : X, (Quotient.mk (MulAction.orbitRel G X) x) = ω ∧ MulAction.stabilizer G x = Z}
open Classical in

def FreeFree : Prop :=
  ∀ (G X : Type) [Group G] [Fintype G] [MulAction G X] [Fintype X] (Z : Subgroup G) (ε : ℝ),
    (∀ z ∈ Z, ∀ x : X, z • x = x) →
    (∑ g ∈ univ.filter (fun g : G => g ∉ Z), (Nat.card (MulAction.fixedBy X g) : ℝ)) ≤
      ε * Fintype.card X →
    (Nat.card Z : ℝ) * (1 - ε) * Fintype.card X ≤
      (Nat.card (freeOrbits G X Z) : ℝ) * Fintype.card G
def equivFns (K G X V : Type) [Field K] [Group G] [MulAction G X] [AddCommGroup V] [Module K V]
    [DistribMulAction G V] [SMulCommClass G K V] : Submodule K (X → V) where
  carrier := {φ | ∀ (g : G) (x : X), φ (g • x) = g • φ x}
  add_mem' := by
    intro a b ha hb g x
    simp only [Set.mem_ofPred_eq] at ha hb
    simp [ha g x, hb g x, smul_add]
  zero_mem' := by intro g x; simp
  smul_mem' := by
    intro c a ha g x
    simp only [Set.mem_ofPred_eq] at ha
    simp [ha g x, smul_comm]
def FreeEquivDim : Prop :=
  ∀ (K G X V : Type) [Field K] [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [DistribMulAction G V]
    [SMulCommClass G K V] (Z : Subgroup G), (∀ z ∈ Z, ∀ v : V, z • v = v) →
    Module.finrank K V * Nat.card (freeOrbits G X Z) ≤ Module.finrank K (equivFns K G X V) ∧
      Module.finrank K (equivFns K G X V) ≤
        Module.finrank K V * Nat.card (MulAction.orbitRel.Quotient G X)
open Classical in

def FreeConsequence : Prop :=
  ∀ (K G X V : Type) [Field K] [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [DistribMulAction G V]
    [SMulCommClass G K V] (Z : Subgroup G) (ε : ℝ), 0 ≤ ε → ε ≤ 1 / 4 →
    (∀ z ∈ Z, ∀ v : V, z • v = v) → (∀ z ∈ Z, ∀ x : X, z • x = x) →
    (∑ g ∈ univ.filter (fun g : G => g ∉ Z), (Nat.card (MulAction.fixedBy X g) : ℝ)) ≤
      ε * Fintype.card X →
    (Module.finrank K V : ℝ) * Nat.card (MulAction.orbitRel.Quotient G X) ≤
      (1 + 3 * ε) * Module.finrank K (equivFns K G X V)
def FixedHyperplanes : Prop :=
  ∀ (F V : Type) [Field F] [Fintype F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g : V →ₗ[F] V) (s : ℕ),
    (∀ μ : F, Module.finrank F (LinearMap.ker (g - μ • LinearMap.id)) + s ≤
      Module.finrank F V) →
    (Nat.card {H : Submodule F V //
        Module.finrank F H + 1 = Module.finrank F V ∧ H.map g ≤ H} : ℝ) *
        ((Fintype.card F : ℝ) - 1) ≤
      (Module.finrank F V : ℝ) * ((Fintype.card F : ℝ) ^ (Module.finrank F V - s) - 1)
def UDcount : Prop :=
  ∀ (F W : Type) [Field F] [Fintype F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    [Fintype W], 2 ≤ Module.finrank F W →
    ∀ (f : Submodule F W → ℂ) (H₀ : Submodule F W), Module.finrank F H₀ + 1 = Module.finrank F W →
    (∑ᶠ (ℓ : Submodule F W) (_ : Module.finrank F ℓ = 1 ∧ ¬ ℓ ≤ H₀),
      ∑ᶠ (H : Submodule F W) (_ : Module.finrank F H + 1 = Module.finrank F W ∧ ¬ ℓ ≤ H), f H) =
    (Fintype.card F : ℂ) ^ (Module.finrank F W - 2) * f H₀ +
      ((Fintype.card F : ℂ) ^ (Module.finrank F W - 1) -
          (Fintype.card F : ℂ) ^ (Module.finrank F W - 2)) *
        ∑ᶠ (H : Submodule F W) (_ : Module.finrank F H + 1 = Module.finrank F W), f H
def LHyp {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (ϖ : R) (U D : V →ₗ[R] V)
    (S B : ℕ → Submodule R V) (a d I : ℕ) : Prop :=
  (∀ s, S s ≤ B s) ∧
  (∀ s, Module.Free R (S s) ∧ Module.Finite R (S s) ∧ Module.finrank R (S s) ≤ d) ∧
  (∀ s, Module.length R (B s ⧸ (S s).comap (B s).subtype) ≤ (I : ℕ∞)) ∧
  (∀ s, ∀ φ ∈ S (s + 1), D φ ∈ B s ∧ U (D φ) = ϖ ^ a • φ)
def L3 : Prop :=
  ∀ (R V : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup V]
    [Module R V] (ϖ : R), Irreducible ϖ →
    ∀ (U D : V →ₗ[R] V) (S B : ℕ → Submodule R V) (a d I : ℕ), LHyp ϖ U D S B a d I →
    ∀ j s : ℕ, j ≤ s →
      Module.length R (S s ⧸ (S s ⊓ (S (s - j)).map (U ^ j)).comap (S s).subtype) ≤
        ((j * (a * d + I) : ℕ) : ℕ∞)
def TransferenceModuleLength : Prop :=
  ∀ (R V : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup V]
    [Module R V] (ϖ : R), Irreducible ϖ →
    ∀ (U D : V →ₗ[R] V) (S B : ℕ → Submodule R V) (a d I : ℕ), LHyp ϖ U D S B a d I →
    ∀ (j s g r : ℕ), j ≤ s → S s ≤ S 0 →
      Module.Free R (S 0 ⧸ (S s).comap (S 0).subtype) →
      Module.Finite R (S 0 ⧸ (S s).comap (S 0).subtype) →
      Module.finrank R (S 0 ⧸ (S s).comap (S 0).subtype) ≤ r →
      Module.length R (S 0 ⧸ ((S 0 ⊓ (S (s - j)).map (U ^ j)) ⊔
          (S 0).map ((ϖ ^ g) • LinearMap.id)).comap (S 0).subtype) ≤
        ((j * (a * d + I) + g * r : ℕ) : ℕ∞)
def typ {G n : ℕ} (i : Fin n → Fin G) : Fin G → ℕ := fun j => (univ.filter fun m => i m = j).card
def JetEntry : Prop :=
  ∀ (R : Type) [CommRing R] (G n : ℕ) (P : MvPolynomial (Fin G) R) (i : Fin n → Fin G),
    eval 0 ((List.ofFn i).foldr (fun j Q => pderiv j Q) P) =
      ((∏ j, (typ i j).factorial : ℕ) : R) * coeff (Finsupp.equivFunOnFinite.symm (typ i)) P
def JetNorm : Prop :=
  ∀ (G n : ℕ) (c : (Fin G → ℕ) → ℂ),
    ∑ i : Fin n → Fin G, ‖((∏ j, (typ i j).factorial : ℕ) : ℂ) * c (typ i)‖ ^ 2 =
      (n.factorial : ℝ) * ∑ e ∈ Finset.Nat.antidiagonalTuple G n,
        ((∏ j, (e j).factorial : ℕ) : ℝ) * ‖c e‖ ^ 2
def polyMap {K W : Type} [Field K] [AddCommGroup W] [Module K W] (m d : ℕ)
    (w : (Fin m → ℕ) → W) (g : Fin m → K) : W :=
  ∑ e ∈ Fintype.piFinset (fun _ : Fin m => range (d + 1)), (∏ i, g i ^ e i) • w e
def GridSpanAll : Prop :=
  ∀ (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] (m d : ℕ)
    (w : (Fin m → ℕ) → W),
    Submodule.span K (Set.range fun e : Fin m → Fin (d + 1) =>
        polyMap m d w (fun i => ((e i : ℕ) : K))) =
      Submodule.span K (Set.range (polyMap (K := K) m d w))
def GridSpanOpen : Prop :=
  ∀ (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] (m d : ℕ)
    (w : (Fin m → ℕ) → W) (P : MvPolynomial (Fin m) K), P ≠ 0 →
    Submodule.span K (polyMap m d w '' {g | eval g P ≠ 0}) =
      Submodule.span K (Set.range (polyMap (K := K) m d w))
def CoeffTorus : Prop :=
  ∀ (m : ℕ) (P : MvPolynomial (Fin m) ℂ) (M : ℝ),
    (∀ z : Fin m → ℂ, (∀ i, ‖z i‖ = 1) → ‖eval z P‖ ≤ M) → ∀ e, ‖coeff e P‖ ≤ M
def rowSubst {N n r : ℕ} (x₀ : Fin n → ℂ) (y : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (p : Fin (N + 1) × Fin n) : MvPolynomial ((Fin N × Fin r) ⊕ Fin N) ℂ :=
  Fin.cases (motive := fun _ => Fin n → MvPolynomial ((Fin N × Fin r) ⊕ Fin N) ℂ)
    (fun k => C (x₀ k))
    (fun j k => (∑ i, X (Sum.inl (j, i)) * C (y i k)) + X (Sum.inr j) * C (z k)) p.1 p.2
def vlen {n : ℕ} (x : Fin n → ℂ) : ℝ := Real.sqrt (∑ k, ‖x k‖ ^ 2)
def RowBound : Prop :=
  ∀ (N n r : ℕ) (ν : Fin (N + 1) → ℕ) (F : MvPolynomial (Fin (N + 1) × Fin n) ℂ),
    F ∈ weightedHomogeneousSubmodule ℂ (Formalism.NormUnitaryCountingLemmas.blockWt (N + 1) n) ν →
    ∀ (x₀ : Fin n → ℂ) (y : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (Rb : ℝ),
    (∀ i, vlen (y i) ≤ Rb) → vlen z ≤ 1 →
    ∀ e, ‖coeff e (aeval (rowSubst x₀ y z) F)‖ ≤
      Formalism.NormUnitaryCountingLemmas.bnorm F * vlen x₀ ^ ν 0 * ((r : ℝ) * Rb + 1) ^ (∑ j : Fin N, ν j.succ)
def Hadamard : Prop :=
  ∀ (ρ : ℕ) (A : Matrix (Fin ρ) (Fin ρ) ℂ), ‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖A i j‖ ^ 2
def HadamardMax : Prop :=
  ∀ (ρ : ℕ) (A : Matrix (Fin ρ) (Fin ρ) ℂ) (M : ℝ), (∀ i j, ‖A i j‖ ≤ M) →
    ‖A.det‖ ^ 2 ≤ ((ρ : ℝ) * M ^ 2) ^ ρ
def ProductBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : K), x ≠ 0 →
    ∀ (A : NumberField.InfinitePlace K → ℝ) (S : Finset (NumberField.FinitePlace K))
      (B : NumberField.FinitePlace K → ℝ),
      (∀ w, w x ≤ A w) → (∀ w ∈ S, w x ≤ B w) → (∀ w, w ∉ S → w x ≤ 1) →
      1 ≤ (∏ w, A w ^ w.mult) * ∏ w ∈ S, B w
def IndepExtract : Prop :=
  ∀ (k E V : Type) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] [AddCommGroup V]
    [Module E V] [Module k V] [IsScalarTower k E V] [FiniteDimensional E V]
    (v : Fin (Module.finrank k E * Module.finrank E V) → V), LinearIndependent k v →
    ∃ ι : Fin (Module.finrank E V) → Fin (Module.finrank k E * Module.finrank E V),
      Function.Injective ι ∧ LinearIndependent E (v ∘ ι)
def AmGmNorm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (a : K),
    (∀ φ : K →+* ℂ, 0 < (φ a).re ∧ (φ a).im = 0) →
    (Module.finrank ℚ K : ℝ) * |(Algebra.norm ℚ a : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ K) ≤
      ∑ φ : K →+* ℂ, (φ a).re
end Formalism.HadamardInequality


