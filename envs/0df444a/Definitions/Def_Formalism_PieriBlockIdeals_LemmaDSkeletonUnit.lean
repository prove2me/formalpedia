-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_LemmaDSkeletonUnit
-- name    : Formalism_PieriBlockIdeals_LemmaDSkeletonUnit
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:31:16.265873+00:00
-- url     : https://prove2.me/theorems/233445cd-ae5d-4abc-8a58-a6e38b3133ad
-- title:
--   Lemma DSkeleton Unit
-- statement:
--   Definitions and structural lemmas for Lemma DSkeleton Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/LemmaDSkeletonUnit.lean

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_IntegralQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace Formalism.CohomologicalDescent.BinaryFormsExample
open Formalism.CohomologicalDescent.Symmetrization
def GoodPartAbstract : Prop :=
  ∀ (K M I : Type) [Field K] [AddCommGroup M] [Module K M] (n : ℕ) (c : Fin n → Module.End K M)
    (Mt : I → Submodule K M) (χ : I → Fin n → K), (∀ τ a, ∀ m ∈ Mt τ, c a m = χ τ a • m) →
    (⨆ τ, Mt τ) = ⊤ → ∀ w : K,
    LinearMap.range (w ^ n • (1 : Module.End K M) + ∑ a : Fin n, w ^ a.val • c a) =
      ⨆ τ ∈ {τ : I | w ^ n + ∑ a : Fin n, χ τ a * w ^ a.val ≠ 0}, Mt τ
def GoodPart : Prop :=
  ∀ (K R P M I : Type) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq R] [DecidableEq P]
    [Fintype R] [Fintype P] (EM : R → R → Module.End K M), GlRel EM →
    ∀ (n : ℕ) (Mt : I → Submodule K (Sym (R × P) n → M)) (χ : I → Fin n → K),
    (∀ (τ : I) (a : Fin n) (z : Tens R P M n), toSym K z ∈ Mt τ →
      toSym K ((AApoly K EM n).coeff a.val z) = χ τ a • toSym K z) →
    (⨆ τ, Mt τ) = ⊤ → ∀ (w : K) (good : Set I),
    (∀ τ, τ ∉ good → (X ^ n + ∑ a : Fin n, C (χ τ a) * X ^ a.val : K[X]).eval w = 0) →
    (∀ z : Tens R P M n, toSym K (AA K EM n w z) ∈ ⨆ τ ∈ good, Mt τ) ∧
      ((∀ τ ∈ good, (X ^ n + ∑ a : Fin n, C (χ τ a) * X ^ a.val : K[X]).eval w ≠ 0) →
        ∀ y ∈ ⨆ τ ∈ good, Mt τ, ∃ z : Tens R P M n, y = toSym K (AA K EM n w z))
def Contra {k V P R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    (S : HidaSetting k V P R) (B : LinearMap.BilinForm k V) : Prop :=
  ∀ a b x y, B (S.E a b x) y = B x (S.E b a y)
def Generated {k V P R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    (S : HidaSetting k V P R) : Prop :=
  ∀ U : Submodule k V, S.W ≤ U → (∀ a b, ∀ x ∈ U, S.E a b x ∈ U) → U = ⊤
def DeltaAll {O K V P R : Type*} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R] (S : HidaSetting K V P R)
    (DelL : Submodule O S.W) : Submodule O V :=
  ⨆ n, S.DeltaN n DelL
def NablaL {O K V P R : Type*} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] [DecidableEq P] [DecidableEq R] (S : HidaSetting K V P R) (B : LinearMap.BilinForm K V)
    (DelL : Submodule O S.W) : Submodule O S.W :=
  (B.restrict S.W).dualSubmodule DelL
def NablaSpec : Prop :=
  ∀ (O K V P R : Type) [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R] (S : HidaSetting K V P R)
    (B : LinearMap.BilinForm K V) (DelL : Submodule O S.W),
    (∀ v : V, v ∈ B.dualSubmodule (DeltaAll S DelL) ↔ ∀ x ∈ DeltaAll S DelL, ∃ c : O, B v x = algebraMap O K c) ∧
      ∀ u : S.W, u ∈ NablaL S B DelL ↔ ∀ x ∈ DelL, ∃ c : O, B (u : V) (x : V) = algebraMap O K c
def ContraWord : Prop :=
  ∀ (k V P R : Type) [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    (S : HidaSetting k V P R) (B : LinearMap.BilinForm k V), Contra S B → ∀ (n : ℕ) (x y : V),
    (∀ g : Fin n → R × P, B (S.Fw g x) y = B x (S.Ew g y) ∧ B x (S.Fw g y) = B (S.Ew g x) y) ∧
      ∀ m : Sym (R × P) n, B (S.Fs m x) y = B x (S.Es m y) ∧ B x (S.Fs m y) = B (S.Es m x) y
def ContraIota : Prop :=
  ∀ (k V P R : Type) [Field k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R]
    (S : HidaSetting k V P R) (B : LinearMap.BilinForm k V), Contra S B → ∀ (n : ℕ) (m : Sym (R × P) n) (u v : V),
    B (((mfact m : k)⁻¹) • S.Fs m u) v = B u (S.iota n v m) ∧ B v (((mfact m : k)⁻¹) • S.Fs m u) = B (S.iota n v m) u
def WeightOrthogonal : Prop :=
  ∀ (k V P R : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    (S : HidaSetting k V P R) (B : LinearMap.BilinForm k V), Contra S B → ∀ κ κ' : P ⊕ R → ℤ, κ ≠ κ' →
    ∀ x ∈ S.wt κ, ∀ y ∈ S.wt κ', B x y = 0
def DepthEigen : Prop :=
  ∀ (k V P R : Type) [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R]
    (S : HidaSetting k V P R) (n : ℕ) (z : Tens R P S.W n),
    (∑ α : P, S.E (Sum.inl α) (Sum.inl α)) (S.mu n z) = ((Fintype.card P : k) * S.w - (n : k)) • S.mu n z
def DepthOrthogonal : Prop :=
  ∀ (k V P R : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    [Fintype P] [Fintype R] (S : HidaSetting k V P R) (B : LinearMap.BilinForm k V), Contra S B →
    ∀ n n' : ℕ, n ≠ n' → ∀ (z : Tens R P S.W n) (z' : Tens R P S.W n'), B (S.mu n z) (S.mu n' z') = 0
def DepthSpan : Prop :=
  ∀ (k V P R : Type) [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R]
    (S : HidaSetting k V P R),
    LinearMap.range (S.mu 0) = S.W ∧
    (∀ (n : ℕ) (v : R × P) (z : Tens R P S.W n), S.f v (S.mu n z) ∈ LinearMap.range (S.mu (n + 1))) ∧
    (∀ (n : ℕ) (v : R × P) (z : Tens R P S.W (n + 1)), S.e v (S.mu (n + 1) z) ∈ LinearMap.range (S.mu n)) ∧
    (∀ (v : R × P) (z : Tens R P S.W 0), S.e v (S.mu 0 z) = 0) ∧
    (∀ (n : ℕ) (z : Tens R P S.W n), (∀ c d : R, S.E (Sum.inr c) (Sum.inr d) (S.mu n z) ∈ LinearMap.range (S.mu n)) ∧
      ∀ α β : P, S.E (Sum.inl α) (Sum.inl β) (S.mu n z) ∈ LinearMap.range (S.mu n)) ∧
    (∀ a b, ∀ x ∈ ⨆ n, LinearMap.range (S.mu n), S.E a b x ∈ ⨆ n, LinearMap.range (S.mu n)) ∧
    (Generated S → (⨆ n, LinearMap.range (S.mu n)) = ⊤)
def IotaKernel : Prop :=
  ∀ (k V P R : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    [Fintype P] [Fintype R] (S : HidaSetting k V P R) (B : LinearMap.BilinForm k V), Contra S B →
    ∀ (n : ℕ) (v : V), (∀ m, S.iota n v m = 0) → ∀ z : Tens R P S.W n, B (S.mu n z) v = 0
def IotaInjectiveLocal : Prop :=
  ∀ (k V P R : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    [Fintype P] [Fintype R] (S : HidaSetting k V P R) (B : LinearMap.BilinForm k V), Contra S B → ∀ n : ℕ,
    (∀ z : Tens R P S.W n, (∀ z' : Tens R P S.W n, B (S.mu n z') (S.mu n z) = 0) → S.mu n z = 0) →
    ∀ z : Tens R P S.W n, (∀ m, S.iota n (S.mu n z) m = 0) → S.mu n z = 0
def IotaInjective : Prop :=
  ∀ (k V P R : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    [Fintype P] [Fintype R] (S : HidaSetting k V P R) (B : LinearMap.BilinForm k V), Contra S B → Generated S →
    (∀ v : V, (∀ x : V, B x v = 0) → v = 0) →
    ∀ (n : ℕ) (z : Tens R P S.W n), (∀ m, S.iota n (S.mu n z) m = 0) → S.mu n z = 0
def NablaCriterion : Prop :=
  ∀ (O K V P R : Type) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R] (S : HidaSetting K V P R)
    (B : LinearMap.BilinForm K V) (DelL : Submodule O S.W), Contra S B → ∀ (n : ℕ) (z : Tens R P S.W n),
    (S.mu n z ∈ B.dualSubmodule (DeltaAll S DelL) ↔
      ∀ m, ∃ u ∈ NablaL S B DelL, S.iota n (S.mu n z) m = (u : V))
def DualStable : Prop :=
  ∀ (O K V P R : Type) [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] [DecidableEq P] [DecidableEq R] (S : HidaSetting K V P R)
    (B : LinearMap.BilinForm K V) (DelL : Submodule O S.W), Contra S B →
    (∀ b b', ∀ u ∈ DelL, S.EW b b' u ∈ DelL) → ∀ b b', ∀ u ∈ NablaL S B DelL, S.EW b b' u ∈ NablaL S B DelL
def shapesAll (p i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : Finset (Fin q → ℕ) :=
  (Fintype.piFinset fun a : Fin q => Finset.Icc (lam2 a) (lam2 a + i)).filter fun tau =>
    (∀ a b : Fin q, a ≤ b → tau b ≤ tau a) ∧ ∑ a, tau a = ∑ a, lam2 a + i ∧
      (∀ b : Fin q, ∀ j < tau b, LD.colLen lam2 tau j ≤ p)
def MemShapes : Prop :=
  ∀ (p w i q : ℕ) (lam2 tau : Fin q → ℕ),
    tau ∈ LD.shapes p w i lam2 ↔ tau ∈ shapesAll p i lam2 ∧ LD.boxesOfContent lam2 tau (w : ℤ) = 0
def ShapeEvalZero : Prop :=
  ∀ (q : ℕ) (lam2 tau : Fin q → ℕ) (c : ℤ), (shapePoly lam2 tau).eval c = 0 ↔ LD.boxesOfContent lam2 tau c ≠ 0
def ShapeCoeff : Prop :=
  ∀ (A : Type) [CommRing A] (p i q : ℕ) (lam2 : Fin q → ℕ), ∀ tau ∈ shapesAll p i lam2,
    (X ^ i + ∑ a : Fin i, C (((shapePoly lam2 tau).coeff a.val : ℤ) : A) * X ^ a.val : A[X]) =
      (shapePoly lam2 tau).map (Int.castRingHom A)
def ShapeDvdField : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (p w i q : ℕ) (lam2 : Fin q → ℕ), (∀ b, lam2 b ≤ w) →
    (∀ tau ∈ LD.shapes p w i lam2,
      (X ^ i + ∑ a : Fin i, C (((shapePoly lam2 tau).coeff a.val : ℤ) : K) * X ^ a.val : K[X]) ∣
        ((DnPoly p w i lam2).map (Int.castRingHom O)).map (algebraMap O K)) ∧
    ((DnPoly p w i lam2).map (Int.castRingHom O)).eval (w : O) = ((LD.Dn p w i lam2 : ℤ) : O) ∧
    ∀ tau ∈ shapesAll p i lam2, tau ∉ LD.shapes p w i lam2 →
      (X ^ i + ∑ a : Fin i, C (((shapePoly lam2 tau).coeff a.val : ℤ) : K) * X ^ a.val : K[X]).eval (w : K) = 0
def UnitClause : Prop :=
  ∀ (O V : Type) [CommRing O] [AddCommGroup V] [Module O V] (Del : Submodule O V) (l D η : O) (e a : ℕ) (v : V),
    IsUnit η → D = η * l ^ a → (l ^ e * D) • v ∈ Del → l ^ (e + a) • v ∈ Del
def ValuationUnit : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ), l.Prime → (∀ m : ℤ, ¬ (l : ℤ) ∣ m → IsUnit (m : O)) →
    ∀ D : ℤ, D ≠ 0 → ∃ η : O, IsUnit η ∧ (D : O) = η * (l : O) ^ padicValInt l D
def LemmaDSkeletonUnit : Prop :=
  ∀ (O K V P R I : Type) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R] (S : HidaSetting K V P R) (n : ℕ)
    (wO : O) (nabL DelL : Submodule O S.W) (Mt : I → Submodule K (Sym (R × P) n → S.W)) (χ : I → Fin n → K)
    (Dn : O[X]) (xi : (P ⊕ R → ℤ) →+ ℤ) (lam : P ⊕ R → ℤ) (l : O) (e : ℕ) (i' : ℤ),
    S.w = algebraMap O K wO →
    (∀ b b', ∀ u ∈ nabL, S.EW b b' u ∈ nabL) →
    (∀ z : Tens R P S.W n, (∀ m, S.iota n (S.mu n z) m = 0) → S.mu n z = 0) →
    (∀ (τ : I) (a : Fin n) (z : Tens R P S.W n), toSym K z ∈ Mt τ →
      toSym K ((AApoly K S.EW n).coeff a.val z) = χ τ a • toSym K z) →
    (∀ τ, (X ^ n + ∑ a : Fin n, C (χ τ a) * X ^ a.val : K[X]) ∣ Dn.map (algebraMap O K)) →
    (∀ z : Tens R P S.W n, toSym K (AA K S.EW n S.w z) ∈ ⨆ τ, Mt τ) →
    (∀ (α : P) (b : R), 0 ≤ xi (Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1)) →
    (∀ κ, xi (lam - κ) ≤ i' → ∀ u ∈ nabL, (u : V) ∈ S.wt κ → l ^ e • u ∈ DelL) →
    ∀ ν, xi (lam - ν) ≤ i' → ∀ z : Tens R P S.W n, S.mu n z ∈ S.wt ν →
      (∀ m, ∃ u ∈ nabL, S.iota n (S.mu n z) m = (u : V)) →
      ∀ (a : ℕ) (η : O), IsUnit η → Dn.eval wO = η * l ^ a → l ^ (e + a) • S.mu n z ∈ S.DeltaN n DelL
structure LemmaDInputs {O K V P : Type} {q : ℕ} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [DecidableEq P] [Fintype P] (S : HidaSetting K V P (Fin q))
    (B : LinearMap.BilinForm K V) (n w : ℕ) (lam2 : Fin q → ℕ) (DelL : Submodule O S.W)
    (Mt : (Fin q → ℕ) → Submodule K (Sym (Fin q × P) n → S.W)) (xi : (P ⊕ Fin q → ℤ) →+ ℤ) (lam : P ⊕ Fin q → ℤ)
    (l : O) (e : ℕ) (i' : ℤ) : Prop where

  scalar : S.w = (w : K)

  le_w : ∀ b, lam2 b ≤ w

  contra : Contra S B

  generated : Generated S

  nondeg : ∀ v : V, (∀ x : V, B x v = 0) → v = 0

  stable : ∀ b b', ∀ u ∈ DelL, S.EW b b' u ∈ DelL

  eigen : ∀ τ ∈ shapesAll (Fintype.card P) n lam2, ∀ (a : Fin n) (z : Tens (Fin q) P S.W n), toSym K z ∈ Mt τ →
    toSym K ((AApoly K S.EW n).coeff a.val z) = (((shapePoly lam2 τ).coeff a.val : ℤ) : K) • toSym K z

  decomp : (⨆ τ ∈ shapesAll (Fintype.card P) n lam2, Mt τ) = ⊤

  dominant : ∀ (α : P) (b : Fin q), 0 ≤ xi (Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1)

  expL : ∀ κ, xi (lam - κ) ≤ i' → ∀ u ∈ NablaL S B DelL, (u : V) ∈ S.wt κ → l ^ e • u ∈ DelL
def LemmaDSkeleton2 : Prop :=
  ∀ (O K V P : Type) (q : ℕ) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [DecidableEq P] [Fintype P] (S : HidaSetting K V P (Fin q))
    (B : LinearMap.BilinForm K V) (n w : ℕ) (lam2 : Fin q → ℕ) (DelL : Submodule O S.W)
    (Mt : (Fin q → ℕ) → Submodule K (Sym (Fin q × P) n → S.W)) (xi : (P ⊕ Fin q → ℤ) →+ ℤ) (lam : P ⊕ Fin q → ℤ)
    (l : O) (e : ℕ) (i' : ℤ), LemmaDInputs S B n w lam2 DelL Mt xi lam l e i' →
    ∀ ν, xi (lam - ν) ≤ i' → ∀ v ∈ B.dualSubmodule (DeltaAll S DelL), v ∈ LinearMap.range (S.mu n) → v ∈ S.wt ν →
      (l ^ e * ((LD.Dn (Fintype.card P) w n lam2 : ℤ) : O)) • v ∈ S.DeltaN n DelL ∧
        ∀ (a : ℕ) (η : O), IsUnit η → ((LD.Dn (Fintype.card P) w n lam2 : ℤ) : O) = η * l ^ a →
          l ^ (e + a) • v ∈ S.DeltaN n DelL
def LemmaDSkeleton2Val : Prop :=
  ∀ (O K V P : Type) (q : ℕ) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [DecidableEq P] [Fintype P] (S : HidaSetting K V P (Fin q))
    (B : LinearMap.BilinForm K V) (n w : ℕ) (lam2 : Fin q → ℕ) (DelL : Submodule O S.W)
    (Mt : (Fin q → ℕ) → Submodule K (Sym (Fin q × P) n → S.W)) (xi : (P ⊕ Fin q → ℤ) →+ ℤ) (lam : P ⊕ Fin q → ℤ)
    (l : ℕ) (e : ℕ) (i' : ℤ), l.Prime → (∀ m : ℤ, ¬ (l : ℤ) ∣ m → IsUnit (m : O)) →
    LemmaDInputs S B n w lam2 DelL Mt xi lam (l : O) e i' →
    ∀ ν, xi (lam - ν) ≤ i' → ∀ v ∈ B.dualSubmodule (DeltaAll S DelL), v ∈ LinearMap.range (S.mu n) → v ∈ S.wt ν →
      (l : O) ^ (e + padicValInt l (LD.Dn (Fintype.card P) w n lam2)) • v ∈ S.DeltaN n DelL
def GL2PieriInstance : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) →
    ∀ y d : ℕ, 1 ≤ d →
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module K V) (_ : Module O V) (_ : IsScalarTower O K V)
      (S : HidaSetting K V Unit (Fin 1)) (B : LinearMap.BilinForm K V) (DelL : Submodule O S.W)
      (Mt : (Fin 1 → ℕ) → Submodule K (Sym (Fin 1 × Unit) 1 → S.W)) (xi : (Unit ⊕ Fin 1 → ℤ) →+ ℤ)
      (lam ν : Unit ⊕ Fin 1 → ℤ) (v : V),
      (∀ l : O, LemmaDInputs S B 1 (y + d) (fun _ => y) DelL Mt xi lam l 0 1) ∧
      LD.Dn (Fintype.card Unit) (y + d) 1 (fun _ : Fin 1 => y) = (d : ℤ) ∧
      xi (lam - ν) ≤ 1 ∧ v ∈ B.dualSubmodule (DeltaAll S DelL) ∧ v ∈ LinearMap.range (S.mu 1) ∧ v ∈ S.wt ν ∧
      ∀ c : O, c • v ∈ S.DeltaN 1 DelL ↔ (d : O) ∣ c
def DepthOfWeight : Prop :=
  ∀ (k V P R : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    [Fintype P] [Fintype R] (S : HidaSetting k V P R) (w n : ℕ), S.w = (w : k) → Generated S →
    ∀ (ν : P ⊕ R → ℤ) (v : V), v ∈ S.wt ν → ∑ α : P, ν (Sum.inl α) + (n : ℤ) = (Fintype.card P : ℤ) * (w : ℤ) →
      v ∈ LinearMap.range (S.mu n)
def DeltaDepth : Prop :=
  ∀ (O K V P R : Type) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R] (S : HidaSetting K V P R)
    (DelL : Submodule O S.W) (n : ℕ) (x : V),
    x ∈ S.DeltaN n DelL ↔ x ∈ DeltaAll S DelL ∧ x ∈ LinearMap.range (S.mu n)
def LemmaDSkeleton2Lit : Prop :=
  ∀ (O K V P : Type) (q : ℕ) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [DecidableEq P] [Fintype P] (S : HidaSetting K V P (Fin q))
    (B : LinearMap.BilinForm K V) (n w : ℕ) (lam2 : Fin q → ℕ) (DelL : Submodule O S.W)
    (Mt : (Fin q → ℕ) → Submodule K (Sym (Fin q × P) n → S.W)) (xi : (P ⊕ Fin q → ℤ) →+ ℤ) (lam : P ⊕ Fin q → ℤ)
    (l : ℕ) (e : ℕ) (i' : ℤ), l.Prime → (∀ m : ℤ, ¬ (l : ℤ) ∣ m → IsUnit (m : O)) →
    LemmaDInputs S B n w lam2 DelL Mt xi lam (l : O) e i' →
    ∀ ν, ∑ α : P, ν (Sum.inl α) + (n : ℤ) = (Fintype.card P : ℤ) * (w : ℤ) → xi (lam - ν) ≤ i' →
      ∀ v ∈ B.dualSubmodule (DeltaAll S DelL), v ∈ S.wt ν →
      (l : O) ^ (e + padicValInt l (LD.Dn (Fintype.card P) w n lam2)) • v ∈ DeltaAll S DelL ∧
        (l : O) ^ (e + padicValInt l (LD.Dn (Fintype.card P) w n lam2)) • v ∈ S.wt ν
def Dpart (k : Type*) {R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] {n : ℕ} [DecidableEq R] [DecidableEq P]
    (EM : R → R → Module.End k M) (j : ℕ) (b b' : R) : Module.End k (Tens R P M n) :=
  onM k (EM b b') + ∑ s ∈ Finset.univ.filter (fun s : Fin n => s.val < j), unitY k s b b'
def Cas (k : Type*) {R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] {n : ℕ} [DecidableEq R] [DecidableEq P]
    [Fintype R] (EM : R → R → Module.End k M) (j : ℕ) : Module.End k (Tens R P M n) :=
  ∑ b, ∑ b', Dpart k EM j b b' * Dpart k EM j b' b
def CasimirJM : Prop :=
  ∀ (k R P M : Type) [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P] [Fintype R]
    (EM : R → R → Module.End k M) (n : ℕ) (j : Fin n),
    (Cas k EM (j.val + 1) - Cas k EM j.val : Module.End k (Tens R P M n)) =
      2 • xJM k EM j + Fintype.card R • (1 : Module.End k (Tens R P M n))
def casVal {q : ℕ} (κ : Fin q → ℕ) : ℤ := ∑ b : Fin q, (κ b : ℤ) * ((κ b : ℤ) + (q : ℤ) - 1 - 2 * (b.val : ℤ))
structure IsPath {q : ℕ} (n : ℕ) (lam2 tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q) : Prop where

  start : κ 0 = lam2

  step : ∀ j : Fin n, κ (j.val + 1) = κ j.val + Pi.single (ρ j) 1

  stop : κ n = tau

  dom : ∀ j ≤ n, Antitone (κ j)
noncomputable def pathPoly {q n : ℕ} (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q) : ℤ[X] :=
  ∏ j : Fin n, (X - C ((κ j.val (ρ j) : ℤ) - ((ρ j).val : ℤ)))
def PathEigen : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q),
    (∀ j : Fin n, κ (j.val + 1) = κ j.val + Pi.single (ρ j) 1) → ∀ z : Tens (Fin q) P M n,
    (∀ j ≤ n, Cas K EM j z = ((casVal (κ j) : ℤ) : K) • z) →
    (∀ j : Fin n, xJM K EM j z = (((κ j.val (ρ j) : ℤ) - ((ρ j).val : ℤ) : ℤ) : K) • z) ∧
      ∀ a : ℕ, (AApoly K EM n).coeff a z = (((pathPoly κ ρ).coeff a : ℤ) : K) • z
def PathShape : Prop :=
  ∀ (q n : ℕ) (lam2 tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ →
    pathPoly κ ρ = shapePoly lam2 tau ∧ (∀ b, lam2 b ≤ tau b ∧ tau b ≤ lam2 b + n) ∧ ∑ b, tau b = ∑ b, lam2 b + n
def PathSpace (K : Type*) {P M : Type*} {q : ℕ} [Field K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 tau : Fin q → ℕ) : Submodule K (Tens (Fin q) P M n) :=
  Submodule.span K {z | ∃ (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ ∧
    ∀ j ≤ n, Cas K EM j z = ((casVal (κ j) : ℤ) : K) • z}
def PathSpaceEigen : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P] [Fintype P]
    (EM : Fin q → Fin q → Module.End K M), GlRel EM → ∀ (n : ℕ) (lam2 tau : Fin q → ℕ) (a : Fin n)
    (z : Tens (Fin q) P M n), toSym K z ∈ (PathSpace K EM n lam2 tau).map (toSym K) →
    toSym K ((AApoly K EM n).coeff a.val z) = (((shapePoly lam2 tau).coeff a.val : ℤ) : K) • toSym K z
def PathDecomp : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [AddCommGroup M] [Module K M] [DecidableEq P] [Fintype P]
    (EM : Fin q → Fin q → Module.End K M) (n p : ℕ) (lam2 : Fin q → ℕ),
    (⨆ tau, PathSpace K (P := P) EM n lam2 tau) = ⊤ →
    (∀ tau, (∃ b : Fin q, ∃ j < tau b, p < LD.colLen lam2 tau j) →
      ∀ z ∈ PathSpace K (P := P) EM n lam2 tau, toSym K z = 0) →
    (⨆ tau ∈ shapesAll p n lam2, (PathSpace K (P := P) EM n lam2 tau).map (toSym K)) = ⊤
structure LemmaDInputs3 {O K V P : Type} {q : ℕ} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [DecidableEq P] [Fintype P] (S : HidaSetting K V P (Fin q))
    (B : LinearMap.BilinForm K V) (n w : ℕ) (lam2 : Fin q → ℕ) (DelL : Submodule O S.W)
    (xi : (P ⊕ Fin q → ℤ) →+ ℤ) (lam : P ⊕ Fin q → ℤ) (l : O) (e : ℕ) (i' : ℤ) : Prop where

  scalar : S.w = (w : K)

  le_w : ∀ b, lam2 b ≤ w

  contra : Contra S B

  generated : Generated S

  nondeg : ∀ v : V, (∀ x : V, B x v = 0) → v = 0

  stable : ∀ b b', ∀ u ∈ DelL, S.EW b b' u ∈ DelL

  pieri : (⨆ tau, PathSpace K (P := P) S.EW n lam2 tau) = ⊤

  columns : ∀ tau, (∃ b : Fin q, ∃ j < tau b, Fintype.card P < LD.colLen lam2 tau j) →
    ∀ z ∈ PathSpace K (P := P) S.EW n lam2 tau, toSym K z = 0

  dominant : ∀ (α : P) (b : Fin q), 0 ≤ xi (Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1)

  expL : ∀ κ, xi (lam - κ) ≤ i' → ∀ u ∈ NablaL S B DelL, (u : V) ∈ S.wt κ → l ^ e • u ∈ DelL
def InputsFromPieri : Prop :=
  ∀ (O K V P : Type) (q : ℕ) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [DecidableEq P] [Fintype P] (S : HidaSetting K V P (Fin q))
    (B : LinearMap.BilinForm K V) (n w : ℕ) (lam2 : Fin q → ℕ) (DelL : Submodule O S.W)
    (xi : (P ⊕ Fin q → ℤ) →+ ℤ) (lam : P ⊕ Fin q → ℤ) (l : O) (e : ℕ) (i' : ℤ),
    LemmaDInputs3 S B n w lam2 DelL xi lam l e i' →
    LemmaDInputs S B n w lam2 DelL (fun tau => (PathSpace K S.EW n lam2 tau).map (toSym K)) xi lam l e i'
def LemmaDSkeleton3 : Prop :=
  ∀ (O K V P : Type) (q : ℕ) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [DecidableEq P] [Fintype P] (S : HidaSetting K V P (Fin q))
    (B : LinearMap.BilinForm K V) (n w : ℕ) (lam2 : Fin q → ℕ) (DelL : Submodule O S.W)
    (xi : (P ⊕ Fin q → ℤ) →+ ℤ) (lam : P ⊕ Fin q → ℤ)
    (l : ℕ) (e : ℕ) (i' : ℤ), l.Prime → (∀ m : ℤ, ¬ (l : ℤ) ∣ m → IsUnit (m : O)) →
    LemmaDInputs3 S B n w lam2 DelL xi lam (l : O) e i' →
    ∀ ν, ∑ α : P, ν (Sum.inl α) + (n : ℤ) = (Fintype.card P : ℤ) * (w : ℤ) → xi (lam - ν) ≤ i' →
      ∀ v ∈ B.dualSubmodule (DeltaAll S DelL), v ∈ S.wt ν →
      (l : O) ^ (e + padicValInt l (LD.Dn (Fintype.card P) w n lam2)) • v ∈ DeltaAll S DelL ∧
        (l : O) ^ (e + padicValInt l (LD.Dn (Fintype.card P) w n lam2)) • v ∈ S.wt ν
def GL2PieriInstanceRankThree : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) →
    ∀ y d : ℕ, 1 ≤ d →
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module K V) (_ : Module O V) (_ : IsScalarTower O K V)
      (S : HidaSetting K V Unit (Fin 1)) (B : LinearMap.BilinForm K V) (DelL : Submodule O S.W)
      (xi : (Unit ⊕ Fin 1 → ℤ) →+ ℤ) (lam ν : Unit ⊕ Fin 1 → ℤ) (v : V),
      (∀ l : O, LemmaDInputs3 S B 1 (y + d) (fun _ => y) DelL xi lam l 0 1) ∧
      LD.Dn (Fintype.card Unit) (y + d) 1 (fun _ : Fin 1 => y) = (d : ℤ) ∧
      ∑ α : Unit, ν (Sum.inl α) + ((1 : ℕ) : ℤ) = (Fintype.card Unit : ℤ) * ((y + d : ℕ) : ℤ) ∧
      xi (lam - ν) ≤ 1 ∧ v ∈ B.dualSubmodule (DeltaAll S DelL) ∧ v ∈ S.wt ν ∧
      ∀ c : O, c • v ∈ DeltaAll S DelL ↔ (d : O) ∣ c
end Formalism.CohomologicalDescent.BinaryFormsExample


