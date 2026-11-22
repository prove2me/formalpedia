-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_EdgeSumGoodRank
-- name    : Formalism_PolynomialDimension_EdgeSumGoodRank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:29.131808+00:00
-- url     : https://prove2.me/theorems/0b18b325-c194-4a2c-8f12-563f5123b59f
-- title:
--   Edge Sum Good Rank
-- statement:
--   Definitions and structural lemmas for Edge Sum Good Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/EdgeSumGoodRank.lean

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_WeylDim
import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_SubspaceCounting_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
def KronGoodRank : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O), Irreducible π →
    ∀ (A B A' B' : Type) [AddCommGroup A] [Module O A] [Module.Free O A] [Module.Finite O A]
      [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B]
      [AddCommGroup A'] [Module O A'] [Module.Free O A'] [Module.Finite O A']
      [AddCommGroup B'] [Module O B'] [Module.Free O B'] [Module.Finite O B']
      (f : A →ₗ[O] B) (g : A' →ₗ[O] B') (n m D E : ℕ),
      Formalism.G0.GoodRank π f n D → Formalism.G0.GoodRank π g m E →
        Formalism.G0.GoodRank π (TensorProduct.map f g) (n * m) (D + E)
def KronGoodRankPi : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O), Irreducible π →
    ∀ (J : ℕ) (A B : Fin J → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module O (A j)]
      [∀ j, Module.Free O (A j)] [∀ j, Module.Finite O (A j)]
      [∀ j, AddCommGroup (B j)] [∀ j, Module O (B j)] [∀ j, Module.Free O (B j)] [∀ j, Module.Finite O (B j)]
      (f : ∀ j, A j →ₗ[O] B j) (n D : Fin J → ℕ),
      (∀ j, Formalism.G0.GoodRank π (f j) (n j) (D j)) →
        Formalism.G0.GoodRank π (PiTensorProduct.map f) (∏ j, n j) (∑ j, D j)
def ShareProd : Prop :=
  ∀ (J : ℕ) (κ : Fin J → ℝ) (n d : Fin J → ℕ), (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) →
    (∀ j, (1 - κ j) * (d j : ℝ) ≤ n j) →
      (1 - ∑ j, κ j) * ((∏ j, d j : ℕ) : ℝ) ≤ ((∏ j, n j : ℕ) : ℝ)
def MultinomialKLog : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (c k : ℕ) (α : Fin c → ℕ) (a : ℝ), 5 ≤ p → c ≤ k → 1 ≤ a →
    ((∑ i, α i : ℕ) : ℝ) ≤ 2 * a →
      (padicValNat p ((∑ i, α i).factorial / ∏ i, (α i).factorial) : ℝ) ≤ k * Real.logb p a
def FockGaussKLog : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ Z : Type) [Fintype σ] [DecidableEq σ] [Fintype Z] [DecidableEq Z]
    (letter : σ → Z) (d : Z → ℕ) (N k : ℕ) (a : ℝ), 5 ≤ p → 1 ≤ a →
    Fintype.card Z ≤ 2 * N → (∀ z, (univ.filter fun i => letter i = z).card ≤ k) → (∀ z, (d z : ℝ) ≤ 2 * a) →
    ∀ F : MvPolynomial σ ℚ, IsLetterHom letter d F →
      vG p F + (((padicValNat p (∏ z, (d z).factorial) : ℝ) / 2 -
          (2 * N * k * Real.logb p a) / 2 : ℝ) : WithTop ℝ) ≤ vBB p F ∧
        vBB p F ≤ vG p F + (((padicValNat p (∏ z, (d z).factorial) : ℝ) / 2 : ℝ) : WithTop ℝ)
def KeyPower : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (d : ℕ) (ι σ : Type) [Fintype ι] (u v : ι → σ) (wu wv : σ → ℕ),
    (∀ i, wu (u i) = 1 ∧ wu (v i) = 0 ∧ wv (u i) = 0 ∧ wv (v i) = 1) →
      ∃ R : MvPolynomial σ ℤ,
        (∑ i, X (u i) * X (v i)) ^ (p ^ d) = ∑ i, (X (u i) * X (v i)) ^ (p ^ d) + C (p : ℤ) * R ∧
          R.IsWeightedHomogeneous wu (p ^ d) ∧ R.IsWeightedHomogeneous wv (p ^ d)
def DegZRoom : Prop :=
  ∀ (A c o La k de C N₁ Ib b' : ℝ), 0 < k → 0 ≤ A → 4 ≤ C → 1 ≤ N₁ → 0 ≤ La → 0 ≤ Ib → 0 < b' →
    de = C * N₁ * La / k + 2 * Ib / b' → o ≤ c + La * A / k → c < A * (1 - de / 2) →
      de * A / 4 ≤ A - o
def dd {K σ : Type} [Field K] (x : σ) (m : ℕ) (f : MvPolynomial σ K) : MvPolynomial σ K :=
  C ((m.factorial : K)⁻¹) * (⇑(pderiv x))^[m] f
def DerivE : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type) [DecidableEq σ] (x : σ) (y r f : MvPolynomial σ K),
    x ∉ y.vars → x ∉ r.vars → ∀ j m : ℕ,
      X x ^ m * dd x m ((X x * y + r) ^ j * f) =
        ∑ l ∈ range (m + 1), C (j.choose l : K) * (X x * y + r) ^ (j - l) * (X x * y) ^ l * X x ^ (m - l) *
          dd x (m - l) f
def DerivS : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type) [DecidableEq σ] (s : σ) (z r y : MvPolynomial σ K),
    s ∉ z.vars → s ∉ r.vars → s ∉ y.vars → ∀ j m : ℕ,
      X s ^ m * dd s m ((z * X s + r) ^ j * y) = C (j.choose m : K) * (z * X s) ^ m * (z * X s + r) ^ (j - m) * y
def DerivZ : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type) [DecidableEq σ] (zv : σ) (s r y : MvPolynomial σ K),
    zv ∉ s.vars → zv ∉ r.vars → zv ∉ y.vars → ∀ j n m : ℕ,
      X zv ^ m * dd zv m ((X zv * s + r) ^ j * X zv ^ n * y) =
        ∑ l ∈ range (m + 1), C ((j.choose l * n.choose (m - l) : ℕ) : K) * (X zv * s) ^ l *
          (X zv * s + r) ^ (j - l) * X zv ^ n * y
def PartnerGoodRank : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O), Irreducible π →
    ∀ (A B : Type) [AddCommGroup A] [Module O A] [Module.Free O A] [Module.Finite O A]
      [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B]
      (b : A →ₗ[O] Module.Dual O B) (n D : ℕ) (g : (Fin n → O) →ₗ[O] A),
      (∀ x : Fin n → O, (∃ i, ¬ π ∣ x i) → ∃ u' : B, ¬ π ^ (D + 1) ∣ b (g x) u') →
        Formalism.G0.GoodRank π b n D
def EdgeSumGoodRank : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O), Irreducible π →
    ∀ (B : Type) [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B]
      (M : ℕ) (n : Fin M → ℕ) (β : ∀ e : Fin M, (Fin (n e) → O) →ₗ[O] Module.Dual O B) (D c : ℕ), D < c →
      (∀ (e : Fin M) (x : Fin (n e) → O), (∃ i, ¬ π ∣ x i) →
        ∃ G : B, ¬ π ^ (D + 1) ∣ β e x G ∧ ∀ e', e' ≠ e → ∀ y : Fin (n e') → O, π ^ c ∣ β e' y G) →
        Formalism.G0.GoodRank π (LinearMap.lsum O (fun e : Fin M => Fin (n e) → O) O β) (∑ e, n e) D
def RoomI : Prop :=
  ∀ Cm : ℝ, 0 ≤ Cm → ∃ C : ℝ, 1 ≤ C ∧ ∀ C₀ : ℝ, 1 ≤ C₀ →
    ∀ (p N N₁ k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ),
      HypI C C₀ p N N₁ k n' G' Y Yb a b' Ib cl D cStar →
      12 * constantBudget p N k n' a cl cStar + ((N₁ : ℝ) + 1) * (Cm * k * N₁ * (p : ℝ) ^ G' * constantBudget p N k n' a cl cStar) ≤
        (2 * Ib / b') * (b' / (2 * (p : ℝ) ^ G')) / 4
end Formalism.CountingSumsFrames


