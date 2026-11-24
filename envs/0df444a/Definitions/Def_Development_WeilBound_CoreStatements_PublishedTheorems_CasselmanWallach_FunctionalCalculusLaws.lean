-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:51.487599+00:00
-- url     : https://prove2.me/theorems/b1ee9ca5-3470-447c-83ea-447f15250156
-- title:
--   Functional Calculus Laws
-- statement:
--   Definitions and structural lemmas for Functional Calculus Laws, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/FunctionalCalculusLaws.lean

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
namespace PositivityTheory.CW
def ForMod (P : ∀ (n : ℕ) (_ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V],
    (Fin n → Fin n → Module.End ℂ V) → Prop) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Mod ε E → P n ε V E
def ForBas (P : ∀ (n : ℕ) (_ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V],
    (Fin n → Fin n → Module.End ℂ V) → ∀ ι : Type, Module.Basis ι ℂ V → (ι → ℝ) → Prop) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Mod ε E → ∀ (ι : Type) (b : Module.Basis ι ℂ V) (μ : ι → ℝ),
    EigBasis ε E b μ → P n ε V E ι b μ
def A0 : Prop := ForMod fun _ ε _ _ _ E =>
  (∀ x y, inner ℂ (casimirK ε E x) y = inner ℂ x (casimirK ε E y)) ∧
  (∀ μ v, Eig ε E μ v → v ≠ 0 → 0 ≤ μ) ∧
  (∀ a b, ε a = ε b → Z ε E a b = 0) ∧
  ∀ κ, Cas E κ → ∀ w,
    ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 ∧
    ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 = (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 ∧
    ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = (κ : ℂ) • w - casimirK ε E w
def A1 : Prop := ForMod fun _ ε _ _ _ E =>
  (∀ j k, j ≤ k → U E j ≤ U E k) ∧ 1 ∈ U E 0 ∧ (∀ a b, E a b ∈ U E 1) ∧
  (∀ j k, ∀ x ∈ U E j, ∀ y ∈ U E k, x * y ∈ U E (j + k)) ∧
  (∀ j k, ∀ x ∈ U E j, ∀ y ∈ U E k, x * y - y * x ∈ U E (j + k - 1)) ∧
  casimirK ε E ∈ U E 2 ∧ ∀ a b, Z ε E a b ∈ U E 2
def FiltrationAdjointStable : Prop := ForMod fun _ _ _ _ _ E =>
  ∀ k, ∀ u ∈ U E k, ∃ u' ∈ U E k, ∀ x y, inner ℂ x (u y) = inner ℂ (u' x) y
def A2 : Prop := ForMod fun _ _ _ _ _ E =>
  ∀ (k : ℕ) c d, E c d * (Mm E ^ k).trace = (Mm E ^ k).trace * E c d
def A3 : Prop := ForMod fun _ _ V _ _ E =>
  ∀ T : Module.End ℂ V, (∀ a b, E a b * T = T * E a b) → ∃ c : ℂ, ∀ v, T v = c • v
def CasimirIsRealScalar : Prop := ForMod fun _ _ _ _ _ E => ∃ κ : ℝ, Cas E κ
def A4 : Prop := ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (N : Matrix (Fin n) (Fin n) R),
  (∀ k, (N ^ (k + 1)).trace = 0) → N ^ n = 0
def CommutatorAdjointModLower : Prop := ForMod fun _ ε _ _ _ E =>
  ∀ a b, (Mm E * Md ε E - Md ε E * Mm E) a b + Z ε E a b ∈ U E 1
def A5 : Prop := ForMod fun n ε V _ _ E =>
  ∀ m : ℕ, 1 ≤ m → n ≤ m → ∀ a b, ∃ u ∈ U E (2 * m - 1), ∃ w : Fin n → Fin n → Module.End ℂ V,
    (∀ c d, w c d ∈ U E (2 * m - 2)) ∧ ((Md ε E * Mm E) ^ m) a b = u + ∑ c, ∑ d, w c d * Z ε E c d
def A6 : Prop := ForMod fun _ ε _ _ _ E =>
  ∀ k, ∀ u ∈ U E k, ∃ C : ℝ, 0 ≤ C ∧ ∀ μ v, 0 ≤ μ → Eig ε E μ v → ‖u v‖ ≤ C * Real.sqrt (1 + μ) ^ k * ‖v‖
def A7 : Prop := ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (P : Module.End ℂ W),
  (∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) → ∀ x, ‖x‖ = 1 → 0 ≤ (inner ℂ x (P x)).re →
    ∀ j : ℕ, (inner ℂ x (P x)).re ^ (2 ^ j) ≤ (inner ℂ x ((P ^ (2 ^ j)) x)).re
def ColumnOperatorMoments : Prop := ForMod fun _ ε _ _ _ E =>
  ∀ v, ‖v‖ = 1 → ∀ e (j : ℕ),
    (∑ a, ‖E a e v‖ ^ 2) ^ (2 ^ j) ≤ (inner ℂ v (((Md ε E * Mm E) ^ (2 ^ j)) e e v)).re
def A8 : Prop := ForMod fun _ ε _ _ _ E =>
  ∃ c₀ x₁ : ℝ, 0 < c₀ ∧ ∀ μ v, x₁ ≤ μ → Eig ε E μ v →
    c₀ * (1 + μ) ^ 2 * ‖v‖ ^ 2 ≤ ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v‖ ^ 2
def A9 : Prop := ForMod fun _ ε _ _ _ E =>
  ∃ C : ℝ, 0 ≤ C ∧ ∀ μ v, 0 ≤ μ → Eig ε E μ v →
    ‖∑ p ∈ nc ε, inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)‖ ≤ C * (1 + μ) * ‖v‖ ^ 2 ∧
    ∑ p ∈ nc ε, ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2 ≤ C * (1 + μ) ^ 3 * ‖v‖ ^ 2
def A10 : Prop := ∀ s : ℕ, 1 ≤ s → ∃ c : ℝ, 0 ≤ c ∧ ∀ y : ℝ, -1 < y →
  1 - s * y + (s : ℝ) ^ 2 / 4 * y ^ 2 - c * y ^ 4 ≤ ((1 + y) ^ s)⁻¹
def EigenbasisExists : Prop := ForMod fun _ ε V _ _ E =>
  ∃ (ι : Type) (b : Module.Basis ι ℂ V) (μ : ι → ℝ), EigBasis ε E b μ
def FunctionalCalculusLaws : Prop := ForBas fun _ ε _ _ _ E _ b μ =>
  (∀ φ ν v, Eig ε E ν v → fc b μ φ v = ((φ ν : ℝ) : ℂ) • v) ∧
  (∀ φ x y, inner ℂ (fc b μ φ x) y = inner ℂ x (fc b μ φ y)) ∧
  (∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w, (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re) ∧
  (∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ) ∧
  (∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x * ψ x) = fc b μ φ * fc b μ ψ) ∧
  (∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1) ∧ fc b μ (fun x => x) = casimirK ε E
def EigenspacesOrthogonalAlt : Prop := ForBas fun _ ε _ _ _ E _ b μ =>
  ∀ φ ν ν' v w, ν ≠ ν' → Eig ε E ν v → Eig ε E ν' w → beta ε E (fc b μ φ) v w = 0
def A12 : Prop := ForBas fun _ ε _ _ _ E _ b μ =>
  ∀ κ, Cas E κ → ∀ c : ℝ, 0 ≤ c → ∃ (s : ℕ) (x₀ : ℝ), 1 ≤ s ∧ 0 ≤ x₀ ∧ ∀ ν v, x₀ ≤ ν → Eig ε E ν v →
    ((1 + ν) ^ s)⁻¹ * (ν - κ + c) * ‖v‖ ^ 2 ≤ (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) v v).re
open Classical in

def BasisSumAsFormValues : Prop := ForBas fun _ ε V _ _ E ι b μ =>
  ∀ (φ : ℝ → ℝ) (S : Finset ι), (∀ i, i ∉ S → φ (μ i) = 0) → ∃ T : Finset ι, S ⊆ T ∧ ∀ f : V →ₗ[ℂ] ℂ,
    ∑ i ∈ S, φ (μ i) * ∑ p ∈ nc ε, ‖f (E p.1 p.2 (b i))‖ ^ 2 =
      ∑ ν ∈ T.image μ, (beta ε E (fc b μ φ) (∑ j ∈ T.filter (fun j => μ j = ν), starRingEnd ℂ (f (b j)) • b j)
        (∑ j ∈ T.filter (fun j => μ j = ν), starRingEnd ℂ (f (b j)) • b j)).re
def A13 : Prop := ForBas fun _ ε V _ _ E ι b μ =>
  ∀ κ, Cas E κ → ∀ c : ℝ, 0 ≤ c → ∃ (s : ℕ) (x₀ C₁ : ℝ), 1 ≤ s ∧ 0 ≤ C₁ ∧ ∀ (R : ℝ) (f : V →ₗ[ℂ] ℂ) (S T : Finset ι),
    (∀ i, i ∈ S ↔ μ i < R) → (∀ i, i ∈ T ↔ μ i < x₀) →
    c * ∑ i ∈ S, phiR s R (μ i) * ‖f (b i)‖ ^ 2 - C₁ * ∑ i ∈ T, ‖f (b i)‖ ^ 2 ≤
      ∑ i ∈ S, phiR s R (μ i) * (∑ p ∈ nc ε, ‖f (E p.1 p.2 (b i))‖ ^ 2 - (μ i - κ) * ‖f (b i)‖ ^ 2)
def B1 : Prop := ForMod fun _ ε V _ _ E =>
  (∀ p ∈ nc ε, inP ε (Xp p.1 p.2)) ∧
  (∀ κ, Cas E κ → ∀ v, ∑ p ∈ nc ε, actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) v) = (κ : ℂ) • v - casimirK ε E v) ∧
  ∀ (f : V →ₗ[ℂ] ℂ) w, ∑ p ∈ nc ε, ‖f (actM E (Xp p.1 p.2) w)‖ ^ 2 = ∑ p ∈ nc ε, ‖f (E p.1 p.2 w)‖ ^ 2
def B2 : Prop := ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) (r : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ,
  ∃ (w' : ℝ → ℝ) (w'' : ℝ), (∀ t, HasDerivAt (fun t : ℝ => (1 + hs2 (g * NormedSpace.exp (t • X))) ^ r) (w' t) t) ∧
    HasDerivAt w' w'' 0 ∧ w'' ≤ c * (1 + hs2 g) ^ r
def B3 : Prop := ∀ (ψ ψ' : ℝ → ℝ) (d : ℝ), IsLocalMax ψ 0 → (∀ t, HasDerivAt ψ (ψ' t) t) → HasDerivAt ψ' d 0 → d ≤ 0
def UnitaryGroupFacts : Prop := ∀ (n : ℕ) (ε : Fin n → Bool),
  (∀ ρ : ℝ, IsCompact {g | g ∈ UJset ε ∧ hs2 g ≤ ρ}) ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε ∧
  (∀ g ∈ UJset ε, ∀ X, inP ε X → ∀ t : ℝ, g * NormedSpace.exp (t • X) ∈ UJset ε) ∧
  (∀ (X : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ),
    NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X)) ∧
  Continuous (hs2 : Matrix (Fin n) (Fin n) ℂ → ℝ) ∧ ∀ p ∈ nc ε, inP ε (Xp p.1 p.2)
def MaximumPrincipleVar : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (r : ℕ), ∃ c : ℝ, 0 ≤ c ∧
  ∀ (u : Matrix (Fin n) (Fin n) ℂ → ℝ) (A : ℝ), 0 ≤ A → ContinuousOn u (UJset ε) →
    (∃ C : ℝ, ∀ g ∈ UJset ε, u g ≤ C * (1 + hs2 g) ^ r) →
    (∀ g ∈ UJset ε, ∃ d : Fin n × Fin n → ℝ,
      (∀ p ∈ nc ε, ∃ u' : ℝ → ℝ, (∀ t, HasDerivAt (fun t : ℝ => u (g * NormedSpace.exp (t • Xp p.1 p.2))) (u' t) t) ∧
        HasDerivAt u' (d p) 0) ∧ c * u g - A * (1 + hs2 g) ^ r ≤ ∑ p ∈ nc ε, d p) →
    u 1 ≤ A * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ r
def SumSquaresSecondDerivative : Prop := ForBas fun n ε V _ _ E ι b μ =>
  ∀ κ, Cas E κ → ∀ F : V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ),
    (∀ X, inP ε X → ∀ v, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => F v (g * NormedSpace.exp (t • X))) (F (actM E X v) g) 0) →
    ∀ (S : Finset ι) (a : ι → ℝ), ∀ g ∈ UJset ε, ∃ d : Fin n × Fin n → ℝ,
      (∀ p ∈ nc ε, ∃ u' : ℝ → ℝ, (∀ t, HasDerivAt
        (fun t : ℝ => ∑ i ∈ S, a i * ‖F (b i) (g * NormedSpace.exp (t • Xp p.1 p.2))‖ ^ 2) (u' t) t) ∧
        HasDerivAt u' (d p) 0) ∧
      ∑ p ∈ nc ε, d p =
        2 * ∑ i ∈ S, a i * (∑ p ∈ nc ε, ‖F (E p.1 p.2 (b i)) g‖ ^ 2 - (μ i - κ) * ‖F (b i) g‖ ^ 2)
def B5 : Prop := ForBas fun _ ε V _ _ E ι b μ =>
  ∀ (f : V →ₗ[ℂ] ℂ) (s : ℕ) (K : ℝ), 0 ≤ K →
    (∀ (R : ℝ) (S : Finset ι), (∀ i, i ∈ S ↔ μ i < R) → ∑ i ∈ S, phiR s R (μ i) * ‖f (b i)‖ ^ 2 ≤ K ^ 2) → 1 ≤ s →
    ∀ v, ‖f v‖ ≤ K * ‖((1 + casimirK ε E) ^ s) v‖
end PositivityTheory.CW
end


