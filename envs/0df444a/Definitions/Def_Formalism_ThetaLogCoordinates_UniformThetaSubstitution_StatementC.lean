-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:39:37.725354+00:00
-- url     : https://prove2.me/theorems/53c158c1-2ab6-4a22-9ac4-5c7978d4cf44
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/StatementC.lean

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
def eF {K σ : Type} [CommRing K] [Fintype σ] (x : σ → K) (l : ℕ) : K :=
  MvPolynomial.eval x (MvPolynomial.esymm σ K l)
def hF {K σ : Type} [CommRing K] [Fintype σ] [DecidableEq σ] (x : σ → K) (l : ℕ) : K :=
  MvPolynomial.eval x (MvPolynomial.hsymm σ K l)
def beFam {K : Type} [Field K] (Q : K) (g : ℕ) : Fin g → K :=
  fun i => Q ^ ((g : ℤ) - 1 - 2 * (i.val : ℤ))
def FFam {K : Type} [Field K] (Q : K) (t : ℕ) (m : ℕ → K) (j : ℕ) : Fin j × Fin (t + 1) → K :=
  fun x => m (x.1.val + 1) * beFam Q (t + 1) x.2
def GaussEsymm : Prop :=
  ∀ (K : Type) [Field K] (Q g l : ℕ), (Q : K) ≠ 0 →
    ((Formalism.G0.gaussBinom (Q ^ 2) g l : ℕ) : K) = (Q : K) ^ (l * (g - l)) * eF (beFam (Q : K) g) l
def TwiceExponent : Prop :=
  ∀ N g j l : ℤ,
    j * N + 2 * (j - l) * (g - l) - (j - l) * (N + g) + l * (g - l) + (j - l) * (N - j + l) =
      j * (N + g - j)
def NormalisedCount : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (Q N g : ℕ) (Dn Up : ℕ → V), (Q : K) ≠ 0 →
    (∀ j, Dn j = ∑ l ∈ range (j + 1),
      (((Q ^ 2) ^ ((j - l) * (g - l)) * Formalism.G0.gaussBinom (Q ^ 2) g l : ℕ) : K) • Up (j - l)) →
    ∀ j : ℕ,
      ((Q : K) ^ (-((j : ℤ) * ((N : ℤ) + g - j)))) • ((Q : K) ^ (j * N)) • Dn j =
        ∑ l ∈ range (j + 1), eF (beFam (Q : K) g) l •
          ((Q : K) ^ (-(((j - l : ℕ) : ℤ) * ((N : ℤ) - (j - l : ℕ))))) •
            ((Q : K) ^ ((j - l) * (N + g))) • Up (j - l)
def HEConvolution : Prop :=
  ∀ (K σ : Type) [CommRing K] [Fintype σ] [DecidableEq σ] (x : σ → K) (n : ℕ), 1 ≤ n →
    ∑ a ∈ range (n + 1), (-1 : K) ^ a * hF x a * eF x (n - a) = 0
def Kc {K : Type} [Field K] {M : ℕ → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) : ∀ j, M 0 →ₗ[K] M j
  | 0 => LinearMap.id
  | j + 1 => (Kk j).comp (Kc Kk j)
def Intertwine {K : Type} [Field K] {M : ℕ → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) (e : ∀ j, ℕ → Module.End K (M j)) (Q : K) (t : ℕ) (m : ℕ → K)
    (J : ℕ) : Prop :=
  ∀ j, j < J → ∀ i,
    (e (j + 1) i).comp (Kk j) =
      (Kk j).comp (∑ l ∈ range (i + 1), eF (fun x => m (j + 1) * beFam Q (t + 1) x) l • e j (i - l))
def AbsorbUnits : Prop :=
  ∀ (K : Type) [Field K] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) (e : ∀ j, ℕ → Module.End K (M j)) (Q : K) (t : ℕ)
    (m u : ℕ → K) (J : ℕ), (∀ j, u j ≠ 0) →
    (∀ j, j < J → ∀ i,
      (e (j + 1) i).comp (Kk j) =
        (u (j + 1) ^ i) • (Kk j).comp
          (∑ l ∈ range (i + 1), eF (fun x => m (j + 1) * beFam Q (t + 1) x) l • e j (i - l))) →
    Intertwine Kk (fun j i => ((∏ a ∈ Icc 1 j, u a) ^ i)⁻¹ • e j i) Q t
      (fun j => (∏ a ∈ Icc 1 (j - 1), u a)⁻¹ * m j) J
def Iterate : Prop :=
  ∀ (K : Type) [Field K] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) (e : ∀ j, ℕ → Module.End K (M j)) (Q : K) (t : ℕ) (m : ℕ → K)
    (J : ℕ), Intertwine Kk e Q t m J →
    ∀ j, j ≤ J → ∀ i,
      (e j i).comp (Kc Kk j) =
        (Kc Kk j).comp (∑ l ∈ range (i + 1), eF (FFam Q t m j) l • e 0 (i - l))
def Inversion : Prop :=
  ∀ (K : Type) [Field K] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) (e : ∀ j, ℕ → Module.End K (M j)) (Q : K) (t : ℕ) (m : ℕ → K)
    (J : ℕ), Intertwine Kk e Q t m J →
    ∀ j, j ≤ J → ∀ r,
      (∑ l ∈ range (r + 1), ((-1 : K) ^ l * hF (FFam Q t m j) l) • e j (r - l)).comp (Kc Kk j) =
        (Kc Kk j).comp (e 0 r)
def NN (k t j : ℕ) : ℕ := k + j * (t + 1)
def NprimeZ {ι : Type} (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (wj : ι → ℤ) (i : ℕ) : ℤ :=
  ∑ s ∈ Ev, ∑ a ∈ Icc 1 i, lam s a + (i : ℤ) * ∑ s ∈ Od, wj s
def ArZ {ι : Type} (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (k r : ℕ) : ℤ :=
  ∑ s ∈ Ev, ∑ a ∈ Icc 1 r, lam s a - ∑ s ∈ Od, ∑ a ∈ Icc (k + 1 - r) k, lam s a
def PrZ {ι : Type} (Od : Finset ι) (lam : ι → ℕ → ℤ) (wj : ι → ℤ) (k r j t ν : ℕ) : ℤ :=
  ∑ s ∈ Od, ((r : ℤ) * wj s + ∑ a ∈ Icc (k + 1 - r) k, lam s a) + (ν : ℤ) * r * j * (t + 1)
def cCoef {K ι : Type} [Field K] (pp : K) (ν : ℕ) (Ev Od : Finset ι) (lam : ι → ℕ → ℤ)
    (w : ℕ → ι → ℤ) (m : ℕ → K) (k t r j l : ℕ) : K :=
  pp ^ (NprimeZ Ev Od lam (w j) r - NprimeZ Ev Od lam (w j) (r - l)) *
    (pp ^ ν) ^ ((l : ℤ) * ((NN k t j : ℤ) - 2 * r + l)) * hF (FFam (pp ^ ν) t m j) l
def Ttil {K ι V : Type} [Field K] [AddCommGroup V] [Module K V] (pp : K) (Ev Od : Finset ι)
    (lam : ι → ℕ → ℤ) (wj : ι → ℤ) (Tm : ℕ → Module.End K V) (i : ℕ) : Module.End K V :=
  pp ^ (NprimeZ Ev Od lam wj i) • Tm i
def Zop {K ι V : Type} [Field K] [AddCommGroup V] [Module K V] (pp : K) (ν : ℕ) (Ev Od : Finset ι)
    (lam : ι → ℕ → ℤ) (w : ℕ → ι → ℤ) (m : ℕ → K) (k t r j : ℕ) (Tm : ℕ → Module.End K V) :
    Module.End K V :=
  ∑ l ∈ range (r + 1),
    ((-1 : K) ^ l * cCoef pp ν Ev Od lam w m k t r j l) • Ttil pp Ev Od lam (w j) Tm (r - l)
def ThmCi : Prop :=
  ∀ (K ι : Type) [Field K] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) (Tm : ∀ j, ℕ → Module.End K (M j)) (pp : K) (ν k t r j : ℕ)
    (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (w : ℕ → ι → ℤ) (m : ℕ → K),
    pp ≠ 0 → r ≤ k →
    Intertwine Kk (fun a i => ((pp ^ ν) ^ (-((i : ℤ) * ((NN k t a : ℤ) - i)))) • Tm a i)
      (pp ^ ν) t m j →
    (Zop pp ν Ev Od lam w m k t r j (Tm j)).comp (Kc Kk j) =
      pp ^ (PrZ Od lam (w j) k r j t ν) • (Kc Kk j).comp (pp ^ (ArZ Ev Od lam k r) • Tm 0 r)
def WeightsOK {ι : Type} (S : Finset ι) (lam : ι → ℕ → ℤ) (w : ℕ → ι → ℤ) (k j : ℕ) : Prop :=
  (∀ s ∈ S, ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → lam s b ≤ lam s a) ∧
  (∀ s ∈ S, -lam s k ≤ w 1 s) ∧
  (∀ s ∈ S, ∀ a b, 1 ≤ a → a ≤ b → b ≤ j → w a s ≤ w b s)
def ThmCiiIntegral : Prop :=
  ∀ (K ι : Type) [DecidableEq ι] [NormedField K] [IsUltrametricDist K] (p ν k t r j l : ℕ)
    (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (w : ℕ → ι → ℤ) (m : ℕ → K),
    2 ≤ p → ‖(p : K)‖ = (p : ℝ)⁻¹ → 1 ≤ j → 2 * r ≤ k → l ≤ r →
    WeightsOK (Ev ∪ Od) lam w k j →
    (∀ a, 1 ≤ a → a ≤ j → ‖m a‖ = (p : ℝ) ^ (-(∑ s ∈ Ev, w a s - ∑ s ∈ Od, w a s))) →
    ‖cCoef (p : K) ν Ev Od lam w m k t r j l‖ ≤
        (p : ℝ) ^ (-(∑ s ∈ Ev, (∑ a ∈ Icc (r - l + 1) r, lam s a + (l : ℤ) * w 1 s))) ∧
      0 ≤ ∑ s ∈ Ev, (∑ a ∈ Icc (r - l + 1) r, lam s a + (l : ℤ) * w 1 s) ∧
      ‖cCoef (p : K) ν Ev Od lam w m k t r j l‖ ≤ 1
def ThmCiiTop : Prop :=
  ∀ (K ι : Type) [DecidableEq ι] [NormedField K] [IsUltrametricDist K] (p ν k t r j : ℕ)
    (Ev Od TTev : Finset ι) (lam : ι → ℕ → ℤ) (w : ℕ → ι → ℤ) (m : ℕ → K),
    2 ≤ p → ‖(p : K)‖ = (p : ℝ)⁻¹ → 1 ≤ j → 1 ≤ r → 2 * r ≤ k → TTev ⊆ Ev →
    WeightsOK (Ev ∪ Od) lam w k j →
    (∀ a, 1 ≤ a → a ≤ j → ‖m a‖ = (p : ℝ) ^ (-(∑ s ∈ Ev, w a s - ∑ s ∈ Od, w a s))) →
    ‖cCoef (p : K) ν Ev Od lam w m k t r j r‖ ≤ (p : ℝ) ^ (-(∑ s ∈ TTev, (lam s 1 - lam s 2)))
def ThmCiii : Prop :=
  ∀ (K ι V : Type) [DecidableEq ι] [NormedField K] [IsUltrametricDist K] [SeminormedAddCommGroup V]
    [IsUltrametricDist V] [NormedSpace K V] (p ν k t r j : ℕ)
    (Ev Od TTev : Finset ι) (lam : ι → ℕ → ℤ) (w : ℕ → ι → ℤ) (m : ℕ → K)
    (Tm : ℕ → Module.End K V) (x : V) (g : ℝ),
    2 ≤ p → ‖(p : K)‖ = (p : ℝ)⁻¹ → 1 ≤ j → 1 ≤ r → 2 * r ≤ k → TTev ⊆ Ev →
    WeightsOK (Ev ∪ Od) lam w k j →
    (∀ a, 1 ≤ a → a ≤ j → ‖m a‖ = (p : ℝ) ^ (-(∑ s ∈ Ev, w a s - ∑ s ∈ Od, w a s))) →
    Tm 0 = 1 →
    (∀ i, 1 ≤ i → i ≤ r → ‖Ttil (p : K) Ev Od lam (w j) Tm i x‖ ≤ (p : ℝ) ^ (-g)) →
    ‖x‖ ≤ (p : ℝ) ^ (-(g - ((∑ s ∈ TTev, (lam s 1 - lam s 2) : ℤ) : ℝ))) →
    ‖Zop (p : K) ν Ev Od lam w m k t r j Tm x‖ ≤ (p : ℝ) ^ (-g)
def PriceOne : Prop :=
  ∀ (ι : Type) [DecidableEq ι] (Od TTod : Finset ι) (lam : ι → ℕ → ℤ) (wj : ι → ℤ) (k j t ν : ℕ)
    (b : ι → ℝ) (bx eta w2 c : ℝ),
    TTod ⊆ Od → Od.card = ν → 1 ≤ k → 0 ≤ w2 + eta + c →
    (∀ s ∈ TTod, (lam s k : ℝ) = -b s ∧ (wj s : ℝ) ≤ b s + bx + eta) →
    (∀ s ∈ Od \ TTod, (lam s k : ℝ) ≤ c ∧ (wj s : ℝ) ≤ w2 + eta) →
    ((PrZ Od lam wj k 1 j t ν : ℤ) : ℝ) ≤
      TTod.card * (bx + eta) + ν * (w2 + eta + c) + (2 * ν : ℝ) * j * (t + 1) / 2
def PriceGen : Prop :=
  ∀ (ι : Type) [DecidableEq ι] (Od TTod : Finset ι) (lam : ι → ℕ → ℤ) (wj : ι → ℤ) (k r j t ν : ℕ)
    (b : ι → ℝ) (b' bx eta w2 c : ℝ),
    TTod ⊆ Od → Od.card = ν → 1 ≤ r → 2 * r ≤ k → 0 ≤ w2 + eta + c → 0 ≤ c → 0 ≤ b' →
    (∀ s ∈ TTod, (lam s k : ℝ) = -b s ∧ (wj s : ℝ) ≤ b s + bx + eta ∧ b s ≤ 3 * b' / 2 ∧
      ∀ a, 2 ≤ a → a < k → (lam s a : ℝ) ≤ c) →
    bx + eta ≤ b' / 2 →
    (∀ s ∈ Od \ TTod, (wj s : ℝ) ≤ w2 + eta ∧ ∀ a, 1 ≤ a → a ≤ k → (lam s a : ℝ) ≤ c) →
    ((PrZ Od lam wj k r j t ν : ℤ) : ℝ) ≤
      r * (TTod.card * (2 * b' + c) + ν * (w2 + eta + c) + (2 * ν : ℝ) * j * (t + 1) / 2)
end Formalism.InvariantFactorPaths.G7


