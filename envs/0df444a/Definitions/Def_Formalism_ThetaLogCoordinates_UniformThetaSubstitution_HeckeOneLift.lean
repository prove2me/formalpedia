-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_HeckeOneLift
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_HeckeOneLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:42:55.525034+00:00
-- url     : https://prove2.me/theorems/c8de01e0-453a-48d5-8fcb-7cb3c97d0525
-- title:
--   Hecke One Lift
-- statement:
--   Definitions and structural lemmas for Hecke One Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/HeckeOneLift.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
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
def HeckeOneLift : Prop :=
  ∀ (K X X' Fn V V' : Type) [Field K] [AddCommGroup Fn] [Module K Fn] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (Q N g : ℕ) (up dn : ℕ → X → Finset X)
    (dn' : ℕ → X' → Finset X') (kk : X → X' → Fn) (sv : X → X' → K) (abelian₂ : Fn →ₗ[K] (V →ₗ[K] V'))
    (ε : X → K) (ε' : X' → K) (a b : K) (cs : (X → V') →ₗ[K] V') (Forms : Set (X → V)),
    (Q : K) ≠ 0 → b ≠ 0 →
    (∀ L L' j, ∑ L1 ∈ dn' j L', kk L L1 = ∑ l ∈ range (j + 1),
      (((Q ^ 2) ^ ((j - l) * (g - l)) * Formalism.G0.gaussBinom (Q ^ 2) g l : ℕ) : K) •
        ∑ L1 ∈ up (j - l) L, kk L1 L') →
    (∀ L L' j, ∀ L1 ∈ dn' j L', sv L L1 = (Q : K) ^ (j * N) * sv L L' ∧ ε' L1 = a ^ j * ε' L') →
    (∀ L L' i, ∀ L1 ∈ up i L, sv L1 L' = (Q : K) ^ (i * (N + g)) * sv L L' ∧ ε L1 = b ^ i * ε L) →
    (∀ i L', ∀ F ∈ Forms,
      cs (fun L => ∑ L1 ∈ up i L, (ε L1 * ε' L' * sv L1 L') • abelian₂ (kk L1 L') (F L)) =
        cs (fun L1 => (ε L1 * ε' L' * sv L1 L') • abelian₂ (kk L1 L') (∑ L ∈ dn i L1, F L))) →
    ∀ F ∈ Forms, ∀ (i : ℕ) (L' : X'),
      ((Q : K) ^ (-((i : ℤ) * ((N : ℤ) + g - i)))) •
          ∑ L1 ∈ dn' i L', cs (fun L => (ε L * ε' L1 * sv L L1) • abelian₂ (kk L L1) (F L)) =
        (a / b) ^ i • ∑ l ∈ range (i + 1), eF (fun x => b * beFam (Q : K) g x) l •
          cs (fun L => (ε L * ε' L' * sv L L') • abelian₂ (kk L L')
            (((Q : K) ^ (-(((i - l : ℕ) : ℤ) * ((N : ℤ) - (i - l : ℕ))))) • ∑ L0 ∈ dn (i - l) L, F L0))
def ThmCiUnits : Prop :=
  ∀ (K ι : Type) [Field K] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) (Tm : ∀ j, ℕ → Module.End K (M j)) (pp : K) (ν k t r j : ℕ)
    (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (w : ℕ → ι → ℤ) (m u : ℕ → K),
    pp ≠ 0 → r ≤ k → (∀ a, u a ≠ 0) →
    (∀ a, a < j → ∀ i : ℕ,
      (((pp ^ ν) ^ (-((i : ℤ) * ((NN k t (a + 1) : ℤ) - i)))) • Tm (a + 1) i).comp (Kk a) =
        (u (a + 1) ^ i) • (Kk a).comp
          (∑ l ∈ range (i + 1), eF (fun x => m (a + 1) * beFam (pp ^ ν) (t + 1) x) l •
            (((pp ^ ν) ^ (-(((i - l : ℕ) : ℤ) * ((NN k t a : ℤ) - (i - l : ℕ))))) • Tm a (i - l)))) →
    (Zop pp ν Ev Od lam w (fun l => (∏ a ∈ Icc 1 (l - 1), u a)⁻¹ * m l) k t r j
        (fun i => ((∏ a ∈ Icc 1 j, u a) ^ i)⁻¹ • Tm j i)).comp (Kc Kk j) =
      pp ^ (PrZ Od lam (w j) k r j t ν) • (Kc Kk j).comp (pp ^ (ArZ Ev Od lam k r) • Tm 0 r)
def ThmCiiiMulti : Prop :=
  ∀ (K Pl H V : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq Pl] [CommRing H]
    [Algebra K H] [SeminormedAddCommGroup V] [IsUltrametricDist V] [NormedSpace K V] [Module H V]
    [IsScalarTower K H V] (p : ℝ) (B : Finset Pl) (r : Pl → ℕ) (cc : Pl → ℕ → K)
    (Tt : Pl → ℕ → H) (g A : Pl → ℝ) (rest : ℝ) (x : V),
    1 < p → (∀ v ∈ B, ∀ l, l ≤ r v → ‖cc v l‖ ≤ 1) → (∀ v ∈ B, ‖cc v (r v)‖ ≤ p ^ (-(A v))) →
    (∀ L : Pl → ℕ, (∀ v ∈ B, L v ≤ r v) →
      ‖(∏ v ∈ B, Tt v (r v - L v)) • x‖ ≤
        p ^ (-(∑ v ∈ B, (if L v = r v then g v - A v else g v) + rest))) →
    ‖(∏ v ∈ B, ∑ l ∈ range (r v + 1), ((-1 : K) ^ l * cc v l) • Tt v (r v - l)) • x‖ ≤
      p ^ (-(∑ v ∈ B, g v + rest))
def ScaleHomog : Prop :=
  ∀ (K V V' : Type) [NormedField K] [SeminormedAddCommGroup V] [NormedSpace K V]
    [SeminormedAddCommGroup V'] [NormedSpace K V'] (T : V →ₗ[K] V') (ρ : ℝ),
    (∃ c : K, 1 < ‖c‖) → (∀ G : V, ∃ c : K, ‖c‖ = ‖G‖) → (∀ G : V, ‖G‖ ≤ 1 → ‖T G‖ ≤ ρ) →
    ∀ G : V, ‖T G‖ ≤ ρ * ‖G‖
end Formalism.InvariantFactorPaths.G7


