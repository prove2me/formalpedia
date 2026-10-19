-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Pairings
-- name    : OAI_Analysis_C0Absorption_Pairings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T20:58:06.505861+00:00
-- url     : https://prove2.me/theorems/47a26c1e-1fa2-4822-bcab-5a145f1b7229
-- title:
--   Extending test pairings to the completed space
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. For a set $S$, molecules are finitely supported functions $m:S\to\mathbb R$ with $\sum_sm(s)=0$; a function $f$ on $S$ pairs with $m$ by $\langle f,m\rangle=\sum_sm(s)f(s)$, and $\delta_s-\delta_t$ is the basic molecule.
--
--   1. **Completed pairing.** For a function $f$ on $S$, the pairing $m\mapsto\langle f,m\rangle$ is extended to the completion $Z$ by uniform continuity. If $|\langle f,m\rangle|\le K\|m\|$, it is a continuous linear functional on $Z$ agreeing with $\langle f,\cdot\rangle$ on molecules.
--   2. **Singleton lists.** A single $C$-Lipschitz function $f$ in a class is an admissible list, and its list seminorm is $|\langle f,m\rangle|$.
--   3. **Test bound.** If $f\in L_j$ is $C_n$-Lipschitz, where $n$ has class index $j$ and constant $C_n$, then
--   $$
--   |\langle f,m\rangle|\le w_n^{-1}\|m\|,
--   $$
--   so every such test function defines a bounded functional on $Z$.
--   4. **Transfer.** Admissible lists are transferred between indices with the same class and constant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Pairings.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Pairings.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists

namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedPairings

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def completedPairing (f : S → ℝ) : TestSpace L o → ℝ :=
  Completion.extension (fun m : PreSpace L o => pairing S f m)

def initialPairing (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) : PreSpace L o →L[ℝ] ℝ :=
  (show PreSpace L o →ₗ[ℝ] ℝ from pairing S f).mkContinuous (E := PreSpace L o) K
    (fun m => h m)

theorem initialPairing_lipschitz (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) :
    LipschitzWith K (fun m : PreSpace L o => pairing S f m) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let T := initialPairing L o f K h
  change dist (T x) (T y) ≤ K * dist x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact h (x-y)

@[simp] theorem completedPairing_coe (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) (m : PreSpace L o) :
    completedPairing L o f (toTestSpace L o m) = pairing S f m :=
  Completion.extension_coe (initialPairing_lipschitz L o f K h).uniformContinuous m

def completedTest (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) : TestSpace L o →L[ℝ] ℝ :=
  (initialPairing L o f K h).extend (toTestSpace L o)

def AdmissibleList.singleton {L₀ : Set (S → ℝ)} {C : ℝ≥0}
    (f : S → ℝ) (hf : f ∈ L₀) (hC : LipschitzWith C f) : AdmissibleList L₀ C where
  length := 1
  test _ := f
  mem _ := hf
  signed_lipschitz ε hε := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [Fin.sum_univ_one, Real.dist_eq, ← mul_sub, abs_mul, hε, one_mul]
    exact hC.dist_le_mul s t

theorem singleton_norm {L₀ : Set (S → ℝ)} {C : ℝ≥0}
    (f : S → ℝ) (hf : f ∈ L₀) (hC : LipschitzWith C f)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : Molecule S) :
    ‖(AdmissibleList.singleton f hf hC).eval p m‖ = |pairing S f m| := by
  change ‖WithLp.toLp p (fun _ : Fin 1 => pairing S f m)‖ = |pairing S f m|
  apply le_antisymm
  · simpa only [Fin.sum_univ_one, WithLp.ofLp_toLp] using
      finite_lp_norm_le_sum p (WithLp.toLp p (fun _ : Fin 1 => pairing S f m))
  · exact PiLp.norm_apply_le (WithLp.toLp p (fun _ : Fin 1 => pairing S f m)) 0

theorem test_pairing_bound (n : ℕ) (f : S → ℝ) (hf : f ∈ L (triple n).1)
    (hC : LipschitzWith (listConstant n) f) (m : PreSpace L o) :
    |pairing S f m| ≤ (squareWeight n)⁻¹ * ‖m‖ := by
  have h₁ := list_le_sigma (L (triple n).1) (listConstant n) (listExponent n) o
    (AdmissibleList.singleton f hf hC) (show Molecule S from m)
  have hs := singleton_norm f hf hC (listExponent n) (show Molecule S from m)
  change ‖(AdmissibleList.singleton f hf hC).eval (listExponent n) m‖ ≤ _ at h₁
  rw [hs] at h₁
  exact h₁.trans (sigma_le_preNorm L o n m)

def transferredList (n n' : ℕ) (hL : (triple n').1 = (triple n).1)
    (hC : listConstant n' = listConstant n)
    (l : AdmissibleList (L (triple n).1) (listConstant n)) :
    AdmissibleList (L (triple n').1) (listConstant n') where
  length := l.length
  test := l.test
  mem i := by rw [hL]; exact l.mem i
  signed_lipschitz ε hε := by rw [hC]; exact l.signed_lipschitz ε hε

end CompletedPairings

section FurtherDetectors

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

end FurtherDetectors

end
end C0Absorption

end OAI


