-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Completion
-- name    : OAI_Analysis_C0Absorption_Completion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T20:54:15.648846+00:00
-- url     : https://prove2.me/theorems/0dfde85c-ce8c-48e3-bbf2-bf17352b1fa8
-- title:
--   The test space as the completion of normed molecules
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. For a set $S$, molecules are finitely supported functions $m:S\to\mathbb R$ with $\sum_sm(s)=0$; a function $f$ on $S$ pairs with $m$ by $\langle f,m\rangle=\sum_sm(s)f(s)$, and $\delta_s-\delta_t$ is the basic molecule.
--
--   1. **Completed seminorms.** A seminorm $q$ on a normed space with $q\le C\|\cdot\|$ is $C$-Lipschitz and extends uniquely to a seminorm on the completion.
--   2. **Pre-space and test space.** The pre-space is $\mathrm{Mol}(S)$ with the selected norm (a seminormed space). The test space $Z=Z(L,o)$ is its completion, a real Banach space.
--   3. **Coordinates.** The map $m\mapsto(q_n(m))_n\in\ell^2$ is $1$-Lipschitz and extends to $Z$. Each selected coordinate $q_n$ extends to a seminorm on $Z$.
--   4. **Points.** With a base point $o$, $\zeta(s)$ is the image of the molecule $\delta_s-\delta_o$ in $Z$. The map $\zeta$ is $1$-Lipschitz with $\zeta(o)=0$, and its range spans a dense subspace. If $S$ is separable, so is $Z$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Completion.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Completion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm

namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedSeminorms

open UniformSpace Completion

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

theorem seminorm_lipschitz (q : Seminorm ℝ X) (C : ℝ≥0)
    (h : ∀ x, q x ≤ C * ‖x‖) : LipschitzWith C q := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  exact (seminorm_abs_sub_le q x y).trans (h (x - y))

def completedSeminorm (q : Seminorm ℝ X) (C : ℝ≥0) (h : ∀ x, q x ≤ C * ‖x‖) :
    Seminorm ℝ (Completion X) :=
  Seminorm.of (Completion.extension q)
    (by
      intro x y
      induction x, y using Completion.induction_on₂ with
      | hp =>
        exact isClosed_le
          (Completion.continuous_extension.comp (continuous_fst.add continuous_snd))
          ((Completion.continuous_extension.comp continuous_fst).add
            (Completion.continuous_extension.comp continuous_snd))
      | ih x y =>
        simpa only [← Completion.coe_add,
          Completion.extension_coe (seminorm_lipschitz q C h).uniformContinuous] using
          map_add_le_add q x y)
    (by
      intro a x
      induction x using Completion.induction_on with
      | hp =>
        exact isClosed_eq
          (Completion.continuous_extension.comp (continuous_const_smul a))
          (continuous_const.mul Completion.continuous_extension)
      | ih x =>
        simpa only [← Completion.coe_smul,
          Completion.extension_coe (seminorm_lipschitz q C h).uniformContinuous] using
          map_smul_eq_mul q a x)

@[simp] theorem completedSeminorm_coe (q : Seminorm ℝ X) (C : ℝ≥0)
    (h : ∀ x, q x ≤ C * ‖x‖) (x : X) : completedSeminorm q C h (x : Completion X) = q x :=
  Completion.extension_coe (seminorm_lipschitz q C h).uniformContinuous x

end CompletedSeminorms

section SelectedCompletion

open UniformSpace Completion

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def PreSpace (_L : ℕ → Set (S → ℝ)) (_o : S) : Type _ := Molecule S

instance : SeminormedAddCommGroup (PreSpace L o) :=
  (selectedNorm L o).toAddGroupSeminorm.toSeminormedAddCommGroup
instance : NormedSpace ℝ (PreSpace L o) where
  __ : Module ℝ (PreSpace L o) := inferInstanceAs (Module ℝ (Molecule S))
  norm_smul_le a x := by
    change selectedNorm L o (a • x) ≤ ‖a‖ * selectedNorm L o x
    exact (map_smul_eq_mul (selectedNorm L o) a x).le

instance : IsBoundedSMul ℝ (PreSpace L o) :=
  NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := PreSpace L o)

def TestSpace := Completion (PreSpace L o)

instance : NormedAddCommGroup (TestSpace L o) :=
  inferInstanceAs (NormedAddCommGroup (Completion (PreSpace L o)))
instance : NormedSpace ℝ (TestSpace L o) :=
  inferInstanceAs (NormedSpace ℝ (Completion (PreSpace L o)))
instance : CompleteSpace (TestSpace L o) :=
  inferInstanceAs (CompleteSpace (Completion (PreSpace L o)))

def toTestSpace : PreSpace L o →L[ℝ] TestSpace L o :=
  (Completion.toComplL : PreSpace L o →L[ℝ] Completion (PreSpace L o))

@[simp] theorem norm_toTestSpace (m : PreSpace L o) :
    ‖toTestSpace L o m‖ = selectedNorm L o m := Completion.norm_coe m

def initialCoordinates (m : PreSpace L o) : lp (fun _ : ℕ => ℝ) 2 :=
  squareVector (selectedCoordinate L) (selectedCoordinate_summable L o) m

theorem initialCoordinates_lipschitz : LipschitzWith 1 (initialCoordinates L o) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  exact squareVector_sub_norm_le (selectedCoordinate L) (selectedCoordinate_summable L o) x y

def normCoordinates : TestSpace L o → lp (fun _ : ℕ => ℝ) 2 :=
  Completion.extension (initialCoordinates L o)

@[simp] theorem normCoordinates_coe (m : PreSpace L o) :
    normCoordinates L o (toTestSpace L o m) = initialCoordinates L o m :=
  Completion.extension_coe (initialCoordinates_lipschitz L o).uniformContinuous m

theorem selectedCoordinate_le_norm (n : ℕ) (m : PreSpace L o) :
    selectedCoordinate L n m ≤ (1 : ℝ≥0) * ‖m‖ := by
  change selectedCoordinate L n m ≤ (1 : ℝ) * selectedNorm L o m
  rw [one_mul]
  exact coordinate_le_squareSeminorm (selectedCoordinate L) (selectedCoordinate_summable L o) n m

def completedCoordinate (n : ℕ) : Seminorm ℝ (TestSpace L o) :=
  completedSeminorm (X := PreSpace L o) (selectedCoordinate L n) 1
    (selectedCoordinate_le_norm L o n)

@[simp] theorem completedCoordinate_coe (n : ℕ) (m : PreSpace L o) :
    completedCoordinate L o n (toTestSpace L o m) = selectedCoordinate L n m :=
  completedSeminorm_coe _ _ _ m

def prePoint (s : S) : PreSpace L o := molecule s o

theorem prePoint_lipschitz : LipschitzWith 1 (prePoint L o) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  change selectedNorm L o (molecule s o - molecule t o) ≤ (1 : ℝ) * dist s t
  rw [molecule_sub_molecule, one_mul]
  exact selectedNorm_molecule_le L o s t

theorem prePoint_span : Submodule.span ℝ (Set.range (prePoint L o)) = ⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro m
  have heq : m = ∑ s ∈ m.val.support, m.val s • prePoint L o s := molecule_decomposition m o
  rw [heq]
  apply Submodule.sum_mem
  intro s hs
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

instance [TopologicalSpace.SeparableSpace S] : TopologicalSpace.SeparableSpace (PreSpace L o) := by
  have hsep := (TopologicalSpace.isSeparable_range (prePoint_lipschitz L o).continuous).span (R := ℝ)
  rw [prePoint_span, Submodule.top_coe] at hsep
  exact TopologicalSpace.isSeparable_univ_iff.mp hsep

instance [TopologicalSpace.SeparableSpace S] : TopologicalSpace.SeparableSpace (TestSpace L o) :=
  inferInstanceAs (TopologicalSpace.SeparableSpace (Completion (PreSpace L o)))

def zeta (s : S) : TestSpace L o := toTestSpace L o (prePoint L o s)

@[simp] theorem zeta_base : zeta L o o = 0 := by
  have h : prePoint L o o = (0 : PreSpace L o) := molecule_self o
  rw [zeta, h, map_zero]

end SelectedCompletion

end
end C0Absorption

end OAI


