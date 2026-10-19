-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Duality
-- name    : OAI_Analysis_C0Absorption_Duality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:04:55.295811+00:00
-- url     : https://prove2.me/theorems/64715cda-ddc6-49c4-a03f-2f568719c14d
-- title:
--   Bounded tests, the source space and flattening operations
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. For a set $S$, molecules are finitely supported functions $m:S\to\mathbb R$ with $\sum_sm(s)=0$; a function $f$ on $S$ pairs with $m$ by $\langle f,m\rangle=\sum_sm(s)f(s)$, and $\delta_s-\delta_t$ is the basic molecule.
--
--   1. **Bounded tests.** A function $f$ on $S$ is a bounded test if $|\langle f,m\rangle|\le K\|m\|$ for some $K$ and all molecules $m$. If all members of a class $L_j$ are $K$-Lipschitz, the class has a uniform pairing bound.
--   2. **Source space.** With base point the origin of the unit ball $B$ of $c_0$, the source space is the test space built from the source classes ($T_{h+1}$ and $V_{h+1}$ alternately) on $B$:
--   $$
--   Z_{\mathrm{src}}=\overline{\bigl(\mathrm{Mol}(B),\|\cdot\|_{\mathrm{sel}}\bigr)} .
--   $$
--   The classes $T_h$ increase with $h$, and each $T_h$ has a uniform pairing bound.
--   3. **Flattening operations.** For a coordinate set $I$, a scale index $a$ and a point $v$ of the cube, $\mathrm{flattenOperation}(I,a,v)$ is the flattening operation at scale $2^{-a}$ centred at the grid point nearest to $v$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Duality.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Duality.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section ClassDuality
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

def BoundedTest (f : S → ℝ) : Prop :=
  ∃ K : ℝ≥0, ∀ m : PreSpace L o, |pairing S f m| ≤ K*‖m‖

theorem class_pairing_bound (j : ℕ) (K : ℝ≥0)
    (hK : ∀ f ∈ L j, LipschitzWith K f) :
    ∃ A : ℝ≥0, ∀ f ∈ L j, ∀ m : PreSpace L o, |pairing S f m| ≤ A*‖m‖ := by
  obtain ⟨C,hC⟩ := exists_nat_gt (K : ℝ)
  obtain ⟨n,hn⟩ := triple_surjective (j,C,0)
  refine ⟨(squareWeight n)⁻¹,?_⟩
  intro f hf m
  apply test_pairing_bound L o n f
  · simpa only [hn] using hf
  · apply (hK f hf).weaken
    change K ≤ ((triple n).2.1 : ℝ≥0)+1
    rw [hn]
    exact_mod_cast (show (K : ℝ) ≤ (C : ℝ)+1 by linarith)

end ClassDuality

variable {Γ : Type*} {B : CylinderBases Γ}

def c0Origin : C0Ball := ⟨0,by simp⟩
abbrev SourceSpace (B : CylinderBases Γ) := TestSpace (sourceClasses B) c0Origin

theorem TClass_mono {h k : ℕ} (hk : h ≤ k) : TClass B h ⊆ TClass B k := by
  rintro f ⟨γ,r,hr,rfl⟩
  exact ⟨γ,r,hr.trans hk,rfl⟩

theorem TClass_pairing_bound (B : CylinderBases Γ) (h : ℕ) :
    ∃ A : ℝ≥0, ∀ f ∈ TClass B h, ∀ m : PreSpace (sourceClasses B) c0Origin,
      |pairing C0Ball f m| ≤ A*‖m‖ := by
  have hh := class_pairing_bound (sourceClasses B) c0Origin (2*h) (4^(h+1)*B.L0) (by
    simpa only [sourceClasses_even] using (fun f hf => TClass_lipschitz B (h+1) (f := f) hf))
  obtain ⟨A,hA⟩ := hh
  exact ⟨A,fun f hf => hA f (by simpa only [sourceClasses_even] using TClass_mono (Nat.le_succ h) hf)⟩

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def flattenOperation (I : Finset ℕ) (a : ℕ) (v : Cube I) : CylinderOperation I :=
  ⟨a,nearestOperationGrid I a v,true⟩

@[simp] theorem flattenOperation_scale (I : Finset ℕ) (a : ℕ) (v : Cube I) :
    (flattenOperation I a v).scale = dyadic a := rfl

@[simp] theorem flattenOperation_act (I : Finset ℕ) (a : ℕ) (v : Cube I) (u : Cube I → ℝ) :
    (flattenOperation I a v).act u = localG (flattenOperation I a v).point (dyadic a) u := rfl

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation
end
end C0Absorption

end OAI


