-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateSpace
-- name    : OAI_Analysis_DiamondDistortion_CoordinateSpace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:05:33.183072+00:00
-- url     : https://prove2.me/theorems/c6917b58-d74a-472f-b881-3d5c5aafc19a
-- title:
--   Completion of finitely supported arrays under a norm with bounded coordinate evaluations
-- statement:
--   Let $\iota$ be an index set, $c_{00}(\iota)$ the space of finitely supported functions $v:\iota\to\mathbb{R}$, and $\delta_i$ the indicator of $\{i\}$. The file sets up a general completion procedure for norms on $c_{00}(\iota)$.
--
--   1. **Coordinate completion data.** A seminorm $N$ on $c_{00}(\iota)$ such that every coordinate evaluation is bounded: for each $i\in\iota$ there is $C_i\in\mathbb{R}$ with
--   $$
--   |v(i)|\le C_i\,N(v)\qquad\text{for all }v\in c_{00}(\iota).
--   $$
--   Consequently $N(v)=0$ forces $v=0$, so $N$ is a norm. No bound on the norms of coordinate projections is required, so the unit vectors need not form a Schauder basis.
--
--   2. **The space.** $X_N$ is the completion of the normed space $(c_{00}(\iota),N)$, with the canonical linear embedding $\jmath:c_{00}(\iota)\to X_N$, which satisfies $\|\jmath v\|=N(v)$.
--
--   3. **Coordinates and unit vectors.** The coordinate functional $e_i^*\in X_N^*$ is the continuous extension of the evaluation $v\mapsto v(i)$, which is bounded by the hypothesis, and the unit vector is $e_i=\jmath(\delta_i)$. Then $e_i^*(\jmath v)=v(i)$, and $e_i^*(e_j)$ equals $1$ if $j=i$ and $0$ otherwise.
--
--   4. **Finite coordinate projections.** For a finite set $H\subseteq\iota$, the bounded linear operator
--   $$
--   P_H x=\sum_{i\in H}e_i^*(x)\,e_i\qquad(x\in X_N),
--   $$
--   which satisfies $e_i^*(P_Hx)=e_i^*(x)$ for $i\in H$ and $e_i^*(P_Hx)=0$ for $i\notin H$.
--
--   This gives a uniform way to define Banach spaces of arrays by an explicit formula for the norm of finitely supported vectors: any seminorm that dominates each coordinate up to a constant yields a complete space in which coordinates, unit vectors and finite coordinate projections are available. In the surrounding development, the recursively normed model spaces on forests of countably branching trees are presented in this form.
--
--   **Formalization Note** The data is the structure `CoordinateCompletion.Data`, with fields `seminorm` and `coordinate_bound`; $X_N$ is `Space`, the completion of the type synonym `Finite` whose normed-space structure is built from $N$ using the separation lemma `separates`. $\jmath$ is `embedding`, $e_i^*$ is `coordinate i` (on finite vectors it uses a chosen constant $C_i$ as operator bound), $e_i$ is `unit i` and $P_H$ is `projection H`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/CoordinateSpace.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/CoordinateSpace.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiamondDistortion mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace CoordinateCompletion
variable {ι : Type*}

/-- A specified coordinate norm, with individually bounded coordinate evaluations.
    No bound on the norms of coordinate projections is imposed. -/
structure Data (ι : Type*) where
  seminorm : Seminorm ℝ (ι →₀ ℝ)
  coordinate_bound : ∀ i,∃ C : ℝ,∀ v,|v i| ≤ C*seminorm v

namespace Data
variable (A : Data ι)
lemma separates (v : ι →₀ ℝ) (hv : A.seminorm v=0) : v=0 := by
  ext i
  obtain ⟨C,hC⟩ := A.coordinate_bound i
  have hh := hC v
  rw [hv,mul_zero] at hh
  exact abs_nonpos_iff.mp hh

def Finite (_A : Data ι) := ι →₀ ℝ
instance : AddCommGroup A.Finite := inferInstanceAs (AddCommGroup (ι →₀ ℝ))
instance : Module ℝ A.Finite := inferInstanceAs (Module ℝ (ι →₀ ℝ))
instance : NormedAddCommGroup A.Finite := AddGroupNorm.toNormedAddCommGroup
  { A.seminorm.toAddGroupSeminorm with eq_zero_of_map_eq_zero' := A.separates }
instance : NormedSpace ℝ A.Finite where
  norm_smul_le t v := le_of_eq (A.seminorm.smul' t v)
abbrev Space := UniformSpace.Completion A.Finite

def finite (v : ι →₀ ℝ) : A.Finite := v
def array (v : A.Finite) : ι →₀ ℝ := v
def embedding : (ι →₀ ℝ) →ₗ[ℝ] A.Space :=
  (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := A.Finite)).toLinearMap
@[simp] lemma norm_embedding (v : ι →₀ ℝ) : ‖A.embedding v‖=A.seminorm v :=
  UniformSpace.Completion.norm_coe _

def coordinateFinite (i : ι) : A.Finite →L[ℝ] ℝ :=
  (show A.Finite →ₗ[ℝ] ℝ from Finsupp.lapply i).mkContinuous
    (A.coordinate_bound i).choose (by
      intro v
      change ‖(show ι →₀ ℝ from v) i‖ ≤ (A.coordinate_bound i).choose*A.seminorm v
      simpa only [Real.norm_eq_abs] using (A.coordinate_bound i).choose_spec v)
def coordinate (i : ι) : A.Space →L[ℝ] ℝ :=
  (A.coordinateFinite i).extend UniformSpace.Completion.toComplL
@[simp] lemma coordinate_coe (i : ι) (v : A.Finite) : A.coordinate i (v : A.Space)=A.array v i :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) v
@[simp] lemma coordinate_embedding (i : ι) (v : ι →₀ ℝ) : A.coordinate i (A.embedding v)=v i :=
  A.coordinate_coe i (A.finite v)
def unit (i : ι) : A.Space := A.embedding (Finsupp.single i 1)
@[simp] lemma coordinate_unit (i j : ι) : A.coordinate i (A.unit j)=if j=i then 1 else 0 := by
  simp [unit,Finsupp.single_apply]

def projection (H : Finset ι) : A.Space →L[ℝ] A.Space :=
  ∑ i ∈ H,(A.coordinate i).smulRight (A.unit i)
@[simp] lemma projection_apply (H : Finset ι) (x : A.Space) :
    A.projection H x=∑ i ∈ H,A.coordinate i x • A.unit i := by simp [projection]
@[simp] lemma coordinate_projection (H : Finset ι) (x : A.Space) (i : ι) :
    A.coordinate i (A.projection H x)=if i ∈ H then A.coordinate i x else 0 := by
  simp [projection_apply,map_sum,map_smul,smul_eq_mul,mul_ite,Finset.sum_ite_eq']
end Data
end CoordinateCompletion

namespace CoordinateCompletion.Data
variable {ι κ : Type*} (A : CoordinateCompletion.Data ι)

end CoordinateCompletion.Data

end DiamondDistortion

end

end OAI


