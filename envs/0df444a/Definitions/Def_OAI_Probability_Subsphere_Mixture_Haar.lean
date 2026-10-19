-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar
-- name    : OAI_Probability_Subsphere_Mixture_Haar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:56:15.794608+00:00
-- url     : https://prove2.me/theorems/58e1d161-ad8c-4a96-831a-a47e6c5b6ee0
-- title:
--   Haar probability measure on the orthogonal group and block-diagonal orthogonal maps
-- statement:
--   Let $E$ be a finite-dimensional real inner product space. Its orthogonal group $O(E)$ is realized as the group of unitary elements of the algebra of linear operators on $E$, i.e. the operators $U$ with $U^{*}U=UU^{*}=I$; it is a compact group for the operator-norm topology and carries the corresponding Borel $\sigma$-algebra. Let $\mathfrak h_E$ denote the Haar measure on $O(E)$ normalized so that $\mathfrak h_E(O(E))=1$. For a linear subspace $V\subseteq E$, $V^{\perp}$ is its orthogonal complement, $P_V$ and $P_{V^\perp}$ are the orthogonal projections onto $V$ and $V^{\perp}$, and $V$, $V^{\perp}$ carry the induced inner products, so that $O(V)$ and $O(V^{\perp})$ are defined.
--
--   1. **Haar probability on $O(E)$.** $\mathfrak h_E$ is a probability measure and a Haar measure on $O(E)$ (invariant under left translations $A\mapsto uA$). It is also right-invariant: for every $u\in O(E)$ the map $v\mapsto vu$ preserves $\mathfrak h_E$, so
--   $$\mathfrak h_E(uA)=\mathfrak h_E(Au)=\mathfrak h_E(A)\qquad\text{for all Borel }A\subseteq O(E),\ u\in O(E).$$
--   2. **Action map.** $\operatorname{act}(u,x)=ux$ is the evaluation of $u\in O(E)$ at $x\in E$. The map $(u,x)\mapsto ux$ is jointly continuous on $O(E)\times E$, and $\operatorname{act}(I,x)=x$.
--   3. **Block-diagonal orthogonal maps.** For $u\in O(V)$ and $w\in O(V^{\perp})$, the block map $B_V(u,w)$ is the linear isometric automorphism of $E=V\oplus V^{\perp}$ acting by $u$ on $V$ and by $w$ on $V^{\perp}$; explicitly
--   $$B_V(u,w)\,x=u\,(P_Vx)+w\,(P_{V^\perp}x),\qquad x\in E.$$
--   The file records this formula, the joint continuity of $(u,w,x)\mapsto B_V(u,w)x$ on $O(V)\times O(V^{\perp})\times E$, the identity $B_V(I,I)=\mathrm{id}_E$, and the restriction rules $B_V(u,w)y=uy$ for $y\in V$ and $B_V(u,w)z=wz$ for $z\in V^{\perp}$.
--
--   Haar-random orthogonal maps are the standard way to produce rotation-invariant randomness: applying a Haar-random $u$ to a fixed unit vector gives a uniformly distributed point of the unit sphere, and a block map $B_V(I,w)$ with Haar-random $w\in O(V^{\perp})$ randomizes the component orthogonal to $V$ while fixing $V$ pointwise. These are the basic ingredients of the direction laws on spheres that are compared with uniform and latitude laws in the spherical mixture estimate.
--
--   **Formalization Note** $O(E)$ is `Orthogonal E := unitary (E →L[ℝ] E)` and $\mathfrak h_E$ is `orthogonalLaw`, Mathlib's `Measure.haarMeasure` normalized on the compact set `univ`; compactness of $O(E)$, `orthogonalLaw` and `blockIso V u w : E ≃ₗᵢ[ℝ] E` come from the base definitions of this project. This file adds the instances `orthogonal_probability`, `orthogonal_haar`, `orthogonal_right`, the function `act` with `continuous_act` and `act_one`, and the lemmas `blockIso_apply`, `continuous_blockIso`, `blockIso_one`, `blockIso_on_left`, `blockIso_on_right`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/Haar.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/Haar.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

instance orthogonal_probability : IsProbabilityMeasure (orthogonalLaw (E := E)) :=
  ⟨Measure.haarMeasure_self⟩

instance orthogonal_haar : (orthogonalLaw (E := E)).IsHaarMeasure := by
  unfold orthogonalLaw
  infer_instance

instance orthogonal_right : (orthogonalLaw (E := E)).IsMulRightInvariant := by
  constructor
  intro u
  haveI : IsProbabilityMeasure ((orthogonalLaw (E := E)).map (· * u)) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const u).aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

def act (u : Orthogonal E) (x : E) : E := (u.val : E →L[ℝ] E) x

lemma continuous_act : Continuous (fun z : Orthogonal E × E => act z.1 z.2) := by
  unfold act
  fun_prop

lemma act_one (x : E) : act (1 : Orthogonal E) x = x := rfl

variable [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma blockIso_apply (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : E) :
    blockIso V u w x = (act (E := V) u (V.orthogonalProjectionOnto x) : E) +
      (act (E := Vᗮ) w (Vᗮ.orthogonalProjectionOnto x) : E) := by
  simp only [blockIso,LinearIsometryEquiv.trans_apply,Submodule.orthogonalDecomposition_symm_apply,
    Submodule.orthogonalDecomposition_apply,LinearIsometryEquiv.withLpProdCongr_apply]
  rfl

lemma continuous_blockIso (V : Submodule ℝ E) :
    Continuous (fun z : (Orthogonal V × Orthogonal Vᗮ) × E => blockIso V z.1.1 z.1.2 z.2) := by
  simp only [blockIso_apply]
  exact ((continuous_subtype_val.comp (continuous_act.comp
      ((continuous_fst.comp continuous_fst).prodMk (V.orthogonalProjectionOnto.continuous.comp continuous_snd)))).add
    (continuous_subtype_val.comp (continuous_act.comp
      ((continuous_snd.comp continuous_fst).prodMk (Vᗮ.orthogonalProjectionOnto.continuous.comp continuous_snd)))))

@[simp] lemma blockIso_one (V : Submodule ℝ E) (x : E) : blockIso V 1 1 x = x := by
  rw [blockIso_apply,act_one,act_one]
  exact V.starProjection_add_starProjection_orthogonal x

@[simp] lemma blockIso_on_left (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : V) :
    blockIso V u w (x : E) = ((act (E := V) u x : V) : E) := by
  rw [blockIso_apply,Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)]
  simp [act]

@[simp] lemma blockIso_on_right (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : Vᗮ) :
    blockIso V u w (x : E) = ((act (E := Vᗮ) w x : Vᗮ) : E) := by
  rw [blockIso_apply,V.orthogonalProjectionOnto_apply_of_mem_orthogonal x.prop]
  simp [act]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
noncomputable section
universe u v w
namespace SubsphereCurrent

end SubsphereCurrent
end
end

end OAI


