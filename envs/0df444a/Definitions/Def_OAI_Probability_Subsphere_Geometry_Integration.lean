-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
-- name    : OAI_Probability_Subsphere_Geometry_Integration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:45:26.87252+00:00
-- url     : https://prove2.me/theorems/a2cf0efb-4bd1-4e7a-aed9-88075398b809
-- title:
--   Radial extensions, affine subsphere tests, nested tests, spherical caps and quarter-turn isometries
-- statement:
--   Throughout, $E$ is a finite-dimensional real inner product space with unit sphere $S_E=\{x\in E:\|x\|=1\}$. For a linear subspace $K\le E$, $K^\perp$ is its orthogonal complement, $P_K$ the orthogonal projection onto $K$, $S_K$ the unit sphere of $K$ and $\sigma_K$ the uniform probability law on $S_K$ (normalized surface measure).
--
--   1. **Unit direction and radial extension.** For $x\neq0$, $x/\|x\|\in S_E$. For $g:S_E\to[0,\infty]$, the radial extension is $\tilde g(x)=g(x/\|x\|)$ for $x\neq0$ and $\tilde g(0)=0$.
--   2. **Sphere maps.** A linear isometric isomorphism $e:E\to F$ between real inner product spaces restricts to a homeomorphism $S_E\to S_F$ of their unit spheres.
--   3. **Affine subsphere tests.** A $k$-dimensional test $A$ in $E$ consists of a subspace $K_A\le E$ of dimension $k$, a centre $c_A\in K_A^\perp$ and a radius $r_A>0$ with $\|c_A\|^2+r_A^2=1$. Its point map
--   $$S_{K_A}\ni s\longmapsto c_A+r_A\,s\in S_E$$
--   parametrizes the subsphere $S_E\cap(c_A+K_A)$ of the unit sphere. The same notion for $E=\mathbb{R}^d$ is used below for $n$-dimensional tests in $\mathbb{R}^d$.
--   4. **Rescaled tests.** For $x\in E$ and $r\in\mathbb{R}$ put $N(x,r)=\sqrt{\|x\|^2+r^2}$; it is positive when $r>0$, and $N(x,r)^2=\|x\|^2+r^2$. For a subspace $K$, a point $x\in K^\perp$ and $r>0$, the rescaled test has space $K$, centre $x/N(x,r)$ and radius $r/N(x,r)$: the sphere of radius $r$ about $x$ in the affine plane $x+K$, scaled onto the unit sphere.
--   5. **Controlled functions.** For $g:S_E\to[0,\infty]$, $k,b\in\mathbb{N}$ and $C\in[0,\infty]$, $g$ is $(k,b,C)$-controlled if
--   $$r_A^{\,b}\int_{S_{K_A}}g(c_A+r_A s)\,d\sigma_{K_A}(s)\le C\qquad\text{for every $k$-dimensional test } A .$$
--   6. **Nested tests.** Let $A$ be an $n$-dimensional test in $\mathbb{R}^d$ and $B$ a $k$-dimensional test inside the space $K_A$ (so $K_B\le K_A$ and $c_B\in K_A$ is orthogonal to $K_B$). The nested test is the $k$-dimensional test in $\mathbb{R}^d$ with space $K_B$ (viewed in $\mathbb{R}^d$ through a linear isometry onto its image), centre $c_A+r_Ac_B$ and radius $r_Ar_B$; its points are $c_A+r_A(c_B+r_Bs)$.
--   7. **Caps.** For $g:S_E\to[0,\infty]$, $z\in E$ and $t\in\mathbb{R}$, the cap restriction is $g_{z,t}(s)=g(s)$ if $\|s-z\|\le t$ and $0$ otherwise; the ball cap is the function on $E$ equal to the radial extension of $g_{z,t}$ on the open unit ball and $0$ outside it.
--   8. **Quarter turns.** For a real inner product space $F$, the twin turn is the linear isometry $(x,y)\mapsto(-y,x)$ of $F\times F$ with the Euclidean product norm. For a subspace $F\le E$ and a linear isometric isomorphism $e$ of $F$, the extension of $e$ is the linear isometry of $E$ acting as $e$ on $F$ and as the identity on $F^\perp$, namely $x\mapsto e(P_Fx)+P_{F^\perp}x$.
--
--   Tests and controlled functions are the affine slices of the sphere over which spherical averages are measured in the radius-weighted estimates; rescaled and nested tests express that slices of slices, and suitably rescaled spheres in affine planes, are again slices; the radial extension and ball caps convert spherical integrals into volume integrals over the unit ball; and sphere maps and quarter-turn extensions are isometries used to move the uniform spherical law and to displace points by a controlled amount.
--
--   **Formalization Note** Names: `Polar.unitDirection`, `Polar.radial`, `Polar.sphereMap`, `Slice.Test E k` with `Test.point`, `Slice.radiusNorm` (lemmas `radiusNorm_pos`, `radiusNorm_sq`), `Slice.scaledTest` (of dimension `Module.finrank ℝ K`), `Slice.Controlled`, `Weighted.nestedSpaceEquiv` (simp lemma `nestedSpaceEquiv_val`), `Weighted.nestedTest` (from an `Affine.Test d n` and a `Slice.Test A.space k`), `Slice.capFunction`, `Slice.ballCap`, `Quarter.twinTurn F` on `WithLp 2 (F × F)` and `Quarter.extend F e`. The law $\sigma_K$ is `Affine.sphereLaw K`, and the radius power in `Controlled` is the natural power `ENNReal.ofReal (A.radius ^ b)`. Several of these constructions (radial extension, sphere maps, caps, the twin turn) do not use finite-dimensionality, and the `[Nontrivial E]` assumptions of some sections are not arguments of these definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Integration.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Geometry/Integration.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def unitDirection (x : E) (hx : x ≠ 0) : Metric.sphere (0 : E) 1 :=
  ⟨NormedSpace.normalize x,mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx)⟩

def radial (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  by
    classical
    exact if hx : x = 0 then 0 else g (unitDirection x hx)

end SubsphereCurrent.Polar
end
end
section
/-! Isometric naturality of the exact normalized Haar spherical law. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
noncomputable section
namespace SubsphereCurrent.Polar
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

def sphereMap (e : E ≃ₗᵢ[ℝ] F) : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1 :=
  e.toHomeomorph.subtype (fun x => by
    simp only [mem_sphere_zero_iff_norm]
    exact (e.norm_map x).symm ▸ Iff.rfl)

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

structure Test (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) where
  space : Submodule ℝ E
  dimension : Module.finrank ℝ space = k
  center : E
  perpendicular : center ∈ spaceᗮ
  radius : ℝ
  positive : 0 < radius
  unit : ‖center‖^2 + radius^2 = 1

def Test.point {k : ℕ} (A : Test E k) (s : Metric.sphere (0 : A.space) 1) : Metric.sphere (0 : E) 1 := by
  refine ⟨A.center+A.radius • (s.val : E),mem_sphere_zero_iff_norm.mpr ?_⟩
  have ho : ⟪A.center,(s.val : E)⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal s.val.property A.perpendicular
  have hs : ‖(s.val : E)‖ = 1 := by
    rw [Submodule.norm_coe]
    exact mem_sphere_zero_iff_norm.mp s.property
  have hh : ‖A.center+A.radius • (s.val : E)‖^2 = 1 := by
    rw [norm_add_sq_real,real_inner_smul_right,ho,mul_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos A.positive,hs,mul_one]
    nlinarith [A.unit]
  nlinarith [norm_nonneg (A.center+A.radius • (s.val : E))]

def radiusNorm (x : E) (r : ℝ) : ℝ := Real.sqrt (‖x‖^2+r^2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma radiusNorm_pos (x : E) {r : ℝ} (hr : 0 < r) : 0 < radiusNorm x r := by
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg ‖x‖,sq_pos_of_pos hr]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma radiusNorm_sq (x : E) (r : ℝ) : radiusNorm x r ^ 2 = ‖x‖^2+r^2 :=
  Real.sq_sqrt (by positivity)

def scaledTest (K : Submodule ℝ E) {x : E} (hx : x ∈ Kᗮ)
    (r : ℝ) (hr : 0 < r) : Test E (Module.finrank ℝ K) where
  space := K
  dimension := rfl
  center := (radiusNorm x r)⁻¹ • x
  perpendicular := Kᗮ.smul_mem _ hx
  radius := r / radiusNorm x r
  positive := div_pos hr (radiusNorm_pos x hr)
  unit := by
    have hp := radiusNorm_pos x hr
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
    have hh := radiusNorm_sq x r
    field_simp
    nlinarith

def Controlled (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) (k b : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ A : Test E k, ENNReal.ofReal (A.radius^b) *
    (∫⁻ s, g (A.point s) ∂Affine.sphereLaw A.space) ≤ C

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Weighted

def nestedSpaceEquiv {d n k : ℕ} (A : Affine.Test d n) (B : Slice.Test A.space k) :
    B.space ≃ₗᵢ[ℝ] B.space.map A.space.subtype where
  toLinearEquiv := B.space.equivMapOfInjective A.space.subtype Subtype.val_injective
  norm_map' := by intro x; rfl

@[simp] lemma nestedSpaceEquiv_val {d n k : ℕ} (A : Affine.Test d n)
    (B : Slice.Test A.space k) (x : B.space) :
    (nestedSpaceEquiv A B x : Vector d) = (x.val : Vector d) := rfl

def nestedTest {d n k : ℕ} (A : Affine.Test d n) (B : Slice.Test A.space k) : Affine.Test d k where
  space := B.space.map A.space.subtype
  dimension := (nestedSpaceEquiv A B).toLinearEquiv.finrank_eq.symm.trans B.dimension
  center := A.center + A.radius • (B.center : Vector d)
  perpendicular := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro y hy
    obtain ⟨x,hx,rfl⟩ := hy
    rw [inner_add_right,real_inner_smul_right]
    have hA : ⟪(x : Vector d),A.center⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal x.property A.perpendicular
    have hB : ⟪(x : Vector d),(B.center : Vector d)⟫ = 0 := by
      change ⟪x,B.center⟫ = 0
      exact Submodule.inner_right_of_mem_orthogonal hx B.perpendicular
    change ⟪(x : Vector d),A.center⟫ + A.radius*⟪(x : Vector d),(B.center : Vector d)⟫ = 0
    rw [hA,hB,mul_zero,add_zero]
  radius := A.radius * B.radius
  radius_positive := mul_pos A.radius_positive B.positive
  unit := by
    have ho : ⟪A.center,(B.center : Vector d)⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal B.center.property A.perpendicular
    rw [norm_add_sq_real,real_inner_smul_right,ho,mul_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos A.radius_positive,Submodule.norm_coe]
    nlinarith [A.unit, B.unit]

end SubsphereCurrent.Weighted
end
end
section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def capFunction (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) (z : E) (t : ℝ)
    (s : Metric.sphere (0 : E) 1) : ℝ≥0∞ :=
  if dist s.val z ≤ t then g s else 0

def ballCap (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) (z : E) (t : ℝ) : E → ℝ≥0∞ :=
  (Metric.ball (0 : E) 1).indicator (Polar.radial (capFunction g z t))

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Quarter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def twinTurn (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    WithLp 2 (F × F) ≃ₗᵢ[ℝ] WithLp 2 (F × F) :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ F F).trans
    ((LinearIsometryEquiv.neg ℝ).withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ F))

def extend (F : Submodule ℝ E) (e : F ≃ₗᵢ[ℝ] F) : E ≃ₗᵢ[ℝ] E :=
  (F.orthogonalDecomposition.trans
    (e.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ Fᗮ))).trans F.orthogonalDecomposition.symm

end SubsphereCurrent.Quarter
end
end

end OAI


