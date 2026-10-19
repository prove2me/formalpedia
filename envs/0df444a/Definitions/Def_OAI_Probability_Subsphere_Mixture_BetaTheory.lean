-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Mixture_BetaTheory
-- name    : OAI_Probability_Subsphere_Mixture_BetaTheory
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:57:13.280612+00:00
-- url     : https://prove2.me/theorems/f602800e-5164-449d-8761-6dca54a90a2f
-- title:
--   Beta–gamma change of variables, Gaussian-radius sphere laws and spherical mixture laws
-- statement:
--   Throughout, $E$ is a finite-dimensional real inner product space with its Borel $\sigma$-algebra and Lebesgue measure $\lambda_E$ (normalized so that the cube spanned by an orthonormal basis has volume $1$). $S_E=\{x\in E:\|x\|=1\}$ is the unit sphere, $|S_E|=\dim E\cdot\lambda_E(B(0,1))$ is its surface area, and $\sigma_E$ is the uniform probability measure on $S_E$ (surface measure divided by $|S_E|$), also regarded as a measure on $E$ concentrated on $S_E$. For a linear subspace $V\subseteq E$, $V^{\perp}$ is its orthogonal complement, $P_V$ and $P_{V^\perp}$ are the orthogonal projections, and $V$, $V^{\perp}$ carry the induced inner products (so $\sigma_V$, $\sigma_{V^\perp}$ are defined). $\Gamma(\alpha,1)$ is the gamma law with shape $\alpha$ and rate $1$ (density $x^{\alpha-1}e^{-x}/\Gamma(\alpha)$ on $(0,\infty)$) and $\mathrm{Beta}(a,b)$ is the beta law on $(0,1)$.
--
--   1. **Restriction to an invariant subspace.** For a subspace $N\subseteq E$ and a linear isometric automorphism $e$ of $E$ with $e(N)=N$, the restriction $e|_N$ is $e$ regarded as a linear isometric automorphism of $N$.
--   2. **Perpendicular coordinate.** $h_V(x)=\|P_{V^\perp}x\|^{2}$ for $x\in E$, the squared length of the component of $x$ orthogonal to $V$.
--   3. **Mixture sampler and mixture law.** For $h\in\mathbb{R}$, $s\in V$ and $t\in V^{\perp}$,
--   $$\Phi_V(h,s,t)=\sqrt{1-h}\,s+\sqrt{h}\,t,$$
--   and for a measure $\rho$ on $\mathbb{R}$ the mixture law is the image measure on $E$
--   $$M_V(\rho)=(\Phi_V)_{\#}\bigl(\rho\otimes\sigma_V\otimes\sigma_{V^\perp}\bigr).$$
--   If $\rho$ is a probability measure on $[0,1]$ and $V\ne\{0\}\ne V^{\perp}$, this is the law of the unit vector $\sqrt{1-H}\,S+\sqrt{H}\,T$, where $H\sim\rho$, $S$ is uniform on the unit sphere of $V$ and $T$ is uniform on the unit sphere of $V^{\perp}$, all independent; its perpendicular coordinate is $H$.
--   4. **Beta–gamma change of variables.** On $\mathbb{R}^{2}$,
--   $$\operatorname{split}(x,g)=\bigl(xg,\,(1-x)g\bigr),\qquad \operatorname{join}(y,z)=\Bigl(\frac{y}{y+z},\,y+z\Bigr),$$
--   with the domains $D_\beta=(0,1)\times(0,\infty)$ and $D_\Gamma=(0,\infty)\times(0,\infty)$, and the derivative of $\operatorname{split}$ at $z=(z_1,z_2)$, the linear map
--   $$D\operatorname{split}(z)(h_1,h_2)=\bigl(z_2h_1+z_1h_2,\ -z_2h_1+(1-z_1)h_2\bigr),$$
--   whose determinant is $z_2$.
--   5. **Gaussian-radius sphere law.** $\Gamma^{\circ}_E$ is the law of $\sqrt{G}\,S$ with $S\sim\sigma_E$ and $G\sim\Gamma(\tfrac{\dim E}{2},1)$ independent,
--   $$\Gamma^{\circ}_E=\bigl((s,g)\mapsto\sqrt{g}\,s\bigr)_{\#}\bigl(\sigma_E\otimes\Gamma(\tfrac{\dim E}{2},1)\bigr),$$
--   and its density constant is
--   $$c_E=\frac{2}{\Gamma(\dim E/2)}\cdot\frac{1}{|S_E|}.$$
--   When $E\ne\{0\}$, $\Gamma^{\circ}_E$ is a probability measure.
--   6. **Sum over an orthogonal splitting.** For a subspace $V$ with $V\ne\{0\}$ and $V^{\perp}\ne\{0\}$, $\Sigma_V$ is the law on $E$ of $X+Y$, where $X\sim\Gamma^{\circ}_V$ and $Y\sim\Gamma^{\circ}_{V^\perp}$ are independent; it is a probability measure.
--
--   These objects identify the scalar coordinate laws needed to compare rotation-invariant laws on spheres. The module shows that $\operatorname{split}$ maps $D_\beta$ bijectively onto $D_\Gamma$ with inverse $\operatorname{join}$ and carries $\mathrm{Beta}(a,b)\otimes\Gamma(a+b,1)$ to $\Gamma(a,1)\otimes\Gamma(b,1)$ for $a,b>0$; that for $E\ne\{0\}$ the law $\Gamma^{\circ}_E$ has density $c_E\,e^{-\|x\|^{2}}$ with respect to $\lambda_E$ (it is the centred Gaussian law with covariance $\tfrac12 I$); and, through $\Sigma_V$, that for $V\ne\{0\}\ne V^{\perp}$ the squared projection $\|P_Vx\|^{2}$ has law $\mathrm{Beta}(\tfrac{\dim V}{2},\tfrac{\dim V^{\perp}}{2})$ when $x\sim\sigma_E$. Mixture laws are the general form of block-invariant spherical laws: for $V\ne\{0\}\ne V^{\perp}$, every probability measure on the unit sphere of $E$ that is invariant under all block-diagonal orthogonal maps of $V\oplus V^{\perp}$ equals $M_V(\rho)$ with $\rho$ the law of $h_V$ (this is proved later in the development), so comparisons between mixing laws on $[0,1]$ transfer to comparisons between spherical laws.
--
--   **Formalization Note** The definitions are `restrictIso`, `perpCoordinate`, `mixtureSampler`, `mixtureLaw`, `betaSplit`, `betaJoin`, `betaDomain`, `gammaDomain`, `betaSplitDeriv`, `gammaSphere`, `gammaSphereConstant` and `sumGamma`, with the instances `gammaSphere_probability` (which assumes `[Nontrivial E]`) and `sumGamma_probability`. `sumGamma` takes `[Nontrivial V] [Nontrivial Vᗮ]` as arguments, while `gammaSphere` itself does not assume $E\ne\{0\}$. Here $\sigma_E$ is `SubsphereRegression.ambientSphereLaw`, $|S_E|$ is `(volume : Measure E).toSphere univ`, and the gamma and beta laws are Mathlib's `gammaMeasure α 1` and `betaMeasure a b`. `Real.sqrt` returns $0$ on negative arguments and real division by $0$ gives $0$; these conventions only matter outside the intended domains.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/BetaTheory.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/BetaTheory.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory Set
open scoped RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Restriction of an actual ambient orthogonal map to a stable subspace. -/
def restrictIso (N : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (he : N.map e.toLinearMap = N) : N ≃ₗᵢ[ℝ] N :=
  (LinearIsometryEquiv.submoduleMap N e).trans (LinearIsometryEquiv.ofEq _ _ he)

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

/-- Squared norm of the distinguished perpendicular component. -/
def perpCoordinate (V : Submodule ℝ E) (x : E) : ℝ := ‖Vᗮ.orthogonalProjectionOnto x‖^2

/-- Common direction kernel for all block-invariant spherical laws. -/
def mixtureSampler (V : Submodule ℝ E) (z : ℝ × (V × Vᗮ)) : E :=
  Real.sqrt (1-z.1) • (z.2.1 : E) + Real.sqrt z.1 • (z.2.2 : E)

def mixtureLaw (V : Submodule ℝ E) (ρ : Measure ℝ) : Measure E :=
  (ρ.prod ((SubsphereRegression.ambientSphereLaw (E := V)).prod
    (SubsphereRegression.ambientSphereLaw (E := Vᗮ)))).map (mixtureSampler V)

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
open MeasureTheory
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set Module
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

def betaSplit (z : ℝ × ℝ) : ℝ × ℝ := (z.1*z.2,(1-z.1)*z.2)
def betaJoin (z : ℝ × ℝ) : ℝ × ℝ := (z.1/(z.1+z.2),z.1+z.2)
def betaDomain : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)
def gammaDomain : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)

def betaSplitDeriv (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (z.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + z.1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((-z.2) • ContinuousLinearMap.fst ℝ ℝ ℝ + (1-z.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)

end SubsphereCurrent.Mixture
end
end
section
/-! Exact beta/gamma independence and products, needed to identify the scalar
coordinate laws in the geometric comparison. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- A uniform direction with independent squared radius Γ(dim/2,1). -/
def gammaSphere : Measure E :=
  ((SubsphereRegression.sphereLaw (E := E)).prod
    (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1)).map
      (fun z => Real.sqrt z.2 • z.1.val)

def gammaSphereConstant (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : ℝ≥0∞ :=
  ENNReal.ofReal (2/Real.Gamma ((Module.finrank ℝ E : ℝ)/2)) *
    ((volume : Measure E).toSphere univ)⁻¹

instance gammaSphere_probability : IsProbabilityMeasure (gammaSphere (E := E)) := by
  let : IsProbabilityMeasure (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1) :=
    isProbabilityMeasure_gammaMeasure (by have := Module.finrank_pos (R := ℝ) (M := E); positivity)
      (by norm_num)
  unfold gammaSphere
  exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def sumGamma (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ] : Measure E :=
  ((gammaSphere (E := V)).prod (gammaSphere (E := Vᗮ))).map
    (fun z => (z.1 : E)+(z.2 : E))

instance sumGamma_probability (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ] :
    IsProbabilityMeasure (sumGamma V) := by
  unfold sumGamma
  exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
/-! Actual squared-projection beta law of the normalized Haar sphere. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end

end OAI


