-- Prove2me | Definitions.Def_RandomDimReduction_Channel_Moment
-- name    : RandomDimReduction_Channel_Moment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:23:55.429411+00:00
-- url     : https://prove2.me/theorems/5eb966f5-fb00-49e6-b112-22f946e8a802
-- title:
--   The Grassmannian moment and the integral-defined reduction channel
-- statement:
--   Let $M=\mathbb E_V[(VW_0W_0^\dagger V^\dagger)^{\otimes n}]$. Its inverse positive square root $A=\sqrt{M^+}$ is spectral functional calculus of $x\mapsto1/\sqrt{x}$, taking zero at zero. Let $Q$ and $P$ be the orthogonal projectors onto the actual kernel and image of $M$. Define
--   $$ R(X)=\mathbb E_V[(VW_0)^{\dagger\otimes n} A X A (VW_0)^{\otimes n}],\qquad R^{\rm TP}(X)=R(X)+\frac{\operatorname{tr}(QX)}{k^n}I. $$
--   These are formulas for every complex operator; no channel or twirling identity is assumed. The singular-moment case is included.
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), §2.2, Eqs.(2)–(3), pp.6–7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Tensor

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eq.(2), p.6: the actual Grassmannian projection moment. -/
def moment (n k d : ℕ) : Op (Word n d) :=
  ∫ V : Matrix.unitaryGroup (Fin d) ℂ,
    tensor n (randomEmbedding k V * (randomEmbedding k V)ᴴ)
    ∂MixedCloning.Optimal.haar d

/-- Positive inverse square root with zero on the kernel, i.e. √(M⁺).
The continuous functional calculus is on the finite spectrum, including zero. -/
def inverseRootMoment (n k d : ℕ) : Op (Word n d) :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (moment n k d)

/-- Q is literally the projector onto ker M, not a spectral formula assumed correct. -/
def kernelProjector (n k d : ℕ) : Op (Word n d) :=
  subspaceProjector (LinearMap.ker (Matrix.toEuclideanLin (moment n k d)))

/-- The image projector, separately from the kernel projector. -/
def imageProjector (n k d : ℕ) : Op (Word n d) :=
  subspaceProjector (LinearMap.range (Matrix.toEuclideanLin (moment n k d)))

/-- The integral-defined reduction map of §2.2, p.6. -/
def reduction (n k d : ℕ) (X : Op (Word n d)) : Op (Word n k) :=
  ∫ V : Matrix.unitaryGroup (Fin d) ℂ,
    (tensor n (randomEmbedding k V))ᴴ * inverseRootMoment n k d * X *
      inverseRootMoment n k d * tensor n (randomEmbedding k V)
    ∂MixedCloning.Optimal.haar d

/-- Eq.(3), pp.6–7, on every operator, including the kernel of M. -/
def RTP (n k d : ℕ) (X : Op (Word n d)) : Op (Word n k) :=
  reduction n k d X + (((kernelProjector n k d * X).trace) / (k ^ n : ℕ)) • 1

end RandomDimReduction.Channel


