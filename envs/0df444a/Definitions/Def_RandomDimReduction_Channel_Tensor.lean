-- Prove2me | Definitions.Def_RandomDimReduction_Channel_Tensor
-- name    : RandomDimReduction_Channel_Tensor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:22:53.233034+00:00
-- url     : https://prove2.me/theorems/32604614-4990-4cdb-a66d-0a1cc3250b92
-- title:
--   Tensor registers, rectangular powers, Haar twirling and projectors
-- statement:
--   Registers have standard basis indexed by functions from $\{0,\ldots,n-1\}$ to $\{0,\ldots,d-1\}$. For a rectangular matrix $W$, define
--   $$ (W^{\otimes n})_{i,j}=\prod_{t=0}^{n-1}W_{i(t),j(t)}. $$
--   The coordinate embedding $W_0$ has entries $\delta_{i,j}$; the random embedding is $VW_0$ for normalized Haar $V\in U(d)$. The unitary twirl integrates conjugation by $U^{\otimes n}$. Orthogonal projectors are the matrices of the actual subspace projections. Published Haar, CPTP and partial-trace primitives are reused.
--
--   These definitions fix the rectangular tensor and basis conventions used throughout the mission.
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), §§1.3–2.2, pp.5–6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Mathlib
import Definitions.Def_MixedCloning_Optimal_Model
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel
import Definitions.Def_WildeQIT_partialTrace

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Word (n d : ℕ) := Fin n → Fin d
abbrev Op (ι : Type*) := Matrix ι ι ℂ

/-- Rectangular tensor power; §1.3, pp.5–6. -/
def tensor {a b : Type} (n : ℕ) (W : Matrix a b ℂ) :
    Matrix (Fin n → a) (Fin n → b) ℂ := fun i j => ∏ t, W (i t) (j t)

/-- The source's fixed coordinate embedding W₀; for k ≤ d it is isometric. -/
def baseEmbedding (k d : ℕ) : Matrix (Fin d) (Fin k) ℂ :=
  fun i j => if i.val = j.val then 1 else 0

/-- Averaging over V defines the source's Haar-random isometry V W₀. -/
def randomEmbedding {d : ℕ} (k : ℕ) (V : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin d) (Fin k) ℂ := (V : Op (Fin d)) * baseEmbedding k d

/-- The continuous n-fold unitary twirl, on arbitrary complex operators. -/
def twirl (n d : ℕ) (X : Op (Word n d)) : Op (Word n d) :=
  ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    tensor n (U : Op (Fin d)) * X * (tensor n (U : Op (Fin d)))ᴴ
    ∂MixedCloning.Optimal.haar d

/-- Literal orthogonal subspace projector, in the standard tensor basis. -/
def subspaceProjector {ι : Type} [Fintype ι] (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    Op ι := fun i j => (S.starProjection ((EuclideanSpace.basisFun ι ℂ) j)) i

end RandomDimReduction.Channel


