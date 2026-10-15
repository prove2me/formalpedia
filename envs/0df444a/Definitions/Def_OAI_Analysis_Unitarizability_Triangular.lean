-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_Triangular
-- name    : OAI_Analysis_Unitarizability_Triangular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:10:09.636986+00:00
-- url     : https://prove2.me/theorems/df83c1ff-2cee-481d-8658-614bad8124e0
-- title:
--   Hilbert double $H\oplus_2 H$ and upper-triangular representations built from a twisted cocycle
-- statement:
--   Let $G$ be a group and let $H$ be a complex inner product space; write $B(H)$ for the algebra of bounded linear operators on $H$. This file builds, from a representation $U$ of $G$ on $H$ and a cocycle $D$, a representation of $G$ on $H\oplus H$ by upper-triangular block operators.
--
--   1. **The Hilbert double.** $H\oplus_2H$ is the space of pairs $(x,y)\in H\times H$ with the $\ell^2$ norm
--   $$\|(x,y)\|=\bigl(\|x\|^2+\|y\|^2\bigr)^{1/2}.$$
--   The coordinate embeddings $\iota_1x=(x,0)$ and $\iota_2y=(0,y)$ are bounded linear maps $H\to H\oplus_2H$, and both are isometric: $\|\iota_1x\|=\|\iota_2x\|=\|x\|$.
--   2. **Diagonal operators.** For $U\in B(H)$, the operator $\operatorname{diag}(U)\in B(H\oplus_2H)$ acts by $\operatorname{diag}(U)(x,y)=(Ux,\,Uy)$.
--   3. **Triangular operators.** For $U,D\in B(H)$, the operator $T(U,D)\in B(H\oplus_2H)$ is
--   $$T(U,D)(x,y)=\bigl(Ux+DUy,\ Uy\bigr),\qquad\text{that is,}\qquad T(U,D)=\begin{pmatrix}U&DU\\0&U\end{pmatrix}.$$
--   4. **Triangular representation.** Let $U:G\to B(H)$ be a group homomorphism into the multiplicative monoid of $B(H)$ (so $U(1)=I$, $U(gh)=U(g)U(h)$, and in particular $U(g^{-1})U(g)=I$), and let $D:G\to B(H)$ satisfy $D(1)=0$ and the twisted cocycle identity
--   $$D(gh)=D(g)+U(g)\,D(h)\,U(g^{-1})\qquad(g,h\in G).$$
--   Then
--   $$\pi_{U,D}(g)=T\bigl(U(g),D(g)\bigr)=\begin{pmatrix}U(g)&D(g)U(g)\\0&U(g)\end{pmatrix}$$
--   defines a group homomorphism $\pi_{U,D}:G\to B(H\oplus_2H)$.
--
--   In this project, triangular representations are the mechanism for producing representations that are not similar to unitary ones. Every coboundary $D(g)=B-U(g)BU(g^{-1})$ with $B\in B(H)$ satisfies the cocycle identity, and a separate theorem of the project shows, for complete $H$, the converse obstruction: if $\pi_{U,D}$ is similar to a unitary representation, then $D$ is such a coboundary for some bounded $B$. Hence a uniformly bounded cocycle over a unitary $U$ that is not of this form produces a uniformly bounded representation that is not unitarizable.
--
--   **Formalization Note** $H\oplus_2H$ is `Double H`, an abbreviation for `WithLp 2 (H × H)`; the embeddings are `inl` and `inr`, the operators are `diagonal U` and `operator U D`, and the representation is `representation U D h1 hD`, where the cocycle identity is written with `conjugate U g T`, i.e. $U(g)\,T\,U(g^{-1})$. The simp lemmas `inl_apply`, `inr_apply`, `inl_norm`, `inr_norm`, `diagonal_fst`, `diagonal_snd`, `operator_fst`, `operator_snd` record the coordinate formulas above, and `inv_apply` records $U(g^{-1})\bigl(U(g)x\bigr)=x$. Completeness of $H$ is not assumed in this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Triangular.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Triangular.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Dixmier mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames
import Definitions.Def_OAI_Analysis_Unitarizability_Frames
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum
import Definitions.Def_OAI_Analysis_Unitarizability_Masked
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra
import Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds

namespace OAI

/-! Bounded Hilbert sums and triangular representations. -/
noncomputable section
namespace Dixmier
namespace Triangular
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
abbrev Double (H : Type*) := WithLp 2 (H × H)

def inl : H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H H)

def inr : H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ H H)

@[simp] theorem inl_apply (x : H) : inl x = WithLp.toLp 2 (x,0) := rfl
@[simp] theorem inr_apply (x : H) : inr x = WithLp.toLp 2 (0,x) := rfl
@[simp] theorem inl_norm (x : H) : ‖inl x‖ = ‖x‖ := WithLp.norm_toLp_fst 2 H H x
@[simp] theorem inr_norm (x : H) : ‖inr x‖ = ‖x‖ := WithLp.norm_toLp_snd 2 H H x

def diagonal (U : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  inl.comp (U.comp (WithLp.fstL 2 ℂ H H)) +
    inr.comp (U.comp (WithLp.sndL 2 ℂ H H))

@[simp] theorem diagonal_fst (U : H →L[ℂ] H) (x : Double H) :
    (diagonal U x).fst = U x.fst := by simp [diagonal, inl, inr]
@[simp] theorem diagonal_snd (U : H →L[ℂ] H) (x : Double H) :
    (diagonal U x).snd = U x.snd := by simp [diagonal, inl, inr]

def operator (U D : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  diagonal U + inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H)))

@[simp] theorem operator_fst (U D : H →L[ℂ] H) (x : Double H) :
    (operator U D x).fst = U x.fst + D (U x.snd) := by simp [operator, inl]
@[simp] theorem operator_snd (U D : H →L[ℂ] H) (x : Double H) :
    (operator U D x).snd = U x.snd := by simp [operator, inl]

@[simp] theorem inv_apply (U : G →* (H →L[ℂ] H)) (g : G) (x : H) : U g⁻¹ (U g x) = x := by
  have h : U g⁻¹ * U g = 1 := by rw [← map_mul]; simp
  exact congrArg (fun T : H →L[ℂ] H => T x) h

def representation (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h)) :
    G →* (Double H →L[ℂ] Double H) where
  toFun g := operator (U g) (D g)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext <;> simp [h1]
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext
    · change (operator (U (g*h)) (D (g*h)) x).fst =
        (operator (U g) (D g) (operator (U h) (D h) x)).fst
      simp only [operator_fst, operator_snd, map_mul, hD, conjugate,
        add_apply, mul_apply_eq_comp, map_add, inv_apply]
      abel
    · simp [map_mul, mul_apply_eq_comp]

end Triangular
end Dixmier

end

end OAI


