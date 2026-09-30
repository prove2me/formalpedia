-- Prove2me | Definitions.Def_TranscendenceTheory_GraphQuotientExtension
-- name    : TranscendenceTheory_GraphQuotientExtension
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-08T16:16:14.148267+00:00
-- url     : https://prove2.me/theorems/6063c3f0-37a2-4e50-8945-bec72ba903e7
-- title:
--   Period graph quotient, extension maps and one-parameter subgroup
-- statement:
--   For modules $A,B$ over a ring $R$, a submodule $\Lambda\subseteq A$ and a linear map $\eta:\Lambda\to B$, define $\Gamma_\eta=\{(\omega,-\eta(\omega)):\omega\in\Lambda\}$, $E_\eta=(A\times B)/\Gamma_\eta$ and $G_\eta=A\times E_\eta$. The associated linear maps are $i(b)=[(0,b)]$, $p([(a,b)])=a\bmod\Lambda$, $\varphi(a)=(a,[(a,0)])$, $p_a(t,e)=t$ and $p_E(t,e)=p(e)$. The definition includes the elementary well-definedness of $p$, since each graph period has first coordinate in $\Lambda$. Exactness, subgroup pullbacks and finite quotient-count identities are separate theorem obligations. For the elliptic application, $R=\mathbb Z$, $A=B=\mathbb C$ and $\eta$ is the canonical quasiperiod homomorphism. No topology or algebraic-group structure is asserted by these definitions.
-- source:
--   Derived additive quotient model from Senthil Kumar K (2026), Appendix A.2, equation (A.3) and the displayed exponential map before equation (A.4), https://doi.org/10.1017/S001309152610145X. The exponential kernel in the last two coordinates consists of (omega,-eta(omega)); the definitions generalize this graph quotient to modules.

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Prod

noncomputable section
namespace TranscendenceTheory

variable {R A B : Type*} [Ring R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]

/-- Period pairs `(omega, -eta omega)` for a linear map on a submodule. -/
def extensionPeriodGraph (Λ : Submodule R A) (η : Λ →ₗ[R] B) : Submodule R (A × B) :=
  LinearMap.range (Λ.subtype.prod (-η))

/-- The additive quotient underlying an extension by `B`. -/
abbrev GraphQuotientExtension (Λ : Submodule R A) (η : Λ →ₗ[R] B) :=
  (A × B) ⧸ extensionPeriodGraph Λ η

/-- The vertical inclusion into the quotient extension. -/
def extensionInclusion (Λ : Submodule R A) (η : Λ →ₗ[R] B) :
    B →ₗ[R] GraphQuotientExtension Λ η :=
  (extensionPeriodGraph Λ η).mkQ.comp (LinearMap.inr R A B)

/-- The first coordinate modulo `Λ`, which is well-defined on the extension. -/
def extensionProjection (Λ : Submodule R A) (η : Λ →ₗ[R] B) :
    GraphQuotientExtension Λ η →ₗ[R] A ⧸ Λ :=
  (extensionPeriodGraph Λ η).liftQ (Λ.mkQ.comp (LinearMap.fst R A B)) (by
    rintro _ ⟨ω, rfl⟩
    simp)

/-- The extra additive factor used in the three-dimensional group. -/
abbrev GraphExtensionGroup (Λ : Submodule R A) (η : Λ →ₗ[R] B) :=
  A × GraphQuotientExtension Λ η

/-- The one-parameter subgroup `z ↦ (z, [(z, 0)])`. -/
def extensionCurve (Λ : Submodule R A) (η : Λ →ₗ[R] B) :
    A →ₗ[R] GraphExtensionGroup Λ η :=
  LinearMap.id.prod ((extensionPeriodGraph Λ η).mkQ.comp (LinearMap.inl R A B))

/-- Projection onto the extra additive factor. -/
def extensionAdditiveProjection (Λ : Submodule R A) (η : Λ →ₗ[R] B) :
    GraphExtensionGroup Λ η →ₗ[R] A :=
  LinearMap.fst R A (GraphQuotientExtension Λ η)

/-- Projection onto the quotient of the first coordinate of the extension. -/
def extensionEllipticProjection (Λ : Submodule R A) (η : Λ →ₗ[R] B) :
    GraphExtensionGroup Λ η →ₗ[R] A ⧸ Λ :=
  (extensionProjection Λ η).comp (LinearMap.snd R A (GraphQuotientExtension Λ η))

end TranscendenceTheory


