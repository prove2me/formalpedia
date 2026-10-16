-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_ReplicaLift
-- name    : OAI_Algebra_AffineCancellation_ReplicaLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:34:04.436382+00:00
-- url     : https://prove2.me/theorems/4c7d9db1-d28d-4604-a5b3-15e19f43db47
-- title:
--   The formal derivative on $F[X]$, finite generation of $B$, and the coefficient map from the polynomial model into $\mathrm{Frac}(B)$
-- statement:
--   This file collects auxiliary constructions used to lift a locally nilpotent derivation of the degenerate hypersurface ring through its polynomial model.
--
--   **Setting.** Let $G=\mathbb{C}[p,s,u,F,J]/(x^2F-(1+2sx)J-p^2J^2)$ with $x=s^2+u^3+p^2F$. Let $S=\mathbb{C}[a,d,b,c,u]/(ac-bd-1)$, $v=a^3b-a^2u^3-d^2\in S$, and let $B=S[\tau,V]/(\tau^2V-v)$ be the affine modification of $S$ along $v$; $B$ is an integral domain with field of fractions $K_B$ and canonical embedding $i_B:B\to K_B$. Let $\pi^*:G\to B$ be the injective pullback homomorphism, given on generators by $p\mapsto\tau$, $s\mapsto dc-ab(ab-u^3)$, $u\mapsto u$, $F\mapsto C_1V$ and $J\mapsto b^2V$, where $C_1=c^2-b^2(ab-u^3)$.
--
--   1. **Formal derivative.** For fields $k$ and $F$ with $F$ a $k$-algebra, the formal derivative on $F[X]$,
--   $$\partial_X\Bigl(\sum_i f_iX^i\Bigr)=\sum_i i\,f_iX^{i-1},$$
--   regarded as a $k$-linear derivation of $F[X]$.
--   2. **Finite generation.** $B$ is a finitely generated $\mathbb{C}$-algebra.
--   3. **Polynomial model.** Let $D$ be a locally nilpotent $\mathbb{C}$-derivation of $G$ (for each $r\in G$ some iterate $D^m(r)$ vanishes). Let $K=\mathrm{Frac}(G)$, let $\tilde D$ be the extension of $D$ to $K$ by the quotient rule, let $F_D=\{\xi\in K:\tilde D\xi=0\}$ be its field of constants, and put $P_D=F_D[X]$. Given a slice $t\in K$, i.e. an element with $\tilde D t=1$, the model homomorphism $\rho_D:G\to F_D[X]$ sends $r$ to the polynomial with coefficients in $F_D$ that takes the value $r$ at $X=t$:
--   $$\rho_D(r)(t)=r\qquad(r\in G).$$
--   4. **Fraction-field map.** $\theta:K\to K_B$ is the $\mathbb{C}$-algebra homomorphism extending the injective map $i_B\circ\pi^*:G\to K_B$ to the field of fractions of $G$.
--   5. **Inverse coefficient map.** $\chi:F_D[X]\to K_B$ is evaluation at the slice followed by $\theta$:
--   $$\chi(q)=\theta\bigl(q(t)\bigr)\qquad(q\in F_D[X]).$$
--
--   By item 3, $\chi\circ\rho_D=i_B\circ\pi^*$, so $\chi$ is a coefficient map of exactly the kind needed to invert the forward map attached to a frame over the polynomial model $\rho_D$. The derivation $\partial_X$ on $P_D$ corresponds to $D$ under $\rho_D$, in the sense that $\partial_X\rho_D(r)=\rho_D(D r)$, and is the derivation that is transported to $B$.
--
--   **Formalization Note** Item 1 is `SliceDerivative.derivation` (built from `Polynomial.derivative` with `Derivation.mk'`), item 2 is the instance `Bundle.finiteType`, and the file also records that $G$ has characteristic zero. In the namespace `PolynomialTorsor`, `K` and `P` are $K$ and $F_D[X]$ (with $F_D$ = `PolynomialModel.F D`), `ρ` is `PolynomialModel.model D hD ht`, which picks a polynomial representative using the slice theorem of earlier files, `toField` is $\theta$ (via `IsFractionRing.liftAlgHom`, using injectivity of `Bundle.pullback`), and `inverseCoefficient` is $\chi$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/ReplicaLift.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/ReplicaLift.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveObstruction
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorFrame
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorInverse

namespace OAI

noncomputable section

namespace ComplexCancellation.SliceDerivative
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
def derivation : Derivation k (Polynomial F) (Polynomial F) :=
  Derivation.mk' ((Polynomial.derivative (R := F)).restrictScalars k) (by
    intro p q
    change (p*q).derivative=p*q.derivative+q*p.derivative
    rw [Polynomial.derivative_mul,mul_comm p.derivative q,add_comm])
end ComplexCancellation.SliceDerivative

namespace ComplexCancellation.Bundle
instance finiteType : Algebra.FiniteType ℂ B := by
  let : Algebra.FiniteType ℂ Determinant.T := Algebra.FiniteType.quotient ℂ _
  infer_instance
end ComplexCancellation.Bundle

namespace ComplexCancellation.Torsor
open LaurentPolynomial
variable {P : Type*} [CommRing P] [IsDomain P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ) (D : Derivation ℂ Degeneration.G Degeneration.G)
variable (hρ : Function.Injective ρ) (hc : ∀ p, p ∈ InvariantClearing.subalgebra ρ D)
variable (Dp : Derivation ℂ P P) (hDp : LND.LocallyNilpotent Dp) (hder : ∀ r, Dp (ρ r)=ρ (D r))
include hρ hc hDp hder
end ComplexCancellation.Torsor

namespace ComplexCancellation.PolynomialTorsor
open PolynomialModel
instance : CharZero Degeneration.G := Algebra.charZero_of_charZero ℂ Degeneration.G
variable (D : Derivation ℂ Degeneration.G Degeneration.G) (hD : LND.LocallyNilpotent D)
abbrev K := FractionRing Degeneration.G
abbrev P := Polynomial (PolynomialModel.F D)
variable {t : K} (ht : FractionDerivation.extend D t=1)
noncomputable def ρ : Degeneration.G →ₐ[ℂ] P D := model D hD ht
def toField : K →ₐ[ℂ] Torsor.KB :=
  IsFractionRing.liftAlgHom (g := Torsor.ib.comp Bundle.pullback)
    ((IsFractionRing.injective Bundle.B Torsor.KB).comp Bundle.pullback_injective)
def inverseCoefficient : P D →ₐ[ℂ] Torsor.KB := (toField).comp (PolynomialModel.evaluation (D := D) (t := t))
end ComplexCancellation.PolynomialTorsor

end

end OAI


