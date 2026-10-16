-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_TorsorFrame
-- name    : OAI_Algebra_AffineCancellation_TorsorFrame
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:16:13.121967+00:00
-- url     : https://prove2.me/theorems/02f432a1-e3a5-4437-b157-1829b63cadc4
-- title:
--   Frames over the degenerate hypersurface and the forward map from the modification $B$ to Laurent polynomials
-- statement:
--   This file attaches to a *frame*, a determinant-one $2\times2$ matrix whose products of entries recover a point of the quadric $xy=z(z+1)$, an explicit algebra homomorphism from the affine modification $B$ into a ring of Laurent polynomials.
--
--   **Setting.** Let $G=\mathbb{C}[p,s,u,F,J]/(x^2F-(1+2sx)J-p^2J^2)$, where $x=s^2+u^3+p^2F$ (the defining polynomial is the polynomial $H$ of the main theorem with the term $-pu$ removed), and put $y=s+x(x-u^3)$ and $z=sx+p^2J$ in $G$; these satisfy $xy=z(z+1)$. Let $R=\mathbb{C}[X,Y,Z,U]/(XY-Z(Z+1))$, put $\sigma=Y-X(X-U^3)$, $f=X-\sigma^2-U^3$ and $g=Z-\sigma X$ in $R$, and let $\kappa:R\to G$ be the $\mathbb{C}$-algebra homomorphism with $X,Y,Z,U\mapsto x,y,z,u$; then $\kappa(f)=p^2F$ and $\kappa(g)=p^2J$. Let $S=\mathbb{C}[a,d,b,c,u]/(ac-bd-1)$ and let $\iota:R\to S$ send $X,Y,Z,U$ to $ab,\,dc,\,db,\,u$. In $S$ put
--
--   $$v=a^3b-a^2u^3-d^2,\qquad h=ab-u^3,\qquad C_1=c^2-b^2h,\qquad \alpha=a^2(1-2bd),\qquad \beta=d^2(3+2bd)+\alpha h,$$
--
--   so that $\iota(f)=C_1v$, $\iota(g)=b^2v$ and $\alpha C_1+\beta b^2=1$. Finally let $B=S[\tau,V]/(\tau^2V-v)$ be the affine modification of $S$ along $v$, with structure map $j:S\to B$.
--
--   Fix a commutative $\mathbb{C}$-algebra $P$ and a $\mathbb{C}$-algebra homomorphism $\rho:G\to P$, and let $L=P[T,T^{-1}]$ be the ring of Laurent polynomials over $P$. Elements of $P$, and through $\rho$ elements of $G$, are regarded as constants in $L$.
--
--   1. **Frames.** A frame for $\rho$ is a quadruple $(a_0,d_0,b_0,c_0)\in P^4$ with
--   $$a_0b_0=\rho(x),\qquad d_0c_0=\rho(y),\qquad d_0b_0=\rho(z),\qquad a_0c_0-d_0b_0=1 .$$
--   2. **The frame map.** Given a frame, $\Phi:S\to L$ is the $\mathbb{C}$-algebra homomorphism with
--   $$\Phi(a)=a_0T,\quad \Phi(d)=d_0T,\quad \Phi(b)=b_0T^{-1},\quad \Phi(c)=c_0T^{-1},\quad \Phi(u)=\rho(u)$$
--   (the variable $u$ of $S$ goes to the image of the variable $u$ of $G$). It is well defined because $(a_0T)(c_0T^{-1})-(b_0T^{-1})(d_0T)=1$. It is compatible with $\rho$ on the quadric, $\Phi\circ\iota=\rho\circ\kappa$ as maps $R\to L$, and consequently $\rho(p)^2\rho(F)=\Phi(C_1)\Phi(v)$ and $\rho(p)^2\rho(J)=\Phi(b^2)\Phi(v)$.
--   3. **The element $v_\Phi$.** Put $v_\Phi=\Phi(\alpha)\,\rho(F)+\Phi(\beta)\,\rho(J)\in L$. It satisfies $\rho(p)^2\,v_\Phi=\Phi(v)$.
--   4. **The forward map.** $\Phi^{+}:B\to L$ is the $\mathbb{C}$-algebra homomorphism with $\Phi^{+}(j(r))=\Phi(r)$ for $r\in S$, $\Phi^{+}(\tau)=\rho(p)$ and $\Phi^{+}(V)=v_\Phi$; it is well defined by item 3.
--
--   The Laurent variable $T$ plays the role of a fiber coordinate: $\Phi$ gives $a,d$ degree $1$ and $b,c$ degree $-1$ in $T$, while $u$, $\tau$ and all coefficients coming from $G$ have degree $0$. In the construction $P$ is a polynomial model of $G$ over a field, where frames exist by a Bézout argument, and the forward map is the channel through which a derivation of $P$, extended coefficientwise to $L$, is transported to the ring $B$.
--
--   **Formalization Note** `Frame ρ` is a structure with fields `a₀ d₀ b₀ c₀` and the four equations `ab`, `dc`, `db`, `det`. `L` is `LaurentPolynomial P`, `cc` is the constant embedding of $P$ into $L$ and `base` is its composite with $\rho$. The frame map is built as `frameEval` on the polynomial ring and descended to $S$ (`Determinant.T`) as `frameMap`; likewise `forwardEval` on $S[\tau,V]$ descends to `forward` on $B$ (`Bundle.B`). The element $v_\Phi$ is `vb`; `frameMap_inclusion`, `frame_f`, `frame_g` and `vb_equation` are the identities of items 2 and 3, `mono_pair` is the identity $(rT)(sT^{-1})=rs$, and the remaining simp lemmas give the values on generators.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/TorsorFrame.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/TorsorFrame.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.Torsor
open LaurentPolynomial
open MvPolynomial (X aeval aeval_X eval₂Hom_C eval₂Hom_X)
variable {P : Type*} [CommRing P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P)
structure Frame where
  a₀ : P
  d₀ : P
  b₀ : P
  c₀ : P
  ab : a₀*b₀=ρ Degeneration.x
  dc : d₀*c₀=ρ Degeneration.y
  db : d₀*b₀=ρ Degeneration.z
  det : a₀*c₀-d₀*b₀=1
variable (Q : Frame ρ)
abbrev L := LaurentPolynomial P
def cc : P →ₐ[ℂ] L (P := P) := IsScalarTower.toAlgHom ℂ P (L (P := P))
def base : Degeneration.G →ₐ[ℂ] L (P := P) := (cc (P := P)).comp ρ
omit [Algebra ℂ P] in
lemma mono_pair (r s : P) : C r*T (1:ℤ)*(C s*T (-1))=C (r*s) := by
  calc C r*T (1:ℤ)*(C s*T (-1)) = C (r*s)*(T (1:ℤ)*T (-1)) := by rw [map_mul]; ring
    _ = _ := by rw [← T_add]; norm_num

def frameEval : Determinant.Poly →ₐ[ℂ] L (P := P) :=
  aeval ![C Q.a₀*T 1,C Q.d₀*T 1,C Q.b₀*T (-1),C Q.c₀*T (-1),C (ρ Degeneration.u)]
lemma frameEval_relation : frameEval ρ Q Determinant.relation=0 := by
  simp only [frameEval,Determinant.relation,map_sub,map_mul,map_one,aeval_X,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [mono_pair,mul_comm (C Q.b₀*T (-1)),mono_pair,← map_sub,Q.det,map_one,sub_self]
def frameMap : Determinant.T →ₐ[ℂ] L (P := P) :=
  Ideal.Quotient.liftₐ _ (frameEval ρ Q) (by
    intro r hr
    obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
    rw [map_mul,frameEval_relation,zero_mul])
@[simp] lemma frameMap_π (r : Determinant.Poly) : frameMap ρ Q (Determinant.π r)=frameEval ρ Q r :=
  Ideal.Quotient.lift_mk _ _ _
@[simp] lemma frameMap_a : frameMap ρ Q Determinant.a=C Q.a₀*T 1 := by simp [Determinant.a,frameEval]
@[simp] lemma frameMap_d : frameMap ρ Q Determinant.d=C Q.d₀*T 1 := by simp [Determinant.d,frameEval]
@[simp] lemma frameMap_b : frameMap ρ Q Determinant.b=C Q.b₀*T (-1) := by simp [Determinant.b,frameEval,Matrix.cons_val]
@[simp] lemma frameMap_c : frameMap ρ Q Determinant.c=C Q.c₀*T (-1) := by simp [Determinant.c,frameEval,Matrix.cons_val]
@[simp] lemma frameMap_u : frameMap ρ Q Determinant.u=C (ρ Degeneration.u) := by simp [Determinant.u,frameEval,Matrix.cons_val]
lemma frameMap_inclusion : (frameMap ρ Q).comp Bundle.inclusion = (base ρ).comp Degeneration.coefficientMap := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change frameMap ρ Q (Bundle.inclusion Quadric.x)=base ρ (Degeneration.coefficientMap Quadric.x)
    rw [Bundle.inclusion_x,map_mul,frameMap_a,frameMap_b,mono_pair,Q.ab,Degeneration.coefficientMap_x]
    rfl
  · change frameMap ρ Q (Bundle.inclusion Quadric.y)=base ρ (Degeneration.coefficientMap Quadric.y)
    rw [Bundle.inclusion_y,map_mul,frameMap_d,frameMap_c,mono_pair,Q.dc,Degeneration.coefficientMap_y]
    rfl
  · change frameMap ρ Q (Bundle.inclusion Quadric.z)=base ρ (Degeneration.coefficientMap Quadric.z)
    rw [Bundle.inclusion_z,map_mul,frameMap_d,frameMap_b,mono_pair,Q.db,Degeneration.coefficientMap_z]
    rfl
  · change frameMap ρ Q (Bundle.inclusion Quadric.u)=base ρ (Degeneration.coefficientMap Quadric.u)
    rw [Bundle.inclusion_u,frameMap_u,Degeneration.coefficientMap_u]
    rfl
lemma frame_f : base ρ Degeneration.p^2*base ρ Degeneration.F =
    frameMap ρ Q Bundle.C₁*frameMap ρ Q Determinant.v := by
  have h := DFunLike.congr_fun (frameMap_inclusion ρ Q) Quadric.f
  simpa only [AlgHom.comp_apply,Bundle.inclusion_f,map_mul,Degeneration.coefficientMap_f,map_pow] using h.symm
lemma frame_g : base ρ Degeneration.p^2*base ρ Degeneration.J =
    frameMap ρ Q (Determinant.b^2)*frameMap ρ Q Determinant.v := by
  have h := DFunLike.congr_fun (frameMap_inclusion ρ Q) Quadric.g
  simpa only [AlgHom.comp_apply,Bundle.inclusion_g,map_mul,Degeneration.coefficientMap_g,map_pow] using h.symm

def vb : L (P := P) := frameMap ρ Q Bundle.α*base ρ Degeneration.F+frameMap ρ Q Bundle.β*base ρ Degeneration.J
lemma vb_equation : base ρ Degeneration.p^2*vb ρ Q=frameMap ρ Q Determinant.v := by
  have h := congrArg (frameMap ρ Q) Bundle.certificate
  simp only [map_add,map_mul,map_one] at h
  calc _ = frameMap ρ Q Bundle.α*(base ρ Degeneration.p^2*base ρ Degeneration.F)+
      frameMap ρ Q Bundle.β*(base ρ Degeneration.p^2*base ρ Degeneration.J) := by dsimp [vb]; ring
    _ = _ := by rw [frame_f,frame_g]; linear_combination frameMap ρ Q Determinant.v*h

def forwardEval : AffineModification.P Determinant.T →ₐ[ℂ] L (P := P) where
  __ := MvPolynomial.eval₂Hom (frameMap ρ Q).toRingHom ![base ρ Degeneration.p,vb ρ Q]
  commutes' r := by
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C (algebraMap ℂ Determinant.T r))=_
    rw [eval₂Hom_C]
    exact (frameMap ρ Q).commutes r
@[simp] lemma forwardEval_C (r : Determinant.T) : forwardEval ρ Q (MvPolynomial.C r)=frameMap ρ Q r := eval₂Hom_C _ _ _
@[simp] lemma forwardEval_X (i : Fin 2) : forwardEval ρ Q (X i)=![base ρ Degeneration.p,vb ρ Q] i := by
  change MvPolynomial.eval₂ _ _ (X i)=_
  exact MvPolynomial.eval₂_X _ _ _
lemma forwardEval_rel : forwardEval ρ Q (AffineModification.rel Determinant.T Determinant.v)=0 := by
  simp only [AffineModification.rel,map_sub,map_mul,map_pow,forwardEval_C,forwardEval_X,
    Matrix.cons_val_zero,Matrix.cons_val_one,vb_equation,sub_self]
def forward : Bundle.B →ₐ[ℂ] L (P := P) :=
  Ideal.Quotient.liftₐ _ (forwardEval ρ Q) (by
    intro r hr
    obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
    rw [map_mul,forwardEval_rel,zero_mul])
@[simp] lemma forward_π (r : AffineModification.P Determinant.T) :
    forward ρ Q (AffineModification.π Determinant.T Determinant.v r)=forwardEval ρ Q r :=
  Ideal.Quotient.lift_mk _ _ _
@[simp] lemma forward_j (r : Determinant.T) : forward ρ Q (Bundle.j r)=frameMap ρ Q r :=
by
  change forward ρ Q (AffineModification.π Determinant.T Determinant.v (MvPolynomial.C r))=_
  rw [forward_π,forwardEval_C]
@[simp] lemma forward_τ : forward ρ Q Bundle.τ=base ρ Degeneration.p := by
  simp [Bundle.τ,AffineModification.τ]
@[simp] lemma forward_V : forward ρ Q Bundle.V=vb ρ Q := by
  simp [Bundle.V,AffineModification.V]
variable [IsDomain P]
end ComplexCancellation.Torsor

end

end OAI


