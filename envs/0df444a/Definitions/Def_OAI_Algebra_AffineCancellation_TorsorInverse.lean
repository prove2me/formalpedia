-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_TorsorInverse
-- name    : OAI_Algebra_AffineCancellation_TorsorInverse
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:32:03.272138+00:00
-- url     : https://prove2.me/theorems/4ca84622-2a36-4270-9b54-7c22ede5887e
-- title:
--   The backward map from Laurent polynomials to the fraction field of the modification $B$ attached to a frame
-- statement:
--   This file constructs, from a frame and a compatible coefficient map into the fraction field of the affine modification $B$, an algebra homomorphism from Laurent polynomials back into that fraction field.
--
--   **Setting.** Let $G=\mathbb{C}[p,s,u,F,J]/(x^2F-(1+2sx)J-p^2J^2)$ with $x=s^2+u^3+p^2F$, and put $y=s+x(x-u^3)$ and $z=sx+p^2J$ in $G$. Let $R=\mathbb{C}[X,Y,Z,U]/(XY-Z(Z+1))$ with $\sigma=Y-X(X-U^3)$, let $\kappa:R\to G$ send $X,Y,Z,U$ to $x,y,z,u$, let $S=\mathbb{C}[a,d,b,c,u]/(ac-bd-1)$, and let $\iota:R\to S$ send $X,Y,Z,U$ to $ab,dc,db,u$. With $v=a^3b-a^2u^3-d^2$, $h=ab-u^3$ and $C_1=c^2-b^2h$ in $S$, let $B=S[\tau,V]/(\tau^2V-v)$, with structure map $j:S\to B$. The *pullback* $\pi^*:G\to B$ is the $\mathbb{C}$-algebra homomorphism with
--
--   $$\pi^*(p)=\tau,\quad \pi^*(s)=j(\iota(\sigma)),\quad \pi^*(u)=j(u),\quad \pi^*(F)=j(C_1)\,V,\quad \pi^*(J)=j(b^2)\,V,$$
--
--   and it satisfies $\pi^*\circ\kappa=j\circ\iota$. The ring $B$ is an integral domain; let $K_B$ be its field of fractions, $i_B:B\to K_B$ the canonical embedding, and write $\bar r=i_B(j(r))$ for $r\in S$.
--
--   Let $P$ be a commutative $\mathbb{C}$-algebra, $\rho:G\to P$ a $\mathbb{C}$-algebra homomorphism, $(a_0,d_0,b_0,c_0)\in P^4$ a frame for $\rho$ (that is, $a_0b_0=\rho(x)$, $d_0c_0=\rho(y)$, $d_0b_0=\rho(z)$ and $a_0c_0-d_0b_0=1$), and $L=P[T,T^{-1}]$. Let $\varphi:P\to K_B$ be a $\mathbb{C}$-algebra homomorphism with $\varphi\circ\rho=i_B\circ\pi^*$.
--
--   1. **Transported relations.** $\varphi(\rho(\kappa(r)))=\overline{\iota(r)}$ for all $r\in R$; consequently
--   $$\varphi(a_0)\varphi(b_0)=\bar a\bar b,\quad \varphi(d_0)\varphi(c_0)=\bar d\bar c,\quad \varphi(d_0)\varphi(b_0)=\bar d\bar b,\quad \varphi(a_0)\varphi(c_0)=\bar a\bar c,$$
--   and $\bar a\bar c-\bar b\bar d=1$.
--   2. **The comparison unit.** Put
--   $$w=\varphi(c_0)\,\bar a-\varphi(b_0)\,\bar d,\qquad w'=\varphi(a_0)\,\bar c-\varphi(d_0)\,\bar b .$$
--   Then $\varphi(b_0)\,w'=\bar b$, $\varphi(c_0)\,w'=\bar c$ and $ww'=1$, so $w$ is a unit of $K_B$ with inverse $w'$.
--   3. **The backward map.** $\Psi:L\to K_B$ is the $\mathbb{C}$-algebra homomorphism that applies $\varphi$ to coefficients and sends $T$ to $w$:
--   $$\Psi\Bigl(\sum_{n\in\mathbb{Z}} r_nT^n\Bigr)=\sum_{n\in\mathbb{Z}}\varphi(r_n)\,w^n,\qquad\text{in particular}\quad \Psi(T^{-1})=w' .$$
--
--   In matrix terms, $w$ and $w'$ are the diagonal entries of $\varphi(M_0)^{-1}M$, where $M_0=\begin{pmatrix}a_0&b_0\\ d_0&c_0\end{pmatrix}$ and $M=\begin{pmatrix}\bar a&\bar b\\ \bar d&\bar c\end{pmatrix}$ both have determinant one. By item 2, $\Psi$ sends $b_0T^{-1}$ and $c_0T^{-1}$ back to $\bar b$ and $\bar c$. The map $\Psi$ is the candidate left inverse of the forward map $B\to L$ built from the same frame (which sends $j(a),j(d),j(b),j(c)$ to $a_0T,d_0T,b_0T^{-1},c_0T^{-1}$), and it is what is used to prove that the forward map is injective.
--
--   **Formalization Note** `KB` is `FractionRing Bundle.B`, `ib` is $i_B$ and `bc` is the map $r\mapsto\bar r$. The hypothesis on $\varphi$ is `hf : f.comp ρ = ib.comp Bundle.pullback`. Item 1 consists of `compatibility`, `back_ab`, `back_dc`, `back_db`, `back_ac` and `bc_det`; item 2 of `w`, `wi`, `back_b`, `back_c`, `w_wi` and the unit `W`; the backward map is `backward`, defined with `LaurentPolynomial.eval₂`, with values `backward_C`, `backward_T_one` and `backward_T_neg_one`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/TorsorInverse.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/TorsorInverse.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.Torsor
open LaurentPolynomial
variable {P : Type*} [CommRing P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ)
abbrev KB := FractionRing Bundle.B
def ib : Bundle.B →ₐ[ℂ] KB := IsScalarTower.toAlgHom ℂ Bundle.B KB
def bc : Determinant.T →ₐ[ℂ] KB := ib.comp Bundle.j
variable (f : P →ₐ[ℂ] KB) (hf : f.comp ρ=ib.comp Bundle.pullback)
include hf
lemma compatibility (r : Quadric.R) : f (ρ (Degeneration.coefficientMap r))=bc (Bundle.inclusion r) := by
  rw [← AlgHom.comp_apply,hf]
  change ib (Bundle.pullback (Degeneration.coefficientMap r))=_
  change ib ((Bundle.pullback.comp Degeneration.coefficientMap) r)=_
  rw [Bundle.pullback_coefficientMap]
  rfl
lemma back_ab : f Q.a₀*f Q.b₀=bc Determinant.a*bc Determinant.b := by
  rw [← map_mul,Q.ab]
  simpa only [Degeneration.coefficientMap_x,Bundle.inclusion_x,map_mul] using compatibility ρ f hf Quadric.x
lemma back_dc : f Q.d₀*f Q.c₀=bc Determinant.d*bc Determinant.c := by
  rw [← map_mul,Q.dc]
  simpa only [Degeneration.coefficientMap_y,Bundle.inclusion_y,map_mul] using compatibility ρ f hf Quadric.y
lemma back_db : f Q.d₀*f Q.b₀=bc Determinant.d*bc Determinant.b := by
  rw [← map_mul,Q.db]
  simpa only [Degeneration.coefficientMap_z,Bundle.inclusion_z,map_mul] using compatibility ρ f hf Quadric.z
omit hf in
lemma bc_det : bc Determinant.a*bc Determinant.c-bc Determinant.b*bc Determinant.d=1 := by
  simpa only [map_mul,map_sub,map_one] using congrArg bc Determinant.determinant
lemma back_ac : f Q.a₀*f Q.c₀=bc Determinant.a*bc Determinant.c := by
  have he := congrArg f Q.det
  simp only [map_mul,map_sub,map_one] at he
  rw [back_db ρ Q f hf] at he
  linear_combination he-bc_det

def w : KB := f Q.c₀*bc Determinant.a-f Q.b₀*bc Determinant.d
def wi : KB := f Q.a₀*bc Determinant.c-f Q.d₀*bc Determinant.b
lemma back_b : f Q.b₀*wi ρ Q f=bc Determinant.b := by
  dsimp [wi]
  calc _ = (f Q.a₀*f Q.b₀)*bc Determinant.c-(f Q.d₀*f Q.b₀)*bc Determinant.b := by ring
    _ = _ := by rw [back_ab ρ Q f hf,back_db ρ Q f hf]; linear_combination bc Determinant.b*bc_det
lemma back_c : f Q.c₀*wi ρ Q f=bc Determinant.c := by
  dsimp [wi]
  calc _ = (f Q.a₀*f Q.c₀)*bc Determinant.c-(f Q.d₀*f Q.c₀)*bc Determinant.b := by ring
    _ = _ := by rw [back_ac ρ Q f hf,back_dc ρ Q f hf]; linear_combination bc Determinant.c*bc_det
lemma w_wi : w ρ Q f*wi ρ Q f=1 := by
  calc _ = bc Determinant.a*(f Q.c₀*wi ρ Q f)-bc Determinant.d*(f Q.b₀*wi ρ Q f) := by dsimp [w]; ring
    _ = _ := by rw [back_c ρ Q f hf,back_b ρ Q f hf]; linear_combination bc_det
def W : KBˣ := ⟨w ρ Q f,wi ρ Q f,w_wi ρ Q f hf,by rw [mul_comm]; exact w_wi ρ Q f hf⟩
def backward : L (P := P) →ₐ[ℂ] KB where
  __ := LaurentPolynomial.eval₂ f.toRingHom (W ρ Q f hf)
  commutes' r := by
    change LaurentPolynomial.eval₂ f.toRingHom (W ρ Q f hf) (C (algebraMap ℂ P r))=_
    rw [LaurentPolynomial.eval₂_C]
    exact f.commutes r
@[simp] lemma backward_C (r : P) : backward ρ Q f hf (C r)=f r := LaurentPolynomial.eval₂_C _ _ _
@[simp] lemma backward_T_one : backward ρ Q f hf (T 1)=w ρ Q f := by
  change LaurentPolynomial.eval₂ f.toRingHom (W ρ Q f hf) (T 1)=_
  rw [LaurentPolynomial.eval₂_T]
  simp only [zpow_one,W,Units.val_mk]
@[simp] lemma backward_T_neg_one : backward ρ Q f hf (T (-1))=wi ρ Q f := by
  change LaurentPolynomial.eval₂ f.toRingHom (W ρ Q f hf) (T (-1))=_
  rw [LaurentPolynomial.eval₂_T]
  simp only [zpow_neg_one]
  rfl
end ComplexCancellation.Torsor

end

end OAI


