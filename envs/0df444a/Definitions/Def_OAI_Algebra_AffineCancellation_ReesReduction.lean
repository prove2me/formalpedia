-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
-- name    : OAI_Algebra_AffineCancellation_ReesReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:20:32.047036+00:00
-- url     : https://prove2.me/theorems/d170b775-81f2-40db-a8b5-17f898891912
-- title:
--   Reduction of the Rees deformation modulo $q$ onto the degeneration
-- statement:
--   Let $\hat x=s^2+u^3+p^2F$ and consider the rings
--   $$B=\mathbb{C}[q,p,s,u,F,J]\big/\bigl(\hat x^2F-(1+2s\hat x)J-p^2J^2-q^3pu\bigr),\qquad G=\mathbb{C}[p,s,u,F,J]\big/\bigl(\hat x^2F-(1+2s\hat x)J-p^2J^2\bigr),$$
--   the Rees deformation and the degeneration; in both, letters denote the classes of the variables. The defining relation of $B$ becomes that of $G$ when $q=0$. The file defines the following maps.
--
--   1. **The reduction map.** $\mathrm{red}:B\to G$ is the $\mathbb{C}$-algebra homomorphism with $q\mapsto0$ and $p,s,u,F,J\mapsto p,s,u,F,J$; it is well defined because substituting $q=0$ in the relation of $B$ gives the relation of $G$. In particular $\mathrm{red}(q)=0$.
--
--   2. **The special fiber.** $B/qB$, with quotient map $\rho:B\to B/qB$; thus $\rho(q)=0$.
--
--   3. **The return map.** $\sigma:G\to B/qB$ is the $\mathbb{C}$-algebra homomorphism with $p,s,u,F,J\mapsto\rho(p),\rho(s),\rho(u),\rho(F),\rho(J)$. It is well defined because the relation of $G$, evaluated at these classes, equals $\rho$ applied to the relation of $B$ (which is $0$) once $\rho(q)=0$ is used.
--
--   These two maps are used to identify the special fiber $B/qB$ with $G$ (one has $\sigma\circ\mathrm{red}=\rho$), and hence to show that the kernel of the reduction map is $qB$. This is how a locally nilpotent derivation of $B$ that annihilates $q$ is pushed down to a derivation of $G$.
--
--   **Formalization Note** `B`, `π` and `q` come from the Rees module (`Poly = MvPolynomial (Fin 6) ℂ` with variables q, p, s, u, F, J) and `Degeneration.G` from the degeneration module (variables p, s, u, F, J). The reduction map is `red`, induced by `redEval = aeval ![0,p,s,u,F,J]` (well-definedness `redEval_relation`, value `red_q`); `Special = B ⧸ Ideal.span {q}` with quotient map `ρ` and `ρ_q`; the return map is `backRed`, induced by `backRedEval`, with well-definedness `backRedEval_relation`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/ReesReduction.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/ReesReduction.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial
def redValues : Fin 6 → Degeneration.G := ![0,Degeneration.p,Degeneration.s,
  Degeneration.u,Degeneration.F,Degeneration.J]
def redEval : Poly →ₐ[ℂ] Degeneration.G := aeval redValues
lemma redEval_relation : redEval relation=0 := by
  have h := Degeneration.relation_zero
  simpa [relation,xp,redEval,redValues,Degeneration.relation,Degeneration.xp,
    Degeneration.p,Degeneration.s,Degeneration.u,Degeneration.F,Degeneration.J,
    Matrix.cons_val,map_ofNat] using h
def red : B →ₐ[ℂ] Degeneration.G := Ideal.Quotient.liftₐ _ redEval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,redEval_relation,zero_mul])
@[simp] lemma red_π (r : Poly) : red (π r)=redEval r := Ideal.Quotient.lift_mk _ _ _
@[simp] lemma red_q : red q=0 := by simp [q,redEval,redValues]
abbrev Special := B ⧸ Ideal.span {q}
def ρ : B →ₐ[ℂ] Special := Ideal.Quotient.mkₐ ℂ _
def backRedValues : Fin 5 → Special := ![ρ (π (X 1)),ρ (π (X 2)),ρ (π (X 3)),
  ρ (π (X 4)),ρ (π (X 5))]
def backRedEval : Degeneration.P →ₐ[ℂ] Special := aeval backRedValues
lemma ρ_q : ρ q=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
lemma backRedEval_relation : backRedEval Degeneration.relation=0 := by
  have h := congrArg ρ relation_zero
  have hq := ρ_q
  change ρ (π (X 0))=0 at hq
  simp only [relation,xp,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,hq] at h
  norm_num at h
  simp only [backRedEval,backRedValues,Degeneration.relation,Degeneration.xp,aeval_X,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  linear_combination h
def backRed : Degeneration.G →ₐ[ℂ] Special := Ideal.Quotient.liftₐ _ backRedEval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  simp only [map_mul,backRedEval_relation]
  ring)
@[simp] lemma backRed_π (r : Degeneration.P) : backRed (Degeneration.π r)=backRedEval r :=
  Ideal.Quotient.lift_mk _ _ _
end ComplexCancellation.Rees

end

end OAI


