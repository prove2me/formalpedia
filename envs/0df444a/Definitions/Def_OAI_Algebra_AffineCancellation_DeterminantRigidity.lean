-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
-- name    : OAI_Algebra_AffineCancellation_DeterminantRigidity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:09:32.507589+00:00
-- url     : https://prove2.me/theorems/7838b28b-35b9-4093-8336-a61e9b88be2e
-- title:
--   The $\mathfrak{sl}_2$ derivations, fiber Euler operator and auxiliary grading on $\mathbb{C}[a,d,b,c,u]/(ac-bd-1)$
-- statement:
--   Let $T=\mathbb{C}[a,d,b,c,u]/(ac-bd-1)$, where $a,d,b,c,u$ are the classes of five independent polynomial variables. Thus $T$ is the coordinate ring of $\mathrm{SL}_2\times\mathbb{A}^1$: the matrix $M=\begin{pmatrix}a&b\\ d&c\end{pmatrix}$ has determinant $1$, and $u$ is a free coordinate. This file equips $T$ with an $\mathfrak{sl}_2$-triple of derivations, a predicate for derivations that shift the fiber weight by a fixed amount, and an auxiliary $\mathbb{Z}$-grading.
--
--   1. **The two unipotent derivations.** The polynomial derivations $a\,\partial_b+d\,\partial_c$ and $b\,\partial_a+c\,\partial_d$ of $\mathbb{C}[a,d,b,c,u]$ both annihilate $ac-bd-1$, so they descend to $\mathbb{C}$-derivations $\delta$ and $\eta$ of $T$, determined by
--   $$\delta(a)=\delta(d)=\delta(u)=0,\quad \delta(b)=a,\quad \delta(c)=d,\qquad \eta(b)=\eta(c)=\eta(u)=0,\quad \eta(a)=b,\quad \eta(d)=c.$$
--   They are the infinitesimal generators of the column operations $M\mapsto M\begin{pmatrix}1&t\\0&1\end{pmatrix}$ and $M\mapsto M\begin{pmatrix}1&0\\t&1\end{pmatrix}$.
--
--   2. **The fiber Euler operator.** It is the commutator $\mathrm{Eu}=[\delta,\eta]=\delta\circ\eta-\eta\circ\delta$, a derivation of $T$ with
--   $$\mathrm{Eu}(a)=a,\quad \mathrm{Eu}(d)=d,\quad \mathrm{Eu}(b)=-b,\quad \mathrm{Eu}(c)=-c,\quad \mathrm{Eu}(u)=0 .$$
--   Hence $\mathrm{Eu}$ multiplies the class of a monomial $a^{i}d^{j}b^{k}c^{l}u^{m}$ by its fiber weight $i+j-k-l$, the weight for the right action of the diagonal torus $\operatorname{diag}(\lambda,\lambda^{-1})$ on $M$.
--
--   3. **Fixed fiber shift.** A $\mathbb{C}$-derivation $E$ of $T$ has fiber shift $e\in\mathbb{Z}$ if
--   $$\mathrm{Eu}\bigl(E(r)\bigr)-E\bigl(\mathrm{Eu}(r)\bigr)=e\,E(r)\qquad\text{for all } r\in T,$$
--   that is, $[\mathrm{Eu},E]=eE$: the derivation $E$ raises fiber weights by exactly $e$. For example, $\delta$ has fiber shift $2$ and $\eta$ has fiber shift $-2$.
--
--   4. **The auxiliary grading.** Give $a,d,b,c,u$ the auxiliary weights $0,3,-3,0,2$. The monomials $ac$, $bd$ and $1$ all have weight $0$, so $ac-bd-1$ is homogeneous and the ideal it generates is homogeneous. Writing $T_i$ for the image in $T$ of the span of the monomials of auxiliary weight $i$, one obtains a $\mathbb{Z}$-graded $\mathbb{C}$-algebra
--   $$T=\bigoplus_{i\in\mathbb{Z}}T_i ,$$
--   in which negative degrees occur.
--
--   These objects are the ingredients of the rigidity theorem for $T$, which excludes nonzero locally nilpotent derivations $E$ of $T$ having a fixed fiber shift $e\le0$ and satisfying $E^2(v)=0$, where $v=a^3b-a^2u^3-d^2$. The auxiliary grading separates the two parts of $v$ (both summands of $d^2+a^2u^3$ have auxiliary degree $6$, while $a^3b$ has degree $-3$) and lets one pass to the highest homogeneous component of $E$; the triple $\delta,\eta,\mathrm{Eu}$ is the $\mathfrak{sl}_2$-structure used to rule out the remaining derivations of negative fiber weight.
--
--   **Formalization Note** `T` is `MvPolynomial (Fin 5) ℂ ⧸ Ideal.span {relation}` with `relation = X 0 * X 3 - X 2 * X 1 - 1`; the generators `a, d, b, c, u` are the images of `X 0, X 1, X 2, X 3, X 4` (they are defined in the companion determinant module). The derivations `δ` and `η` are obtained with `QuotientDerivation.derivation` from `δP = mkDerivation ℂ ![0,0,X 0,X 1,0]` and `ηP = mkDerivation ℂ ![X 2,X 3,0,0,0]` after the checks `δP_relation` and `ηP_relation`; `Euler` is the Lie bracket `⁅δ,η⁆`, and the simp lemmas `δ_a`, …, `Euler_u` record the values on generators. The fiber-shift predicate is `FiberShift E e`, with `e` cast to ℂ. The grading is `aux = QuotientGrading.pieces auxPoly π` with `auxPoly = weightedHomogeneousSubmodule ℂ auxWeight`, `auxWeight = ![0,3,-3,0,2]`, homogeneity of the kernel `aux_ker`, and the instance `auxGrading`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/DeterminantRigidity.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/DeterminantRigidity.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.Determinant
open MvPolynomial

def δP : Derivation ℂ Poly Poly := MvPolynomial.mkDerivation ℂ ![0,0,X 0,X 1,0]
def ηP : Derivation ℂ Poly Poly := MvPolynomial.mkDerivation ℂ ![X 2,X 3,0,0,0]

lemma δP_relation : δP relation = 0 := by
  simp [δP, relation, Derivation.leibniz, smul_eq_mul]
  ring
lemma ηP_relation : ηP relation = 0 := by
  simp [ηP, relation, Derivation.leibniz, smul_eq_mul]
  ring

def δ : Derivation ℂ T T := QuotientDerivation.derivation _ δP
  (QuotientDerivation.span_singleton_stable δP (by rw [δP_relation]; exact Ideal.zero_mem _))
def η : Derivation ℂ T T := QuotientDerivation.derivation _ ηP
  (QuotientDerivation.span_singleton_stable ηP (by rw [ηP_relation]; exact Ideal.zero_mem _))
def Euler : Derivation ℂ T T := ⁅δ,η⁆

@[simp] lemma δ_π (r : Poly) : δ (π r) = π (δP r) := rfl
@[simp] lemma η_π (r : Poly) : η (π r) = π (ηP r) := rfl
@[simp] lemma δ_a : δ a = 0 := by simp [a, δP]
@[simp] lemma δ_d : δ d = 0 := by simp [d, δP]
@[simp] lemma δ_b : δ b = a := by simp [a, b, δP]
@[simp] lemma δ_c : δ c = d := by simp [d, c, δP]
@[simp] lemma δ_u : δ u = 0 := by simp [u, δP]
@[simp] lemma η_a : η a = b := by simp [a, b, ηP]
@[simp] lemma η_d : η d = c := by simp [d, c, ηP]
@[simp] lemma η_b : η b = 0 := by simp [b, ηP]
@[simp] lemma η_c : η c = 0 := by simp [c, ηP]
@[simp] lemma η_u : η u = 0 := by simp [u, ηP]
@[simp] lemma Euler_a : Euler a = a := by simp [Euler, Derivation.commutator_apply]
@[simp] lemma Euler_d : Euler d = d := by simp [Euler, Derivation.commutator_apply]
@[simp] lemma Euler_b : Euler b = -b := by simp [Euler, Derivation.commutator_apply]
@[simp] lemma Euler_c : Euler c = -c := by simp [Euler, Derivation.commutator_apply]
@[simp] lemma Euler_u : Euler u = 0 := by simp [Euler, Derivation.commutator_apply]

/-- Exact infinitesimal formulation of a fixed fiber-weight shift. -/
def FiberShift (E : Derivation ℂ T T) (e : ℤ) : Prop :=
  ∀ r, Euler (E r) - E (Euler r) = (e : ℂ) • E r

end ComplexCancellation.Determinant

namespace ComplexCancellation.Determinant
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

def auxWeight : Fin 5 → ℤ := ![0,3,-3,0,2]
abbrev auxPoly : ℤ → Submodule ℂ Poly := weightedHomogeneousSubmodule ℂ auxWeight
abbrev aux : ℤ → Submodule ℂ T := QuotientGrading.pieces auxPoly π

lemma relation_aux : relation ∈ auxPoly 0 := by
  have h1 := (isWeightedHomogeneous_X (R := ℂ) auxWeight 0).mul
    (isWeightedHomogeneous_X (R := ℂ) auxWeight 3)
  have h2 := (isWeightedHomogeneous_X (R := ℂ) auxWeight 2).mul
    (isWeightedHomogeneous_X (R := ℂ) auxWeight 1)
  have h1' : IsWeightedHomogeneous auxWeight (X 0 * X 3 : Poly) 0 := by
    simpa [auxWeight] using h1
  have h2' : IsWeightedHomogeneous auxWeight (X 2 * X 1 : Poly) 0 := by
    simpa [auxWeight] using h2
  exact (h1'.sub h2').sub (isWeightedHomogeneous_one ℂ auxWeight)

lemma aux_ker : (RingHom.ker π).IsHomogeneous auxPoly := by
  change (RingHom.ker (Ideal.Quotient.mk (Ideal.span {relation}))).IsHomogeneous _
  rw [Ideal.mk_ker]
  apply Ideal.homogeneous_span
  intro r hr
  have hr' : r = relation := Set.mem_singleton_iff.mp hr
  subst r
  exact ⟨0, relation_aux⟩

instance auxGrading : GradedAlgebra aux :=
  QuotientGrading.grading auxPoly π (Ideal.Quotient.mkₐ_surjective _ _) aux_ker

end ComplexCancellation.Determinant

end

end OAI


