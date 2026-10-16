-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
-- name    : OAI_RepresentationTheory_FoulkesHowe_Multiplication
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:42:40.134306+00:00
-- url     : https://prove2.me/theorems/21b19bc1-35a4-4bff-89c4-7cbf85bc30b7
-- title:
--   Graded multiplication between symmetric powers
-- statement:
--   Let $V$ be a complex vector space and $S(V)$ its symmetric algebra over $\mathbb{C}$, the free commutative $\mathbb{C}$-algebra on $V$. For $n\in\mathbb{N}$ let $\mathrm{Sym}^nV\subseteq S(V)$ be the $\mathbb{C}$-span of all products $u_0\cdots u_{n-1}$ of $n$ vectors of $V$, and write $[u_0,\dots,u_{n-1}]$ for such a product viewed in $\mathrm{Sym}^nV$. For $v=(v_0,\dots,v_{m-1})$ and $w=(w_0,\dots,w_{n-1})$ write $v\Vert w=(v_0,\dots,v_{m-1},w_0,\dots,w_{n-1})$ for the concatenated tuple.
--
--   The module establishes and defines:
--
--   1. **Concatenation.** In $S(V)$ the product of the concatenated list is the product of the two partial products: $\prod(v\Vert w)=(v_0\cdots v_{m-1})(w_0\cdots w_{n-1})$.
--   2. **Products of homogeneous spans.** As submodules of $S(V)$,
--   $$
--   \mathrm{Sym}^mV\cdot\mathrm{Sym}^nV=\mathrm{Sym}^{m+n}V,
--   $$
--   where the left side is the span of all products $xy$ with $x\in\mathrm{Sym}^mV$ and $y\in\mathrm{Sym}^nV$. In particular $xy\in\mathrm{Sym}^{m+n}V$ for all such $x,y$.
--   3. **Graded multiplication.** The $\mathbb{C}$-bilinear map
--   $$
--   \mathrm{Sym}^mV\times\mathrm{Sym}^nV\to\mathrm{Sym}^{m+n}V,\qquad (x,y)\mapsto xy,
--   $$
--   with the product computed in $S(V)$. On monomials it is concatenation: $[v]\cdot[w]=[v\Vert w]$.
--   4. **Degree transport.** For $m=n$, the identity of $S(V)$ regarded as a linear isomorphism $\mathrm{Sym}^mV\cong\mathrm{Sym}^nV$; it sends $[v_0,\dots,v_{m-1}]$ to the same product with its indices reread in $\{0,\dots,n-1\}$.
--   5. **Multiplication into a prescribed degree.** For $m+n=d$, the bilinear map $\mathrm{Sym}^mV\times\mathrm{Sym}^nV\to\mathrm{Sym}^dV$ obtained by composing the graded multiplication with the degree transport; as an element of $S(V)$ its value at $(x,y)$ is again $xy$.
--
--   Graded multiplication is used to form elements such as $x^r\cdot Q\in\mathrm{Sym}^{r+m}V$, with $x^r=[x,\dots,x]\in\mathrm{Sym}^rV$ and $Q\in\mathrm{Sym}^mV$, which relate forms on $\mathrm{Sym}^{r+m}V$ to forms on the lower symmetric power $\mathrm{Sym}^mV$.
--
--   **Formalization Note** The degree of a symmetric power is part of its type, so an equality of degrees $m=n$ has to be transported explicitly; this is the purpose of `symPowCast` and `symPowMulCast`. The multiplication itself is `symPowMul m n`, and `symPowMul_symMonomial` records its action on monomials via `Fin.append`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/Multiplication.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/Multiplication.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap

namespace OAI

noncomputable section
open scoped BigOperators Pointwise
universe u

namespace Problem346

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Concatenating two lists of factors multiplies their symmetric monomials. -/
theorem symMonomialRaw_append (m n : ℕ) (v : Fin m → V) (w : Fin n → V) :
    symMonomialRaw (m + n) V (Fin.append v w) =
      symMonomialRaw m V v * symMonomialRaw n V w := by
  simp [symMonomialRaw, Fin.prod_univ_add]

/-- Products of homogeneous spans have the sum of their degrees. -/
theorem symPowSubmodule_mul (m n : ℕ) :
    symPowSubmodule m V * symPowSubmodule n V = symPowSubmodule (m + n) V := by
  unfold symPowSubmodule
  rw [Submodule.span_mul_span]
  apply congrArg (Submodule.span ℂ)
  ext z
  constructor
  · rintro ⟨x, ⟨v, rfl⟩, y, ⟨w, rfl⟩, rfl⟩
    exact ⟨Fin.append v w, symMonomialRaw_append m n v w⟩
  · rintro ⟨v, rfl⟩
    refine ⟨symMonomialRaw m V (fun i => v (Fin.castAdd n i)),
      ⟨_, rfl⟩, symMonomialRaw n V (fun i => v (Fin.natAdd m i)), ⟨_, rfl⟩, ?_⟩
    simp [symMonomialRaw, Fin.prod_univ_add]

/-- The product of two elements of the indicated homogeneous pieces. -/
theorem symPow_mul_mem (m n : ℕ) (x : SymPow m V) (y : SymPow n V) :
    (x : SymmetricAlgebra ℂ V) * (y : SymmetricAlgebra ℂ V) ∈
      symPowSubmodule (m+n) V := by
  rw [← symPowSubmodule_mul]
  exact Submodule.mul_mem_mul x.property y.property

/-- Graded multiplication in the symmetric algebra, as a bilinear map. -/
def symPowMul (m n : ℕ) :
    SymPow m V →ₗ[ℂ] SymPow n V →ₗ[ℂ] SymPow (m+n) V :=
  LinearMap.mk₂ ℂ
    (fun x y => ⟨(x : SymmetricAlgebra ℂ V) * (y : SymmetricAlgebra ℂ V),
      symPow_mul_mem m n x y⟩)
    (by intros; apply Subtype.ext; exact add_mul _ _ _)
    (by intros; apply Subtype.ext; exact smul_mul_assoc _ _ _)
    (by intros; apply Subtype.ext; exact mul_add _ _ _)
    (by intros; apply Subtype.ext; exact mul_smul_comm _ _ _)

@[simp] theorem symPowMul_coe (m n : ℕ) (x : SymPow m V) (y : SymPow n V) :
    (symPowMul m n x y : SymmetricAlgebra ℂ V) =
      (x : SymmetricAlgebra ℂ V) * (y : SymmetricAlgebra ℂ V) := rfl

@[simp] theorem symPowMul_symMonomial (m n : ℕ) (v : Fin m → V) (w : Fin n → V) :
    symPowMul m n (symMonomial m V v) (symMonomial n V w) =
      symMonomial (m+n) V (Fin.append v w) := by
  apply Subtype.ext
  exact (symMonomialRaw_append m n v w).symm

/-- Transport a homogeneous element across an equality of degrees. -/
def symPowCast {m n : ℕ} (h : m = n) : SymPow m V ≃ₗ[ℂ] SymPow n V :=
  LinearEquiv.ofEq _ _ (congrArg (fun k => symPowSubmodule k V) h)

@[simp] theorem symPowCast_coe {m n : ℕ} (h : m = n) (x : SymPow m V) :
    (symPowCast h x : SymmetricAlgebra ℂ V) = x := rfl

@[simp] theorem symPowCast_symMonomial {m n : ℕ} (h : m = n) (v : Fin m → V) :
    symPowCast h (symMonomial m V v) =
      symMonomial n V (fun i => v (Fin.cast h.symm i)) := by
  subst h
  rfl

/-- Multiplication followed by transport to a specified total degree. -/
def symPowMulCast (m n b : ℕ) (h : m+n=b) :
    SymPow m V →ₗ[ℂ] SymPow n V →ₗ[ℂ] SymPow b V :=
  (LinearMap.llcomp ℂ (SymPow n V) (SymPow (m+n) V) (SymPow b V)
    (symPowCast h).toLinearMap).comp (symPowMul m n)

@[simp] theorem symPowMulCast_coe (m n b : ℕ) (h : m+n=b)
    (x : SymPow m V) (y : SymPow n V) :
    (symPowMulCast m n b h x y : SymmetricAlgebra ℂ V) =
      (x : SymmetricAlgebra ℂ V) * (y : SymmetricAlgebra ℂ V) := rfl

end Problem346

end

end OAI


