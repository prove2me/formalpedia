-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
-- name    : OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:34:27.432168+00:00
-- url     : https://prove2.me/theorems/9a6a4e6f-5dd2-466d-8208-470971283e9e
-- title:
--   Transposing a linear map along perfect pairings
-- statement:
--   Let $R$ be a commutative semiring and $E,F,E',F'$ modules over $R$. For an $R$-module $M$ write $M^*=\mathrm{Hom}_R(M,R)$ for its dual. A linear isomorphism $e:E\to(E')^*$ is the same thing as a perfect pairing $E\times E'\to R$, $(x,y)\mapsto e(x)(y)$.
--
--   1. **Reversing a pairing.** Suppose that $E$ is reflexive, i.e. the canonical evaluation map $E\to E^{**}$ is bijective, and let $e:E'\to E^*$ be a linear isomorphism. Then there is a linear isomorphism $e^{\flat}:E\to(E')^*$ given by
--   $$e^{\flat}(x)(y)=e(y)(x)\qquad(x\in E,\ y\in E').$$
--   2. **Transpose.** Let $e:E\to(E')^*$ and $f:F\to(F')^*$ be linear isomorphisms and $\mu:E'\to F'$ a linear map. The transpose of $\mu$ along $e$ and $f$ is the linear map $\mu^{\top}=e^{-1}\circ\mu^*\circ f:F\to E$, where $\mu^*:(F')^*\to(E')^*$, $\psi\mapsto\psi\circ\mu$, is the dual map. It satisfies
--   $$e\bigl(\mu^{\top}(y)\bigr)(x)=f(y)\bigl(\mu(x)\bigr)\qquad\text{for all }y\in F,\ x\in E'.$$
--
--   Since $\mu^*$ is injective whenever $\mu$ is surjective, the transpose turns a surjective linear map $E'\to F'$ into an injective linear map $F\to E$ in the opposite direction. When the pairings are compatible with a group action and $\mu$ is an intertwiner, this gives an algebraic way to obtain an injective intertwiner without splitting representations by complete reducibility.
--
--   **Formalization Note** `flipPairing e` is the composite of `Module.evalEquiv` with the dual of `e` and requires `Module.IsReflexive R E`; `transpose e f μ` is `e.symm` composed with `μ.dualMap` and `f`, and `pairing_transpose` is the displayed identity. All modules are only assumed to be additive commutative monoids.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/DualEmbedding.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/DualEmbedding.lean by skeleton subtraction
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

namespace OAI

/-!
# Transposed embeddings

A surjective intertwiner yields an injective intertwiner in the opposite
 direction when both modules carry compatible perfect pairings.  This is an
 algebraic alternative to splitting a representation by complete reducibility.
-/

noncomputable section

namespace Problem346
namespace DualEmbedding

variable {R E F E' F' : Type*} [CommSemiring R]
  [AddCommMonoid E] [Module R E] [AddCommMonoid F] [Module R F]
  [AddCommMonoid E'] [Module R E'] [AddCommMonoid F'] [Module R F']

/-- Reverse a perfect pairing when the first module is reflexive.  This turns
    the usual chart `E' ≃ Dual E` into the orientation needed by `transpose`. -/
def flipPairing [Module.IsReflexive R E] (e : E' ≃ₗ[R] Module.Dual R E) :
    E ≃ₗ[R] Module.Dual R E' :=
  (Module.evalEquiv R E).trans e.dualMap

@[simp]
theorem flipPairing_apply [Module.IsReflexive R E]
    (e : E' ≃ₗ[R] Module.Dual R E) (x : E) (y : E') :
    flipPairing e x y = e y x := rfl

/-- Transport the dual of a linear map along two perfect pairings. -/
def transpose (e : E ≃ₗ[R] Module.Dual R E')
    (f : F ≃ₗ[R] Module.Dual R F') (μ : E' →ₗ[R] F') : F →ₗ[R] E :=
  e.symm.toLinearMap.comp (μ.dualMap.comp f.toLinearMap)

@[simp]
theorem pairing_transpose (e : E ≃ₗ[R] Module.Dual R E')
    (f : F ≃ₗ[R] Module.Dual R F') (μ : E' →ₗ[R] F') (y : F) (x : E') :
    e (transpose e f μ y) x = f y (μ x) := by
  simp [transpose]

end DualEmbedding
end Problem346

end

end OAI


