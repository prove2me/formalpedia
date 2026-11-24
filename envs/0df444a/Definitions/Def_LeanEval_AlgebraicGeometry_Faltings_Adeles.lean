-- Prove2me | Definitions.Def_LeanEval_AlgebraicGeometry_Faltings_Adeles
-- name    : LeanEval_AlgebraicGeometry_Faltings_Adeles
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T01:47:32.556826+00:00
-- url     : https://prove2.me/theorems/2f0767c2-8e93-490c-b9cb-35b5a945c243
-- title:
--   LeanEval function fields: adele ring, principal and integral adeles, adelic genus
-- statement:
--   The adele ring of an algebraic function field of one variable, its principal and integral adeles, and the adelic genus, following Stichtenoth, *Algebraic Function Fields and Codes*, Definitions 1.5.1, 1.5.2 and 1.5.3 and Corollary 1.5.5.
--
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $\operatorname{Place}(F/K)$ be the places of $F/K$: the proper $K$-subalgebras $\mathcal O_v \subseteq F$ that are valuation subrings.
--
--   The **adele ring** is the restricted product
--
--   $$\mathcal A_F \;=\; \Big\{ (a_v)_v \in \prod_{v} F \;:\; a_v \in \mathcal O_v \text{ for all but finitely many } v \Big\},$$
--
--   taken with respect to the cofinite filter. It is a commutative ring under componentwise operations and a $K$-algebra through the constant families indexed by $K$.
--
--   The **principal adeles** are the constant families,
--
--   $$P_F \;=\; \{\, a \in \mathcal A_F \;:\; a_v = a_w \text{ for all places } v, w \,\},$$
--
--   a $K$-subspace of $\mathcal A_F$. The **integral adeles** are the $K$-subspace $\mathcal A_F(0) = \{ a \in \mathcal A_F : a_v \in \mathcal O_v \text{ for every } v \}$. The **genus** is the natural number
--
--   $$g(F/K) \;=\; \dim_K \frac{\mathcal A_F}{\mathcal A_F(0) + P_F},$$
--
--   which is finite for every algebraic function field of one variable and agrees with the genus of the smooth projective curve with function field $F$. It is the quantity whose size governs the arithmetic of the curve, and the hypothesis of Faltings' theorem in this development.
--
--   When $F/K$ is a function field, each $x \in F$ has only finitely many poles, so the constant family $(x)_v$ is an adele and $x \mapsto (x)_v$ is a $K$-algebra homomorphism $F \to \mathcal A_F$ whose image is exactly $P_F$. That statement is the mission's theorem `Adele.exists_algHom_range_eq_principal`; it is what identifies the subspace $P_F$ used here with the image of the diagonal used in the benchmark declaration.
--
--   **Formalization Note.** The place type comes from `LeanEval_AlgebraicGeometry_Faltings_Places`. The principal adeles are presented as the constant-family submodule, exactly as in the proved library (`Faltings.Adele.principal`, `Mordell/FunctionField/Adele/Basic.lean`), rather than as the range of the diagonal ring homomorphism used by the benchmark. The two presentations define the same subspace, and the source file itself proves the resulting genera equal (`Faltings.LeanEval.genus_eq`). This presentation is required because a platform definition may import only theorems that are already Proved, whereas the diagonal is defined by the finiteness of poles, which is an Open target. The definitions are sorry-free and import no theorem. Two further adaptations are forced by the pinned Mathlib (`0df444a`, Lean v4.33.1), where the named restricted-product instances do not exist and `Algebra` does not extend `Module`: the `CommRing` and `Module K` structures are obtained by `inferInstanceAs` through the same restricted product presented over the underlying $K$-subalgebras (a definitionally equal type), and the constant-field algebra supplies `smul` from that module. The types of `Adele`, `integralAdele` and `genus` are unchanged.
-- source:
--   LeanEval benchmark problem `faltings`, adele/genus layer (lines 68–120), https://github.com/leanprover/lean-eval/blob/bcc142463a0530038f12e8f1c1e9cce78e129f0a/LeanEval/AlgebraicGeometry/Faltings.lean#L68-L120 ; principal adeles as constant families and the genus as in the proved library: AxiomMath/Mordell, `Mordell/FunctionField/Adele/Basic.lean` and `Mordell/FunctionField/Genus.lean`, https://github.com/AxiomMath/Mordell/blob/82a30cb7857f6e3cfdb1be91f5533c0ccb57d493/Mordell/FunctionField/Adele/Basic.lean ; equality with the benchmark's diagonal presentation: `Mordell/LeanEval/Faltings.lean` lines 245–278 (`map_integralAdele`, `map_range_toAlgHom`, `genus_eq`), https://github.com/AxiomMath/Mordell/blob/82a30cb7857f6e3cfdb1be91f5533c0ccb57d493/Mordell/LeanEval/Faltings.lean#L245-L278 . Mathematical source: H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., Springer GTM 254, 2009, Definitions 1.5.1–1.5.3, Corollary 1.5.5, https://doi.org/10.1007/978-3-540-77086-4 .

import Mathlib
import Definitions.Def_LeanEval_AlgebraicGeometry_Faltings_Places

namespace LeanEval
namespace AlgebraicGeometry
namespace Faltings

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

open scoped RestrictedProduct

/-- [Stichtenoth, Definition 1.5.2]. -/
abbrev Adele : Type _ := RestrictedProduct (fun _ ↦ F) (fun v : Place K F ↦ v) Filter.cofinite

private abbrev AdeleSubalgebra : Type _ :=
  RestrictedProduct (fun _ ↦ F) (fun v : Place K F ↦ (v.toSubalgebra : Set F)) Filter.cofinite

instance Adele.instCommRing : CommRing (Adele K F) :=
  inferInstanceAs (CommRing (AdeleSubalgebra K F))

instance Adele.instModuleConstants : Module K (Adele K F) :=
  inferInstanceAs (Module K (AdeleSubalgebra K F))

open RestrictedProduct

/-- The principal adeles `P_F`: the `K`-subspace of constant families
[Stichtenoth, Definition 1.5.1]. -/
def Adele.principal : Submodule K (Adele K F) where
  carrier := {α | ∀ v w : Place K F, α v = α w}
  add_mem' {a b} ha hb v w := by
    show a v + b v = a w + b w
    rw [ha v w, hb v w]
  zero_mem' v w := rfl
  smul_mem' c {a} ha v w := by
    show c • a v = c • a w
    rw [ha v w]

instance Adele.instAlgebraConstants : Algebra K (Adele K F) where
  smul := (inferInstance : SMul K (Adele K F)).smul
  algebraMap.toFun x := ⟨fun _ ↦ algebraMap K F x, .of_forall fun _ ↦ algebraMap_mem ..⟩
  algebraMap.map_one' := by ext; exact (algebraMap K F).map_one
  algebraMap.map_mul' _ _ := by ext; exact (algebraMap K F).map_mul ..
  algebraMap.map_add' _ _ := by ext; exact (algebraMap K F).map_add ..
  algebraMap.map_zero' := by ext; exact (algebraMap K F).map_zero
  commutes' _ _ := mul_comm ..
  smul_def' _ _ := by ext; apply Algebra.smul_def

/-- The $K$-subspace $\mathcal{A}_F(0)$, see [Stichtenoth, Definition 1.5.3]. -/
def integralAdele : Submodule K (Adele K F) where
  carrier := {x | ∀ v, x v ∈ v}
  add_mem' h₁ h₂ v := add_mem (h₁ v) (h₂ v)
  zero_mem' _ := zero_mem _
  smul_mem' _ _ h v := v.smul_mem (h v) _

/-- The genus of a function field, [Stichtenoth, Corollary 1.5.5]. -/
noncomputable def genus [BundledFunctionField K F] : ℕ :=
  Module.finrank K (Adele K F ⧸ integralAdele K F ⊔ Adele.principal K F)

end Faltings
end AlgebraicGeometry
end LeanEval


