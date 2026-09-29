-- Prove2me | Definitions.Def_AutomorphicForm_SlabProfile
-- name    : AutomorphicForm_SlabProfile
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/28b8fe2a-57b1-543c-ae72-eca3233ad325
-- title:
--   Slab profiles and pseudo-Eisenstein series on adelic GL(2)
-- statement:
--   Throughout, $F$ is a number field, $G = \mathrm{GL}_2(\mathbb{A}_F)$ is `AdelicGL2 (𝓞 F) F`, $Z$ is a subgroup of the idele group $\mathbb{A}_F^\times$ and $\xi \colon Z \to \mathbb{C}^\times$ a group homomorphism.
--
--   The structure `IsSlabProfile F Z ξ φ` is a six-field predicate on a function $\varphi \colon G \to \mathbb{C}$: (i) `measurable`, $\varphi$ is measurable; (ii) `unipotent_mul`, $\varphi(n(x)g) = \varphi(g)$ for every adele $x$ and every $g$, where $n(x) =$ `unipotentGL2 x` is the unipotent element of $\mathrm{GL}_2$ whose matrix has both diagonal entries $1$ and lower-left entry $0$; (iii) `borel_mul`, $\varphi(\gamma g) = \varphi(g)$ for every $\gamma$ in `borelSubgroup F`, that is, every $\gamma \in \mathrm{GL}_2(F)$ whose $(1,0)$ entry vanishes, embedded in $G$ by applying $F \to \mathbb{A}_F$ entrywise; (iv) `central_transform`, $\varphi(\mathrm{diag}(z,z)\,g) = \xi(z)\varphi(g)$ for $z \in Z$, the scalar matrix being `centralScalar`; (v) `bounded_on_slab`, for all reals $d_1, d_2$ with $0 < d_1$ there is a $C$ with $\lVert\varphi(g)\rVert \le C$ whenever the idele norm of $\det g$ — the value of Mathlib's module-scaling character `distribHaarChar` of $\mathbb{A}_F$, read as a real number — lies in $[d_1,d_2]$; (vi) `height_band`, there are reals $a,b$ with $0<a$ such that $\varphi(g) \neq 0$ forces `adelicHeight F g` $\in [a,b]$, where the adelic height is the product of the archimedean height `archHeight` of the infinite component and the finite product over the finite places $v$ of $\lVert\det g_v\rVert / \max(\lVert (g_v)_{10}\rVert, \lVert (g_v)_{11}\rVert)^2$.
--
--   For an arbitrary $\varphi \colon G \to \mathbb{C}$, `pseudoEisenstein F φ` is the function $g \mapsto \varphi(g) + \sum_{\beta \in F} \varphi\bigl(w\,n(\beta)\,g\bigr)$, with $w =$ `adelicWeyl (𝓞 F) F` the image in $G$ of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$; the sum is an unconditional `tsum` over $F$, hence $0$ at points where the family fails to be summable. Three small lemmas accompany these: `pseudoEisenstein_apply` restates the definition, `isSlabProfile_zero` records that the zero function is a slab profile for every $Z$ and $\xi$ (with height band $[1,1]$, vacuously satisfied), and `pseudoEisenstein_zero` that the construction sends the zero function to the zero function.
--
--   **Relation to Mathlib.** Mathlib has no notion of automorphic forms or Eisenstein series on adelic $\mathrm{GL}_2$; `IsSlabProfile` and `pseudoEisenstein` are the project's own. They are phrased using Mathlib's adele ring, `Matrix.GeneralLinearGroup` and (through `ideleNorm`) the module-scaling character `distribHaarChar`.
--
--   **Where it is used.** The module belongs to the project's adelic $\mathrm{GL}_2$ layer: `IsSlabProfile` packages the invariance, central transformation, slabwise boundedness and height-support conditions on a function on $\mathrm{GL}_2(\mathbb{A}_F)$ which is invariant under the rational Borel subgroup, and `pseudoEisenstein` adds to such a function the sum over the second Bruhat cell. It is imported throughout the automorphic side of the formalisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_SlabProfile.lean

import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField
open NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

structure IsSlabProfile (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop where
  measurable : Measurable φ
  unipotent_mul : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
    φ (unipotentGL2 x * g) = φ g
  borel_mul : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
    φ (globalPoints (𝓞 F) F γ * g) = φ g
  central_transform : ∀ (z : Z) (g : AdelicGL2 (𝓞 F) F),
    φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g
  bounded_on_slab : ∀ d₁ d₂ : ℝ, 0 < d₁ → ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂ →
      ‖φ g‖ ≤ C
  height_band : ∃ a b : ℝ, 0 < a ∧ ∀ g : AdelicGL2 (𝓞 F) F,
    φ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b

def pseudoEisenstein (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => φ g + ∑' β : F, φ (adelicWeyl (𝓞 F) F
    * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)

variable {F}

theorem pseudoEisenstein_apply (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    pseudoEisenstein F φ g = φ g + ∑' β : F, φ (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) :=
  rfl

theorem isSlabProfile_zero (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) :
    IsSlabProfile F Z ξ (fun _ => (0 : ℂ)) where
  measurable := measurable_const
  unipotent_mul := fun _ _ => rfl
  borel_mul := fun _ _ _ => rfl
  central_transform := fun _ _ => by simp
  bounded_on_slab := fun _ _ _ => ⟨0, fun _ _ => by simp⟩
  height_band := ⟨1, 1, one_pos, fun _ h => absurd rfl h⟩

theorem pseudoEisenstein_zero :
    pseudoEisenstein F (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  funext g
  simp [pseudoEisenstein]

end AutomorphicForm

end


