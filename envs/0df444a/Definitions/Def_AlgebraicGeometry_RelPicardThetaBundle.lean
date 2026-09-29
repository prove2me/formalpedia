-- Prove2me | Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
-- name    : AlgebraicGeometry_RelPicardThetaBundle
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/5cacc37f-17a5-5755-a218-6dd36f72b9e0
-- title:
--   Picard bundles and theta bundles of rigidified line bundles
-- statement:
--   Throughout, $R$ is a commutative ring, $c\colon C \to \operatorname{Spec} R$ a morphism of schemes, $\varepsilon$ a morphism over $\operatorname{Spec} R$ from $\operatorname{Spec} R$ to $C$ (a section of $c$), and $t\colon T \to \operatorname{Spec} R$ a further $R$-scheme; all objects below live on the fibre product $C \times_{\operatorname{Spec} R} T$, realised as `pullback c t`, or on $T$. The induced section $\varepsilon_T\colon T \to C\times_R T$ is `rigSection c t ε`, and `sectionIdeal` is its kernel ideal sheaf, i.e. the ideal sheaf data on $C\times_R T$ attached to $\varepsilon_T$. For $r \in \mathbb N$, `sectionTwist` is $\bigl(\mathcal I_{\varepsilon_T}^{\,r}\bigr)^{\vee}$: the $r$-th power of that ideal sheaf, viewed as a sheaf of modules (the kernel of the unit map to the pushforward of the unit along the closed immersion of the associated subscheme) and then dualised in the symmetric monoidal closed structure on sheaves of modules, the dual being the internal hom into the unit.
--
--   For a rigidified line bundle $M$ on $C\times_R T$ — a structure consisting of a module $M.L$, a witness that it is locally isomorphic to the unit sheaf, and the nonemptiness of an isomorphism between its pullback along $\varepsilon_T$ and the unit sheaf on $T$ — and an arbitrary module $N$ on $C\times_R T$, `picardBundle` is the pushforward of $M.L \otimes N$ along the projection $\operatorname{pr}_2 =$ `pullback.snd c t` to $T$; this is the plain (non-derived) pushforward, with no properness, flatness or base-change hypotheses imposed. For $r, n \in \mathbb N$, `thetaBundle` is the dual of the $n$-th exterior power of `picardBundle c ε t M (sectionTwist c ε t r)`, the exterior power being the sheafification of the sectionwise $n$-th exterior power; note that $n$ is an explicit parameter rather than a rank computed from the geometry. Finally, for a field $k$ and a point $s\colon \operatorname{Spec} k \to T$, the abbreviation `fibreModule` restricts a module on $C\times_R T$ to the fibre $(C\times_R T)\times_T \operatorname{Spec} k$ by pullback along the first projection. Two lemmas record the defining equations of `picardBundle` and `thetaBundle` for rewriting.
--
--   **Relation to Mathlib.** Mathlib provides `Scheme.IdealSheafData` together with pushforward and pullback of sheaves of modules; the symmetric monoidal closed structure on `X.Modules` (hence the tensor product and the dual used here), the sectionwise exterior power of presheaves of modules and its sheafification, and the notion of rigidified line bundle over a section are the project's own.
--
--   **Where it is used.** These are the vocabulary for the theta polarisation on relative Picard functors: the determinant of the Picard bundle of a degree-adjusted line bundle provides the ample bundle used in the construction and quasi-projectivity of relative Jacobians, which underlies the Néron model theory for elliptic curves employed in the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardThetaBundle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesDet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra MonoidalCategory

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

def sectionIdeal : (pullback c t).IdealSheafData := (rigSection c t ε).ker

def sectionTwist (r : ℕ) : (pullback c t).Modules := ((sectionIdeal c ε t) ^ r).invModule

def picardBundle (M : RigidifiedLineBundle c ε t) (N : (pullback c t).Modules) : T.Modules :=
  (Scheme.Modules.pushforward (pullback.snd c t)).obj (M.L ⊗ N)

def thetaBundle (M : RigidifiedLineBundle c ε t) (r n : ℕ) : T.Modules :=
  Scheme.Modules.dual (Scheme.Modules.det n (picardBundle c ε t M (sectionTwist c ε t r)))

abbrev fibreModule {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (F : (pullback c t).Modules) : (pullback (pullback.snd c t) s).Modules :=
  (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj F

@[simp] theorem picardBundle_def (M : RigidifiedLineBundle c ε t) (N : (pullback c t).Modules) :
    picardBundle c ε t M N = (Scheme.Modules.pushforward (pullback.snd c t)).obj (M.L ⊗ N) := rfl

@[simp] theorem thetaBundle_def (M : RigidifiedLineBundle c ε t) (r n : ℕ) :
    thetaBundle c ε t M r n = Scheme.Modules.dual (Scheme.Modules.det n (picardBundle c ε t M (sectionTwist c ε t r))) := rfl

end AlgebraicGeometry.RelPicard

end


