-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesIhomSectionsV2
-- name    : AlgebraicGeometry_ModulesIhomSectionsV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/086b2fab-d3d8-5f75-806f-46d2c9edcd38
-- title:
--   Context for sections of internal Homs of module sheaves
-- statement:
--   This module opens no new declarations: it fixes the standing context in which sections of internal Homs of sheaves of modules are discussed, and makes the relevant imported notions available. The context consists of a site, namely a category $C$ with a Grothendieck topology $J$ together with a presheaf of commutative rings $\mathcal{O}$ on $C$ and the hypothesis that $\mathcal{O}$, viewed in $\mathrm{RingCat}$, is a sheaf for $J$; sheaves of modules $M$, $N$, $P$ over the associated sheaf of rings; and, on the geometric side, a scheme $X$ with an open $U \subseteq X$, objects $M$, $N$, $P$ of $X.\mathrm{Modules}$, and an open immersion $f \colon X \to Y$ of schemes.
--
--   The mathematics it presupposes comes from the imported definitions. For presheaves of modules $F$, $N$ over $R$, the internal Hom is built from the $R(X)$-module `naturalFamilies F N X` of families $(\varphi_f \colon F(Y) \to N(Y))_{f \colon X \to Y}$ of $R(Y)$-linear maps subject to the compatibility $N(g)(\varphi_f x) = \varphi_{f \circ g}(F(g)x)$, with scalar action $(r \cdot \varphi)_f = R(f)(r)\,\varphi_f$; these form a presheaf of modules `ihomObj F N`, functorial in $N$, right adjoint to tensoring with $F$ by way of the explicit curry and uncurry maps, whence a monoidal closed structure on presheaves of modules. Sheaves of modules over a ringed site, and in particular $\mathcal{O}_X$-modules on a scheme, inherit symmetric monoidal and monoidal closed structures by localising this structure along sheafification; the imported section-level material supplies tensor products of sections, unit sections, tensor powers and the predicate that a section is a local frame.
--
--   **Relation to Mathlib.** The internal Hom of presheaves of modules, the tensor–Hom adjunction realising it, and the resulting monoidal closed structures on presheaves and sheaves of modules (and on $\mathcal{O}_X$-modules for a scheme) are supplied by the imported project definitions on top of Mathlib's `PresheafOfModules`, `SheafOfModules` and sheafification machinery.
--
--   **Where it is used.** The material sits in the scheme-theoretic layer of the formalisation, where internal Homs of $\mathcal{O}_X$-modules and their sections are used to describe duals of invertible sheaves and the tensor–Hom adjunction at the level of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesIhomSectionsV2.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v' u'

open CategoryTheory MonoidalCategory Limits Opposite
open scoped TensorProduct

noncomputable section

namespace PresheafOfModules

namespace InternalHom

namespace IsSheafAux

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F N : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

variable {F N}

end IsSheafAux

end InternalHom

end PresheafOfModules

end

noncomputable section

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {G N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}

end PresheafOfModules

end

namespace CategoryTheory.MonoidalClosed

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C] [MonoidalClosed C]

end CategoryTheory.MonoidalClosed

noncomputable section

namespace SheafOfModules

open PresheafOfModules PresheafOfModules.InternalHom Functor.Monoidal Functor.LaxMonoidal
  Functor.OplaxMonoidal

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

section unit

variable {𝒪 h𝒪}

end unit

variable (M N : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪))

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {M N}

variable (M N)

variable {M N}

variable (M) (P : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪))

variable {M P}

end SheafOfModules

end

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace

variable {X : Scheme.{u}}

section restrict

set_option maxHeartbeats 400000

variable (U : X.Opens)

variable (M N : X.Modules)

variable {U M N}

variable (U M N)

end restrict

variable (M N : X.Modules)

variable {M N} {P : X.Modules}

variable (M N)

variable {M N}

variable (M N)

variable {M N}

section restrictUnit

variable {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

end restrictUnit

end AlgebraicGeometry.Scheme.Modules

end


