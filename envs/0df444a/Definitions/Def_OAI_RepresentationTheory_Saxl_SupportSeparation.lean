-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
-- name    : OAI_RepresentationTheory_Saxl_SupportSeparation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:18:11.811909+00:00
-- url     : https://prove2.me/theorems/98fb0e35-b7f7-4afb-854a-12513d0654af
-- title:
--   Subrepresentations as group-algebra submodules and their inclusion intertwiners
-- statement:
--   Two identifications for invariant subspaces of a group representation.
--
--   Let $G$ be a group, $\rho$ a representation of $G$ on a complex vector space $V$, and $S\subseteq V$ a subrepresentation, i.e. a subspace with $\rho(g)S\subseteq S$ for all $g\in G$; write $\rho|_S$ for the restricted representation. Let $\mathbb{C}[G]$ be the group algebra; a representation makes its space a $\mathbb{C}[G]$-module through $\big(\sum_g c_g\,g\big)\cdot v=\sum_g c_g\,\rho(g)v$.
--
--   1. **Subrepresentation versus submodule.** $S$ is a $\mathbb{C}[G]$-module in two ways: through its own representation $\rho|_S$, and as the $\mathbb{C}[G]$-submodule of $V$ formed by the vectors of $S$. The identity on vectors,
--   $$
--   \Psi_S:\big(S,\rho|_S\big)\longrightarrow\big(S\subseteq V\big),\qquad \Psi_S(x)=x,
--   $$
--   is a $\mathbb{C}[G]$-linear isomorphism between these two modules.
--
--   2. **Inclusion intertwiner.** The inclusion $S\hookrightarrow V$, as a $G$-equivariant linear map from $\rho|_S$ to $\rho$.
--
--   These identifications let module-theoretic facts about semisimple $\mathbb{C}[G]$-modules, such as the equivalence between containment of simple constituents and separation by homomorphisms, be applied to invariant subspaces of representations, and let maps into a cyclic subrepresentation be composed back into the ambient space.
--
--   **Formalization Note** `subrepModuleEquiv S` is a linear equivalence over `MonoidAlgebra ℂ G` between `S.toRepresentation.asModule` and `S.asSubmodule`; it is the identity on underlying vectors, and only its compatibility with scalars from the group algebra requires an argument. `subrepInclusion S` is the subtype map packaged as a `Representation.IntertwiningMap`. The group $G$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/SupportSeparation.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/SupportSeparation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification

namespace OAI

noncomputable section

open scoped TensorProduct

universe uR uX uY uG uV

namespace Saxl
open scoped MonoidAlgebra

/- In a semisimple module, support containment is equivalent to separation
by homomorphisms (multiplicities are immaterial for the band step). -/
end Saxl

namespace Saxl
open scoped MonoidAlgebra

/- The invariant-subspace and group-algebra subtype constructions agree. -/
def subrepModuleEquiv {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    S.toRepresentation.asModule ≃ₗ[ℂ[G]] S.asSubmodule where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change (⟨(a • x).val, _⟩ : S.asSubmodule) = a • ⟨x.val, x.property⟩
    apply Subtype.ext
    change (a • x).val = ρ.asModuleEquiv (a • ρ.asModuleEquiv.symm x.val)
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp only [zero_smul, map_zero]; rfl
    | add a b ha hb =>
      simp only [add_smul, map_add]
      change (a • x).val + (b • x).val = _
      rw [ha, hb]
    | single g c =>
      rw [Representation.single_smul, Representation.single_smul]
      rfl

end Saxl

namespace Saxl
open scoped MonoidAlgebra

end Saxl

namespace Saxl
open scoped MonoidAlgebra

end Saxl

namespace Saxl

def subrepInclusion {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    Representation.IntertwiningMap S.toRepresentation ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

/- All constituents needed from a d-letter permutation module are detected
by a module containing each Specht type of height at most d. -/
end Saxl

end

end OAI


