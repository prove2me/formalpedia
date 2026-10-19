-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
-- name    : OAI_GroupTheory_Hyperbolic_CyclicAction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:06:06.008454+00:00
-- url     : https://prove2.me/theorems/b9805c3c-3757-44ac-9bb8-6b95675d07b0
-- title:
--   Free chains as modules over a finite subgroup
-- statement:
--   Translation actions on free chains $\mathbb Z[A\times G]$ and their restriction to a finite subgroup $H\le G$.
--
--   1. **Translation.** Translation by $g$ satisfies $(g\cdot c)(a,x)=c(a,g^{-1}x)$, the identity acts trivially, and $(gh)\cdot c=g\cdot(h\cdot c)$.
--   2. **Right cosets.** Choosing representatives of the right cosets $Hx$ gives a bijection $G\cong H\backslash G\times H$, $x\mapsto(Hx,\ x\,\mathrm{rep}(Hx)^{-1})$. Hence free chains on $A\times G$ are identified with finitely supported functions from $A\times H\backslash G$ to the group ring $\mathbb Z[H]$. Under this identification translation by $h\in H$ becomes the left regular representation, and the norm map $c\mapsto\sum_{h\in H}h\cdot c$ becomes the norm of the regular representation.
--   3. **Augmentation.** The augmentation $\varepsilon(c)=\sum_{(a,x)}c(a,x)$ is translation-invariant and satisfies
--   $$
--   \varepsilon\Bigl(\sum_{h\in H}h\cdot c\Bigr)=|H|\,\varepsilon(c).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/CyclicAction.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/CyclicAction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains

namespace OAI

namespace Release075
namespace FreeChain
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A G : Type} [Group G]

@[simp] theorem shift_apply (g : G) (c : FreeChain A G) (a : A) (x : G) :
    chainShift g c (a,x) = c (a,g⁻¹*x) := by
  simp [chainShift,Finsupp.domLCongr_apply]

@[simp] theorem shift_one (c : FreeChain A G) : chainShift (1 : G) c = c := by
  ext ⟨a,x⟩; simp

@[simp] theorem shift_mul (g h : G) (c : FreeChain A G) :
    chainShift (g*h) c = chainShift g (chainShift h c) := by
  ext ⟨a,x⟩; simp [mul_assoc]

abbrev RightCosets (H : Subgroup G) := Quotient (QuotientGroup.rightRel H)

def coset (H : Subgroup G) (x : G) : RightCosets H := Quotient.mk _ x

noncomputable def cosetCoord (H : Subgroup G) (x : G) : H :=
  ⟨x * (coset H x).out⁻¹, QuotientGroup.rightRel_apply.mp
    (Quotient.exact (Quotient.out_eq (coset H x)))⟩

@[simp] theorem coset_mul (H : Subgroup G) (h : H) (x : G) :
    coset H ((h : G)*x) = coset H x := by
  apply Quotient.sound
  change QuotientGroup.rightRel H ((h:G)*x) x
  rw [QuotientGroup.rightRel_apply]
  simp [mul_inv_rev]

noncomputable def rightCosetEquiv (H : Subgroup G) : G ≃ RightCosets H × H where
  toFun x := (coset H x,cosetCoord H x)
  invFun q := q.2 * q.1.out
  left_inv x := by simp [cosetCoord]
  right_inv q := by
    rcases q with ⟨q,h⟩
    have hc : coset H ((h:G)*q.out) = q := by
      rw [coset_mul]; exact Quotient.out_eq q
    apply Prod.ext hc
    apply Subtype.ext
    simp only [cosetCoord, hc]
    simp

noncomputable def chainCosetEquiv (H : Subgroup G) :
    FreeChain A G ≃ₗ[ℤ] (A × RightCosets H) →₀ MonoidAlgebra ℤ H :=
  (Finsupp.domLCongr ((Equiv.prodCongr (Equiv.refl A) (rightCosetEquiv H)).trans
    (Equiv.prodAssoc A (RightCosets H) H).symm)).trans
    ((Finsupp.curryLinearEquiv ℤ).trans
      (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm))

@[simp] theorem chainCosetEquiv_coeff (H : Subgroup G) (c : FreeChain A G)
    (a : A) (q : RightCosets H) (h : H) :
    ((chainCosetEquiv H c) (a,q)).coeff h = c (a,(h:G)*q.out) := by
  rfl

@[simp] theorem chainCosetEquiv_shift (H : Subgroup G) (h : H) (c : FreeChain A G)
    (i : A × RightCosets H) :
    chainCosetEquiv H (chainShift (h:G) c) i =
      Representation.leftRegular ℤ H h (chainCosetEquiv H c i) := by
  apply MonoidAlgebra.ext
  ext k
  rcases i with ⟨a,q⟩
  simp only [chainCosetEquiv_coeff,shift_apply,Representation.coeff_ofMulAction]
  simp [mul_assoc]

noncomputable def subgroupNorm (H : Subgroup G) [Fintype H] :
    FreeChain A G →ₗ[ℤ] FreeChain A G := ∑ h : H, (chainShift (h:G)).toLinearMap

@[simp] theorem chainCosetEquiv_norm (H : Subgroup G) [Fintype H] (c : FreeChain A G)
    (i : A × RightCosets H) :
    chainCosetEquiv H (subgroupNorm H c) i =
      (Representation.leftRegular ℤ H).norm (chainCosetEquiv H c i) := by
  simp only [subgroupNorm,LinearMap.sum_apply,map_sum,Representation.norm]
  rw [Finsupp.coe_finsetSum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro h _
  exact chainCosetEquiv_shift H h c i

end FreeChain
end Release075

namespace Release075
open CategoryTheory
attribute [local instance] Classical.propDecidable Classical.decEq

namespace FreeChain
variable {A G : Type} [Group G] (H : Subgroup G) [Fintype H] [IsCyclic H]
    (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g)

end FreeChain
end Release075

namespace Release075.FreeChain
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B G : Type} [Group G]

noncomputable def augmentation : FreeChain A G →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => (1:ℤ))

omit [Group G] in
@[simp] theorem augmentation_single (a : A) (x : G) (n : ℤ) :
    augmentation (Finsupp.single (a,x) n) = n := by
  simp [augmentation]

@[simp] theorem augmentation_shift (g : G) (c : FreeChain A G) :
    augmentation (chainShift g c) = augmentation c := by
  have he : (augmentation (A:=A)).comp (chainShift g).toLinearMap = augmentation := by
    apply Finsupp.lhom_ext
    intro ⟨a,x⟩ n
    simp [chainShift]
  exact LinearMap.congr_fun he c

@[simp] theorem augmentation_norm (H : Subgroup G) [Fintype H] (c : FreeChain A G) :
    augmentation (subgroupNorm H c) = (Fintype.card H : ℤ) * augmentation c := by
  simp [subgroupNorm,LinearMap.sum_apply]

end Release075.FreeChain

end OAI


