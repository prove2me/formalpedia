-- Prove2me | Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
-- name    : AlgebraicGeometry_OrderedAffineCoverCochainPullback
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/de11bf4f-3e46-5725-8cd6-94beaa82bf10
-- title:
--   Refinement pull-back of alternating Čech cochains along a scheme morphism
-- statement:
--   Throughout, an `OrderedAffineCover` of a scheme $V$ consists of a finite linearly ordered index type $\iota$ together with affine opens $U_i$ whose supremum is $\top$; $\mathcal{K}.\mathrm{Idx}\,n$ is the type of strictly monotone $s \colon \mathrm{Fin}(n+1) \to \iota$, and $\mathcal{K}.\mathrm{inter}\,s = \bigsqcap_j U_{s(j)}$. Fix a morphism $h \colon X \to Y$, covers $\mathcal W$ of $X$ and $\mathcal K$ of $Y$, and a map $\lambda \colon \mathcal W.\iota \to \mathcal K.\iota$ on index sets.
--
--   First, `sortIdx`: for $s \in \mathcal W.\mathrm{Idx}\,n$ such that $\lambda \circ s$ is injective, it is the element of $\mathcal K.\mathrm{Idx}\,n$ given by $(\lambda \circ s) \circ \mathrm{Tuple.sort}(\lambda \circ s)$, i.e. the tuple $(\lambda s_0, \dots, \lambda s_n)$ rearranged into increasing order, which is strictly monotone because the sorted tuple is monotone and injective. The accompanying `sortIdx_val` records this description, and `inter_le_preimage_inter_sortIdx` states that under the hypothesis $\mathcal W.U_w \le h^{-1}(\mathcal K.U_{\lambda w})$ for all $w$ one has $\mathcal W.\mathrm{inter}\,s \le h^{-1}\bigl(\mathcal K.\mathrm{inter}(\mathrm{sortIdx}\,s)\bigr)$.
--
--   Second, for structure morphisms $\pi_X \colon X \to \operatorname{Spec} R'$ and $\pi_Y \colon Y \to \operatorname{Spec} R$ (which supply the module structures on the presheaf `unit`, whose sections over $U$ are $\Gamma(V,U)$), `unitPullback` sends an $n$-cochain $z$ for $\mathcal K$ to the $n$-cochain for $\mathcal W$ whose value at $s$ is $0$ when $\lambda \circ s$ fails to be injective, and otherwise is the sign of the sorting permutation times the image of $z(\mathrm{sortIdx}\,s)$ under $h^{\sharp}$ on $\mathcal K.\mathrm{inter}(\mathrm{sortIdx}\,s)$ followed by restriction to $\mathcal W.\mathrm{inter}\,s$. The two lemmas `unitPullback_apply_of_injective` and `unitPullback_apply_of_not_injective` extract the two branches.
--
--   **Relation to Mathlib.** Mathlib provides the sorting permutation `Tuple.sort` and its monotonicity, but no alternating Čech cochain complex attached to an ordered finite affine cover; the ordered covers, the cochain groups and this refinement pull-back are the project's own.
--
--   **Where it is used.** The construction supplies pull-back of Čech cochains of the structure sheaf along a morphism that need not be affine and along an index map that need not preserve the orderings, which is what is required when comparing cochains for covers of a product or under a group law; this is part of the coherent-cohomology machinery underlying the geometric input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OrderedAffineCover

open CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)

def sortIdx {n : ℕ} (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) : 𝒦.Idx n :=
  ⟨(lam ∘ s.1) ∘ (Tuple.sort (lam ∘ s.1)),
    (Tuple.monotone_sort (lam ∘ s.1)).strictMono_of_injective (hinj.comp (Tuple.sort (lam ∘ s.1)).injective)⟩

theorem sortIdx_val {n : ℕ} (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) :
    (𝒲.sortIdx 𝒦 lam s hinj).1 = (lam ∘ s.1) ∘ (Tuple.sort (lam ∘ s.1)) :=
  rfl

theorem inter_le_preimage_inter_sortIdx (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    {n : ℕ} (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) :
    𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj) := by
  change 𝒲.inter s ≤ h ⁻¹ᵁ (⨅ j, 𝒦.U ((𝒲.sortIdx 𝒦 lam s hinj).1 j))
  rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
  refine le_iInf fun j => ?_
  exact (iInf_le (fun i => 𝒲.U (s.1 i)) (Tuple.sort (lam ∘ s.1) j)).trans (hlam _)

end AlgebraicGeometry.Scheme.OrderedAffineCover

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory Opposite TopologicalSpace

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable {X Y : Scheme.{u}} {πX : X ⟶ Spec (.of R')} {πY : Y ⟶ Spec (.of R)}

def unitPullback (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (z : (unit πY).cochain 𝒦 n) : (unit πX).cochain 𝒲 n :=
  fun s => by
    classical
    exact if hinj : Function.Injective (lam ∘ s.1) then
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op).hom
          ((h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (z (𝒲.sortIdx 𝒦 lam s hinj)))
    else 0

theorem unitPullback_apply_of_injective (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (z : (unit πY).cochain 𝒦 n) (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) :
    unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z s =
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op).hom
          ((h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (z (𝒲.sortIdx 𝒦 lam s hinj))) := by
  classical
  simp only [unitPullback, dif_pos hinj]

theorem unitPullback_apply_of_not_injective (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (z : (unit πY).cochain 𝒦 n) (s : 𝒲.Idx n) (hinj : ¬ Function.Injective (lam ∘ s.1)) :
    unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z s = 0 := by
  classical
  simp only [unitPullback, dif_neg hinj]

end AlgebraicGeometry.OModulePresheaf

end


