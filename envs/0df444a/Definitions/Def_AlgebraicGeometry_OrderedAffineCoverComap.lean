-- Prove2me | Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
-- name    : AlgebraicGeometry_OrderedAffineCoverComap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/5674cf21-425b-529b-9a18-322106be21a2
-- title:
--   Pullback and base change of ordered affine covers
-- statement:
--   Throughout, an `OrderedAffineCover` of a scheme $V$ is the project's structure consisting of a finite linearly ordered index type $\iota$, a family of opens $U_i \subseteq V$, a proof that each $U_i$ is an affine open, and a proof that $\bigsqcup_i U_i = \top$; for a strictly increasing chain $s = (s_0 < \dots < s_i)$ in $\iota$ (an element of `Idx i`) the open `inter s` is $\bigcap_j U_{s_j}$, and `face s j` deletes the $j$-th entry of the chain.
--
--   The module first records `preimage_iInf_fin`: for a morphism of schemes $f\colon Y \to Z$ and a family $W\colon \mathrm{Fin}(n+1) \to Z.\mathrm{Opens}$, one has $f^{-1}\bigl(\bigwedge_j W_j\bigr) = \bigwedge_j f^{-1}(W_j)$, proved by induction on $n$ from the binary case.
--
--   For an ordered affine cover $\mathcal U$ of $X$ and an affine morphism $f\colon Y \to X$, `comap` is the ordered affine cover of $Y$ with the same index type, the same finiteness and linear order data, charts $f^{-1}(U_i)$, affineness of each chart from the fact that the preimage of an affine open under an affine morphism is affine, and the covering condition from commutation of preimage with suprema. The accompanying lemmas state that the index type, the chain types `Idx i`, the face maps, and the charts of `comap` coincide with those of $\mathcal U$, and that $(\mathcal U \text{ comap } f).\mathrm{inter}\, s = f^{-1}(\mathcal U.\mathrm{inter}\, s)$, together with the two resulting inequalities.
--
--   The base-change case is an abbreviation: given $\pi\colon X \to \operatorname{Spec} R$ and an $R$-algebra $A$, `baseChange` is `comap` along the first projection $X \times_{\operatorname{Spec} R} \operatorname{Spec} A \to X$, which is affine as a base change of $\operatorname{Spec} A \to \operatorname{Spec} R$; the same list of identities is restated in this notation. Finally, `toOrderedAffineCover_pullback` asserts that for a two-chart affine open cover $\mathcal V$ of $X$, the ordered affine cover attached to the pulled-back two-chart cover $\mathcal V.\mathrm{pullback}\,\pi\,A$ equals the base change along $\pi$, $A$ of the ordered affine cover attached to $\mathcal V$.
--
--   **Relation to Mathlib.** Mathlib has `Scheme.OpenCover` and `Scheme.AffineOpenCover`, but not this structure of a finite linearly ordered affine cover; `OrderedAffineCover` and its `comap`/`baseChange` operations are the project's own. Mathlib supplies the ingredients used: `IsAffineHom`, the stability of affine opens under preimage along an affine morphism, and scheme pullbacks.
--
--   **Where it is used.** These covers are the geometric input for the alternating Čech complex of an `OModulePresheaf`: `baseChange` produces the cover on which the Čech complex after base change to an $R$-algebra $A$ is formed, so that cohomology-and-base-change arguments for coherent sheaves can be phrased, and `comap` along a closed immersion handles pushforward along such a map. The compatibility with the two-chart covers links this $n$-chart setting to the two-term Čech complexes used for the modular-curve and deformation-ring computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverComap.lean

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OrderedAffineCover

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Scheme.TwoAffineOpenCover

theorem preimage_iInf_fin {Y Z : Scheme.{u}} (f : Y ⟶ Z) {n : ℕ} (W : Fin (n + 1) → Z.Opens) :
    f ⁻¹ᵁ (⨅ j, W j) = ⨅ j, f ⁻¹ᵁ (W j) := by
  have hsplit : ∀ {α : Type u} [CompleteLattice α] {m : ℕ} (g : Fin (m + 2) → α),
      (⨅ j : Fin (m + 2), g j) = g 0 ⊓ (⨅ j : Fin (m + 1), g j.succ) := fun g =>
    le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
      (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
  induction n with
  | zero => simp only [show (⨅ j : Fin 1, W j) = W 0 from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl),
      show (⨅ j : Fin 1, f ⁻¹ᵁ (W j)) = f ⁻¹ᵁ (W 0) from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)]
  | succ m ih =>
    rw [hsplit W, Scheme.Hom.preimage_inf, ih (fun j => W j.succ), hsplit (fun j => f ⁻¹ᵁ (W j))]

section Comap

variable {X Y : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (f : Y ⟶ X) [IsAffineHom f]

def comap : Y.OrderedAffineCover where
  ι := 𝒰.ι
  instFintype := 𝒰.instFintype
  instLinearOrder := 𝒰.instLinearOrder
  U i := f ⁻¹ᵁ 𝒰.U i
  isAffineOpen i := (𝒰.isAffineOpen i).preimage f
  iSup_eq_top := by rw [← Scheme.Hom.preimage_iSup, 𝒰.iSup_eq_top]; rfl

theorem comap_ι : (𝒰.comap f).ι = 𝒰.ι := rfl

theorem comap_U (i : 𝒰.ι) : (𝒰.comap f).U i = f ⁻¹ᵁ 𝒰.U i := rfl

theorem comap_Idx (i : ℕ) : (𝒰.comap f).Idx i = 𝒰.Idx i := rfl

theorem comap_face {i : ℕ} (s : 𝒰.Idx (i + 1)) (j : Fin (i + 2)) : (𝒰.comap f).face s j = 𝒰.face s j := rfl

theorem comap_inter {i : ℕ} (s : 𝒰.Idx i) : (𝒰.comap f).inter s = f ⁻¹ᵁ 𝒰.inter s :=
  (preimage_iInf_fin f (fun j => 𝒰.U (s.1 j))).symm

theorem comap_inter_le {i : ℕ} (s : 𝒰.Idx i) : (𝒰.comap f).inter s ≤ f ⁻¹ᵁ 𝒰.inter s :=
  (𝒰.comap_inter f s).le

theorem le_comap_inter {i : ℕ} (s : 𝒰.Idx i) : f ⁻¹ᵁ 𝒰.inter s ≤ (𝒰.comap f).inter s :=
  (𝒰.comap_inter f s).ge

end Comap

section BaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (π : X ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A]

abbrev baseChange : (Limits.pullback π (specMap R A)).OrderedAffineCover :=
  haveI := isAffineHom_fst π A
  𝒰.comap (Limits.pullback.fst π (specMap R A))

theorem baseChange_ι : (𝒰.baseChange π A).ι = 𝒰.ι := rfl

theorem baseChange_U (i : 𝒰.ι) :
    (𝒰.baseChange π A).U i = (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.U i := rfl

theorem baseChange_Idx (i : ℕ) : (𝒰.baseChange π A).Idx i = 𝒰.Idx i := rfl

theorem baseChange_face {i : ℕ} (s : 𝒰.Idx (i + 1)) (j : Fin (i + 2)) :
    (𝒰.baseChange π A).face s j = 𝒰.face s j := rfl

theorem baseChange_inter {i : ℕ} (s : 𝒰.Idx i) :
    (𝒰.baseChange π A).inter s = (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s :=
  haveI := isAffineHom_fst π A
  𝒰.comap_inter _ s

theorem baseChange_inter_le {i : ℕ} (s : 𝒰.Idx i) :
    (𝒰.baseChange π A).inter s ≤ (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s :=
  (𝒰.baseChange_inter π A s).le

theorem le_baseChange_inter {i : ℕ} (s : 𝒰.Idx i) :
    (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s ≤ (𝒰.baseChange π A).inter s :=
  (𝒰.baseChange_inter π A s).ge

end BaseChange

end AlgebraicGeometry.Scheme.OrderedAffineCover

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (π : X ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A]

theorem toOrderedAffineCover_pullback :
    (𝒱.pullback π A).toOrderedAffineCover = 𝒱.toOrderedAffineCover.baseChange π A := by
  unfold Scheme.TwoAffineOpenCover.toOrderedAffineCover Scheme.OrderedAffineCover.baseChange
    Scheme.OrderedAffineCover.comap
  congr 1
  funext i; rcases i with ⟨i⟩; fin_cases i <;> rfl

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end


