-- Prove2me | Definitions.Def_NumberField_Extension
-- name    : NumberField_Extension
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/2350559f-29f6-5a64-8c6e-d73d21a3de05
-- title:
--   Extensions of complex embeddings and of infinite places
-- statement:
--   For a field extension $L/K$ the module first fixes a relation between complex embeddings: for $f : K \to \mathbb{C}$ and $g : L \to \mathbb{C}$, `IsExtension f g` is the equality $g \circ (\text{algebraMap } K\ L) = f$, i.e. $g$ restricts to $f$ on $K$. Two refinements are defined: `IsMixedExtension f g` is the conjunction of `IsExtension f g` with `IsReal f` and $\lnot$`IsReal g` (where Mathlib's `IsReal` says an embedding is fixed by postcomposition with complex conjugation), and `IsUnmixedExtension f g` is `IsExtension f g` together with the negation of `IsMixedExtension f g`; thus the unmixed case is the residual one, and `IsUnmixedExtension.isReal_of_isReal` records that an unmixed extension of a real embedding is real. Accompanying lemmas state that if $f$ is not real then `conjugate g` cannot also extend $f$, that embeddings differing in whether they extend $f$ are distinct, and that any extension of a non-real embedding is non-real. The definition `isExtensionEquivSum` exhibits the resulting bijection between the extensions of $f$ and the disjoint union of its mixed and unmixed extensions.
--
--   On the level of infinite places, `Extension L v` is the subtype of places $w$ of $L$ with `w.comap (algebraMap K L) = v`, with `toExtension` viewing an arbitrary $w$ as an extension of its own restriction. For such a $w$ it is shown that $v$ complex forces $w$ complex, that $w$ real forces $v$ real, that $v$ is the place attached to the restriction of `w.embedding`, and that either `w.embedding` or its conjugate extends `v.embedding`. These two alternatives are also packaged as classes `IsLift` and `IsConjugateLift`, each a structure whose single field is the corresponding `IsExtension` assertion, so that the alternatives can be assumed as instances; `isLift_or_isConjugateLift` gives the dichotomy. Finally `RamifiedExtension L v` and `UnramifiedExtension L v` are the subtypes of places $w$ above $v$ satisfying `w.IsRamified K`, respectively `w.IsUnramified K`, with coercions to `Extension L v`, constructors from an extension plus a ramification hypothesis, and projections recording in the ramified case that $w$ is complex and $v$ is real.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here — `NumberField.ComplexEmbedding.IsReal` and `conjugate`, `InfinitePlace` with `comap`, `mk`, `embedding`, and `IsRamified`/`IsUnramified`. The predicate that one complex embedding extends another, the mixed/unmixed dichotomy with its bijection, the subtypes of places above a given place (including the ramified and unramified variants), and the classes `IsLift`/`IsConjugateLift` are introduced in this module.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/NumberField/InfinitePlace/Extension.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_Extension.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

noncomputable section

namespace NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
  (f : K →+* ℂ) (g : L →+* ℂ)

abbrev IsExtension := g.comp (algebraMap K L) = f

variable {f g} in
theorem IsExtension.not_isExtension_conjugate (h : IsExtension f g)
    (hf : ¬ComplexEmbedding.IsReal f) :
    ¬IsExtension f (conjugate g) := by
  simp_all [RingHom.ext_iff, ComplexEmbedding.isReal_iff]

variable {f g} in
theorem IsExtension.ne {r : L →+* ℂ} (hg : IsExtension f g) (hr : ¬IsExtension f r) :
    g ≠ r := by
  simp_all only [← hg, RingHom.ext_iff, RingHom.coe_comp, Function.comp_apply, not_forall,
    ne_eq]
  let ⟨x, hx⟩ := hr
  exact ⟨algebraMap K L x, by aesop⟩

abbrev IsMixedExtension :=
  IsExtension f g ∧ ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g

theorem not_isReal_of_not_isReal {f : K →+* ℂ} {g : L →+* ℂ} (h : IsExtension f g)
    (hf : ¬ComplexEmbedding.IsReal f) :
    ¬ComplexEmbedding.IsReal g :=
  mt (IsReal.comp _) (h ▸ hf)

namespace IsMixedExtension

theorem isExtension (h : IsMixedExtension f g) :
    IsExtension f g := h.1

theorem isReal (h : IsMixedExtension f g) :
    ComplexEmbedding.IsReal f := h.2.1

theorem not_isReal (h : IsMixedExtension f g) :
    ¬ComplexEmbedding.IsReal g := h.2.2

end IsMixedExtension

abbrev IsUnmixedExtension := IsExtension f g ∧ ¬IsMixedExtension f g

variable {f g} in
theorem IsUnmixedExtension.isReal_of_isReal (h : IsUnmixedExtension f g)
    (hf : ComplexEmbedding.IsReal f) :
    ComplexEmbedding.IsReal g := by
  simp only [IsUnmixedExtension, not_and, not_not] at h
  exact h.2 h.1 hf

open scoped Classical in

def isExtensionEquivSum (f : K →+* ℂ) :
    { g : L →+* ℂ // IsExtension f g } ≃
      { g : L →+* ℂ // IsMixedExtension f g } ⊕ { g : L →+* ℂ // IsUnmixedExtension f g } :=
  (Equiv.sumCompl
    (fun g => ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g.1)).symm.trans <|
    Equiv.sumCongr
      (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun g => _ ∧ ¬ComplexEmbedding.IsReal g))
      ((Equiv.subtypeSubtypeEquivSubtypeInter _
        (fun g => ¬(_ ∧ ¬ComplexEmbedding.IsReal g))).trans
        (Equiv.subtypeEquiv (Equiv.refl _) (fun _ => by aesop)))

end NumberField.ComplexEmbedding

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] (v : InfinitePlace K) (w : InfinitePlace L)

variable [Algebra K L]

variable (L) in

abbrev Extension (v : InfinitePlace K) := { w : InfinitePlace L // w.comap (algebraMap K L) = v }

variable (K) in

abbrev toExtension : (w.comap (algebraMap K L)).Extension L := ⟨w, rfl⟩

theorem coe_toExtension (w : InfinitePlace L) : (toExtension K w).1 = w := rfl

namespace Extension

variable {v : InfinitePlace K} (w : v.Extension L)

theorem isComplex_of_isComplex (hv : v.IsComplex) :
    w.1.IsComplex := by
  rw [isComplex_iff, ComplexEmbedding.isReal_iff, RingHom.ext_iff, not_forall] at hv ⊢
  let ⟨x, hx⟩ := hv
  use algebraMap K L x
  rw [← w.2, ← mk_embedding w.1, comap_mk] at hx
  cases embedding_mk_eq (w.1.embedding.comp (algebraMap K L)) with
  | inl hl => simp_all
  | inr hr => aesop

theorem isReal_base (hw : w.1.IsReal) :
    v.IsReal := by
  simp_all only [← not_isComplex_iff_isReal]
  exact mt w.isComplex_of_isComplex hw

theorem mk_embedding : mk (w.1.embedding.comp (algebraMap K L)) = v := by
  rw [← comap_mk, w.1.mk_embedding, w.2]

theorem isExtension_or_isExtension_conjugate :
    IsExtension v.embedding w.1.embedding ∨ IsExtension v.embedding (conjugate w.1.embedding) := by
  cases embedding_mk_eq (w.1.embedding.comp (algebraMap K L)) with
  | inl hl =>
    convert Or.inl <| hl ▸ congrArg InfinitePlace.embedding w.mk_embedding
  | inr hr =>
    convert Or.inr <| hr ▸ congrArg InfinitePlace.embedding w.mk_embedding
    rfl

theorem isExtension_conjugate_of_not_isExtension (h : ¬IsExtension v.embedding w.1.embedding) :
    IsExtension v.embedding (conjugate w.1.embedding) :=
  w.isExtension_or_isExtension_conjugate.resolve_left h

variable (L)

variable (v : InfinitePlace K) (w : v.Extension L)

class IsLift where
  isExtension' : IsExtension v.embedding w.1.embedding

theorem IsLift.isExtension [w.IsLift L v] : IsExtension v.embedding w.1.embedding :=
  IsLift.isExtension'

class IsConjugateLift where
  isExtension' : IsExtension v.embedding (conjugate w.1.embedding)

theorem IsConjugateLift.isExtension [w.IsConjugateLift L v] :
    IsExtension v.embedding (conjugate w.1.embedding) := IsConjugateLift.isExtension'

theorem isLift_or_isConjugateLift (v : InfinitePlace K) (w : v.Extension L) :
    w.IsLift L v ∨ w.IsConjugateLift L v := by
  cases isExtension_or_isExtension_conjugate w with
  | inl hl => exact Or.inl ⟨hl⟩
  | inr hr => exact Or.inr ⟨hr⟩

end Extension

variable (L)

abbrev RamifiedExtension (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsRamified K }

abbrev UnramifiedExtension (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsUnramified K }

variable {L v}

def Extension.toRamifiedExtension {w : v.Extension L} (h : w.1.IsRamified K) :
    v.RamifiedExtension L := ⟨w.1, ⟨w.2, h⟩⟩

def Extension.toUnramifiedExtension {w : v.Extension L} (h : w.1.IsUnramified K) :
    v.UnramifiedExtension L := ⟨w.1, ⟨w.2, h⟩⟩

namespace RamifiedExtension

theorem comap_eq (w : v.RamifiedExtension L) : w.1.comap (algebraMap K L) = v := w.2.1

theorem isRamified (w : v.RamifiedExtension L) : w.1.IsRamified K := w.2.2

theorem isReal_comap (w : v.RamifiedExtension L) : (w.1.comap (algebraMap K L)).IsReal :=
  (isRamified_iff.1 w.isRamified).2

instance : Coe (v.RamifiedExtension L) (v.Extension L) where
  coe w := ⟨w.1, w.2.1⟩

theorem isReal (w : v.RamifiedExtension L) : v.IsReal :=
  w.comap_eq ▸ w.isReal_comap

theorem isComplex (w : v.RamifiedExtension L) :
    (w.1 : InfinitePlace L).IsComplex :=
  (isRamified_iff.1 w.isRamified).1

end RamifiedExtension

namespace UnramifiedExtension

theorem comap_eq (w : UnramifiedExtension L v) : w.1.comap (algebraMap K L) = v := w.2.1

theorem isUnramified (w : UnramifiedExtension L v) : w.1.IsUnramified K := w.2.2

instance : Coe (v.UnramifiedExtension L) (v.Extension L) where
  coe w := ⟨w.1, w.comap_eq⟩

end UnramifiedExtension

end NumberField.InfinitePlace


