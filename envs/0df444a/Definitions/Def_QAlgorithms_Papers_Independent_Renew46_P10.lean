-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P10
-- name    : QAlgorithms_Papers_Independent_Renew46_P10
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:04:21.185019+00:00
-- url     : https://prove2.me/theorems/c1084765-7901-4623-a4d4-e683653fbc94
-- title:
--   Definitions for Reductive and unipotent actions of affine groups
-- statement:
--   The objects the formalized statements of *Reductive and unipotent actions of affine groups* (arXiv:1406.4446) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RightActionLaws`: Right action laws, Observation 5.4, PDF p.12. The underlying set may be empty.
--   - `TranslationExtension`: An extension of right translation on the first factor, Observation 5.4, PDF p.12. Every element of H acts by (h,l) ↦ (h*r,l).
--   - `BaseAction`: The base right action is trivial on H, Observation 5.4, PDF p.12. This does not require that the full G-action on L be trivial.
--   - `TwistedCocycleData`: Twisted cocycle data, equation (4), Observation 5.4, PDF p.12. Products and conjugation in the cocycle identity are taken in the ambient G; c itself takes values in H.
--   - `NestedCocycleData`: Equivalent nested cocycle data, equation (7), Observation 5.4, PDF p.12.
--   - `cocycleAction`: Reconstruct the extension, Observation 5.4, PDF p.12: (h,l)·g = (c(l,hg),l⋆g). The printed dummy h/r mismatch is corrected by using the first coordinate h consistently.
--   - `extensionBase`: Extract the base coordinate at (1,l), Observation 5.4, PDF p.12.
--   - `extensionCocycle`: Extract the H-coordinate at (1,l), Observation 5.4, PDF p.12.
-- source:
--   Reductive and unipotent actions of affine groups, arXiv:1406.4446v1, https://arxiv.org/abs/1406.4446v1

import Mathlib

/-! Statements from Ferrer Santos–Rittatore, arXiv:1406.4446v1.
Only Observation 5.4 is stated here. The algebraic-geometric nodes and the
source-defective nodes are individually deferred in the unit's HARD.md and GAPS.json.
Compilation is pending the batch mechanical handoff.
-/

namespace QAlgorithms.Papers.Independent.Renew46.P10

universe u v

/-- Right action laws, Observation 5.4, PDF p.12. The underlying set may be empty. -/
def RightActionLaws {G : Type u} [Group G] {A : Type v}
    (act : A → G → A) : Prop :=
  (∀ a, act a 1 = a) ∧
  (∀ a g g2, act (act a g) g2 = act a (g * g2))

/-- An extension of right translation on the first factor, Observation 5.4,
PDF p.12. Every element of H acts by (h,l) ↦ (h*r,l). -/
def TranslationExtension {G : Type u} [Group G] (H : Subgroup G) {L : Type v}
    (act : (H × L) → G → (H × L)) : Prop :=
  RightActionLaws act ∧ ∀ (h r : H) (l : L), act (h, l) (r : G) = (h * r, l)

/-- The base right action is trivial on H, Observation 5.4, PDF p.12.
This does not require that the full G-action on L be trivial. -/
def BaseAction {G : Type u} [Group G] (H : Subgroup G) {L : Type v}
    (star : L → G → L) : Prop :=
  RightActionLaws star ∧ ∀ (l : L) (h : H), star l (h : G) = l

/-- Twisted cocycle data, equation (4), Observation 5.4, PDF p.12.
Products and conjugation in the cocycle identity are taken in the ambient G;
c itself takes values in H. -/
def TwistedCocycleData {G : Type u} [Group G] (H : Subgroup G) {L : Type v}
    (star : L → G → L) (c : L → G → H) : Prop :=
  BaseAction H star ∧
  (∀ (l : L) (h : H), c l (h : G) = h) ∧
  (∀ (l : L) (g g2 : G),
    (c l (g * g2) : G) =
      (c (star l g) g2 : G) * g2⁻¹ * (c l g : G) * g2)

/-- Equivalent nested cocycle data, equation (7), Observation 5.4, PDF p.12. -/
def NestedCocycleData {G : Type u} [Group G] (H : Subgroup G) {L : Type v}
    (star : L → G → L) (c : L → G → H) : Prop :=
  BaseAction H star ∧
  (∀ (l : L) (h : H), c l (h : G) = h) ∧
  (∀ (l : L) (g g2 : G),
    c l (g * g2) = c (star l g) ((c l g : G) * g2))

/-- Reconstruct the extension, Observation 5.4, PDF p.12:
(h,l)·g = (c(l,hg),l⋆g). The printed dummy h/r mismatch is corrected
by using the first coordinate h consistently. -/
def cocycleAction {G : Type u} [Group G] {H : Subgroup G} {L : Type v}
    (star : L → G → L) (c : L → G → H) : (H × L) → G → (H × L) :=
  fun p g => (c p.2 ((p.1 : G) * g), star p.2 g)

/-- Extract the base coordinate at (1,l), Observation 5.4, PDF p.12. -/
def extensionBase {G : Type u} [Group G] {H : Subgroup G} {L : Type v}
    (act : (H × L) → G → (H × L)) : L → G → L :=
  fun l g => (act (1, l) g).2

/-- Extract the H-coordinate at (1,l), Observation 5.4, PDF p.12. -/
def extensionCocycle {G : Type u} [Group G] {H : Subgroup G} {L : Type v}
    (act : (H × L) → G → (H × L)) : L → G → H :=
  fun l g => (act (1, l) g).1

/-- Sanity: the trivial right action satisfies both action laws on any set. -/
example {G : Type u} [Group G] {A : Type v} :
    RightActionLaws (fun (a : A) (_ : G) => a) :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

/-- Sanity: reconstruction preserves exactly the supplied second coordinate. -/
example {G : Type u} [Group G] {H : Subgroup G} {L : Type v}
    (star : L → G → L) (c : L → G → H) :
    extensionBase (cocycleAction star c) = star := rfl

/-- Sanity: extraction at the identity first coordinate recovers exactly c. -/
example {G : Type u} [Group G] {H : Subgroup G} {L : Type v}
    (star : L → G → L) (c : L → G → H) :
    extensionCocycle (cocycleAction star c) = c := by
  funext l g
  simp [extensionCocycle, cocycleAction]

/-- Sanity: for H=G and L a point the cocycle c(g)=g has the printed
conjugation order. No commutativity assumption is used. -/
example {G : Type u} [Group G] (g g2 : G) :
    g * g2 = g2 * g2⁻¹ * g * g2 := by
  simp

/-- Sanity: when H=G, a trivial base action and c(l,g)=g satisfy
all of equation (4), including normalization, for any group and any set L. -/
example {G : Type u} [Group G] {L : Type v} :
    TwistedCocycleData (⊤ : Subgroup G) (fun (l : L) (_ : G) => l)
      (fun (_ : L) (g : G) => (⟨g, trivial⟩ : (⊤ : Subgroup G))) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro l
    rfl
  · intro l g g2
    rfl
  · intro l h
    rfl
  · intro l h
    apply Subtype.ext
    rfl
  · intro l g g2
    simp

end QAlgorithms.Papers.Independent.Renew46.P10


