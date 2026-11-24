-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroTokenSemantics
-- name    : Sensitivity214439_PairedSemantic_Solutions_MacroTokenSemantics
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:56:34.055367+00:00
-- url     : https://prove2.me/theorems/3fa0bd5f-d82e-4e81-aa2b-29d38ca726f9
-- title:
--   Semantic compatibility of cyclic tokens and bit masks
-- statement:
--   A token is a macro together with a Boolean side. Two tokens are compatible when one of their directed macro displacements is selected by the orientation mask and its destination side equals that displacement's label. A marker at macro $p$ marks a token when the arc from $p$ to the token's macro is selected and its label agrees with the token side. A token clique requires compatibility for every distinct token pair.
--
--   The mask-model structure identifies three finite base masks with these semantic relations. Translation then identifies the rotated masks at every source. A label-preserving multiplier and translation act by $(m,b)\mapsto(g(m-t),b)$, preserving compatibility and marking; an inverse multiplier makes the map injective. This connects checked bit-mask clique certificates to actual token cardinality bounds.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MacroTokenSemantics.lean lines 17–124; SHA256 18bc7df9a2195a753a4da8f53224f779b0dee3fb789d4bdf75e39b7a450af333; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CliqueCertificate
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CyclicTokenMasks
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Ring.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

namespace SensitivityCyclicTokens
end SensitivityCyclicTokens



/-!
# Literal coherent macro tokens and affine symmetries

A token records a macro vertex and its inactive child. On an arc from `u` to
`v`, compatibility requires the inactive child at `v` to equal that arc's
literal label. A perfect marker restricts tokens to its outgoing labeled arcs.
-/

namespace SensitivityCyclicTokens

open scoped Fin.CommRing

def labelBit {n : ℕ} (labels : ℕ) (d : Fin n) : Fin 2 :=
  if labels.testBit d.val then 1 else 0

def compatible {n : ℕ} (orient labels : ℕ) (a b : Fin n × Fin 2) : Prop :=
  (orient.testBit (b.1 - a.1).val = true ∧ b.2 = labelBit labels (b.1 - a.1)) ∨
  (orient.testBit (a.1 - b.1).val = true ∧ a.2 = labelBit labels (a.1 - b.1))

def marked {n : ℕ} (orient labels : ℕ) (v : Fin n) (a : Fin n × Fin 2) : Prop :=
  orient.testBit (a.1 - v).val = true ∧ a.2 = labelBit labels (a.1 - v)

def TokenClique {n : ℕ} (orient labels : ℕ) (vertices : Finset (Fin n × Fin 2)) : Prop :=
  ∀ a ∈ vertices, ∀ b ∈ vertices, a ≠ b → compatible orient labels a b

theorem compatible_difference {n : ℕ} [NeZero n] (orient labels : ℕ)
    (a b : Fin n × Fin 2) :
    compatible orient labels a b ↔
      compatible orient labels (0, a.2) (b.1 - a.1, b.2) := by
  simp only [compatible, sub_zero, zero_sub, neg_sub]

theorem marked_difference {n : ℕ} [NeZero n] (orient labels : ℕ)
    (v : Fin n) (a : Fin n × Fin 2) :
    marked orient labels v a ↔ marked orient labels 0 (a.1 - v, a.2) := by
  simp only [marked, sub_zero]

structure TokenMaskModel (n orient labels base0 base1 markerBase : ℕ) [NeZero n] : Prop where
  base0_lt : base0 < 2 ^ (2 * n)
  base1_lt : base1 < 2 ^ (2 * n)
  marker_lt : markerBase < 2 ^ (2 * n)
  root_correct : ∀ (a b : Fin 2) (d : Fin n),
    ((if a.val = 0 then base0 else base1).testBit (encode (d, b)) = true) ↔
      compatible orient labels (0, a) (d, b)
  marker_correct : ∀ (b : Fin 2) (d : Fin n),
    (markerBase.testBit (encode (d, b)) = true) ↔ marked orient labels 0 (d, b)

theorem TokenMaskModel.adjacency_iff {n orient labels base0 base1 markerBase : ℕ}
    [NeZero n] (model : TokenMaskModel n orient labels base0 base1 markerBase)
    (a b : Fin n × Fin 2) :
    (adjacency n base0 base1 (encode a)).testBit (encode b) = true ↔
      compatible orient labels a b := by
  rw [adjacency_token model.base0_lt model.base1_lt, model.root_correct]
  exact (compatible_difference orient labels a b).symm

theorem TokenMaskModel.marker_iff {n orient labels base0 base1 markerBase : ℕ}
    [NeZero n] (model : TokenMaskModel n orient labels base0 base1 markerBase)
    (v : Fin n) (a : Fin n × Fin 2) :
    (marker n markerBase v.val).testBit (encode a) = true ↔ marked orient labels v a := by
  rw [marker_token model.marker_lt, model.marker_correct]
  exact (marked_difference orient labels v a).symm

theorem TokenMaskModel.clique_bound {n orient labels base0 base1 markerBase mask bound : ℕ}
    [NeZero n] (model : TokenMaskModel n orient labels base0 base1 markerBase)
    (certificate : SensitivityCliqueCertificate.Certificate)
    (hcheck : SensitivityCliqueCertificate.check (adjacency n base0 base1)
      mask bound certificate = true)
    (vertices : Finset (Fin n × Fin 2)) (hclique : TokenClique orient labels vertices)
    (hmask : ∀ a ∈ vertices, mask.testBit (encode a) = true) :
    vertices.card ≤ bound := by
  have h := SensitivityCliqueCertificate.check_sound (adjacency n base0 base1)
    certificate mask bound hcheck (vertices.image encode) ?_ ?_
  · simpa only [Finset.card_image_of_injective _ encode_injective] using h
  · intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    exact hmask a ha
  · intro v hv w hw hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
    apply (model.adjacency_iff a b).mpr
    exact hclique a ha b hb (fun heq => hne (congrArg encode heq))

abbrev IsLabelMultiplier {n : ℕ} (orient labels : ℕ) (g : Fin n) : Prop :=
  ∀ d : Fin n,
    orient.testBit (g * d).val = orient.testBit d.val ∧
      labels.testBit (g * d).val = labels.testBit d.val

def affineToken {n : ℕ} (g t : Fin n) (a : Fin n × Fin 2) : Fin n × Fin 2 :=
  (g * (a.1 - t), a.2)

theorem affineToken_injective {n : ℕ} [NeZero n] (g gi t : Fin n)
    (hinv : gi * g = 1) : Function.Injective (affineToken g t) := by
  intro a b hab
  have hfst := congrArg Prod.fst hab
  have hmul := congrArg (fun z => gi * z) hfst
  have hsub : a.1 - t = b.1 - t := by
    simpa only [affineToken, ← mul_assoc, hinv, one_mul] using hmul
  have heq : a.1 = b.1 := by
    have h := congrArg (fun z => z + t) hsub
    simpa only [sub_add_cancel] using h
  have hsnd := congrArg (fun p : Fin n × Fin 2 => p.2) hab
  change a.2 = b.2 at hsnd
  exact Prod.ext heq hsnd

theorem compatible_affine {n orient labels : ℕ} [NeZero n]
    {g : Fin n} (hg : IsLabelMultiplier orient labels g)
    (t : Fin n) (a b : Fin n × Fin 2) :
    compatible orient labels (affineToken g t a) (affineToken g t b) ↔
      compatible orient labels a b := by
  have hf : g * (b.1 - t) - g * (a.1 - t) = g * (b.1 - a.1) := by ring
  have hb : g * (a.1 - t) - g * (b.1 - t) = g * (a.1 - b.1) := by ring
  simp only [compatible, affineToken, hf, hb, (hg (b.1 - a.1)).1,
    (hg (a.1 - b.1)).1, labelBit, (hg (b.1 - a.1)).2, (hg (a.1 - b.1)).2]

theorem marked_affine {n orient labels : ℕ} [NeZero n]
    {g : Fin n} (hg : IsLabelMultiplier orient labels g)
    (t v : Fin n) (a : Fin n × Fin 2) :
    marked orient labels (g * (v - t)) (affineToken g t a) ↔
      marked orient labels v a := by
  have hdiff : g * (a.1 - t) - g * (v - t) = g * (a.1 - v) := by ring
  simp only [marked, affineToken, hdiff, (hg (a.1 - v)).1, labelBit, (hg (a.1 - v)).2]




end SensitivityCyclicTokens


