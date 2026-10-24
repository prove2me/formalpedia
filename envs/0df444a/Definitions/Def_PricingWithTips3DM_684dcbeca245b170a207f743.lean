-- Prove2me | Definitions.Def_PricingWithTips3DM_684dcbeca245b170a207f743
-- name    : PricingWithTips3DM_684dcbeca245b170a207f743
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:01:12.042431+00:00
-- url     : https://prove2.me/theorems/a0241ed8-4cb2-4a3c-adbf-8fd141e8d784
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeedRowSource
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_3d06fdaba09255b5d609af60
import Definitions.Def_PricingWithTips3DM_c74718a616769e19e5aa2ff6
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform sources with one row per transition seed

Recursive transition assembly repeatedly combines independently verified
numeric fragments that share the same raw input and transition-row index.
This module packages that invariant once: a source exposes one semantic row
for every canonical verifier transition seed, together with a concrete
polynomial-time TM2 producing the marked row family.  The append operation
then reuses the physical same-input row concatenator.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- A concrete raw-input source whose output has exactly one row for every
canonical verifier transition seed. -/
structure VerifierTransitionSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) where
  row : TransitionRowSeed → List UnaryFrameSym
  family : List Γ → UnaryFrameMarkedRowFamily
  rows_eq : ∀ input,
    (family input).rows = (verifierTransitionRowSeeds W input).map row
  computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily family

namespace VerifierTransitionSeedRowSource

/-- Every seed-row source has the canonical transition row count. -/
theorem rows_length
    {Γ : Type} {L : Language Γ} {W : VerifierWitness L}
    (source : VerifierTransitionSeedRowSource W) (input : List Γ) :
    (source.family input).rows.length =
      (verifierTransitionRowSeeds W input).length := by
  rw [source.rows_eq]
  simp

private theorem concat_map_rows
    {α : Type} (items : List α)
    (left right : α → List UnaryFrameSym) :
    concatUnaryFrameMarkedRows (items.map left) (items.map right) =
      items.map fun item => left item ++ right item := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.map_cons, concatUnaryFrameMarkedRows]
      rw [ih]

/-- Append two independently generated fragments pointwise at every
transition seed.  The implementation runs the two source machines and uses
the verified streaming boundary eraser, rather than an oracle-side append. -/
noncomputable def append
    {Γ : Type} {L : Language Γ} {W : VerifierWitness L}
    (left right : VerifierTransitionSeedRowSource W) :
    VerifierTransitionSeedRowSource W := by
  letI : Fintype Γ := W.alphabetFintype
  let aligned : ∀ input,
      (left.family input).rows.length =
        (right.family input).rows.length := fun input => by
    rw [left.rows_length, right.rows_length]
  exact
    { row := fun seed => left.row seed ++ right.row seed
      family := UnaryFrameMarkedRowParallelConcat.concatenatedFamily aligned
      rows_eq := fun input => by
        change concatUnaryFrameMarkedRows
            (left.family input).rows (right.family input).rows = _
        rw [left.rows_eq, right.rows_eq]
        exact concat_map_rows (verifierTransitionRowSeeds W input)
          left.row right.row
      computableInPolyTime :=
        UnaryFrameMarkedRowParallelConcat.computableInPolyTime
          left.computableInPolyTime right.computableInPolyTime aligned }

@[simp] theorem append_row
    {Γ : Type} {L : Language Γ} {W : VerifierWitness L}
    (left right : VerifierTransitionSeedRowSource W)
    (seed : TransitionRowSeed) :
    (left.append right).row seed = left.row seed ++ right.row seed := rfl

end VerifierTransitionSeedRowSource

end CLRS.Chapter34.Turing.CookLevin


