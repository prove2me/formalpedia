-- Prove2me | Definitions.Def_MazurTransfer_ScalarCharacterLineOriginalRepresentationsAndIntertwiningData20261018
-- name    : MazurTransfer_ScalarCharacterLineOriginalRepresentationsAndIntertwiningData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T23:47:36.910736+00:00
-- url     : https://prove2.me/theorems/332f3168-a63c-4511-9586-121090aed293
-- title:
--   Original scalar character representation and eigenvector intertwining map
-- statement:
--   The original scalar representation, its immediate action certificate, and the eigenvector intertwining constructor. Three full declaration types and two whole values are checked in all original universes. Named downstream consumer: the actual arithmetic-character exact sequence. Injectivity and range remain separate theorem contracts.
-- source:
--   MazurTheorem original declarations and immediately necessary constructor certificates; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a nonzero eigenvector for a character gives an injective
intertwining map from its scalar representation onto its generated line.
Named downstream consumer: the actual arithmetic13-to-cyclotomic19 norm
kernel short exact sequence.
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
universe u v w
namespace MazurTransfer.ScalarCharacterLine
variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

def scalarRepresentation (χ : G →* kˣ) : Representation k G k where
  toFun g := LinearMap.lsmul k k (χ g : k)
  map_one' := by
    apply LinearMap.ext
    intro c
    change (χ 1 : k) * c = c
    simp only [map_one, Units.val_one, one_mul]
  map_mul' g h := by
    apply LinearMap.ext
    intro c
    change (χ (g * h) : k) * c = (χ g : k) * ((χ h : k) * c)
    rw [map_mul, Units.val_mul, mul_assoc]

theorem scalarRepresentation_apply (χ : G →* kˣ) (g : G) (c : k) :
    scalarRepresentation χ g c = (χ g : k) * c := rfl

def vectorIntertwining (χ : G →* kˣ) (ρ : Representation k G V) (v : V)
    (hv : ∀ g : G, ρ g v = (χ g : k) • v) :
    Representation.IntertwiningMap (scalarRepresentation χ) ρ :=
  (LinearMap.toSpanSingleton k V v).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g c
    change ((χ g : k) * c) • v = ρ g (c • v)
    rw [map_smul, hv g, smul_smul, mul_comm])

end MazurTransfer.ScalarCharacterLine
#print axioms MazurTransfer.ScalarCharacterLine.scalarRepresentation
#print axioms MazurTransfer.ScalarCharacterLine.vectorIntertwining


