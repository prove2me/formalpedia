-- Prove2me | Definitions.Def_MazurTransfer_IntertwiningMapOriginalKernelCoordinateData20261019
-- name    : MazurTransfer_IntertwiningMapOriginalKernelCoordinateData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T02:35:13.724078+00:00
-- url     : https://prove2.me/theorems/c9172284-a7cb-4a96-a0c5-59ff9cf52874
-- title:
--   Original literal kernels of specified intertwining quotients
-- statement:
--   The restricted representation on the actual linear kernel of a given quotient, its literal inclusion and the restriction of a second given quotient. Six original declaration types and three whole values are compared with the source. The inclusion injectivity and range certificates are included. Named downstream consumer: exact scalar-character inclusions for the previously selected actual norm quotient maps.
-- source:
--   MazurTheorem IntertwiningMapKernelCoordinates; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain a GIVEN intertwining quotient and give its
EXISTING linear kernel the restricted representation, with its literal
inclusion and restriction of another GIVEN quotient.
Named downstream consumer: exact character inclusions for the PREVIOUSLY
SELECTED actual order-13 norm-character quotient maps.
-/
import Mathlib.RepresentationTheory.Intertwining

noncomputable section
namespace MazurTransfer.IntertwiningMapKernelCoordinates
variable {k G V B : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup B] [Module k B]
variable (ρ : Representation k G V) (τ : Representation k G B)

def kernelRepresentation (p : Representation.IntertwiningMap ρ τ) :
    Representation k G (LinearMap.ker p.toLinearMap) := p.ker.toRepresentation

def kernelInclusion (p : Representation.IntertwiningMap ρ τ) :
    Representation.IntertwiningMap (kernelRepresentation ρ τ p) ρ :=
  (LinearMap.ker p.toLinearMap).subtype.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)

theorem kernelInclusion_injective (p : Representation.IntertwiningMap ρ τ) :
    Function.Injective (kernelInclusion ρ τ p) := Subtype.val_injective

theorem kernelInclusion_range (p : Representation.IntertwiningMap ρ τ) :
    LinearMap.range (kernelInclusion ρ τ p).toLinearMap = LinearMap.ker p.toLinearMap :=
  Submodule.range_subtype _

def kernelRestriction (p q : Representation.IntertwiningMap ρ τ) :
    Representation.IntertwiningMap (kernelRepresentation ρ τ p) τ :=
  q.comp (kernelInclusion ρ τ p)

theorem kernelRestriction_apply (p q : Representation.IntertwiningMap ρ τ)
    (x : LinearMap.ker p.toLinearMap) : kernelRestriction ρ τ p q x = q x.val := rfl

end MazurTransfer.IntertwiningMapKernelCoordinates
#print axioms MazurTransfer.IntertwiningMapKernelCoordinates.kernelRepresentation
#print axioms MazurTransfer.IntertwiningMapKernelCoordinates.kernelInclusion
#print axioms MazurTransfer.IntertwiningMapKernelCoordinates.kernelInclusion_injective
#print axioms MazurTransfer.IntertwiningMapKernelCoordinates.kernelInclusion_range
#print axioms MazurTransfer.IntertwiningMapKernelCoordinates.kernelRestriction
#print axioms MazurTransfer.IntertwiningMapKernelCoordinates.kernelRestriction_apply


