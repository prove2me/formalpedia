-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelSchemesData
-- name    : MazurTransfer_Order13ActualPicardNormKernelSchemesData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T21:19:59.690334+00:00
-- url     : https://prove2.me/theorems/a20b9469-555b-4baf-a124-fe8627d29fcb
-- title:
--   The two original actual Picard norm kernel schemes and their structural morphisms
-- statement:
--   Let P be the same actual rational represented Picard scheme, with the original norm endomorphisms pi and pi-bar and the original zero section over Q. Retain both kernel schemes as the fibre products of these morphisms with the zero section, and retain both structural maps to Spec Q. All four complete constructor types and values are compared to the originals; the same Picard group-object provider is compared as well. The named downstream consumers are the original finite-etale kernel theorems and actual norm-isogeny descent.
-- source:
--   Complete original MazurTheorem Order13ActualPicardNormFiniteEtaleIsogenies.piKernel, piKernelToQ, piConjugateKernel and piConjugateKernelToQ, retaining all four pullback constructors and structural morphisms. Uses the same actual rational Picard family and original norm factors; official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the kernels of the same actual norm endomorphisms and
both structural maps over Q, with their original pullback constructors.
Named downstream consumers: original piKernelToQ_finite_etale and
piConjugateKernelToQ_finite_etale; actual norm-isogeny descent.
Original MazurTheorem Order13ActualPicardNormFiniteEtaleIsogenies
constructors; official Anthropic FLT Picard interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
noncomputable section
namespace MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies
open CategoryTheory AlgebraicGeometry
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
def piKernel : Scheme := CategoryTheory.Limits.pullback schemePi.left actualPicard.zeroSection

def piKernelToQ : piKernel ⟶ Spec (CommRingCat.of ℚ) :=
  CategoryTheory.Limits.pullback.snd schemePi.left actualPicard.zeroSection

def piConjugateKernel : Scheme := CategoryTheory.Limits.pullback schemePiConjugate.left actualPicard.zeroSection

def piConjugateKernelToQ : piConjugateKernel ⟶ Spec (CommRingCat.of ℚ) :=
  CategoryTheory.Limits.pullback.snd schemePiConjugate.left actualPicard.zeroSection


end MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies
#print axioms MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.piKernel
#print axioms MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.piKernelToQ
#print axioms MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.piConjugateKernel
#print axioms MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.piConjugateKernelToQ


