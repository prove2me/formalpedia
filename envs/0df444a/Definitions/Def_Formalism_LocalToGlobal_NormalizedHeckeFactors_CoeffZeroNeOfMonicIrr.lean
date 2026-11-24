-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
-- name    : Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:54:42.741258+00:00
-- url     : https://prove2.me/theorems/696776ad-ba7f-4223-9329-82db6ef741ed
-- title:
--   Coeff Zero Ne Of Monic Irr
-- statement:
--   Definitions and structural lemmas for Coeff Zero Ne Of Monic Irr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory
namespace Formalism.L2.NT
variable {g : ℕ} [Fact g.Prime]
def convC (ι : Formalism.CyclotomicNorms.Fbar g →* ℂ) (hι : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → ι x = ι y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) : LabelConv (ZMod g) where
  ι := ι
  ι_inj := hι
  gen := ζ
  gen_order d hd := by
    rw [ZMod.card]
    exact (hζ d hd).1
  gen_norm d e hd he := by
    rw [ZMod.card]
    exact (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)
def LabTwLawO {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K} (O : LabelMap K C) : Prop :=
  ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)) (x : K), 1 ≤ d → x ≠ 0 → Simple τ → IsCuspidal K τ → Simple τ' →
    IsCuspidal K τ' →
    (∀ (γ : GL (Fin d) K) (m : ℕ),
      C.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin d) (Fin d) K)) →
      LinearMap.trace ℂ τ' (τ'.ρ γ) = C.ι (algebraMap K (AlgebraicClosure K) x) ^ m * LinearMap.trace ℂ τ (τ.ρ γ)) →
    rootsBar K (O.lab d τ') = (rootsBar K (O.lab d τ)).map (· * algebraMap K (AlgebraicClosure K) x)
def eSerO {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) (r : ℕ) (f : (ZMod g)[X]) :
    MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) :=
  ∑ᶠ (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)))
    (_ : ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f), z
end Formalism.L2.NT
namespace Formalism.L2.PT
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
section Transp
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
end Transp
end Formalism.L2.PT
namespace Formalism.L2.NT
open Formalism.L2.PT
variable {g : ℕ} [Fact g.Prime]
end Formalism.L2.NT
end


