-- Prove2me | Definitions.Def_Formalism_LogVandermondeBounds_GaussOperatorProductFormula
-- name    : Formalism_LogVandermondeBounds_GaussOperatorProductFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:56:07.532797+00:00
-- url     : https://prove2.me/theorems/91829d51-bcfc-4ca3-aa0e-9f1f14ffda76
-- title:
--   Gauss Operator Product Formula
-- statement:
--   Definitions and structural lemmas for Gauss Operator Product Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/GaussOperatorProductFormula.lean

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
section Ops
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}
def opGs (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (f : Fin r → k) : ℂ :=
  ∑ c : kˣ, ψ (c : k) * φ ((c : k) • f)
def opGsStar (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (f : Fin r → k) : ℂ :=
  ∑ c : kˣ, (starRingEnd ℂ) (ψ (c : k)) * φ (((c⁻¹ : kˣ) : k) • f)
def opFF (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (x : Fin r → k) : ℂ :=
  ∑ f ∈ univ.filter (fun f => f ≠ 0), ψ (pair f x) * φ f
end Ops
def GaussOperatorProductFormula : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ (φ : (Fin r → k) → ℂ) (f : Fin r → k),
      opGs ψ (opGsStar ψ φ) f = (Fintype.card k : ℂ) * φ f - nmP φ f
def FourierEqDownGauss : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ),
    ∀ (φ : (Fin r → k) → ℂ), (∀ f, f ≠ 0 → nmP φ f = 0) →
      ∀ x : Fin r → k, opFF ψ φ x = opD (opGs ψ φ) x
def FourierIsometryNormKernel : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ (φ φ' : (Fin r → k) → ℂ), (∀ f, f ≠ 0 → nmP φ f = 0) → (∀ f, f ≠ 0 → nmP φ' f = 0) →
      ∑ x ∈ univ.filter (fun x => x ≠ 0), (starRingEnd ℂ) (opFF ψ φ x) * opFF ψ φ' x =
        (Fintype.card k : ℂ) ^ r * ∑ f ∈ univ.filter (fun f => f ≠ 0), (starRingEnd ℂ) (φ f) * φ' f
def GaussOperatorAdjoint : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ) (φ φ' : (Fin r → k) → ℂ),
    ∑ f, (starRingEnd ℂ) (opGs ψ φ f) * φ' f = ∑ f, (starRingEnd ℂ) (φ f) * opGsStar ψ φ' f
def FourierIntertwinesDiagonal : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ),
    ∀ (φ : (Fin r → k) → ℂ) (c : kˣ), opFF ψ (diaP c φ) = diaV c (opFF ψ φ)
def FourierMapsNormKernel : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ),
    ∀ (φ : (Fin r → k) → ℂ), (∀ f, f ≠ 0 → nmP φ f = 0) →
      ∀ x : Fin r → k, x ≠ 0 → nmV (opFF ψ φ) x = 0
end Formalism.LogVandermondeBounds.product_first_zeroth_parts


