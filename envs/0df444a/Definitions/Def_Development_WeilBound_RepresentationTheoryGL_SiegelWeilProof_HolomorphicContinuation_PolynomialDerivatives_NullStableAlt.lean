-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:15.838536+00:00
-- url     : https://prove2.me/theorems/219a799e-7d40-453c-b06d-a16517cb7313
-- title:
--   Null Stable Alt
-- statement:
--   Definitions and structural lemmas for Null Stable Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullStableAlt.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FockMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
def FockBasic : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → IsLinearMap ℂ (fock (m := m) (n := n) c) ∧ Function.Bijective (fock (m := m) (n := n) c) ∧
    ∀ k (p : PX m n), fock c (X k * p) = cr c k (fock c p)
def FockHOp : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ (a b : Fin m) (p : PX m n),
    hOp ε c a b (fock c p) = fock c (Dop ε c a b p)
def FockMom : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → mom (m := m) (n := n) c 1 ≠ 0 ∧ ∀ p : PX m n, mom c (fock c p) = mom c (1 : PX m n) * contr c p
def NullStable : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ (i j : Fin n) (P : PX m n), NullSec ε c P →
    NullSec ε c (lapS ε c i j P) ∧ NullSec ε c (eulH c i j P) ∧ NullSec ε c (eulA c i j P) ∧ NullSec ε c (mulQ ε i j P)
def FockK : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∃ a₁ a₂ a₃ a₄ a₅ : ℂ, ∀ (i j : Fin n) (p : PX m n),
    fock c (KopL ε i j p) = a₁ • mulQ ε i j (fock c p) + a₂ • lapS ε c i j (fock c p) + a₃ • eulH c i j (fock c p) +
      a₄ • eulA c i j (fock c p) + (if i = j then a₅ else 0) • fock c p
def CoreLC : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ Λ : PX m n →ₗ[ℂ] ℂ, (∀ a b p, Λ (Dop ε c a b p) = 0) →
    ∀ p, ∃ w ∈ kAlg ε, Λ p = contr c (w p)
end PositivityTheory.Rg.Sw.LC


