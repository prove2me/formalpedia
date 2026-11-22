-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
-- name    : Formalism_RealPlaceAnalysis_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:54.953942+00:00
-- url     : https://prove2.me/theorems/b73a67c1-9c8a-4656-a213-c15b81e8b58b
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/StatementC.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.REAL
def cyc {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  sInf {W : Submodule ℂ V | v ∈ W ∧ ∀ a b, ∀ x ∈ W, E a b x ∈ W}
def cval {n : ℕ} (ν : Fin n → ℂ) : ℂ :=
  ∑ a, ν a ^ 2 + ∑ a, ∑ b ∈ univ.filter (fun b => a < b), (ν a - ν b)
def chamber {n : ℕ} (G : Fin n → Fin n → ℤ) : Set (Fin n → ℤ) :=
  {m | ∀ a b, a < b → G a b ≤ m a - m b}
def CasHW : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v → Cas E v = cval ν • v
def CasCyc : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ x ∈ cyc E v, Cas E x = cval ν • x
def CharId : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ x ∈ cyc E v, ∀ a b : Fin n,
      ∑ i ∈ range (n + 1),
        (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a b x = 0
def DegVand : Prop :=
  ∀ (n : ℕ) (c : ℂ) (G : Fin n → Fin n → ℤ) (f : (Fin n → ℤ) → ℂ),
    (∀ a b, a < b → 1 ≤ G a b) →
    (∀ (m : Fin n → ℤ) (s : Fin n), m ∈ chamber G → m - Pi.single s 1 ∈ chamber G →
      f (m - Pi.single s 1) = Dfac (fun a => c + (m a : ℂ)) s * f m) →
    ∀ m m', m ∈ chamber G → m' ∈ chamber G →
      f m * vand (fun a => c + (m' a : ℂ)) = f m' * vand (fun a => c + (m a : ℂ))
end Formalism.REAL


