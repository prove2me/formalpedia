-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:40.31271+00:00
-- url     : https://prove2.me/theorems/0fddf7d8-8bc1-468f-8972-38e3b4ef70e4
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/StatementC.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
def kapC (p n d : ℕ) : ℕ := n.choose 2 * Nat.log p (d + n - 1)
def FockAdj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (c d : Fin r)
    (F G : MvPolynomial (Fin N × Fin r) ℚ_[p]), fock p (glAct p LL j c d F) G = fock p F (glAct p LL j d c G)
def SpanIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)),
    (⨆ la : Fin r → ℤ, IsoC p LL j Cs la) = ⊤
def OrthIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la mu : Fin r → ℤ),
    (∃ c ∈ Cs, la c ≠ mu c) → ∀ x ∈ IsoC p LL j Cs la, ∀ y ∈ IsoC p LL j Cs mu, fock p x y = 0
def ProjP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ)),
    CsSaturated Cs T → ∃ P, IsTypeProj p LL j Cs T P ∧ ∀ F G, fock p (P F) G = fock p F (P G)
def CommP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j j' : ℕ) (Cs Cs' : Finset (Fin r))
    (T T' : Set (Fin r → ℤ)) (P P'), j ≤ j' → Cs' ⊆ Cs →
    IsTypeProj p LL j Cs T P → IsTypeProj p LL j' Cs' T' P' → P ∘ₗ P' = P' ∘ₗ P
def IntP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ)) (P),
    CsSaturated Cs T → IsTypeProj p LL j Cs T P →
    ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ kapC p Cs.card LL.total) • P F ∈ IntPol p (Fin N × Fin r)
def WeylP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N), HypW p (r := r) LL (kapC p r LL.total)
def ExtP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r), HypE p LL ρ (kapC p (r - 1) LL.total)
end Formalism.InvariantFactorPaths.PW


