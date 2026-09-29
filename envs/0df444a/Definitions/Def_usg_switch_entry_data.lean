-- Prove2me | Definitions.Def_usg_switch_entry_data
-- name    : usg_switch_entry_data
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-09-22T23:08:45.228751+00:00
-- url     : https://prove2.me/theorems/b05e0320-5abc-475b-a8da-5f11a4e141e6
-- title:
--   Occupation potential and swap rates for the three-state switch
-- statement:
--   For a configuration c, let N(c) count occupied sites and B(c) count vacuum/occupied boundary edges in both directions. Its potential is
--
--   $$V_a(c)=aN(c)+B(c).$$
--
--   The transition rate W_b(c,c′) is b times the number of horizontal edges with distinct occupied spins whose transposition transforms c into c′. These explicit finite counts express the switch Hamiltonian as a diagonal potential plus a weighted configuration-graph Laplacian. They introduce no spectral assertions.
-- source:
--   Original auxiliary specialization of the vacuum/occupied-sector construction in Cubitt–Pérez-García–Wolf, arXiv:1502.04573v5, Section 6.2, equations (130a)–(130d); the occupied-row interaction is twice the spin-1/2 Hamiltonian in Napiórkowski–Seiringer, doi:10.1007/s11005-021-01375-4, equation (2.1). Explicit computational-basis expansion: each occupied unequal-spin horizontal edge contributes the 2-by-2 Laplacian [[1,-1],[-1,1]], and each vacuum/occupied edge contributes one to the diagonal.

import Definitions.Def_usg_three_state_switch

set_option autoImplicit false
namespace UndecidableSpectralGap

def switchOccupiedCount (L : ℕ) (c : Config L 3) : ℕ :=
  (Finset.univ.filter fun p : Site L => c p ≠ 0).card

def switchBoundaryAt {L : ℕ} (c : Config L 3) (e : Site L × Site L) : Prop :=
  (c e.1 = 0 ∧ c e.2 ≠ 0) ∨ (c e.1 ≠ 0 ∧ c e.2 = 0)

instance {L : ℕ} (c : Config L 3) (e : Site L × Site L) :
    Decidable (switchBoundaryAt c e) := inferInstanceAs (Decidable
      ((c e.1 = 0 ∧ c e.2 ≠ 0) ∨ (c e.1 ≠ 0 ∧ c e.2 = 0)))

def switchBoundaryCount (L : ℕ) (c : Config L 3) : ℕ :=
  ((rowEdges L).filter (switchBoundaryAt c)).card +
    ((colEdges L).filter (switchBoundaryAt c)).card

def switchPotential (L : ℕ) (a : ℝ) (c : Config L 3) : ℝ :=
  a * (switchOccupiedCount L c : ℝ) + (switchBoundaryCount L c : ℝ)

def switchTransitionRate (L : ℕ) (b : ℝ) (c c' : Config L 3) : ℝ :=
  b * (((rowEdges L).filter fun e =>
    c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧
      c' = c ∘ Equiv.swap e.1 e.2).card : ℝ)

end UndecidableSpectralGap


