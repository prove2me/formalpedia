-- Prove2me | Definitions.Def_AvoidPlast_IsNTimeVerifier
-- name    : AvoidPlast_IsNTimeVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:47.413315+00:00
-- url     : https://prove2.me/theorems/12e0a094-c643-4890-bdc3-ba694a76ed0a
-- title:
--   $L\in\mathrm{NTIME}[t(n)]$
-- statement:
--   A language $L$ is in $\mathrm{NTIME}[t(n)]$, witnessed by a deterministic verifier $V_0$ with read-only tapes for $x$ and $w$: $V_0$ halts within $C(t(n)+1)$ steps, and $x\in L$ if and only if some $w$ with $|w|\le C(t(n)+1)$ is accepted.
--
--   **Formalization Note** Jumps are allowed: this is the paper's RAM model (reading R5), where sublinear time makes sense. The bound is an integer so that a machine can check it.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 4.2, p.18

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Accepts

namespace AvoidPlast

/-- `L ∈ NTIME[t(n)]` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §4.2, p.18): a deterministic verifier `V₀` with read-only tapes for `x` and
the witness `w`, running in time `C · (t(n) + 1)`, with `x ∈ L ⟺ ∃ w`, `|w| ≤ C · (t(n) + 1)`, accepted.

**Formalization Note** Jumps are allowed (reading R5): the paper works in the RAM model, which is what
makes sublinear time meaningful. The bound is on naturals, so that a machine can check it. -/
def IsNTimeVerifier (V₀ : Machine 2) (L : Set (List Bool)) (t : ℕ → ℕ) (C : ℕ) : Prop :=
  (∀ x w : List Bool, HaltsWithin V₀ ![x, w] (C * (t x.length + 1))) ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ w : List Bool, w.length ≤ C * (t x.length + 1) ∧ Accepts V₀ ![x, w]

end AvoidPlast


