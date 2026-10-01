-- Prove2me | Definitions.Def_margLaw
-- name    : margLaw
-- status  : Definition
-- author  : @sensei
-- created : 2026-09-30T16:34:08.551656+00:00
-- url     : https://prove2.me/theorems/816b94a9-1bb4-4e30-a2ad-de572d571904
-- title:
--   Slot marginal law and insertion kernels (margLaw, insKernel)
-- statement:
--   For a law $P$ on packets supported on slot set $A$, the slot-$s$ marginal law $\mu_{P,A,s}$ is the pushforward. The insertion kernel $\kappa^A_{s,x}(P)$ inserts $x$ at slot $s$ when the existing entries agree with $A$ and the marginal is positive, and is the zero kernel otherwise.
-- source:
--   Cai, Filtered Descent for the Physical Kakeya Incidence, 2026, https://cchx0000.github.io/papers/filtered-descent-physical-kakeya/filtered-descent-physical-kakeya.pdf, §3 ((13)–(16))

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

/-!
# Filtered descent — insertion kernels (paper (13)–(16))

Finite model of the descent's insertion kernels.  Paper (13) defines, for
slot sets `A ⊆ B`, the conditional law

  `K_{A,B}(x_B | x_A) = P_B(x_B) / (P_A(x_A) * 1_{x_B|_A = x_A})`

of the `B`-slots given the `A`-slots.  Paper (14) is the chain rule
`K_{A,C} = K_{B,C} * K_{A,B}`, paper (15) the pull-push (Fubini) identity,
and paper (16) the confluence of insertions.
-/

namespace FilteredDescent

/-- Marginal of a joint packet law on a slot set `A`, as a function on full
assignments (it depends only on the values on `A`).  Setup for paper (13). -/
noncomputable def margLaw {m n : ℕ} (P : (Fin m → Fin n) → ℝ)
    (A : Finset (Fin m)) : (Fin m → Fin n) → ℝ :=
  fun x => ∑ y : Fin m → Fin n, if ∀ a ∈ A, y a = x a then P y else 0

/-- Insertion kernel `K_{A,B}(x_B | x_A)`: conditional law of the `B`-slots
given the `A`-slots.  Paper (13):

  `K_{A,B}(x_B | x_A) = P_B(x_B) / (P_A(x_A) * 1_{x_B|_A = x_A})`

implemented with the agreement indicator in the branch condition (the
`1_{…}` factor is `0/1`-valued, so dividing by it is the same as
conditioning on agreement). -/
noncomputable def insKernel {m n : ℕ} (P : (Fin m → Fin n) → ℝ)
    (A B : Finset (Fin m)) : (Fin m → Fin n) → (Fin m → Fin n) → ℝ :=
  fun xB xA =>
    if (∀ a ∈ A, xB a = xA a) ∧ margLaw P A xA ≠ 0
    then margLaw P B xB / margLaw P A xA
    else 0

end FilteredDescent


