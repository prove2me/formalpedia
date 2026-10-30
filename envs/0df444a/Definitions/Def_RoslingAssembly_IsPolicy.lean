-- Prove2me | Definitions.Def_RoslingAssembly_IsPolicy
-- name    : RoslingAssembly_IsPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:35:11.736407+00:00
-- url     : https://prove2.me/theorems/720a83e7-ae20-43d9-a557-8c2089c6b972
-- title:
--   Policy for problem P: non-anticipating, measurable ordering decisions
-- statement:
--   In each period $t=1,2,\dots$, first outstanding orders arrive and new orders are placed, then the period's demand $\xi_t$ for the end item occurs. A **policy** chooses the echelon inventory positions $Y_{1t},\dots,Y_{Nt}$ after ordering in period $t$ as a function of the history; the history beyond the fixed pre-horizon data consists of the demands $\xi_1,\dots,\xi_{t-1}$ of the earlier periods. We require:
--   1. **non-anticipation**: $Y_{\cdot t}$ depends on the demand path only through $\xi_1,\dots,\xi_{t-1}$;
--   2. **measurability**: each $Y_{it}$ is a measurable function of the demand path.
--
--   These are the paper's "decisions $Y_{it}$, dependent on system history up to period $t$".
--
--   **Formalization Note** A policy is a function `pol t ω i`; `ω : ℕ → ℝ` is the demand path with `ω j` $=\xi_{j+1}$, and `pol t ω` is the decision of paper period $t+1$. Policies are deterministic.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, pp. 566–567

import Mathlib

namespace RoslingAssembly

/-- **Policy for problem P** (§1, p. 567). Rosling, *Optimal Inventory Policies for Assembly
Systems under Random Demands*, Operations Research 37(4), 1989, p. 567 (unnumbered): "the problem
may be stated as finding decisions Y_it, dependent on system history up to period t, that solve
problem P."; p. 566: "Everything occurs at the beginning of periods and in the following order.
First, outstanding orders for purchase and assembly arrive and new ordering decisions are made.
Then, old backlogs are expedited and, thereafter, customer demands occur for the end product."

A policy is `pol : ℕ → (ℕ → ℝ) → Fin N → ℝ`. Here `ω : ℕ → ℝ` is a demand path, `ω j` being the
demand ξ_{j+1} of paper period `j + 1`, and `pol t ω i` is the decision `Y_{i,t+1}` of paper
period `t + 1`. `IsPolicy pol` says:
1. *non-anticipation*: `pol t ω` depends only on `ω 0, …, ω (t − 1)`, i.e. on the demands
   ξ_1, …, ξ_t of the periods before `t + 1` (the decision of a period is made before that
   period's demand occurs);
2. *measurability*: each `ω ↦ pol t ω i` is measurable for the product σ-algebra on `ℕ → ℝ`.

**Formalization Note.** Lean decision index `t` is paper period `t + 1`. Policies are
deterministic functions of the observed demands (the pre-horizon history is fixed data, so it
needs no argument). Items are `Fin N`, 0-based. -/
def IsPolicy {N : ℕ} (pol : ℕ → (ℕ → ℝ) → Fin N → ℝ) : Prop :=
  (∀ (t : ℕ) (ω ω' : ℕ → ℝ), (∀ j < t, ω j = ω' j) → pol t ω = pol t ω') ∧
    ∀ (t : ℕ) (i : Fin N), Measurable (fun ω => pol t ω i)

end RoslingAssembly


