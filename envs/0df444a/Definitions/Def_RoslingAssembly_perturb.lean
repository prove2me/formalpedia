-- Prove2me | Definitions.Def_RoslingAssembly_perturb
-- name    : RoslingAssembly_perturb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:43:15.097441+00:00
-- url     : https://prove2.me/theorems/4c4c18b2-5243-4273-8ae7-3dcb9b360302
-- title:
--   The perturbed policy of the proof of Theorem 4(i)
-- statement:
--   Fix an item $i$, let $S=\{i\}\cup B(i)$ and $M_m=\max_{k\in S}M_k$, and let $n$ be a real number. The **perturbed policy** orders $n$ more units of every item $k\in S$ in period $M_m-M_k+1$ than the policy $\pi$ and keeps them forever:
--   $$Y'_{kt}=Y_{kt}+n\cdot\mathbf 1\big[k\in S,\ t\ge M_m-M_k+1\big].$$
--   The component with the greatest total lead time is ordered in period 1; item $i$ in period $M_m-M_i+1$. For $n=1$ this is the "alternative policy" of the proof of Theorem 4(i).
--
--   **Formalization Note** The Lean decision index $t$ is paper period $t+1$. The paper adds one unit; $n$ units give the unbounded family used to conclude.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, Appendix B, Proof of Theorem 4, p. 578

import Mathlib
import Definitions.Def_RoslingAssembly_Network_B
import Definitions.Def_RoslingAssembly_Network_M

namespace RoslingAssembly

/-- **The perturbed policy of the proof of Theorem 4(i)** (Appendix B, p. 578). Rosling, *Optimal
Inventory Policies for Assembly Systems under Random Demands*, Operations Research 37(4), 1989,
Appendix B, Proof of Theorem 4, p. 578 (unnumbered): "Consider the subsystem {i} ∪ B(i) … Then
consider an alternative policy that orders one more unit in period 1 of the component, m, with
the greatest total lead-time M_m, in period M_m − M_l + 1 of the component, l, with the next to
the greatest total lead-time and so on, so that one more unit is ordered of item i in period
M_m − M_i + 1. This additional unit is held in stock forever."

Let `S = {i} ∪ B(i)` and `M_m = max_{k ∈ S} M_k`. `perturb net ℓ pol i n` raises the echelon
position of every `k ∈ S` by `n` from paper period `M_m − M_k + 1` on (`n` more units of `k` are
ordered in that period and kept forever) and leaves everything else as in `pol`:
$$Y'_{kt}=Y_{kt}+n\cdot\mathbf 1[k\in S,\ t\ge M_m-M_k+1].$$

**Formalization Note.** Lean decision index `t` is paper period `t + 1`, so the condition is
`M_m − M_k + 1 ≤ t + 1`; the natural subtraction is exact because `M_k ≤ M_m` for `k ∈ S`. The
paper adds one unit; `n` units (any real `n`, nonnegative where used) give the unbounded family
of the proof. Items are `Fin N`, 0-based. -/
noncomputable def perturb {N : ℕ} (net : Network N) (ℓ : Fin N → ℕ)
    (pol : ℕ → (ℕ → ℝ) → Fin N → ℝ) (i : Fin N) (n : ℝ) : ℕ → (ℕ → ℝ) → Fin N → ℝ :=
  fun t ω k =>
    pol t ω k +
      if k ∈ insert i (net.B i) ∧
          (insert i (net.B i)).sup' (Finset.insert_nonempty _ _) (net.M ℓ) - net.M ℓ k + 1 ≤ t + 1
      then n else 0

end RoslingAssembly


