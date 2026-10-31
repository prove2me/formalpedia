-- Prove2me | Definitions.Def_MaskedLinx_linx
-- name    : MaskedLinx_linx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:53.431128+00:00
-- url     : https://prove2.me/theorems/9e244ff7-54dc-499c-985a-7920b8936bdf
-- title:
--   Scaled linx bound $\mathrm{linx}(C,s;\gamma)=\max\{f(C,s;\gamma;x): x\in P(n,s)\}$
-- statement:
--   For a real square matrix $C$ indexed by a finite set $N$ with $|N|=n$, a natural number $s$ and a scaling parameter $\gamma>0$, the scaled linx bound is
--
--   $$\mathrm{linx}(C,s;\gamma)=\max\{f(C,s;\gamma;x) : x\in P(n,s)\},$$
--
--   the maximum of the scaled linx objective over the feasible set. Three special cases appear in the paper:
--
--   1. the linx bound (1) of Anstreicher, $\mathrm{linx}(C,s)=\mathrm{linx}(C,s;1)$;
--   2. the scaled linx bound (2), $\mathrm{linx}(C,s;\gamma)$;
--   3. the scaled and masked linx bound (3), $\mathrm{linx}(C,s;M,\gamma)=\mathrm{linx}(C\circ M,s;\gamma)$, for a mask $M$ (a positive semidefinite matrix with unit diagonal).
--
--   For a covariance matrix $C$ the linx bound is an upper bound on the maximum-entropy sampling value $\max\{\mathrm{ldet}\,C[S,S]: |S|=s\}$.
--
--   **Formalization Note** The maximum is written as the supremum in `EReal` over $P(n,s)$. For $0\le s\le n$ the feasible set is nonempty and compact and the objective is upper semicontinuous, so the supremum is attained. An empty feasible set ($s>n$) gives $-\infty$.
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, displays (1) and (2), p.2, and display (3), p.3

import Mathlib
import Definitions.Def_MaskedLinx_feasibleSet
import Definitions.Def_MaskedLinx_linxObjective

namespace MaskedLinx

/-- **The scaled linx bound `linx(C,s;γ) := max{f(C,s;γ;x) : x ∈ P(n,s)}`.**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, display (2), p.2. The unscaled bound (1), `linx(C,s)`, is `linx C s 1`;
the scaled and masked bound (3), p.3, `linx(C,s;M,γ)`, is `linx (C ⊙ M) s γ`.

**Formalization Note.** The paper's `max` is written as the supremum in `EReal` over the
feasible set `P(n,s)`; for `0 ≤ s ≤ |ι|` the set is nonempty and compact and the objective is
upper semicontinuous, so the supremum is attained and equals the paper's maximum. An empty
feasible set (`s > |ι|`) gives `⊥`. -/
noncomputable def linx {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (s : ℕ) (γ : ℝ) : EReal :=
  ⨆ x ∈ feasibleSet ι s, linxObjective C s γ x

end MaskedLinx


