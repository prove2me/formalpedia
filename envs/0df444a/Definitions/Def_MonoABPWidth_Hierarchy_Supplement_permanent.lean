-- Prove2me | Definitions.Def_MonoABPWidth_Hierarchy_Supplement_permanent
-- name    : MonoABPWidth_Hierarchy_Supplement_permanent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:35:11.88439+00:00
-- url     : https://prove2.me/theorems/3dd11697-e3db-4afe-8bbc-bcdbf9b2eed0
-- title:
--   Permanent, independent leaf optimum, and ordered-composition recurrence
-- statement:
--   For the generic real $n\times n$ matrix, define
--   $$\operatorname{per}_n=\sum_{\pi\in S_n}\prod_{i=1}^n x_{i,\pi(i)}.$$
--   The true optimum $\operatorname{Opt}(n,d)$ is the infimum of leaf counts of actual monotone trees computing this polynomial with multiplication depth exactly $d$. It is $+\infty$ if there is no feasible formula. This definition uses no recurrence.
--
--   Separately define the candidate function $L(n,1)=n\,n!$ and, for $d\ge2$,
--   $$L(n,d)=\min_{n=n_1+\cdots+n_\ell\atop \ell\ge1,\ n_i\ge1}\frac{n!}{\prod_i n_i!}\sum_i L(n_i,d-1).$$
--   Mathlib's finite type of ordered positive compositions supplies every decomposition, including a single part and unbalanced parts. The multinomial coefficient uses exact integer division. At depth zero set $L(n,0)=n$ for $n\le1$ and $+\infty$ otherwise, as in the proof. Only positive $n$ is used in the permanent theorems; the recurrence has an unused empty-composition extension at $n=0$. Finally $\ell_d(x)$ is the $(d-1)$-fold composition of natural logarithm. This separates the actual optimum from both the proposed recurrence and its claimed asymptotic.
-- source:
--   Julian Dörfler, Alexander Rogovskyy, STOC 2027 submission #927 (October 2026), §7, p.22, PDF23; Theorem 7.6 and proof, pp.22–24, PDF23–25

import Definitions.Def_MonoABPWidth_Hierarchy_Supplement_formulas

open scoped BigOperators ENNReal

namespace MonoABPWidth.Hierarchy.Supplement

/-- §7, p.22: the permanent of the generic real n×n matrix. -/
noncomputable def permanent (n : ℕ) : MvPolynomial (Fin n × Fin n) ℝ :=
  ∑ π : Equiv.Perm (Fin n), ∏ i : Fin n, MvPolynomial.X (i, π i)

/-- True optimum over actual formulas, independent of any recurrence. The empty
feasible set has infimum +infinity in ENNReal. -/
noncomputable def permanentOpt (n d : ℕ) : ℝ≥0∞ :=
  ⨅ F : {F : Formula (Fin n × Fin n) // F.eval = permanent n ∧ F.mulDepth = d},
    (F.val.leaves : ℝ≥0∞)

/-- The finite ordered-composition recurrence in Theorem 7.5, with d=0 extended
as on p.22. Composition n contains every ordered positive composition, including
the single part n for n>0. Its finite nonempty minimum never uses a default value. -/
noncomputable def permanentL : ℕ → ℕ → ℝ≥0∞
  | n, 0 => if n ≤ 1 then (n : ℝ≥0∞) else ⊤
  | n, 1 => (n * n.factorial : ℕ)
  | n, d + 2 => Finset.univ.inf' Finset.univ_nonempty (fun c : Composition n =>
      (n.factorial / (c.blocks.map Nat.factorial).prod : ℕ) *
        (c.blocks.map (fun m => permanentL m (d + 1))).sum)

/-- Composition of natural log (d−1) times, not a power or a change of base. -/
noncomputable def iteratedLog (d : ℕ) (x : ℝ) : ℝ := (Real.log^[d - 1]) x

end MonoABPWidth.Hierarchy.Supplement


