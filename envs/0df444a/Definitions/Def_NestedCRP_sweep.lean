-- Prove2me | Definitions.Def_NestedCRP_sweep
-- name    : NestedCRP_sweep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:46.198183+00:00
-- url     : https://prove2.me/theorems/7fa6bc03-3628-4ccb-ba14-013e2095d605
-- title:
--   Site kernels and one sweep of the collapsed Gibbs sampler
-- statement:
--   The level kernel at site $s_0$ moves a state $x$ to the state with the level of $s_0$ set to $k$, with probability
--
--   $$
--   \frac{\mathrm{levelWeight}(k)}{\sum_{k'}\mathrm{levelWeight}(k')},
--   $$
--
--   all else fixed. The path kernel of document $d$ moves $x=(T,z)$ to $(T',z)$, for a tree $T'$ with the same restriction to the other documents, with probability proportional to the path weight of $T'$. One sweep runs, for $d=0,\dots,D-1$ in order, the path kernel of $d$ and then the level kernels of $(d,0),\dots,(d,N_d-1)$, composed as transition functions. These are steps (a) and (b) of §5.3.
--
--   **Formalization Note** The kernels are the closed forms of Eqs. (2) and (4), never abstract conditional laws, so their invariance is a theorem. The level draw is exact over all levels $k\in\mathbb N$: the staged Bernoulli recipe of §5.1 (p.7:17) is false as printed and is not this kernel. The transition functions are real-valued, as in `MarkovMixing.IsStationaryC`.
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §5.3, p.7:17

import Mathlib
import Definitions.Def_NestedCRP_levelWeight
import Definitions.Def_NestedCRP_pathWeight

namespace NestedCRP

variable {V D : ℕ}

open Classical in
/-- Site update of step (b): from `x`, draw `z_{d,n}` from Eq. (2), keeping everything else fixed.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.3, step (b), p.7:17.

**Formalization Note** The kernel is the closed form of Eq. (2), never an abstract conditional law.
The draw is exact over all levels `k : ℕ`: the staged Bernoulli recipe of §5.1 (p.7:17) is false
as printed and is not this kernel. -/
noncomputable def levelKernel (H : Hyper) (C : Corpus V D) (s₀ : C.Site) (x y : C.State) : ℝ :=
  if y.1 = x.1 ∧ ∀ s : C.Site, s ≠ s₀ → y.2 s.1 s.2 = x.2 s.1 s.2 then
    levelWeight H C x s₀ (y.2 s₀.1 s₀.2) / ∑' k, levelWeight H C x s₀ k
  else 0

open Classical in
/-- Path update of step (a): from `x`, draw the path of document `d` from Eq. (4), that is, a tree
with the same restriction to the other documents, keeping the levels fixed.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.3, step (a), p.7:17.

**Formalization Note** The kernel is the closed form of Eq. (4), never an abstract conditional law.
The sum runs over the countably many trees that agree with `x.1` off `d`. -/
noncomputable def pathKernel (H : Hyper) (C : Corpus V D) (d : Fin D) (x y : C.State) : ℝ :=
  if y.2 = x.2 ∧ x.1.AgreesOff d y.1 then
    pathWeight H C x.2 d y.1 / ∑' T' : {T' : Tree D // x.1.AgreesOff d T'}, pathWeight H C x.2 d T'.1
  else 0

/-- Composition of transition functions: first `P`, then `Q`. -/
noncomputable def compK {S : Type*} (P Q : S → S → ℝ) (x y : S) : ℝ :=
  ∑' z, P x z * Q z y

open Classical in
/-- The identity transition function. -/
noncomputable def idK {S : Type*} (x y : S) : ℝ :=
  if y = x then 1 else 0

/-- The part of one sweep that handles document `d`: step (a), then step (b) for each word
`n = 0, …, N d − 1`. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.3, p.7:17. -/
noncomputable def docKernel (H : Hyper) (C : Corpus V D) (d : Fin D) : C.State → C.State → ℝ :=
  (List.finRange (C.N d)).foldl (fun K n => compK K (levelKernel H C ⟨d, n⟩)) (pathKernel H C d)

/-- One sweep of the Gibbs sampler: documents `d = 0, …, D − 1` in order.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.3, p.7:17. -/
noncomputable def sweep (H : Hyper) (C : Corpus V D) : C.State → C.State → ℝ :=
  (List.finRange D).foldl (fun K d => compK K (docKernel H C d)) idK

end NestedCRP


