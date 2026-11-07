-- Prove2me | Definitions.Def_KMeansTaper_IsSparseOutput
-- name    : KMeansTaper_IsSparseOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:28.401186+00:00
-- url     : https://prove2.me/theorems/b891134f-961f-4bea-b324-de3c52ca28d6
-- title:
--   The algorithm on a sparse instance (output relation)
-- statement:
--   Let $F'\subseteq F$ be a restricted facility set, $T\subseteq F'$, $\Gamma$ a threshold and $t\in\mathbb N$. The **algorithm on a sparse instance** runs:
--
--   1. $T'\leftarrow T$; while $|T'|>k$ and some $i\in T'$ (the first in the order of indices) has $\mathrm{cost}_2(T'\setminus\{i\})\le\mathrm{cost}_2(T')+\Gamma$, delete it.
--   2. If $|T'|\le k$, return $T'$.
--   3. Otherwise, for every $D\subseteq T'$ and $V\subseteq F'$ with $|D|+|V|=k$ and $|V|<t$: for $i\in D$ let $L_i=d(i,T'\setminus\{i\})$ and let $f_i\in\mathrm{FBall}(i,\delta L_i)$ minimize $\sum_{j\in\mathrm{CBall}(i,\xi L_i)}\min\{d(j,f)^2,d(j,V)^2\}$ (with $d(j,\emptyset)=\infty$); put $S_{D,V}=V\cup\{f_i:i\in D\}$. Return a cheapest $S_{D,V}$.
--
--   A set $S$ is an **output** if it is returned for some choice of the minimizers $f_i$ and of the cheapest pair.
--
--   **Formalization Note** Step (1) is a recursion with $|T|$ steps of fuel. Step (3) is a relation: an output exists for some selection of minimizers, so a statement about every output covers every tie-break.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Appendix F, "Algorithm on a sparse instance", p.43 (PDF p.46)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_cost2
import Definitions.Def_KMeansTaper_IsDense

namespace KMeansTaper

open OAI.MetricKMedian (Instance nearest)

open Classical in
/-- **Step (1) of the algorithm on a sparse instance**, Appendix F, p.43 (PDF p.46): starting
from `T' = T`, while `|T'| > k` and some `i ∈ T'` has `cost(T' \ {i}) ≤ cost(T') + Γ`, delete the
first such `i` (in the order of `Fin n`).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b661022…fc5a3).

**Formalization Note.** Written with a fuel argument; fuel `|T|` suffices since every step
deletes one facility. The cost of the restricted instance equals `cost2 I` (same clients and
distances). -/
noncomputable def prune (I : Instance) (Γ : ℝ) : ℕ → Finset (Fin I.n) → Finset (Fin I.n)
  | 0, T' => T'
  | fuel + 1, T' =>
    if h : I.k < T'.card ∧
        (T'.filter (fun i => cost2 I (T'.erase i) ≤ cost2 I T' + Γ)).Nonempty then
      prune I Γ fuel (T'.erase ((T'.filter (fun i => cost2 I (T'.erase i) ≤ cost2 I T' + Γ)).min' h.2))
    else T'

open Classical in
/-- **The ball cost minimized by `f_i`** in step (3), p.43:
`∑_{j ∈ CBall(i, ξ L_i)} min{d(j, f)², d(j, V)²}`, where `min{d(j, f)², d(j, ∅)²} = d(j, f)²`. -/
noncomputable def ballCost (I : Instance) (i : Fin I.n) (Li : ℝ) (V : Finset (Fin I.n))
    (f : Fin I.n) : ℝ :=
  ∑ j ∈ CBall I i (xiF * Li),
    (if V.Nonempty then min ((I.distance j f : ℝ) ^ 2) (nearest I j V ^ 2)
      else (I.distance j f : ℝ) ^ 2)

/-- **The output relation of the algorithm on a sparse instance**, Appendix F, p.43 (PDF p.46),
for the restricted facility set `F'`, the input set `T`, the threshold `Γ` and the parameter
`t`: with `T'` the result of step (1), either (2) `|T'| ≤ k` and `S = T'`, or (3) `|T'| > k` and,
for some choice of minimizers `f_i ∈ FBall(i, δ L_i)` of the ball cost (`L_i = d(i, T' \ {i})`),
one for every pair `(D, V)` with `D ⊆ T'`, `V ⊆ F'`, `|D| + |V| = k`, `|V| < t`, the set `S` is a
cheapest `S_{D,V} = V ∪ {f_i : i ∈ D}`.

**Formalization Note.** The choice of minimizers (`f`) and of the cheapest pair are
existentially quantified, so a statement about every output covers every tie-break. -/
def IsSparseOutput (I : Instance) (F' T : Finset (Fin I.n)) (Γ : ℝ) (t : ℕ)
    (S : Finset (Fin I.n)) : Prop :=
  ((prune I Γ T.card T).card ≤ I.k ∧ S = prune I Γ T.card T) ∨
  (I.k < (prune I Γ T.card T).card ∧
    ∃ f : Finset (Fin I.n) → Finset (Fin I.n) → Fin I.n → Fin I.n,
      (∀ D V : Finset (Fin I.n), D ⊆ prune I Γ T.card T → V ⊆ F' → D.card + V.card = I.k →
        V.card < t → ∀ i ∈ D,
          f D V i ∈ FBall I F' i (deltaF * nearest I i ((prune I Γ T.card T).erase i)) ∧
          ∀ g ∈ FBall I F' i (deltaF * nearest I i ((prune I Γ T.card T).erase i)),
            ballCost I i (nearest I i ((prune I Γ T.card T).erase i)) V (f D V i)
              ≤ ballCost I i (nearest I i ((prune I Γ T.card T).erase i)) V g) ∧
      ∃ D V : Finset (Fin I.n), D ⊆ prune I Γ T.card T ∧ V ⊆ F' ∧ D.card + V.card = I.k ∧
        V.card < t ∧ S = V ∪ D.image (f D V) ∧
        ∀ D' V' : Finset (Fin I.n), D' ⊆ prune I Γ T.card T → V' ⊆ F' →
          D'.card + V'.card = I.k → V'.card < t →
          cost2 I (V ∪ D.image (f D V)) ≤ cost2 I (V' ∪ D'.image (f D' V')))

end KMeansTaper


