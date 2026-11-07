-- Prove2me | Definitions.Def_KMeansTaper_IsDense
-- name    : KMeansTaper_IsDense
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:19.428317+00:00
-- url     : https://prove2.me/theorems/08e4172c-69a0-4bf0-bcfd-75ea92a8b9dd
-- title:
--   Balls, $A$-dense facilities and the sparsification family of Appendix F
-- statement:
--   Fix $\xi=1/3$ and $\delta=1/10$. For a point $i$ and $r>0$, $\mathrm{CBall}(i,r)$ is the set of clients and $\mathrm{FBall}(i,r)$ the set of facilities (of a facility set $F'$) at distance strictly less than $r$ from $i$. For an optimal set $\mathrm{OPT}$ and $A\in\mathbb R$, a facility $i$ is **$A$-dense** if
--
--   $$\bigl((1-\xi)\,d(i,\mathrm{OPT})\bigr)^2\,\bigl|\mathrm{CBall}(i,\xi\, d(i,\mathrm{OPT}))\bigr|>A,$$
--
--   and **$A$-sparse** otherwise. For $t\in\mathbb N$, the **sparsification family** consists of the facility sets $F'=F\setminus\bigcup_{x\le q}\mathrm{FBall}(i_x,d(i_x,i'_x))$ over all sequences of $q\le t$ facility pairs $(i_x,i'_x)$.
--
--   These are the objects of the squared Li–Svensson reduction (Lemma F.2).
--
--   **Formalization Note** The paper states density for $A>0$; the formula is the same for every real $A$.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Appendix F, p.42 (PDF p.45), Notation; Lemma F.2, p.43 (PDF p.46)

import Mathlib
import Definitions.Def_MetricKMedian

namespace KMeansTaper

open OAI.MetricKMedian (Instance nearest)

/-- `ξ = 1/3`, Appendix F, p.42 (PDF p.45).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b661022…fc5a3). -/
noncomputable def xiF : ℝ := 1 / 3

/-- `δ = 1/10`, Appendix F, p.42 (PDF p.45). -/
noncomputable def deltaF : ℝ := 1 / 10

/-- **Client ball** `CBall(i, r)`: the clients at distance strictly less than `r` from `i`
(Appendix F, Notation, p.42). -/
noncomputable def CBall (I : Instance) (i : Fin I.n) (r : ℝ) : Finset (Fin I.n) :=
  I.clients.filter (fun j => (I.distance i j : ℝ) < r)

/-- **Facility ball** `FBall(i, r)` of a (restricted) facility set `F'`: the facilities of `F'`
at distance strictly less than `r` from `i` (Appendix F, Notation, p.42). -/
noncomputable def FBall (I : Instance) (F' : Finset (Fin I.n)) (i : Fin I.n) (r : ℝ) :
    Finset (Fin I.n) :=
  F'.filter (fun f => (I.distance i f : ℝ) < r)

/-- **`A`-dense facility** (Appendix F, Notation, p.42): `i` is `A`-dense for the optimal set
`OPT` if `((1 - ξ) d(i, OPT))² |CBall(i, ξ d(i, OPT))| > A`; otherwise it is `A`-sparse.

**Formalization Note.** `d(i, OPT)` is `nearest I i OPT` (OPT is nonempty in every use). The
paper states the notion for `A > 0`; the definition is the same formula for every real `A`. -/
def IsDense (I : Instance) (OPT : Finset (Fin I.n)) (A : ℝ) (i : Fin I.n) : Prop :=
  A < ((1 - xiF) * nearest I i OPT) ^ 2 * ((CBall I i (xiF * nearest I i OPT)).card : ℝ)

/-- **Deleting facility balls** (Lemma F.2, p.43, PDF p.46): the facilities of `F` outside
every ball `FBall(i_x, d(i_x, i'_x))` for the pairs `(i_x, i'_x)` of the list. -/
noncomputable def deleteBalls (I : Instance) (pairs : List (Fin I.n × Fin I.n)) :
    Finset (Fin I.n) :=
  I.facilities.filter
    (fun f => ∀ pr ∈ pairs, ¬ ((I.distance pr.1 f : ℝ) < I.distance pr.1 pr.2))

/-- **The family of restricted facility sets of Lemma F.2**, p.43 (PDF p.46): `F'` obtained by
deleting the balls `FBall(i_x, d(i_x, i'_x))`, `x ≤ q`, for all sequences of `q ≤ t` pairs of
facilities `(i_x, i'_x)`. -/
noncomputable def sparsifyFamily (I : Instance) (t : ℕ) : Finset (Finset (Fin I.n)) :=
  (Finset.range (t + 1)).biUnion fun q =>
    ((Finset.univ : Finset (Fin q → Fin I.n × Fin I.n)).filter
        (fun v => ∀ x, (v x).1 ∈ I.facilities ∧ (v x).2 ∈ I.facilities)).image
      (fun v => deleteBalls I (List.ofFn v))

end KMeansTaper


