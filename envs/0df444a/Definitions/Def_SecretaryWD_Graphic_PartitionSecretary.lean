-- Prove2me | Definitions.Def_SecretaryWD_Graphic_PartitionSecretary
-- name    : SecretaryWD_Graphic_PartitionSecretary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:07:19.256988+00:00
-- url     : https://prove2.me/theorems/f650daf3-ecdd-4fa0-9dd2-db902e8ac102
-- title:
--   The per-part classical secretary algorithm and its expected value
-- statement:
--   This file defines the online algorithm used in Theorem 5.4 and Theorem 1.5.
--
--   Number the edges of the finite edge set $E$ as $0,\dots,|E|-1$ by a fixed enumeration. An arrival order is a permutation $\pi$ of these numbers: the edge numbered $\pi(t)$ arrives at time $t$.
--
--   Given a family $P$ of parts, the algorithm treats each part $p$ separately. The edges of $p$ arrive at certain times; the algorithm runs the classical secretary rule on this subsequence of arrivals, ranking edges by the tie-break order (larger value first, and among equal values the smaller edge number first). Each run selects at most one edge of $p$. Edges in no part are never selected. The output is the set of all selected edges, and its value is
--   $$\mathrm{ALG}(P,\pi)=\sum_{e \text{ selected}} v(e).$$
--   Every decision depends only on the edges that have arrived so far, so the algorithm is online.
--
--   For a random partition $\mu$, drawn independently of the order, the expected value of the algorithm is
--   $$\mathbb E[\mathrm{ALG}]=\mathbb E_{P\sim\mu}\Big[\frac{1}{|E|!}\sum_{\pi}\mathrm{ALG}(P,\pi)\Big].$$
--
--   **Formalization Note.** Times are $0$-based. The fixed enumeration of $E$ serves only to index the uniform order and to break ties consistently. The partition is known to the algorithm before the first arrival, as in the paper's reduction, where the matroid is known in advance.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 10, proof of Theorem 5.4 ("just run the classical secretary algorithm on each set in the partition")

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_ClassicalSecretary
import Definitions.Def_SecretaryWD_Graphic_GraphicMatroid

namespace SecretaryWD.Graphic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `E` are numbered `0, …, |E| - 1` by a fixed enumeration; `edgeAt E j` is the
edge with number `j`. Arrival orders permute these numbers, and the tie-break prefers the smaller
number among equal values. -/
noncomputable def edgeAt (E : Finset (Sym2 V)) (j : Fin E.card) : Sym2 V :=
  (E.equivFin.symm j).1

/-- The arrival times of the edges of the part `p`, when the edges of `E` arrive in the order
`π` (time `t` brings the edge numbered `π t`). -/
noncomputable def partTimes (E : Finset (Sym2 V)) (π : Equiv.Perm (Fin E.card))
    (p : Finset (Sym2 V)) : Finset (Fin E.card) :=
  Finset.univ.filter fun t => edgeAt E (π t) ∈ p

/-- The time of the `i`-th arrival (0-based) among the edges of the part `p`. -/
noncomputable def partArrivalTime (E : Finset (Sym2 V)) (π : Equiv.Perm (Fin E.card))
    (p : Finset (Sym2 V)) (i : Fin (partTimes E π p).card) : Fin E.card :=
  (partTimes E π p).orderEmbOfFin rfl i

/-- The edge selected in the part `p` (if any): the classical secretary rule run on the arrivals
of the part's edges, in arrival order, ranked by the tie-break key `(v e, edge number)`. -/
noncomputable def partSelection (E : Finset (Sym2 V)) (v : Sym2 V → ℝ)
    (π : Equiv.Perm (Fin E.card)) (p : Finset (Sym2 V)) : Option (Sym2 V) :=
  (SecretaryWD.DiscUpper.classicalSecretary (partTimes E π p).card fun i =>
      SecretaryWD.DiscUpper.tieKey (fun j => v (edgeAt E j)) (π (partArrivalTime E π p i))).map
    fun i => edgeAt E (π (partArrivalTime E π p i))

/-- The output of the per-part algorithm (proof of Theorem 5.4, p. 10) for the partition `P` and
the arrival order `π`: the set of edges selected in the parts. Edges in no part are never
selected. -/
noncomputable def partitionSecretaryOutput (E : Finset (Sym2 V)) (v : Sym2 V → ℝ)
    (P : Finset (Finset (Sym2 V))) (π : Equiv.Perm (Fin E.card)) : Finset (Sym2 V) :=
  P.biUnion fun p => (partSelection E v π p).toFinset

/-- The value of the per-part algorithm's output. -/
noncomputable def partitionSecretaryValue (E : Finset (Sym2 V)) (v : Sym2 V → ℝ)
    (P : Finset (Finset (Sym2 V))) (π : Equiv.Perm (Fin E.card)) : ℝ :=
  ∑ e ∈ partitionSecretaryOutput E v P π, v e

/-- The expected value of the algorithm that draws the partition `P ∼ μ` (independently of the
order), lets the edges of `E` arrive in a uniformly random order, and runs the per-part
algorithm: `E_{P∼μ} E_π [value]`. -/
noncomputable def expectedAlgValue (E : Finset (Sym2 V)) (v : Sym2 V → ℝ)
    (μ : PMF (Finset (Finset (Sym2 V)))) : ℝ :=
  pmfExp μ fun P => SecretaryWD.DiscUpper.uniformAvg fun π => partitionSecretaryValue E v P π

end SecretaryWD.Graphic


