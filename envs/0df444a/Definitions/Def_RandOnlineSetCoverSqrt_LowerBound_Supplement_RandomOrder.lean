-- Prove2me | Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Supplement_RandomOrder
-- name    : RandOnlineSetCoverSqrt_LowerBound_Supplement_RandomOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:11:35.123982+00:00
-- url     : https://prove2.me/theorems/d20ad042-1ace-4166-a387-033153a36aef
-- title:
--   Random-order arrival: reordered instances, distinct requests and the order-averaged expected cost
-- statement:
--   In the **random-order model** of online set cover the set system is known in advance, the adversary fixes a *set* $E$ of $N$ distinct requested elements (and $N$ may be announced to the algorithm), and the elements of $E$ are revealed in a uniformly random order $\pi$, independent of the algorithm's internal randomness.
--
--   On the canonical known universe $U_m=\{u_A:\varnothing\ne A\subseteq[m]\}$ an element is identified with its nonempty incidence label $A$. A fixed input is a list $I=(A_1,\dots,A_N)$ of nonempty incidence labels (an instance of the published online set-cover model). This file defines:
--
--   1. the reordered instance $I\circ\pi=(A_{\pi(1)},\dots,A_{\pi(N)})$ for a permutation $\pi$ of $\{1,\dots,N\}$;
--   2. the predicate that $I$ lists $N$ **distinct** elements, i.e. $i\mapsto A_i$ is injective (no element is requested twice, so $I$ is a set $E$ of $N$ elements);
--   3. for a randomized algorithm $R$ (a probability distribution over valid deterministic online algorithms for horizon $N$), the **random-order expected cost**
--   $$\mathbb E_{\pi,R}\bigl[|X_N|\bigr]=\frac1{N!}\sum_{\pi\in S_N}\mathbb E_R\bigl[\operatorname{cost}(I\circ\pi)\bigr].$$
--
--   The average over orders is taken outside the algorithm's expectation, which makes the order independent of the algorithm's coins.
--
--   **Formalization Note** The algorithm class, its expected cost and the offline optimum are the published model's (`RandAlg`, `expectedCost`, `Opt`); only the permutation average and the distinctness predicate are new.
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, random-order model, §2, printed p. 7 / PDF p. 8

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Canonical

namespace RandOnlineSetCoverSqrt.LowerBound.Supplement

/-- Random-order online set cover, printed p. 7 / PDF p. 8: the requests of a fixed instance
revealed in the order `π`, i.e. the `i`-th arrival is the `π i`-th listed request. -/
def reorder {m N : ℕ} (I : RandOnlineSetCover.InfoLB.Instance m N) (π : Equiv.Perm (Fin N)) :
    RandOnlineSetCover.InfoLB.Instance m N :=
  ⟨fun i => I.val (π i), fun i => I.property (π i)⟩

/-- The adversary fixes a SET of `N` distinct elements: on the canonical universe `U_m` an
element is its nonempty incidence label, so distinctness is injectivity of the incidences. -/
def DistinctRequests {m N : ℕ} (I : RandOnlineSetCover.InfoLB.Instance m N) : Prop :=
  Function.Injective I.val

/-- `E_{π,A}[|X_N|]`: the uniform average over all `N!` arrival orders `π` of the algorithm's
expected cost; the order is independent of the algorithm's coins (product law). -/
noncomputable def randomOrderExpectedCost {m N : ℕ} (R : RandOnlineSetCover.InfoLB.RandAlg m N)
    (I : RandOnlineSetCover.InfoLB.Instance m N) : ℝ :=
  (∑ π : Equiv.Perm (Fin N), RandOnlineSetCover.InfoLB.expectedCost R (reorder I π)) /
    (Nat.factorial N : ℝ)

end RandOnlineSetCoverSqrt.LowerBound.Supplement


