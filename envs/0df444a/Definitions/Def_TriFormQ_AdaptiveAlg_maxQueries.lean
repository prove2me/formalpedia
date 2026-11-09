-- Prove2me | Definitions.Def_TriFormQ_AdaptiveAlg_maxQueries
-- name    : TriFormQ_AdaptiveAlg_maxQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:10.323975+00:00
-- url     : https://prove2.me/theorems/94626478-d10a-4154-89ce-967c6eef3f36
-- title:
--   Worst-case number of queries of an adaptive algorithm on a given oracle
-- statement:
--   For an adaptive quantum query algorithm $A$ and an oracle function $g$, $\mathrm{maxQueries}(A,g)$ is the largest total number of oracle queries made along a run of $A$ with oracle $g$ whose measurement outcomes all have positive probability:
--
--   $$\mathrm{maxQueries}(\mathrm{halt},g)=0,\qquad \mathrm{maxQueries}(\mathrm{round}_T,g)=T+\max_{z:\ |\langle z|\psi_g\rangle|^2>0}\mathrm{maxQueries}(\mathrm{next}(z),g).$$
--
--   A statement "the algorithm makes at most $X$ queries to the oracle of $f$" is $\mathrm{maxQueries}(A,f)\le X$: a worst-case bound on every run that can occur on that oracle, not an expectation.
--
--   **Formalization Note** A copy of the platform's `QAlgorithms.AdaptiveQueryAlg.maxQueries` (08848af9) for oracles valued in a finite additive group.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 1, p.3 (PDF p.6)

import Definitions.Def_TriFormQ_AdaptiveAlg

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 1, p.3 (PDF p.6): "makes
at most … queries to the oracle". The largest total number of oracle queries over the
measurement transcripts of positive probability when the oracle is `g`.

**Formalization Note.** A worst-case count on the oracle actually queried, not an expectation:
every run of positive probability on `g` makes at most `maxQueries A g` queries. It is a copy of
the platform's `QAlgorithms.AdaptiveQueryAlg.maxQueries` (08848af9) for an oracle valued in `κ`. -/
noncomputable def AdaptiveAlg.maxQueries {ι κ α : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [AddCommGroup κ] (A : AdaptiveAlg ι κ α) (g : ι → κ) : ℕ :=
  match A with
  | .halt _ => 0
  | .round T _ Q next =>
      open Classical in
      T + (Finset.univ.filter fun z =>
          0 < QAlgorithms.prob (Q.finalState (QAlgorithms.xorOracle g)) z).sup
        fun z => (next z).maxQueries g

end TriFormQ


