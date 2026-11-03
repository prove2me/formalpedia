-- Prove2me | Definitions.Def_SparseBatchBandit_sample
-- name    : SparseBatchBandit_sample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:29:11.652664+00:00
-- url     : https://prove2.me/theorems/7331ff8a-7ae9-499a-a960-b7d2296edef4
-- title:
--   Estimation sample $T^{(m)}$
-- statement:
--   The sample used to compute $\hat\theta_m$ is
--
--   $$
--   T^{(m)}=\bigcup_{m'=1}^{m}T_{m'}^{(m)},
--   $$
--
--   the $m$-th interval of each of the batches $1,\dots,m$. It is not the set of all past rounds. This sample splitting is what makes the noise on $T^{(m)}$ independent of the contexts selected on $T^{(m)}$.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Algorithm 1, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_subInterval

namespace SparseBatchBandit

/-- The estimation sample `T^{(m)} = ⋃_{m'=1}^m T_{m'}^{(m)}` of `θ̂_m`: the `m`-th interval of
each of the batches `1, …, m`, not all the rounds so far. Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, Algorithm 1, p.16 (PDF 16). -/
noncomputable def sample (T s₀ M m : ℕ) : Finset (Fin T) :=
  (Finset.Icc 1 m).biUnion (fun m' => subInterval T s₀ M m' m)

end SparseBatchBandit


