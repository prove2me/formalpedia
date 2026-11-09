-- Prove2me | Definitions.Def_InflMaxAdapt_kappa
-- name    : InflMaxAdapt_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:16.129299+00:00
-- url     : https://prove2.me/theorems/9fe75605-4ec6-4da9-9b2c-d5efe821ebe8
-- title:
--   Connection probability to the set, $\kappa(v) = \mathbb P(v \leftrightarrow S)$
-- statement:
--   For a fixed set $S \subseteq V$,
--   $$
--   \kappa(v) \;:=\; \mathbb P(v \leftrightarrow S)
--   $$
--   is the probability that the vertex $v$ connects to $S$.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), proof of Lemma 4, printed p.6 (PDF p.7)

import Mathlib
import Definitions.Def_InflMaxAdapt_edgeProb
import Definitions.Def_InflMaxAdapt_ConnSet

namespace InflMaxAdapt

/-- `κ(v) := P(v ↔ S)`, the probability that `v` connects to the set `S` (proof of Lemma 4,
printed p.6 = PDF p.7, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)). -/
noncomputable def kappa {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (S : Finset V) (v : V) : ℝ :=
  edgeProb q (fun E => ConnSet E v S)

end InflMaxAdapt


