-- Prove2me | Definitions.Def_SparseBatchBandit_coordScale
-- name    : SparseBatchBandit_coordScale
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:02.360239+00:00
-- url     : https://prove2.me/theorems/4f1eda8a-06f5-4aa4-bb84-adaf3e451413
-- title:
--   Coordinate scale $M_{m,l}$
-- statement:
--   For a set $S$ of rounds and a coordinate $l\in[d]$,
--
--   $$
--   \sqrt{\frac1{|S|}\sum_{t\in S}x_{t,a_t,l}^2}.
--   $$
--
--   The paper's $M_{m,l}$ is this quantity with $S=T^{(m)}$. It is the scale of the noise term of the Lasso analysis in coordinate $l$.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, proof of Lemma 6, p.27

import Mathlib

namespace SparseBatchBandit

/-- `M_{m,l} = √((1/|T^{(m)}|) ∑_{t∈T^{(m)}} x²_{t,a_t,l})`, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, proof of Lemma 6, p.27 (PDF 27),
for `S = T^{(m)}`. -/
noncomputable def coordScale {T K d : ℕ} (c : Fin T → Fin K → Fin d → ℝ) (a : Fin T → Fin K)
    (S : Finset (Fin T)) (l : Fin d) : ℝ :=
  Real.sqrt ((1 / (S.card : ℝ)) * ∑ t ∈ S, c t (a t) l ^ 2)

end SparseBatchBandit


