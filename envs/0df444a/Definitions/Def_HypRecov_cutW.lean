-- Prove2me | Definitions.Def_HypRecov_cutW
-- name    : HypRecov_cutW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:31.889206+00:00
-- url     : https://prove2.me/theorems/dc772883-cd3f-4576-8310-a0183acee054
-- title:
--   Cut function of a weighted hypergraph $\widehat H$
-- statement:
--   A **weighted hypergraph** $\widehat H$ is a finite list of pairs $(e,w)$ of a vertex set $e\subseteq V$ and a weight $w\in\mathbb N$. Its cut function is
--   $$\mathrm{cut}_{\widehat H}(S)=\sum_{(e,w)\in\widehat H:\ e\cap S\ne\emptyset,\ e\setminus S\ne\emptyset} w .$$
--   Theorem 1.1 returns such a representation, "permitting weighted synthetic edges", whose cuts agree with those of $H$ after truncation at $k$; Lemma 7.1 builds one from weight-$k$ two-vertex edges and weight-one original edges.
--
--   **Formalization Note** A list allows the same vertex set to appear several times; the weights add.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 1.1, p.2 (PDF p.3); Lemma 7.1, p.18 (PDF p.19)

import Mathlib

namespace HypRecov

/-- **Cut function of a weighted hypergraph `Ĥ`.** Zhang, Chen, Shen, *Hypergraph Recovery from
Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Theorem 1.1, p.2
(PDF p.3): "a hypergraph representation Ĥ, permitting weighted synthetic edges"; Lemma 7.1, p.18.

`Ĥ` is a list of weighted edges `(e, w)`; `cutW Ĥ S` is the total weight of the listed edges that
meet both `S` and its complement.

**Formalization Note.** A list allows repeated edges; weights are natural numbers (the paper uses
weight `k` for synthetic edges and weight `1` for original ones). -/
def cutW {n : ℕ} (H : List (Finset (Fin n) × ℕ)) (S : Finset (Fin n)) : ℕ :=
  ((H.filter (fun p => decide ((p.1 ∩ S).Nonempty ∧ (p.1 \ S).Nonempty))).map Prod.snd).sum

end HypRecov


