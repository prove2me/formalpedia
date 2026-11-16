-- Prove2me | Definitions.Def_HiddenPartition_Supplement_edgeDensity
-- name    : HiddenPartition_Supplement_edgeDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:58:49.944798+00:00
-- url     : https://prove2.me/theorems/9c5ba2cf-7332-48f5-9677-b01ab0630e52
-- title:
--   Edge density and pair density of a vertex set
-- statement:
--   Let $G$ be a simple graph and $U\subseteq V(G)$ a nonempty vertex set, and write $|E(G[U])|$ for the number of edges of $G$ with both endpoints in $U$. The **edge density** and the **pair density** of $U$ are
--
--   $$
--   \mathrm{ED}_G(U)=\frac{|E(G[U])|}{|U|},\qquad \mathrm{PD}_G(U)=\frac{|E(G[U])|}{\binom{|U|}{2}}\quad(|U|\ge 2),
--   $$
--
--   and the pair density of a single vertex is $0$. For $|U|\ge1$ one has $\mathrm{ED}_G(U)=\frac{|U|-1}{2}\,\mathrm{PD}_G(U)$.
--
--   These are the densities whose minimum or sum over the parts of a partition defines the objectives of Densest-$q$-Partition.
--
--   **Formalization Note** Values are real numbers. $|E(G[U])|$ is the published `HiddenPartition.edgeCount`. At $U=\emptyset$, where the paper defines nothing, Lean's division returns $0$; no statement uses this value.
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), §2 "Edge and Pair Densities", p.9 (pdf p.11)

import Mathlib
import Definitions.Def_HiddenPartition_edgeCount

set_option autoImplicit false

namespace HiddenPartition.Supplement

open HiddenPartition

/-- **Edge density** (Agrawal, Eua-anant, Haeupler, Laekhanukit, Mihov, Milenković, Santos, Zhang,
*From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering*,
STOC 2027 submission, manuscript sha256 17239d0b…, §2 "Edge and Pair Densities", p.9 (pdf p.11)).

For a nonempty vertex set `U`, `ED_G(U) = |E(G[U])| / |U|`, with `|E(G[U])|` the published
`HiddenPartition.edgeCount G U`.

**Formalization Note.** The value is real. The paper defines `ED_G(U)` only for nonempty `U`;
Lean's division gives `0` at `U = ∅`, a value no statement of the mission uses (every part of a
partition into nonempty parts is nonempty). -/
noncomputable def edgeDensity {V : Type*} [DecidableEq V] (G : SimpleGraph V) (U : Finset V) : ℝ :=
  (edgeCount G U : ℝ) / (U.card : ℝ)

/-- **Pair density** (Agrawal et al., STOC 2027 submission, manuscript sha256 17239d0b…, §2
"Edge and Pair Densities", p.9 (pdf p.11)).

`PD_G(U) = |E(G[U])| / binom(|U|, 2)` when `|U| ≥ 2`, and the pair density of a single vertex is
`0`.

**Formalization Note.** The value is real; the case `|U| ≤ 1` returns `0` (the paper's convention
for a single vertex; the empty set is never a part of a partition). -/
noncomputable def pairDensity {V : Type*} [DecidableEq V] (G : SimpleGraph V) (U : Finset V) : ℝ :=
  if 2 ≤ U.card then (edgeCount G U : ℝ) / ((U.card.choose 2 : ℕ) : ℝ) else 0

end HiddenPartition.Supplement


