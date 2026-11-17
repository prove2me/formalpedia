-- Prove2me | Definitions.Def_ShortBroadcastDom_Supplement_tauRel
-- name    : ShortBroadcastDom_Supplement_tauRel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:38:01.958176+00:00
-- url     : https://prove2.me/theorems/0ee5039b-3156-4e4f-be93-d90f5a738432
-- title:
--   Covering LP value $\tau_c$ and integral optimum $\mathrm{OPT}_c$ for a general covering relation $C(r)$
-- statement:
--   Let $G$ be a finite graph, $R\subseteq V(G)$ a set of **demands**, and for each demand $r$ let $C(r)$ be the set of candidates allowed to cover $r$ (in the paper $C(r)$ is a nonempty subset of the closed neighbourhood $N_G[r]$). For vertex costs $c_v$, the **fractional covering optimum** is
--
--   $$
--   \tau_c=\min\Bigl\{\sum_v c_vx_v\;:\;x\ge0,\ \sum_{v\in C(r)}x_v\ge1\text{ for every demand }r\Bigr\},
--   $$
--
--   and the **integral optimum** $\mathrm{OPT}_c$ is the minimum of $\sum_{v\in S}c_v$ over vertex sets $S$ that cover every demand, i.e. $S\cap C(r)\neq\emptyset$ for all $r\in R$.
--
--   With $C(r)=N_G[r]$ this is the domination program of the base mission; with $R=V(G)$, $C(r)=N_G(r)$ and unit costs it is the fractional total domination number $\gamma_{t,f}(G)$; with $R$ the red vertices and $C(r)$ the blue neighbours of $r$ it is red-blue domination.
--
--   **Formalization Note** Both optima are infima over $\mathbb R$ of the feasible objective values. For nonnegative costs and nonempty covering sets of all demands the programs are feasible and bounded below, so the infima are the minima; every statement of the mission uses them only in that case. The vector $x$ ranges over all vertices; a vertex in no covering set covers nothing and, with a nonnegative cost, never lowers the value, so this equals the program over the admissible vertices.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §1.1, p.2 (PDF p.5); §6.6, p.41 (PDF p.44)

import Mathlib

namespace ShortBroadcastDom.Supplement

/-- **The covering LP value `τ_c` for a general covering relation.** For a demand set `R`, a
covering relation `Cov` (the set `C(r)` of candidates allowed to cover the demand `r`) and real
vertex costs `c`, `tauRel R Cov c` is
`inf { ∑_v c_v x_v : x ≥ 0, ∑_{v ∈ C(r)} x_v ≥ 1 for every demand r }`.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §1.1, p.2 (PDF 5): "Each demand r specifies a nonempty set C(r) of allowed candidates in
its closed neighborhood. … We write the minimum fractional cost as
τc = min{∑_v cv xv : x ≥ 0, ∑_{v∈C(r)} xv ≥ 1 for every demand r}"; §6.6, p.41 (PDF 44). With
`C(r) = N(r)`, `R = V(G)` and unit costs it is the fractional total domination number (App. F,
p.76); with `C(r)` the blue neighbours of a red demand `r` it is the red-blue `τ_c` (App. H, p.102).

**Formalization Note** The optimum is `sInf` over `ℝ` of the feasible objective values. When every
cost is nonnegative the set is bounded below by `0`, and when every `C(r)` (`r ∈ R`) is nonempty it
contains the value of `x ≡ 1`, so `sInf` is the LP minimum (the minimum is attained: it is a
feasible LP with a nonnegative objective). Every statement of the mission uses `tauRel` only in that
case. The vector `x` ranges over all vertices; a vertex in no `C(r)` covers nothing, and with a
nonnegative cost it never lowers the value, so this equals the paper's program over the admissible
vertices (§6.6, p.41). The graph enters only through the relation (`C(r) ⊆ N[r]` is a hypothesis of
the statements that need it). -/
noncomputable def tauRel {V : Type} [Fintype V] (R : Finset V) (Cov : V → Finset V)
    (c : V → ℝ) : ℝ :=
  sInf {s : ℝ | ∃ x : V → ℝ, (∀ v, 0 ≤ x v) ∧ (∀ r ∈ R, 1 ≤ ∑ v ∈ Cov r, x v) ∧
    s = ∑ v, c v * x v}

/-- **The integral optimum `OPT_c`**: the minimum cost `∑_{v ∈ S} c_v` of a vertex set `S` that
covers every demand, i.e. `S ∩ C(r) ≠ ∅` for every `r ∈ R`.

§1.1, p.2 (PDF 5): "let OPTc be the minimum cost of an integral cover"; §6.6, p.41 (PDF 44): "A
vertex set X covers a demand r if X ∩ C(r) ≠ ∅."

**Formalization Note** An integral cover is a set (each candidate used at most once). The value is
`sInf` over `ℝ`; when every `C(r)` is nonempty the set `S = V` is a cover, and there are finitely
many sets, so `sInf` is the minimum. -/
noncomputable def optRel {V : Type} [Fintype V] (R : Finset V) (Cov : V → Finset V)
    (c : V → ℝ) : ℝ :=
  sInf {s : ℝ | ∃ S : Finset V, (∀ r ∈ R, ∃ v ∈ S, v ∈ Cov r) ∧ s = ∑ v ∈ S, c v}

end ShortBroadcastDom.Supplement


