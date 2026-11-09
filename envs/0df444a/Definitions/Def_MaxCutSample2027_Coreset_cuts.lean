-- Prove2me | Definitions.Def_MaxCutSample2027_Coreset_cuts
-- name    : MaxCutSample2027_Coreset_cuts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:34:30.724825+00:00
-- url     : https://prove2.me/theorems/041de68e-f5ce-454c-8aa4-f51897fda671
-- title:
--   Weighted matrices and the finite Max-Cut value
-- statement:
--   Let $V$ be a finite vertex set. A weight matrix $A:V\times V\to\mathbb R$ is admissible when it is symmetric, has zero diagonal, and has nonnegative entries. For a subset $S\subseteq V$, define
--   $$\operatorname{cutValue}_A(S)=\sum_{u\in S}\sum_{v\notin S}A_{uv},\qquad
--   \operatorname{maxCut}(A)=\max_{S\subseteq V}\operatorname{cutValue}_A(S).$$
--   Each crossing edge is counted once. The maximum ranges over all subsets of the actual index type, including when that type is the sample's $k$ labelled copies. The definition of the value also makes sense for arbitrary real matrices; admissibility is a separate predicate.
--
--   This module supplies the general graph interface used by the sampling model. The maximum is a nonempty finite maximum, including for an empty vertex type (value zero), and carries no optimality hypothesis.
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), §1, p. 1; §2 standing assumptions, p. 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Mathlib
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset

/-- The source's undirected, loopless, nonnegative real weight matrices. -/
def IsWeightMatrix {V : Type*} (A : V → V → ℝ) : Prop :=
  (∀ u v, A u v = A v u) ∧ (∀ v, A v v = 0) ∧ (∀ u v, 0 ≤ A u v)

/-- A crossing edge is counted once, from the chosen side to its complement. -/
def cutValue {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, A u v

/-- A genuine finite maximum over every subset of the matrix's vertex type. -/
def maxCut {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → ℝ) : ℝ :=
  (Finset.univ : Finset (Finset V)).sup' Finset.univ_nonempty (cutValue A)

end MaxCutSample2027.Coreset


