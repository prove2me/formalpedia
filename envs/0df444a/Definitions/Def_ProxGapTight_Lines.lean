-- Prove2me | Definitions.Def_ProxGapTight_Lines
-- name    : ProxGapTight_Lines
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:56.580195+00:00
-- url     : https://prove2.me/theorems/8ea4f3ba-1337-4fc7-bbcc-d5aa24dbb623
-- title:
--   Lines $X$ of $\mathbb F_Q^m$
-- statement:
--   For a field $K$ (in the paper $K=\mathbb F_Q$) and $m\ge0$, let $X$ be the set of **lines** of $K^m$, that is, the one-dimensional subspaces of $K^m$.
--
--   The lines index the coordinates of the ambient code $U_m$: the code has length $n_m=|X|=(Q^m-1)/(Q-1)$.
--
--   **Formalization Note** A line is a submodule of $K^m$ of dimension one. For a finite field $K$ there are finitely many, and the module provides the corresponding finiteness instance.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §3.1, p.7

import Mathlib

namespace ProxGapTight

/-- The set `X` of **lines** (one-dimensional subspaces) of `F_Q^m`, Kominers, Thaler, Zheng,
manuscript (Sept. 2026), §3.1, p.7 ("We let X denote the set of one-dimensional subspaces, or
lines, of F_Q^m").

**Formalization Note.** `F_Q` is any field `K`; the coordinate space is `Fin m → K`. A line is a
submodule of `finrank` one. For a finite field the type is finite (the instance below), which is
what lets words be indexed by `X`. -/
def Lines (K : Type) [Field K] (m : ℕ) : Type :=
  {ℓ : Submodule K (Fin m → K) // Module.finrank K ℓ = 1}

instance (K : Type) [Field K] [Fintype K] (m : ℕ) : Finite (Lines K m) := by
  unfold Lines
  infer_instance

noncomputable instance (K : Type) [Field K] [Fintype K] (m : ℕ) : Fintype (Lines K m) :=
  Fintype.ofFinite _

end ProxGapTight


