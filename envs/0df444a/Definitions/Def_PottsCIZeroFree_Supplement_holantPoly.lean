-- Prove2me | Definitions.Def_PottsCIZeroFree_Supplement_holantPoly
-- name    : PottsCIZeroFree_Supplement_holantPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:35:47.556448+00:00
-- url     : https://prove2.me/theorems/b6f5c4b9-2ac8-430e-ba26-418bda51a8c5
-- title:
--   Symmetric Boolean signatures, log-concavity, and the Holant polynomial $Z_{G,\mathbf f}(\mathbf z)$
-- statement:
--   A **symmetric Boolean signature** of arity $d$ is a map $f:\{0,\dots,d\}\to[0,\infty)$; $f(k)$ is the value assigned when exactly $k$ incident edges are selected. It is **log-concave** if
--   1. its positive support $\{k:f(k)>0\}$ is an interval of consecutive integers, and
--   2. $f(k)^2\ge f(k-1)f(k+1)$ for $1\le k<d$.
--
--   For a graph $G=(V,E)$, signatures $\mathbf f=(f_v)_{v\in V}$ and edge activities $\mathbf z=(z_e)_{e\in E}\in\mathbb C^E$, the **Holant polynomial** is
--   $$Z_{G,\mathbf f}(\mathbf z)=\sum_{S\subseteq E}\ \prod_{v\in V}f_v\big(\deg_S(v)\big)\prod_{e\in S}z_e,$$
--   where $\deg_S(v)$ is the number of edges of $S$ incident to $v$.
--
--   These are the objects of the log-concave Holant polytube theorem (Theorem 5.6), which concerns assignments with $\mathrm{arity}(f_v)=\deg_G(v)$ drawn from a finite family of log-concave signatures with $f(0)>0$.
--
--   **Formalization Note** A signature is a structure carrying its arity $d$ and values `val : Fin (d+1) → ℝ` with `0 ≤ val k`, so a family may mix arities; `SymSig.eval f k` is $f(k)$ for $k\le d$ and $0$ beyond (values beyond the arity never occur in the sum when $\mathrm{arity}(f_v)=\deg_G(v)$). Activities are indexed by the edge set `G.edgeSet`. The arity condition is imposed by the theorem, not inside the polynomial. No normalization by $\prod_v f_v(0)$.
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), §5.2, p.29 (PDF p.31), signatures, log-concavity and display (44)

import Mathlib

open Classical

namespace PottsCIZeroFree.Supplement

noncomputable section

/-- A symmetric Boolean signature of arity `d`, §5.2 of Shao, Shi, *Coupling Independence
Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.29 (PDF p.31):
a map `f : {0, …, d} → [0, ∞)`, where `f(k)` is the value assigned when exactly `k` incident
edges are selected.

**Formalization Note.** The arity is part of the data (`arity = d`), so a family may contain
signatures of several arities; the values are `val : Fin (d + 1) → ℝ` with `0 ≤ val k`. -/
structure SymSig where
  /-- The arity `d`. -/
  arity : ℕ
  /-- The values `f(0), …, f(d)`. -/
  val : Fin (arity + 1) → ℝ
  /-- The values lie in `[0, ∞)`. -/
  nonneg : ∀ k, 0 ≤ val k

/-- The value `f(k)` of a signature, extended by `0` for `k > d` (such `k` never occur in the
Holant sum (44), since `deg_S(v) ≤ deg_G(v) = d`). -/
def SymSig.eval (f : SymSig) (k : ℕ) : ℝ :=
  if h : k ≤ f.arity then f.val ⟨k, Nat.lt_succ_of_le h⟩ else 0

/-- Log-concavity of a symmetric Boolean signature, printed p.29 (PDF p.31): (a) its positive
support `{k ∈ {0,…,d} : f(k) > 0}` is an interval of consecutive integers, and
(b) `f(k)² ≥ f(k − 1) f(k + 1)` for `1 ≤ k < d`. -/
def SymSig.LogConcave (f : SymSig) : Prop :=
  (∀ i j k : ℕ, i ≤ j → j ≤ k → k ≤ f.arity → 0 < f.eval i → 0 < f.eval k → 0 < f.eval j) ∧
  (∀ k : ℕ, 1 ≤ k → k < f.arity → f.eval (k - 1) * f.eval (k + 1) ≤ f.eval k ^ 2)

/-- `deg_S(v)`: the number of edges of `S ⊆ E` incident to `v` (printed p.29, PDF p.31). -/
def degIn {V : Type*} [Fintype V] {G : SimpleGraph V} (S : Finset G.edgeSet) (v : V) : ℕ :=
  (S.filter (fun e => v ∈ (e : Sym2 V))).card

/-- The Holant polynomial (44), printed p.29 (PDF p.31): for a graph `G = (V, E)`, signatures
`f = (f_v)_{v ∈ V}` and edge activities `z = (z_e)_{e ∈ E} ∈ ℂ^E`,
`Z_{G,f}(z) = Σ_{S ⊆ E} ∏_{v ∈ V} f_v(deg_S(v)) ∏_{e ∈ S} z_e`.

**Formalization Note.** Activities are indexed by the edge set `G.edgeSet` (a finite subtype of
`Sym2 V`); `S` ranges over all finite subsets of it. The requirement `arity(f_v) = deg_G(v)` is
imposed by the statements that use this polynomial, not here; `SymSig.eval` returns `0` past the
arity. No normalization by `∏_v f_v(0)` is applied. -/
def holantPoly {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → SymSig)
    (z : G.edgeSet → ℂ) : ℂ :=
  ∑ S : Finset G.edgeSet, (∏ v, ((f v).eval (degIn S v) : ℂ)) * ∏ e ∈ S, z e

end

end PottsCIZeroFree.Supplement


