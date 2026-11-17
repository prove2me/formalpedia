-- Prove2me | Definitions.Def_GyoriLovasz_Supplement_FESAC
-- name    : GyoriLovasz_Supplement_FESAC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:11:53.266873+00:00
-- url     : https://prove2.me/theorems/a1998d91-3470-42cf-8eeb-01826521f7c0
-- title:
--   Flow-Essential Split-Assignment Condition
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T$, capacities $c_t$ ($t\in T$) and weights $w_v$ ($v\in V\setminus T$). A **flow-essential split-assignment** is a function $\psi:(V\setminus T)\times T\to\mathbb N$ that sends exactly the weight of every non-terminal:
--
--   $$
--   \sum_{t\in T}\psi(v,t)=w_v\qquad\text{for every } v\in V\setminus T .
--   $$
--
--   $G$ satisfies the **Flow-Essential Split-Assignment Condition** if some such $\psi$ (a *witness*) also satisfies:
--
--   1. for every $v\in V\setminus T$ and $t\in T$ with $\psi(v,t)>0$, the terminal $t$ is essential for $v$ (removing $t$ lowers the terminal connectivity $\kappa_G(v)$ by exactly one);
--   2. for every $t\in T$, $\sum_{v\in V\setminus T}\psi(v,t)\le c_t$.
--
--   This relaxes the Flow-Essential Assignment Condition in two ways: a vertex may split its weight among several essential terminals, and capacities are upper bounds instead of equalities. It is the hypothesis of Theorem 4.
--
--   **Formalization Note** $\psi$, $c$ and $w$ are total functions on the vertex type; only $\psi$ on $(V\setminus T)\times T$, $c$ on $T$ and $w$ on $V\setminus T$ are read. Essentiality is the base mission's published definition, unchanged.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Definition 3.5, p.21; Definition 1.3, pp.12 and 21

import Mathlib
import Definitions.Def_GyoriLovasz_IsEssential

namespace GyoriLovasz

namespace Supplement

/-- **Flow-essential split-assignment witness.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the
Exponential Barrier*, arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 3.5, p.21: "a function
ψ : (V \ T) × T → N≥0 such that, for every vertex v ∈ V \ T, ∑_{t∈T} ψ(v, t) = w_v"; Definition 1.3, pp.12, 21:
"1. for every vertex v ∈ V \ T and terminal t ∈ T with ψ(v, t) > 0, the terminal t is essential for v; and 2. for every
terminal t ∈ T, we have ∑_{v∈V\T} ψ(v, t) ≤ c_t."

**Formalization Note.** `ψ`, `c` and `w` are total functions; only `ψ` on `(V \ T) × T`, `c` on `T` and `w` on `V \ T`
are read. Essentiality is the published `IsEssential` ("the definition of essentiality does not change", p.21). -/
def IsSplitWitness {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (c w : V → ℕ) (ψ : V → V → ℕ) : Prop :=
  (∀ v ∈ G.verts \ T, ∑ t ∈ T, ψ v t = w v) ∧
    (∀ v ∈ G.verts \ T, ∀ t ∈ T, 0 < ψ v t → IsEssential G T v t) ∧
    ∀ t ∈ T, ∑ v ∈ G.verts \ T, ψ v t ≤ c t

/-- **The Flow-Essential Split-Assignment Condition.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the
Exponential Barrier*, arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 1.3, pp.12, 21: "We say that G
satisfies the Flow-Essential Split-Assignment Condition if there exists a flow-essential split-assignment ψ such
that" `IsSplitWitness` holds. -/
def FESAC {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (c w : V → ℕ) : Prop :=
  ∃ ψ : V → V → ℕ, IsSplitWitness G T c w ψ

end Supplement

end GyoriLovasz


