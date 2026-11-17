-- Prove2me | Definitions.Def_LovaszECCKernel_Supplement_ECPBelowEdges
-- name    : LovaszECCKernel_Supplement_ECPBelowEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:11:10.857204+00:00
-- url     : https://prove2.me/theorems/07b010fb-8e0a-493b-bd8d-3fbe54944e15
-- title:
--   ECP and ECC below the number of edges — yes-instances
-- statement:
--   For a graph $G$ with $m=|E(G)|$ edges and an integer $t\ge0$:
--
--   1. $(G,t)$ is a yes-instance of **Edge Clique Partition below the number of edges** if $\mathrm{ecp}(G)\le m-t$;
--   2. $(G,t)$ is a yes-instance of **Edge Clique Cover below the number of edges** if $\mathrm{ecc}(G)\le m-t$, i.e. the ECC instance $(G,k)$ with $k=m-t$ is a yes-instance.
--
--   The edges themselves always form an edge clique partition of size $m$, so $m$ is a trivial upper bound for both numbers, and $t$ measures how far below it the target lies. These are the problems of the paper's Theorems 7, 8 and 9.
--
--   **Formalization Note** $m$ is the published `edgeCount`; the comparisons are in $\mathbb Z$, so $t>m$ gives a no-instance. The parameter $t$ is a natural number; instances with $t<0$ (for ECC: $k>m$) are trivial yes-instances and are not represented.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorems 7 and 8, p.44 (= PDF p.44); Theorem 9, p.59 (= PDF p.59)

import Mathlib
import Definitions.Def_LovaszECCKernel_Supplement_ecp
import Definitions.Def_LovaszECCKernel_nonEdges

set_option autoImplicit false

namespace LovaszECCKernel.Supplement

/-- `(G, t)` is a **yes-instance of ECP below the number of edges** (Fomin, Golovach, Khargeliia,
Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic Extensions of the Lovász and
Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorems 7 and 8,
p.44 (= PDF p.44)): "deciding whether the edges of a graph G could be partitioned in at most
|E(G)| − t cliques", i.e. `ecp(G) ≤ |E(G)| − t`.

**Formalization Note** `|E(G)|` is the published `edgeCount`; the comparison is in `ℤ`, so `t > |E(G)|`
gives a no-instance. The parameter `t` is a natural number (a negative `t` is a trivial yes-instance,
since the edges themselves form a partition). -/
def ECPBelowEdges {V : Type*} [Fintype V] (G : SimpleGraph V) (t : ℕ) : Prop :=
  (ecp G : ℤ) ≤ (edgeCount G : ℤ) - t

/-- `(G, t)` is a **yes-instance of ECC below the number of edges** (Fomin et al., STOC 2027
submission (manuscript sha256 a9d53ab8…), Theorem 9, p.59 (= PDF p.59)): "ECC … parameterized by
t = |E(G)| − k", i.e. `ecc(G) ≤ k = |E(G)| − t`.

**Formalization Note** `ecc` is the published edge clique cover number; the comparison is in `ℤ`.
The instance is given by `t ∈ ℕ` (then `k = |E(G)| − t`); instances with `k > |E(G)|` are trivial
yes-instances and are not represented. -/
def ECCBelowEdges {V : Type*} [Fintype V] (G : SimpleGraph V) (t : ℕ) : Prop :=
  (ecc G : ℤ) ≤ (edgeCount G : ℤ) - t

end LovaszECCKernel.Supplement


