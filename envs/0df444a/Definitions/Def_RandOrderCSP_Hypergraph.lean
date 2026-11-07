-- Prove2me | Definitions.Def_RandOrderCSP_Hypergraph
-- name    : RandOrderCSP_Hypergraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:06:18.893195+00:00
-- url     : https://prove2.me/theorems/fcee7796-4a52-4ee7-a5dc-9167ee20bb17
-- title:
--   $k$-uniform hypergraph
-- statement:
--   A **$k$-uniform hypergraph** is a triple $H=(\mathcal V_H,\mathcal E_H,M_H)$: a finite vertex set, a finite edge-index set, and a matrix $M_H\in\mathcal V_H^{\mathcal E_H\times[k]}$ whose rows have distinct entries. The entry $M_H(j,\ell)$ is the $\ell$-th vertex of the edge $j$. Distinct edge indices may carry identical rows, and empty vertex or edge sets are allowed.
--
--   The module also defines $\mathcal V_H(j)$, the set $\mathcal E_H(v)$ of edges incident to $v$, the degree $\deg_H(v)=|\mathcal E_H(v)|$, and the condition that every degree is at most $D$. This is the combinatorial object underlying every instance, gadget and neighbourhood in the mission.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §3.2, p.13

import Mathlib

namespace RandOrderCSP

/-- **k-uniform hypergraph** (§3.2, p.13).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), §3.2, p.13: "A k-uniform hypergraph H is a
triple H = (𝒱_H, ℰ_H, M_H), where 𝒱_H is a finite “vertex set”, ℰ_H is a finite “edge-index set”,
and M_H ∈ (𝒱_H)^{ℰ_H×[k]} is a matrix satisfying that all entries in each row are distinct."

**Formalization Note.** The vertex set `V` and the edge-index set `E` are type parameters (finiteness
is assumed through `Fintype` instances where it is used). Row `j` of the matrix is `M j : Fin k → V`;
"all entries in each row are distinct" is `row_inj`. Empty vertex or edge sets are allowed, and
distinct edge indices may have identical rows, as on p.13. -/
structure Hypergraph (k : ℕ) (V E : Type) where
  /-- `M j ℓ` is the `ℓ`-th vertex of the `j`-th edge. -/
  M : E → Fin k → V
  /-- The entries of each row are distinct. -/
  row_inj : ∀ j, Function.Injective (M j)

namespace Hypergraph

variable {k : ℕ} {V E : Type}

/-- `𝒱_H(j)`: the set of vertices of the edge `j` (p.13). -/
def verts [DecidableEq V] (H : Hypergraph k V E) (j : E) : Finset V :=
  Finset.univ.image (H.M j)

/-- `ℰ_H(v)`: the set of edges incident to the vertex `v` (p.13). -/
def edgesAt [Fintype E] [DecidableEq V] (H : Hypergraph k V E) (v : V) : Finset E :=
  Finset.univ.filter (fun j => v ∈ H.verts j)

/-- `deg_H(v) = |ℰ_H(v)|` (p.13). -/
def deg [Fintype E] [DecidableEq V] (H : Hypergraph k V E) (v : V) : ℕ :=
  (H.edgesAt v).card

/-- "Maximum degree `D`": every vertex has degree at most `D` (p.14, "degree-at-most-D"). -/
def MaxDegLE [Fintype E] [DecidableEq V] (H : Hypergraph k V E) (D : ℕ) : Prop :=
  ∀ v, H.deg v ≤ D

end Hypergraph

end RandOrderCSP


