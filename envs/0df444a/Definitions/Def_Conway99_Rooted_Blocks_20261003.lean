-- Prove2me | Definitions.Def_Conway99_Rooted_Blocks_20261003
-- name    : Conway99_Rooted_Blocks_20261003
-- status  : Definition
-- author  : @harry
-- created : 2026-10-03T07:59:08.277983+00:00
-- url     : https://prove2.me/theorems/f0af17cf-ff7f-44a9-a8f7-b0a64f86340e
-- title:
--   Graph-owned rooted blocks for Conway graphs
-- statement:
--   Let $G$ be a finite simple graph on a vertex set $V$, and choose a vertex $r$. Write $A$ for its adjacency matrix over the integers, let $L=N_G(r)$ be the neighbors of $r$, and let $F=V\setminus(\{r\}\cup L)$ be the remaining vertices. Define the graph-owned blocks and rectangular all-ones matrix by
--
--   $$
--   A_F=A[F,F],\qquad N=A[F,L],\qquad M=A[L,L],\qquad (J_{X,Y})_{xy}=1.
--   $$
--
--   Every block is a literal restriction of the same adjacency matrix $A$; there are no independently chosen matrix parameters. These definitions do not assume that $G$ is strongly regular or assert that a graph with Conway's parameters exists. They provide the interface for stating necessary rooted block identities.
-- source:
--   Local source: Conway99/Conway99/Verified/Rooted.lean at rooted-bridge lane commit 688f16d30aaf045040290462f60369db373fbe5b, declarations Conway99.RootedVerified.transport, far_quadratic, and far_degree. Graph-owned definitions are extracted from Conway99.Core. Consolidated standalone source: prove2me/RootedBridge.lean, SHA-256 817c75531a9be7c498b143f3db1e6a06cfb8c208416ec30d7e638cedd18505c5. Context is the public Conway99.conway_99 target at https://prove2.me/theorems/7bc34ad9-a7f2-480e-ac84-4cfe4cd5042a; these necessary identities do not solve that target.

import Mathlib

set_option autoImplicit false

namespace Conway99

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def allOnes (m n : Type*) (α : Type*) [One α] : Matrix m n α := Matrix.of fun _ _ => 1

@[simp] lemma allOnes_apply {m n α : Type*} [One α] (i : m) (j : n) :
    allOnes m n α i j = 1 := rfl

namespace Rooted

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

/-- The neighbors of the chosen root in the same graph. -/
def LocF : Finset V := G.neighborFinset r

/-- The vertices outside the root and its neighbors in the same graph. -/
def FarF : Finset V := Finset.univ \ insert r (LocF G r)

/-- The local vertex subtype. -/
abbrev LocT := {x : V // x ∈ LocF G r}

/-- The far vertex subtype. -/
abbrev FarT := {x : V // x ∈ FarF G r}

/-- The far adjacency block of the same graph. -/
def AFar : Matrix (FarT G r) (FarT G r) ℤ :=
  (G.adjMatrix ℤ).submatrix (fun x => x.1) (fun x => x.1)

/-- The far-to-local adjacency block of the same graph. -/
def NReg : Matrix (FarT G r) (LocT G r) ℤ :=
  (G.adjMatrix ℤ).submatrix (fun x => x.1) (fun x => x.1)

/-- The local adjacency block of the same graph. -/
def MMate : Matrix (LocT G r) (LocT G r) ℤ :=
  (G.adjMatrix ℤ).submatrix (fun x => x.1) (fun x => x.1)

end Rooted

end Conway99


