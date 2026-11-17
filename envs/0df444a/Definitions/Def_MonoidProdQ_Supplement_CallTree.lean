-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_CallTree
-- name    : MonoidProdQ_Supplement_CallTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:06:54.678333+00:00
-- url     : https://prove2.me/theorems/d27dbd18-199e-4fcc-ba2a-303aa3d560f4
-- title:
--   Deterministic procedures with subroutine calls and predicted branches
-- statement:
--   Fix a finite index set $J$ and, for each $j\in J$, a finite answer set $\Gamma_j$. A **call procedure** with outputs in $O$ is a finite tree of one of two kinds:
--
--   1. a **leaf** $\mathrm{leaf}(o)$ that stops and outputs $o\in O$;
--   2. a **call node** that calls the function $g_j$ for some $j\in J$, groups its answer $\gamma\in\Gamma_j$ into one of finitely many outgoing branches by a map $\pi:\Gamma_j\to\{0,\dots,k-1\}$, designates at most one branch as **predicted**, and continues with the subtree attached to the branch $\pi(\gamma)$ taken.
--
--   This is the model of Theorem 16: "The choice of which function to call may depend on earlier answers. At each call, designate at most one outgoing branch as predicted. Return values may be grouped into one branch provided the subsequent computation, including retained data, depends only on that branch."
--
--   **Formalization Note** Branches are numbered $0,\dots,k-1$ (any finite branch set is in bijection with one of these). Grouping is the map $\pi$: since each subtree depends only on the branch, so does everything computed after the call. Only finite trees exist; a procedure that makes at most $q$ calls on the promise domain can be truncated below depth $q$ without changing any execution on it.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 16, p.31

import Mathlib

universe u v w

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 16, p.31: "a deterministic
procedure computes f(x), accessing x only through calls to the functions g_j. The choice of
which function to call may depend on earlier answers. At each call, designate at most one
outgoing branch as predicted. Return values may be grouped into one branch provided the
subsequent computation, including retained data, depends only on that branch." A procedure of
this kind is a finite tree:

* `leaf o` stops and outputs `o ∈ O`;
* `node j k branch predicted child` calls `g_j`, groups its return value `γ ∈ Γ_j` into the
  branch `branch γ` among `k` outgoing branches, designates the branch `predicted` as predicted
  (`none`: no branch is predicted), and continues with the subtree `child (branch γ)`.

**Formalization Note.** The outgoing branches of a call are `Fin k` (any finite set of branches
is in bijection with one of these). Grouping is the map `branch`; since a subtree depends only on
the branch taken, so does everything computed after the call. The inductive type has only
finite trees; on the promise domain the procedure makes at most `q` calls, so truncating any
procedure below depth `q` loses nothing. -/
inductive CallTree (J : Type u) (Γ : J → Type v) (O : Type w) : Type (max u v w)
  /-- Stop and output `o`. -/
  | leaf (o : O) : CallTree J Γ O
  /-- Call `g_j`, take the branch of its answer among `k`, with an optional predicted branch. -/
  | node (j : J) (k : ℕ) (branch : Γ j → Fin k) (predicted : Option (Fin k))
      (child : Fin k → CallTree J Γ O) : CallTree J Γ O

end MonoidProdQ.Supplement


