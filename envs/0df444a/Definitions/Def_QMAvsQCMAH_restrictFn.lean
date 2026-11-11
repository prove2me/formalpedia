-- Prove2me | Definitions.Def_QMAvsQCMAH_restrictFn
-- name    : QMAvsQCMAH_restrictFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:52.694247+00:00
-- url     : https://prove2.me/theorems/4a7ed221-7558-47bd-bb30-8a572a72593f
-- title:
--   Restricted Boolean functions $g^{P,U}$
-- statement:
--   For $f:\{0,1\}^{\mathcal X}\to\{0,1\}$, $P\subseteq\mathcal X$ and $U:\mathcal X\setminus P\to\{0,1\}$, the **restriction** is $g^{P,U}(r)=f(\mathcal O_r)$ for $r:P\to\{0,1\}$, where $\mathcal O_r=r$ on $P$ and $\mathcal O_r=U$ outside $P$.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Definition 23, p.36

import Mathlib

set_option autoImplicit false

namespace QMAvsQCMAH

/-- The assignment `O_r` that equals `r` on `P` and the fixed answers `U` outside `P`. -/
def oFrom {X : Type} [DecidableEq X] (P : Finset X) (U : {u // u ∉ P} → Bool)
    (r : {u // u ∈ P} → Bool) : X → Bool :=
  fun u => if h : u ∈ P then r ⟨u, h⟩ else U ⟨u, h⟩

/-- The restriction `B|_{X∖P}` of a function to the complement of `P`. -/
def offP {X : Type} (B : X → Bool) (P : Finset X) : {u // u ∉ P} → Bool := fun u => B u.1

/-- The **restricted Boolean function** `g^{P,U}(r) = f(O_r)`, `O_r = r` on `P`, `U` off `P`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Definition 23, p.36 (PDF p.39): "Let X ⊆ {0, 1}∗ be finite, f : {0, 1}^X → {0, 1},
P ⊆ X, and U : X \ P → {0, 1}. We define the restriction g^{P,U} of f obtained by setting the
answers outside P to U as follows: for r : P → {0, 1}, let O_r(u) = r(u), u ∈ P, U(u), u ∉ P,
g^{P,U}(r) = f(O_r)." -/
def restrictFn {X : Type} [DecidableEq X] (f : (X → Bool) → Bool) (P : Finset X)
    (U : {u // u ∉ P} → Bool) : ({u // u ∈ P} → Bool) → Bool :=
  fun r => f (oFrom P U r)

end QMAvsQCMAH


