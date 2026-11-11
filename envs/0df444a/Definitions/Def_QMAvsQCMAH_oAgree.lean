-- Prove2me | Definitions.Def_QMAvsQCMAH_oAgree
-- name    : QMAvsQCMAH_oAgree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:10.217531+00:00
-- url     : https://prove2.me/theorems/e2f40cf6-8d85-47c6-8e1e-252013bd1ae0
-- title:
--   Oracles $\mathcal O_F^R$ agreeing outside a set
-- statement:
--   For $C:\mathcal X\to\{0,1\}$, a set $F\subseteq\mathcal X$ and $R:F\to\{0,1\}$,
--   $$\mathcal O_F^R(u)=\begin{cases}R(u),&u\in F,\\C(u),&u\notin F.\end{cases}$$
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Definition 19, p.31

import Mathlib

set_option autoImplicit false

namespace QMAvsQCMAH

/-- The oracle `O_F^R` that **agrees with `C` outside `F`**: `O_F^R(u) = R(u)` for `u ∈ F` and
`C(u)` for `u ∉ F`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Definition 19, p.31 (PDF p.34): "For a Boolean function C : X → {0, 1}, a set F ⊆ X and
R : F → {0, 1}, we define O_F^R, which agrees with C outside F, by O_F^R(u) = R(u), u ∈ F,
C(u), u ∉ F." -/
def oAgree {X : Type} [DecidableEq X] (C : X → Bool) (F : Finset X) (R : {u // u ∈ F} → Bool) :
    X → Bool :=
  fun u => if h : u ∈ F then R ⟨u, h⟩ else C u

end QMAvsQCMAH


