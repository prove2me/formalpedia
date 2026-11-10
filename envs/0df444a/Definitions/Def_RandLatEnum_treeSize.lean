-- Prove2me | Definitions.Def_RandLatEnum_treeSize
-- name    : RandLatEnum_treeSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:18.72602+00:00
-- url     : https://prove2.me/theorems/1c9213fb-a7f4-4869-862d-7b2bdc263e54
-- title:
--   Enumeration tree size $T(B,R)=1+\sum_{d=1}^n N_d(B,R)$
-- statement:
--   The **full enumeration tree** of an ordered basis $B$ of a rank-$n$ lattice at radius $R$ has
--   $$
--   T(B,R)=1+\sum_{d=1}^{n}N_d(B,R)
--   $$
--   nodes: the root ($d=0$) and, at each depth $d$, the points of the projected lattice $\pi_{n-d+1}(L)$ in the ball of radius $R$. The paper's tree size is $T(B)=T(B,\lambda_1(L))$, the number of nodes of the full enumeration tree at radius $\lambda_1(L)$ ((1.1), p.2).
--
--   This is the cost of enumeration (Fincke–Pohst / Kannan style SVP search) on the basis $B$, and the quantity bounded in Theorem 1.5.
--
--   **Formalization Note** The sum runs over the 0-based projection indices $j=n-d\in\{0,\dots,n-1\}$; the leading $1$ is the root.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §3.1, (3.1), p.17; (1.1), p.2

import Mathlib
import Definitions.Def_RandLatEnum_levelCount

namespace RandLatEnum

/-- The size of the full enumeration tree, `T(B, R) = 1 + Σ_{d=1}^{n} N_d(B, R)` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §3.1,
(3.1), p.17); `T(B) = T(B, λ₁(L))` by (1.1), p.2.

**Formalization Note.** The `1` is the root (`d = 0`); the sum runs over the 0-based projection
indices `j = n − d ∈ {0, …, n−1}`, i.e. over the levels `d = 1, …, n`. -/
noncomputable def treeSize {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (R : ℝ) : ℕ :=
  1 + ∑ j : Fin m, levelCount b j R

end RandLatEnum


