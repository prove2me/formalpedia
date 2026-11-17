-- Prove2me | Definitions.Def_LiftSAParity_Supplement_bphp
-- name    : LiftSAParity_Supplement_bphp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:15:09.19347+00:00
-- url     : https://prove2.me/theorems/f4f8f355-0cbd-422e-b867-3b657f3da5ec
-- title:
--   The binary pigeonhole principle $\mathrm{BPHP}^m_n$, $n=2^k$
-- statement:
--   Let $m\ge1$ and $k\ge0$, and let $n=2^k$. The **binary pigeonhole principle** $\mathrm{BPHP}^m_n$ has variables $x_{u,t}$ for pigeons $u\in[m]$ and bits $t\in[k]$; the bits $(x_{u,1},\dots,x_{u,k})$ encode the hole of pigeon $u$. For every pair of distinct pigeons $u\neq u'$ and every hole $a\in\{0,1\}^k$ it has the clause
--   $$
--   \bigvee_{t\in[k]}(x_{u,t}\neq a_t)\ \vee\ \bigvee_{t\in[k]}(x_{u',t}\neq a_t),
--   $$
--   which is falsified exactly when pigeons $u$ and $u'$ both sit in hole $a$. An assignment satisfies the formula iff the pigeons sit in pairwise distinct holes, so $\mathrm{BPHP}^m_n$ is unsatisfiable iff $m>n$. The blocks are the pigeons, each a block of $k$ variables.
--
--   **Formalization Note** The paper does not list the clauses; this is the standard collision encoding. In the CNF convention the literal $(v,b)$ is true iff $x_v=b$, so $x_{u,t}\neq a_t$ is the literal $((u,t),\lnot a_t)$. The ordered pairs $(u,u')$ and $(u',u)$ give the same clause.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §1.1, p.5; §6.2, p.23

import Mathlib
import Definitions.Def_LiftSAParity_CNF

namespace LiftSAParity

namespace Supplement

/-- The clause of `BPHP^m_n` saying that the distinct pigeons `u ≠ u'` are not both in the hole
`a ∈ {0,1}^k`: `⋁_t (x_{u,t} ≠ a_t) ∨ ⋁_t (x_{u',t} ≠ a_t)`. In the CNF convention the literal
`(v, b)` is true iff `x_v = b`, so `x_{u,t} ≠ a_t` is the literal `((u,t), !a_t)`. -/
def bphpClause {m k : ℕ} (u u' : Fin m) (a : Fin k → Bool) : Clause (Fin m × Fin k) :=
  (Finset.univ.image fun t : Fin k => ((u, t), !a t)) ∪
    (Finset.univ.image fun t : Fin k => ((u', t), !a t))

/-- **The binary pigeonhole principle** `BPHP^m_n`, `n = 2^k` (de Rezende–Engström–Shekhovtsov,
*Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size*, manuscript (sha256
cab5a032…), §1.1, p.5 and §6.2, p.23): "m pigeons cannot sit in n = 2^ℓ holes … For each of m
pigeons we have ℓ bits encoding its hole. The formula's variables are indexed by [m] × [ℓ]."
Blocks are pigeons (`Fin m`), each of `k` bits (`Fin k`).

**Formalization Note** The paper gives no clause list. This is the standard collision CNF: for
every ordered pair of distinct pigeons `u ≠ u'` and every hole `a ∈ {0,1}^k`, the clause
`bphpClause u u' a`, falsified exactly when both pigeons sit in hole `a` (the pairs `(u,u')` and
`(u',u)` give the same clause). An assignment satisfies every clause iff the pigeons sit in
pairwise distinct holes, so the formula is unsatisfiable iff `m > 2^k`. -/
def bphp (m k : ℕ) : CNF (Fin m × Fin k) :=
  ((Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2)) ×ˢ
      (Finset.univ : Finset (Fin k → Bool))).image
    (fun q => bphpClause q.1.1 q.1.2 q.2)

end Supplement

end LiftSAParity


