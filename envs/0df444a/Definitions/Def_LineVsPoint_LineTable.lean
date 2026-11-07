-- Prove2me | Definitions.Def_LineVsPoint_LineTable
-- name    : LineVsPoint_LineTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:00.254998+00:00
-- url     : https://prove2.me/theorems/5c9bafa2-1a04-47f2-8501-25f091dec6a6
-- title:
--   Degree-$d$ line tables and accepted incidences
-- statement:
--   Fix a field $\mathbb F$ and $m\ge 0$. A **line parameterization** chooses for every affine line $L$ of $\mathbb F^m$ a translate $a_L$ and a direction $u_L\neq 0$ with
--
--   $$
--   L=\{a_L+tu_L : t\in\mathbb F\},
--   $$
--
--   and writes $L(t):=a_L+tu_L$. A **degree-$d$ line table** $\{P_L\}_{L\in\mathcal L_{q,m}}$ adds, for every line $L$, a formal univariate polynomial $p_L\in\mathbb F[t]$ of degree at most $d$; the line function is $P_L(L(t))=p_L(t)$.
--
--   Given a point table $f:\mathbb F^m\to\mathbb F$, an incident pair $(x,L)$ with $x\in L$ is **accepted** when $P_L(x)=f(x)$, that is, when $p_L(t)=f(x)$ at the unique parameter $t$ with $L(t)=x$.
--
--   The table is total (every line carries a polynomial) and its degree bound is on the formal polynomial. These are the objects tested by the line–versus–point test.
--
--   **Formalization Note** `LinePar F m` holds the parameterization (`a`, `u`, `u_ne`, `range_eq`), `LineTable F m d` extends it with `p` and `natDegree_le`, and `Accepted f P x L` is $x\in L$ together with the existence of $t$ with $a_L+tu_L=x$ and $p_L(t)=f(x)$. Every statement of the mission quantifies over all parameterizations, as the paper fixes them arbitrarily.
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), §1.1, p.4; §1.2, p.5

import Definitions.Def_LineVsPoint_AffFlat

set_option autoImplicit false

namespace LineVsPoint

/-- A **fixed affine parameterization of every line** of `F^m`: Dao, Kominers, Thaler, Zheng,
*Cube-Root Soundness Is Optimal for the Line–versus–Point Test* (manuscript, sha256 328a8943…),
§1.1, p.4: "For every affine line `L`, fix once and for all an affine parameterization,
consisting of translate `a_L ∈ L` and direction `u_L`, and write `L(t) := a_L + t u_L`."

**Formalization Note.** The parameterization is data; every statement quantifies over all of
them, since the paper fixes it arbitrarily. `range_eq` says `t ↦ a_L + t u_L` sweeps out exactly
`L` (so `a_L ∈ L`), and `u_ne` that `u_L ≠ 0`. -/
structure LinePar (F : Type*) [Field F] (m : ℕ) where
  /-- The translate `a_L`. -/
  a : Line F m → Fin m → F
  /-- The direction `u_L`. -/
  u : Line F m → Fin m → F
  /-- `u_L ≠ 0`. -/
  u_ne : ∀ L, u L ≠ 0
  /-- `L = {a_L + t u_L : t ∈ F}`. -/
  range_eq : ∀ L, L.carrier = Set.range (fun t : F => a L + t • u L)

/-- A **degree-`d` line table** `{P_L}_{L ∈ L_{q,m}}` (p.4): for every affine line `L` of `F^m`
a formal univariate polynomial `p_L ∈ F[t]` of degree at most `d`, read in the line's fixed
parameterization, so that `P_L(L(t)) = p_L(t)`. Manuscript (sha256 328a8943…), §1.1, p.4.

**Formalization Note.** The table is total: every line carries a polynomial. Degrees are formal
(`natDegree`), not degrees of functions on `F`. -/
structure LineTable (F : Type*) [Field F] (m d : ℕ) extends LinePar F m where
  /-- The line polynomial `p_L ∈ F[t]`. -/
  p : Line F m → Polynomial F
  /-- `deg p_L ≤ d`. -/
  natDegree_le : ∀ L, (p L).natDegree ≤ d

/-- An **accepted incidence** `(x, L)` of the line–versus–point test (p.4): `x ∈ L` and
`P_L(x) = f(x)`, i.e. `p_L(t) = f(x)` at the parameter `t` with `L(t) = x`.
Manuscript (sha256 328a8943…), §1.1, p.4 and §1.2, p.5 ("accepted incidences").

**Formalization Note.** The parameter `t` with `a_L + t u_L = x` is unique (`u_L ≠ 0`), so the
existential is the value `P_L(x)`. -/
def Accepted {F : Type*} [Field F] {m d : ℕ} (f : (Fin m → F) → F) (P : LineTable F m d)
    (x : Fin m → F) (L : Line F m) : Prop :=
  x ∈ L.carrier ∧ ∃ t : F, P.a L + t • P.u L = x ∧ (P.p L).eval t = f x

end LineVsPoint


