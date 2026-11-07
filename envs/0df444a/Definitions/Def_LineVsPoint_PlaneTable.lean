-- Prove2me | Definitions.Def_LineVsPoint_PlaneTable
-- name    : LineVsPoint_PlaneTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:54.047139+00:00
-- url     : https://prove2.me/theorems/6e0d49d1-ac13-49fd-96aa-22566267881a
-- title:
--   Degree-$d$ plane tables, restrictions $Q|_P$ and plane–point agreement
-- statement:
--   A **degree-$d$ plane table** $T$ on $\mathbb F^m$ assigns to every affine plane $P$ a polynomial $T(P)$ of total degree at most $d$ on $P$, read in a fixed parameterization of $P$: a base point $a_P$ and linearly independent directions $u_{1,P},u_{2,P}$ with $P=\{a_P+su_{1,P}+tu_{2,P}\}$, and $T(P)\in\mathbb F[s,t]$.
--
--   For a global polynomial $Q\in\mathbb F[X_1,\dots,X_m]$, its **restriction** to $P$ is $Q|_P(s,t)=Q(a_P+su_{1,P}+tu_{2,P})\in\mathbb F[s,t]$. For a point table $f$, the **plane–point agreement** of $P$ is
--
--   $$
--   \Pr_{x\in P}\bigl[T(P)(x)=f(x)\bigr],
--   $$
--
--   the fraction of points of $P$ at which $T(P)$, evaluated at the parameters of the point, equals $f$.
--
--   **Formalization Note** `PlaneTable F m d` stores the parameterization and the polynomials; `planeRestrict T Q P` is the restriction and `planeAgr f T P` the agreement. The event $T(P)=Q|_P$ of Theorem 4.2 is read as the formal identity, which for $d<q$ coincides with equality of functions on $P$.
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), §4, pp.17–18; Theorem 4.2 and Lemma 4.3, p.18

import Definitions.Def_LineVsPoint_AffFlat

set_option autoImplicit false

namespace LineVsPoint

/-- A **degree-`d` plane table** on `F^m`: Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is
Optimal for the Line–versus–Point Test* (manuscript, sha256 328a8943…), §4, pp.17–18 ("For a
plane table `T`", "a degree-`d` plane table `T`"): for every affine plane `P` a polynomial
`T(P)` of total degree at most `d` on `P`, read in a fixed parameterization of `P`, as for lines
(§1.1, p.4).

**Formalization Note.** Each plane carries a base point `a P` and linearly independent
directions `u₁ P, u₂ P` with `P = {a P + s u₁ P + t u₂ P}`; `T P ∈ F[s, t]` (the variables `0, 1`
of `MvPolynomial (Fin 2) F`) has formal total degree `≤ d`, and its value at the point
`a P + s u₁ P + t u₂ P` is `T P (s, t)`. Statements quantify over every parameterization. -/
structure PlaneTable (F : Type*) [Field F] (m d : ℕ) where
  /-- Base point of the plane. -/
  a : Plane F m → Fin m → F
  /-- First direction. -/
  u₁ : Plane F m → Fin m → F
  /-- Second direction. -/
  u₂ : Plane F m → Fin m → F
  /-- The two directions are linearly independent. -/
  indep : ∀ P, LinearIndependent F ![u₁ P, u₂ P]
  /-- `P = {a + s u₁ + t u₂ : s, t ∈ F}`. -/
  range_eq : ∀ P, P.carrier = Set.range (fun st : F × F => a P + st.1 • u₁ P + st.2 • u₂ P)
  /-- The plane polynomial `T(P) ∈ F[s, t]`. -/
  T : Plane F m → MvPolynomial (Fin 2) F
  /-- `deg T(P) ≤ d`. -/
  totalDegree_le : ∀ P, (T P).totalDegree ≤ d

open Polynomial in
/-- The **restriction `Q|_P` of a global polynomial to a parameterized plane**: for
`Q ∈ F[X₁, …, X_m]` and the plane `P` with the table's parameterization,
`Q(a P + s u₁ P + t u₂ P) ∈ F[s, t]`. Manuscript (sha256 328a8943…), Theorem 4.2, p.18
("`T(P) = Q|_P`").

**Formalization Note.** "`T(P) = Q|_P`" is read as the formal identity
`planeRestrict T Q P = T.T P` in `F[s, t]` (for `d < q` the same as equality of functions on
`P`). -/
noncomputable def planeRestrict {F : Type*} [Field F] {m d : ℕ} (T : PlaneTable F m d)
    (Q : MvPolynomial (Fin m) F) (P : Plane F m) : MvPolynomial (Fin 2) F :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (T.a P i) + MvPolynomial.C (T.u₁ P i) *
    MvPolynomial.X 0 + MvPolynomial.C (T.u₂ P i) * MvPolynomial.X 1) Q

open Classical in
/-- **Plane–point agreement** `Pr_{x ∈ P}[T(P)(x) = f(x)]`: the fraction of the points `x` of
the plane `P` at which the plane polynomial `T(P)`, evaluated at the parameters of `x`, equals
`f(x)`. Manuscript (sha256 328a8943…), Lemma 4.3, p.18. -/
noncomputable def planeAgr {F : Type*} [Field F] [Fintype F] {m d : ℕ}
    (f : (Fin m → F) → F) (T : PlaneTable F m d) (P : Plane F m) : ℝ :=
  ((Finset.univ.filter fun x : Fin m → F => x ∈ P.carrier ∧ ∃ s t : F,
      T.a P + s • T.u₁ P + t • T.u₂ P = x ∧ MvPolynomial.eval ![s, t] (T.T P) = f x).card : ℝ) /
    ((Finset.univ.filter fun x : Fin m → F => x ∈ P.carrier).card : ℝ)

end LineVsPoint


