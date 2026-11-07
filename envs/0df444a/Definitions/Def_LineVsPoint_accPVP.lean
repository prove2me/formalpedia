-- Prove2me | Definitions.Def_LineVsPoint_accPVP
-- name    : LineVsPoint_accPVP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:44.242088+00:00
-- url     : https://prove2.me/theorems/ef3a4b79-96ab-4ce7-b6aa-f61a56e93726
-- title:
--   Acceptance probability $\mathrm{Acc}_{\mathrm{PVP}}(T)$ of the plane–versus–plane test
-- statement:
--   The **affine Grassmann graph** on the planes of $\mathbb F^m$ joins $P$ and $P'$ when $P\cap P'$ is a line. Let $G$ be the uniform distribution on its (ordered) edges. For a plane table $T$,
--
--   $$
--   \mathrm{Acc}_{\mathrm{PVP}}(T):=\Pr_{(P,P')\sim G}\bigl[T(P)|_{P\cap P'}=T(P')|_{P\cap P'}\bigr].
--   $$
--
--   This is the acceptance probability of the plane–versus–plane test of Bhangale and Richelson, which the paper uses to pass from planes to higher dimensions.
--
--   **Formalization Note** `pvpEdges F m` is the set of ordered pairs of planes meeting in a line, and the event is that the two plane polynomials take the same value at every point of $P\cap P'$ (`PlanesAgree`). For $d<q$ this is the same as equality of the two restricted polynomials of degree at most $d$.
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), §4, p.18

import Definitions.Def_LineVsPoint_PlaneTable

set_option autoImplicit false

namespace LineVsPoint

/-- A set of points of `F^m` **is an affine line**. -/
def IsLineSet {F : Type*} [Field F] {m : ℕ} (S : Set (Fin m → F)) : Prop :=
  ∃ L : Line F m, L.carrier = S

open Classical in
/-- The edges of the **affine Grassmann graph** on planes: ordered pairs `(P, P′)` of affine planes
of `F^m` with `P ∩ P′` a line. Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for
the Line–versus–Point Test* (manuscript, sha256 328a8943…), p.18: "the affine Grassmann graph on
`P_{m,q}`, where `P` and `P′` are adjacent when `P ∩ P′` is a line". -/
noncomputable def pvpEdges (F : Type*) [Field F] [Fintype F] (m : ℕ) :
    Finset (Plane F m × Plane F m) :=
  Finset.univ.filter fun PP => IsLineSet (PP.1.carrier ∩ PP.2.carrier)

/-- The plane polynomials `T(P)` and `T(P′)` **agree on `P ∩ P′`**: at every common point `x`,
the value of `T(P)` at the parameters of `x` in `P` equals the value of `T(P′)` at the parameters
of `x` in `P′`. -/
def PlanesAgree {F : Type*} [Field F] {m d : ℕ} (T : PlaneTable F m d) (P P' : Plane F m) :
    Prop :=
  ∀ s t s' t' : F, T.a P + s • T.u₁ P + t • T.u₂ P = T.a P' + s' • T.u₁ P' + t' • T.u₂ P' →
    MvPolynomial.eval ![s, t] (T.T P) = MvPolynomial.eval ![s', t'] (T.T P')

open Classical in
/-- The **acceptance probability of the plane–versus–plane test**, manuscript (sha256 328a8943…),
p.18: "`Acc_PVP(T) := Pr_{(P,P′) ∼ G}[T(P)|_{P∩P′} = T(P′)|_{P∩P′}]`", with `G` the uniform edge
distribution on the affine Grassmann graph.

**Formalization Note.** The event is equality of the two restrictions as functions on the line
`P ∩ P′` (`PlanesAgree`); for `d < q` this is the same as equality of the restricted degree-`≤ d`
polynomials. -/
noncomputable def accPVP {F : Type*} [Field F] [Fintype F] {m d : ℕ} (T : PlaneTable F m d) :
    ℝ :=
  (((pvpEdges F m).filter fun PP => PlanesAgree T PP.1 PP.2).card : ℝ) /
    ((pvpEdges F m).card : ℝ)

end LineVsPoint


