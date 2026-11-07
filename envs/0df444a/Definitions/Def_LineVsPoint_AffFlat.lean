-- Prove2me | Definitions.Def_LineVsPoint_AffFlat
-- name    : LineVsPoint_AffFlat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:02.495751+00:00
-- url     : https://prove2.me/theorems/b68c818d-2ff0-41b0-969a-3830bfa59b3f
-- title:
--   Affine $k$-flats, lines and planes of $\mathbb F^m$, as sets
-- statement:
--   Let $\mathbb F$ be a field and $1\le k$, $m\ge 0$. An **affine $k$-dimensional subspace** (affine $k$-flat) of $\mathbb F^m$ is a set of the form
--
--   $$
--   W=\{a+t_1u_1+\dots+t_ku_k : t_1,\dots,t_k\in\mathbb F\},
--   $$
--
--   where $a\in\mathbb F^m$ and $u_1,\dots,u_k\in\mathbb F^m$ are linearly independent. Flats of dimension $1$ and $2$ are **lines** and **planes**; $\mathcal L_{q,m}$ denotes the set of lines and $\mathcal P_{m,q}$ the set of planes of $\mathbb F_q^m$.
--
--   Every flat is counted once as a set, however many parameterizations $(a,u_1,\dots,u_k)$ describe it. Uniform choices of a line or a plane in the line–versus–point and plane–versus-plane tests are uniform over these sets. Over a finite field there are finitely many flats.
--
--   **Formalization Note** `AffFlat F m k` is a structure holding the point set together with the proof that it has the displayed form; `Line F m` and `Plane F m` are the cases $k=1,2$. A parameterization is not part of a flat: line and plane tables supply one.
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), §2.1, p.10; §1.1, p.4; §4, p.17

import Mathlib

set_option autoImplicit false

namespace LineVsPoint

/-- An **affine `k`-dimensional subspace** (affine `k`-flat) of `F^m`, as a set: Dao, Kominers,
Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test* (manuscript,
sha256 328a8943…), §2.1, p.10: "It has the form `{a + u₁t₁ + ⋯ + u_k t_k : t₁, …, t_k ∈ F_q}`,
where `u₁, …, u_k` are linearly independent." Lines (`k = 1`) and planes (`k = 2`) are
`Line F m` and `Plane F m`.

**Formalization Note.** A flat is its point set (`carrier`); each flat is one element of
`AffFlat F m k`, however many parameterizations `(a, u)` it has, so uniform choices of a line or
a plane are uniform over the sets, as in the paper (`L_{q,m}`, `P_{m,q}`). The parameterization
is not part of the flat; tables supply it (`LinePar`, `PlanePar`). -/
@[ext]
structure AffFlat (F : Type*) [Field F] (m k : ℕ) where
  /-- The point set of the flat. -/
  carrier : Set (Fin m → F)
  /-- It is `{a + ∑ᵢ tᵢ • vᵢ}` for a base point `a` and linearly independent directions `v`. -/
  isFlat : ∃ (a : Fin m → F) (v : Fin k → Fin m → F), LinearIndependent F v ∧
    carrier = Set.range (fun t : Fin k → F => a + ∑ i, t i • v i)

/-- Affine lines of `F^m` (the set `L_{q,m}` of p.4), as sets. -/
abbrev Line (F : Type*) [Field F] (m : ℕ) := AffFlat F m 1

/-- Affine planes of `F^m` (the set `P_{m,q}` of p.17), as sets. -/
abbrev Plane (F : Type*) [Field F] (m : ℕ) := AffFlat F m 2

instance AffFlat.instFinite (F : Type*) [Field F] [Finite F] (m k : ℕ) :
    Finite (AffFlat F m k) :=
  Finite.of_injective AffFlat.carrier (fun _ _ h => AffFlat.ext h)

noncomputable instance AffFlat.instFintype (F : Type*) [Field F] [Finite F] (m k : ℕ) :
    Fintype (AffFlat F m k) :=
  Fintype.ofFinite _

end LineVsPoint


