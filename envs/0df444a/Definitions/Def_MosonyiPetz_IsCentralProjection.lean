-- Prove2me | Definitions.Def_MosonyiPetz_IsCentralProjection
-- name    : MosonyiPetz_IsCentralProjection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:18.268644+00:00
-- url     : https://prove2.me/theorems/77910eb7-d9a2-4592-8b57-faa3cc5fb7fb
-- title:
--   Central projection of a $*$-subalgebra
-- statement:
--   Let $\mathcal A$ be a unital $*$-subalgebra of $\mathcal B(\mathcal K)$ and $\mathcal A'$ its commutant (the matrices commuting with every element of $\mathcal A$). A matrix $z$ is a **central projection of $\mathcal A$** if
--
--   1. $z\in\mathcal A$ and $z\in\mathcal A'$;
--   2. $z$ is an orthogonal projection: $z^2=z=z^*$.
--
--   These are the projections of the centre $\mathcal A\cap\mathcal A'$.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, pp.5–6 and p.9

import Mathlib

open scoped Matrix

namespace MosonyiPetz

/-- **A central projection of a subalgebra.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, pp.5–6 and p.9: the projections `P_{m,d}`, `P_m` "commute with elements of A", and "the
minimal central projections in D_K".

`IsCentralProjection A z` holds when `z ∈ A`, `z` commutes with every element of `A` (`z` lies
in the commutant `A′`), and `z` is an orthogonal projection: `z * z = z` and `zᴴ = z`.

**Formalization Note.** `A` is a unital *-subalgebra of `Matrix K K ℂ` (`StarSubalgebra`); the
commutant `A′` is `Set.centralizer A`. -/
def IsCentralProjection {K : Type*} [Fintype K] [DecidableEq K] (A : StarSubalgebra ℂ (Matrix K K ℂ))
    (z : Matrix K K ℂ) : Prop :=
  z ∈ A ∧ z ∈ Set.centralizer (A : Set (Matrix K K ℂ)) ∧ z * z = z ∧ zᴴ = z

end MosonyiPetz


