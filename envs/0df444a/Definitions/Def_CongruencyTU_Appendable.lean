-- Prove2me | Definitions.Def_CongruencyTU_Appendable
-- name    : CongruencyTU_Appendable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:59.706683+00:00
-- url     : https://prove2.me/theorems/c0a5654d-9aeb-404c-9fa4-3c3065596137
-- title:
--   TU-appendable and elementary vectors
-- statement:
--   Let $T\in\mathbb Z^{k\times n}$ be totally unimodular.
--
--   1. A vector $d\in\mathbb Z^n$ is **TU-appendable** to $T$ if the matrix $\begin{pmatrix} d^\top\\ T\end{pmatrix}$ is totally unimodular.
--   2. A vector $x\in\mathbb Z^n$ is **elementary** with respect to $T$ if $d^\top x\in\{-1,0,1\}$ for every $d$ that is TU-appendable to $T$.
--
--   Elementary vectors are the building blocks of the decomposition lemma (Lemma 7); TU-appendable rows are the scalar products that can be confined to short ranges (Lemma 25).
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, Definition 6, p.5 (PDF p.6)

import Mathlib

open Matrix

namespace CongruencyTU

/-- **TU-appendable vector** (Definition 6 (i), Nägele–Santiago–Zenklusen, arXiv:2109.03148v3,
p.5 (PDF p.6)): for a totally unimodular `T ∈ ℤ^{k×n}`, a vector `d ∈ ℤⁿ` is TU-appendable to `T` if
the matrix `(d⊤ ; T)` is totally unimodular.

**Formalization Note.** `(d⊤ ; T)` is `Matrix.fromRows (Matrix.replicateRow (Fin 1) d) T`, rows
indexed by `Fin 1 ⊕ Fin k`. -/
def IsTUAppendable {k n : ℕ} (T : Matrix (Fin k) (Fin n) ℤ) (d : Fin n → ℤ) : Prop :=
  (Matrix.fromRows (Matrix.replicateRow (Fin 1) d) T).IsTotallyUnimodular

/-- **Elementary vector** (Definition 6 (ii), p.5): `x ∈ ℤⁿ` is elementary w.r.t. `T` if
`d⊤x ∈ {−1, 0, 1}` for every `d` TU-appendable to `T`. -/
def IsElementary {k n : ℕ} (T : Matrix (Fin k) (Fin n) ℤ) (x : Fin n → ℤ) : Prop :=
  ∀ d : Fin n → ℤ, IsTUAppendable T d → d ⬝ᵥ x = -1 ∨ d ⬝ᵥ x = 0 ∨ d ⬝ᵥ x = 1

end CongruencyTU


