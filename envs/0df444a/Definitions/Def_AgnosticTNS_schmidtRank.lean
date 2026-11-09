-- Prove2me | Definitions.Def_AgnosticTNS_schmidtRank
-- name    : AgnosticTNS_schmidtRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:11.100858+00:00
-- url     : https://prove2.me/theorems/b81aa3af-bc68-45dc-8c7f-b0df78715556
-- title:
--   Schmidt rank across $A\mid[n]\setminus A$
-- statement:
--   The Schmidt rank of a vector $|\psi\rangle\in(\mathbb C^d)^{\otimes n}$ across the bipartition $A\mid[n]\setminus A$ is the rank of its coefficient matrix $(a,b)\mapsto\psi(a\cup b)$, whose rows are indexed by the labels $a$ of the qudits in $A$ and columns by the labels $b$ of the remaining qudits.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Lemma 3.4, p.20; Eq. (2.7), p.12

import Mathlib

namespace AgnosticTNS

/-- **The Schmidt rank of an `n`-qudit vector across `A | [n]∖A`**, used in Lemma 3.4, p.20 and
Eq. (2.7), p.12 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the rank of the coefficient matrix
`(a, b) ↦ ψ(a ∪ b)` with rows indexed by the labels `a` of the qudits in `A` and columns by the labels
`b` of the qudits outside `A`.

**Formalization Note** `a ∪ b` is the configuration equal to `a` on `A` and to `b` off `A`. -/
noncomputable def schmidtRank {n d : ℕ} (A : Finset (Fin n)) (ψ : (Fin n → Fin d) → ℂ) : ℕ :=
  (Matrix.of fun (a : ↥A → Fin d) (b : {i // i ∉ A} → Fin d) =>
    ψ (fun i => if h : i ∈ A then a ⟨i, h⟩ else b ⟨i, h⟩)).rank

end AgnosticTNS


