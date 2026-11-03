-- Prove2me | Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel
-- name    : WildeQIT_EntBreaking_IsQuantumChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:08.321962+00:00
-- url     : https://prove2.me/theorems/f595dc40-ae7e-4e7c-93bb-2f53ed5b03ce
-- title:
--   Quantum channel — a linear, completely positive, trace-preserving map (Definition 4.4.3)
-- statement:
--   Let $\mathcal H_A$ and $\mathcal H_B$ be finite-dimensional Hilbert spaces and let $\mathcal N:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_B)$ be a linear map. Then $\mathcal N$ is a **quantum channel** when
--
--   1. $\mathcal N$ is **completely positive** (Definition 4.4.2): for a reference system $R$ of every finite size, the map $\mathrm{id}_R\otimes\mathcal N$ sends positive semidefinite operators on $\mathcal H_R\otimes\mathcal H_A$ to positive semidefinite operators on $\mathcal H_R\otimes\mathcal H_B$, where $(\mathrm{id}_R\otimes\mathcal N)\big(\sum_{i,j}|i\rangle\langle j|_R\otimes X^{i,j}_A\big)=\sum_{i,j}|i\rangle\langle j|_R\otimes\mathcal N(X^{i,j}_A)$;
--   2. $\mathcal N$ is **trace preserving** (Criterion 4.4.3): $\operatorname{Tr}\{\mathcal N(X_A)\}=\operatorname{Tr}\{X_A\}$ for every $X_A\in\mathcal L(\mathcal H_A)$.
--
--   This is the book's notion of a physical evolution; every theorem of the mission is about such maps.
--
--   **Formalization Note** Operators on $\mathcal H_A$ are complex matrices indexed by a finite type, and linearity is carried by the type of $\mathcal N$. Complete positivity is the published `QAlgorithms.Entanglement.IsCompletelyPositive`, with the reference $\mathbb C^r$ (every $r$) as the first tensor factor; every finite-dimensional reference is isomorphic to one of these.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 4.4.3, p. 150; Criterion 4.4.1, p. 149; Definition 4.4.2 and Criterion 4.4.3, p. 150

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §4.4.1,
Definition 4.4.3 (Quantum Channel), p. 150, with Criterion 4.4.1 (Linearity, p. 149),
Definition 4.4.2 (Completely Positive Map, p. 150) and Criterion 4.4.3 (Trace Preservation, p. 150).
-/

namespace WildeQIT.EntBreaking

open scoped Matrix

/-- **Definition 4.4.3 (Quantum Channel)**, Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 150: "A quantum channel is a linear, completely positive, trace preserving
map". A map `N : L(ℋ_A) → L(ℋ_B)` is a `ℂ`-linear map `Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ`
(Criterion 4.4.1); it is a quantum channel when

1. it is completely positive (Definition 4.4.2, p. 150): `id_R ⊗ N` is a positive map for a
   reference system `R` of every finite size; this is `QAlgorithms.Entanglement.IsCompletelyPositive`,
   whose reference is the first tensor factor `Fin r × a`, as in the book's (4.180)–(4.184);
2. it is trace preserving on all operators (Criterion 4.4.3, p. 150): `Tr{N(X)} = Tr{X}` for every
   `X ∈ L(ℋ_A)`.

**Formalization Note.** Hilbert spaces are finite dimensional (the book's setting): operators on
`ℋ_A` are complex matrices indexed by a finite type `a`. Linearity is carried by the type of `N`.
Every finite-dimensional reference space is isomorphic to `ℂ^r` for some `r`, so quantifying over
`Fin r` covers a reference of arbitrary size. -/
def IsQuantumChannel {a b : Type} [Fintype a] [Fintype b]
    (N : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ) : Prop :=
  QAlgorithms.Entanglement.IsCompletelyPositive N ∧ ∀ X : Matrix a a ℂ, (N X).trace = X.trace

end WildeQIT.EntBreaking


