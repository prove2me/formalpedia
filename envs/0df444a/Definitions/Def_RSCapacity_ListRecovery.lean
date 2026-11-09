-- Prove2me | Definitions.Def_RSCapacity_ListRecovery
-- name    : RSCapacity_ListRecovery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:51.820806+00:00
-- url     : https://prove2.me/theorems/0b2ed6e9-632e-438e-9d92-4f1fbf4f5481
-- title:
--   Reed–Solomon codes and the list-recovery set $\mathcal L(D,k,\mathbf S,A)$
-- statement:
--   Let $F$ be a field and let $D=\{\alpha_1,\dots,\alpha_n\}\subseteq F$ consist of $n$ distinct points, given as an injective map $\alpha:[n]\to F$. Let $S_1,\dots,S_n\subseteq F$ be finite **lists** (empty lists are allowed). For a polynomial $P\in F[X]$, its number of **list hits** is
--   $$\mathrm{hits}(P)=\bigl|\{i\in[n]: P(\alpha_i)\in S_i\}\bigr|,$$
--   and the **incidence size** of the instance is $M=\sum_{i=1}^n |S_i|$. For a degree bound $k$ and an agreement threshold $A$, the **list-recovery set** is
--   $$\mathcal L(D,k,\mathbf S,A)=\{P\in F[X]:\ \deg P<k,\ \mathrm{hits}(P)\ge A\},$$
--   the set of valid polynomials of Definition 3.1. The **Reed–Solomon code** is
--   $$\mathrm{RS}_F(D,k)=\{(P(\alpha_1),\dots,P(\alpha_n)) : P\in F[X],\ \deg P<k\}.$$
--   Singleton lists $S_i=\{y_i\}$ recover ordinary list decoding of a received word $y$.
--
--   These objects are the input and output of every decoding statement of the mission.
--
--   **Formalization Note** Degrees are `Polynomial.degree`, valued in `WithBot ℕ`, so the zero polynomial satisfies $\deg 0<k$ (the paper's convention that a zero polynomial satisfies every displayed upper degree bound, p.10). The lists are `Finset`s; relative Hamming distance is Mathlib's `hammingDist` divided by $n$.
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), §1, p.1 (PDF 3); §3, p.10 (PDF 12); Definition 3.1, p.11 (PDF 13)

import Mathlib

open Polynomial

set_option autoImplicit false

namespace RSCapacity

/-!
# Reed–Solomon codes and the list-recovery set ℒ(D, k, 𝐒, A)

Jeronimo, *Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon
Codes*, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…): §1, p.1 (PDF 3)
(the code RS_{𝔽_q}(D, k) and ℒ(D, k, 𝐒, A)); §3, p.10 (PDF 12) (relative Hamming distance,
list decodability); Definition 3.1, p.11 (PDF 13) (sparse list-recovery instance, incidence size,
valid polynomials).

**Formalization Note.**
* The evaluation set D = {α_1, …, α_n} is an injective map `α : Fin n → F`.
* The lists S_i are finite sets `S i : Finset F`; empty lists are allowed (Definition 3.1).
* Degrees are `Polynomial.degree` (values in `WithBot ℕ`), so the zero polynomial has degree `⊥`
  and satisfies `deg P < k` ("a zero polynomial satisfies every displayed upper degree bound",
  p.10).
-/

/-- The number of list hits |{i ∈ [n] : P(α_i) ∈ S_i}| of a polynomial `P` (Definition 3.1,
p.11). -/
noncomputable def hits {F : Type*} [Field F] {n : ℕ} (α : Fin n → F) (S : Fin n → Finset F)
    (P : F[X]) : ℕ :=
  {i : Fin n | P.eval (α i) ∈ S i}.ncard

/-- The incidence size M = ∑_{i=1}^n |S_i| of a list-recovery instance (Definition 3.1, p.11). -/
def incidence {F : Type*} {n : ℕ} (S : Fin n → Finset F) : ℕ :=
  ∑ i, (S i).card

/-- The list-recovery set ℒ(D, k, 𝐒, A) = {P ∈ F[X] : deg P < k, |{i : P(α_i) ∈ S_i}| ≥ A}
(p.1; the valid polynomials of Definition 3.1, p.11). -/
noncomputable def listSet {F : Type*} [Field F] {n : ℕ} (α : Fin n → F) (k : ℕ)
    (S : Fin n → Finset F) (A : ℕ) : Set F[X] :=
  {P | P.degree < k ∧ A ≤ hits α S P}

/-- The Reed–Solomon code RS_F(D, k) = {(P(α_1), …, P(α_n)) : P ∈ F[X], deg P < k} (p.1). -/
def rsCode {F : Type*} [Field F] {n : ℕ} (α : Fin n → F) (k : ℕ) : Set (Fin n → F) :=
  {c | ∃ P : F[X], P.degree < k ∧ ∀ i, c i = P.eval (α i)}

end RSCapacity


