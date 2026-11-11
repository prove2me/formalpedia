-- Prove2me | Definitions.Def_GoldProxGap_goldMoment
-- name    : GoldProxGap_goldMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:48.2307+00:00
-- url     : https://prove2.me/theorems/8d485d37-a3cd-4522-bf3b-4d4bf7455261
-- title:
--   Alternating binary matrices, $\mathbb F_2$-independence, Gold moments $M_k(A)$ and the pairing $\langle A,B\rangle$
-- statement:
--   An **alternating binary matrix** is a symmetric $d\times d$ matrix over $\mathbb F_2$ with zero diagonal. For $\omega_1,\dots,\omega_d$ in a finite field $\mathbb B$ of characteristic two, linearly independent over $\mathbb F_2$, the **$k$-th Gold moment** of $A$ is
--   $$
--   M_k(A)=\sum_{i<j}A_{ij}\bigl(\omega_i\omega_j^{2^k}+\omega_j\omega_i^{2^k}\bigr)\in\mathbb B .
--   $$
--   For two alternating matrices, $\langle A,B\rangle=\sum_{i<j}A_{ij}B_{ij}\in\mathbb F_2$.
--
--   The equations $M_1(A)=\dots=M_{t-1}(A)=0$ are the constraints that make the quadratic functions of the Gold construction yield polynomials with many roots; the pairing is the one under which the Delsarte–Goethals moment identity counts their solutions.
--
--   **Formalization Note** Matrices are indexed by `Fin d` ($0$-based). An entry $A_{ij}\in\mathbb F_2$ enters $\mathbb B$ as $0$ or $1$. Linear independence over $\mathbb F_2$ (`F2LinIndep`) is stated separately as: no nonempty subfamily of the $\omega_i$ sums to zero.
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Definition 3.15, p.24; Definition 5.7, p.39; proof of Lemma 5.13, p.42

import Mathlib

namespace GoldProxGap

/-!
# Alternating binary matrices and Gold moments

Dao, Kominers, Thaler, Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary
Fields*, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), Definition 3.15
(p.24), Definition 5.7 (p.39), and the pairing `⟨A, B⟩` of the proof of Lemma 5.13 (p.42).

**Formalization Note.**
* Matrices are `Matrix (Fin d) (Fin d) (ZMod 2)`; "alternating binary" is symmetric over `F₂`
  with zero diagonal (Definition 3.15). Indices are `0`-based (`Fin d`), the paper's are `1`-based.
* In `goldMoment ω A k`, an entry `A i j ∈ F₂` enters `B` as `0` or `1` (`ZMod.val`, cast).
  Definition 5.7 asks the `ω i` to be linearly independent over `F₂`; this is `F2LinIndep ω`,
  stated separately: no nonempty subfamily of the `ω i` sums to zero.
* `altPairing A B = Σ_{i<j} A_ij B_ij ∈ F₂`.
-/

/-- Definition 3.15: an alternating binary matrix (symmetric over `F₂`, zero diagonal). -/
def IsAltBin {d : ℕ} (A : Matrix (Fin d) (Fin d) (ZMod 2)) : Prop :=
  A.IsSymm ∧ ∀ i, A i i = 0

/-- Linear independence over `F₂` of `ω₁, …, ω_d ∈ B`: no nonempty subfamily sums to zero. -/
def F2LinIndep {B : Type*} [AddCommMonoid B] {d : ℕ} (ω : Fin d → B) : Prop :=
  ∀ s : Finset (Fin d), s.Nonempty → ∑ i ∈ s, ω i ≠ 0

/-- Definition 5.7: the `k`-th Gold moment
`M_k(A) = Σ_{i<j} A_ij (ω_i ω_j^{2^k} + ω_j ω_i^{2^k}) ∈ B`. -/
noncomputable def goldMoment {B : Type*} [Field B] {d : ℕ} (ω : Fin d → B)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (k : ℕ) : B :=
  ∑ i : Fin d, ∑ j ∈ Finset.Ioi i,
    ((A i j).val : B) * (ω i * ω j ^ (2 ^ k) + ω j * ω i ^ (2 ^ k))

/-- The pairing `⟨A, B⟩ = Σ_{i<j} A_ij B_ij ∈ F₂` of alternating matrices (p.42). -/
def altPairing {d : ℕ} (A B : Matrix (Fin d) (Fin d) (ZMod 2)) : ZMod 2 :=
  ∑ i : Fin d, ∑ j ∈ Finset.Ioi i, A i j * B i j

end GoldProxGap


