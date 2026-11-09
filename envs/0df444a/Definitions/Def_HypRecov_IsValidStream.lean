-- Prove2me | Definitions.Def_HypRecov_IsValidStream
-- name    : HypRecov_IsValidStream
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:50.089199+00:00
-- url     : https://prove2.me/theorems/f910d812-1c65-4b45-ba3c-c8bc3899d6e0
-- title:
--   Valid anonymous $q$-projection streams and their net count vector
-- statement:
--   A **stream** is a finite list of updates $(A,\Delta)$, where $A\subseteq V$ and $\Delta\in\mathbb Z$; an update adds $\Delta$ to the count $y_A$. The **net count vector** of a stream $\sigma$ is
--   $$\mathrm{net}_\sigma(A)=\sum_{(A,\Delta)\in\sigma}\Delta ,$$
--   the sum of the increments applied to $A$, which does not depend on the order of the updates.
--
--   The stream is a **valid $q$-projection stream** of the hypergraph $H$ if every update is on a set of size $q$ and, for every $q$-set $A$,
--   $$\mathrm{net}_\sigma(A)=|\{e\in E(H):\ A\subseteq e\}| ,$$
--   that is, the terminal state is $y=W_{q,r}x$, the complete $q$-projection of $H$ (eq. (2)). Intermediate counts are arbitrary signed integers, every ordering is allowed, and insertion-only streams are a special case.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), §1.1, pp.1–2 (PDF pp.2–3); §2, p.5 (PDF p.6), eq. (2)

import Mathlib

namespace HypRecov

/-- The net count vector of a stream: `net σ A` is the sum of the increments the stream applies
to the vertex set `A`. Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous Projection Streams*,
STOC 2027 submission (manuscript sha256 719dcfff…), §2, p.5 (PDF p.6): "An input update (A, ∆) adds
an integer ∆ to coordinate y_A." -/
def net {n : ℕ} (σ : List (Finset (Fin n) × ℤ)) (A : Finset (Fin n)) : ℤ :=
  ((σ.filter (fun u => decide (u.1 = A))).map Prod.snd).sum

/-- **Valid anonymous `q`-projection stream of `H`.** Ibid., §1.1, pp.1–2 and §2, p.5, eq. (2): "An
update adds an integer to the count of a q-vertex subset. The terminal counts form the complete
q-projection of H, and prefixes may contain arbitrary signed counts." "The terminal state satisfies
y = W_{q,r}x. Intermediate counts may be arbitrary integers."

`IsValidStream E q σ`: every update is on a `q`-set, and for every `q`-set `A` the increments on `A`
add up to the number of edges of `E` containing `A`.

**Formalization Note.** A stream is a finite list of updates `(A, Δ)`, in any order, with signed
increments and no condition on prefixes; insertion-only streams are a special case. -/
def IsValidStream {n : ℕ} (E : Finset (Finset (Fin n))) (q : ℕ) (σ : List (Finset (Fin n) × ℤ)) :
    Prop :=
  (∀ u ∈ σ, u.1.card = q) ∧
    ∀ A : Finset (Fin n), A.card = q → net σ A = ((E.filter (fun e => A ⊆ e)).card : ℤ)

end HypRecov


