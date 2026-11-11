-- Prove2me | Definitions.Def_QCollLB_Buckets
-- name    : QCollLB_Buckets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:11.743751+00:00
-- url     : https://prove2.me/theorems/ff686d4d-3455-4a97-8eba-7f895c294a70
-- title:
--   Definitions 5.23, 6.1 — public buckets, Permutation Bucket Finding, the inputs $x^\pi$ and the balanced set $X^\iota_{n,k}$
-- statement:
--   Fix $k\ge2$ and $n=kN$. A **public bucket map** is the label map $b:[n]\to[N]$ of a partition $[n]=B_1\sqcup\dots\sqcup B_N$ with $|B_y|=k$, $b(u)=y$ for $u\in B_y$. The target family is $\mathcal B=\{B_1,\dots,B_N\}$.
--
--   **Permutation Bucket Finding.** Given forward access to $\pi\in S_n$, a valid output is $\rho\subseteq[n]$ with $|\rho|=k$ and $\pi(\rho)=B_y$ for some $y$.
--
--   **Balanced inputs.** For an injection $\iota:[N]\hookrightarrow\mathbb Z_q$ (so $q\ge N$),
--   $$
--   X^\iota_{n,k}=\{x\in\mathbb Z_q^n:\ |\{i:x_i=\iota(y)\}|=k\ \text{for every }y\in[N]\},
--   $$
--   and for $\pi\in S_n$ the input $x^\pi$ has entries $x^\pi_i=\iota(b(\pi(i)))$.
--
--   These objects connect $k$-to-one finding with a uniformly random permutation.
--
--   **Formalization Note** Slots are `Fin n` and labels `Fin N` (0-based). A bucket map is any `b : Fin n → Fin N` all of whose fibres have size $k$; this forces $n=kN$.
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Definition 5.23 p.42, p.43, Definition 6.1 p.46, p.47

import Mathlib

namespace QCollLB

/-- `b : [n] → [N]` is the label map of a partition `[n] = B_1 ⊔ ⋯ ⊔ B_N` into public buckets of
size `k`, `b(u) = y` for `u ∈ B_y` (Peng–Wu, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc),
Definition 5.23, p.42, and p.43).

**Formalization Note.** Slots `[n]` are `Fin n` and bucket labels `[N]` are `Fin N` (0-based).
Every fibre having size `k` forces `n = kN`. -/
def IsBucketMap {n N : ℕ} (k : ℕ) (b : Fin n → Fin N) : Prop :=
  ∀ y, (Finset.univ.filter fun u => b u = y).card = k

/-- The public bucket `B_y = b⁻¹(y)` (arXiv:2611.01767, Definition 5.23, p.42). -/
def bucket {n N : ℕ} (b : Fin n → Fin N) (y : Fin N) : Finset (Fin n) :=
  Finset.univ.filter fun u => b u = y

/-- The target family `𝓑 = {B_1, …, B_N}` of the buckets (arXiv:2611.01767, p.43). -/
def bucketFamily {n N : ℕ} (b : Fin n → Fin N) : Finset (Finset (Fin n)) :=
  Finset.univ.image (bucket b)

/-- `ρ` is a valid output of Permutation Bucket Finding on `π`: `|ρ| = k` and `π(ρ) = B_y` for
some `y ∈ [N]` (arXiv:2611.01767, Definition 5.23, p.42). -/
def IsBucketFind {n N : ℕ} (k : ℕ) (b : Fin n → Fin N) (π : Equiv.Perm (Fin n))
    (ρ : Finset (Fin n)) : Prop :=
  ρ.card = k ∧ ∃ y, ρ.image π = bucket b y

/-- The input `x^π ∈ Z_q^n`, `x^π_i = ι(b(π(i)))`, induced by a permutation `π`, the bucket map
`b` and the injection `ι : [N] ↪ Z_q` (arXiv:2611.01767, p.47). -/
def xPi {n N q : ℕ} (ι : Fin N ↪ ZMod q) (b : Fin n → Fin N) (π : Equiv.Perm (Fin n)) :
    Fin n → ZMod q :=
  fun i => ι (b (π i))

/-- `X^ι_{n,k} = {x ∈ Z_q^n : |{i : x_i = ι(y)}| = k for every y ∈ [N]}`, the support of the
balanced input distribution (arXiv:2611.01767, Definition 6.1, p.46).

**Formalization Note.** `[NeZero q]` makes `Z_q^n` finite; it excludes only `q = 0`. -/
noncomputable def balancedSet {n N q : ℕ} [NeZero q] (k : ℕ) (ι : Fin N ↪ ZMod q) :
    Finset (Fin n → ZMod q) := by
  classical
  exact Finset.univ.filter fun x => ∀ y, (Finset.univ.filter fun i => x i = ι y).card = k

end QCollLB


