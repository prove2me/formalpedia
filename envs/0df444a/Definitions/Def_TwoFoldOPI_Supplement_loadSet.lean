-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_loadSet
-- name    : TwoFoldOPI_Supplement_loadSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:50:24.091008+00:00
-- url     : https://prove2.me/theorems/9759f165-42b1-4cf4-b821-ca1be9ed0943
-- title:
--   The load set $\mathcal T=\{x\in[n]^m: c_a(x)\in B_a\ \forall a\}$
-- statement:
--   For a word $x\in[n]^m$ the **load** of a symbol $a\in[n]$ is $c_a(x)=|\{i:x_i=a\}|$. Given allowed loads $B_a$ for every symbol, the **load set** is
--   $$\mathcal T=\{x\in[n]^m:\ c_a(x)\in B_a\ \text{for all } a\in[n]\}.$$
--
--   Load sets are the target sets of the histogram-constrained code-intersection problems of Part II.
--
--   **Formalization Note** $[n]=\{0,\dots,n-1\}$. Each $B_a$ may be any set of naturals; only its part in $\{0,\dots,m\}$ matters, so $B_a=B_r$ and $B_a=B_r\cap\{0,\dots,m\}$ (Definition 10.10) give the same set.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.1, Definitions 10.1–10.2, eq. (22), p. 53

import Mathlib

namespace TwoFoldOPI

namespace Supplement

open Classical in
/-- **The load set `T = {x ∈ [n]^m : c_a(x) ∈ B_a ∀ a ∈ [n]}`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.1, Definition 10.1, p.53: "For x ∈ [n]^m, we define its histogram c(x) ∈ Z^n_{≥0} by:
c_a(x) = |{i : x_i = a}|. (22)"; Definition 10.2, p.53: "For each symbol a ∈ [n], let
B_a ⊆ {0, 1, …, m} be given … Define the set: T = {x ∈ [n]^m : c_a(x) ∈ B_a ∀a ∈ [n]}."

Words are `x : Fin m → Fin n` (`[n] = {0, …, n−1}`); the load `c_a(x)` is the number of
coordinates equal to `a`.

**Formalization Note.** `Bs a` may be any set of naturals; only its part in `{0, …, m}` matters,
since every load is at most `m`. So `Bs a = B_r` and `Bs a = B_r ∩ {0, …, m}` (Definition
10.10) give the same `T`. -/
noncomputable def loadSet (m n : ℕ) (Bs : Fin n → Set ℕ) : Finset (Fin m → Fin n) :=
  Finset.univ.filter fun x => ∀ a : Fin n, (Finset.univ.filter fun i => x i = a).card ∈ Bs a

end Supplement

end TwoFoldOPI


