-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_blockSuccess
-- name    : TwoFoldOPI_Supplement_blockSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:59:13.917268+00:00
-- url     : https://prove2.me/theorems/17973b6b-136b-493b-bd1b-9453636b0783
-- title:
--   Success of a code-intersection output: $x\in C\cap A_{H_1,\dots,H_m}$
-- statement:
--   For $H_1,\dots,H_m:\mathbb F_q^s\to[n]$ and a load set $\mathcal T\subseteq[n]^m$, the blockwise preimage is
--   $$A_{H_1,\dots,H_m}=\{x\in\mathbb F_q^{M}:\ (H_1(x_1),\dots,H_m(x_m))\in\mathcal T\},$$
--   where $x_i$ is the $i$-th block of $s$ consecutive coordinates. An output $x$ **succeeds** if $x\in\mathrm{RS}_{\mathbb F_q,\gamma,k}\cap A_{H_1,\dots,H_m}$.
--
--   With $s=1$ and $H_i=\pi_i$ this is the success event of Definition 12.1.
--
--   **Formalization Note** Coordinates beyond $q-2$ read as $0$; they never occur when $ms=q-1$, as in both uses.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §9.2, Definition 9.8, p. 52; Definition 11.2, p. 57; Definition 12.1, p. 65

import Mathlib
import Definitions.Def_TwoFoldOPI_Supplement_rsCode
import Definitions.Def_TwoFoldOPI_Supplement_loadSet

namespace TwoFoldOPI

namespace Supplement

/-- **Success of a code-intersection output: `x ∈ C ∩ A_{H_1,…,H_m}` for a Reed–Solomon code.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §9.2, Definition 9.8, p.52: "Let H_1, …, H_m : F_q^s → [n] be arbitrary functions and let
T ⊆ [n]^m. We define the blockwise preimage of T under H_1, …, H_m to be the set
A_{H_1,…,H_m} ⊆ F_q^M given by: A_{H_1,…,H_m} := {x ∈ F_q^M : (H_1(x_1), H_2(x_2), …, H_m(x_m)) ∈ T}";
Definition 11.2, p.57 ("An output succeeds precisely when it belongs to C_λ ∩ A_{H_1,…,H_m}");
Definition 12.1, p.65 ("Definition 9.8 is used with s = 1 and H_i = π_i").

For `x ∈ K^{q−1}` (`q = |K|`), block `i` is `x_i = (x_{is}, …, x_{is+s−1}) ∈ K^s` (0-based
coordinates). `blockSuccess B γ k part H x` says `x ∈ RS_{K,γ,k}` and
`(H_0(x_0), …, H_{m−1}(x_{m−1})) ∈ T`, where `T` is the load set with `B_a = B_{part a}`.

**Formalization Note.** Blocks are consecutive (the "fixed identification F_q^M = (F_q^s)^m").
Coordinates past `q − 2` read as `0`; they never occur when `ms = q − 1` (both uses). -/
def blockSuccess {K : Type*} [Field K] [Fintype K] {R s m n : ℕ} (B : Fin R → Set ℕ) (γ : K)
    (k : ℕ) (part : Fin n → Fin R) (H : Fin m → (Fin s → K) → Fin n)
    (x : Fin (Fintype.card K - 1) → K) : Prop :=
  x ∈ rsCode γ k ∧
    (fun i : Fin m => H i fun j : Fin s =>
      if hj : i.val * s + j.val < Fintype.card K - 1 then x ⟨i.val * s + j.val, hj⟩ else 0) ∈
      loadSet m n (fun a => B (part a))

end Supplement

end TwoFoldOPI


