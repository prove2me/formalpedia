-- Prove2me | Definitions.Def_RandModSubsetSum_CRT
-- name    : RandModSubsetSum_CRT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:20.31834+00:00
-- url     : https://prove2.me/theorems/ba02b6d4-094c-4cac-acd2-e70e0b35504f
-- title:
--   Residue law of uniform coefficients modulo the auxiliary primes
-- statement:
--   For $n$ independent uniform coefficients $a_k\in\{0,\dots,Q-1\}$ and moduli $p_0,\dots,p_7$, the module defines the joint law of the residue array $(a_k\bmod p_i)_{i,k}$, the uniform law on $\prod_i\mathbb F_{p_i}^n$ (the auxiliary residue model), and the total variation distance between them,
--   $$\mathrm{TV}=\tfrac12\sum_y\big|\Pr[(a_k\bmod p_i)_{i,k}=y]-\textstyle\prod_ip_i^{-n}\big|.$$
--   This is the distance bounded in (48).
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), proof of Theorem 3.2, (48), p. 52

import Mathlib

open scoped BigOperators

namespace RandModSubsetSum

open Classical in
/-- The joint law of the residues `(a_k mod p_i)_{i,k}` of `n` independent uniform coefficients
`a_k ∈ {0, …, Q − 1}`, for moduli `p_0, …, p_7` (the eight auxiliary primes, §6.4, p. 51): the
probability of the residue array `y`.
Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), proof of Theorem 3.2, (48), p. 52. -/
noncomputable def residueLaw (n Q : ℕ) (p : Fin 8 → ℕ) (y : (i : Fin 8) → Fin n → Fin (p i)) : ℝ :=
  ((Finset.univ.filter (fun a : Fin n → Fin Q => ∀ i k, (a k).val % p i = (y i k).val)).card : ℝ) /
    (Q : ℝ) ^ n

/-- The auxiliary model's residue law: independent uniform residues in `Π_i F_{p_i}ⁿ`. -/
noncomputable def uniformResidueLaw (n : ℕ) (p : Fin 8 → ℕ) : ℝ :=
  1 / ∏ i, ((p i : ℝ) ^ n)

/-- Total variation distance between the actual joint residue law and the auxiliary model (48). -/
noncomputable def residueTV (n Q : ℕ) (p : Fin 8 → ℕ) : ℝ :=
  (1 / 2) * ∑ y : (i : Fin 8) → Fin n → Fin (p i), |residueLaw n Q p y - uniformResidueLaw n p|

end RandModSubsetSum


