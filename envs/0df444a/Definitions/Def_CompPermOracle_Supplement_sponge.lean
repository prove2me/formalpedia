-- Prove2me | Definitions.Def_CompPermOracle_Supplement_sponge
-- name    : CompPermOracle_Supplement_sponge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:48:22.235187+00:00
-- url     : https://prove2.me/theorems/e0adb13c-2ad4-474e-ac2e-bbe352ffe937
-- title:
--   The sponge with digest length $d$ and the Davies–Meyer compression function
-- statement:
--   **Sponge.** Fix a rate $r\ge1$, a capacity $c\ge1$ and a permutation $\varphi$ of the $2^{r+c}$ states $\{0,1\}^{r+c}$, each state consisting of $r$ rate bits followed by $c$ capacity bits. For a nonempty sequence of blocks $m=m_1\|\cdots\|m_\ell$ with $m_i\in\{0,1\}^r$, start from $s_0=0^{r+c}$ and set
--   $$
--   s_i=\varphi\big(s_{i-1}\oplus(m_i\|0^c)\big),\qquad 1\le i\le\ell.
--   $$
--   For a digest length $1\le d\le r$, the sponge returns the first $d$ bits of $s_\ell$.
--
--   **Davies–Meyer.** For a family $\Phi=(\varphi_k)_{k\in\mathcal K}$ of permutations of $\{0,1\}^n$,
--   $$
--   \mathrm{DM}^\Phi(k,x)=\varphi_k(x)\oplus x .
--   $$
--
--   These are the two hash constructions whose preimage and collision resistance is bounded in Theorems 5.5 and 5.6.
--
--   **Formalization Note** The oracle permutations act on `Fin N`, and the bit strings $\{0,1\}^{r+c}$ (as pairs of rate and capacity bits) or $\{0,1\}^n$ are identified with `Fin N` through an equivalence `e`, which the theorems quantify over; the permutation acts on bit strings as $e^{-1}\circ\varphi\circ e$. The sponge absorbs a list of blocks by a left fold; the empty list is excluded in the theorems by the padding hypothesis.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), §3.5, p.10 (sponge, Davies–Meyer); §5.3, p.30 (digest length d); §5.5, p.33

import Mathlib

namespace CompPermOracle.Supplement

/-- Bitwise XOR of two bit strings of length `n`. -/
def bxor {n : ℕ} (u v : Fin n → Bool) : Fin n → Bool := fun i => xor (u i) (v i)

/-- The sponge state after absorbing the blocks `m₁, …, m_ℓ` (Carolan, Majenz, arXiv:2609.28469
(version of 2026-11-03, sha256 52ebc507…), §3.5, p.10): `s₀ = 0^{r+c}` and
`s_i = φ(s_{i−1} ⊕ (m_i ∥ 0^c))`.

**Formalization Note.** A state is a pair (rate bits, capacity bits); `m_i ∥ 0^c` XORs `m_i` into
the rate bits and leaves the capacity bits. The permutation `φ` acts on `Fin N`, and states are
identified with `Fin N` through the equivalence `e`, so `φ` acts on states as `e⁻¹ ∘ φ ∘ e`. -/
def spongeState {r c N : ℕ} (e : (Fin r → Bool) × (Fin c → Bool) ≃ Fin N)
    (φ : Equiv.Perm (Fin N)) (m : List (Fin r → Bool)) : (Fin r → Bool) × (Fin c → Bool) :=
  m.foldl (fun s b => e.symm (φ (e (bxor s.1 b, s.2)))) (fun _ => false, fun _ => false)

/-- The sponge digest of length `d ≤ r`: the first `d` bits of the final state, i.e. its first `d`
rate bits (arXiv:2609.28469, §5.3, p.30: "following absorption, the sponge returns the first `d`
bits of its final state"). -/
def spongeDigest {r c d N : ℕ} (hd : d ≤ r) (e : (Fin r → Bool) × (Fin c → Bool) ≃ Fin N)
    (φ : Equiv.Perm (Fin N)) (m : List (Fin r → Bool)) : Fin d → Bool :=
  fun i => (spongeState e φ m).1 (Fin.castLE hd i)

/-- The Davies–Meyer compression function `DM^Φ(k, x) = φ_k(x) ⊕ x` (arXiv:2609.28469, §3.5, p.10
and §5.5, p.33).

**Formalization Note.** `Φ` is a family of permutations of `Fin N`, and `{0,1}^n` is identified
with `Fin N` through the equivalence `e`; the XOR is taken on bit strings. -/
def dm {n N : ℕ} {K : Type} (e : (Fin n → Bool) ≃ Fin N) (Φ : K → Equiv.Perm (Fin N)) (k : K)
    (x : Fin N) : Fin n → Bool :=
  bxor (e.symm (Φ k x)) (e.symm x)

end CompPermOracle.Supplement


