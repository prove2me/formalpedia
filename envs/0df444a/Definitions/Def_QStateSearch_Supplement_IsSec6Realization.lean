-- Prove2me | Definitions.Def_QStateSearch_Supplement_IsSec6Realization
-- name    : QStateSearch_Supplement_IsSec6Realization
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:24:43.375304+00:00
-- url     : https://prove2.me/theorems/dbf1bc0d-e23c-4aef-a3b6-081abeab9164
-- title:
--   Realizations of the Section 6 construction
-- statement:
--   A pair $(L,\psi)$ is a **realization** of the Section 6 construction if
--
--   1. for every $n\ge4$, $L_n\subseteq\{0,1\}^n$ has exactly $K=\lfloor 2^{n/2}\rfloor$ elements;
--   2. for $1\le n\le3$, $L_n$ is the set of strings with first letter $0$, and $L_0=\emptyset$;
--   3. every $\psi_x$ is a unit vector of $\mathbb C^{2^{|x|}}$.
--
--   The paper samples $L_n$ uniformly among $K$-subsets and each $\psi_x$ Haar-randomly; a realization is any outcome, and "for some realization" is an existential over $(L,\psi)$.
--
--   **Formalization Note** The small lengths are "defined arbitrarily" in the paper; this choice makes $L_n$ and its complement nonempty for every $n\ge1$.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 6.2, p.17

import Mathlib

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- `(L, ψ)` is a **realization of the Section 6 construction**:
1. for every `n ≥ 4`, `L_n ⊆ {0,1}^n` has exactly `K = ⌊2^{n/2}⌋` elements;
2. for `1 ≤ n ≤ 3`, `L_n` is the set of strings whose first letter is `0` (the small lengths,
   where the paper leaves membership arbitrary), and `L_0 = ∅`;
3. every `ψ_x` is a unit vector of `ℂ^{2^n}` (`n = |x|`).

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 6.2, p.17: "Fix n ≥ 4, let N = 2^n, and put K = ⌊2^{n/2}⌋. Choose L_n uniformly among
all K-element subsets of {0,1}^n. Independently choose an n-qubit Haar-random state |ψ_x⟩ for
every x ∈ {0,1}^n … Membership at the finitely many smaller lengths is defined arbitrarily."

**Formalization Note.** A realization is any outcome of the random choice; "for some realization"
is an existential over `(L, ψ)`. The small-length choice makes `L_n` and its complement nonempty
at every `n ≥ 1`, so the distributions of Definition 3 exist at every length. -/
def IsSec6Realization (L : (n : ℕ) → Finset (Fin n → Bool))
    (ψ : (n : ℕ) → (Fin n → Bool) → EuclideanSpace ℂ (Fin (2 ^ n))) : Prop :=
  (∀ n, 4 ≤ n → (L n).card = ⌊(2 : ℝ) ^ ((n : ℝ) / 2)⌋₊) ∧
  (∀ n, 1 ≤ n → n < 4 → L n = Finset.univ.filter fun x => ∀ i : Fin n, i.val = 0 → x i = false) ∧
  L 0 = ∅ ∧
  (∀ n x, ‖ψ n x‖ = 1)

end QStateSearch.Supplement


