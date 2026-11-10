-- Prove2me | Definitions.Def_SeededShannon_setFamily
-- name    : SeededShannon_setFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:44:48.68073+00:00
-- url     : https://prove2.me/theorems/12ecf622-56ae-455b-ac33-be1df0e6aa90
-- title:
--   Sparse set agreement predicate $f_S(x)=1\iff\delta(x)\le p\wedge x_S=1$ and its family
-- statement:
--   For $x\in\{0,1\}^n$ write $\mathrm{wt}(x)$ for its Hamming weight. For a set $S\subseteq[n]$ the **sparse set agreement predicate** is
--   $$f_S(x)=1\iff \delta(x)\le p\ \wedge\ x_S=1,$$
--   i.e. $x$ has relative weight at most $p$ and is $1$ on every position of $S$. The **sparse set agreement family** $\mathcal F_{\lambda,n}$ consists of the $f_S$ with $|S|\le B(\lambda,n)$. The module also defines efficient computability of a two-argument integer function: one polynomial-time machine computes $B(\lambda,n)$ in binary from $(1^\lambda,1^n)$.
--
--   This is the family of the sparse-set evasive obfuscator, which tests in Construction 6.1 whether every header chunk of the hidden set is heavily corrupted.
--
--   **Formalization Note** Sets are indicator vectors $S:[n]\to\{0,1\}$; $\delta(x)\le p$ is $\mathrm{wt}(x)\le p\cdot n$.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorems 5.2 and 5.5, pp.31–32 (PDF pp.34–35)

import Mathlib
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_KarpLiptonOM_binW

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier

/-- The Hamming weight `wt(x) = Δ(x, 0^n)` of `x ∈ {0,1}^n` (Dujmovic, Lu, Silbak, Wichs, STOC 2027
submission (manuscript sha256 52f4b606…a769709), §3, p.16). -/
def wt {n : ℕ} (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

/-- The **sparse set agreement predicate** (Theorems 5.2 and 5.5, pp.31–32): for a set
`S ⊆ [n]` given by its indicator vector, `f_S(x) = 1 ⟺ δ(x) ≤ p ∧ x_S = 1`.

**Formalization Note** `δ(x) ≤ p` is written `wt(x) ≤ p · n`. -/
def setAgree (p : ℝ) {n : ℕ} (S x : Fin n → Bool) : Prop :=
  (wt x : ℝ) ≤ p * n ∧ ∀ i, S i = true → x i = true

/-- The **sparse set agreement family** `F_{λ,n}` (Theorems 5.2 and 5.5, pp.31–32): the functions
`f_S` for sets `S ⊆ [n]` of size at most `B(λ, n)`. -/
def setFamily (p : ℝ) (B : ℕ → ℕ → ℕ) (lam n : ℕ) : Set ((Fin n → Bool) → Bool) :=
  {f | ∃ S : Fin n → Bool, wt S ≤ B lam n ∧ ∀ x, f x = true ↔ setAgree p S x}

/-- A two-argument integer-valued function is **efficiently computable** (Theorems 5.2, 5.5,
pp.31–32): one polynomial-time machine computes the binary representation of `B(λ, n)` from
`(1^λ, 1^n)`. -/
def EffComputable₂ (B : ℕ → ℕ → ℕ) : Prop :=
  PolyTimeOn (ι := ℕ × ℕ) (fun z => [unary z.1, unary z.2])
    (fun z => KarpLiptonOM.binW (Nat.size (B z.1 z.2)) (B z.1 z.2))

end SeededShannon


