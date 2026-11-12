-- Prove2me | Definitions.Def_SmallSecretLWE_Classical_Basic
-- name    : SmallSecretLWE_Classical_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:26:28.376032+00:00
-- url     : https://prove2.me/theorems/1a960803-ec35-4d7f-ba5c-b61770d32352
-- title:
--   Centered values and $\ell_p$ 'norms' on $\mathbb Z_q^n$, sparse rows, and the random and planted k-LIN$(\mathbb Z_q)$ laws
-- statement:
--   For a positive integer $q$, every $x\in\mathbb Z_q$ has a unique **centered lift** $\tilde x\in\{-\lceil q/2\rceil+1,\dots,\lfloor q/2\rfloor\}$ with $\tilde x\equiv x \pmod q$, and $|x| := |\tilde x|$. For $x\in\mathbb Z_q^n$ and $1\le p<\infty$,
--   $$\|x\|_p=\Big(\sum_{j=1}^n |x_j|^p\Big)^{1/p},\qquad \|x\|_\infty=\max_j |x_j| ,\qquad \|x\|_0=\#\{j: x_j\neq 0\}.$$
--   These are not norms (no homogeneity) but are positive definite. $(\mathbb Z_q^n)_t$ is the set of vectors with exactly $t$ nonzero entries; a matrix $A\in\mathbb Z_q^{m\times n}$ has **k-sparse rows** when every row lies in $(\mathbb Z_q^n)_k$. A **k-LIN$(\mathbb Z_q)$ instance** is $(A,b)$ with such $A$ (arbitrary, "semirandom") and $b\in\mathbb Z_q^m$.
--
--   In a **random instance** $b$ is uniform on $\mathbb Z_q^m$ (each value has probability $q^{-m}$). In a **planted instance** with secret $s\in\mathbb Z_q^n$ and noise law $\Psi$ on $\mathbb Z_q$, $b=As+e$ with $e_1,\dots,e_m$ i.i.d. $\Psi$; $\Psi^t$ is the product law on $\mathbb Z_q^t$, with $\Pr_{\Psi^t}[e]=\prod_i\Psi(e_i)$, and $\mathrm{tailProb}(\Psi,t,D)=\Pr_{\tilde e\sim\Psi^t}[\|\tilde e\|_\infty>D]$.
--
--   **Formalization Note.** `ZMod q`, with `ZMod.valMinAbs` as the centered lift (range $(-q/2,q/2]$); `cabs`, `l1`, `linf`, `l0` are real/natural valued, `lpNorm p` takes $p\in[1,\infty]$ as an `ENNReal` ($\|x\|_\infty=0$ for $n=0$). Laws on $\mathbb Z_q$ are `PMF (ZMod q)`; probabilities are written as finite real sums.
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 6 fn. 3; p. 10, §3.1 and Definition 3.1; p. 12, Definitions 3.4–3.6

import Mathlib

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace SmallSecretLWE.Classical

/-!
# Centered values and "norms" on `Z_q^n`, sparse vectors, k-LIN(Z_q) instances and their laws

Agrawal, Bagchi, Kumar, *Algorithms for Sparse LWE and LPN with Small Secrets*, STOC 2027
submission (manuscript sha256 8d93a268…): §3.1 and Definition 3.1, p. 10; footnote 3, p. 6;
Definitions 3.4–3.6, p. 12.

* `ZMod q` is `Z_q`. The centered lift of `x` is `ZMod.valMinAbs x`, the representative in
  `{−⌈q/2⌉+1, …, ⌊q/2⌋}` (Definition 3.1); `cabs x = |x̃|` is its absolute value, a real number.
* `lpNorm p x = ‖x̃‖_p` for `p ∈ [1, ∞]` (an extended real; `p = ∞` is the maximum, `0` for the
  empty vector). `l1`, `linf` are the cases `p = 1`, `p = ∞`; `l0 x` counts the nonzero entries.
* `(Z_q^n)_t` is `{x | l0 x = t}`; a matrix `A : Matrix (Fin m) (Fin n) (ZMod q)` has k-sparse
  rows (`HasKSparseRows k A`) when every row has exactly `k` nonzero entries.
* A law on `Z_q` is a `PMF (ZMod q)`. `prodProb Ψ e = ∏_i Ψ(e_i)` is the probability of
  `e ∈ Z_q^t` under the product law `Ψ^t`; `tailProb Ψ t D = Pr_{ẽ ∼ Ψ^t}[‖ẽ‖_∞ > D]`.
* Random instance (Definition 3.5): `b` uniform on `Z_q^m`, each value of probability `q^{−m}`.
  Planted instance (Definition 3.6) with secret `s` and noise `Ψ`: `b = A s + e`, `e ∼ Ψ^m`.
-/

/-- The centered absolute value `|x| = |x̃|`, `x̃ ∈ {−⌈q/2⌉+1, …, ⌊q/2⌋}` the centered lift. -/
def cabs {q : ℕ} (x : ZMod q) : ℝ := |((x.valMinAbs : ℤ) : ℝ)|

/-- `‖x‖_∞ = max_j |x_j|` (centered), `0` for the empty vector. -/
def linf {n q : ℕ} (x : Fin n → ZMod q) : ℝ :=
  ((Finset.univ.sup fun j => Real.toNNReal (cabs (x j)) : NNReal) : ℝ)

/-- `‖x‖_1 = Σ_j |x_j|` (centered). -/
def l1 {n q : ℕ} (x : Fin n → ZMod q) : ℝ := ∑ j, cabs (x j)

/-- `‖x‖_p` for `p ∈ [1, ∞]`: `(Σ_j |x_j|^p)^{1/p}` for finite `p`, `‖x‖_∞` for `p = ∞`
(Definition 3.1: the ℓp norm of the centered lift). -/
def lpNorm {n q : ℕ} (p : ENNReal) (x : Fin n → ZMod q) : ℝ :=
  if p = ⊤ then linf x else (∑ j, cabs (x j) ^ p.toReal) ^ (1 / p.toReal)

/-- `‖x‖_0`, the number of nonzero entries (Hamming weight). -/
def l0 {n q : ℕ} (x : Fin n → ZMod q) : ℕ := (Finset.univ.filter fun j => x j ≠ 0).card

/-- Every row of `A` has exactly `k` nonzero entries (rows in `(Z_q^n)_k`). -/
def HasKSparseRows {m n q : ℕ} (k : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod q)) : Prop :=
  ∀ i, l0 (A i) = k

/-- `Pr_{e ∼ Ψ^t}[e]`: the probability of `e ∈ Z_q^t` under the product law `Ψ^t`. -/
def prodProb {q t : ℕ} (Ψ : PMF (ZMod q)) (e : Fin t → ZMod q) : ℝ := ∏ i, (Ψ (e i)).toReal

/-- `Pr_{ẽ ∼ Ψ^t}[‖ẽ‖_∞ > D]`. -/
def tailProb {q : ℕ} [NeZero q] (Ψ : PMF (ZMod q)) (t : ℕ) (D : ℝ) : ℝ :=
  ∑ e : Fin t → ZMod q, if D < linf e then prodProb Ψ e else 0

/-- The probability of each right-hand side `b ∈ Z_q^m` in a random instance: `q^{−m}`. -/
def unifProb (q m : ℕ) : ℝ := 1 / (q : ℝ) ^ m

/-- The planted right-hand side `b = A s + e`. -/
def plantedRHS {m n q : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q)) (s : Fin n → ZMod q)
    (e : Fin m → ZMod q) : Fin m → ZMod q :=
  A.mulVec s + e

end SmallSecretLWE.Classical


