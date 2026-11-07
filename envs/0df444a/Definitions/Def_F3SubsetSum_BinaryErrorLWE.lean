-- Prove2me | Definitions.Def_F3SubsetSum_BinaryErrorLWE
-- name    : F3SubsetSum_BinaryErrorLWE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:47.578819+00:00
-- url     : https://prove2.me/theorems/a8cd82b0-297b-4f52-b4d3-2739c8cf71e1
-- title:
--   Binary-Error LWE over $\mathbb F_q$: samples, decoders, pointwise and average-case error
-- statement:
--   Fix a prime $q\ge 3$. An instance of **Binary-Error LWE** (Problem 1.5) is a pair $(A,b)$ with $A\in\mathbb F_q^{n\times m}$ and
--
--   $$
--   b=A^{\top}s+e,\qquad s\in\mathbb F_q^n,\quad e\in\{0,1\}^m ,
--   $$
--
--   so $b_i=\langle a_i,s\rangle+e_i$ for the columns $a_1,\dots,a_m$ of $A$. A **deterministic decoder** is a function $\mathrm{Dec}(A,b)\in\mathbb F_q^n$, one for each pair of dimensions $(n,m)$. For fixed $s$ and $e$, its **pointwise failure probability** is
--
--   $$
--   \Pr_{A\sim\mathbb F_q^{n\times m}}\bigl[\mathrm{Dec}(A,A^{\top}s+e)\neq s\bigr],
--   $$
--
--   and, for $q=3$, its **average-case error** (Theorem 3.1) is
--
--   $$
--   \eta=\Pr_{A\sim\mathbb F_3^{n\times m},\,s\sim\mathbb F_3^n,\,e\sim\{0,1\}^m}\bigl[\mathrm{Dec}(A,A^{\top}s+e)\neq s\bigr],
--   $$
--
--   with $A$, $s$, $e$ independent and uniform. Problem 1.5 asks for a bound on the pointwise failure probability that holds for every $s$ and $e$; averaging it gives a bound on $\eta$.
--
--   **Formalization Note** $e\in\{0,1\}^m$ is given by a pattern `Fin m → Bool`, mapped to $\{0,1\}\subseteq\mathbb F_q$. Probabilities are finite counts over $q^{nm}$ matrices (and $3^n2^m$ pairs $(s,e)$ for $\eta$).
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Problem 1.5, p.5; Theorem 3.1, p.13

import Mathlib

namespace F3SubsetSum

open Matrix

/-- **The binary error vector** `e ∈ {0,1}^m ⊆ F_q^m` (Problem 1.5). Kothari, Metger, O'Donnell,
Shutty, Wu, arXiv:2609.40321v1, Problem 1.5, p.5: "b = A⊤s + e, for arbitrary unknown vectors
s ∈ F_q^n and e ∈ {0, 1}^m".

**Formalization Note** A vector of `{0,1}^m` is given by its pattern `e : Fin m → Bool`
(`true ↦ 1`, `false ↦ 0`), so that "e ∈ {0,1}^m" needs no side condition. -/
def binVec (q : ℕ) {m : ℕ} (e : Fin m → Bool) : Fin m → ZMod q :=
  fun i => if e i then 1 else 0

/-- **A Binary-Error LWE sample** `b = A⊤s + e` (Problem 1.5, p.5), for `A ∈ F_q^{n×m}`,
`s ∈ F_q^n` and `e ∈ {0,1}^m`. Column `i` of `A` is `a_i`, and `b_i = ⟨a_i, s⟩ + e_i`. -/
def lweSample {q n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (s : Fin n → ZMod q)
    (e : Fin m → Bool) : Fin m → ZMod q :=
  Aᵀ *ᵥ s + binVec q e

/-- **A deterministic decoder** for Binary-Error LWE (Problem 1.5, p.5): for every pair of
dimensions `(n, m)`, a function `Dec(A, b) ∈ F_q^n` of the input `(A, b) ∈ F_q^{n×m} × F_q^m`.
The decoder receives only `(A, b)` (and `n`, `m`, which are visible in the input). -/
abbrev DecoderFn (q : ℕ) : Type :=
  (n m : ℕ) → Matrix (Fin n) (Fin m) (ZMod q) → (Fin m → ZMod q) → (Fin n → ZMod q)

open Classical in
/-- **Pointwise failure probability** (Problem 1.5, p.5): for fixed `s ∈ F_q^n` and
`e ∈ {0,1}^m`, `Pr_{A∼F_q^{n×m}}[Dec(A, A⊤s + e) ≠ s]`, the fraction of the `q^{nm}` matrices `A`
on which the decoder misses `s`. "Dec has pointwise failure probability at most δ" is
`∀ s e, pointwiseFailure Dec n m s e ≤ δ`. -/
noncomputable def pointwiseFailure {q : ℕ} [NeZero q] (Dec : DecoderFn q) (n m : ℕ)
    (s : Fin n → ZMod q) (e : Fin m → Bool) : ℝ :=
  ((Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod q) =>
      Dec n m A (lweSample A s e) ≠ s).card : ℝ) / (q : ℝ) ^ (n * m)

open Classical in
/-- **Average-case error over `F₃`** (Theorem 3.1, p.13):
`Pr_{A∼F₃^{n×m}, s∼F₃^n, e∼{0,1}^m}[Dec(A, A⊤s + e) ≠ s]`, with `A`, `s`, `e` independent and
uniform: the number of failing triples divided by `3^{nm} · 3^n · 2^m`. -/
noncomputable def avgError (Dec : DecoderFn 3) (n m : ℕ) : ℝ :=
  ((Finset.univ.filter fun x : Matrix (Fin n) (Fin m) (ZMod 3) × (Fin n → ZMod 3) ×
      (Fin m → Bool) => Dec n m x.1 (lweSample x.1 x.2.1 x.2.2) ≠ x.2.1).card : ℝ) /
    ((3 : ℝ) ^ (n * m) * (3 : ℝ) ^ n * (2 : ℝ) ^ m)

end F3SubsetSum


