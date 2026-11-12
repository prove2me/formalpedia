-- Prove2me | Definitions.Def_FourMsgQMA_LWEHyp
-- name    : FourMsgQMA_LWEHyp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:03.992612+00:00
-- url     : https://prove2.me/theorems/3c56998f-ce17-4226-8c06-ec48c7cabc0c
-- title:
--   Post-quantum decisional LWE (Assumption 3.10) and the regime $\mathrm{Hyp}(\varepsilon)$
-- statement:
--   Let $n=n(\lambda)$ and $q=q(\lambda)\ge2$, and let $\chi_\lambda=D_{\mathbb Z,\sigma(\lambda)}$ be the discrete Gaussian, $\Pr[x]\propto e^{-\pi x^2/\sigma^2}$ on $\mathbb Z$, reduced modulo $q$. **$\mathrm{LWE}_{n,q,\chi}$ holds** if the following is true for every polynomial sample bound $m(\lambda)$ and every QPT distinguisher (nonuniform, polynomial size, with quantum advice). There is a negligible $\nu$ with
--   $$
--   \Pr\big[\hat b=b:\ A\leftarrow\mathbb Z_q^{m\times n},\ s\leftarrow\mathbb Z_q^n,\ e\leftarrow\chi^m,\ u\leftarrow\mathbb Z_q^m,\ b\leftarrow\{0,1\},\ v_0:=As+e,\ v_1:=u,\ \hat b\leftarrow\mathcal A(A,v_b)\big]\le\tfrac12+\nu(\lambda).
--   $$
--   A family $(n,q,\sigma)$ is **in the regime of $\varepsilon$** when it is efficiently computable, $n$ is polynomially bounded, $n(\lambda)\ge\max(\lambda,1)$, $2\le q(\lambda)\le2^{n(\lambda)^\varepsilon}$ and $\sigma(\lambda)\ge2\sqrt{n(\lambda)}$. **$\mathrm{Hyp}(\varepsilon)$** asserts $\mathrm{LWE}_{n,q,D_{\mathbb Z,\sigma}}$ for every family in the regime of $\varepsilon$.
--
--   $\mathrm{Hyp}(\varepsilon)$ for $\varepsilon\in(0,1)$ is LWE with polynomial dimension and subexponential modulus-to-noise ratio, in Regev's Gaussian regime $\sigma\ge2\sqrt n$. It is the hypothesis of the goal and of every LWE-based milestone.
--
--   **Formalization Note** Pinned-down version (operator request) of "post-quantum LWE … at the parameters supporting the base protocol and the primitive instantiations" (Corollary 5.15). The paper keeps "the measurement protocol's superpolynomial modulus-to-noise ratio" (p.14), and GSW needs $q>8(M+1)^LB$ with "lattice dimension and $\log q$ … polynomial in $(\lambda,L)$" (p.18). Distinguishers are the published `QTest`/`IsQTestFamily`; elements of $\mathbb Z_q$ are given in $\lceil\log_2q\rceil$-bit binary.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Assumption 3.10, p.15 (PDF 17); LWE parameters, p.14 (PDF 16); Theorem 3.16 discussion, p.18 (PDF 20)

import Mathlib
import Definitions.Def_FourMsgQMA_ComputedOn

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), Assumption 3.10 (p.15, PDF 17) and the
LWE parameter discussion of pp.14, 18 (PDF 16, 20): post-quantum decisional LWE, and the parameter
regime `Hyp(ε)` of the pinned-down version (operator request).
-/

open TightPQRepetition.Main

/-- The discrete Gaussian `D_{ℤ,σ}` on `ℤ`: `Pr[x] = ρ_σ(x) / ∑_{z ∈ ℤ} ρ_σ(z)` with
`ρ_σ(x) = exp(−π x² / σ²)`. -/
noncomputable def dgWeight (σ : ℝ) (x : ℤ) : ℝ :=
  Real.exp (-Real.pi * (x : ℝ) ^ 2 / σ ^ 2) / ∑' z : ℤ, Real.exp (-Real.pi * (z : ℝ) ^ 2 / σ ^ 2)

/-- An element `a ∈ ℤ_q = {0, …, q − 1}` written in binary with `⌈log₂ q⌉` bits, least
significant first. -/
def encZq (q a : ℕ) : Bits := List.ofFn fun j : Fin (Nat.clog 2 q) => a.testBit j

/-- The input `(A, v)` handed to an LWE distinguisher: the entries of `A ∈ ℤ_q^{m×n}` row by row,
then those of `v ∈ ℤ_q^m`, each in `⌈log₂ q⌉` bits. -/
def lweInput {m n : ℕ} (q : ℕ) (A : Fin m → Fin n → Fin q) (v : Fin m → ℕ) : Bits :=
  pack ((List.ofFn fun i => List.ofFn fun j => encZq q (A i j)).flatten ++
    List.ofFn fun i => encZq q (v i))

/-- `As + e (mod q)`. -/
def lweSample {m n q : ℕ} (A : Fin m → Fin n → Fin q) (s : Fin n → Fin q) (e : Fin m → ℤ) :
    Fin m → ℕ :=
  fun i => ((∑ j, ((A i j : ℕ) : ℤ) * ((s j : ℕ) : ℤ) + e i) % (q : ℤ)).toNat

/-- The probability that the distinguisher `T` outputs `1` on `(A, As + e mod q)` with `A, s`
uniform and `e ← χ^m`, `χ = D_{ℤ,σ}`. -/
noncomputable def lweRealAccept (n q m : ℕ) (σ : ℝ) (T : QTest) : ℝ :=
  ((q : ℝ) ^ (m * n) * (q : ℝ) ^ n)⁻¹ *
    ∑ A : Fin m → Fin n → Fin q, ∑ s : Fin n → Fin q,
      ∑' e : Fin m → ℤ, (∏ i, dgWeight σ (e i)) * T.accept (lweInput q A (lweSample A s e))

/-- The probability that `T` outputs `1` on `(A, u)` with `A, u` uniform. -/
noncomputable def lweIdealAccept (n q m : ℕ) (T : QTest) : ℝ :=
  ((q : ℝ) ^ (m * n) * (q : ℝ) ^ m)⁻¹ *
    ∑ A : Fin m → Fin n → Fin q, ∑ v : Fin m → Fin q, T.accept (lweInput q A fun i => (v i : ℕ))

/-- `Pr[b̂ = b]` in the game of Assumption 3.10: `b ← {0,1}`, `v₀ := As + e (mod q)`, `v₁ := u`,
`b̂ ← T(A, v_b)`. -/
noncomputable def lweGuess (n q m : ℕ) (σ : ℝ) (T : QTest) : ℝ :=
  (1 / 2) * (1 - lweRealAccept n q m σ T) + (1 / 2) * lweIdealAccept n q m T

/-- Assumption 3.10 (p.15): `LWE_{n,q,χ}` with `χ_λ = D_{ℤ,σ(λ)}` holds against quantum
polynomial-time algorithms: for every polynomial sample bound `m(λ)` and every QPT distinguisher
(nonuniform, polynomial size, with quantum advice) there is a negligible `ν` with
`Pr[b̂ = b] ≤ 1/2 + ν(λ)`. -/
def LWEHolds (n q : ℕ → ℕ) (σ : ℕ → ℝ) : Prop :=
  ∀ m : ℕ → ℕ, PolyBound m → ∀ T : ℕ → QTest, IsQTestFamily T →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, lweGuess (n lam) (q lam) (m lam) (σ lam) (T lam) ≤ 1 / 2 + ν lam

/-- The parameter regime of `Hyp(ε)`: polynomial dimension `n(λ) ≥ max(λ, 1)`, modulus
`2 ≤ q(λ) ≤ 2^{n(λ)^ε}`, Gaussian width `σ(λ) ≥ 2√n(λ)`, all efficiently computable. -/
def InRegime (ε : ℝ) (n q : ℕ → ℕ) (σ : ℕ → ℝ) : Prop :=
  PolyBound n ∧ (∀ lam, lam ≤ n lam ∧ 1 ≤ n lam) ∧
    (∀ lam, 2 ≤ q lam ∧ (q lam : ℝ) ≤ (2 : ℝ) ^ ((n lam : ℝ) ^ ε)) ∧
    (∀ lam, 2 * Real.sqrt (n lam) ≤ σ lam) ∧
    EfficientlyComputable (fun lam => (n lam : ℝ)) ∧
    EfficientlyComputable (fun lam => (q lam : ℝ)) ∧ EfficientlyComputable σ

/-- `Hyp(ε)`: post-quantum LWE (Assumption 3.10) for every efficiently computable family
`(n, q, σ)` with polynomial dimension `n ≥ λ`, modulus-to-noise ratio at most `2^{n^ε}`
(`q ≤ 2^{n^ε}`) and discrete Gaussian error of width `σ ≥ 2√n`.

**Formalization Note** Pinned-down version (operator request) of "post-quantum LWE … at the
parameters supporting the base protocol and the primitive instantiations in Section 3"
(Corollary 5.15, p.44). The paper keeps "the measurement protocol's superpolynomial
modulus-to-noise ratio" (p.14) and GSW needs `q > 8(M+1)^L B` with "lattice dimension and `log q`
… polynomial in `(λ, L)`" (p.18), i.e. a ratio `2^{poly}`; with the dimension polynomially large
this is `q/σ ≤ 2^{n^ε}`. `σ ≥ 2√n` is Regev's regime. -/
def LWEHyp (ε : ℝ) : Prop :=
  ∀ (n q : ℕ → ℕ) (σ : ℕ → ℝ), InRegime ε n q σ → LWEHolds n q σ

end FourMsgQMA


