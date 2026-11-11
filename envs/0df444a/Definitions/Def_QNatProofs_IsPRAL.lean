-- Prove2me | Definitions.Def_QNatProofs_IsPRAL
-- name    : QNatProofs_IsPRAL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:03:10.520197+00:00
-- url     : https://prove2.me/theorems/912118b1-3a34-4607-b328-a19971e95e69
-- title:
--   Pseudorandom amplitude-list (PRAL) families and efficient approximate preparability
-- statement:
--   A candidate family assigns to every $n,\lambda,T\in\mathbb N$ a measure $D_{n,\lambda,T}$ on normalized $n$-qubit vectors.
--
--   It is a **PRAL family** (Definition 2.3) if every $D_{n,\lambda,T}$ is a probability measure and, for every probabilistic polynomial-time classical distinguisher $A$ and every pair of polynomially bounded $\lambda,T:\mathbb N\to\mathbb N$,
--   $$
--   \Big|\Pr_{\psi\leftarrow D_{n,\lambda(n),T(n)}}\big[A(1^n,1^{\lambda(n)},\mathrm{al}_{T(n)}(\psi))=1\big]-\Pr_{\phi\sim\mathrm{Haar}_n}\big[A(1^n,1^{\lambda(n)},\mathrm{al}_{T(n)}(\phi))=1\big]\Big|\le 2^{-\lambda(n)}
--   $$
--   for all sufficiently large $n$. The running time of $A$ is measured in its total input length; efficient sampling from $D_{n,\lambda,T}$ is not required.
--
--   The family is **efficiently $\varepsilon$-approximately $\mathcal C$-preparable** (Definition 2.4) if there is a polynomial $q$ such that for every $n,\lambda,T$ and every $|\psi\rangle$ in the support of $D_{n,\lambda,T}$ some circuit $C_\psi\in\mathcal C$ of size at most $q(n,\lambda,T)$, applied to the all-zero state with the non-output register traced out, prepares $\sigma_\psi$ with $\tfrac12\||\psi\rangle\langle\psi|-\sigma_\psi\|_1\le\varepsilon(n)$.
--
--   A PRAL family preparable in $\mathcal C$ is exactly what Theorem 2.1 needs to rule out natural proofs against $\mathcal C$.
--
--   **Formalization Note** $A$ is a probabilistic algorithm with explicit fair coins (`CoinAlg`, polynomially many coins and one polynomial-time machine), on the input $1^n0\,1^\lambda0\,s$. Because $\mathrm{al}_T$ takes finitely many values, the probability over $\psi$ and the coins is the finite sum $\sum_s D\{\mathrm{al}_T=s\}\cdot\Pr_{\text{coins}}[A(1^n,1^\lambda,s)=1]$ over the strings of length $T2^{n+1}$. The support is Mathlib's `Measure.support`. The preparation polynomial is one polynomial in $n+\lambda+T$, which is equivalent to a polynomial in $(n,\lambda,T)$.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 2.3, p.9; Definition 2.4, p.10

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Algorithms
import Definitions.Def_QNatProofs_PromiseProperty

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms QAlgorithms.Complexity MeasureTheory Filter Polynomial PPADSIS.SubexpSIS

/-- `f : ℕ → ℕ` is **polynomially bounded**: `f(n) ≤ p(n)` for some polynomial `p`. -/
def PolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ p : ℕ[X], ∀ n, f n ≤ p.eval n

/-- The probability that a test `acc` (a probability for each string) accepts `al_T(ψ)` when `ψ`
is drawn from `μ`: `Σ_s μ{ψ : al_T(ψ) = s} · acc(s)`, summed over the `2^{T 2^{n+1}}` strings of the
length of an amplitude list. -/
noncomputable def alProb {n : ℕ} (μ : Measure (sphere n)) (T : ℕ) (acc : List Bool → ℝ) : ℝ :=
  ∑ s : Fin (T * 2 ^ (n + 1)) → Bool,
    (μ {ψ | al T (ψ : EuclideanSpace ℂ (Qubits n)) = List.ofFn s}).toReal * acc (List.ofFn s)

/-- The input `(1ⁿ, 1^λ, s)` of a PRAL distinguisher, written as the string `1ⁿ0 1^λ0 s`. -/
def pralCode (a : ℕ × ℕ × List Bool) : List Bool :=
  QAlgorithms.Complexity.encNat a.1 ++ QAlgorithms.Complexity.encNat a.2.1 ++ a.2.2

/-- A candidate PRAL family: for every `n, λ, T` a measure on the normalized `n`-qubit vectors. -/
abbrev PRALFamilyData : Type := (n lam T : ℕ) → Measure (sphere n)

/-- **Pseudorandom amplitude-list (PRAL) family** (Li, Parham, arXiv:2610.06826 (held copy sha256
b604fa11…), Definition 2.3, p.9): every `D_{n,λ,T}` is a probability distribution on normalized
`n`-qubit state vectors, and for every probabilistic polynomial-time classical distinguisher `A`
and every pair of polynomially bounded `λ, T : ℕ → ℕ`,
`|Pr_{ψ←D_{n,λ(n),T(n)}}[A(1ⁿ, 1^{λ(n)}, al_{T(n)}(ψ)) = 1] − Pr_{ϕ∼Haar_n}[A(1ⁿ, 1^{λ(n)}, al_{T(n)}(ϕ)) = 1]| ≤ 2^{-λ(n)}`
for all sufficiently large `n`. The running time of `A` is measured in its total input length;
efficient sampling is not required.

**Formalization Note** `A` is a probabilistic algorithm with explicit fair coins
(`PPADSIS.SubexpSIS.CoinAlg`, polynomially many coins, one polynomial-time machine), and the
probability is over `ψ` and the coins; the output `1` is the string `[true]`. -/
def IsPRAL (𝒟 : PRALFamilyData) : Prop :=
  (∀ n lam T, IsProbabilityMeasure (𝒟 n lam T)) ∧
  ∀ A : CoinAlg pralCode, A.IsPPT → ∀ lamF TF : ℕ → ℕ, PolyBounded lamF → PolyBounded TF →
    ∀ᶠ n in atTop,
      |alProb (𝒟 n (lamF n) (TF n)) (TF n) (fun s => A.prob (n, lamF n, s) (· = [true])) -
        alProb (haar n) (TF n) (fun s => A.prob (n, lamF n, s) (· = [true]))| ≤
        (2 : ℝ) ^ (-(lamF n : ℝ))

/-- **Efficiently `ε`-approximately `C`-preparable** (Li, Parham, arXiv:2610.06826 (held copy
sha256 b604fa11…), Definition 2.4, p.10): there is a polynomial `q` such that for every
`n, λ, T` and every `ψ` in the support of `D_{n,λ,T}` there is a circuit `C_ψ ∈ C` of size at most
`q(n, λ, T)` that, applied to the all-zero state with the non-output register traced out,
prepares an `n`-qubit state `σ_ψ` with `½‖|ψ⟩⟨ψ| − σ_ψ‖₁ ≤ ε(n)`.

**Formalization Note** The support is Mathlib's `Measure.support` (the points all of whose
neighbourhoods have positive measure). The polynomial is one polynomial in `n + λ + T`, which is
equivalent to a polynomial in `(n, λ, T)`. -/
def EffApproxPreparable {S : Set Gate} (𝒟 : PRALFamilyData) (C : CircuitClass S)
    (ε : ℕ → ℝ) : Prop :=
  ∃ q : ℕ[X], ∀ n lam T : ℕ, ∀ ψ ∈ (𝒟 n lam T).support,
    ∃ (w : ℕ) (c : Circuit S (n + w)), c ∈ C (n + w) ∧ c.size ≤ q.eval (n + lam + T) ∧
      ApproxPrepares c (ψ : EuclideanSpace ℂ (Qubits n)) (ε n)

end QNatProofs


