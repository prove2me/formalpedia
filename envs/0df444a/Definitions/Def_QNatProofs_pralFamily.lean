-- Prove2me | Definitions.Def_QNatProofs_pralFamily
-- name    : QNatProofs_pralFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:04:40.101924+00:00
-- url     : https://prove2.me/theorems/c96f7078-dc76-43da-a965-e9d015b83a79
-- title:
--   The PRAL target-state distributions $D_{n,\lambda,T}$ of Theorem 3.4 and the finite Poisson sampler family
-- statement:
--   A **sampler family** gives, for $n$ qubits, precision $T$ and requested error $\varepsilon=2^{-j}$, a tape length $R$, a precision $q$, a sampler $\mathrm{Samp}_{n,T,j}:\{0,1\}^R\to\{0,1\}^{2q}$ and a rescaling factor $s$.
--
--   The **target-state distributions** (proof of Theorem 3.4, p.17, with Fact 3.2): for $n,\lambda,T$ take the sampler at $(n,T,\lambda+1)$, so $\varepsilon=2^{-\lambda-1}$, with tape length $R$, rescaling $s$ and threshold $\gamma=1/(2s)$; the PRF security parameter $\kappa=n^2+\lambda+1$; and the derived family $F_{n,\kappa,k}(x)=G_{m,k}(0^{m-n}x)_{1,\dots,R}$, $m=(n+R+\kappa)^{\lceil1/a\rceil+1}$. Then $D_{n,\lambda,T}$ is the law of $|\psi_{F_k,\gamma}\rangle$ for a uniformly random key $k\in\mathcal K_m$.
--
--   The **finite Poisson sampler family** uses the parameters of p.25 and of the proof of Lemma 4.3 (p.21): with $N=2^n$,
--   $$
--   \xi=\frac{2^{-j}}{16CN^{3/2}2^T},\quad \eta=\frac{2^{-j}}{4N},\quad \mu=\lceil\ln(3/\eta)\rceil,\quad K_{\max}=3\mu,
--   $$
--   $q$ the least precision with $K_{\max}2^{-q}\le\eta/3$ and $(1+2\pi)\sqrt\mu\,2^{-q}\le\xi$, thresholds $T_i=\lfloor2^qP_i\rfloor$, $R=(2K_{\max}+2)q$, and $s=\sqrt\mu$.
--
--   These are "the resulting target-state distributions" of Theorem 3.4 and "the resulting PRAL family" of Corollary 4.6.2 and Theorem 4.7, defined once.
--
--   **Formalization Note** The paper's "choose $q$ sufficiently large" is the least such $q$. A machine computes a FinTM2 function within a step bound in the sense of Mathlib's `TM2OutputsInTime`.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), proof of Theorem 3.4, p.17; Fact 3.2, p.16; proof of Lemma 4.3, p.21; 'Compatibility with security parameters', p.25

import Mathlib
import Definitions.Def_QNatProofs_KeyedFam
import Definitions.Def_QNatProofs_psiState
import Definitions.Def_QNatProofs_finPoissonSampler
import Definitions.Def_QNatProofs_IsPRAL

set_option autoImplicit false

namespace QNatProofs

/-- The FinTM2 machine `M` (input and output alphabet `Bool`) started on `inp` halts with `out`
on its output stack within `t` steps. -/
def MachineComputesIn (M : Turing.TM2ComputableAux Bool Bool) (inp out : List Bool) (t : ℕ) :
    Prop :=
  Nonempty (Turing.TM2OutputsInTime M.tm (inp.map M.inputAlphabet.invFun)
    (some (out.map M.outputAlphabet.invFun)) t)

/-- A **family of complex Gaussian samplers** indexed by `(n, T, j)`, for the requested error
tolerance `ε = 2^{-j}` at `n` qubits and truncation precision `T` (Theorem 3.4, p.17): tape length
`R`, output precision `q`, the sampler, and its rescaling factor `s`. -/
structure SamplerFamily where
  /-- Tape length. -/
  R : ℕ → ℕ → ℕ → ℕ
  /-- Output precision (bits per polar coordinate). -/
  q : ℕ → ℕ → ℕ → ℕ
  /-- The sampler. -/
  samp : (n T j : ℕ) → Sampler (R n T j) (q n T j)
  /-- The rescaling factor. -/
  s : ℕ → ℕ → ℕ → ℝ

/-- **The target-state distributions of Theorem 3.4** (Li, Parham, arXiv:2610.06826 (held copy
sha256 b604fa11…), proof of Theorem 3.4, p.17, with Fact 3.2, p.16): for `n, λ, T`, take the
sampler of the family at `(n, T, λ + 1)` (requested error `ε = 2^{-λ-1}`), with tape length `R`,
rescaling `s` and threshold `γ = 1/(2s)` (Corollary 3.2.1); the PRF security parameter
`κ = n² + λ + 1`; and the derived family `F_{n,κ,k}(x) = G_{m,k}(0^{m−n}x)_{1,…,R}`,
`m = (n + R + κ)^{⌈1/a⌉+1}` (Fact 3.2). `D_{n,λ,T}` is the law of `|ψ_{F_k,γ}⟩` ((6), (7)) for a
uniformly random key `k ∈ 𝒦_m`. -/
noncomputable def pralFamily (G : KeyedFam) (a : ℝ) (SF : SamplerFamily) : PRALFamilyData :=
  fun n lam T =>
    DF (1 / (2 * SF.s n T (lam + 1))) (SF.samp n T (lam + 1))
      (fun k : G.K (prfLen a n (SF.R n T (lam + 1)) (n ^ 2 + lam + 1)) =>
        prfTape G (prfLen a n (SF.R n T (lam + 1)) (n ^ 2 + lam + 1)) n (SF.R n T (lam + 1)) k)

/-- Lemma 4.3's sampler parameters for approximation error `ξ` and failure probability `η`
(proof of Lemma 4.3, p.21): `µ = ⌈ln(3/η)⌉`. -/
noncomputable def poissonMu (η : ℝ) : ℕ := ⌈Real.log (3 / η)⌉₊

open Classical in
/-- Lemma 4.3's precision (p.21): the least `q` with `K_max 2^{-q} ≤ η/3` and
`(1 + 2π)√µ 2^{-q} ≤ ξ`, where `µ = ⌈ln(3/η)⌉` and `K_max = 3µ` (`0` if there is none, which happens
only for `ξ ≤ 0` or `η ≤ 0`). -/
noncomputable def poissonQ (ξ η : ℝ) : ℕ :=
  if h : ∃ q : ℕ, (3 * poissonMu η : ℝ) * (2 : ℝ)⁻¹ ^ q ≤ η / 3 ∧
      (1 + 2 * Real.pi) * Real.sqrt (poissonMu η) * (2 : ℝ)⁻¹ ^ q ≤ ξ then Nat.find h
  else 0

/-- The sampler parameters of the "Compatibility with security parameters" paragraph (p.25) for
`n` qubits, precision `T`, requested error `ε = 2^{-j}`, and the constant `C` of Theorem 3.1:
`ξ = ε/(16 C N^{3/2} 2^T)` and `η = ε/(4N)` with `N = 2ⁿ`. -/
noncomputable def poissonXi (C : ℝ) (n T j : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ j / (16 * C * ((2 : ℝ) ^ n) ^ ((3 : ℝ) / 2) * (2 : ℝ) ^ T)

/-- `η = ε/(4N)` with `ε = 2^{-j}`, `N = 2ⁿ` (p.25). -/
noncomputable def poissonEta (n j : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ j / (4 * (2 : ℝ) ^ n)

/-- **The finite Poisson sampler family of Lemma 4.1 with the parameters of p.25** (Li, Parham,
arXiv:2610.06826 (held copy sha256 b604fa11…), proof of Lemma 4.1 and "Compatibility with security
parameters", p.25; proof of Lemma 4.3, p.21): at `(n, T, j)`, `ξ = 2^{-j}/(16 C N^{3/2} 2^T)`,
`η = 2^{-j}/(4N)`, `µ = ⌈ln(3/η)⌉`, `K_max = 3µ`, `q` the least precision with `K_max 2^{-q} ≤ η/3`
and `(1 + 2π)√µ 2^{-q} ≤ ξ`, the thresholds `T_i = ⌊2^q P_i⌋`, tape length `R = (2K_max + 2)q`, and
rescaling `s = √µ`. -/
noncomputable def poissonSF (C : ℝ) : SamplerFamily where
  R n T j := (2 * (3 * poissonMu (poissonEta n j)) + 2) *
    poissonQ (poissonXi C n T j) (poissonEta n j)
  q n T j := poissonQ (poissonXi C n T j) (poissonEta n j)
  samp n T j := finPoissonSampler (3 * poissonMu (poissonEta n j))
    (poissonQ (poissonXi C n T j) (poissonEta n j))
    (stdThresholds (poissonMu (poissonEta n j)) (poissonQ (poissonXi C n T j) (poissonEta n j)))
  s n _ j := Real.sqrt (poissonMu (poissonEta n j))

end QNatProofs


