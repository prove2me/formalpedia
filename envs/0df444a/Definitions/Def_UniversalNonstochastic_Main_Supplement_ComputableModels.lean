-- Prove2me | Definitions.Def_UniversalNonstochastic_Main_Supplement_ComputableModels
-- name    : UniversalNonstochastic_Main_Supplement_ComputableModels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:25:43.716728+00:00
-- url     : https://prove2.me/theorems/90b7cb2b-b283-4159-92b0-70af82464cdf
-- title:
--   Gödel numberings, numbers of computable probability measures and $N^Q_{\alpha,\beta}$
-- statement:
--   Fix a **Gödel numbering** $(\varphi_\pi)_{\pi\in\mathbb N}$ of the algorithms that take a pair $(\omega,n)\in\mathcal X\times\mathbb N$ and output a rational number: the universal function $(\pi,x)\mapsto\varphi_\pi(x)$ is partial computable, and every partial computable family $(\psi_j)_{j\in\mathbb N_0}$ of such algorithms is translated into the numbering by a computable map $t$ with $\varphi_{t(j)}=\psi_j$ (in particular, every such algorithm has a number).
--
--   A **probability measure** $P$ on $\mathcal X$ has nonnegative atoms $P(\{\omega\})$ summing to $1$; its support may be infinite. A number $\pi\in\mathbb N$ is a **number of $P$** if the algorithm $\varphi_\pi$, given any $\omega\in\mathcal X$ and $n\in\mathbb N$, halts with a rational number within $2^{-n}$ of $P(\{\omega\})$.
--
--   An object $\omega$ is **$(\alpha,\beta)$-Quasi-stochastic**, for $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty)$, if some probability measure $P$ with a number $\pi$ satisfies
--   $$K(\pi)\le\alpha\qquad\text{and}\qquad K(\omega\mid\pi)\ge-\log P(\{\omega\})-\beta,$$
--   with $-\log0:=\infty$. $N^Q_{\alpha,\beta}$ is the set of objects that are not $(\alpha,\beta)$-Quasi-stochastic.
--
--   These objects carry Theorem 9 and Lemma 21.
--
--   **Formalization Note** Algorithms output rational names $(a,b)\in\mathbb Z\times\mathbb N_0$, read as $a/(b+1)$ (the published `ratVal`). "Within $2^{-n}$" is read as $|q-P(\{\omega\})|\le2^{-n}$. The numbering is a parameter of every statement using it, quantified before the constants, so the results hold for every Gödel numbering in this sense.
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, p.9 (Gödel numbering, numbers of probability measures, (α, β)-Quasi-stochasticity, N^Q_{α,β})

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Effective
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities

namespace UniversalNonstochastic.Main.Supplement

/-- A Gödel numbering (S, p.9; an acceptable numbering in Rogers' sense) of the algorithms
that take a pair `(ω, n) ∈ 𝓧 × ℕ` and output a rational number (written as a rational name
`(a, b)`, read `a / (b + 1)`): indices are positive integers `π`, the universal function
`(π, x) ↦ φ_π(x)` is partial computable, and every partial computable family `(ψ_j)` is
translated into the numbering by a computable map `j ↦ t(j)` with `φ_{t(j)} = ψ_j`
(in particular every partial computable algorithm has a number). -/
structure GodelNumbering where
  φ : ℕ+ → (ℕ+ × ℕ+ →. ℤ × ℕ)
  universal : Partrec₂ φ
  translate : ∀ ψ : ℕ → (ℕ+ × ℕ+ →. ℤ × ℕ), Partrec₂ ψ →
    ∃ t : ℕ → ℕ+, Computable t ∧ ∀ j, φ (t j) = ψ j

/-- A probability measure on `𝓧 = ℕ`: nonnegative atoms summing to exactly `1`
(the support may be infinite). -/
def IsProbabilityOn (P : ℕ+ → ℝ) : Prop := (∀ ω, 0 ≤ P ω) ∧ HasSum P 1

/-- `π` is a number of the probability measure `P` (S, p.9): the algorithm with number `π`
halts on every input `(ω, n)`, `n ∈ ℕ = {1, 2, …}`, and outputs a rational number within
`2^{-n}` of `P({ω})`. -/
def IsNumberOf (G : GodelNumbering) (π : ℕ+) (P : ℕ+ → ℝ) : Prop :=
  ∀ (ω n : ℕ+), ∃ q ∈ G.φ π (ω, n), |P ω - ratVal q| ≤ (1 / 2 : ℝ) ^ (n : ℕ)

/-- `-log₂ x` in `EReal`, with `-log 0 := +∞` (S, p.9). -/
noncomputable def negLog2 (x : ℝ) : EReal :=
  if x = 0 then ⊤ else ((-Real.logb 2 x : ℝ) : EReal)

/-- `N^Q_{α,β}` (S, p.9): objects `ω` that are not `(α, β)`-Quasi-stochastic, i.e. there is no
probability measure `P` on `𝓧` with a number `π` such that `K(π) ≤ α` and
`K(ω | π) ≥ -log₂ P({ω}) - β`. -/
def nonQuasiStochasticGen (G : GodelNumbering) (U : OptimalPrefixDecoder) (α : ℕ) (β : ℝ) :
    Set ℕ+ :=
  {ω | ¬ ∃ (P : ℕ+ → ℝ) (π : ℕ+), IsProbabilityOn P ∧ IsNumberOf G π P ∧
      KNat U π ≤ (α : ℕ∞) ∧
      negLog2 (P ω) - ((β : ℝ) : EReal) ≤ toEReal (U.K (objCode ω) (π : ℕ))}

end UniversalNonstochastic.Main.Supplement


