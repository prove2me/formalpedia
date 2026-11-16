-- Prove2me | Definitions.Def_ElimAgree_Supplement_REIP
-- name    : ElimAgree_Supplement_REIP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:35:37.255198+00:00
-- url     : https://prove2.me/theorems/7e031360-c076-4dbf-8508-c655b4af29e8
-- title:
--   Restricted inner product $\mathrm{REIP}_{n,k}$, $M^*(n,k)$, $\varepsilon_k$ and the hashing bound $(H_\Phi)$
-- statement:
--   In $\mathrm{REIP}_{n,k}$ Bob holds $y\in\mathbb F_2^n$, Alice holds $X\in\mathbb F_2^{k\times n}$, and they must output $\sigma\neq Xy$.
--
--   $M^*(n,k)$ is the least number of distinct messages of a deterministic one-way protocol in which Bob sends $m(y)$ and Alice outputs $o(X,m(y))\neq Xy$ for all $X,y$; $D^{B\to A,A}(\mathrm{REIP}_{n,k})=\lceil\log M^*(n,k)\rceil$. For $k\ge8$,
--
--   $$\eta_k=\frac{\ln(2k\ln k+5k)+1}{k\ln2},\qquad 1+\varepsilon_k=\frac{1+1/k}{1-\eta_k}.$$
--
--   With $Q=2^k$ and $X$ uniform in $\mathbb F_2^{k\times n}$, $X$ is **$\tau$-bad** for $B\subseteq\mathbb F_2^n\setminus\{0\}$ if $\Pr_{y\in B}[Xy=\sigma]<(1-\tau)Q^{-1}$ for some $\sigma\in\mathbb F_2^k$. The **hashing bound** $(H_\Phi)$ holds if for every nonempty $B\subseteq\mathbb F_2^n\setminus\{0\}$ and every $0<\tau<1$,
--
--   $$\Pr_X[X\text{ is }\tau\text{-bad for }B]\le\frac{\Phi}{\tau^2|B|}.\tag{B.2}$$
--
--   **Formalization Note** $\mathbb F_2$ is `ZMod 2`; probabilities are counting fractions; $\lceil\log M^*\rceil$ is `Nat.clog 2`. The set defining $M^*$ is nonempty for $k\ge1$.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Appendix B: REIP, M*, η_k, ε_k, p.30 (PDF p.32); τ-bad and (H_Φ), p.32 (PDF p.34)

import Mathlib

namespace ElimAgree

namespace Supplement

/-!
# Restricted inner product `REIP_{n,k}`, `M*(n, k)`, `ε_k`, and the hashing bound `(H_Φ)`

Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*,
manuscript (STOC 2027 submission), Appendix B, pp.30 and 32.

**Formalization Note.** `F_2` is `ZMod 2`. Alice holds `X ∈ F_2^{k×n}`, Bob holds `y ∈ F_2^n`, and
the answer is `Xy` (`Matrix.mulVec`); an output `σ` is correct iff `σ ≠ Xy`. Probabilities over a
uniform `X` are counting fractions over all `2^{kn}` matrices; `Pr_{y∈B}` is uniform on `B`.
`M*(n, k)` is a least number of messages; the set it minimizes over is nonempty for `k ≥ 1`.
`D^{B→A,A}(REIP_{n,k}) = ⌈log M*(n, k)⌉` is the paper's identity on p.30, taken as the definition.
-/

/-- Alice's inputs of `REIP_{n,k}`: matrices `X ∈ F_2^{k×n}`. -/
abbrev Mat (k n : ℕ) : Type := Matrix (Fin k) (Fin n) (ZMod 2)

/-- Bob's inputs of `REIP_{n,k}`: vectors `y ∈ F_2^n`. -/
abbrev Vec (n : ℕ) : Type := Fin n → ZMod 2

/-- The answer `Xy` of `REIP_{n,k}` (p.30); the parties must output `σ ≠ Xy`. -/
def reipAns {k n : ℕ} (X : Mat k n) (y : Vec n) : Fin k → ZMod 2 := X.mulVec y

/-- `M*(n, k)` (§B.1, p.30): the least number of distinct messages of a deterministic one-way
protocol for `REIP_{n,k}` in which Bob sends `m(y)` and Alice outputs `o(X, m(y)) ≠ Xy`. -/
noncomputable def Mstar (n k : ℕ) : ℕ :=
  sInf {M : ℕ | ∃ (m : Vec n → Fin M) (o : Mat k n → Fin M → (Fin k → ZMod 2)),
    ∀ X y, o X (m y) ≠ reipAns X y}

/-- `D^{B→A,A}(REIP_{n,k}) = ⌈log₂ M*(n, k)⌉` (p.30). -/
noncomputable def DBA (n k : ℕ) : ℕ := Nat.clog 2 (Mstar n k)

/-- `η_k = (ln(2k ln k + 5k) + 1)/(k ln 2)` (p.30, for `k ≥ 8`). -/
noncomputable def etaK (k : ℕ) : ℝ :=
  (Real.log (2 * k * Real.log k + 5 * k) + 1) / (k * Real.log 2)

/-- `ε_k`, defined by `1 + ε_k = (1 + 1/k)/(1 − η_k)` (p.30, for `k ≥ 8`). -/
noncomputable def epsK (k : ℕ) : ℝ := (1 + 1 / (k : ℝ)) / (1 - etaK k) - 1

/-- `Pr_{y∈B}[Xy = σ]`, `y` uniform on `B`. -/
noncomputable def probInB {k n : ℕ} (B : Finset (Vec n)) (X : Mat k n) (σ : Fin k → ZMod 2) :
    ℝ :=
  ((B.filter (fun y => reipAns X y = σ)).card : ℝ) / (B.card : ℝ)

/-- `Pr_X[P(X)]` for `X` uniform in `F_2^{k×n}`. -/
noncomputable def probX {k n : ℕ} (P : Mat k n → Prop) : ℝ :=
  (({X | P X} : Set (Mat k n)).ncard : ℝ) / (Fintype.card (Mat k n) : ℝ)

/-- `X` is `τ`-bad for `B` (§B.2, p.32): `Pr_{y∈B}[Xy = σ] < (1 − τ)Q^{−1}` for some `σ ∈ F_2^k`,
with `Q = 2^k`. -/
def IsTauBad {k n : ℕ} (τ : ℝ) (B : Finset (Vec n)) (X : Mat k n) : Prop :=
  ∃ σ : Fin k → ZMod 2, probInB B X σ < (1 - τ) / 2 ^ k

/-- The hashing bound `(H_Φ)` (B.2), p.32: for every nonempty `B ⊆ F_2^n ∖ {0}` and every
`0 < τ < 1`, `Pr_X[X is τ-bad for B] ≤ Φ/(τ²|B|)`. -/
def HPhi (n k : ℕ) (Φ : ℝ) : Prop :=
  ∀ B : Finset (Vec n), B.Nonempty → (∀ y ∈ B, y ≠ 0) → ∀ τ : ℝ, 0 < τ → τ < 1 →
    probX (fun X : Mat k n => IsTauBad τ B X) ≤ Φ / (τ ^ 2 * B.card)

end Supplement

end ElimAgree


