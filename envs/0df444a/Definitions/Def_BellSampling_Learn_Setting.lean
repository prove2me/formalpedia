-- Prove2me | Definitions.Def_BellSampling_Learn_Setting
-- name    : BellSampling_Learn_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:02.832569+00:00
-- url     : https://prove2.me/theorems/e6ef4a39-e95d-4790-ad26-0a8319baf1e3
-- title:
--   Preliminaries, p. 1 — σ_s, the Bell basis, Bell sampling; p. 2 — the stabilizer set T, the Hermitian Pauli of a string, Algorithm 1
-- statement:
--   This file fixes the objects of Montanaro's *Learning stabilizer states by Bell sampling*.
--
--   **Strings and Pauli-type matrices.** A string $s\in\{0,1\}^{2n}$ is grouped by qubit: coordinate $i$ is the pair $(s_{2i-1},s_{2i})\in\mathbb F_2^2$ labelling qubit $i$, and $s\oplus t$ is coordinatewise addition over $\mathbb F_2$. The four one-qubit matrices are
--   $$\sigma_{00}=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad \sigma_{01}=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad \sigma_{10}=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad \sigma_{11}=\sigma_{10}\sigma_{01}=\begin{pmatrix}0&1\\-1&0\end{pmatrix},$$
--   the Pauli matrices up to applying $-i$ to $\sigma_{11}$. For $s\in\{0,1\}^{2n}$, $\sigma_s=\sigma_{s_1s_2}\otimes\cdots\otimes\sigma_{s_{2n-1}s_{2n}}$, whose entry at row $x$ and column $y$ ($x,y\in\{0,1\}^n$) is $\prod_i \sigma_{s_{2i-1}s_{2i}}(x_i,y_i)$.
--
--   **Bell basis and Bell sampling.** The Bell basis of $\mathbb C^4$ is
--   $$|\sigma_{00}\rangle=\tfrac{1}{\sqrt2}(|00\rangle+|11\rangle),\ |\sigma_{01}\rangle=\tfrac{1}{\sqrt2}(|01\rangle+|10\rangle),\ |\sigma_{10}\rangle=\tfrac{1}{\sqrt2}(|00\rangle-|11\rangle),\ |\sigma_{11}\rangle=\tfrac{1}{\sqrt2}(|01\rangle-|10\rangle),$$
--   and $|\sigma_r\rangle=|\sigma_{r_1r_2}\rangle\cdots|\sigma_{r_{2n-1}r_{2n}}\rangle$ on $2n$ qubits $A_1,\dots,A_n,B_1,\dots,B_n$, the pair $A_iB_i$ carrying the $i$-th factor. *Bell sampling* measures every pair $A_iB_i$ in the Bell basis. On two copies $|\psi\rangle|\psi\rangle$ of an $n$-qubit vector $\psi$ (first copy on $A$, second on $B$) the outcome $r$ has probability
--   $$p_\psi(r)=\Bigl|\sum_{x,y\in\{0,1\}^n}\overline{\langle x,y|\sigma_r\rangle}\,\psi(x)\psi(y)\Bigr|^2 .$$
--
--   **The stabilizer set.** $T(\psi)$ is the set of strings $t$ such that $\psi$ is an eigenvector of $\sigma_t$, i.e. $\sigma_t\psi=c\,\psi$ for some $c\in\mathbb C$: the strings whose $\sigma_t$ lies, up to a phase, in the stabilizer group of $\psi$.
--
--   **Hermitian Pauli of a string.** $M_t=(-i)^{\#\{i:\,t_i=11\}}\sigma_t$, the "corresponding Pauli matrix" whose eigenvalues are $\pm1$; $\sigma_{10}^{\otimes S}$ is $\sigma_t$ for the string $z_S$ with $t_i=10$ on $i\in S$ and $00$ elsewhere.
--
--   **Algorithm 1.** Steps 2–4 succeed on outcomes $r_0,r_1,\dots,r_{2n}$ when the $2n$ vectors $r_i\oplus r_0$ span exactly $T(\psi)$. The $2n+1$ Bell samples each use two fresh copies of $\psi$, so they are independent, and an event $E$ has probability
--   $$\Pr[E]=\sum_{r_0}\sum_{r_1,\dots,r_{2n}}\mathbf 1_E(r_0,r)\,p_\psi(r_0)\prod_{i=1}^{2n}p_\psi(r_i).$$
--   Algorithm 1 uses $2+2\cdot 2n+n=5n+2$ copies of $\psi$, at most two at a time.
--
--   **Formalization Note** Qubit states are functions $\{0,1\}^n\to\mathbb C$ (`StabilizerRank.QState`), with `false` = 0. Strings are `Fin n → ZMod 2 × ZMod 2`. Algorithm 1 is modelled by the law of its outcomes; step 5 is deterministic on the success event and is stated separately. $T(\psi)$ is a set; that it is an $n$-dimensional subspace is a theorem of the mission.
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 1, Preliminaries (σ matrices, Bell basis, σ_s, Bell sampling, |ψ*⟩); p. 2, Learning stabilizer states (T, Algorithm 1)

import Mathlib
import Definitions.Def_StabilizerRank

namespace BellSampling.Learn

open StabilizerRank

/-- A string `s ∈ {0,1}^{2n}`, grouped by qubit: coordinate `i` is the pair
`(s_{2i-1}, s_{2i})` that labels qubit `i`. Addition is the bitwise XOR `⊕`. -/
abbrev PStr (n : ℕ) := Fin n → ZMod 2 × ZMod 2

/-- The index of a computational basis state of one qubit: `false = 0`, `true = 1`. -/
def bitIdx (a : Bool) : Fin 2 := if a then 1 else 0

/-- `σ₀₀ := (1 0; 0 1)`. -/
def sigma00 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- `σ₀₁ := (0 1; 1 0)`. -/
def sigma01 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- `σ₁₀ := (1 0; 0 -1)`. -/
def sigma10 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `σ₁₁ := σ₁₀ σ₀₁`. -/
def sigma11 : Matrix (Fin 2) (Fin 2) ℂ := sigma10 * sigma01

/-- The page's evaluation `σ₁₁ = (0 1; -1 0)`. -/
theorem sigma11_eq : sigma11 = !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigma11, sigma10, sigma01, Matrix.mul_apply, Fin.sum_univ_two]

/-- The one-qubit matrix `σ_c` for a label `c ∈ {0,1}²`, as a matrix indexed by `Bool`
(row `a`, column `b`, with `false = 0`). -/
def sigma1 (c : ZMod 2 × ZMod 2) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    (if c = (0, 0) then sigma00 else if c = (0, 1) then sigma01
      else if c = (1, 0) then sigma10 else sigma11) (bitIdx a) (bitIdx b)

/-- `σ_s := σ_{s₁s₂} ⊗ ⋯ ⊗ σ_{s_{2n-1}s_{2n}}` on `n` qubits: the entry at row `x`,
column `y` is `∏ᵢ σ_{s i}(xᵢ, yᵢ)`. -/
def sigma {n : ℕ} (s : PStr n) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.of fun x y => ∏ i, sigma1 (s i) (x i) (y i)

/-- The two-qubit computational basis vector `|ab⟩`, as a function of `(x, y)`. -/
def ket2 (a b : Bool) : Bool → Bool → ℂ := fun x y => if x = a ∧ y = b then 1 else 0

/-- The Bell basis of `ℂ⁴`, as on the page:
`|σ₀₀⟩ = (|00⟩ + |11⟩)/√2`, `|σ₀₁⟩ = (|01⟩ + |10⟩)/√2`,
`|σ₁₀⟩ = (|00⟩ − |11⟩)/√2`, `|σ₁₁⟩ = (|01⟩ − |10⟩)/√2`.
`bell1 c a b` is the coefficient of `|ab⟩` in `|σ_c⟩` (`a` the `A` qubit, `b` the `B` qubit). -/
noncomputable def bell1 (c : ZMod 2 × ZMod 2) : Bool → Bool → ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) •
    (if c = (0, 0) then ket2 false false + ket2 true true
      else if c = (0, 1) then ket2 false true + ket2 true false
      else if c = (1, 0) then ket2 false false - ket2 true true
      else ket2 false true - ket2 true false)

/-- The Bell vector `|σ_r⟩ = |σ_{r₁r₂}⟩ ⋯ |σ_{r_{2n-1}r_{2n}}⟩` on the `2n` qubits
`A₁ … Aₙ B₁ … Bₙ`, pair `AᵢBᵢ` being `(x i, y i)`: its amplitude at `|x⟩_A |y⟩_B`. -/
noncomputable def bellVec {n : ℕ} (r : PStr n) (x y : Bits n) : ℂ :=
  ∏ i, bell1 (r i) (x i) (y i)

/-- Bell sampling on `|ψ⟩^{⊗2}`: the probability (Born rule) that measuring every pair `AᵢBᵢ`
in the Bell basis returns `r`, where `A` is the first copy and `B` the second, so that the
amplitude of `|ψ⟩|ψ⟩` at `|x⟩|y⟩` is `ψ(x) ψ(y)`. -/
noncomputable def bellProb {n : ℕ} (ψ : QState n) (r : PStr n) : ℝ :=
  ‖∑ x, ∑ y, star (bellVec r x y) * (ψ x * ψ y)‖ ^ 2

/-- `T(ψ)`: the strings `t` such that `σ_t` has `ψ` as an eigenvector, i.e. `σ_t` lies in the
stabilizer group of `ψ` up to a phase. -/
def stabSet {n : ℕ} (ψ : QState n) : Set (PStr n) :=
  {t | ∃ c : ℂ, (sigma t).mulVec ψ = c • ψ}

/-- The Hermitian Pauli matrix of a string `t`: `σ_t` with `−i` applied to each factor `σ₁₁`,
i.e. `(−i)^{#\{i : tᵢ = 11\}} σ_t`. -/
noncomputable def pauliH {n : ℕ} (t : PStr n) : Matrix (Bits n) (Bits n) ℂ :=
  (-Complex.I) ^ (Finset.univ.filter fun i => t i = (1, 1)).card • sigma t

/-- The label of `σ₁₀^{⊗S}`: `σ₁₀` on the qubits of `S`, `σ₀₀` elsewhere. -/
def zStr {n : ℕ} (S : Finset (Fin n)) : PStr n := fun i => if i ∈ S then (1, 0) else (0, 0)

/-- Steps 2–4 of Algorithm 1 succeed on the Bell outcomes `r₀` (step 2) and `r₁, …, r_{2n}`
(step 3): the `2n` vectors `rᵢ ⊕ r₀` span exactly `T(ψ)`, so any basis of the span is a basis
of `T(ψ)`. Algorithm 1 uses `2 + 2·(2n) + n = 5n+2` copies of `ψ`, at most two at a time. -/
def algo1Success {n : ℕ} (ψ : QState n) (r₀ : PStr n) (r : Fin (2 * n) → PStr n) : Prop :=
  ((Submodule.span (ZMod 2) (Set.range fun i => r i + r₀) : Submodule (ZMod 2) (PStr n)) :
      Set (PStr n)) = stabSet ψ

/-- The probability of an event `E` on the outcomes of the `2n + 1` Bell samples of
Algorithm 1. Each sample uses two fresh copies of `ψ`, so the samples are independent and each
has law `bellProb ψ`. -/
noncomputable def algo1Prob {n : ℕ} (ψ : QState n)
    (E : PStr n → (Fin (2 * n) → PStr n) → Prop) : ℝ := by
  classical
  exact ∑ r₀ : PStr n, ∑ r : Fin (2 * n) → PStr n,
    if E r₀ r then bellProb ψ r₀ * ∏ i, bellProb ψ (r i) else 0

end BellSampling.Learn


