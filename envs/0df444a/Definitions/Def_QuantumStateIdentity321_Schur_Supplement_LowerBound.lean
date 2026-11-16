-- Prove2me | Definitions.Def_QuantumStateIdentity321_Schur_Supplement_LowerBound
-- name    : QuantumStateIdentity321_Schur_Supplement_LowerBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:52:25.239504+00:00
-- url     : https://prove2.me/theorems/d32a0cbc-0c13-4a31-ae2c-b9033e4f3c79
-- title:
--   Problem 1 (phase-randomized qubit instances), Problem 2 (binomial counts), total variation distance and Dicke states
-- statement:
--   This module defines the hard instances of §5.
--
--   1. **Problem 1** (p.18). Fix $\alpha\in[0,\pi/2]$. For $\phi\in[0,2\pi)$ let $|\psi_\phi\rangle=\cos\alpha|0\rangle+e^{i\phi}\sin\alpha|1\rangle$ and $|\varphi_\phi\rangle=\sin\alpha|0\rangle+e^{i\phi}\cos\alpha|1\rangle$. For $\theta\in[0,2\pi)^n$ the yes inputs are $|\psi_{\theta_1}\rangle,\dots,|\psi_{\theta_n}\rangle$ (product $|\Psi_0(\theta)\rangle$), and for $i\in[n]$ the no inputs are the same with the $i$-th one replaced by $|\varphi_{\theta_i}\rangle$ (product $|\Psi^1_i(\theta)\rangle$). A tester using $m$ copies of each input **solves Problem 1 with error $\delta$** if it accepts every yes input with probability at least $1-\delta$ and every no input with probability at most $\delta$. The angle of Theorems 5.2 and 5.6 is $\alpha=\frac12\arccos\sqrt{1-\varepsilon}$.
--   2. **Problem 2** (p.20). $P$ is the law of $(X_1,\dots,X_n)$ with $X_i\sim\mathrm{Binomial}(m,p)$ independent; $Q_i$ is the same law with the $i$-th coordinate replaced by an independent $Y\sim\mathrm{Binomial}(m,1-p)$; and $Q=\frac1n\sum_iQ_i$ is the law of $(Z_1,\dots,Z_n)$ when the replaced coordinate $I$ is uniform and independent. The total variation distance is $\|P-Q\|_{TV}=\frac12\sum_x|P(x)-Q(x)|$. An algorithm for Problem 2 is a randomized test, given by its acceptance probability $f(x)\in[0,1]$ on the counts $x$; it **solves Problem 2 with probability at least $1-\delta$** if $\sum_xP(x)f(x)\ge1-\delta$ and $\sum_xQ(x)f(x)\le\delta$.
--   3. **Lemma 5.3's states** (p.19). $|\psi_\phi\rangle=\sqrt{1-p}|0\rangle+e^{i\phi}\sqrt p|1\rangle$; $|\mathrm{wt}_k\rangle=\binom mk^{-1/2}\sum_{|x|=k}|x\rangle$ is the Dicke state on $m$ qubits; and $\mathbb E_{\phi\sim\mathrm{Uniform}(0,2\pi)}[|\psi_\phi\rangle\langle\psi_\phi|^{\otimes m}]$ is the entrywise average $\frac1{2\pi}\int_0^{2\pi}$.
--
--   These are the objects of Theorems 5.1, 5.2, 5.4, 5.6, Lemma 5.3 and Corollary 5.5.
--
--   **Formalization Note** Qubit inputs are `State 2` with basis vectors $|0\rangle,|1\rangle$; a Problem 1 tester is a published `Tester n m 2`. Binomial counts take values in $\{0,\dots,m\}$ (`Fin (m+1)`).
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), §5, Problem 1, (49)–(50), Lemma 5.3, (54), Problem 2, (59), PDF/printed p.18–20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_SwapMatching

/-!
# The hard instances of the lower bound: Problem 1, Problem 2 and Dicke states

Shih-Han Hung, Ming-Hsien Tsai, *Efficient Quantum State Identity Testing*, STOC 2027
submission #321 (October 2026), §5, pp.18–22: Problem 1 (p.18, (49)–(50)), Lemma 5.3's states and
Dicke states (p.19, (54)), Problem 2 and the total variation distance (p.20, (59)).

Problem 1 instances are qubit inputs (`State 2`, basis `|0⟩ = 0`, `|1⟩ = 1`). A Problem 1 tester
with `m` copies of each input state is a published `Tester n m 2`; a Problem 2 algorithm is a
randomized test `f` of the `n` binomial counts, `f x` being its acceptance probability.
-/

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- The qubit vector `a|0⟩ + b|1⟩`. -/
noncomputable def qubit (a b : ℂ) : State 2 := (WithLp.equiv 2 (Fin 2 → ℂ)).symm ![a, b]

/-- Problem 1, p.18: `|ψ_φ⟩ = cos α|0⟩ + e^{iφ} sin α|1⟩`. -/
noncomputable def psiPhase (α φ : ℝ) : State 2 :=
  qubit (Real.cos α) (Complex.exp ((φ : ℂ) * Complex.I) * (Real.sin α : ℂ))

/-- Problem 1, p.18: `|φ_φ⟩ = sin α|0⟩ + e^{iφ} cos α|1⟩`. -/
noncomputable def phiPhase (α φ : ℝ) : State 2 :=
  qubit (Real.sin α) (Complex.exp ((φ : ℂ) * Complex.I) * (Real.cos α : ℂ))

/-- A phase vector `θ ∈ [0, 2π)ⁿ`. -/
def IsPhaseVector {n : ℕ} (θ : Fin n → ℝ) : Prop :=
  ∀ j, θ j ∈ Set.Ico (0 : ℝ) (2 * Real.pi)

/-- (49), p.18, yes case of Problem 1: the inputs `|ψ_{θ₁}⟩, …, |ψ_{θₙ}⟩` (their product is
`|Ψ₀(θ)⟩`). -/
noncomputable def yesInput {n : ℕ} (α : ℝ) (θ : Fin n → ℝ) : Fin n → State 2 :=
  fun j => psiPhase α (θ j)

/-- (50), p.18, no case of Problem 1: the inputs of `|Ψ¹ᵢ(θ)⟩`, i.e. the yes inputs with the
`i`-th one replaced by `|φ_{θᵢ}⟩`. -/
noncomputable def noInput {n : ℕ} (α : ℝ) (θ : Fin n → ℝ) (i : Fin n) : Fin n → State 2 :=
  Function.update (yesInput α θ) i (phiPhase α (θ i))

/-- A tester using `m` copies of each input state solves Problem 1 with angle `α` and error `δ`:
it accepts every yes input `|Ψ₀(θ)⟩` with probability at least `1 − δ`, and accepts every no input
`|Ψ¹ᵢ(θ)⟩` with probability at most `δ` (rejects it with probability at least `1 − δ`), for every
`θ ∈ [0, 2π)ⁿ` and every `i`. -/
def SolvesProblem1 {n m : ℕ} (T : Tester n m 2) (α δ : ℝ) : Prop :=
  (∀ θ : Fin n → ℝ, IsPhaseVector θ → 1 - δ ≤ acceptProb T (yesInput α θ)) ∧
  (∀ θ : Fin n → ℝ, IsPhaseVector θ → ∀ i : Fin n, acceptProb T (noInput α θ i) ≤ δ)

/-- The angle `α = ½ arccos √(1 − ε)` of Theorems 5.2 and 5.6. -/
noncomputable def problem1Angle (ε : ℝ) : ℝ := Real.arccos (Real.sqrt (1 - ε)) / 2

/-! ## Problem 2 (p.20) -/

/-- The `Binomial(m, p)` probability of `k ∈ {0, …, m}`: `C(m,k) p^k (1 − p)^{m−k}`. -/
noncomputable def binomPMF (m : ℕ) (p : ℝ) (k : Fin (m + 1)) : ℝ :=
  (m.choose k.val : ℝ) * p ^ k.val * (1 - p) ^ (m - k.val)

/-- The law `P` of `(X₁, …, Xₙ)`, `Xᵢ ∼ Binomial(m, p)` independent (yes case of Problem 2). -/
noncomputable def yesLaw (n m : ℕ) (p : ℝ) (x : Fin n → Fin (m + 1)) : ℝ :=
  ∏ j, binomPMF m p (x j)

/-- The law `Qᵢ` of `(X₁, …, Xₙ)` with `Xᵢ` replaced by an independent `Y ∼ Binomial(m, 1 − p)`. -/
noncomputable def replacedLaw (n m : ℕ) (p : ℝ) (i : Fin n) (x : Fin n → Fin (m + 1)) : ℝ :=
  ∏ j, if j = i then binomPMF m (1 - p) (x j) else binomPMF m p (x j)

/-- The law `Q = (1/n) Σᵢ Qᵢ` of `(Z₁, …, Zₙ)`: the coordinate `I` that is replaced is uniform on
`[n]` and independent of `(X₁, …, Xₙ, Y)` (no case of Problem 2). -/
noncomputable def noLaw (n m : ℕ) (p : ℝ) (x : Fin n → Fin (m + 1)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, replacedLaw n m p i x

/-- (59), p.20: the total variation distance `‖P − Q‖_TV = ½ Σₓ |P(x) − Q(x)|`. -/
noncomputable def tvDist {X : Type} [Fintype X] (P Q : X → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |P x - Q x|

/-- An algorithm for Problem 2, given by its acceptance probability `f x ∈ [0, 1]` on the
observed counts `x` (classical randomness allowed), solves Problem 2 with probability at least
`1 − δ` if it accepts the yes case with probability at least `1 − δ` and accepts the no case with
probability at most `δ`. -/
def SolvesProblem2 {n m : ℕ} (f : (Fin n → Fin (m + 1)) → ℝ) (p δ : ℝ) : Prop :=
  (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
  1 - δ ≤ ∑ x, yesLaw n m p x * f x ∧
  ∑ x, noLaw n m p x * f x ≤ δ

/-! ## Lemma 5.3's states (p.19) -/

/-- The amplitudes of `|ψ_φ⟩ = √(1 − p)|0⟩ + e^{iφ}√p|1⟩`. -/
noncomputable def binomAmp (p φ : ℝ) : Fin 2 → ℂ :=
  ![(Real.sqrt (1 - p) : ℂ), Complex.exp ((φ : ℂ) * Complex.I) * (Real.sqrt p : ℂ)]

/-- The Hamming weight `|x|` of an `m`-bit string. -/
def hammingWeight {m : ℕ} (x : Fin m → Fin 2) : ℕ :=
  (Finset.univ.filter (fun s => x s = 1)).card

/-- The Dicke state `|wt_k⟩ = C(m,k)^{−1/2} Σ_{|x| = k} |x⟩` on `m` qubits. -/
noncomputable def dicke (m k : ℕ) (x : Fin m → Fin 2) : ℂ :=
  if hammingWeight x = k then ((Real.sqrt (m.choose k : ℝ))⁻¹ : ℂ) else 0

/-- The phase average `E_{φ ∼ Uniform(0, 2π)}[|ψ_φ⟩⟨ψ_φ|^{⊗m}]`, entrywise
`(1/2π) ∫₀^{2π} ψ_φ^{⊗m}(x) · conj(ψ_φ^{⊗m}(y)) dφ`. -/
noncomputable def phaseAveragedPower (p : ℝ) (m : ℕ) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  fun x y => (1 / (2 * Real.pi : ℂ)) *
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      (∏ s, binomAmp p φ (x s)) * star (∏ s, binomAmp p φ (y s))

end QuantumStateIdentity321.Schur.Supplement


