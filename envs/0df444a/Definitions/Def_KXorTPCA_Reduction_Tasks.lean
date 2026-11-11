-- Prove2me | Definitions.Def_KXorTPCA_Reduction_Tasks
-- name    : KXorTPCA_Reduction_Tasks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:21:26.206437+00:00
-- url     : https://prove2.me/theorems/b8a75b1a-5406-40a8-813e-27aa99baaa02
-- title:
--   Solving detection and exact / weak / strong recovery; the hardness conjectures CONJ(k, ρ) (Definitions C.2, C.3, C.7, C.8; Believed Hardness 2.1, 2.2)
-- statement:
--   Let $T=(T_n)_n$ be a sequence of planted problems and $A$ a program. All probabilities are over the instance and, independently, the program's tapes.
--
--   **Detection** (Definition C.2). The Type I + II error of $A$ at dimension $n$ is
--
--   $$\mathrm{err}_n(A)=\mathbb P_{Y\sim T_n^{\mathrm{NULL}}}[A(Y)=1]+\sup_{x\in\{\pm1\}^n}\mathbb P_{Y\sim (T_n)_x}[A(Y)=0],$$
--
--   and $A$ **solves detection with asymptotic Type I + II error $c$** if $\limsup_{n\to\infty}\mathrm{err}_n(A)\le c$.
--
--   **Recovery** (Definitions C.3, C.7, C.8), up to global sign and uniformly over the secret, with success probability tending to $1$: $A$ solves
--
--   - **exact recovery** if $\inf_x\mathbb P[\hat x\in\{x,-x\}]\to1$;
--   - **weak recovery** if for some constant $c>0$, $\inf_x\mathbb P[|\langle x,\hat x\rangle|\ge c\,n]\to1$;
--   - **strong recovery** if for some sequence $\ell_n\to0$, $\inf_x\mathbb P[1-|\langle x,\hat x\rangle|/n\le\ell_n]\to1$.
--
--   The losses are $\ell_n(x,\hat x)=\mathbf 1_{x\ne\hat x}$ (exact) and $\ell_n(x,\hat x)=1-\langle x,\hat x\rangle/n$ (weak/strong), taken up to sign as $\min(\ell_n(x,\hat x),\ell_n(-x,\hat x))$.
--
--   **Conjectures** (Believed Hardness 2.1, 2.2). $\mathrm{CONJ}(k,\rho)$ for detection at level $c$: for every $\eta>0$ no polynomial-time program solves detection with asymptotic error $c$ for $k$-XOR$(n,m=n^{k(1+\rho)/2},\delta=n^{-k\rho/4-\eta/2})$ (that is, $\log_n\delta$ any fixed constant $<-k\rho/4$); likewise for each recovery notion. $\mathrm{CONJ}_\rho$: $\mathrm{CONJ}(k,\rho)$ for all $k\ge3$.
--
--   **Formalization Note** "Solves" is an asymptotic statement over every dimension $n$ (for every $\gamma>0$ there is $n_0$ with the bound for all $n\ge n_0$). Definitions C.7/C.8 leave the success probability $1-\psi^\star_n$ unspecified; it is taken to tend to $1$. Weak recovery's $\ell^\star_n=1-\Omega(1)$ is the constant $c$; strong recovery's $\ell^\star_n=o(1)$ is the sequence $\ell_n$. Conjectures are stated for every detection level $c$ and every recovery notion separately.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), p. 95 (PDF 98), Definition C.2; p. 96 (PDF 99), Definition C.3, footnote 44; p. 100 (PDF 103), Definitions C.7, C.8; pp. 5–6 (PDF 8–9), Believed Hardness 2.1, 2.2

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Models

set_option autoImplicit false

open Filter Topology

/-!
# Detection and recovery: solving the tasks, and the hardness conjectures

G. Bresler, A. Harbuzova, *Average-Case Reductions for k-XOR and Tensor PCA*, arXiv:2601.19016
(copy sha256 6ec029a7…): Definition C.2 (p. 95), Definition C.3 (p. 96), Definitions C.7, C.8
(p. 100), footnote 44 (recovery up to global sign), Believed Hardness 2.1, 2.2 (pp. 5–6).

All probabilities are over the instance (its tapes) and, independently, the algorithm's tapes.
* Detection error at dimension `n`: `P_{null}[A = 1] + sup_x P_x[A = 0]` (`A = 1` iff `A`
  accepts). Solving detection with asymptotic Type I+II error `c`: `lim sup_n err_n ≤ c`.
* Recovery, up to global sign and uniformly over the secret `x`, with success probability
  tending to 1: exact (`x̂ ∈ {x, −x}`), weak (`|⟨x, x̂⟩| ≥ c n` for a constant `c > 0`), strong
  (`1 − |⟨x, x̂⟩|/n ≤ ℓ_n` for a sequence `ℓ_n → 0`).
-/

namespace KXorTPCA.Reduction

/-- Probability of an event of two independent tape pairs (instance, algorithm). -/
noncomputable def prob2 (E : Tapes → Tapes → Prop) : ℝ := probOver 2 (fun w => E (w 0) (w 1))

/-- Type I + Type II error of `A` on the problem `T` (Definition C.2). -/
noncomputable def detErr {n : ℕ} (A : Program) (T : Task n) : ℝ :=
  prob2 (fun ωi ωa => Accepts A (T.null ωi) ωa) +
    ⨆ x : Signal n, prob2 (fun ωi ωa => ¬ Accepts A (T.planted x ωi) ωa)

/-- `A` solves detection for the sequence `T` with asymptotic Type I + II error `c`:
`lim sup_n detErr A (T n) ≤ c` (Definition C.2). -/
def SolvesDetection (A : Program) (T : (n : ℕ) → Task n) (c : ℝ) : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ n₀ : ℕ, ∀ n ≥ n₀, detErr A (T n) ≤ c + γ

/-- The overlap `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ`. -/
def overlap {n : ℕ} (x y : Signal n) : ℝ := ∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)

/-- The recovery notions of Definitions C.7 and C.8. -/
inductive RecoveryNotion
  /-- Exact recovery (Definition C.7). -/
  | exact
  /-- Weak recovery (Definition C.8, `ℓ⋆_n = 1 − Ω(1)`). -/
  | weak
  /-- Strong recovery (Definition C.8, `ℓ⋆_n = o_n(1)`). -/
  | strong

/-- `A`, run on the planted instance of `T` with secret `x`, outputs an estimate with property
`good`: its probability. -/
noncomputable def recProb {n : ℕ} (A : Program) (T : Task n) (x : Signal n)
    (good : Signal n → Prop) : ℝ :=
  prob2 (fun ωi ωa => good (outVec A n (T.planted x ωi) ωa))

/-- `A` solves the recovery notion `N` for the sequence `T`: up to global sign, uniformly over
the secret, with probability tending to `1` (Definitions C.3, C.7, C.8). -/
def SolvesRecovery : RecoveryNotion → Program → ((n : ℕ) → Task n) → Prop
  | .exact, A, T => ∀ γ : ℝ, 0 < γ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x : Signal n,
      1 - γ ≤ recProb A (T n) x (fun xh => xh = x ∨ xh = -x)
  | .weak, A, T => ∃ c : ℝ, 0 < c ∧ ∀ γ : ℝ, 0 < γ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x : Signal n,
      1 - γ ≤ recProb A (T n) x (fun xh => c * n ≤ |overlap x xh|)
  | .strong, A, T => ∃ ℓ : ℕ → ℝ, Tendsto ℓ atTop (𝓝 0) ∧
      ∀ γ : ℝ, 0 < γ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x : Signal n,
      1 - γ ≤ recProb A (T n) x (fun xh => 1 - |overlap x xh| / n ≤ ℓ n)

/-- The loss of exact recovery, `ℓ_n(x, x̂) = 1_{x ≠ x̂}` (Definition C.7). -/
noncomputable def lossExact {n : ℕ} (x xh : Signal n) : ℝ := by
  classical exact if xh = x then 0 else 1

/-- The loss of weak and strong recovery, `ℓ_n(x, x̂) = 1 − ⟨x, x̂⟩/n` (Definition C.8). -/
noncomputable def lossOverlap {n : ℕ} (x xh : Signal n) : ℝ := 1 - overlap x xh / n

/-- A loss taken up to global sign: `min(ℓ(x, x̂), ℓ(−x, x̂))` (Definition C.3, footnote 44). -/
noncomputable def upToSign {n : ℕ} (ℓ : Signal n → Signal n → ℝ) (x xh : Signal n) : ℝ :=
  min (ℓ x xh) (ℓ (-x) xh)

/-- `CONJ(k, ρ)` for detection at asymptotic error level `c` (Believed Hardness 2.1): no
polynomial-time program solves detection with asymptotic Type I+II error `c` for
`k-XOR(n, m = n^{k(1+ρ)/2}, δ)` with `log_n δ` any fixed constant `< −kρ/4`, i.e.
`δ = n^{−kρ/4−η/2}` with `η > 0`. -/
def ConjDet (c : ℝ) (k : ℕ) (ρ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ¬ ∃ A : Program, PolyTime A ∧
    SolvesDetection A (kModel (Choices.std .xor) k ρ η) c

/-- `CONJ(k, ρ)` for the recovery notion `N` (Believed Hardness 2.1). -/
def ConjRec (N : RecoveryNotion) (k : ℕ) (ρ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ¬ ∃ A : Program, PolyTime A ∧
    SolvesRecovery N A (kModel (Choices.std .xor) k ρ η)

/-- `CONJ_ρ`: `CONJ(k, ρ)` for all `k ≥ 3` (Believed Hardness 2.2), detection at level `c`. -/
def ConjDetAll (c ρ : ℝ) : Prop := ∀ k : ℕ, 3 ≤ k → ConjDet c k ρ

/-- `CONJ_ρ` for the recovery notion `N` (Believed Hardness 2.2). -/
def ConjRecAll (N : RecoveryNotion) (ρ : ℝ) : Prop := ∀ k : ℕ, 3 ≤ k → ConjRec N k ρ

end KXorTPCA.Reduction


