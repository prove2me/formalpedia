-- Prove2me | Definitions.Def_IntuitiveDPI_Smooth_Basic
-- name    : IntuitiveDPI_Smooth_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:15.24607+00:00
-- url     : https://prove2.me/theorems/2a685b2c-951e-4903-b916-f2762d7311fe
-- title:
--   pp. 2–7, 9 — CP trace-non-increasing maps, non-conditional H_min^ε and H_0^ε, the subnormalized H(A|B) of (36), and the reading of lim_{ε→0} lim_{n→∞}
-- statement:
--   This module fixes the objects of Beaudry–Renner's proof that are not already published. All systems are finite, all logarithms are base 2 (p. 1), and the purified-distance ball is the one of p. 2: for a matrix $\rho$,
--   $$\mathcal B^\varepsilon(\rho)=\{\rho' : \rho'\ge0,\ \operatorname{Tr}\rho'\le1,\ P(\rho',\rho)\le\varepsilon\},$$
--   with $P$ the purified distance built from the generalized fidelity (footnote c).
--
--   1. **Trace non-increasing maps (Lemma A.1, p. 9).** A finite family $(K_j)_j$ of matrices from $\mathcal H_\iota$ to $\mathcal H_\kappa$ is *trace non-increasing* if $\sum_j K_j^\dagger K_j\le \mathbb 1$. The map $\mathcal E(\rho)=\sum_j K_j\rho K_j^\dagger$ is then completely positive and trace non-increasing.
--   2. **Non-conditional min-entropy (p. 4).** $H_{\min}(A)_\rho=\sup\{\lambda\in\mathbb R : \rho\le 2^{-\lambda}\mathbb 1_A\}$, which for positive semidefinite $\rho\ne0$ equals $-\log\|\rho\|_\infty$; it is $+\infty$ for $\rho=0$.
--   3. **Smooth min-entropy (p. 4).** $H^\varepsilon_{\min}(A)_\rho=\sup_{\rho'\in\mathcal B^\varepsilon(\rho)}H_{\min}(A)_{\rho'}$ ($-\infty$ when the ball is empty).
--   4. **0th order Rényi entropy (p. 4).** $H_0(A)_\rho=\log\operatorname{rank}\rho$ ($-\infty$ at rank $0$), and $H^\varepsilon_0(A)_\rho=\inf_{\rho'\in\mathcal B^\varepsilon(\rho)}H_0(A)_{\rho'}$ ($+\infty$ when the ball is empty).
--   5. **Conditional entropy of a subnormalized state, (36), p. 7.**
--   $$H(A|B)_{\tilde\rho}=\frac{1}{\operatorname{Tr}\tilde\rho_{AB}}\ \sup_{\sigma_B}\ \operatorname{Tr}\bigl(\tilde\rho_{AB}(\log(\mathbb 1_A\otimes\sigma_B)-\log\tilde\rho_{AB})\bigr),$$
--   the supremum running over positive definite density matrices $\sigma_B$.
--   6. **The double limit.** For $L\in\mathbb R$ and $f:\mathbb R\times\mathbb N\to[-\infty,+\infty]$, "$L\le\lim_{\varepsilon\to0}\lim_{n\to\infty}f(\varepsilon,n)$" means: for every $\delta>0$ there is $\varepsilon_0>0$ such that for all $\varepsilon\in(0,\varepsilon_0)$ and all sufficiently large $n$, $L-\delta\le f(\varepsilon,n)$. "$\lim_{\varepsilon\to0}\lim_{n\to\infty}f(\varepsilon,n)\le L$" is the mirror statement with $f(\varepsilon,n)\le L+\delta$.
--
--   These objects carry the paper's milestones: the chain rule (Lemma 5.1), the Rényi bounds and the non-conditional QAEP (Lemmas 5.2, 5.4, 5.5), the bound by a nearby conditional entropy (Lemma 5.6), and the two halves of the QAEP (Lemmas 4.1, 4.2).
--
--   **Formalization Note** The conditional smooth min-entropy (2)–(3), the purified distance, the generalized fidelity, the conditional entropy $H(A|B)=H(AB)-H(B)$ and the grouped tensor power $\rho^{\otimes n}$ on $A^nB^n$ are the published definitions of `QAlgorithms_Papers_Independent_Information100_P67`; the Rényi entropy $H_\alpha$ and the partial trace $\operatorname{Tr}_C$ are those of `QAlgorithms_Papers_Independent_Dependency50_P35` (`renyiEntropy`, `marginalAB`), and the non-conditional tensor power is `QAlgorithms.piKron`. All are imported, not redefined. Entropies that can be infinite take values in `EReal`. In (36) the supremum is over positive definite $\sigma_B$ because Lean's `Real.logb 2 0 = 0` would give a singular $\sigma_B$ the value $0$ instead of $-\infty$ on its kernel; this supremum equals the paper's maximum.
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, p. 2 (2), (3), footnote c; p. 4 (H_0^ε, H_min^ε(A)); p. 7 (36); p. 9 Lemma A.1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

namespace IntuitiveDPI.Smooth

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open scoped ComplexOrder Matrix
open Filter

/-- Lemma A.1, p. 9: the map `ρ ↦ Σ_j K_j ρ K_j†` given by the finite Kraus family `K` is
completely positive (by its Kraus form) and trace non-increasing: `Σ_j K_j† K_j ≤ 1`.
The map itself is `QAlgorithms.krausApply K`. -/
def IsTraceNonincreasingKraus {J ι κ : Type*} [Fintype J] [Fintype κ] [DecidableEq ι]
    (K : J → Matrix κ ι ℂ) : Prop :=
  (1 - ∑ j, (K j)ᴴ * K j).PosSemidef

/-- p. 4: the non-conditional min-entropy `H_min(A)_ρ = -log₂ ‖ρ‖_∞`, written as
`sup {λ ∈ ℝ | ρ ≤ 2^{-λ} 1}` (the case of (2) with trivial `B`). Value in `EReal`:
it is `⊤` at `ρ = 0`; for positive semidefinite `ρ ≠ 0` it is `-log₂` of the largest
eigenvalue. -/
def minEntropy {A : Type*} [Fintype A] [DecidableEq A] (ρ : Matrix A A ℂ) : EReal :=
  sSup {h : EReal | ∃ l : ℝ, h = (l : EReal) ∧
    ((Real.rpow 2 (-l) : ℂ) • (1 : Matrix A A ℂ) - ρ).PosSemidef}

/-- p. 4: the non-conditional smooth min-entropy
`H^ε_min(A)_ρ = max_{ρ' ∈ B^ε(ρ)} H_min(A)_{ρ'}`, where `B^ε(ρ)` is the purified-distance
ball of subnormalized operators (p. 2). The empty ball (`ε < 0`) gives `⊥`. -/
def smoothMinEntropy {A : Type*} [Fintype A] [DecidableEq A] (ρ : Matrix A A ℂ) (ε : ℝ) :
    EReal :=
  sSup {h | ∃ τ : Matrix A A ℂ, IsSubnormalized τ ∧ purifiedDistance τ ρ ≤ ε ∧
    h = minEntropy τ}

/-- p. 4: the 0th order Rényi entropy `H_0(A)_ρ = log₂ rank ρ`, in `EReal`
(`⊥ = log 0` at rank `0`). -/
def zeroEntropy {A : Type*} [Fintype A] (ρ : Matrix A A ℂ) : EReal :=
  if ρ.rank = 0 then ⊥ else ((Real.logb 2 (ρ.rank : ℝ) : ℝ) : EReal)

/-- p. 4: the smooth 0th order Rényi entropy `H^ε_0(A)_ρ = min_{ρ' ∈ B^ε(ρ)} H_0(A)_{ρ'}`.
The empty ball (`ε < 0`) gives `⊤`. -/
def smoothZeroEntropy {A : Type*} [Fintype A] [DecidableEq A] (ρ : Matrix A A ℂ) (ε : ℝ) :
    EReal :=
  sInf {h | ∃ τ : Matrix A A ℂ, IsSubnormalized τ ∧ purifiedDistance τ ρ ≤ ε ∧
    h = zeroEntropy τ}

/-- (36), p. 7: the conditional von Neumann entropy of a subnormalized `ρ̃` on `A × B`,
`H(A|B)_ρ̃ = (1 / Tr ρ̃) max_{σ_B} Tr(ρ̃ (log(1_A ⊗ σ_B) - log ρ̃))`, logarithms base 2.
The optimization runs over positive definite density matrices `σ_B`: with Lean's
`log 0 = 0` a singular `σ_B` would get the junk value `0` instead of `-∞` on its kernel,
and the supremum over positive definite `σ_B` equals the maximum in (36). -/
def condEntropySub {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  (ρ.trace.re)⁻¹ * sSup {v : ℝ | ∃ σ : Matrix B B ℂ, IsDensityMatrix σ ∧ σ.PosDef ∧
    v = (ρ * (cfc (fun x : ℝ => Real.logb 2 x) (Matrix.kronecker (1 : Matrix A A ℂ) σ) -
      cfc (fun x : ℝ => Real.logb 2 x) ρ)).trace.re}

/-- The reading of `L ≤ lim_{ε→0} lim_{n→∞} f(ε, n)` (pp. 3–7, App. B): for every `δ > 0`
there is `ε₀ > 0` such that for every `ε ∈ (0, ε₀)`, eventually in `n`, `L - δ ≤ f(ε, n)`;
that is, `L ≤ lim_{ε→0+} liminf_{n→∞} f(ε, n)`. -/
def IidLowerLimit (L : ℝ) (f : ℝ → ℕ → EReal) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∀ᶠ n in atTop, (((L - δ : ℝ)) : EReal) ≤ f ε n

/-- The reading of `lim_{ε→0} lim_{n→∞} f(ε, n) ≤ L`: for every `δ > 0` there is `ε₀ > 0`
such that for every `ε ∈ (0, ε₀)`, eventually in `n`, `f(ε, n) ≤ L + δ`; that is,
`lim_{ε→0+} limsup_{n→∞} f(ε, n) ≤ L`. -/
def IidUpperLimit (L : ℝ) (f : ℝ → ℕ → EReal) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∀ᶠ n in atTop, f ε n ≤ (((L + δ : ℝ)) : EReal)

end

end IntuitiveDPI.Smooth


