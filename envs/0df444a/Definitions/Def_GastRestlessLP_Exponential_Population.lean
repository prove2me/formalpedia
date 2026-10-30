-- Prove2me | Definitions.Def_GastRestlessLP_Exponential_Population
-- name    : GastRestlessLP_Exponential_Population
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:17:57.385987+00:00
-- url     : https://prove2.me/theorems/e3283ec7-1ca7-4b3d-b536-1842380806b9
-- title:
--   Empirical configurations and the independent one-step transition law
-- statement:
--   For $N$ labeled arms, a state assignment $x$ and action assignment $a$ determine counts $n_{s,b}=\#\{i:x_i=s,a_i=b\}$, empirical state fractions $M_s=\#\{i:x_i=s\}/N$, empirical occupation fractions $Y_{s,b}=n_{s,b}/N$, and total activation count $\#\{i:a_i=1\}$. Theorems use $N>0$.
--
--   Conditional on these assignments, the next state vector has probability $\prod_iP^{a_i}_{x_i,x'_i}$ at $x'$. Its finite support is the entire state-vector space. The error vector is $E(x')=M(x')-\phi(Y)$. Expectations and event probabilities use finite sums of weights on the support, through the referenced finite-law definition. Stochasticity of the arm's transition rows normalizes the product law. No unconditional independence of controlled arms is imposed.
-- source:
--   Gast, Gaujal and Yan, arXiv:2106.10067v3 (22 December 2023), https://arxiv.org/abs/2106.10067v3, pp. 4–7, (1), (2), (6)–(10)

import Definitions.Def_GastRestlessLP_Exponential_Model
import Definitions.Def_RawBlending_UB_FinLaw

open scoped BigOperators
noncomputable section

namespace GastRestlessLP.Exponential

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Number of arms in state s assigned action b. -/
def count {N : ℕ} (x : Fin N → S) (a : Fin N → Fin 2) (s : S) (b : Fin 2) : ℕ :=
  (Finset.univ.filter (fun i => x i = s ∧ a i = b)).card

/-- Empirical state vector. Theorems require N > 0. -/
def empirical {N : ℕ} (x : Fin N → S) (s : S) : ℝ :=
  ((Finset.univ.filter (fun i => x i = s)).card : ℝ) / N

/-- Empirical state-action vector. -/
def empiricalAllocation {N : ℕ} (x : Fin N → S) (a : Fin N → Fin 2) : Allocation S :=
  fun s b => (count x a s b : ℝ) / N

/-- Total number activated. -/
def activeCount {N : ℕ} (a : Fin N → Fin 2) : ℕ :=
  (Finset.univ.filter (fun i => a i = 1)).card

/-- Conditional distribution of the next labeled state vector, equation (1).
The product expresses conditional independence, with stochastic rows supplied by Model. -/
noncomputable def transitionLaw (M : Model S) {N : ℕ}
    (x : Fin N → S) (a : Fin N → Fin 2) : RawBlending.UB.FinLaw (Fin N → S) where
  supp := Finset.univ
  weight x' := ∏ i, M.arm.P (a i) (x i) (x' i)

/-- One-step noise centered at the conditional mean of the empirical allocation. -/
def transitionError (M : Model S) {N : ℕ} (x : Fin N → S)
    (a : Fin N → Fin 2) (x' : Fin N → S) : S → ℝ :=
  fun s => empirical x' s - phi M (empiricalAllocation x a) s

/-- Finite-law event probability. Outside-support weights are never used. -/
noncomputable def probability {A : Type} (μ : RawBlending.UB.FinLaw A)
    (p : A → Prop) : ℝ := by
  classical
  exact μ.expect (fun a => if p a then 1 else 0)

end GastRestlessLP.Exponential


