-- Prove2me | Definitions.Def_RandKSATSample_Main_FiniteInteraction
-- name    : RandKSATSample_Main_FiniteInteraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:58:27.271148+00:00
-- url     : https://prove2.me/theorems/2599c553-a16b-42fd-b683-995c4dd93320
-- title:
--   Variance, averaged conditional variance V_j^π, finite-interaction measures (4.26), R(A) and the random labelled hypergraph moment E_ζ[2^{|A_j|}e^{R(A_j)}]
-- statement:
--   For a law $\pi$ on a finite set and $f$ real, $\mathbb E_\pi[f]=\sum_x\pi(x)f(x)$ and $\mathrm{Var}_\pi(f)=\mathbb E_\pi[f^2]-\mathbb E_\pi[f]^2$ (§2.1). For a block $j$ of a product space, $V_j^\pi(f)=\mathbb E_\pi[\mathrm{Var}_\pi(f(X)\mid X_{-j})]$, computed as $\sum_x\pi(x)(f(x)-\mathbb E_\pi[f\mid\text{class of }x])^2$ over the classes of configurations agreeing outside $j$.
--
--   On $\Omega=\prod_{i=1}^s\Omega_i$ with local weights $\ell_i>0$, labelled hyperedges $e\in\mathcal J$ with vertex sets $V_e\subseteq[s]$, coefficients $a_e\in\mathbb R$ and indicators $Y_e$ depending only on $\sigma_{V_e}$, the **finite-interaction measure** is
--   $$\pi(\sigma)=\frac1{Z_\pi}\Big(\prod_{i=1}^s\ell_i(\sigma_i)\Big)\exp\Big(\sum_{e\in\mathcal J}a_eY_e(\sigma_{V_e})\Big)\quad(4.26).$$
--   For $A\subseteq[s]$, $R(A)=\sum_{e:V_e\cap A\neq\emptyset}|a_e|$ (4.27). The random labelled hypergraph $\zeta$ keeps each $e$ independently with probability $1-e^{-2|a_e|}$ (4.28); $A_j$ is the vertex set of the component of $\zeta$ containing $j$, and the moment is $\mathbb E_\zeta[2^{|A_j|}e^{R(A_j)}]$.
--
--   **Formalization Note.** Conditioning is on the class of a relation $R$ (`condMean`, `condVarAvg`); a class of zero mass contributes nothing. $Y_e$ is a Boolean function on all of $\Omega$, and its dependence on $\sigma_{V_e}$ only is a hypothesis of Lemma 4.4. The expectation over $\zeta$ is the finite sum over its edge sets $T\subseteq\mathcal J$ with probability $\prod_{e\in T}(1-e^{-2|a_e|})\prod_{e\notin T}e^{-2|a_e|}$; components are reachability classes of the graph joining two distinct vertices that lie in a common kept hyperedge.
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), §2.1 p. 7, §4 p. 21, §4.2 pp. 26–27, (4.26)–(4.29)

import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace RandKSATSample.Main

noncomputable section

open Classical

/-!
# Variances, averaged conditional variances, finite-interaction measures and random hypergraphs

He, Li, Yang, *Fast Almost-Uniform Sampling of Random k-SAT Solutions*, arXiv:2610.10474
(version not printed; file sha256 563a4d84…), §2.1 (p. 7), §4 opening (p. 21), §4.2 (pp. 26–27),
(4.26)–(4.29).

A law on a finite type `X` is a function `π : X → ℝ`. Conditioning on `X_{−j}` is conditioning on
the class of a relation `R` ("agrees with the configuration outside block `j`").
-/

variable {X : Type} [Fintype X]

/-- `E_π[f] = Σ_x π(x) f(x)`. -/
def expect (π f : X → ℝ) : ℝ := ∑ x, π x * f x

/-- `Var_π(f) = E_π[f²] − E_π[f]²`. -/
def variance (π f : X → ℝ) : ℝ := expect π (fun x => f x ^ 2) - expect π f ^ 2

/-- The conditional mean `E_π[f | class of x]` over the configurations `y` with `R x y`. -/
def condMean (π f : X → ℝ) (R : X → X → Prop) (x : X) : ℝ :=
  (∑ y ∈ Finset.univ.filter (R x), π y * f y) / (∑ y ∈ Finset.univ.filter (R x), π y)

/-- The averaged conditional variance `E_π[Var_π(f(X) | class of X)]`; with `R` = "agrees outside
block `j`" this is `V_j^π(f) = E_π[Var_π(f(X) | X_{−j})]`. -/
def condVarAvg (π f : X → ℝ) (R : X → X → Prop) : ℝ :=
  ∑ x, π x * (f x - condMean π f R x) ^ 2

/-! ## Finite-interaction measures on a product space (4.26) -/

section product

variable {s : ℕ} {Ωi : Fin s → Type} [∀ i, Fintype (Ωi i)]

/-- Two configurations of `Π_i Ω_i` agree outside the coordinate `j` (`X_{−j} = σ_{−j}`). -/
def AgreeExcept (j : Fin s) (σ σ' : ∀ i, Ωi i) : Prop := ∀ i, i ≠ j → σ i = σ' i

/-- The unnormalised weight `(Π_i ℓ_i(σ_i)) exp(Σ_e a_e Y_e(σ))` of (4.26). -/
def interactionWeight {J : Type} [Fintype J] (lw : ∀ i, Ωi i → ℝ) (a : J → ℝ)
    (Y : J → (∀ i, Ωi i) → Bool) (σ : ∀ i, Ωi i) : ℝ :=
  (∏ i, lw i (σ i)) * Real.exp (∑ e, a e * (if Y e σ then 1 else 0))

/-- The finite-interaction measure `π` of (4.26), normalised by `Z_π`. -/
def interactionMeasure {J : Type} [Fintype J] (lw : ∀ i, Ωi i → ℝ) (a : J → ℝ)
    (Y : J → (∀ i, Ωi i) → Bool) (σ : ∀ i, Ωi i) : ℝ :=
  interactionWeight lw a Y σ / ∑ σ', interactionWeight lw a Y σ'

end product

/-! ## The random labelled hypergraph `ζ` and the moment `E_ζ[2^{|A_j|} e^{R(A_j)}]` -/

section hyper

variable {ι : Type} [Fintype ι] {J : Type} [Fintype J]

/-- The graph on the vertex set `ι` in which `i ≠ i'` are adjacent when some hyperedge `e ∈ T`
contains both. Its connected components are those of the hypergraph `T`. -/
def hyperGraph (V : J → Finset ι) (T : Finset J) : SimpleGraph ι :=
  SimpleGraph.fromRel fun i i' => ∃ e ∈ T, i ∈ V e ∧ i' ∈ V e

/-- `A_j`: the vertex set of the connected component of the hypergraph `T` containing `j`
(`{j}` when `j` is isolated). -/
def compOf (V : J → Finset ι) (T : Finset J) (j : ι) : Finset ι :=
  Finset.univ.filter fun i => (hyperGraph V T).Reachable j i

/-- `R(A) = Σ_{e : V_e ∩ A ≠ ∅} |a_e|` (4.27). -/
def Rsum (V : J → Finset ι) (a : J → ℝ) (A : Finset ι) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => (V e ∩ A).Nonempty), |a e|

/-- The probability that the random hypergraph `ζ` (independent edges, `P(ζ_e = 1) =
1 − e^{−2|a_e|}`, (4.28)) has edge set exactly `T`. -/
def hyperProb (a : J → ℝ) (T : Finset J) : ℝ :=
  (∏ e ∈ T, (1 - Real.exp (-2 * |a e|))) * ∏ e ∈ Finset.univ \ T, Real.exp (-2 * |a e|)

/-- `E_ζ[2^{|A_j|} e^{R(A_j)}]`, the expectation over the random hypergraph `ζ` of (4.28). -/
def hyperMoment (V : J → Finset ι) (a : J → ℝ) (j : ι) : ℝ :=
  ∑ T : Finset J, hyperProb a T *
    ((2 : ℝ) ^ (compOf V T j).card * Real.exp (Rsum V a (compOf V T j)))

end hyper

end

end RandKSATSample.Main


