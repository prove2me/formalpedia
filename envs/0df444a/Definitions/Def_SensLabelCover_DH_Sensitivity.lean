-- Prove2me | Definitions.Def_SensLabelCover_DH_Sensitivity
-- name    : SensLabelCover_DH_Sensitivity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:34:37.305986+00:00
-- url     : https://prove2.me/theorems/0ae5d779-e420-4393-9f6a-8d2dcbb5745d
-- title:
--   Couplings, earth mover's distance, swaps, swap distance, swap closure, swap sensitivity and sensitivity-transfer parameters
-- statement:
--   Let $O$ be a finite set of outputs compared by a cost $d : O\times O\to\mathbb R$ (for Label Cover and 2-CSPs, the Hamming distance of assignments). For probability distributions $\mu,\nu$ on $O$, a **coupling** is a distribution $\Gamma$ on $O\times O$ whose two marginals are $\mu$ and $\nu$, and the **earth mover's distance** is
--   $$\mathrm{EMD}(\mu,\nu)=\min_{\Gamma\in\Pi(\mu,\nu)}\ \mathbb E_{(X,Y)\sim\Gamma}\,[d(X,Y)] .$$
--   A cost is a **pseudometric** if $d(x,x)=0$, $d(x,y)=d(y,x)$ and $d(x,z)\le d(x,y)+d(y,z)$.
--
--   The instances of a problem form a set $S$ with a relation "$J$ is obtained from $I$ by one **swap**". A family $\mathcal F\subseteq S$ is **swap-closed** if every one-swap neighbour of a member is a member. The **swap closure** $\mathrm{SwapClo}(\mathcal F)$ consists of all instances reached from members by finitely many swaps, and $\mathrm{SwapDist}(I,J)\le r$ means that some sequence of at most $r$ swaps transforms $I$ into $J$. A (randomized, computationally unrestricted) **algorithm** is any map $A$ from instances to probability distributions on outputs, and its **swap sensitivity** on $\mathcal F$ is
--   $$\mathrm{SwapSens}(A,\mathcal F)=\sup_{I\in\mathcal F}\ \sup_{J \text{ one swap from } I}\ \mathrm{EMD}(A(I),A(J)).$$
--
--   For a reduction $\mathcal T$ from source instances to target instances and recovery maps $\mathcal R_I$ sending distributions on target outputs to distributions on source outputs, nonnegative reals $(C_{\mathcal T},C_{\mathcal R},D_{\mathcal R})$ are **sensitivity-transfer parameters** on a source family $\mathcal X$ if (1) neighbouring $I,\tilde I\in\mathcal X$ have $\mathrm{SwapDist}(\mathcal T(I),\mathcal T(\tilde I))\le C_{\mathcal T}$; (2) $\mathrm{EMD}(\mathcal R_I(\mu),\mathcal R_I(\nu))\le C_{\mathcal R}\,\mathrm{EMD}(\mu,\nu)$ for every $I\in\mathcal X$ and all $\mu,\nu$; (3) $\mathrm{EMD}(\mathcal R_I(\mu),\mathcal R_{\tilde I}(\mu))\le D_{\mathcal R}$ for neighbouring $I,\tilde I\in\mathcal X$ and every $\mu$.
--
--   These are the measuring tools of the whole mission: every sensitivity statement compares output distributions by EMD, and every reduction is analysed through its transfer parameters.
--
--   **Formalization Note** Distributions are Mathlib `PMF`s on a `Fintype`; $\mathbb E$ is the finite sum `expect`. `emd` is the `sInf` over couplings; on a finite type the coupling set is a nonempty compact polytope, so it is the paper's minimum. `swapSens` is the real `sSup` of the set of one-swap EMDs of members; the set is bounded by the largest cost, and its supremum is $0$ when no member has a neighbour. Swap paths are the inductive `SwapPath adj n I J` (exactly $n$ swaps); `SwapDistLE adj I J r` asks for some path of length $\le r$. The transfer parameters are required to be nonnegative (they bound nonnegative quantities); the ranges of neighbouring instances coincide because each problem has one output type.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 14 (PDF 17) end of Definition 2.1; p. 15 (PDF 18) §2.2; p. 18 (PDF 21) Definition 3.1

import Mathlib

open scoped BigOperators

namespace SensLabelCover.DH

/-! Fleming, Hopkins, Yoshida, *Sensitivity and Locality Lower Bounds via Low-Soundness Label
Cover*, STOC 2027 submission (manuscript sha256 5bfe95ad…): the problem-independent layer of
§2.1 (end of Definition 2.1: couplings and earth mover's distance), §2.2 (swaps, swap-closed
families, swap closure, swap distance, swap sensitivity) and Definition 3.1 (sensitivity-transfer
parameters), printed pp. 14–15 and 18 (PDF pp. 17–18 and 21).

Instances of a problem form a type `S`; `adj I J` says that `J` is obtained from `I` by one swap.
Outputs form a finite type `O`, compared by a cost `d : O → O → ℝ` (for the paper's problems,
the Hamming distance of assignments). A (randomized, computationally unrestricted) algorithm is
any map `S → PMF O`. -/

noncomputable section

/-- Expectation `E_{x∼μ}[f(x)]` of a real function under a law on a finite type. -/
def expect {α : Type} [Fintype α] (μ : PMF α) (f : α → ℝ) : ℝ :=
  ∑ x, (μ x).toReal * f x

/-- `γ` is a coupling of `μ` and `ν`: its two marginals are `μ` and `ν` (the set `Π(μ, ν)`). -/
def IsCoupling {α β : Type} (μ : PMF α) (ν : PMF β) (γ : PMF (α × β)) : Prop :=
  γ.map Prod.fst = μ ∧ γ.map Prod.snd = ν

/-- Earth mover's distance with cost `d` (end of Definition 2.1, p. 14):
`EMD(μ, ν) = inf_{Γ ∈ Π(μ, ν)} E_{(X,Y)∼Γ}[d(X, Y)]`. On a finite type the couplings form a
nonempty compact polytope, so the infimum is the paper's minimum. -/
def emd {O : Type} [Fintype O] (d : O → O → ℝ) (μ ν : PMF O) : ℝ :=
  sInf ((fun γ : PMF (O × O) => expect γ (fun p => d p.1 p.2)) '' {γ | IsCoupling μ ν γ})

/-- A cost is a pseudometric: zero on the diagonal, symmetric, triangle inequality. The Hamming
distance is one. -/
structure IsPseudoCost {O : Type} (d : O → O → ℝ) : Prop where
  self : ∀ x, d x x = 0
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- A family `𝓕` is swap-closed: every one-swap neighbour of a member is a member (§2.2). -/
def SwapClosed {S : Type} (adj : S → S → Prop) (𝓕 : Set S) : Prop :=
  ∀ I ∈ 𝓕, ∀ J, adj I J → J ∈ 𝓕

/-- `SwapPath adj n I J`: `J` is reached from `I` by a sequence of exactly `n` swaps. -/
inductive SwapPath {S : Type} (adj : S → S → Prop) : ℕ → S → S → Prop
  | refl (I : S) : SwapPath adj 0 I I
  | step {n : ℕ} {I J K : S} : SwapPath adj n I J → adj J K → SwapPath adj (n + 1) I K

/-- `SwapDist(I, J) ≤ r` (§2.2): some sequence of at most `r` swaps transforms `I` into `J`
(the swap distance is the least such number of swaps). -/
def SwapDistLE {S : Type} (adj : S → S → Prop) (I J : S) (r : ℝ) : Prop :=
  ∃ n : ℕ, SwapPath adj n I J ∧ (n : ℝ) ≤ r

/-- The swap closure `SwapClo(𝓕)`: all instances obtained from members of `𝓕` by repeated
swaps (§2.2). -/
def swapClo {S : Type} (adj : S → S → Prop) (𝓕 : Set S) : Set S :=
  {J | ∃ I ∈ 𝓕, ∃ n : ℕ, SwapPath adj n I J}

/-- Swap sensitivity of an algorithm `A` on a family `𝓕` (§2.2):
`SwapSens(A, 𝓕) = sup_{I ∈ 𝓕} sup_{J one swap from I} EMD(A(I), A(J))`. The set is bounded
(every EMD is at most the largest cost on the finite output type); on an empty set the value is
`0`. -/
def swapSens {S O : Type} [Fintype O] (adj : S → S → Prop) (d : O → O → ℝ) (𝓕 : Set S)
    (A : S → PMF O) : ℝ :=
  sSup {x : ℝ | ∃ I ∈ 𝓕, ∃ J, adj I J ∧ x = emd d (A I) (A J)}

/-- Sensitivity-transfer parameters `(C_𝒯, C_ℛ, D_ℛ)` (Definition 3.1, p. 18) of a reduction
`𝒯 : S → T` with recovery maps `ℛ_I : D(Y) → D(X)` on a source family `𝓧`:
1. neighbouring `I, J ∈ 𝓧` have `SwapDist(𝒯(I), 𝒯(J)) ≤ C_𝒯`;
2. each `ℛ_I` (`I ∈ 𝓧`) is `C_ℛ`-Lipschitz for EMD;
3. neighbouring `I, J ∈ 𝓧` have `EMD(ℛ_I(μ), ℛ_J(μ)) ≤ D_ℛ` for every `μ`.
The three parameters are nonnegative reals (they bound nonnegative quantities). -/
def IsTransferParams {S T OX OY : Type} [Fintype OX] [Fintype OY]
    (adjS : S → S → Prop) (adjT : T → T → Prop) (dX : OX → OX → ℝ) (dY : OY → OY → ℝ)
    (𝓧 : Set S) (𝒯 : S → T) (ℛ : S → PMF OY → PMF OX) (CT CR DR : ℝ) : Prop :=
  0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ DR ∧
  (∀ I ∈ 𝓧, ∀ J ∈ 𝓧, adjS I J → SwapDistLE adjT (𝒯 I) (𝒯 J) CT) ∧
  (∀ I ∈ 𝓧, ∀ μ ν : PMF OY, emd dX (ℛ I μ) (ℛ I ν) ≤ CR * emd dY μ ν) ∧
  (∀ I ∈ 𝓧, ∀ J ∈ 𝓧, adjS I J → ∀ μ : PMF OY, emd dX (ℛ I μ) (ℛ J μ) ≤ DR)

end

end SensLabelCover.DH


