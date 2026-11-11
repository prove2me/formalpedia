-- Prove2me | Definitions.Def_HopfieldPSpin_Shattering_Shattered
-- name    : HopfieldPSpin_Shattering_Shattered
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:08:48.14665+00:00
-- url     : https://prove2.me/theorems/36140f95-c7cd-474f-b358-844c88c08609
-- title:
--   Shattering (Definition 2.1), Hamming diameter and distance, energy window $W_n(\kappa)$, the set $B_n$, the graph $G_r(S)$, and the free-energy and Laplace-estimate hypotheses
-- statement:
--   For nonempty $A,B\subseteq\Sigma_n$: $\operatorname{diam}_H(A)=\max_{\sigma,\tau\in A}d_H(\sigma,\tau)$ and $\operatorname{dist}_H(A,B)=\min_{\sigma\in A,\tau\in B}d_H(\sigma,\tau)$; $\mu(A)=\sum_{\sigma\in A}\mu(\sigma)$.
--
--   **Definition 2.1(a).** For $0<r<R<1$ and $c=(c_1,c_2,c_3)\in(0,\infty)^3$, a measure $\mu$ on $\Sigma_n$ is **$(r,R,c)$-shattered** if there are pairwise disjoint nonempty $C_1,\dots,C_L\subseteq\Sigma_n$ with $L\ge e^{c_1n}$ such that $\max_i\operatorname{diam}_H(C_i)\le rn$, $\operatorname{dist}_H(C_i,C_j)\ge Rn$ for all $i<j$, $\max_i\mu(C_i)\le e^{-c_2n}$, and $\mu(\bigcup_iC_i)\ge1-e^{-c_3n}$.
--
--   The **energy window** (4.44) is $W_n(\kappa)=\{\sigma:|H_n(\sigma)/n-\beta|\le\kappa\}$ and (4.47) $B_n=\{\sigma\in W_n(\kappa):\exists\tau,\ H_n(\tau)\ge(\beta-\kappa)n,\ d_n(\sigma,\tau)\in[r,R]\}$. For $S\subseteq\Sigma_n$, the graph $G_r(S)$ (Lemma 4.14) has vertex set $S$ and an edge $\{\sigma,\tau\}$ when $\sigma\neq\tau$ and $d_H(\sigma,\tau)<rn$.
--
--   Two hypotheses used by Propositions 4.11, 4.12 and 4.15 are named here. **Free-energy convergence:** $\frac1n\log Z_n(\beta)\to\log2+\beta^2/2$ in probability, i.e. for every $\epsilon>0$, $\mathbb P(|\frac1n\log Z_n(\beta)-\log2-\beta^2/2|>\epsilon)\to0$. **Laplace estimates on a set $A$ of $s$:** there is one sequence $e_n\to0$ with, for all large $n$, all $\sigma,\tau$ and all $s\in A$,
--   $$\Big|\log\mathbb E[e^{sH_n(\sigma)}\mathbf 1_{T_n}]-\tfrac{s^2n}2v_{n,p}\Big|\le e_n\quad(4.23),\qquad \Big|\log\mathbb E[e^{s(H_n(\sigma)+H_n(\tau))}\mathbf 1_{T_n}]-s^2n(v_{n,p}+Q_{n,p}(\sigma,\tau))\Big|\le e_n\quad(4.24).$$
--
--   **Formalization Note.** The shattering predicate takes a mass function $\mu:\Sigma_n\to\mathbb R$ (applied to the Gibbs measure) and contains the parameter conditions $0<r<R<1$ and $c_i>0$. Clusters are a family `Fin L → Finset`; their union is `Finset.biUnion`. $\operatorname{diam}_H$, $\operatorname{dist}_H$ are natural numbers and are only applied to nonempty sets (Lean gives $0$ on empty ones). Components of $G_r(S)$ are Mathlib's `SimpleGraph.ConnectedComponent` on the subtype $S$, mapped back to subsets of $\Sigma_n$.
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 5 (PDF 7), Definition 2.1 and the definitions of diam_H, dist_H; p. 29 (PDF 31), (4.44); p. 30 (PDF 32), (4.47); p. 33 (PDF 35), Lemma 4.14; p. 34 (PDF 36), Proposition 4.15 hypotheses; p. 22 (PDF 24), (4.23)–(4.24)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model
import Definitions.Def_HopfieldPSpin_Shattering_Entropy

open MeasureTheory

noncomputable section

namespace HopfieldPSpin.Shattering

/-- `diam_H(A) = max_{σ, τ ∈ A} d_H(σ, τ)` (p. 5). Used only for nonempty `A` (on `∅` the
Lean value is `0`). -/
def diamH {n : ℕ} (A : Finset (Config n)) : ℕ :=
  (A ×ˢ A).sup fun q => hammingDist q.1 q.2

/-- `dist_H(A, B) = min_{σ ∈ A, τ ∈ B} d_H(σ, τ)` (p. 5). Used only for nonempty `A`, `B`
(otherwise the Lean value is `0`). -/
def distH {n : ℕ} (A B : Finset (Config n)) : ℕ :=
  if h : (A ×ˢ B).Nonempty then (A ×ˢ B).inf' h (fun q => hammingDist q.1 q.2) else 0

/-- Mass `µ(A) = ∑_{σ ∈ A} µ(σ)` of a set of configurations under a mass function `µ`. -/
def massOf {n : ℕ} (μ : Config n → ℝ) (A : Finset (Config n)) : ℝ := ∑ σ ∈ A, μ σ

/-- Definition 2.1(a): `µ` is `(r, R, c)`-shattered, `0 < r < R < 1`, `c ∈ (0, ∞)³`: there are
pairwise disjoint nonempty `C_1, …, C_L ⊆ Σ_n` with `L ≥ e^{c₁ n}`, every diameter `≤ r n`,
every pairwise distance (`i < j`) `≥ R n`, every mass `≤ e^{−c₂ n}`, and union mass
`≥ 1 − e^{−c₃ n}`. -/
def IsShattered (n : ℕ) (r R c₁ c₂ c₃ : ℝ) (μ : Config n → ℝ) : Prop :=
  0 < r ∧ r < R ∧ R < 1 ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
  ∃ L : ℕ, ∃ C : Fin L → Finset (Config n),
    (∀ i, (C i).Nonempty) ∧
    (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
    Real.exp (c₁ * n) ≤ (L : ℝ) ∧
    (∀ i, (diamH (C i) : ℝ) ≤ r * n) ∧
    (∀ i j, i < j → R * n ≤ (distH (C i) (C j) : ℝ)) ∧
    (∀ i, massOf μ (C i) ≤ Real.exp (-(c₂ * n))) ∧
    1 - Real.exp (-(c₃ * n)) ≤ massOf μ (Finset.univ.biUnion C)

/-- The energy window `W_n(κ) = {σ : |H_n(σ)/n − β| ≤ κ}` (4.44). -/
def energyWindow (n M p : ℕ) (β κ : ℝ) (η : Fin M → Fin n → ℝ) : Finset (Config n) :=
  Finset.univ.filter fun σ => |hamiltonian n M p η σ / n - β| ≤ κ

/-- `B_n = {σ ∈ W_n(κ) : ∃ τ, H_n(τ) ≥ (β − κ) n, d_n(σ, τ) ∈ [r, R]}` (4.47). -/
def badSet (n M p : ℕ) (β κ r R : ℝ) (η : Fin M → Fin n → ℝ) : Finset (Config n) :=
  (energyWindow n M p β κ η).filter fun σ =>
    ∃ τ : Config n, (β - κ) * n ≤ hamiltonian n M p η τ ∧ r ≤ normDist σ τ ∧ normDist σ τ ≤ R

/-- The graph `G_r(S)` of Lemma 4.14 on the vertex set `S`: `σ ∼ τ` iff `σ ≠ τ` and
`d_H(σ, τ) < r n`. -/
def clusterGraph (n : ℕ) (r : ℝ) (S : Finset (Config n)) : SimpleGraph S where
  Adj a b := a ≠ b ∧ (hammingDist a.1 b.1 : ℝ) < r * n
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [hammingDist_comm]; exact h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- The vertex set (as a subset of `Σ_n`) of a connected component of `G_r(S)`. -/
def componentVerts {n : ℕ} {r : ℝ} {S : Finset (Config n)}
    (C : (clusterGraph n r S).ConnectedComponent) : Finset (Config n) := by
  classical
  exact (Finset.univ.filter fun v : S => (clusterGraph n r S).connectedComponentMk v = C).map
    (Function.Embedding.subtype _)

/-- Convergence in probability `n⁻¹ log Z_n(β) → f = log 2 + β²/2`: for every `ϵ > 0`, the
probability of `|n⁻¹ log Z_n(β) − f| > ϵ` tends to `0`. -/
def FreeEnergyConverges (p : ℕ) (M : ℕ → ℕ) (law : PatternLaw) (β : ℝ) : Prop :=
  ∀ ϵ : ℝ, 0 < ϵ → Filter.Tendsto
    (fun n : ℕ => disorderLaw n (M n) law
      {η | ϵ < |Real.log (partitionFn n (M n) p β η) / n - (Real.log 2 + β ^ 2 / 2)|})
    Filter.atTop (nhds 0)

/-- The one-replica Laplace estimate (4.23) with a uniform `o(1)` error over all `σ ∈ Σ_n`
and all `s ∈ A`: one error sequence `e_n → 0` with
`|log E[e^{s H_n(σ)} 1_{T_n}] − s² n v_{n,p}/2| ≤ e_n` for all large `n`. -/
def LaplaceOne (p : ℕ) (M : ℕ → ℕ) (law : PatternLaw) (A : Set ℝ) : Prop :=
  ∃ e : ℕ → ℝ, Filter.Tendsto e Filter.atTop (nhds 0) ∧
    ∀ᶠ n in Filter.atTop, ∀ σ : Config n, ∀ s ∈ A,
      |Real.log (truncMGF1 n (M n) p law s σ) - s ^ 2 * n / 2 * covV n p| ≤ e n

/-- The two-replica Laplace estimate (4.24) with a uniform `o(1)` error over all
`σ, τ ∈ Σ_n` and all `s ∈ A`. -/
def LaplaceTwo (p : ℕ) (M : ℕ → ℕ) (law : PatternLaw) (A : Set ℝ) : Prop :=
  ∃ e : ℕ → ℝ, Filter.Tendsto e Filter.atTop (nhds 0) ∧
    ∀ᶠ n in Filter.atTop, ∀ σ τ : Config n, ∀ s ∈ A,
      |Real.log (truncMGF2 n (M n) p law s σ τ) - s ^ 2 * n * (covV n p + covQ n p σ τ)| ≤ e n

end HopfieldPSpin.Shattering


