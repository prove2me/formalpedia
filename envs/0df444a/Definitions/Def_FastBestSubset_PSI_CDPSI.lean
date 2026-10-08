-- Prove2me | Definitions.Def_FastBestSubset_PSI_CDPSI
-- name    : FastBestSubset_PSI_CDPSI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:57.906545+00:00
-- url     : https://prove2.me/theorems/2036607f-865d-4c0b-874c-dd4904b84812
-- title:
--   Definition 3 (PSI(k) minima), Problem (14) and Algorithm 2 (CD-PSI(k))
-- statement:
--   This file builds on the model of Problem (2), with $F$, $\operatorname{Supp}$, $U_S$, stationarity and the CDSS iterates of Algorithm 1 as defined there. It adds the local combinatorial search of Hazimeh and Mazumder.
--
--   **PSI minima** (Definition 3). Let $k$ be a positive integer. A vector $\beta^*$ with support $S$ is a *partial swap inescapable minimum of order $k$*, PSI($k$), if it is a stationary solution and, for every $S_1\subseteq S$ and $S_2\subseteq S^c$ with $|S_1|\le k$, $|S_2|\le k$,
--   $$F(\beta^*)\le\min_{\beta_{S_2}}F\big(\beta^*-U_{S_1}\beta^*+U_{S_2}\beta\big).$$
--   In words: removing at most $k$ coordinates of the support, adding at most $k$ new coordinates and optimizing only over the added ones never lowers the objective.
--
--   **Problem (14).** For a vector $\beta^\ell$ with support $S$, the feasible points of
--   $$\min_{\beta,S_1,S_2}F\big(\beta^\ell-U_{S_1}\beta^\ell+U_{S_2}\beta\big)\quad\text{s.t.}\quad S_1\subseteq S,\ S_2\subseteq S^c,\ |S_1|\le k,\ |S_2|\le k$$
--   are the vectors $\beta^\ell-U_{S_1}\beta^\ell+U_{S_2}\beta$ with $S_1,S_2$ as in the constraints. Problem (14) is *improving* at $\beta^\ell$ if it has a feasible point $\hat\beta$ with $F(\hat\beta)<F(\beta^\ell)$.
--
--   **Algorithm 2 (CD-PSI($k$)).** Start with $\hat\beta^0=\beta^0$. For $\ell=0,1,\dots$, let $\beta^{\ell+1}$ be the output of Algorithm 1 initialized with $\hat\beta^\ell$. If Problem (14) is improving at $\beta^{\ell+1}$, let $\hat\beta^{\ell+1}$ be a feasible point with $F(\hat\beta^{\ell+1})<F(\beta^{\ell+1})$; otherwise terminate. A *run* is a pair of sequences $(\hat\beta^\ell)$, $(\beta^{\ell+1})$ that obeys these rules for every iteration $\ell$ that is reached, i.e. for which Problem (14) was improving at $\beta^1,\dots,\beta^\ell$.
--
--   These definitions are the objects of Theorem 4: CD-PSI($k$) terminates after finitely many iterations at a PSI($k$) minimum.
--
--   **Formalization Note** "$F(\beta^*)\le\min_{\beta_{S_2}}F(\cdots)$" is formalized as "$F(\beta^*)\le F(\beta^*-U_{S_1}\beta^*+U_{S_2}\gamma)$ for every $\gamma\in\mathbb R^p$". That is equivalent whether or not the minimum is attained, and only the coordinates of $\gamma$ in $S_2$ matter. $S_2\subseteq S^c$ is `Disjoint S2 (supp β)`, and empty $S_1$, $S_2$ are allowed. Algorithm 1 runs "while not converged" and never stops, so its output is read as the limit of its iterates: the run requires $\beta^{\ell+1}=\lim_{k}\beta^k$ for the CDSS iterates started at $\hat\beta^\ell$. That condition, and the choice of $\hat\beta^{\ell+1}$, are imposed only for iterations that are reached. After termination both sequences are unconstrained, and the entry $\beta^0$ of the sequence $\beta$ is never used. $\hat\beta^{\ell+1}$ may be any improving feasible point, as the box allows. The improvement test is strict ($<$).
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Definition 3 (p. 7), Problem (14) and Algorithm 2 (p. 13)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

open Filter Topology

namespace FastBestSubset.PSI

variable {n p : ℕ}

/-- Definition 3 (PSI minima), p. 7: `β` with support `S` is a PSI minimum of order `k` if it is a
stationary solution and, for every `S₁ ⊆ S` and `S₂ ⊆ Sᶜ` with `|S₁| ≤ k`, `|S₂| ≤ k`,
`F(β) ≤ min_{β_{S₂}} FastBestSubset.CDSS.F(β − U_{S₁}β + U_{S₂}γ)`, read as `F(β) ≤ FastBestSubset.CDSS.F(β − U_{S₁}β + U_{S₂}γ)` for
every `γ`. -/
def IsPSI (D : FastBestSubset.CDSS.Data n p) (k : ℕ) (β : Fin p → ℝ) : Prop :=
  FastBestSubset.CDSS.IsStationary D β ∧
    ∀ S1 S2 : Finset (Fin p), S1 ⊆ FastBestSubset.CDSS.supp β → Disjoint S2 (FastBestSubset.CDSS.supp β) → S1.card ≤ k → S2.card ≤ k →
      ∀ γ : Fin p → ℝ, FastBestSubset.CDSS.F D β ≤ FastBestSubset.CDSS.F D (β - FastBestSubset.CDSS.U S1 β + FastBestSubset.CDSS.U S2 γ)

/-- Feasible points of Problem (14), p. 13, at `b = βℓ`: the vectors `b − U_{S₁}b + U_{S₂}γ` with
`S₁ ⊆ Supp(b)`, `S₂ ⊆ Supp(b)ᶜ`, `|S₁| ≤ k`, `|S₂| ≤ k`. -/
def Feasible14 (k : ℕ) (b βhat : Fin p → ℝ) : Prop :=
  ∃ (S1 S2 : Finset (Fin p)) (γ : Fin p → ℝ),
    S1 ⊆ FastBestSubset.CDSS.supp b ∧ Disjoint S2 (FastBestSubset.CDSS.supp b) ∧ S1.card ≤ k ∧ S2.card ≤ k ∧
      βhat = b - FastBestSubset.CDSS.U S1 b + FastBestSubset.CDSS.U S2 γ

/-- Problem (14) at `b` has a feasible solution `β̂` with `F(β̂) < FastBestSubset.CDSS.F(b)` (the test of
Algorithm 2, p. 13). -/
def Improving14 (D : FastBestSubset.CDSS.Data n p) (k : ℕ) (b : Fin p → ℝ) : Prop :=
  ∃ βhat : Fin p → ℝ, Feasible14 k b βhat ∧ FastBestSubset.CDSS.F D βhat < FastBestSubset.CDSS.F D b

/-- A run of Algorithm 2 (CD-PSI(k)), p. 13, with Algorithm 1's parameter `C`, started at `β⁰`.
`βhat ℓ` is `β̂ℓ` and `β (ℓ+1)` is `βℓ⁺¹` (`β 0` is not used). `β̂⁰ = β⁰`, and for every iteration `ℓ`
reached (no earlier iteration terminated, i.e. Problem (14) had an improving point at
`β¹, …, βℓ`):
* `βℓ⁺¹`, the output of Algorithm 1 initialized with `β̂ℓ`, is the limit of its iterates;
* if Problem (14) at `βℓ⁺¹` has a feasible `β̂` with `F(β̂) < FastBestSubset.CDSS.F(βℓ⁺¹)`, then `β̂ℓ⁺¹` is such a point
  (otherwise the algorithm terminates and later entries are unconstrained). -/
def IsCDPSIRun [NeZero p] (D : FastBestSubset.CDSS.Data n p) (k C : ℕ) (β0 : Fin p → ℝ)
    (βhat β : ℕ → Fin p → ℝ) : Prop :=
  βhat 0 = β0 ∧
    ∀ ℓ : ℕ, (∀ m < ℓ, Improving14 D k (β (m + 1))) →
      Tendsto (FastBestSubset.CDSS.iter D C (βhat ℓ)) atTop (𝓝 (β (ℓ + 1))) ∧
        (Improving14 D k (β (ℓ + 1)) →
          Feasible14 k (β (ℓ + 1)) (βhat (ℓ + 1)) ∧ FastBestSubset.CDSS.F D (βhat (ℓ + 1)) < FastBestSubset.CDSS.F D (β (ℓ + 1)))

end FastBestSubset.PSI


