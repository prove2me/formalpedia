-- Prove2me | Definitions.Def_AgreementTop736_Exact_Supplement_Transfer
-- name    : AgreementTop736_Exact_Supplement_Transfer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:43:02.043203+00:00
-- url     : https://prove2.me/theorems/47ba875b-f8b6-4413-824a-a5e52ef1ef1f
-- title:
--   Detection minimum, hitting ranks, deviation, restricted distance and optimal global error
-- statement:
--   Fix a coherent layered set poset with top rank $k$, tested rank $h$, top law $\mu$, and uniform subface kernels $D_s$. For an error set $E\subseteq K$, define the detection probability
--   $$p_s(K,E)=\Pr_{S\sim D_s(\cdot\mid K)}[S\cap E\ne\varnothing].$$
--   Using the equivalent singleton formula in (14), put
--   $$\xi_{k,s}=\min_{K:\mu(K)>0,\ x\in K}\Pr_{S\mid K}[x\in S].$$
--   For $0<\kappa\le1$, the predicate $r\in R(\kappa)$ means $r<k$ and, for every supported $K$, every $R\in P_r$ with $R\subseteq K$, and every $E\subseteq K$ with $|E\cap R|\ge\kappa|R|$, one has $p_h(K,E)\ge1/2$.
--
--   For a local assignment family $F_K:K\to\Sigma$ and a global $g:X\to\Sigma$, the deviation probability is the joint event
--   $$W_s(F,g)=\sum_{K,S}\mu(K)D_s(S\mid K)\mathbf1[F_K|_S\ne g|_S].$$
--   The deviation-bound predicate is $\exists g,\ W_s(F,g)\le A_s\tau_s$, with $\tau_s$ the published rejection probability for this layer's scheme. A restricted-distance guarantee at rank $r$ means that, for every positive-mass $R\in P_r$ and all supported parents $K,K'\supseteq R$, distinct restrictions satisfy
--   $$\#\{x\in R:F_K(x)\ne F_{K'}(x)\}\ge\theta_r|R|.$$
--   Identical restrictions are permitted. Finally,
--   $$\Delta(F)=\min_{g:X\to\Sigma}\Pr_{K\sim\mu}[F_K\ne g|_K].$$
--   These objects supply exactly the combinatorial and deviation premises of Theorem 18.
--
--   **Formalization Note** Both minima are finite minima, with zero as a total-function default for an empty value set. The theorem assumes $\xi_{k,r}>0$; for the optimum, the given local-assignment function supplies the global function $F_\varnothing$, so its value set is nonempty. The optimum's use of a layer-zero scheme reads only its top law and does not run a layer-zero test. Zero-mass faces are omitted from conditional statements as stipulated in Section 2.
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), p.16, Section 5, eqs. (13)–(15), definition of R(κ); Section 2.1, p.7, Δ. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Supplement_Layers

/-! Kaufman–Pham, STOC 2027 submission #736, §2.1 p.7 and §5 p.16,
equations (13)–(15): detection, hitting ranks, restricted distance, and global deviation.
No spectral or agreement bound is built into the layer data. -/

namespace AgreementTop736.Exact.Supplement

open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {α : Type*} [Fintype α] [DecidableEq α]

namespace LayeredPoset

/-- Chance that a uniform s-face of K detects the error set E. -/
def hitProb (P : LayeredPoset V) (s : ℕ) (K E : Finset V) : ℝ :=
  ∑ S, P.down s K S * (if (S ∩ E).Nonempty then 1 else 0)

/-- ξ_{k,s} in the singleton form of (14). Only positive-mass top faces occur.
On an empty set of (K,x) this definition returns 0, which is excluded by ξ_{k,r}>0. -/
def detectionMinimum (P : LayeredPoset V) (s : ℕ) : ℝ :=
  let pairs := (univ : Finset (Finset V × V)).filter (fun p => 0 < P.μ p.1 ∧ p.2 ∈ p.1)
  let values := pairs.image (fun p => (P.scheme s).incl p.1 p.2)
  if h : values.Nonempty then values.min' h else 0

/-- Membership r ∈ R(κ), with h the fixed tested layer. All error sets and all
r-faces in every supported top face are tested, including E with equality at κ|R|. -/
def IsHittingRank (P : LayeredPoset V) (h r : ℕ) (κ : ℝ) : Prop :=
  r < P.k ∧ ∀ K, 0 < P.μ K → ∀ R ∈ P.faces r, R ⊆ K →
    ∀ E, E ⊆ K → κ * (R.card : ℝ) ≤ ((E ∩ R).card : ℝ) →
      (1 / 2 : ℝ) ≤ P.hitProb h K E

/-- The joint deviation event in (15), not full top disagreement or test rejection. -/
def deviationProb (P : LayeredPoset V) (s : ℕ) (F : Finset V → V → α)
    (g : V → α) : ℝ :=
  ∑ K, ∑ S, P.μ K * P.down s K S *
    (if ∃ x ∈ S, F K x ≠ g x then 1 else 0)

/-- Each layer admits its own global witness for the stated deviation constant. -/
def HasDeviationBound (P : LayeredPoset V) (s : ℕ) (F : Finset V → V → α)
    (A : ℝ) : Prop :=
  ∃ g : V → α, P.deviationProb s F g ≤ A * (P.scheme s).rejectionProb F

/-- Distance among distinct restrictions of the actual local assignments from all
positive-mass parents of a positive-mass r-face. Identical restrictions are allowed. -/
def HasRestrictedDistance (P : LayeredPoset V) (r : ℕ) (F : Finset V → V → α)
    (θ : ℝ) : Prop :=
  ∀ R, 0 < P.layerMass r R → ∀ K, 0 < P.μ K → R ⊆ K →
    ∀ K', 0 < P.μ K' → R ⊆ K' →
      (∃ x ∈ R, F K x ≠ F K' x) →
        θ * (R.card : ℝ) ≤ ((R.filter (fun x => F K x ≠ F K' x)).card : ℝ)

/-- The finite attained minimum Δ(F) over all global assignments. The empty-value
branch is 0. For any supplied F, the global function F ∅ witnesses nonemptiness. -/
def optimalDistance (P : LayeredPoset V) (F : Finset V → V → α) : ℝ :=
  let values := (univ : Finset (V → α)).image (fun g => (P.scheme 0).disagreementProb F g)
  if h : values.Nonempty then values.min' h else 0

end LayeredPoset
end
end AgreementTop736.Exact.Supplement


