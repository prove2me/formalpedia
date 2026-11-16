-- Prove2me | Definitions.Def_PrivPACLower_ICP_Supplement_Basics
-- name    : PrivPACLower_ICP_Supplement_Basics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:09:00.199631+00:00
-- url     : https://prove2.me/theorems/25b7319a-bb1f-4cdb-971d-ecf4118ebd47
-- title:
--   Supplement interfaces: log*, thresholds, packability, unrestricted ICP, representation dimension, coverings
-- statement:
--   Shared interfaces for the supplement, built on the published learning and packing modules of the base mission.
--
--   1. The **iterated logarithm** $\log^* x$ is the number of base-two logarithms needed to bring the real number $x$ below two, and $\ell_M=\log^*(\max\{2,M\})$.
--   2. The **threshold class** on $[N]=\{1,\dots,N\}$ is $\mathrm{Thr}_N=\{h_t : h_t(x)=\mathbf 1\{x\le t\},\ 0\le t\le N\}$; it contains the all-zero and the all-one hypothesis.
--   3. A tuple $(G_1,\dots,G_k)$ is **independently packable** in $H$, written $(G_1,\dots,G_k)\sqsubseteq H$, when injective maps with pairwise disjoint images realize every combination of component hypotheses (Definition 1).
--   4. The **unrestricted ICP** is Definition 2 as printed: for privacy parameters $(\varepsilon,\delta)$, accuracy $\alpha_0$ and a collection $\mathcal G$,
--   $$\mathrm{ICP}_{\varepsilon,\delta}(H,\mathcal G)=\sup_{(G_1,\dots,G_k)\sqsubseteq H,\ G_i\in\mathcal G}\ \sum_{i=1}^k m_{\rm priv}(G_i;\varepsilon,\delta,\alpha_0,1/4),$$
--   taken over packable tuples of members on arbitrary domains, in $[0,\infty]$. On collections of finite-domain classes it coincides with the published ICP of the base mission.
--   5. $\min\{a,\log(\varepsilon/\delta)\}$ is read as $a$ when $\delta=0$.
--   6. A **probabilistic representation** of $H$ is a distribution $Q$ over finite sets $R$ of hypotheses such that for every $h\in H$ and every distribution $\mu$ realized by $h$, $\Pr_{R\sim Q}[\exists f\in R:\ \mathrm{err}_\mu(f)\le 1/4]\ge 3/4$. Its size is $\max_{R\in\operatorname{supp}Q}\log_2|R|$, and $\mathrm{PRDim}(H)$ is the least size (infinite if none exists).
--   7. A learner is **proper** for $H$ when for every input database its output lies in $H$ almost surely.
--   8. Coverings (Definition 5): for $X_i\subseteq X$, $\Psi_i:X_i\to Y_i$ and $o_i:X\setminus X_i\to\{0,1\}$ the **lifted class** $\widetilde G_i$ consists of the hypotheses equal to $g_i\circ\Psi_i$ on $X_i$ and to $o_i$ outside, $g_i\in G_i$. The **direct-label cover** condition of Theorem 9 says the $X_i$ cover $X$ and every $h\in H$ agrees on each $X_i$ with $g_i\circ\Psi_i$ for some $g_i\in G_i$. The **general product class** of Definition 6 is $\{h : h\circ\Phi_i\in G_i\ \forall i\}$ for injective maps whose images partition $X$.
--   9. For a database $T=(z_1,\dots,z_n)\in[M]^n$, $F_T(t)=\frac1n\sum_i\mathbf 1\{z_i\le t\}$.
--
--   These objects are used by every statement of the supplement.
--
--   **Formalization Note** A point of `Fin N` stands for its value plus one. The infimum defining $\log^*$ is over a set that is nonempty for every real argument. PMFs on the labelled domain are the base mission's reading of a distribution; on finite domains they are all distributions. Sizes of representations use $\log_2$, and `Real.logb 2 0 = 0` only affects the empty set, which never helps a representation.
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), pp. 1, 5, 11–12, 22, 29, 47–48, Definitions 1, 2, 5, 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
import Definitions.Def_PrivPACLower_ICP_Packing
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

open PrivPACLower.ICP

/-- The iterated logarithm (p. 1): the number of base-two logarithms needed to bring `x`
below two. The defining set is nonempty for every real `x`. -/
noncomputable def logStar (x : ℝ) : ℕ :=
  sInf {j : ℕ | (Real.logb 2)^[j] x < 2}

/-- `ℓ_M = log*(max{2, M})` (pp. 36, 47). -/
noncomputable def ellStar (M : ℝ) : ℕ := logStar (max 2 M)

/-- The threshold class `Thr_N` on `[N] = {1, …, N}` (p. 12): point `x : Fin N` stands for
`x + 1`, and `h_t(x) = 1{x ≤ t}` for `t ∈ {0, …, N}`. -/
def Thr (N : ℕ) : Set (Fin N → Bool) :=
  {h | ∃ t : ℕ, t ≤ N ∧ ∀ x : Fin N, (h x = true ↔ x.val + 1 ≤ t)}

/-- `(G_1, …, G_k) ⊑ H` (Definition 1): some maps witness an independent packing. -/
def Packable {X : Type*} {k : ℕ} {Y : Fin k → Type*}
    (H : Set (X → Bool)) (Gs : ∀ i, Set (Y i → Bool)) : Prop :=
  ∃ Φ : ∀ i, Y i → X, PackingVia H Gs Φ

/-- Definition 2 (p. 5) without the finite-domain filter of the published `ICP`: the supremum
over all independently packable tuples of members of the collection. -/
noncomputable def ICPAll {X : Type*} (α₀ ε δ : ℝ) (H : Set (X → Bool))
    (G : ClassCollection) : ℝ≥0∞ :=
  ⨆ (k : ℕ) (Y : Fin k → Type)
    (Gs : ∀ i, Set (Y i → Bool)) (_ : ∀ i, Gs i ∈ G (Y i))
    (Φ : ∀ i, Y i → X) (_ : PackingVia H Gs Φ),
      ∑ i, costReal (mpriv (Gs i) ε δ α₀ (1/4))

/-- `min{a, log(ε/δ)}`, read as `a` when `δ = 0` (where `log(ε/0) = +∞`). -/
noncomputable def minLogRatio (a ε δ : ℝ) : ℝ :=
  if δ = 0 then a else min a (Real.log (ε / δ))

/-- A class with at least two hypotheses (standing assumption of §2 and §7.1). -/
def AtLeastTwo {Y : Type*} (G : Set (Y → Bool)) : Prop :=
  ∃ g₁ ∈ G, ∃ g₂ ∈ G, g₁ ≠ g₂

/-- A proper learner: for every input database, its output lies in `H` almost surely. -/
def ProperLearner {X : Type*} {n : ℕ} (H : Set (X → Bool)) (M : Learner X n) : Prop :=
  ∀ S, (M S : Measure (X → Bool)) Hᶜ = 0

/-- A probabilistic `(1/4, 1/4)` representation of `H` (p. 11): a distribution over finite sets
of hypotheses such that, for every `h ∈ H` and every distribution realized by `h`, the random set
contains a hypothesis of error at most `1/4` with probability at least `3/4`. -/
def IsProbRep {X : Type*} (H : Set (X → Bool)) (Q : PMF (Finset (X → Bool))) : Prop :=
  ∀ h ∈ H, ∀ μ : PMF (X × Bool), populationError μ h = 0 →
    ENNReal.ofReal (3/4) ≤
      Q.toOuterMeasure {R | ∃ f ∈ R, populationError μ f ≤ ENNReal.ofReal (1/4)}

/-- The size of a probabilistic representation: the largest `log₂ |R|` over its support. -/
noncomputable def repSize {X : Type*} (Q : PMF (Finset (X → Bool))) : ℝ≥0∞ :=
  ⨆ R ∈ Q.support, ENNReal.ofReal (Real.logb 2 R.card)

/-- The probabilistic representation dimension `PRDim(H)` (p. 11): the least size of a
probabilistic representation (`⊤` if none exists). -/
noncomputable def PRDim {X : Type*} (H : Set (X → Bool)) : ℝ≥0∞ :=
  ⨅ (Q : PMF (Finset (X → Bool))) (_ : IsProbRep H Q), repSize Q

/-- The lifted class `G̃_i` of Definition 5 (p. 29): `g ∘ Ψ` on `X_i`, the fixed `o` outside. -/
def liftedClass {X Y : Type*} (G : Set (Y → Bool)) (Xi : Set X) (Ψ : Xi → Y)
    (o : ↥(Xiᶜ) → Bool) : Set (X → Bool) :=
  {f | ∃ g ∈ G, (∀ (x : X) (hx : x ∈ Xi), f x = g (Ψ ⟨x, hx⟩)) ∧
    ∀ (x : X) (hx : x ∉ Xi), f x = o ⟨x, hx⟩}

/-- The hypotheses of Theorem 9 (p. 30): the fixed sets `X_i` cover `X`, and every `h ∈ H`
agrees on each `X_i` with `g_i ∘ Ψ_i` for some choice of `g_i ∈ G_i`. -/
def DirectLabelCover {X : Type*} {k : ℕ} {Y : Fin k → Type*}
    (H : Set (X → Bool)) (Gs : ∀ i, Set (Y i → Bool))
    (Xs : Fin k → Set X) (Ψ : ∀ i, Xs i → Y i) : Prop :=
  (∀ x : X, ∃ i, x ∈ Xs i) ∧
    ∀ h ∈ H, ∃ g : ∀ i, Y i → Bool, (∀ i, g i ∈ Gs i) ∧
      ∀ i (x : Xs i), h x = g i (Ψ i x)

/-- Injective maps whose images partition `X` (Definition 6). -/
def PartitioningMaps {X : Type*} {k : ℕ} {Y : Fin k → Type*} (Φ : ∀ i, Y i → X) : Prop :=
  (∀ i, Function.Injective (Φ i)) ∧
    (∀ i j, i ≠ j → Disjoint (Set.range (Φ i)) (Set.range (Φ j))) ∧
    ∀ x : X, ∃ i, x ∈ Set.range (Φ i)

/-- The general product class of Definition 6: all `h` with `h ∘ Φ_i ∈ G_i` for every `i`. -/
def GeneralProductClass {X : Type*} {k : ℕ} {Y : Fin k → Type*}
    (Gs : ∀ i, Set (Y i → Bool)) (Φ : ∀ i, Y i → X) : Set (X → Bool) :=
  {h | ∀ i, h ∘ Φ i ∈ Gs i}

/-- `F_T(t) = (1/n) ∑_i 1{z_i ≤ t}` for a database `T ∈ [M]^n` (p. 48); `z : Fin M` is `z + 1`. -/
noncomputable def thresholdCDF {M n : ℕ} (T : Fin n → Fin M) (t : ℕ) : ℝ :=
  (∑ i, if (T i).val + 1 ≤ t then (1 : ℝ) else 0) / n

end PrivPACLower.ICP.Supplement


