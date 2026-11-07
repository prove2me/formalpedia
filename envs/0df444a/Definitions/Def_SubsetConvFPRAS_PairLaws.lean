-- Prove2me | Definitions.Def_SubsetConvFPRAS_PairLaws
-- name    : SubsetConvFPRAS_PairLaws
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:35.684288+00:00
-- url     : https://prove2.me/theorems/2c9e6b9a-63af-4617-9b03-44cfb929aae2
-- title:
--   Soft intersections $\pi_{t,z}$, the potential $\Phi$, the exchange chain (19), and the factors $w_\lambda,\psi_t$
-- statement:
--   Let $\mu,\nu:2^U\to\mathbb R_{\ge0}$, a penalty vector $t\in(0,1]^U$ and an external field $z\in\mathbb R^U_{>0}$. Write $t^R=\prod_{u\in R}t_u$, $z^R=\prod_{u\in R}z_u$.
--
--   1. The **soft intersection** (§2.3): $\pi_{t,z}(S,T)=\mu(S)\nu(T)\,t^{S\cap T}z^Sz^T/Z_{t,z}$ on pairs of subsets, with partition function $Z_{t,z}$. When $\mu,\nu$ are supported on $\binom Ua$ and $\binom Ub$ this is the **bases pair law** of Definition 5.4. A scalar $t$ is the constant vector.
--   2. The potential (4) $\Phi(y)=\log Z_{t,e^y}-\sum_uy_u$ and the formula $\partial_u\Phi(y)=\pi_{t,z}(u\in S)-\pi_{t,z}(u\notin T)$, $z=e^y$; $\|\nabla\Phi\|_\infty$; and the masses $\pi_{t,z}(T=U\setminus S)$, $\pi_{t,z}(T\ne U\setminus S)$.
--   3. The hypothesis of Lemma 2.5: for every $t\in(0,1]^U$, $z\in\mathbb R^U_{>0}$, an irreducible chain on $\operatorname{supp}\pi_{t,z}$, reversible for $\pi_{t,z}$, with spectral gap at least $\gamma$, whose moves change one of $S,T$ only, and in which for every $u\in S\oplus T$ the total rate of the moves removing the unique copy of $u$ is at most $1$.
--   4. The standing hypotheses of §5: $\mu,\nu\ge0$ supported on $\binom Ua,\binom Ub$ with $a+b=n=|U|\ge1$ and $g_\mu,g_\nu$ log-concave.
--   5. The **exchange chain** (19): for $u\in S$, $v\notin S$,
--   $$q\bigl((S,T),(S-u+v,T)\bigr)=t_u^{-\mathbf 1[u\in T]}\frac{z_v\,\mu(S-u+v)}{\sum_{w\in U\setminus(S-u)}z_w\,\mu(S-u+w)},$$
--   the rates updating $T$ with $(S,\mu)$ and $(T,\nu)$ interchanged, and all other off-diagonal rates $0$.
--   6. The factors of (21) on the ground set $U\sqcup U$: $w_\lambda(S,T)=\hat\mu_{\lambda z}(S)\hat\nu_{\lambda z}(T)$ and $\psi_t(S,T)=t^{S\cap T}$ restricted to $\operatorname{supp}w_\lambda$ (zero outside).
--
--   These are the laws on which the counting algorithm runs: Lemma 2.5 turns a small gradient of $\Phi$ into a large mass of complementary pairs.
--
--   **Formalization Note** A pair $(S,T)$ of the independent-set law is the subset $S\sqcup T$ of $U\sqcup U$, so that Theorem 1.14 on the ground set $U\sqcup U$ applies literally; $(u,1)$, $(u,2)$ of p.22 are the left and right copies. $\|\nabla\Phi\|_\infty$ is the maximum over $U$ (and $0$ on $U=\emptyset$). The verification file proves that the gradient formula is the derivative of $\Phi$.
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), §2.3, (4), Definition 2.4, Lemma 2.5, pp.12–14; §5, Definitions 5.2, 5.4, (19), (21), pp.21–22

import Mathlib
import Definitions.Def_SubsetConvFPRAS_SetWeights
import Definitions.Def_SubsetConvFPRAS_ReversibleChain
import Definitions.Def_SubsetConvFPRAS_Hadamard

open scoped Classical

namespace SubsetConvFPRAS

/-!
# Soft intersections, the exchange chain and the independent-set pair law

X. Chen, K. Liu, *An FPRAS for Counting Common Bases of Two Matroids*, arXiv:2610.06724 (version held,
sha256 6c1d68c2…), §2.3, (4), Definition 2.4, Lemma 2.5, pp.12–14; §5, Definitions 5.2, 5.4, (19), (21),
pp.21–22.

**Formalization Note.**
* `softLaw μ ν t z` is `π_{t,z}`. On weights supported on `(U choose a)` and `(U choose b)` it is the
  bases pair law of Definition 5.4; on general nonzero weights it is the soft intersection of §2.3.
  A scalar penalty `t` is the constant vector `fun _ => t`.
* A pair `(S,T)` of the independent-set pair law is the set `S.disjSum T ⊆ U ⊕ U`, so that Theorem 1.14 on
  the ground set `U ⊕ U` applies literally; `(u,1)` is `Sum.inl u`, `(u,2)` is `Sum.inr u` (p.22).
* `‖∇Φ‖∞` is the real supremum over the finite set `U`, which is `0` at `U = ∅`.
-/

variable {U : Type} [Fintype U] [DecidableEq U]

/-- The unnormalized soft weight `μ(S) ν(T) t^{S∩T} z^S z^T`, §2.3, p.12–13. -/
noncomputable def softWeight (μ ν : Finset U → ℝ) (t z : U → ℝ) (x : Finset U × Finset U) : ℝ :=
  μ x.1 * ν x.2 * (∏ u ∈ x.1 ∩ x.2, t u) * (∏ u ∈ x.1, z u) * ∏ u ∈ x.2, z u

/-- The partition function `Z_{t,z}`, p.13 (and Definition 5.4, p.21). -/
noncomputable def softPartition (μ ν : Finset U → ℝ) (t z : U → ℝ) : ℝ :=
  ∑ x, softWeight μ ν t z x

/-- The law `π_{t,z}`, p.12 (and Definition 5.4, p.21). -/
noncomputable def softLaw (μ ν : Finset U → ℝ) (t z : U → ℝ) : Finset U × Finset U → ℝ :=
  fun x => softWeight μ ν t z x / softPartition μ ν t z

/-- `Φ(y) = log Z_{t,e^y} - ∑_u y_u`, Definition 2.4, (4), p.13. -/
noncomputable def softPhi (μ ν : Finset U → ℝ) (t y : U → ℝ) : ℝ :=
  Real.log (softPartition μ ν t (fun u => Real.exp (y u))) - ∑ u, y u

/-- `∂_uΦ(y) = π_{t,z}(u ∈ S) - π_{t,z}(u ∉ T)`, (4), p.13, with `z = e^y`. -/
noncomputable def softGrad (μ ν : Finset U → ℝ) (t z : U → ℝ) (u : U) : ℝ :=
  (∑ x, if u ∈ x.1 then softLaw μ ν t z x else 0) -
    ∑ x, if u ∉ x.2 then softLaw μ ν t z x else 0

/-- `‖∇Φ(y)‖∞`, with `z = e^y`. -/
noncomputable def softGradSup (μ ν : Finset U → ℝ) (t z : U → ℝ) : ℝ :=
  ⨆ u, |softGrad μ ν t z u|

/-- `π_{t,z}(T = U∖S)`. -/
noncomputable def complementMass (μ ν : Finset U → ℝ) (t z : U → ℝ) : ℝ :=
  ∑ x, if x.2 = x.1ᶜ then softLaw μ ν t z x else 0

/-- `π_{t,z}(T ≠ U∖S)`. -/
noncomputable def nonComplementMass (μ ν : Finset U → ℝ) (t z : U → ℝ) : ℝ :=
  ∑ x, if x.2 ≠ x.1ᶜ then softLaw μ ν t z x else 0

/-- The hypothesis of Lemma 2.5, p.14: for every `t ∈ (0,1]^U`, `z ∈ ℝ^U_{>0}` there is an irreducible
chain on `supp π_{t,z}`, reversible with respect to `π_{t,z}`, with spectral gap at least `γ`. Each move
updates only one of `S, T`. Whenever `u ∈ S ⊕ T`, the total rate of the moves that leave `u` in neither
set is at most `1`. -/
def HasUniformGap (μ ν : Finset U → ℝ) (γ : ℝ) : Prop :=
  ∀ t z : U → ℝ, (∀ u, 0 < t u ∧ t u ≤ 1) → (∀ u, 0 < z u) →
    ∃ r : Supp (softLaw μ ν t z) → Supp (softLaw μ ν t z) → ℝ,
      IsReversibleChain (onSupp (softLaw μ ν t z)) r ∧
      IsIrreducible r ∧
      HasPoincare (onSupp (softLaw μ ν t z)) r γ ∧
      (∀ x y, x ≠ y → 0 < r x y → x.1.1 = y.1.1 ∨ x.1.2 = y.1.2) ∧
      ∀ x, ∀ u, u ∈ symmDiff x.1.1 x.1.2 →
        (∑ y, if u ∉ y.1.1 ∧ u ∉ y.1.2 then r x y else 0) ≤ 1

/-- The standing hypotheses of §5 (those of Theorem 5.1, p.20): `μ, ν` are nonnegative, supported on
`(U choose a)` and `(U choose b)`, with `a + b = n = |U| ≥ 1`, and `g_μ, g_ν` are log-concave. -/
structure IsHomogeneousPair (a b : ℕ) (μ ν : Finset U → ℝ) : Prop where
  nonneg_left : ∀ S, 0 ≤ μ S
  nonneg_right : ∀ S, 0 ≤ ν S
  homogeneous_left : IsHomogeneous μ a
  homogeneous_right : IsHomogeneous ν b
  degree_sum : a + b = Fintype.card U
  one_le_card : 1 ≤ Fintype.card U
  logConcave_left : IsLogConcave μ
  logConcave_right : IsLogConcave ν

/-- A rate of (19), p.21: `t_u^{-1[u∈T]} z_v μ(S-u+v) / ∑_{w ∈ U∖(S-u)} z_w μ(S-u+w)`. The rates
updating `T` use the same formula with `(S, μ)` and `(T, ν)` interchanged. -/
noncomputable def exchangeCoord (μ : Finset U → ℝ) (t z : U → ℝ) (S T : Finset U) (u v : U) : ℝ :=
  (if u ∈ T then (t u)⁻¹ else 1) * (z v * μ (insert v (S.erase u))) /
    ∑ w ∈ (S.erase u)ᶜ, z w * μ (insert w (S.erase u))

/-- The exchange chain's rates (19), p.21, as a function of the target pair: a move replaces `u ∈ S` by
`v ∉ S` in one of the two sets. All other off-diagonal rates are `0`. -/
noncomputable def exchangeRate (μ ν : Finset U → ℝ) (t z : U → ℝ)
    (x y : Finset U × Finset U) : ℝ :=
  (if y.2 = x.2 then
      ∑ u ∈ x.1, ∑ v ∈ x.1ᶜ,
        if y.1 = insert v (x.1.erase u) then exchangeCoord μ t z x.1 x.2 u v else 0
    else 0) +
  (if y.1 = x.1 then
      ∑ u ∈ x.2, ∑ v ∈ x.2ᶜ,
        if y.2 = insert v (x.2.erase u) then exchangeCoord ν t z x.2 x.1 u v else 0
    else 0)

/-- `w_λ(S,T) = μ̂_{λz}(S) ν̂_{λz}(T)`, p.22, as a weight on subsets of `U ⊕ U`. -/
noncomputable def wLam (μ ν : Finset U → ℝ) (lam : ℝ) (z : U → ℝ) : Finset (U ⊕ U) → ℝ :=
  fun X => upField μ (fun u => lam * z u) X.toLeft * upField ν (fun u => lam * z u) X.toRight

/-- `ψ_t(S,T) = t^{S∩T}` restricted to the support of `w`, p.22, extended by zero outside it. -/
noncomputable def psiRestricted (t : U → ℝ) (w : Finset (U ⊕ U) → ℝ) : Finset (U ⊕ U) → ℝ :=
  fun X => if 0 < w X then ∏ u ∈ X.toLeft ∩ X.toRight, t u else 0

end SubsetConvFPRAS


