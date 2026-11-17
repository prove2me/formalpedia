-- Prove2me | Definitions.Def_LiftSAParity_Supplement_extProb
-- name    : LiftSAParity_Supplement_extProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:13:01.216481+00:00
-- url     : https://prove2.me/theorems/0d5537c0-c8c9-4043-bb0e-053e4feae0d2
-- title:
--   The uniformly extended distributions $\widetilde{\mathcal D}_I$ and $\widetilde{\mathcal D}_I[\sigma]$
-- statement:
--   Let $\mathcal D=\{\mathcal D_I\}$ be a family of distributions on blockwise partial assignments over $n$ blocks of $\ell$ variables, and let $A\subseteq\{0,1\}^{[n]\times[\ell]}$.
--
--   The distribution $\widetilde{\mathcal D}_I$ over total assignments samples $\tau\sim\mathcal D_I$ and sets every remaining variable uniformly at random. Thus
--   $$
--   \Pr_{x\sim\widetilde{\mathcal D}_I}[x\in A]=\sum_{\tau}\mathcal D_I(\tau)\,\frac{|\{x\in A: x\supseteq\tau\}|}{|\{x: x\supseteq\tau\}|}.
--   $$
--
--   For a blockwise partial assignment $\sigma$ with $\mathrm{supp}(\sigma)\subseteq I$, the distribution $\mathcal D_I[\sigma]$ is $\mathcal D_I$ conditioned on agreeing with $\sigma$. It is **well-defined** when $|I|\le d$ and some $\tau$ with $\mathcal D_I(\tau)>0$ agrees with $\sigma$. The distribution $\widetilde{\mathcal D}_I[\sigma]$ extends $\mathcal D_I[\sigma]$ uniformly, so
--   $$
--   \Pr_{x\sim\widetilde{\mathcal D}_I[\sigma]}[x\in A]=\frac{\sum_{\tau\supseteq\sigma}\mathcal D_I(\tau)\,|\{x\in A:x\supseteq\tau\}|/|\{x:x\supseteq\tau\}|}{\sum_{\tau\supseteq\sigma}\mathcal D_I(\tau)}.
--   $$
--
--   These are the sampling laws in the definition of fooling distributions (Definition 5.3) and of the measure $\mu$ of §5.3.
--
--   **Formalization Note** `extFrac τ A` is the fraction of the extensions of $\tau$ that lie in $A$; `extProb D I A` and `condExtProb D I σ A` are the two probabilities above, and `CondWellDefined d D I σ` is the well-definedness condition. The conditional probability is used only under that condition, where its denominator is positive.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §5.2, pp.17–18

import Mathlib
import Definitions.Def_LiftSAParity_Supplement_IsBlockLocalDist

namespace LiftSAParity

namespace Supplement

open Classical

/-- The probability that the **uniform extension** of the blockwise partial assignment `τ` to a
total assignment lies in `A`: `|{x ∈ A : x ⊇ τ}| / |{x : x ⊇ τ}|`. -/
noncomputable def extFrac {n ℓ : ℕ} {I : Finset (Fin n)} (τ : BlockAssign n ℓ I)
    (A : Set (Fin n × Fin ℓ → ZMod 2)) : ℝ :=
  ((Finset.univ.filter (fun x => x ∈ A ∧ Agrees x τ)).card : ℝ) /
    ((Finset.univ.filter (fun x : Fin n × Fin ℓ → ZMod 2 => Agrees x τ)).card : ℝ)

/-- `Pr_{x ∼ D̃_I}[x ∈ A]` (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to
Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §5.2, p.18): "We define
D̃_I to be the distribution over total assignments achieved by sampling a partial assignment from
D_I and extending it, setting the remaining variables uniformly at random". So
`Pr_{x∼D̃_I}[x ∈ A] = ∑_τ D_I(τ) · |{x ∈ A : x ⊇ τ}| / 2^{(n−|I|)ℓ}`. -/
noncomputable def extProb {n ℓ : ℕ} (D : (I : Finset (Fin n)) → BlockAssign n ℓ I → ℝ)
    (I : Finset (Fin n)) (A : Set (Fin n × Fin ℓ → ZMod 2)) : ℝ :=
  ∑ τ : BlockAssign n ℓ I, D I τ * extFrac τ A

/-- `D_I[σ]` **is well-defined** (§5.2, pp.17–18): for `supp(σ) ⊆ I`, "The distribution
D_I[σ] is well-defined only if |I| ≤ d and if there is at least one x ∈ supp(D_I) that agrees
with σ." -/
def CondWellDefined {n ℓ : ℕ} (d : ℕ) (D : (I : Finset (Fin n)) → BlockAssign n ℓ I → ℝ)
    (I : Finset (Fin n)) {S : Finset (Fin n)} (σ : BlockAssign n ℓ S) : Prop :=
  S ⊆ I ∧ I.card ≤ d ∧ ∃ τ : BlockAssign n ℓ I, Compat τ σ ∧ 0 < D I τ

/-- `Pr_{x ∼ D̃_I[σ]}[x ∈ A]` (§5.2, pp.17–18): `D_I[σ]` is "the distribution of a random variable
x ∼ D_I conditioned on x agreeing with σ", and `D̃_I[σ]` extends it uniformly to a total
assignment. Equals
`∑_{τ ⊇ σ} D_I(τ) · Pr[uniform extension of τ ∈ A] / ∑_{τ ⊇ σ} D_I(τ)`.

**Formalization Note** Meaningful when `CondWellDefined d D I σ` holds (then the denominator is
positive); every use is guarded by that predicate. -/
noncomputable def condExtProb {n ℓ : ℕ} (D : (I : Finset (Fin n)) → BlockAssign n ℓ I → ℝ)
    (I : Finset (Fin n)) {S : Finset (Fin n)} (σ : BlockAssign n ℓ S)
    (A : Set (Fin n × Fin ℓ → ZMod 2)) : ℝ :=
  (∑ τ ∈ Finset.univ.filter (fun τ : BlockAssign n ℓ I => Compat τ σ), D I τ * extFrac τ A) /
    (∑ τ ∈ Finset.univ.filter (fun τ : BlockAssign n ℓ I => Compat τ σ), D I τ)

end Supplement

end LiftSAParity


