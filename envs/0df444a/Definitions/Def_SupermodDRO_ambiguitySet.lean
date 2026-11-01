-- Prove2me | Definitions.Def_SupermodDRO_ambiguitySet
-- name    : SupermodDRO_ambiguitySet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:32.536852+00:00
-- url     : https://prove2.me/theorems/337b0080-cf1f-426e-9c9e-33b896a6229d
-- title:
--   Scenario-wise ambiguity set $\mathcal F$, (3)
-- statement:
--   A distribution $\mathbb P$ of the pair $(\tilde k,\tilde z)\in[K]\times\mathbb R^n$ belongs to $\mathcal F$ when, with $q_k=\mathbb P(\tilde k=k)$,
--   $$
--   q\in\mathcal Q,\qquad \mathbb E_{\mathbb P}[\tilde z\mid\tilde k=k]=\mu^k,\qquad \mathbb E_{\mathbb P}\bigl[|\tilde z_i-\mu_i^k|\bigm|\tilde k=k\bigr]\le\delta_i^k,\qquad \mathbb P(\underline z^k\le\tilde z\le\overline z^k\mid\tilde k=k)=1
--   $$
--   for every $k\in[K]$ and $i\in[n]$.
--
--   **Formalization Note** The conditional constraints are multiplied by $q_k$: $\int_{\{\tilde k=k\}}\tilde z_i\,d\mathbb P=q_k\mu_i^k$, $\int_{\{\tilde k=k\}}|\tilde z_i-\mu_i^k|\,d\mathbb P\le q_k\delta_i^k$, $\mathbb P(\tilde k=k,\ \tilde z\notin[\underline z^k,\overline z^k])=0$. For $q_k>0$ this is (3); for $q_k=0$, where conditioning on $\tilde k=k$ is undefined, the constraints are void.
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), §2.1, (3), p.6

import Mathlib
import Definitions.Def_SupermodDRO_QSet
import Definitions.Def_SupermodDRO_Data

open MeasureTheory

namespace SupermodDRO

/-- **The scenario-wise ambiguity set `𝓕`, (3).** Long, Qi & Zhang, *Supermodularity in Two-Stage
Distributionally Robust Optimization*, author manuscript (June 2022), §2.1, (3), p.6:
"𝓕 = {ℙ | E_ℙ[z̃ | k̃ = k] = µᵏ ∀ k ∈ [K]; E_ℙ[|z̃ᵢ − µᵢᵏ| | k̃ = k] ≤ δᵢᵏ ∀ k ∈ [K], ∀ i ∈ [n];
ℙ(z̲ᵏ ≤ z̃ ≤ z̄ᵏ | k̃ = k) = 1 ∀ k ∈ [K]; ℙ(k̃ = k) = q_k ∀ k ∈ [K]; q ∈ 𝒬}".

A law `P` of the pair `(k̃, z̃)` is a probability measure on `Fin K × ℝⁿ`. With
`q_k = P(k̃ = k)`: `q ∈ 𝒬`, and for every `k` and `i`
`P(k̃ = k, z̃ ∉ [z̲ᵏ, z̄ᵏ]) = 0`, `∫_{k̃ = k} z̃ᵢ dP = q_k µᵢᵏ` and
`∫_{k̃ = k} |z̃ᵢ − µᵢᵏ| dP ≤ q_k δᵢᵏ`.

**Formalization Note** The conditional constraints of (3) are multiplied by `q_k`. For `q_k > 0`
this is (3) verbatim; for `q_k = 0`, where the paper's conditioning on `k̃ = k` is undefined, the
constraints hold trivially. Under the support constraint every integrand is bounded on
`{k̃ = k}` up to a null set, so the Bochner integrals are the honest ones. -/
def ambiguitySet {l m r n K s : ℕ} (D : Data l m r n K s) :
    Set (Measure (Fin K × (Fin n → ℝ))) :=
  {P | IsProbabilityMeasure P ∧
    (fun k => (P ({k} ×ˢ Set.univ)).toReal) ∈ QSet D.R D.ν ∧
    (∀ k, P ({k} ×ˢ (Set.Icc (D.zl k) (D.zu k))ᶜ) = 0) ∧
    (∀ k i, ∫ ω in ({k} ×ˢ Set.univ : Set (Fin K × (Fin n → ℝ))), ω.2 i ∂P =
      (P ({k} ×ˢ Set.univ)).toReal * D.μ k i) ∧
    (∀ k i, ∫ ω in ({k} ×ˢ Set.univ : Set (Fin K × (Fin n → ℝ))), |ω.2 i - D.μ k i| ∂P ≤
      (P ({k} ×ˢ Set.univ)).toReal * D.δ k i)}

end SupermodDRO


