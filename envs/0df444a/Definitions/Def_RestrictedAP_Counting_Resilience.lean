-- Prove2me | Definitions.Def_RestrictedAP_Counting_Resilience
-- name    : RestrictedAP_Counting_Resilience
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:19:52.016482+00:00
-- url     : https://prove2.me/theorems/0d7a0661-3735-49b4-810a-141326f3fde3
-- title:
--   The triple correlation $\Delta_1$ and $(B,\gamma)$-resilient functions
-- statement:
--   For a distribution $\mu$ on $\Sigma^3$ and $g:\Sigma^n\to\mathbb R$, the **triple correlation** is $\Delta_1(g)=\mathbb E_{(x,y,z)\sim\mu^{\otimes n}}[g(x)g(y)g(z)]$ (p. 31). For a distribution $\nu$ on $\Sigma$, $B\in\mathbb N$ and $0<\gamma\le1$, a function $g:\Sigma^n\to[0,1]$ is **$(B,\gamma)$-resilient** (Definition 5.13) if for every $I\subseteq[n]$ with $|I|\le B$ and every $v\in\Sigma^I$,
--   $$\nu^{\bar I}(g_{I\to v})\ \ge\ \gamma\cdot\nu^{\otimes n}(g),$$
--   where $g_{I\to v}$ is $g$ with the coordinates in $I$ fixed to $v$ and $\nu^{\bar I}(g_{I\to v})$ its mean over the remaining coordinates.
--
--   **Formalization Note.** $v\in\Sigma^I$ is a full vector `v : Fin n → Σ` of which only the coordinates in $I$ are used, and $\nu^{\bar I}(g_{I\to v})$ is $\mathbb E_{x\sim\nu^{\otimes n}}[g(v\text{ on }I,\ x\text{ off }I)]$, the same number. The range conditions on $g$ and $\gamma$ are stated where the paper uses them.
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 31 (Δ₁); p. 32, Definition 5.13

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions

namespace RestrictedAP.Counting

/-!
# The triple correlation `Δ₁` and resilient functions

Bhangale, Khot, Liu, Minzer, *A Counting Lemma for Somewhat Restricted 3-APs*,
arXiv:2608.17365 (copy sha256 de0b96c1…), p. 31 (`Δ₁`), p. 32, Definition 5.13.

* `Delta1 μ g = E_{(x,y,z) ∼ μ^{⊗n}}[g(x) g(y) g(z)]` for `μ` on `Sig^3`.
* `Resilient ν B γ g`: for every `I ⊆ [n]` with `|I| ≤ B` and every `v ∈ Σ^I`,
  `ν^{Ī}(g_{I→v}) ≥ γ · ν^{⊗n}(g)`. A string `v ∈ Σ^I` is encoded as a full vector
  `v : Fin n → Sig` of which only the coordinates in `I` are used, and
  `ν^{Ī}(g_{I→v}) = E_{x ∼ ν^{⊗n}}[g(v on I, x off I)]` (the coordinates of `x` in `I` are
  overwritten, so this is the expectation over `Ī` only).
-/

/-- `Δ₁(g) = E_{(x,y,z) ∼ μ^{⊗n}}[g(x) g(y) g(z)]`. -/
noncomputable def Delta1 {Sig : Type*} [Fintype Sig] {n : ℕ} (μ : Sig × Sig × Sig → ℝ)
    (g : (Fin n → Sig) → ℝ) : ℝ :=
  ∑ t : Fin n → Sig × Sig × Sig, tensorPow μ n t *
    (g (fun i => (t i).1) * g (fun i => (t i).2.1) * g (fun i => (t i).2.2))

/-- `g` is `(B, γ)`-resilient (Definition 5.13): for all `I` with `|I| ≤ B` and all `v`,
`ν^{Ī}(g_{I→v}) ≥ γ · ν^{⊗n}(g)`. -/
def Resilient {Sig : Type*} [Fintype Sig] {n : ℕ} (ν : Sig → ℝ) (B : ℕ) (γ : ℝ)
    (g : (Fin n → Sig) → ℝ) : Prop :=
  ∀ (I : Finset (Fin n)), I.card ≤ B → ∀ v : Fin n → Sig,
    γ * expect (tensorPow ν n) g ≤
      expect (tensorPow ν n) (fun x => g (fun i => if i ∈ I then v i else x i))

end RestrictedAP.Counting


