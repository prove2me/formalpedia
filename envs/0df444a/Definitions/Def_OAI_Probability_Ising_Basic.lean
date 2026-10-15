-- Prove2me | Definitions.Def_OAI_Probability_Ising_Basic
-- name    : OAI_Probability_Ising_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:54:42.98302+00:00
-- url     : https://prove2.me/theorems/fd32f2c1-ade7-4ccd-bfb0-a02d64613708
-- title:
--   Joint block weights, Gibbs expectations and the arbitrary-field covariance bound for finite Ising models
-- statement:
--   Throughout, $G$ is a finite ferromagnetic graph on the vertex set $V=\{0,1,\dots,n-1\}$ with $m$ separately indexed edges: edge $e$ has endpoints $l(e)\neq r(e)$ and coupling $K_e\ge 0$, and parallel edges are allowed. A spin configuration is $\sigma\in\{-1,+1\}^V$, an external field is any $h\in\mathbb{R}^V$, and the Ising weight is $w_h(\sigma)=e^{H_h(\sigma)}$ with energy
--
--   $$H_h(\sigma)=\sum_{e}K_e\,\sigma_{l(e)}\sigma_{r(e)}+\sum_{v\in V}h_v\,\sigma_v .$$
--
--   For $S\subseteq V$ we write $\sigma_S=\rho_S$ when two configurations agree at every vertex of $S$. The file introduces three objects.
--
--   1. **Joint weight.** For vertex sets $I,J,F\subseteq V$ and configurations $\tau,a,b$,
--
--      $$W_{h,\tau}(a,b)=\sum_{\sigma:\ \sigma_I=a_I,\ \sigma_J=b_J,\ \sigma_F=\tau_F}w_h(\sigma).$$
--
--      This is the unnormalized joint law of the spin blocks $(\sigma_I,\sigma_J)$ in the model whose spins on $F$ are pinned to $\tau$. Only the restrictions $a_I$, $b_J$ and $\tau_F$ enter.
--
--   2. **Expectation.** For $f:\{-1,+1\}^V\to\mathbb{R}$, the expectation in the unpinned finite Ising measure with field $h$ is
--
--      $$\langle f\rangle_h=\frac{\sum_{\sigma}w_h(\sigma)\,f(\sigma)}{\sum_{\sigma}w_h(\sigma)} .$$
--
--   3. **Arbitrary-field covariance bound.** The proposition asserting that for all $n,m$, every such graph $G$, every field $h\in\mathbb{R}^V$ and all vertices $u,v$ (equal vertices allowed),
--
--      $$\langle\sigma_u\sigma_v\rangle_h-\langle\sigma_u\rangle_h\langle\sigma_v\rangle_h\le\langle\sigma_u\sigma_v\rangle_0 ,$$
--
--      where the right-hand side is the two-point correlation at zero field.
--
--   The joint weight is the basic quantity in the comparison of conditional laws: the conditional probability that $\sigma_I=a_I$ given $\sigma_J=b_J$ and $\sigma_F=\tau_F$ is $W_{h,\tau}(a,b)$ divided by $\sum_{\sigma:\,\sigma_J=b_J,\,\sigma_F=\tau_F}w_h(\sigma)$. The covariance bound expresses that external fields of arbitrary signs never raise the truncated two-point function of a ferromagnet above its zero-field correlation. Here it is only defined as a statement; it is established separately and then used to control effective couplings.
--
--   **Formalization Note** Configurations are `Spins n`, i.e. functions `Fin n → Bool`, and `spin` sends `true` to $1$ and `false` to $-1$; the simp lemmas `spin_true` and `spin_false` record this. The joint weight is `jointWeight G h I J F τ a b` (the pins $\tau$ are listed before $a,b$) and is defined through `constrainedSum`. `ArbitraryFieldCovarianceBound` is a `Prop` quantifying over all graph sizes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BufferedIsing mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BufferedIsing

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

@[simp] lemma spin_true : spin true = 1 := rfl
@[simp] lemma spin_false : spin false = -1 := rfl

/-- The unnormalized I,J marginal with the common pins F fixed. -/
noncomputable def jointWeight {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ a b : Spins n) : ℝ :=
  constrainedSum G h (fun σ => AgreesOn I σ a ∧ AgreesOn J σ b ∧ AgreesOn F σ τ)

/-- Expectation in the unpinned finite Ising law. -/
noncomputable def expectation {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (f : Spins n → ℝ) : ℝ :=
  (∑ σ, weight G h σ * f σ) / ∑ σ, weight G h σ

/-- Arbitrary real background fields do not increase the spin covariance above the zero-field correlation. -/
def ArbitraryFieldCovarianceBound : Prop :=
  ∀ (n m : ℕ) (G : FiniteGraph n m) (h : Fin n → ℝ) (u v : Fin n),
    expectation G h (fun σ => spin (σ u) * spin (σ v)) -
      expectation G h (fun σ => spin (σ u)) * expectation G h (fun σ => spin (σ v)) ≤
    expectation G (fun _ => 0) (fun σ => spin (σ u) * spin (σ v))

end BufferedIsing

end OAI


