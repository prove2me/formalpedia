-- Prove2me | Definitions.Def_CSPSubsample_gamma
-- name    : CSPSubsample_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:28:12.971102+00:00
-- url     : https://prove2.me/theorems/05f15171-984d-4e28-88ea-5dfe15ca5cf6
-- title:
--   The joint law $\gamma$ of $(U,\mathcal S)$
-- statement:
--   Fix blocks $V_1,\dots,V_T$, a sample size $N$ and a seed size $s$. The law $\gamma$ of $(U,\mathcal S)$: $U=\bigcup_{t\in[T]}U_t$, where each $U_t$, with $|U_t|=N/T$, is sampled without replacement uniformly from $V_t$, and then each $S_t$, with $|S_t|=s$, is sampled without replacement uniformly from $U\setminus U_t$. The probability of an event under $\gamma$ is
--   $$
--   \Pr_{\gamma}[E]=\frac{\#\{(U,\mathcal S)\in\mathcal G:E\}}{\#\mathcal G},\qquad \mathcal G=\{(U,\mathcal S): |U\cap V_t|=N/T,\ S_t\subseteq U\setminus U_t,\ |S_t|=s\ \ \forall t\}.
--   $$
--
--   This is the law under which Lemma 5.4 shows that $\Psi(\mathcal S)$ nearly attains $\mathrm{OPT}^{\mathrm{bal}}(U)$.
--
--   **Formalization Note** Under the sequential description every valid pair has probability $\prod_t\binom{|V_t|}{N/T}^{-1}\prod_t\binom{N-N/T}{s}^{-1}$, because $|U\setminus U_t|=N-N/T$ for every $t$ when $T$ divides $N$; this is constant, so $\gamma$ is the uniform law on the valid pairs $\mathcal G$.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), law γ, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_CSPSubsample_valbal

set_option autoImplicit false

namespace CSPSubsample

/-- The support of the joint law `γ` of `(U, S)` (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.12 =
PDF p.14): the pairs with `|U ∩ V_t| = N/T`, `S_t ⊆ U ∖ U_t` and `|S_t| = s` for every block `t`. -/
def gammaSupport {n T : ℕ} (b : Fin n → Fin T) (N s : ℕ) :
    Finset (Finset (Fin n) × (Fin T → Finset (Fin n))) :=
  Finset.univ.filter fun p =>
    ∀ t, (blockPart b p.1 t).card = N / T ∧ p.2 t ⊆ blockCompl b p.1 t ∧ (p.2 t).card = s

/-- The probability of an event under the joint law `γ` of `(U, S)`: "`U = ⋃_t U_t` where `U_t`
(with `|U_t| = N/T`) is sampled without replacement uniformly from `V_t`, and then `S_t` (with
`|S_t| = s`) is sampled without replacement uniformly from `U ∖ U_t`" (arXiv:2608.00203 (PDF
sha256 fd9ae011…), p.12 = PDF p.14).

**Formalization Note** `γ` is the uniform law on `gammaSupport`. Every valid pair has
probability `∏_t C(|V_t|, N/T)⁻¹ · ∏_t C(N − N/T, s)⁻¹` under the sequential description,
since `|U ∖ U_t| = N − N/T` for every `t` (given `T ∣ N`), a constant; so the sequential law is
uniform on the valid pairs. -/
noncomputable def probGamma {n T : ℕ} (b : Fin n → Fin T) (N s : ℕ)
    (E : Finset (Fin n) × (Fin T → Finset (Fin n)) → Prop) [DecidablePred E] : ℝ :=
  (((gammaSupport b N s).filter E).card : ℝ) / ((gammaSupport b N s).card : ℝ)

end CSPSubsample


