-- Prove2me | Definitions.Def_IAFTRL_qSoft
-- name    : IAFTRL_qSoft
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:54.65421+00:00
-- url     : https://prove2.me/theorems/45a28048-2c4e-4384-9e0d-f4a729eafabc
-- title:
--   Exponential-weights FTRL update $q_t$
-- statement:
--   Let $\hat L_{t-1,a}=a^\top S$ be the cumulative estimated loss of action $a$, where $S=\sum_{s<t}\hat\theta_s$. The FTRL update of IA-FTRL with the (negative) Shannon entropy $\psi(q)=\sum_aq_a\log q_a$,
--   $$
--   q_t=\operatorname*{arg\,min}_{q\in\mathcal P(\mathcal A)}\big\{\langle q,\hat L_{t-1}\rangle+\beta_t\psi(q)\big\},
--   $$
--   is the exponential-weights distribution
--   $$
--   q_{t,a}=\frac{e^{-\hat L_{t-1,a}/\beta_t}}{\sum_{b\in\mathcal A}e^{-\hat L_{t-1,b}/\beta_t}} .
--   $$
--
--   **Formalization Note** The arg min of (2.1) is replaced by its closed form, the unique minimizer for $\beta_t>0$, which is the form the paper uses in (D.151) and Lemma J.2. The definition takes the scale $\beta$ and the cumulative estimate $S$ as inputs.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, p.17, Eq. (2.1); Eq. (D.151), p.90

import Mathlib

namespace IAFTRL

open Matrix

/-- **The FTRL update `q_t` (exponential weights).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, p.17, Eq. (2.1):
"`q_t = argmin_{q∈𝒫(𝒜)} {⟨q, L̂_{t−1}⟩ + β_t ψ(q)}` … `ψ(q) = Σ_a q_a log q_a` is the (negative) Shannon
entropy", with `L̂_{t−1,a} = a^⊤ Σ_{s<t} θ̂_s`. The minimizer is the softmax written in (D.151),
p.90: `q_{t,a} = e^{−L̂_{t−1,a}/β_t} / Σ_b e^{−L̂_{t−1,b}/β_t}`.

`qSoft β arms S a = exp(−⟨a_a, S⟩/β) / Σ_b exp(−⟨a_b, S⟩/β)`, where `S = Σ_{s<t} θ̂_s` is the
cumulative estimate, so `⟨a_a, S⟩ = L̂_{t−1,a}`.

**Formalization Note.** The `argmin` of (2.1) is replaced by its closed form (the unique minimizer
of the strictly convex objective on the simplex for `β > 0`), the form the paper itself uses in
(D.151) and Lemma J.2. -/
noncomputable def qSoft {d K : ℕ} (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) :
    Fin K → ℝ :=
  fun a => Real.exp (-(arms a ⬝ᵥ S) / β) / ∑ b, Real.exp (-(arms b ⬝ᵥ S) / β)

end IAFTRL


