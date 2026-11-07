-- Prove2me | Definitions.Def_SYKCavity_Hermite
-- name    : SYKCavity_Hermite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:43.832356+00:00
-- url     : https://prove2.me/theorems/84321e5b-c0d7-4581-ad61-04f9b738154b
-- title:
--   Hermite products $\langle J_{A_1}\cdots J_{A_v}\rangle_J$, the coefficients $F_{O;A_1,\dots,A_v}$ and the truncated expansion $\mathcal N_O(J)$
-- statement:
--   With the probabilists' Hermite polynomials $He_m$ ($e^{tx-t^2/2}=\sum_mHe_m(x)t^m/m!$),
--   $$\langle J_{A_1}\cdots J_{A_v}\rangle_J=\prod_{B}He_{\#\{r:A_r=B\}}(J_B)\qquad(3.3)$$
--   (product over all $4$-subsets $B$). With $s_0=1-\sum_{r=1}^vs_r$ and Section 3's $H$,
--   $$F_{O;A_1,\dots,A_v}=\sum_{\pi\in S_v}\int_{\substack{s_1,\dots,s_v\ge0\\ s_1+\dots+s_v\le1}}\frac{\mathbb E_J\operatorname{Tr}\bigl[e^{s_0\beta H}\Gamma_{A_{\pi(1)}}e^{s_1\beta H}\cdots\Gamma_{A_{\pi(v)}}e^{s_v\beta H}O\bigr]}{\mathbb E_J\operatorname{Tr}e^{\beta H}}\,ds_1\cdots ds_v\qquad(4.1)$$
--   and the Hermite expansion truncated at order $V$ is
--   $$\mathcal N_O(J)=\sum_{v=0}^V\frac1{v!}\Bigl(\beta\sqrt{\tfrac3{8N^3}}\Bigr)^v\sum_{A_1,\dots,A_v}\langle J_{A_1}\cdots J_{A_v}\rangle_JF_{O;A_1,\dots,A_v}.\qquad(4.2)$$
--
--   $\mathcal N_O(J)$ is the degree-$V$ Hermite approximation of $\operatorname{Tr}(Oe^{\beta H})/\mathbb E_J\operatorname{Tr}e^{\beta H}$ that the algorithm evaluates (Lemma 4).
--
--   **Formalization Note** The inner sum is over ordered $v$-tuples of $4$-subsets; the simplex carries Lebesgue measure on $\mathbb R^v$ (a point of mass one for $v=0$).
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), (3.2)–(3.3), p.21; (4.1)–(4.2), p.25

import Mathlib
import Definitions.Def_SYKCavity_Correlator

open MeasureTheory

namespace SYKCavity

/-!
# Hermite products, the coefficients `F_{O;A_1,…,A_v}` and the truncated expansion `N_O(J)`

A. Schmidhuber, A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass
transition*, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5): (3.2)–(3.3), p.21; (4.1)–(4.2),
p.25.

**Formalization Note.**
* `He_m` is the probabilists' Hermite polynomial, Mathlib's `Polynomial.hermite m`
  (`e^{tx − t²/2} = Σ He_m(x) t^m/m!`), evaluated at a real argument.
* `hermProd J A = ⟨J_{A_1} ⋯ J_{A_v}⟩_J = ∏_B He_{#{r : A_r = B}}(J_B)`, (3.3), the product over all
  4-subsets `B` (factors with multiplicity `0` are `He_0 = 1`).
* `Fcoef β N O A` is (4.1) with Section 3's Hamiltonian: the sum over `π ∈ S_v` of the integral over
  the simplex `s_1, …, s_v ≥ 0`, `Σ s_r ≤ 1` (Lebesgue measure on `ℝ^v`, `s_0 = 1 − Σ s_r`) of
  `E_J Tr[e^{s_0βH} Γ_{A_{π(1)}} e^{s_1βH} ⋯ Γ_{A_{π(v)}} e^{s_vβH} O] / E_J Tr e^{βH}`. For `v = 0`
  the simplex is a point of mass one.
* `NO β V N O J = Σ_{v=0}^{V} (1/v!) (β √(3/(8N³)))^v Σ_{A_1,…,A_v} ⟨J_{A_1} ⋯ J_{A_v}⟩_J F_{O;A}`,
  (4.2), the inner sum over all ordered `v`-tuples of 4-subsets.
-/

/-- `⟨J_{A_1} ⋯ J_{A_v}⟩_J = ∏_B He_{#{r : A_r = B}}(J_B)`, (3.3). -/
noncomputable def hermProd {N v : ℕ} (J : Quad N → ℝ) (A : Fin v → Quad N) : ℝ := by
  classical
  exact ∏ B : Quad N,
    Polynomial.aeval (J B) (Polynomial.hermite ((Finset.univ.filter (fun r => A r = B)).card))

/-- The simplex `{s ∈ ℝ^v : s_r ≥ 0, Σ s_r ≤ 1}`. -/
def simplex (v : ℕ) : Set (Fin v → ℝ) := {s | (∀ r, 0 ≤ s r) ∧ ∑ r, s r ≤ 1}

/-- `F_{O;A_1,…,A_v}`, (4.1). -/
noncomputable def Fcoef (β : ℝ) (N : ℕ) (O : MOp N) {v : ℕ} (A : Fin v → Quad N) : ℂ :=
  ∑ π : Equiv.Perm (Fin v), ∫ s in simplex v,
    avgRatio β N (fun J => expH β N J (1 - ∑ r, s r) *
      ((List.finRange v).map (fun r => Gamma N (A (π r)).1 * expH β N J (s r))).prod * O)

/-- The Hermite expansion truncated at order `V`, `N_O(J)`, (4.2). -/
noncomputable def NO (β : ℝ) (V N : ℕ) (O : MOp N) (J : Quad N → ℝ) : ℂ :=
  ∑ v ∈ Finset.range (V + 1), ((v.factorial : ℂ))⁻¹ * (((β * scale N : ℝ) : ℂ)) ^ v *
    ∑ A : Fin v → Quad N, ((hermProd J A : ℝ) : ℂ) * Fcoef β N O A

end SYKCavity


