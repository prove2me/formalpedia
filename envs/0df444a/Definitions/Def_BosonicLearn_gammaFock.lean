-- Prove2me | Definitions.Def_BosonicLearn_gammaFock
-- name    : BosonicLearn_gammaFock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:31.038769+00:00
-- url     : https://prove2.me/theorems/4d1b64e4-84d5-404a-a1ab-dfbe287beb20
-- title:
--   The second-quantized operator $\Gamma(R)$ in the Fock basis
-- statement:
--   For $R\in\mathbb C^{n\times n}$, $\Gamma(R)=\bigoplus_{m\ge0}R^{\otimes m}|_{\mathrm{Sym}^m(\mathbb C^n)}$ acts on the Fock space. In the Fock basis,
--
--   $$\langle u|\Gamma(R)|v\rangle=\sqrt{\textstyle\prod_i u_i!\,\prod_j v_j!}\ \sum_{M}\ \prod_{i,j}\frac{R_{ij}^{M_{ij}}}{M_{ij}!},$$
--
--   the sum over nonnegative integer matrices $M$ with row sums $u$ and column sums $v$; equivalently $\operatorname{perm}(R[u|v])/\sqrt{\prod_iu_i!\prod_jv_j!}$, with row $i$ of $R$ repeated $u_i$ times and column $j$ repeated $v_j$ times. The matrix element vanishes unless $|u|=|v|$.
--
--   **Formalization Note** The paper defines $\Gamma$ abstractly; this is the standard Fock-basis formula (boson sampling). Checks: $\langle e_i|\Gamma(R)|e_j\rangle=R_{ij}$, and for one mode $\langle m|\Gamma(r)|m\rangle=r^m$ (proved in the mission's verification file).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2, p. 20

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace BosonicLearn

/-- **The second-quantized operator `Γ(R)` in the Fock basis.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, p. 20: "Γ(X) := ⊕_{m=0}^∞ Γ_m(X) and Γ_m(X) := X^{⊗m}|_{Sym^m(ℂⁿ)}, with Γ_0(X) := 1."

For `R ∈ ℂ^{n×n}` and occupation vectors `u, v ∈ ℕⁿ`,
$$⟨u|Γ(R)|v⟩ = \sqrt{\textstyle\prod_i u_i!\prod_j v_j!}\ \sum_{M} \prod_{i,j} \frac{R_{ij}^{M_{ij}}}{M_{ij}!},$$
the sum over matrices `M ∈ ℕ^{n×n}` with row sums `u` and column sums `v`. This equals
`perm(R[u|v]) / √(∏ u_i! ∏ v_j!)` (row `i` repeated `u_i` times, column `j` repeated `v_j` times). There is no
such `M` unless `|u| = |v|`, so `Γ(R)` is block diagonal in the photon-number sectors.

**Formalization Note.** The paper does not print a Fock-basis formula; this is the standard one. Every such
`M` has `M_ij ≤ u_i`, so the sum runs over a finite box. Sanity: `⟨e_i|Γ(R)|e_j⟩ = R_ij`, and for `n = 1`,
`⟨m|Γ(r)|m⟩ = r^m`. -/
noncomputable def gammaFock {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ :=
  fun u v => (Real.sqrt ((∏ i, (Nat.factorial (u i) : ℝ)) * ∏ j, (Nat.factorial (v j) : ℝ)) : ℂ) *
    ∑ M ∈ (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin n => Finset.range (u i + 1)).filter
        (fun M => (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j),
      ∏ i, ∏ j, R i j ^ (M i j) / (Nat.factorial (M i j) : ℂ)

end BosonicLearn


