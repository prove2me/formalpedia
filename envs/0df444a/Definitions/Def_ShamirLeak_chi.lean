-- Prove2me | Definitions.Def_ShamirLeak_chi
-- name    : ShamirLeak_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:55.295011+00:00
-- url     : https://prove2.me/theorems/7b0336e4-f901-49a6-b90e-00e9dce2ad34
-- title:
--   Characters $\chi_a$, $\chi_y$ and the norms $\|f\|_2$, $\|f\|_\infty$ (Definition 7, §2.4)
-- statement:
--   Let $e_p(t)=\exp(2\pi i t/p)$ and $\chi_a(x)=e_p(ax)$ for $a\in\mathbb F_p$ (the index $a$ is a frequency); for vectors $y,x\in\mathbb F_p^n$, $\chi_y(x)=e_p(\sum_i y_ix_i)$. For $f:\mathbb F_p\to\mathbb C$ write
--
--   $$\|f\|_2=\big(\mathbb E_x|f(x)|^2\big)^{1/2},\qquad\|f\|_\infty=\max_x|f(x)|,$$
--
--   with expectations under the uniform distribution on $\mathbb F_p$. The normalized Fourier transform $\widehat f(a)=\mathbb E_x[f(x)\overline{\chi_a(x)}]$ of Definition 7 is the published `HWMaskLeak.fhat`.
--
--   The characters enter the dual-code formula (Lemma 2) and the Fourier weights $\|T_i\chi_a\|_2^2$ of Lemma 7; the norms enter Lemmas 12 and 16.
--
--   **Formalization Note** $e_p$ is Mathlib's `ZMod.stdAddChar` ($j\mapsto\exp(2\pi i\,j/p)$). The maximum in $\|f\|_\infty$ is a `Finset.sup'` over the nonempty type `ZMod p`.
-- source:
--   Nguyen, Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate, arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 7, p.12 (PDF 14); §2.4, p.12

import Mathlib

namespace ShamirLeak

/-- The **character** `χ_a(x) = e_p(a x)` with `e_p(t) = exp(2πi t/p)` (Definition 7, p.12 (PDF p.14)).
H. H. Nguyen, *Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate*,
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 7, p.12 (PDF p.14).

**Formalization Note.** `e_p` is Mathlib's `ZMod.stdAddChar`, whose value at `j` is
`exp(2πi · j.val / p)`. -/
noncomputable def chi {p : ℕ} [NeZero p] (a x : ZMod p) : ℂ :=
  ZMod.stdAddChar (a * x)

/-- The vector character `χ_y(x) = e_p(∑ᵢ yᵢ xᵢ)` on `𝔽_p^n` (Definition 7, p.12 (PDF p.14)).
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Definition 7, p.12. -/
noncomputable def chiVec {p n : ℕ} [NeZero p] (y x : Fin n → ZMod p) : ℂ :=
  ZMod.stdAddChar (∑ i, y i * x i)

/-- The norm `‖f‖_2 = (E_x |f(x)|²)^{1/2}` of `f : 𝔽_p → ℂ` under the uniform measure (§2.4, p.12
(PDF p.14)).
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), §2.4, p.12. -/
noncomputable def l2Norm {p : ℕ} [NeZero p] (f : ZMod p → ℂ) : ℝ :=
  Real.sqrt ((∑ x : ZMod p, ‖f x‖ ^ 2) / (p : ℝ))

/-- The supremum norm `‖f‖_∞ = max_x |f(x)|` of `f : 𝔽_p → ℂ` (§2.4, p.12 (PDF p.14)).
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), §2.4, p.12.

**Formalization Note.** A `Finset.sup'` over the nonempty finite type `ZMod p`, so a true
maximum. -/
noncomputable def supNorm {p : ℕ} [NeZero p] (f : ZMod p → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => ‖f x‖)

end ShamirLeak


