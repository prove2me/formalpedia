-- Prove2me | Definitions.Def_TriFormQ_AR
-- name    : TriFormQ_AR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:46.127076+00:00
-- url     : https://prove2.me/theorems/23c45dad-f0a0-4550-9524-ed720236c940
-- title:
--   Analytic rank $\mathrm{AR}(f)$
-- statement:
--   Let $f$ be a trilinear form on $\mathbb F_q^n$, with zero locus $Z_f$. Its **analytic rank** is
--
--   $$\mathrm{AR}(f)=\log_q\frac{q^{2n}}{|Z_f|}=\log_q\frac{1}{\mathrm{bias}(f)},\qquad \mathrm{bias}(f)=\Pr_{u,v}\big[f(u,v,\cdot)\equiv 0\big].$$
--
--   The paper defines $\mathrm{bias}(f)$ as the average of $\chi(f(u,v,w))$ for a nontrivial additive character $\chi$ and notes that it equals the probability above. Since $(0,0)\in Z_f$, $\mathrm{AR}(f)$ is a well-defined nonnegative real number, and $\mathrm{AR}(0)=0$. Analytic rank measures how far $f$ is from vanishing and is equivalent to slice rank up to constants.
--
--   **Formalization Note** Defined in the zero-locus count form $q^{-\mathrm{AR}(f)}=|Z_f|/q^{2n}$ stated in the paper (pp.12–13), with $q=|\mathbb F|$.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Definition 1, p.12 (PDF p.15); §2.2.1, p.13 (PDF p.16)

import Definitions.Def_TriFormQ_zeroLocus

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Definition 1, p.12 (PDF p.15):
the analytic rank `AR(T) = log_{|F|}(1 / bias(T))`, with
`bias(T) = Pr_{v₁, v₂}[T(v₁, v₂, ·) ≡ 0]` ("It is easy to check that, as χ is nontrivial, …"),
and §2.2.1, p.13 (PDF p.16): "q^{−AR(f)} = |Z|/(|U|·|V|) = |Z|/q^{2n}".

**Formalization Note.** Defined in this zero-locus count form,
`AR(f) = log_q(q^{2n} / |Z_f|)` with `q = |F|`, which the paper states equals the character
definition. `Z_f` contains `(0, 0)`, so the denominator is at least 1 and the value is a
nonnegative real; `AR 0 = 0`. -/
noncomputable def AR {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (θ : TriForm F n) : ℝ :=
  Real.logb (Fintype.card F) ((Fintype.card F : ℝ) ^ (2 * n) / (zeroLocus θ).card)

end TriFormQ


