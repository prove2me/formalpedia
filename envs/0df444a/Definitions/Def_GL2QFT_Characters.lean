-- Prove2me | Definitions.Def_GL2QFT_Characters
-- name    : GL2QFT_Characters
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:01.482298+00:00
-- url     : https://prove2.me/theorems/df7aa5e0-bc94-4534-bd27-3108891e1886
-- title:
--   Characters $\chi_\alpha$, $\theta_k$, $\psi$, trace, norm, Gauss sums $g_q$, $g_{q^2}$ and the Jacobi sum
-- statement:
--   The characters and character sums of Appendix A, fixed by the generators of the field data $D$.
--
--   1. For an exponent label $\alpha\in\mathbb Z/(q-1)\mathbb Z$, $\chi_\alpha(g^d)=e^{2\pi i\alpha d/(q-1)}$ on $\mathbb F_q^*$, where $g=h^{q+1}$; for $k\in\mathbb Z/(q^2-1)\mathbb Z$, $\theta_k(h^d)=e^{2\pi i kd/(q^2-1)}$ on $\mathbb F_{q^2}^*$.
--   2. The additive character is $\psi(x)=e^{2\pi i\,\mathrm{tr}^p_q(x)/p}$, with $\mathrm{tr}^p_q$ the absolute trace of $\mathbb F_q$ over $\mathbb F_p$, and $\psi_b(x)=\psi(bx)$.
--   3. $\mathrm{tr}(z)=z+z^q$ and $N(z)=z^{q+1}$ are the trace and norm of $\mathbb F_{q^2}/\mathbb F_q$.
--   4. The Gauss sums (265)–(266) are
--   $$G_q(\alpha,b)=\sum_{x\in\mathbb F_q^*}\chi_\alpha(x)\psi(bx),\qquad g_q(\alpha)=G_q(\alpha,1),\qquad g_{q^2}(\theta)=\sum_{z\in\mathbb F_{q^2}^*}\theta(z)\psi(\mathrm{tr}(z)),$$
--   and the Jacobi sum is $J(\alpha,\beta)=\sum_{x\in\mathbb F_q^*\setminus\{1\}}\chi_\alpha(x)\chi_\beta(1-x)$.
--   5. $\gamma(k)=k\bmod (q-1)$ is the label with $\theta_k|_{\mathbb F_q^*}=\chi_{\gamma(k)}$.
--
--   These are the coefficients of every representation matrix, Fourier transform and A-block of the mission.
--
--   **Formalization Note** Products and inverses of characters are sums and negatives of labels ($\chi_\alpha\chi_\beta=\chi_{\alpha+\beta}$, $\chi_{\alpha^{-1}}=\chi_{-\alpha}$); the trivial character, written "$\alpha=1$" in the paper, is the label $0$. Characters are set to $0$ at $0$; all sums of the paper run over nonzero elements. The discrete logarithms are the least exponents.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Appendix A pp.78–79 (eqs. (263)–(264), character labels), Definition A.3 eqs. (265)–(266) p.79, Lemma A.4 (Jacobi sum) p.79, Definition 6.18 p.49 (θ coordinates), p.36 (θ|F*q = χγ)

import Definitions.Def_GL2QFT_FieldData

noncomputable section

open Classical

namespace GL2QFT

open scoped ComplexConjugate

namespace FieldData

variable (D : FieldData)

/-- The discrete logarithm of `x ∈ F*_q` to the base `g = gen D`: the least `n` with `g^n = x`
(Appendix A, p.79: "`χ_α(g^d)`"). Since `g` generates `F*_q`, this is the exponent `d ∈ [0, q−2]`
of `x`.

**Formalization Note** The value at `x = 0` (no such `n`) is the junk value `0`; every use of
`dlog` below is guarded by `x ≠ 0`. -/
def dlog (x : D.Fq) : ℕ :=
  if hx : ∃ n : ℕ, D.gen ^ n = x then Nat.find hx else 0

/-- The discrete logarithm of `z ∈ F*_{q²}` to the base `h` (Definition 6.18, p.49:
`θ₀(h) = e^{2πik/(q²−1)}`), the least `n` with `h^n = z` (junk value `0` at `z = 0`). -/
def dlog2 (z : D.Fq2) : ℕ :=
  if hz : ∃ n : ℕ, D.h ^ n = z then Nat.find hz else 0

/-- arXiv:2608.28573, Appendix A, p.79 (PDF p.80), Remark 6.2: the multiplicative character of
`F*_q` with exponent label `α`, `χ_α(g^d) = e^{2πiαd/(q−1)}`.

**Formalization Note** The label `α : ZMod (q−1)` is read through its representative
`α.val ∈ [0, q−2]`; the paper's products `χ_α χ_β = χ_{αβ}` and inverses `χ_{α⁻¹}` are the label
sum `α + β` and negation `−α`, and "`α = 1`" (trivial character) is the label `0`. The paper's sums
run over `F*_q`; at `x = 0` the value is set to `0`. -/
def chi (α : D.Lab) (x : D.Fq) : ℂ :=
  if x = 0 then 0
  else Complex.exp (2 * Real.pi * Complex.I * ((α.val * D.dlog x : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ))

/-- arXiv:2608.28573, Appendix A, p.79, and Definition 6.18, p.49: the multiplicative character of
`F*_{q²}` with exponent label `k`, `θ_k(h^d) = e^{2πikd/(q²−1)}` (value `0` at `z = 0`). -/
def theta (k : D.Lab2) (z : D.Fq2) : ℂ :=
  if z = 0 then 0
  else Complex.exp (2 * Real.pi * Complex.I * ((k.val * D.dlog2 z : ℕ) : ℂ) / ((D.q ^ 2 - 1 : ℕ) : ℂ))

/-- arXiv:2608.28573, Appendix A, p.79: the fixed nontrivial additive character
`ψ(x) = ψ₁(x) = e^{2πi tr^p_q(x)/p}` of `F_q`, where `tr^p_q = Algebra.trace F_p F_q` is the
absolute trace (263), read as an integer in `[0, p−1]`. `ψ_b(x) = ψ(bx)`. -/
def psi (x : D.Fq) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℂ) /
    (D.p : ℂ))

/-- arXiv:2608.28573, Appendix A, p.79: the trace `tr(z) = z + z̄` of `F_{q²}/F_q`
(`Algebra.trace F_q F_{q²}`, which equals `z + z^q`). -/
def tr (z : D.Fq2) : D.Fq := Algebra.trace D.Fq D.Fq2 z

/-- arXiv:2608.28573, Appendix A, p.79, (264): the norm `N(z) = z z̄ = z^{q+1}` of `F_{q²}/F_q`
(`Algebra.norm F_q F_{q²}`). -/
def nrm (z : D.Fq2) : D.Fq := Algebra.norm D.Fq z

/-- arXiv:2608.28573, Definition A.3, eq. (265), p.79 (PDF p.80): the Gauss sum
`G_q(α, b) = Σ_{x ∈ F*_q} χ_α(x) ψ(bx)`. -/
def gaussG (α : D.Lab) (b : D.Fq) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.chi α x * D.psi (b * x)

/-- arXiv:2608.28573, Definition A.3, eq. (265): `g_q(α) := G_q(α, 1)`. -/
def gauss (α : D.Lab) : ℂ := D.gaussG α 1

/-- arXiv:2608.28573, Definition A.3, eq. (266), p.79: the Gauss sum of a character `θ` of
`F*_{q²}`, `g_{q²}(θ) = Σ_{z ∈ F*_{q²}} θ(z) ψ(tr(z))`.

**Formalization Note** `θ` is passed as a function `F_{q²} → ℂ`; only its values on `F*_{q²}`
enter. It is applied to `θ_k` and to products such as `θ_k · (χ_α ∘ N)` and `χ_α ∘ N`. -/
def gaussQ2 (θ : D.Fq2 → ℂ) : ℂ :=
  ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), θ z * D.psi (D.tr z)

/-- arXiv:2608.28573, Lemma A.4, p.79: the Jacobi sum
`J(α, β) = Σ_{x ∈ F*_q ∖ {1}} χ_α(x) χ_β(1 − x)`. -/
def jacobi (α β : D.Lab) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0 ∧ x ≠ 1), D.chi α x * D.chi β (1 - x)

/-- The exponent label of `x ∈ F*_q` (`dlog` read in `ZMod (q−1)`): the label `d` with `x = g^d`,
used for the multiplicative register `|x⟩×` (§6.4.1, p.41). -/
def dlogLab (x : D.Fq) : D.Lab := (D.dlog x : D.Lab)

/-- The restriction label `γ(k)` with `θ_k|_{F*_q} = χ_{γ(k)}` (p.36, (99): "Let `γ` satisfy
`θ|_{F*_q} = χ_γ`"): since `g = h^{q+1}`, `θ_k(g^d) = e^{2πik(q+1)d/(q²−1)} = e^{2πikd/(q−1)}`, so
`γ(k) = k mod (q−1)`. -/
def restrLab (k : D.Lab2) : D.Lab := (k.val : D.Lab)

end FieldData

end GL2QFT


