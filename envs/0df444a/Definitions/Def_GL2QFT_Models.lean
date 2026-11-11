-- Prove2me | Definitions.Def_GL2QFT_Models
-- name    : GL2QFT_Models
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:18.268076+00:00
-- url     : https://prove2.me/theorems/3420755a-1185-4912-bb98-489fc80d2d6e
-- title:
--   Explicit models $I_{\alpha,\beta}$, $\rho_\gamma$, $\pi_\theta$ and the Gelfand–Tsetlin basis vectors (108), (110)–(112)
-- statement:
--   The explicit representations of §6.1.1 in their standard bases and the Gelfand–Tsetlin vectors of §6.2.
--
--   1. **Principal series** (94) on $\mathbb C[\mathcal P^1(\mathbb F_q)]$: $I_{\alpha,\beta}(g)|x\rangle=\chi_{\alpha,\beta}(b^g_x)|gx\rangle$, where $\chi_{\alpha,\beta}\begin{pmatrix}a'&b'\\0&d'\end{pmatrix}=\chi_\alpha(a')\chi_\beta(d')$ and $b^g_x$ is given by (92)–(93) for the transversal $t_x=\begin{pmatrix}x&1\\1&0\end{pmatrix}$, $t_\infty=e$.
--   2. **Borel representation** (89) on $\mathbb C[\mathbb F_q^*]$:
--   $$\rho_\gamma\begin{pmatrix}a&b\\0&d\end{pmatrix}|x\rangle=\chi_\gamma(d)\,\psi\!\left(\tfrac{b}{a}x\right)\left|\tfrac{d}{a}x\right\rangle .$$
--   3. **Cuspidal representation** (99)–(100): $\pi_\theta$ equals (89) on $B$ with $\theta|_{\mathbb F_q^*}=\chi_\gamma$, and $\pi_\theta(w')|x\rangle=\theta(x^{-1})\sum_{y\in\mathbb F_q^*}j_\theta(yx)|y\rangle$ with $j_\theta(u)=-\frac1q\sum_{v\in\mathbb F_{q^2}^*,\,N(v)=u}\psi(\mathrm{tr}(v))\theta(v)$. Off $B$ it is computed through $g=\begin{pmatrix}1&a/c\\0&1\end{pmatrix}w'\begin{pmatrix}-c&-d\\0&-\det g/c\end{pmatrix}$.
--   4. **Gelfand–Tsetlin vectors**: $|v_t\rangle=q^{-1/2}\sum_x\overline{\psi(tx)}|x\rangle$; $|w_\delta\rangle=(q-1)^{-1/2}\sum_{t\in\mathbb F_q^*}\chi_\delta(t)\chi_{\beta^{-1}}(t)|v_t\rangle$ (110); $|v_0\rangle$; $|v\rangle=(q+1)^{-1/2}(\chi_\alpha(-1)|\infty\rangle+\sum_x|x\rangle)$ (111); $|v^\perp\rangle=(q+1)^{-1/2}(\sqrt q\,\chi_\alpha(-1)|\infty\rangle-|v_0\rangle)$ (112); and the multiplicative Fourier basis $|w_\delta\rangle=(q-1)^{-1/2}\sum_x\chi_\delta(x)|x\rangle$ (108).
--
--   These are the paper's representatives and bases; the Fourier transform of the mission is taken in them.
--
--   **Formalization Note** $\mathcal P^1(\mathbb F_q)$ is $\mathbb F_q\cup\{\infty\}$. The formulas were read on the rendered page: the fractions in (89) and (99) are $b/a$ and $d/a$ multiplied by $x$, and $|v_t\rangle$ carries a complex conjugation bar (both are garbled by the PDF text layer). The paper specifies $\pi_\theta$ on $B$ and $w'$ only ("Using the Bruhat decomposition (86) we only have to specify…"); the displayed factorization is one way of writing the forced value. Numerical checks at $q=2,3,5,7$ confirm that all models are homomorphisms and all bases orthonormal and adapted.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), §6.1.1 eqs. (87)–(94), (97), (99)–(100), pp.35–36 (PDF pp.36–37); §6.2 eqs. (108), (110)–(112), pp.37–38 (PDF pp.38–39)

import Definitions.Def_GL2QFT_Characters

noncomputable section

open Classical

namespace GL2QFT

open scoped ComplexConjugate

namespace FieldData

variable (D : FieldData)

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), §6.1.1, eqs. (91)–(94), p.35 (PDF p.36):
the principal series `I_{α,β}` in the standard basis of `ℂ[P¹(F_q)]`,
`I_{α,β}(g)|x⟩ = χ_{α,β}(b^g_x)|gx⟩` with `χ_{α,β}((a' b'; 0 d')) = χ_α(a')χ_β(d')` (87) and `b^g_x`
from `g · t_x = t_{gx} · b^g_x` for the transversal `t_x = (x 1; 1 0)`, `t_∞ = e` (91):
for `g = (a b; c d)`,
* `x ∈ F_q`, `cx + d ≠ 0`: `gx = (ax+b)/(cx+d)`, `b^g_x = (cx+d, c; 0, det g/(cx+d))` (92);
* `x ∈ F_q`, `cx + d = 0`: `gx = ∞`, `b^g_x = (ax+b, a; 0, c)` (92);
* `x = ∞`, `c ≠ 0`: `g∞ = a/c`, `b^g_∞ = (c, d; 0, −det g/c)` (93);
* `x = ∞`, `c = 0`: `g∞ = ∞`, `b^g_∞ = g` (93).

The matrix entry in row `y`, column `x` is `χ_{α,β}(b^g_x)` if `y = gx` and `0` otherwise.

**Formalization Note** `P¹(F_q) = Option F_q` with `none = ∞`. The argument is the matrix `M` of
`g` (entries `M 0 0 = a`, `M 0 1 = b`, `M 1 0 = c`, `M 1 1 = d`); it is a representation on
invertible `M`. -/
def psModel (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq) :
    Matrix (Option D.Fq) (Option D.Fq) ℂ :=
  let a := M 0 0; let b := M 0 1; let c := M 1 0; let d := M 1 1
  let det := a * d - b * c
  fun y x =>
    match x with
    | none =>
      if c ≠ 0 then (if y = some (a / c) then D.chi α c * D.chi β (-det / c) else 0)
      else (if y = none then D.chi α a * D.chi β d else 0)
    | some x =>
      if c * x + d ≠ 0 then
        (if y = some ((a * x + b) / (c * x + d)) then
          D.chi α (c * x + d) * D.chi β (det / (c * x + d)) else 0)
      else (if y = none then D.chi α (a * x + b) * D.chi β c else 0)

/-- arXiv:2608.28573, §6.1.1, eq. (89), p.35: the `(q−1)`-dimensional representation `ρ_γ` of `B`
in the standard basis of `ℂ[F*_q]`, `ρ_γ(a b; 0 d)|x⟩ = χ_γ(d) ψ((b/a)x) |(d/a)x⟩` (read on the
rendered page: the fractions are `b/a` and `d/a`, multiplied by `x`). The arguments are the entries
`a, b, d` of the upper triangular matrix; the matrix entry in row `y`, column `x` is
`χ_γ(d)ψ((b/a)x)` if `y = (d/a)x` and `0` otherwise. The same formula is the restriction (99) of the
cuspidal representation to `B`. -/
def borelModel (γ : D.Lab) (a b d : D.Fq) : Matrix D.Fqˣ D.Fqˣ ℂ :=
  fun y x => if (y : D.Fq) = d / a * x then D.chi γ d * D.psi (b / a * x) else 0

/-- arXiv:2608.28573, eq. (100), p.36: the Bessel function
`j_θ(u) = −(1/q) Σ_{v ∈ F*_{q²}, N(v) = u} ψ(tr(v)) θ(v)` for `θ = θ_k`. -/
def besselJ (k : D.Lab2) (u : D.Fq) : ℂ :=
  -((D.q : ℂ)⁻¹) *
    ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = u), D.psi (D.tr v) * D.theta k v

/-- arXiv:2608.28573, eq. (100), p.36: the cuspidal representation at `w′ = (0 1; −1 0)` in the
standard basis of `ℂ[F*_q]`, `π_θ(w′)|x⟩ = θ(x⁻¹) Σ_{y ∈ F*_q} j_θ(yx)|y⟩`; the matrix entry in row
`y`, column `x` is `θ(x⁻¹) j_θ(yx)` (`x⁻¹ ∈ F*_q ⊂ F*_{q²}`). -/
def wprimeModel (k : D.Lab2) : Matrix D.Fqˣ D.Fqˣ ℂ :=
  fun y x => D.theta k (algebraMap D.Fq D.Fq2 ((x : D.Fq)⁻¹)) * D.besselJ k ((y : D.Fq) * x)

/-- arXiv:2608.28573, eqs. (99)–(100), p.36: the cuspidal representation `π_θ`, `θ = θ_k`, on
`ℂ[F*_q]`, with `γ = γ(k)` (`θ|_{F*_q} = χ_γ`). On `B` (`c = 0`) it is (99), the formula of
`borelModel`. For `c ≠ 0` it is extended through the Bruhat factorization
`(a b; c d) = (1 a/c; 0 1) · w′ · (−c −d; 0 −det/c)`, i.e.
`π_θ(g) = π_θ(1 a/c; 0 1) π_θ(w′) π_θ(−c −d; 0 −det/c)`.

**Formalization Note** The paper says only "Using the Bruhat decomposition (86) we only have to
specify the cuspidal representation on `B` and the element `w′`"; for a representation the value
on `g` is forced by these, and the displayed factorization is one valid way to write it
(the numerics in `numerics/` confirm the homomorphism property). -/
def piModel (k : D.Lab2) (M : Matrix (Fin 2) (Fin 2) D.Fq) : Matrix D.Fqˣ D.Fqˣ ℂ :=
  let a := M 0 0; let b := M 0 1; let c := M 1 0; let d := M 1 1
  let γ := D.restrLab k
  if c = 0 then D.borelModel γ a b d
  else D.borelModel γ 1 (a / c) 1 * D.wprimeModel k * D.borelModel γ (-c) (-d) (-(a * d - b * c) / c)

/-! ### Gelfand–Tsetlin basis vectors (§6.2, pp.37–39) -/

/-- `(√x)⁻¹` as a complex number. -/
def isqrt (x : ℝ) : ℂ := ((Real.sqrt x)⁻¹ : ℝ)

/-- arXiv:2608.28573, §6.2.2, p.38: the additive (inverse) Fourier vector
`|v_t⟩ = q^{−1/2} Σ_{x ∈ F_q} conj(ψ(tx)) |x⟩` of `ℂ[P¹(F_q)]` (no `|∞⟩` component). The complex
conjugation bar is on the rendered page (it is dropped by the PDF text layer). -/
def vT (t : D.Fq) : Option D.Fq → ℂ :=
  fun y => match y with
    | none => 0
    | some x => isqrt D.q * conj (D.psi (t * x))

/-- arXiv:2608.28573, eq. (110), p.38: the vector
`|w_δ⟩ = (q−1)^{−1/2} Σ_{t ∈ F*_q} χ_δ(t) χ_{β⁻¹}(t) |v_t⟩` of the Gelfand–Tsetlin basis of `I_{α,β}`
(and, with `β = α`, of `St_α`, (112)). -/
def wVec (β δ : D.Lab) : Option D.Fq → ℂ :=
  fun y => isqrt (D.q - 1) *
    ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0), D.chi δ t * D.chi (-β) t * D.vT t y

/-- arXiv:2608.28573, eq. (110), p.38: the Gelfand–Tsetlin basis `{|∞⟩, |v₀⟩, |w_δ⟩ : δ ∈ F*_q}` of
the principal series `I_{α,β}` (it depends on `β` only), with `|v₀⟩ = q^{−1/2} Σ_{x∈F_q} |x⟩`.

**Formalization Note** The index type is `Option (Option Lab)`: `none = |∞⟩`, `some none = |v₀⟩`,
`some (some δ) = |w_δ⟩` (δ an exponent label, `X_q ≅ F*_q`, Remark 6.2). -/
def psVec (β : D.Lab) : Option (Option D.Lab) → Option D.Fq → ℂ
  | none => fun y => if y = none then 1 else 0
  | some none => fun y => match y with
    | none => 0
    | some _ => isqrt D.q
  | some (some δ) => D.wVec β δ

/-- arXiv:2608.28573, eqs. (97), (111), p.36 and p.38: the vector
`|v⟩ = (q+1)^{−1/2} (χ_α(−1)|∞⟩ + Σ_{x ∈ F_q} |x⟩)` spanning `det_α` inside `I_{α,α}`. -/
def detVec (α : D.Lab) : Option D.Fq → ℂ :=
  fun y => isqrt (D.q + 1) * (match y with
    | none => D.chi α (-1)
    | some _ => 1)

/-- arXiv:2608.28573, eq. (112), p.38: the Gelfand–Tsetlin basis of the Steinberg representation
`St_α ⊂ I_{α,α}`: `|v^⊥⟩ = (q+1)^{−1/2} (√q χ_α(−1)|∞⟩ − |v₀⟩)` and `|w_δ⟩` (110) with `β = α`,
`δ ∈ F*_q`.

**Formalization Note** Index type `Option Lab`: `none = |v^⊥⟩`, `some δ = |w_δ⟩`. -/
def stVec (α : D.Lab) : Option D.Lab → Option D.Fq → ℂ
  | none => fun y => isqrt (D.q + 1) * (match y with
    | none => (Real.sqrt D.q : ℂ) * D.chi α (-1)
    | some _ => -(isqrt D.q))
  | some δ => D.wVec α δ

/-- arXiv:2608.28573, eq. (108), p.37: the multiplicative Fourier basis
`|w_δ⟩ = (q−1)^{−1/2} Σ_{x ∈ F*_q} χ_δ(x)|x⟩` of `ℂ[F*_q]`, the Gelfand–Tsetlin basis of `ρ_γ` and
of `π_θ` (p.39). -/
def multVec (δ : D.Lab) : D.Fqˣ → ℂ :=
  fun x => isqrt (D.q - 1) * D.chi δ (x : D.Fq)

end FieldData

end GL2QFT


