-- Prove2me | Definitions.Def_AffinePSD_Existence_Regularization
-- name    : AffinePSD_Existence_Regularization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:41.241196+00:00
-- url     : https://prove2.me/theorems/9b752363-f6e6-4dcd-94c6-a22d45a2ac0f
-- title:
--   The regularized operators A^{ε,δ,n} of §5.2: cut-offs ϕ_n, η_ε, s_{ε,n}, σ^{kl}_{ε,n} and (5.10)
-- statement:
--   Fix $\varepsilon,\delta>0$ and $n\in\mathbb N$, and let $\Sigma\in M_d$. Let $\phi_n$ and $\eta_\varepsilon$ be smooth functions on $S_d$, bounded with all derivatives bounded, such that
--   $$0\le\phi_n\le1,\quad\phi_n(x)=1\ (\|x\|\le n),\quad\phi_n(x)=\frac{n}{\|x\|}\ (\|x\|\ge n+1);\tag{5.4}$$
--   $$\eta_\varepsilon(x)=1\ (x\in S_d^+),\qquad\eta_\varepsilon(x)=0\ (x\notin S_d^+-\varepsilon I_d).$$
--   Put
--   $$s_{\varepsilon,n}(x)=\eta_\varepsilon(\phi_n(x)x)\big(\sqrt{\phi_n(x)x+\varepsilon I_d}-\sqrt\varepsilon I_d\big)\ \text{ if }\phi_n(x)x\in S_d^+-\varepsilon I_d,\quad0\text{ otherwise},\tag{5.7}$$
--   $$\sigma^{kl}_{\varepsilon,n}(x)=s_{\varepsilon,n}(x)M^{kl}\Sigma+\Sigma^\top M^{lk}s_{\varepsilon,n}(x),\qquad M^{kl}_{ij}=\delta_{ik}\delta_{jl}.\tag{5.8}$$
--   With $A^{\varepsilon,n}_{ijkl}(x)=(s^2_{\varepsilon,n}(x))_{ik}\alpha_{jl}+(s^2_{\varepsilon,n}(x))_{il}\alpha_{jk}+(s^2_{\varepsilon,n}(x))_{jk}\alpha_{il}+(s^2_{\varepsilon,n}(x))_{jl}\alpha_{ik}$ (5.9), $B^n(x)=B(\phi_n(x)x)$, $m^\delta(d\xi)=m(d\xi)1_{\{\|\xi\|>\delta\}}$ and $M^{\delta,n}(x,d\xi)=\langle\phi_n(x)x,\mu(d\xi)\rangle(\|\xi\|^2\wedge1)^{-1}1_{\{\|\xi\|>\delta\}}$, the regularized operator is
--   $$\mathcal A^{\varepsilon,\delta,n}f(x)=\frac12\sum A^{\varepsilon,n}_{ijkl}(x)\frac{\partial^2f}{\partial x_{ij}\partial x_{kl}}+\sum(b_{ij}+B^n_{ij}(x))\frac{\partial f}{\partial x_{ij}}+\int(f(x+\xi)-f(x))\,m^\delta(d\xi)+\int(f(x+\xi)-f(x)-\langle\chi(\xi),\nabla f(x)\rangle)\,M^{\delta,n}(x,d\xi).\tag{5.10}$$
--   The predicate `RegIntegrable` states that both integrands of (5.10) are integrable for every Schwartz $f$ and every $x\in S_d$.
--
--   These bounded, smooth approximations of the operator (2.12) are the first step of the existence proof.
--
--   **Formalization Note** $\sqrt{\cdot}$ is the positive semidefinite square root, computed by the continuous functional calculus of a symmetric matrix. $I_d$ is written out as the identity matrix, because `1` in the function type is the all-ones matrix. $\phi_n,\eta_\varepsilon$ are functions on $M_d$, with the listed values required on $S_d$. $s_{\varepsilon,n}$ is evaluated at $\operatorname{sym}(x)$, so on $S_d$ it is the page's map. The page writes the case condition of (5.7) as "$x\in S_d^+-\varepsilon I_d$". Read literally, that makes $s_{\varepsilon,n}$ discontinuous: take $x=\operatorname{diag}(-\varepsilon,100)$ with $\|x\|>n$; then $\phi_n(x)x$ lies inside $S_d^+-\varepsilon I_d$, where $\eta_\varepsilon$ may be nonzero. That contradicts the page's own next line, $s_{\varepsilon,n}\in C_b^\infty(S_d,S_d)$. The condition is therefore tested on $\phi_n(x)x$, the argument of $\eta_\varepsilon$ and of the square root. On $S_d^+$ and near $\partial S_d^+$ the two readings agree. For $x\notin S_d^+$ the kernel $M^{\delta,n}(x,\cdot)$ is a signed measure, so its integral is written against $\nu$ with the signed density $\langle\phi_n(x)x,H(\xi)\rangle/(\|\xi\|^2\wedge1)$. The second form of (5.9) is used; the paper shows it equals $\sum_{m,n}(\sigma^{mn}_{\varepsilon,n})_{ij}(\sigma^{mn}_{\varepsilon,n})_{kl}$ when $\Sigma^\top\Sigma=\alpha$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §5.2, (5.4)–(5.10), pp. 41–43

import Mathlib
import Definitions.Def_AffinePSD_Existence_Params
import Definitions.Def_AffinePSD_Existence_Generator

open MeasureTheory
open scoped SchwartzMap

namespace AffinePSD.Existence

/-- The identity matrix `I_d`. Formalization Note: in the Pi type `Mat d` the literal `1` is the
all-ones matrix, so the identity is written out. -/
def Idm (d : ℕ) : Mat d := fun i j => if i = j then 1 else 0

/-- The positive semidefinite square root `√x` of a symmetric matrix, via the continuous
functional calculus of a Hermitian matrix applied to `Real.sqrt` (junk `0` off `S_d`). On `S_d^+`
it is the unique PSD square root. -/
noncomputable def msqrt {d : ℕ} (x : Mat d) : Mat d :=
  if h : (Matrix.of x).IsHermitian then Matrix.of.symm (h.cfc Real.sqrt) else 0

/-- `C_b^∞`: smooth, with the function and every derivative bounded. -/
def IsCbInf {d : ℕ} (f : Mat d → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
    ∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C

/-- A cut-off `ϕ_n` as in (5.4) (arXiv:0910.0137v3, §5.2, p. 41): `ϕ_n ∈ C_b^∞`, `0 ≤ ϕ_n ≤ 1`,
`ϕ_n(x) = 1` for `‖x‖ ≤ n` and `ϕ_n(x) = n/‖x‖` for `‖x‖ ≥ n + 1`.
Formalization Note: `ϕ_n` is a function on `M_d` (every `C_b^∞(S_d)` function extends to one, by
composing with `x ↦ (x + x^⊤)/2`); the listed values are required on `S_d`. -/
def IsPhiN {d : ℕ} (n : ℕ) (ϕ : Mat d → ℝ) : Prop :=
  IsCbInf ϕ ∧ (∀ x, 0 ≤ ϕ x ∧ ϕ x ≤ 1) ∧
  (∀ x, IsSym x → fnorm x ≤ n → ϕ x = 1) ∧
  (∀ x, IsSym x → (n : ℝ) + 1 ≤ fnorm x → ϕ x = n / fnorm x)

/-- A cut-off `η_ε` as in §5.2 (arXiv:0910.0137v3, p. 42): `η_ε ∈ C_b^∞`, `η_ε(x) = 1` for
`x ∈ S_d^+` and `η_ε(x) = 0` for `x ∈ S_d` with `x ∉ S_d^+ − εI_d`. -/
def IsEtaEps {d : ℕ} (ε : ℝ) (η : Mat d → ℝ) : Prop :=
  IsCbInf η ∧ (∀ x, PSD x → η x = 1) ∧
  (∀ x, IsSym x → ¬ PSD (x + ε • Idm d) → η x = 0)

open Classical in
/-- `s_{ε,n}` of (5.7) (arXiv:0910.0137v3, p. 42):
`s_{ε,n}(x) = η_ε(ϕ_n(x)x)(√(ϕ_n(x)x + εI_d) − √ε I_d)` if `ϕ_n(x)x ∈ S_d^+ − εI_d`, and `0`
otherwise.
Formalization Note: the page writes the case condition as `x ∈ S_d^+ − εI_d`. Read literally,
that makes `s_{ε,n}` discontinuous wherever `ϕ_n(x) < 1` and the smallest eigenvalue of `x` is
`−ε` (for instance `x = diag(−ε, 100)` with `‖x‖ > n`, where `ϕ_n(x)x` lies inside
`S_d^+ − εI_d` and `η_ε(ϕ_n(x)x)` may be nonzero). That contradicts the page's next line,
`s_{ε,n} ∈ C_b^∞(S_d, S_d)`. The condition is therefore tested on `ϕ_n(x)x`, the argument of `η_ε`
and of the square root. The map is unchanged on `S_d^+` and near `∂S_d^+`. The map is evaluated at
`y = (x + x^⊤)/2`, so that on `S_d` it is the page's map and on `M_d` it is that map composed with
the symmetrization (derivatives in symmetric directions are the page's derivatives on `S_d`). -/
noncomputable def sReg {d : ℕ} (ϕ η : Mat d → ℝ) (ε : ℝ) (x : Mat d) : Mat d :=
  if PSD (ϕ (sym x) • sym x + ε • Idm d) then
    η (ϕ (sym x) • sym x) • (msqrt (ϕ (sym x) • sym x + ε • Idm d) - Real.sqrt ε • Idm d)
  else 0

/-- `σ^{kl}_{ε,n}(x) = s_{ε,n}(x) M^{kl} Σ + Σ^⊤ M^{lk} s_{ε,n}(x)` (5.8), with
`M^{kl}_{ij} = δ_{ik}δ_{jl}` (arXiv:0910.0137v3, p. 43). -/
noncomputable def sigmaReg {d : ℕ} (ϕ η : Mat d → ℝ) (ε : ℝ) (Sg : Mat d) (k l : Fin d)
    (x : Mat d) : Mat d :=
  mmul (mmul (sReg ϕ η ε x) (E k l)) Sg + mmul (mmul (transpose Sg) (E l k)) (sReg ϕ η ε x)

/-- The regularized operator `A^{ε,δ,n}` of (5.10) (arXiv:0910.0137v3, p. 43), applied to a
Schwartz function `F` on `M_d`, at `x ∈ S_d`:
`½ Σ A^{ε,n}_{ijkl}(x) ∂²F/∂x_{ij}∂x_{kl} + Σ (b_{ij} + B^n_{ij}(x)) ∂F/∂x_{ij}
 + ∫ (F(x+ξ) − F(x)) m^δ(dξ) + ∫ (F(x+ξ) − F(x) − ⟨χ(ξ), ∇F(x)⟩) M^{δ,n}(x, dξ)`, with
`A^{ε,n}_{ijkl}` the second form of (5.9) (`A_{ijkl}` of (2.13) at `s²_{ε,n}(x)`),
`B^n(x) = B(ϕ_n(x)x)`, `m^δ = m 1_{‖ξ‖>δ}` and
`M^{δ,n}(x, dξ) = ⟨ϕ_n(x)x, μ(dξ)⟩/(‖ξ‖² ∧ 1) 1_{‖ξ‖>δ}`.
Formalization Note: `M^{δ,n}(x, ·)` is a signed measure for `x ∉ S_d^+`, so its integral is
written as `∫_{‖ξ‖>δ} (…) ⟨ϕ_n(x)x, H(ξ)⟩/(‖ξ‖² ∧ 1) ν(dξ)` through the encoding `μ = H ν`;
on `S_d^+` it is the integral against `Mker P (ϕ_n(x)x)` restricted to `{‖ξ‖ > δ}`. The first form
of (5.9), `Σ_{m,n} σ^{mn}_{ij} σ^{mn}_{kl}`, equals the second for `Σ^⊤Σ = α`. -/
noncomputable def Areg {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d) (ϕ η : Mat d → ℝ) (ε δ : ℝ)
    (F : 𝓢(Mat d, ℝ)) (x : Mat d) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k, ∑ l,
      AffinePSD.Necessity.Acoef P (mmul (sReg ϕ η ε x) (sReg ϕ η ε x)) i j k l * AffinePSD.Necessity.D2 F x i j k l +
  ∑ i, ∑ j, (P.b i j + AffinePSD.Necessity.Bmap P (ϕ x • x) i j) * AffinePSD.Necessity.D1 F x i j +
  ∫ ξ in {ξ : Cone d | δ < fnorm (ξ : Mat d)}, (F (x + (ξ : Mat d)) - F x) ∂P.m +
  ∫ ξ in {ξ : Cone d | δ < fnorm (ξ : Mat d)},
    (F (x + (ξ : Mat d)) - F x - tr (χ.χ ξ) (AffinePSD.Necessity.grad F x)) *
      (tr (ϕ x • x) (P.H ξ) / min (fnorm (ξ : Mat d) ^ 2) 1) ∂P.ν

/-- The two integrands of (5.10) are integrable for every Schwartz `F` and every `x ∈ S_d`:
`ξ ↦ F(x+ξ) − F(x)` against `m^δ` and `ξ ↦ F(x+ξ) − F(x) − ⟨χ(ξ), ∇F(x)⟩` against
`M^{δ,n}(x, ·)` (written through `ν`). Formalization Note: concluded alongside every statement
about `A^{ε,δ,n}`, so that the Bochner integrals in `Areg` are the page's integrals and not Lean's
junk value `0`. -/
def RegIntegrable {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d) (ϕ : Mat d → ℝ) (δ : ℝ) : Prop :=
  ∀ (F : 𝓢(Mat d, ℝ)) (x : Mat d), IsSym x →
    Integrable (fun ξ : Cone d => F (x + (ξ : Mat d)) - F x)
      (P.m.restrict {ξ : Cone d | δ < fnorm (ξ : Mat d)}) ∧
    Integrable (fun ξ : Cone d => (F (x + (ξ : Mat d)) - F x - tr (χ.χ ξ) (AffinePSD.Necessity.grad F x)) *
      (tr (ϕ x • x) (P.H ξ) / min (fnorm (ξ : Mat d) ^ 2) 1))
      (P.ν.restrict {ξ : Cone d | δ < fnorm (ξ : Mat d)})

end AffinePSD.Existence


