-- Prove2me | Definitions.Def_MKVDPP_Weak_Canonical
-- name    : MKVDPP_Weak_Canonical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T13:27:58.283979+00:00
-- url     : https://prove2.me/theorems/03eecebb-e513-401f-9663-c744638a0f8b
-- title:
--   §4.1 — the canonical space Ω̄, the generator, weak control rules (Def. 4.1), 𝒫̂_W, 𝒫̄_W, J(t,ℙ̄), and the truncated sets of p. 20
-- statement:
--   This file formalizes the canonical reformulation of §4.1 and the truncated sets of p. 20 of Djete, Possamaï and Tan.
--
--   Let $\hat\Omega:=\mathcal C^n\times\mathcal C\times\mathcal C^d\times\mathcal C^\ell$ and $\bar\Omega:=\hat\Omega\times C([0,T],\mathcal P(\hat\Omega))$ with canonical process $(X,A,W,B,\hat\mu)$, natural filtration $\bar{\mathbb F}$ and Borel $\sigma$-field. Put $\bar\alpha_s:=\pi^{-1}\big(\limsup_{n\to\infty}n(A_s-A_{0\vee(s-1/n)})\big)$, $\bar\mu_s:=\hat\mu_s\circ(\hat X_{s\wedge\cdot},\hat\alpha_s)^{-1}$, $\mu_s:=\hat\mu_s\circ(\hat X_{s\wedge\cdot})^{-1}$, $B^t_s:=B_{s\vee t}-B_t$, and let $\bar{\mathbb G}^t$ be trivial before $t$ and $\bar{\mathcal G}^t_s:=\sigma((B^t_r,\hat\mu_r):r\le s)$ for $s\ge t$ (4.1).
--
--   For $\varphi\in C^2_b(\mathbb R^n\times\mathbb R^d\times\mathbb R^\ell)$ the generator is
--   $$\mathcal L_s\varphi=\sum_i\bar b_i\,\partial_i\varphi+\tfrac12\sum_{i,j}\bar a_{ij}\,\partial^2_{ij}\varphi,\qquad \bar b=(b,0_d,0_\ell),\quad \bar a=CC^\top,\ C=\begin{pmatrix}\sigma&\sigma_0\\ I_d&0\\ 0&I_\ell\end{pmatrix},$$
--   evaluated at $(X_s,W_s,B_s)$. For a rule with initial time $t$, let $|\bar S|_s:=\int_t^s(|\bar b|+|\bar a|)\,dr$, $\bar S^\varphi_s:=\varphi(X_s,W_s,B_s)-\int_t^s\mathcal L_r\varphi\,dr$ for $s\ge t$, $\tau_m:=\inf\{s:|\bar S|_s\ge m\}$ and $S^{\varphi,m}_s:=\bar S^\varphi_{s\wedge\tau_m}$ (4.4)–(4.5).
--
--   A probability $\bar{\mathbb P}$ on $\bar\Omega$ is a **weak control rule** with initial condition $(t,\hat\nu)$ (Definition 4.1) if
--   1. $\bar{\mathbb P}[\bar\alpha_s\in U]=1$ for a.e. $s\in[t,T]$ and $\mathbb E[\int_t^T\rho(u_0,\bar\alpha_s)^p\,ds]<\infty$;
--   2. $\hat\mu_s=\bar{\mathbb P}\circ(X_{s\wedge\cdot},A_{s\wedge\cdot},W,B_{s\wedge\cdot})^{-1}$ for $s\le t$ and $\hat\mu_s=\bar{\mathbb P}^{\bar{\mathcal G}^t_T}\circ(X_{s\wedge\cdot},A_{s\wedge\cdot},W,B_{s\wedge\cdot})^{-1}$ for $s\in(t,T]$, a.s. (4.6), with $\bar{\mathbb P}\circ(X_{t\wedge\cdot},A_{t\wedge\cdot},W_{t\wedge\cdot},B_{t\wedge\cdot})^{-1}=\hat\nu(t)$;
--   3. $\mathbb E[\|X\|^p]<\infty$, $|\bar S|_T<\infty$ a.s., and $\bar S^\varphi$ is an $(\bar{\mathbb F},\bar{\mathbb P})$-local martingale on $[t,T]$ for every $\varphi\in C^2_b$.
--
--   Then $\hat{\mathcal P}_W(t,\hat\nu)$ is the set of these rules, $\bar{\mathcal P}_W(t,\nu):=\bigcup_{\hat\nu\circ\hat X^{-1}=\nu}\hat{\mathcal P}_W(t,\hat\nu)$, and
--   $$J(t,\bar{\mathbb P}):=\mathbb E^{\bar{\mathbb P}}\Big[\int_t^T L(s,X,\bar\mu_s,\bar\alpha_s)\,ds+g(X,\mu_T)\Big].$$
--   For $M\ge0$, $\bar{\mathcal P}^M_t$ is the set of $\bar{\mathbb P}$ with $\mathbb E[\|X\|^p]+\mathbb E[\int_t^T\rho(u_0,\bar\alpha_s)^p\,ds]\le M$, $\bar{\mathcal P}^M_W(t,\nu):=\bar{\mathcal P}_W(t,\nu)\cap\bar{\mathcal P}^M_t$, $\hat{\mathcal P}^M_W(t,\hat\nu):=\hat{\mathcal P}_W(t,\hat\nu)\cap\bar{\mathcal P}^M_t$ and $V^M_W(t,\nu):=\sup_{\bar{\mathbb P}\in\bar{\mathcal P}^M_W(t,\nu)}J(t,\bar{\mathbb P})$. The graph sets $[\![\hat{\mathcal P}_W]\!]$, $[\![\bar{\mathcal P}_W]\!]$ and $\{(t,\nu,M,\bar{\mathbb P}):\bar{\mathbb P}\in\bar{\mathcal P}^M_W(t,\nu)\}$ are also defined.
--
--   These objects are where the measurable-selection argument behind the dynamic programming principle takes place.
--
--   **Formalization Note** (a) The local martingale property is pinned to: for every $m\ge1$, $S^{\varphi,m}$ is an integrable $(\bar{\mathbb F},\bar{\mathbb P})$-martingale on $[t,T]$; the integral in $S^{\varphi,m}$ is the real (Bochner) integral, finite up to $\tau_m$. (b) Where $\bar\alpha_s=\partial$ the coefficients are evaluated at $u_0$, and $\bar\mu_s$ is the image of $\hat\mu_s$ under $(\hat X_{s\wedge\cdot},\hat\alpha_s)$ with $\partial$ read as $u_0$; under condition 1 this affects only a $d\bar{\mathbb P}\otimes ds$-null set. (c) $|\bar a|$ is the Frobenius norm and $\sum_{ij}\bar a_{ij}\partial^2_{ij}\varphi$ is written as $\sum_kD^2\varphi(c_k,c_k)$ over the columns $c_k$ of $C$. (d) $M$ ranges over $[0,\infty)$; the page writes $M>0$ in the definition and $M\ge0$, $\mathbb R_+$ in Lemma 4.10. (e) The page integrates $|\bar S|$ and $\bar S^\varphi$ from $0$. Here they start at the initial time $t$. Before $t$ the control $\bar\alpha$ may be the cemetery point $\partial$, where the coefficients are undefined, and a coefficient that is not integrable on $[0,t)$ would make $\hat{\mathcal P}_W(t,\cdot)$ empty while $\Gamma_W(t,\cdot)$ is not, contradicting Corollary 4.6. The proof of Lemma 4.4 (p. 17) obtains $|\bar S|_T<\infty$ from the integrals of (2.4), which run over $[t,T]$. On $[t,T]$ the two versions of $\bar S^\varphi$ differ by the $\bar{\mathcal F}_t$-measurable quantity $\int_0^t\mathcal L_r\varphi\,dr$, so the local martingale property is the same.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, pp. 15–16 and 20, §4.1.1–4.1.2, (4.1)–(4.6), Definition 4.1, (4.9), definitions of 𝒫̄^M_t and V^M_W

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_completedSDEPast
import Definitions.Def_MKVDPP_Weak_Setting
import Definitions.Def_MKVDPP_Weak_WeakControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MKVDPP.Weak

noncomputable section

/-! ## The second canonical space `Ω̄` (§4.1.1, p. 15) -/

/-- `Ω̄ := Ω̂ × C([0,T], 𝒫(Ω̂))`, with the product topology (uniform topology on the path factor)
and its Borel σ-field `ℱ̄ := 𝓑(Ω̄)`. -/
def OmegaBar (T : ℝ≥0) (n d ℓ : ℕ) : Type :=
  OmegaHat T n d ℓ × C(Set.Icc (0:ℝ) (T:ℝ), ProbabilityMeasure (OmegaHat T n d ℓ))

variable {T : ℝ≥0} {n d ℓ : ℕ}

instance : TopologicalSpace (OmegaBar T n d ℓ) :=
  inferInstanceAs (TopologicalSpace (OmegaHat T n d ℓ ×
    C(Set.Icc (0:ℝ) (T:ℝ), ProbabilityMeasure (OmegaHat T n d ℓ))))

instance : MeasurableSpace (OmegaBar T n d ℓ) := borel _

instance : BorelSpace (OmegaBar T n d ℓ) := ⟨rfl⟩

/-- The `Ω̂`-component `(X, A, W, B)` of `ω̄ ∈ Ω̄`. -/
def hatOf (ω : OmegaBar T n d ℓ) : OmegaHat T n d ℓ :=
  (ω : OmegaHat T n d ℓ × C(Set.Icc (0:ℝ) (T:ℝ), ProbabilityMeasure (OmegaHat T n d ℓ))).1

/-- The canonical measure-valued path `μ̂` of `ω̄ ∈ Ω̄`. -/
def muHatOf (ω : OmegaBar T n d ℓ) : C(Set.Icc (0:ℝ) (T:ℝ), ProbabilityMeasure (OmegaHat T n d ℓ)) :=
  (ω : OmegaHat T n d ℓ × C(Set.Icc (0:ℝ) (T:ℝ), ProbabilityMeasure (OmegaHat T n d ℓ))).2

/-- Builds `ω̄ = (ω̂, m)`. -/
def mkBar (z : OmegaHat T n d ℓ)
    (m : C(Set.Icc (0:ℝ) (T:ℝ), ProbabilityMeasure (OmegaHat T n d ℓ))) : OmegaBar T n d ℓ :=
  ((z, m) : OmegaHat T n d ℓ × C(Set.Icc (0:ℝ) (T:ℝ), ProbabilityMeasure (OmegaHat T n d ℓ)))

theorem measurable_hatOf : Measurable (hatOf (T := T) (n := n) (d := d) (ℓ := ℓ)) := by
  have h : Continuous (hatOf (T := T) (n := n) (d := d) (ℓ := ℓ)) := continuous_fst
  exact h.measurable

theorem measurable_muHatOf : Measurable (muHatOf (T := T) (n := n) (d := d) (ℓ := ℓ)) := by
  have h : Continuous (muHatOf (T := T) (n := n) (d := d) (ℓ := ℓ)) := continuous_snd
  exact h.measurable

/-- Canonical processes `X, A, W, B` on `Ω̄` (as paths). -/
def Xc (ω : OmegaBar T n d ℓ) : Cpath T n := (hatOf ω).1
def Ac (ω : OmegaBar T n d ℓ) : CR T := (hatOf ω).2.1
def Wc (ω : OmegaBar T n d ℓ) : Cpath T d := (hatOf ω).2.2.1
def Bc (ω : OmegaBar T n d ℓ) : Cpath T ℓ := (hatOf ω).2.2.2

/-! ## The control read off the `A` coordinate -/

/-- `lim̄_{k→∞} k (a_s − a_{0∨(s−1/k)})`, computed in `EReal`. -/
def limRate (a : CR T) (s : ℝ≥0) : EReal :=
  Filter.limsup (fun k : ℕ => (((k:ℝ) * (pathAt a s - pathAt a (s - 1 / (k:ℝ≥0))) : ℝ) : EReal))
    atTop

theorem measurable_limRate (s : ℝ≥0) : Measurable (fun a : CR T => limRate a s) := by
  unfold limRate
  refine Measurable.limsup fun k => ?_
  refine measurable_coe_real_ereal.comp ?_
  refine measurable_const.mul ?_
  exact ((continuous_eval_const _).measurable).sub (continuous_eval_const _).measurable

variable {U : Type*} [MetricSpace U] [MeasurableSpace U] [BorelSpace U]

/-- `α̂_s = π⁻¹(lim̄ k(Â_s − Â_{0∨(s−1/k)}))` on `Ω̂`, with the cemetery `∂` read as `u₀`
(the `U`-valued reading used inside the coefficients). -/
def alphaHatU (π : U → ℝ) (u₀ : U) (s : ℝ≥0) (z : OmegaHat T n d ℓ) : U :=
  πinvU π u₀ (limRate z.2.1 s)

omit [MetricSpace U] in
theorem measurable_alphaHatU {π : U → ℝ} (hπ : IsControlEncoding π) (u₀ : U) (s : ℝ≥0) :
    Measurable (alphaHatU (T := T) (n := n) (d := d) (ℓ := ℓ) π u₀ s) :=
  (measurable_πinvU hπ u₀).comp ((measurable_limRate s).comp measurable_snd.fst)

/-- The `Ū`-valued canonical control `ᾱ_s = π⁻¹(lim̄ k(A_s − A_{0∨(s−1/k)}))` on `Ω̄`. -/
def alphaBar (π : U → ℝ) (s : ℝ≥0) (ω : OmegaBar T n d ℓ) : Option U :=
  πinv π (limRate (Ac ω) s)

/-- `ᾱ_s` with `∂` read as `u₀`. -/
def alphaBarU (π : U → ℝ) (u₀ : U) (s : ℝ≥0) (ω : OmegaBar T n d ℓ) : U :=
  πinvU π u₀ (limRate (Ac ω) s)

/-- `μ̄_s := μ̂_s ∘ (X̂_{s∧·}, α̂_s)⁻¹`, with `α̂_s = ∂` read as `u₀` so that the measure lives on
`𝒞ⁿ × U` (it is the restriction of the paper's `μ̄_s` whenever `μ̂_s[α̂_s ∈ U] = 1`). -/
def muBarU {π : U → ℝ} (hπ : IsControlEncoding π) (u₀ : U) (s : ℝ≥0) (ω : OmegaBar T n d ℓ) :
    ProbabilityMeasure (Cpath T n × U) :=
  (pathAt (muHatOf ω) s).map
    (((measurable_stopPath s).comp measurable_fst).prodMk (measurable_alphaHatU hπ u₀ s)).aemeasurable

/-- `μ_s := μ̂_s ∘ (X̂_{s∧·})⁻¹`. -/
def muC (s : ℝ≥0) (ω : OmegaBar T n d ℓ) : ProbabilityMeasure (Cpath T n) :=
  margX s (pathAt (muHatOf ω) s)

/-! ## The generator and the martingale problem (§4.1.2, pp. 15–16) -/

/-- The state space `ℝⁿ × ℝ^d × ℝ^ℓ` of the test functions. -/
abbrev StateSp (n d ℓ : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin ℓ)

/-- `φ ∈ C²_b`: twice continuously differentiable, with `φ`, `Dφ`, `D²φ` bounded. -/
structure IsC2b (φ : StateSp n d ℓ → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 φ
  bounded : ∃ C, ∀ z, |φ z| ≤ C
  bounded_fderiv : ∃ C, ∀ z, ‖fderiv ℝ φ z‖ ≤ C
  bounded_fderiv2 : ∃ C, ∀ z, ‖iteratedFDeriv ℝ 2 φ z‖ ≤ C

/-- The block matrix `( σ σ₀ ; I_{d×d} 0_{d×ℓ} ; 0_{ℓ×d} I_{ℓ×ℓ} )` of (4.3). -/
def cMat (σ : Matrix (Fin n) (Fin d) ℝ) (σ₀ : Matrix (Fin n) (Fin ℓ) ℝ) :
    Matrix (Fin n ⊕ (Fin d ⊕ Fin ℓ)) (Fin d ⊕ Fin ℓ) ℝ :=
  Matrix.of fun r k =>
    match r, k with
    | Sum.inl i, Sum.inl j => σ i j
    | Sum.inl i, Sum.inr j => σ₀ i j
    | Sum.inr r', k => if r' = k then 1 else 0

/-- `ā := C Cᵀ` (4.3). -/
def aBar (σ : Matrix (Fin n) (Fin d) ℝ) (σ₀ : Matrix (Fin n) (Fin ℓ) ℝ) :
    Matrix (Fin n ⊕ (Fin d ⊕ Fin ℓ)) (Fin n ⊕ (Fin d ⊕ Fin ℓ)) ℝ :=
  cMat σ σ₀ * (cMat σ σ₀).transpose

/-- The Frobenius norm `|a| = (Σ a_{ij}²)^{1/2}`. -/
def frob {ι κ : Type*} [Fintype ι] [Fintype κ] (a : Matrix ι κ ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, a i j ^ 2)

/-- The `k`-th column of `C`, as a vector of `ℝⁿ × ℝ^d × ℝ^ℓ`. -/
def colVec (σ : Matrix (Fin n) (Fin d) ℝ) (σ₀ : Matrix (Fin n) (Fin ℓ) ℝ) (k : Fin d ⊕ Fin ℓ) :
    StateSp n d ℓ :=
  (WithLp.toLp 2 (fun i => cMat σ σ₀ (Sum.inl i) k),
   WithLp.toLp 2 (fun i => cMat σ σ₀ (Sum.inr (Sum.inl i)) k),
   WithLp.toLp 2 (fun i => cMat σ σ₀ (Sum.inr (Sum.inr i)) k))

/-- `Σ_i b̄_i ∂_iφ(z) + ½ Σ_{i,j} ā_{ij} ∂²_{ij}φ(z)`, with `b̄ = (b, 0_d, 0_ℓ)` and `ā = C Cᵀ`,
written as `Dφ(z)(b̄) + ½ Σ_k D²φ(z)(c_k, c_k)` over the columns `c_k` of `C`. -/
def genL (φ : StateSp n d ℓ → ℝ) (b : EuclideanSpace ℝ (Fin n)) (σ : Matrix (Fin n) (Fin d) ℝ)
    (σ₀ : Matrix (Fin n) (Fin ℓ) ℝ) (z : StateSp n d ℓ) : ℝ :=
  fderiv ℝ φ z (b, 0, 0) +
    (1/2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ φ) z (colVec σ σ₀ k) (colVec σ σ₀ k)

/-- `(X_s, W_s, B_s)` on `Ω̄`. -/
def zAt (s : ℝ≥0) (ω : OmegaBar T n d ℓ) : StateSp n d ℓ :=
  (pathAt (Xc ω) s, pathAt (Wc ω) s, pathAt (Bc ω) s)

variable {π : U → ℝ} (hπ : IsControlEncoding π) (c : Coeffs T n d ℓ U) (u₀ : U)

/-- `𝓛_sφ(X, W, B, μ̄_s, ᾱ_s)` on `Ω̄`. -/
def Lgen (φ : StateSp n d ℓ → ℝ) (s : ℝ≥0) (ω : OmegaBar T n d ℓ) : ℝ :=
  genL φ (c.b s (Xc ω) (muBarU hπ u₀ s ω) (alphaBarU π u₀ s ω))
    (c.σ s (Xc ω) (muBarU hπ u₀ s ω) (alphaBarU π u₀ s ω))
    (c.σ₀ s (Xc ω) (muBarU hπ u₀ s ω) (alphaBarU π u₀ s ω)) (zAt s ω)

/-- `|S̄|_s := ∫_t^s (|b̄| + |ā|)(r, X, W, B, μ̄_r, ᾱ_r) dr ∈ [0, ∞]` (`= 0` for `s ≤ t`).
The page integrates from `0`; the integral starts at the initial time `t` of the rule, because
before `t` the control `ᾱ` may be the cemetery `∂`, where the coefficients are not defined, and a
coefficient that is not integrable on `[0,t)` would make `𝒫̂_W(t,·)` empty while `Γ_W(t,·)` is
not (the proof of Lemma 4.4, p. 17, derives `|S̄|_T < ∞` from the integrals of (2.4), which run
over `[t,T]`). The local martingale property on `[t,T]` is unchanged by this shift. -/
def absS (t s : ℝ≥0) (ω : OmegaBar T n d ℓ) : ℝ≥0∞ :=
  ∫⁻ r in Set.Icc (t:ℝ) s, ENNReal.ofReal
    (‖c.b r.toNNReal (Xc ω) (muBarU hπ u₀ r.toNNReal ω) (alphaBarU π u₀ r.toNNReal ω)‖ +
     frob (aBar (c.σ r.toNNReal (Xc ω) (muBarU hπ u₀ r.toNNReal ω) (alphaBarU π u₀ r.toNNReal ω))
       (c.σ₀ r.toNNReal (Xc ω) (muBarU hπ u₀ r.toNNReal ω) (alphaBarU π u₀ r.toNNReal ω))))

/-- `s ∧ τ_m`, where `τ_m := inf{r : |S̄|_r ≥ m}` (`inf ∅ = +∞`), `|S̄|` counted from `t`. -/
def stopTimeM (t : ℝ≥0) (m : ℕ) (s : ℝ≥0) (ω : OmegaBar T n d ℓ) : ℝ≥0 :=
  sInf (insert s {r : ℝ≥0 | ((m : ℝ≥0∞)) ≤ absS hπ c u₀ t r ω})

/-- The localised process `S^{φ,m}_s := S̄^φ_{s∧τ_m} = φ(X, W, B)_{s∧τ_m} − ∫_t^{s∧τ_m} 𝓛_rφ dr`
(4.4)–(4.5) on `[t,T]` (real valued: the integrand is integrable up to `τ_m`). It differs from
the page's `S̄^φ_{s∧τ_m}` by the `ℱ̄_t`-measurable `∫_0^t 𝓛_rφ dr` (see `absS`). -/
def Sm (t : ℝ≥0) (φ : StateSp n d ℓ → ℝ) (m : ℕ) (s : ℝ≥0) (ω : OmegaBar T n d ℓ) : ℝ :=
  φ (zAt (stopTimeM hπ c u₀ t m s ω) ω) -
    ∫ r in Set.Icc (t:ℝ) (stopTimeM hπ c u₀ t m s ω), Lgen hπ c u₀ φ r.toNNReal ω

/-! ## Filtrations on `Ω̄` -/

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
/-- The coordinate `(X_r, A_r, W_r, B_r, μ̂_r)`. -/
def coordBar (r : ℝ≥0) (ω : OmegaBar T n d ℓ) :
    EuclideanSpace ℝ (Fin n) × ℝ × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin ℓ) ×
      ProbabilityMeasure (OmegaHat T n d ℓ) :=
  (pathAt (Xc ω) r, pathAt (Ac ω) r, pathAt (Wc ω) r, pathAt (Bc ω) r, pathAt (muHatOf ω) r)

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
theorem measurable_coordBar (r : ℝ≥0) :
    Measurable (coordBar (T := T) (n := n) (d := d) (ℓ := ℓ) r) := by
  have hX : Measurable (fun ω : OmegaBar T n d ℓ => (hatOf ω).1) := measurable_fst.comp measurable_hatOf
  have hA : Measurable (fun ω : OmegaBar T n d ℓ => (hatOf ω).2.1) :=
    measurable_snd.fst.comp measurable_hatOf
  have hW : Measurable (fun ω : OmegaBar T n d ℓ => (hatOf ω).2.2.1) :=
    measurable_snd.snd.fst.comp measurable_hatOf
  have hB : Measurable (fun ω : OmegaBar T n d ℓ => (hatOf ω).2.2.2) :=
    measurable_snd.snd.snd.comp measurable_hatOf
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)))
  · exact (continuous_eval_const _).measurable.comp hX
  · exact (continuous_eval_const _).measurable.comp hA
  · exact (continuous_eval_const _).measurable.comp hW
  · exact (continuous_eval_const _).measurable.comp hB
  · exact (measurable_of_continuous_pm (continuous_eval_const _)).comp measurable_muHatOf

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
/-- The canonical filtration `𝔽̄ = (ℱ̄_s)`: the natural filtration of `(X, A, W, B, μ̂)`. -/
def Fbar (T : ℝ≥0) (n d ℓ : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (OmegaBar T n d ℓ)) where
  seq s := ⨆ r ≤ s, MeasurableSpace.comap (coordBar r) inferInstance
  mono' _ _ hst := iSup₂_le fun r hr => le_iSup₂ (f := fun r (_ : r ≤ _) =>
    MeasurableSpace.comap (coordBar (T := T) (n := n) (d := d) (ℓ := ℓ) r) inferInstance) r
      (hr.trans hst)
  le' _ := iSup₂_le fun r _ => (measurable_coordBar r).comap_le

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
/-- The coordinate `(B^t_r, μ̂_r)`. -/
def coordGt (t r : ℝ≥0) (ω : OmegaBar T n d ℓ) :
    EuclideanSpace ℝ (Fin ℓ) × ProbabilityMeasure (OmegaHat T n d ℓ) :=
  (pathAt (shiftPath t (Bc ω)) r, pathAt (muHatOf ω) r)

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
theorem measurable_coordGt (t r : ℝ≥0) :
    Measurable (coordGt (T := T) (n := n) (d := d) (ℓ := ℓ) t r) := by
  have hB : Measurable (fun ω : OmegaBar T n d ℓ => (hatOf ω).2.2.2) :=
    measurable_snd.snd.snd.comp measurable_hatOf
  refine Measurable.prodMk ?_ ?_
  · have hc : Continuous (fun b : Cpath T ℓ => pathAt (shiftPath t b) r) :=
      (continuous_eval_const _).comp (continuous_shiftPath t)
    exact hc.measurable.comp hB
  · exact (measurable_of_continuous_pm (continuous_eval_const _)).comp measurable_muHatOf

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
/-- The filtration `𝔾̄^t` of (4.1): trivial before `t`, and `σ((B^t_r, μ̂_r) : r ∈ [0,s])` for
`s ≥ t`. -/
def Gbar (T : ℝ≥0) (n d ℓ : ℕ) (t : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (OmegaBar T n d ℓ)) where
  seq s := if s < t then ⊥ else ⨆ r ≤ s, MeasurableSpace.comap (coordGt t r) inferInstance
  mono' a b hab := by
    by_cases ha : a < t
    · simp only [if_pos ha]; exact bot_le
    · have hb : ¬ b < t := fun hb => ha (lt_of_le_of_lt hab hb)
      simp only [if_neg ha, if_neg hb]
      exact iSup₂_le fun r hr => le_iSup₂ (f := fun r (_ : r ≤ b) =>
        MeasurableSpace.comap (coordGt (T := T) (n := n) (d := d) (ℓ := ℓ) t r) inferInstance) r
          (hr.trans hab)
  le' s := by
    by_cases hs : s < t
    · simp only [if_pos hs]; exact bot_le
    · simp only [if_neg hs]
      exact iSup₂_le fun r _ => (measurable_coordGt t r).comap_le

/-! ## Weak control rules (Definition 4.1, p. 16) -/

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
/-- `(X_{s∧·}, A_{s∧·}, W, B_{s∧·})` on `Ω̄`. -/
def Ybar (s : ℝ≥0) (ω : OmegaBar T n d ℓ) : OmegaHat T n d ℓ := stopHatW s (hatOf ω)

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
/-- `(x_{t∧·}, a_{t∧·}, w_{t∧·}, b_{t∧·})` on `Ω̂`. -/
def stopHatAll (t : ℝ≥0) (z : OmegaHat T n d ℓ) : OmegaHat T n d ℓ :=
  (stopPath t z.1, stopPath t z.2.1, stopPath t z.2.2.1, stopPath t z.2.2.2)

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
theorem measurable_stopHatAll (t : ℝ≥0) :
    Measurable (stopHatAll (T := T) (n := n) (d := d) (ℓ := ℓ) t) :=
  ((measurable_stopPath t).comp measurable_fst).prodMk
    (((measurable_stopPath t).comp measurable_snd.fst).prodMk
      (((measurable_stopPath t).comp measurable_snd.snd.fst).prodMk
        ((measurable_stopPath t).comp measurable_snd.snd.snd)))

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
/-- `ν̂(t) := ν̂ ∘ (X̂_{t∧·}, Â_{t∧·}, Ŵ_{t∧·}, B̂_{t∧·})⁻¹`. -/
def lawHatStop (ν : ProbabilityMeasure (OmegaHat T n d ℓ)) (t : ℝ≥0) :
    ProbabilityMeasure (OmegaHat T n d ℓ) :=
  ν.map (measurable_stopHatAll t).aemeasurable

/-- `𝔼^ℙ̄[∫_t^T ρ(u₀, ᾱ_s)^p ds]` (with `∂` read as `u₀`). -/
def costAlpha (p : ℝ) (t : ℝ≥0) (P : ProbabilityMeasure (OmegaBar T n d ℓ)) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ r in Set.Icc (t:ℝ) T, edist u₀ (alphaBarU π u₀ r.toNNReal ω) ^ p ∂volume
    ∂(P : Measure (OmegaBar T n d ℓ))

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
/-- `𝔼^ℙ̄[‖X‖^p]`. -/
def momentX (p : ℝ) (P : ProbabilityMeasure (OmegaBar T n d ℓ)) : ℝ≥0∞ :=
  ∫⁻ ω, ‖Xc ω‖ₑ ^ p ∂(P : Measure (OmegaBar T n d ℓ))

/-- `ℙ̄` is a weak control rule with initial condition `(t, ν̂)` (Definition 4.1). The local
martingale property of (iii) is read as: every localised process `S^{φ,m}` (`m ≥ 1`) is an
`(𝔽̄, ℙ̄)`-martingale on `[t,T]`; `|S̄|` and the time integral in `S̄^φ` run from `t` (see `absS`). -/
structure IsWeakControlRule (p : ℝ) (t : ℝ≥0) (νh : ProbabilityMeasure (OmegaHat T n d ℓ))
    (P : ProbabilityMeasure (OmegaBar T n d ℓ)) : Prop where
  /-- (i) -/
  alpha_mem_U : ∀ᵐ r ∂(volume.restrict (Set.Icc (t:ℝ) T)),
    (P : Measure (OmegaBar T n d ℓ)) {ω | InRangeπ π (limRate (Ac ω) r.toNNReal)} = 1
  alpha_integrable : costAlpha u₀ (π := π) p t P < ⊤
  /-- (ii), (4.6) -/
  muhat_le : ∀ s : ℝ≥0, s ≤ t → s ≤ T → ∀ᵐ ω ∂(P : Measure (OmegaBar T n d ℓ)),
    ((pathAt (muHatOf ω) s : ProbabilityMeasure (OmegaHat T n d ℓ)) : Measure (OmegaHat T n d ℓ)) =
      (P : Measure (OmegaBar T n d ℓ)).map (Ybar s)
  muhat_gt : ∀ s : ℝ≥0, t < s → s ≤ T →
    IsCondLaw (Gbar T n d ℓ t T) (P : Measure (OmegaBar T n d ℓ)) (Ybar s)
      (fun ω => pathAt (muHatOf ω) s)
  initial : (P : Measure (OmegaBar T n d ℓ)).map (fun ω => stopHatAll t (hatOf ω)) =
    (lawHatStop νh t : Measure (OmegaHat T n d ℓ))
  /-- (iii) -/
  moment_X : momentX p P < ⊤
  absS_finite : (P : Measure (OmegaBar T n d ℓ)) {ω | absS hπ c u₀ t T ω < ⊤} = 1
  martingale : ∀ φ : StateSp n d ℓ → ℝ, IsC2b φ → ∀ m : ℕ, 1 ≤ m → ∀ r s : ℝ≥0,
    t ≤ r → r ≤ s → s ≤ T →
      Integrable (Sm hπ c u₀ t φ m s) (P : Measure (OmegaBar T n d ℓ)) ∧
      condExp (Fbar T n d ℓ r) (P : Measure (OmegaBar T n d ℓ)) (Sm hπ c u₀ t φ m s)
        =ᵐ[(P : Measure (OmegaBar T n d ℓ))] Sm hπ c u₀ t φ m r

/-- `𝒫̂_W(t, ν̂)`. -/
def PhatW (p : ℝ) (t : ℝ≥0) (νh : ProbabilityMeasure (OmegaHat T n d ℓ)) :
    Set (ProbabilityMeasure (OmegaBar T n d ℓ)) :=
  {P | IsWeakControlRule hπ c u₀ p t νh P}

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
/-- `ν̂ ∘ X̂⁻¹`. -/
def margXhat (νh : ProbabilityMeasure (OmegaHat T n d ℓ)) : ProbabilityMeasure (Cpath T n) :=
  νh.map measurable_fst.aemeasurable

/-- `𝒫̄_W(t, ν) := ⋃_{ν̂ ∈ 𝒱(ν)} 𝒫̂_W(t, ν̂)`, `𝒱(ν) := {ν̂ : ν̂ ∘ X̂⁻¹ = ν}`. -/
def PbarW (p : ℝ) (t : ℝ≥0) (ν : ProbabilityMeasure (Cpath T n)) :
    Set (ProbabilityMeasure (OmegaBar T n d ℓ)) :=
  {P | ∃ νh : ProbabilityMeasure (OmegaHat T n d ℓ), margXhat νh = ν ∧ P ∈ PhatW hπ c u₀ p t νh}

/-- `𝒫̄^M_t := {ℙ̄ : 𝔼[‖X‖^p] + 𝔼[∫_t^T ρ(u₀, ᾱ_s)^p ds] ≤ M}` (p. 20). -/
def PbarM (p : ℝ) (t : ℝ≥0) (M : ℝ≥0) : Set (ProbabilityMeasure (OmegaBar T n d ℓ)) :=
  {P | momentX p P + costAlpha u₀ (π := π) p t P ≤ (M : ℝ≥0∞)}

/-- `𝒫̂^M_W(t, ν̂) := 𝒫̂_W(t, ν̂) ∩ 𝒫̄^M_t`. -/
def PhatWM (p : ℝ) (t : ℝ≥0) (νh : ProbabilityMeasure (OmegaHat T n d ℓ)) (M : ℝ≥0) :
    Set (ProbabilityMeasure (OmegaBar T n d ℓ)) :=
  PhatW hπ c u₀ p t νh ∩ PbarM u₀ (π := π) p t M

/-- `𝒫̄^M_W(t, ν) := 𝒫̄_W(t, ν) ∩ 𝒫̄^M_t`. -/
def PbarWM (p : ℝ) (t : ℝ≥0) (ν : ProbabilityMeasure (Cpath T n)) (M : ℝ≥0) :
    Set (ProbabilityMeasure (OmegaBar T n d ℓ)) :=
  PbarW hπ c u₀ p t ν ∩ PbarM u₀ (π := π) p t M

/-- `J(t, ℙ̄) := 𝔼^ℙ̄[∫_t^T L(s, X, μ̄_s, ᾱ_s) ds + g(X, μ_T)]` (4.9). -/
def Jbar (t : ℝ≥0) (P : ProbabilityMeasure (OmegaBar T n d ℓ)) : EReal :=
  eExp (P : Measure (OmegaBar T n d ℓ)) (fun ω =>
    timeInt t T (fun s => ((c.L s (Xc ω) (muBarU hπ u₀ s ω) (alphaBarU π u₀ s ω) : ℝ) : EReal)) +
      ((c.g (Xc ω) (muC T ω) : ℝ) : EReal))

/-- `V^M_W(t, ν) := sup_{ℙ̄ ∈ 𝒫̄^M_W(t,ν)} J(t, ℙ̄)` (p. 20). -/
def VWM (p : ℝ) (t : ℝ≥0) (ν : ProbabilityMeasure (Cpath T n)) (M : ℝ≥0) : EReal :=
  ⨆ P ∈ PbarWM hπ c u₀ p t ν M, Jbar hπ c u₀ t P

/-- The graph `⟦𝒫̂_W⟧ ⊆ [0,T] × 𝒫(Ω̂) × 𝒫(Ω̄)`. -/
def graphPhatW (p : ℝ) :
    Set (Set.Icc (0:ℝ≥0) T × ProbabilityMeasure (OmegaHat T n d ℓ) ×
      ProbabilityMeasure (OmegaBar T n d ℓ)) :=
  {x | x.2.2 ∈ PhatW hπ c u₀ p x.1 x.2.1}

/-- The graph `⟦𝒫̄_W⟧ ⊆ [0,T] × 𝒫(𝒞ⁿ) × 𝒫(Ω̄)`. -/
def graphPbarW (p : ℝ) :
    Set (Set.Icc (0:ℝ≥0) T × ProbabilityMeasure (Cpath T n) ×
      ProbabilityMeasure (OmegaBar T n d ℓ)) :=
  {x | x.2.2 ∈ PbarW hπ c u₀ p x.1 x.2.1}

/-- The graph `{(t, ν, M, ℙ̄) : ℙ̄ ∈ 𝒫̄^M_W(t, ν)}` of (4.10). -/
def graphPbarWM (p : ℝ) :
    Set (Set.Icc (0:ℝ≥0) T × ProbabilityMeasure (Cpath T n) × ℝ≥0 ×
      ProbabilityMeasure (OmegaBar T n d ℓ)) :=
  {x | x.2.2.2 ∈ PbarWM hπ c u₀ p x.1 x.2.1 x.2.2.1}

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
/-- `(X, A^t, W^t, B^t)` on `Ω̄`, where `A^t_· := A_{·∨t} − A_t` (Lemma 4.9). -/
def shiftBar (t : ℝ≥0) (ω : OmegaBar T n d ℓ) : OmegaHat T n d ℓ :=
  (Xc ω, shiftPath t (Ac ω), shiftPath t (Wc ω), shiftPath t (Bc ω))

omit [MetricSpace U] [MeasurableSpace U] [BorelSpace U] in
theorem measurable_shiftBar (t : ℝ≥0) :
    Measurable (shiftBar (T := T) (n := n) (d := d) (ℓ := ℓ) t) := by
  have hX : Measurable (fun ω : OmegaBar T n d ℓ => (hatOf ω).1) := measurable_fst.comp measurable_hatOf
  have hA : Measurable (fun ω : OmegaBar T n d ℓ => (hatOf ω).2.1) :=
    measurable_snd.fst.comp measurable_hatOf
  have hW : Measurable (fun ω : OmegaBar T n d ℓ => (hatOf ω).2.2.1) :=
    measurable_snd.snd.fst.comp measurable_hatOf
  have hB : Measurable (fun ω : OmegaBar T n d ℓ => (hatOf ω).2.2.2) :=
    measurable_snd.snd.snd.comp measurable_hatOf
  exact hX.prodMk (((continuous_shiftPath t).measurable.comp hA).prodMk
    (((continuous_shiftPath t).measurable.comp hW).prodMk ((continuous_shiftPath t).measurable.comp hB)))

/-- The map `ω ↦ (X^γ, A^γ, W^γ, B^γ, μ̂^γ)(ω) ∈ Ω̄` of a weak control (4.7). -/
def embedBar {c : Coeffs T n d ℓ U} {u₀ : U} {p : ℝ} {π : U → ℝ} {Ω : Type} [MeasurableSpace Ω]
    {t : ℝ≥0} {ν : ProbabilityMeasure (Cpath T n)} (γ : WeakControl c u₀ p π Ω t ν) (ω : Ω) :
    OmegaBar T n d ℓ :=
  mkBar (γ.X ω, γ.A ω, γ.W ω, γ.B ω) (γ.μhat ω)

end

end MKVDPP.Weak


