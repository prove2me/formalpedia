-- Prove2me | Definitions.Def_SysBathGibbs_Generator
-- name    : SysBathGibbs_Generator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:19.39112+00:00
-- url     : https://prove2.me/theorems/c4b2aee0-3a4b-4a3e-9f04-ea693ce17203
-- title:
--   The second-order generator $\mathcal L$, its KMS part $\mathcal L_{\mathrm{KMS}}$, the Lamb shift and the ideal channel
-- statement:
--   All objects are at $\sigma=\beta/2$, for a chain $H_n$ and a site $x$, with $Q=4^q-1$ couplings $A_{x,a}$. For a time window $I$ (the finite window $(-T,T)$ or all of $\mathbb R$):
--
--   1. the filtered coupling $V_{A}(u)=\int_I f_\sigma(t)A(t)e^{-iut}\,dt$ and the bath correlation $c_{\beta,\sigma}(v)=\int g_{\beta,\sigma}(u)e^{iuv}du$;
--   2. the site generator (3.8), $\mathcal L_{x}(\rho)=-\sum_a\int g_{\beta,\sigma}(\omega)\int_{s<t,\ s,t\in I}\operatorname{Tr}_{E}[W_{A_{x,a},\omega}(t),[W_{A_{x,a},\omega}(s),\rho\otimes\tau_\omega]]\,ds\,dt\,d\omega$, with $W_{A,\omega}(t)=f_\sigma(t)A(t)\otimes(e^{i\omega t}B+e^{-i\omega t}B^\dagger)$ and $\tau_\omega=e^{\tilde\beta\omega Z/2}/\operatorname{Tr}(\cdot)$;
--   3. the transition map $\mathcal J_x(\rho)=\sum_a\int g\,V\rho V^\dagger$, the ordered coefficient $Q_x=\sum_a\int_{s<t}f_\sigma(t)f_\sigma(s)c_{\beta,\sigma}(t-s)A_{x,a}(t)A_{x,a}(s)$, the decay matrix $M_x=\sum_a\int g\,V^\dagger V$, the coherent term $H_x=(Q_x-Q_x^\dagger)/(2i)$ and the dissipators $\mathcal D_V(\rho)=V\rho V^\dagger-\tfrac12\{V^\dagger V,\rho\}$;
--   4. on the infinite window: $\mathcal L=\sum_x\mathcal L_x$, $G_{D,x}=\tfrac i2\sum_\nu\tanh(\beta\nu/4)(M_x)_\nu$, $B^{\mathrm{Lamb}}_x=H_x-G_{D,x}$, $H_{\mathrm{Lamb}}=\sum_xB^{\mathrm{Lamb}}_x$, and
--   $$
--   \mathcal L_{\mathrm{KMS}}(\rho)=-i[G_D,\rho]+\sum_{x,a}\int g_{\beta,\sigma}(u)\mathcal D_{V_{A_{x,a}}(u)}(\rho)\,du,
--   $$
--   with its site version $\mathcal L_{\mathrm{KMS},x}$;
--   5. the ideal round $\tilde\Phi_{\alpha,T}=\mathcal U(T)e^{\alpha^2\mathcal L}\mathcal U(T)$ and its average over a law of $T$.
--
--   **Formalization Note** The infinite-window objects are defined directly by integrals over $\mathbb R$ and $\{s<t\}\subseteq\mathbb R^2$, which converge absolutely because $f_\sigma\in L^1$; they equal the limits $T\to\infty$ of p.26. $B^{\mathrm{Lamb}}_x$ here is the uncentered form of (3.25).
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), §3.2–§3.3 eqs. (3.2), (3.8), (3.12)–(3.17), (3.22), (3.25)–(3.26), pp.21–27; (2.15), p.12; (2.20)/(5.1) for the ideal channel

import Definitions.Def_SysBathGibbs_KMS

open Matrix MeasureTheory
open scoped Kronecker

namespace SysBathGibbs

/-!
# The second-order generator, the KMS part, and the Lamb shift

Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), §3.2–§3.3, (3.2), (3.8),
(3.12)–(3.17), (3.22), (3.25)–(3.26), pp.21–27, and (5.1), (2.20) for the ideal channel.

**Formalization Note.** All objects are at `σ = β/2`. The time integrals run over a window `I`: the
paper's finite window is `I = Ioo (-T) T` (`finWin T`), and its infinite window is `I = univ`, on which
the integrals converge absolutely since `f_σ ∈ L¹`. These equal the limits `T → ∞` taken on p.26.
The double integrals are over `(t, s) ∈ I × I` with `s < t`, under Lebesgue measure on `ℝ × ℝ`. A
coupling `A_{x,a}` is Hermitian, so `(3.2)` and `(3.15)` use it without adjoints, as the paper does.
-/

variable {n q : ℕ}

/-- The finite window `-T < t < T`. -/
def finWin (T : ℝ) : Set ℝ := Set.Ioo (-T) T

/-- The region `{(t, s) ∈ I × I : s < t}` of the ordered double integrals, (3.8), (3.15). -/
def ordered (I : Set ℝ) : Set (ℝ × ℝ) := {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 < p.1}

/-- `g_{β,σ}` at `σ = β/2`. -/
noncomputable def g (β u : ℝ) : ℝ := freqDensity β (β / 2) u

/-- The bath correlation function `c_{β,σ}(v) = ∫ g_{β,σ}(u) e^{iuv} du`, (3.13). -/
noncomputable def bathCorr (β v : ℝ) : ℂ :=
  ∫ u, (g β u : ℂ) * Complex.exp (Complex.I * u * v)

/-- The filtered coupling `V_{A,T}(u) = ∫_{-T}^{T} f_σ(t) A(t) e^{-iut} dt`, (3.12). -/
noncomputable def filtered (β : ℝ) (H A : SysMat n q) (I : Set ℝ) (u : ℝ) : SysMat n q :=
  matInt (volume.restrict I) fun t =>
    ((pulse (β / 2) t : ℂ) * Complex.exp (-(Complex.I * u * t))) • evo H t A

/-- The single-qubit `B = |1⟩⟨0|`, (3.2). -/
def B1 : Matrix Bool Bool ℂ := Matrix.of fun i j => if i = true ∧ j = false then 1 else 0

/-- `b_ω(t) = e^{iωt} B + e^{-iωt} B†`, (3.2). -/
noncomputable def bOmega (w t : ℝ) : Matrix Bool Bool ℂ :=
  Complex.exp (Complex.I * w * t) • B1 + Complex.exp (-(Complex.I * w * t)) • B1ᴴ

/-- `W_{A,ω}(t) = f_σ(t) A(t) ⊗ b_ω(t)`, (3.2). -/
noncomputable def WA (β : ℝ) (H A : SysMat n q) (w t : ℝ) :
    Matrix (Site n q × Bool) (Site n q × Bool) ℂ :=
  (pulse (β / 2) t : ℂ) • (evo H t A ⊗ₖ bOmega w t)

/-- The single bath qubit's state `τ_ω = e^{β̃ωZ/2} / Tr[e^{β̃ωZ/2}]`, p.21, at `σ = β/2`. -/
noncomputable def tauOmega (β w : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => ((bathWeight (betaTilde β (β / 2)) w b : ℝ) : ℂ)

/-- The site generator (3.8), with window `I`:
`L_{x,T}(ρ) = -∑_a ∫ g(ω) ∫_{-T<s<t<T} Tr_{E_{x,a}}[W(t), [W(s), ρ ⊗ τ_ω]] ds dt dω`. The window
`I = univ` gives the limit `L_x` of p.26. -/
noncomputable def siteGen (β : ℝ) (h : Fin (n - 1) → SysMat n q) (x : Fin n) (I : Set ℝ)
    (ρ : SysMat n q) : SysMat n q :=
  -∑ a : Coupling q,
    matInt volume fun w =>
      (g β w : ℂ) •
        matInt (volume.restrict (ordered I)) fun p : ℝ × ℝ =>
          WildeQIT.partialTraceRight
            (comm (WA β (chainHam h) (pauliString x a.1) w p.1)
              (comm (WA β (chainHam h) (pauliString x a.1) w p.2) (ρ ⊗ₖ tauOmega β w)))

/-- The site transition map `J_{x,T}(ρ) = ∑_a ∫ g(u) V(u) ρ V(u)† du`, (3.14). -/
noncomputable def siteJ (β : ℝ) (h : Fin (n - 1) → SysMat n q) (x : Fin n) (I : Set ℝ)
    (ρ : SysMat n q) : SysMat n q :=
  ∑ a : Coupling q,
    matInt volume fun u =>
      (g β u : ℂ) •
        (filtered β (chainHam h) (pauliString x a.1) I u * ρ *
          (filtered β (chainHam h) (pauliString x a.1) I u)ᴴ)

/-- The ordered coefficient
`Q_{x,T} = ∑_a ∫_{-T<s<t<T} f_σ(t) f_σ(s) c_{β,σ}(t-s) A(t) A(s) ds dt`, (3.15). -/
noncomputable def siteQ (β : ℝ) (h : Fin (n - 1) → SysMat n q) (x : Fin n) (I : Set ℝ) :
    SysMat n q :=
  ∑ a : Coupling q,
    matInt (volume.restrict (ordered I)) fun p : ℝ × ℝ =>
      (((pulse (β / 2) p.1 * pulse (β / 2) p.2 : ℝ) : ℂ) * bathCorr β (p.1 - p.2)) •
        (evo (chainHam h) p.1 (pauliString x a.1) * evo (chainHam h) p.2 (pauliString x a.1))

/-- The decay matrix `M_{x,T} = ∑_a ∫ g(u) V(u)† V(u) du`, (3.16). -/
noncomputable def siteM (β : ℝ) (h : Fin (n - 1) → SysMat n q) (x : Fin n) (I : Set ℝ) :
    SysMat n q :=
  ∑ a : Coupling q,
    matInt volume fun u =>
      (g β u : ℂ) •
        ((filtered β (chainHam h) (pauliString x a.1) I u)ᴴ *
          filtered β (chainHam h) (pauliString x a.1) I u)

/-- The coherent term `H_{x,T} = (Q_{x,T} - Q†_{x,T})/(2i)`, (3.16). -/
noncomputable def siteH (β : ℝ) (h : Fin (n - 1) → SysMat n q) (x : Fin n) (I : Set ℝ) :
    SysMat n q :=
  (2 * Complex.I)⁻¹ • (siteQ β h x I - (siteQ β h x I)ᴴ)

/-- The Lindblad dissipator `D_V(ρ) = V ρ V† - ½{V†V, ρ}`, (2.15). -/
noncomputable def dissipator (V ρ : SysMat n q) : SysMat n q :=
  V * ρ * Vᴴ - (1 / 2 : ℂ) • acomm (Vᴴ * V) ρ

/-- The term `∑_a ∫ g(u) D_{V_{A_{x,a}}(u)}(ρ) du` of a site, in (3.17) and (3.26). -/
noncomputable def siteDiss (β : ℝ) (h : Fin (n - 1) → SysMat n q) (x : Fin n) (I : Set ℝ)
    (ρ : SysMat n q) : SysMat n q :=
  ∑ a : Coupling q,
    matInt volume fun u =>
      (g β u : ℂ) • dissipator (filtered β (chainHam h) (pauliString x a.1) I u) ρ

/-- The infinite-window effective Lindbladian `L = ∑_x L_x`, (3.22). -/
noncomputable def Leff (β : ℝ) (h : Fin (n - 1) → SysMat n q) (ρ : SysMat n q) : SysMat n q :=
  ∑ x, siteGen β h x Set.univ ρ

/-- The site KMS coherent correction `G_{D,x} = (i/2) ∑_ν tanh(βν/4) (M_x)_ν`, (3.25). -/
noncomputable def siteGD (β : ℝ) (h : Fin (n - 1) → SysMat n q) (x : Fin n) : SysMat n q :=
  bohrSum (fun ν => (Complex.I / 2) * ((Real.tanh (β * ν / 4) : ℝ) : ℂ)) (chainHam h)
    (siteM β h x Set.univ)

/-- `B^Lamb_x = H_x - G_{D,x}`, (3.25) (the uncentered form). -/
noncomputable def siteLamb (β : ℝ) (h : Fin (n - 1) → SysMat n q) (x : Fin n) : SysMat n q :=
  siteH β h x Set.univ - siteGD β h x

/-- `H_Lamb = ∑_x B^Lamb_x`, (3.25) (the uncentered form). -/
noncomputable def HLamb (β : ℝ) (h : Fin (n - 1) → SysMat n q) : SysMat n q :=
  ∑ x, siteLamb β h x

/-- The site KMS generator `L_{KMS,x}(ρ) = -i[G_{D,x}, ρ] + ∑_a ∫ g(u) D_{V_{A_{x,a}}(u)}(ρ) du`,
p.27. -/
noncomputable def siteLKMS (β : ℝ) (h : Fin (n - 1) → SysMat n q) (x : Fin n) (ρ : SysMat n q) :
    SysMat n q :=
  (-Complex.I) • comm (siteGD β h x) ρ + siteDiss β h x Set.univ ρ

/-- The KMS generator `L_KMS(ρ) = -i[G_D, ρ] + ∑_{x,a} ∫ g(u) D_{V_{A_{x,a}}(u)}(ρ) du`, (3.26),
with `G_D = ∑_x G_{D,x}`. -/
noncomputable def LKMS (β : ℝ) (h : Fin (n - 1) → SysMat n q) (ρ : SysMat n q) : SysMat n q :=
  (-Complex.I) • comm (∑ x, siteGD β h x) ρ + ∑ x, siteDiss β h x Set.univ ρ

/-- The ideal round `Φ̃_{α,T} = U(T) e^{α²L} U(T)`, (2.20), (5.1). -/
noncomputable def idealRound (β : ℝ) (h : Fin (n - 1) → SysMat n q) (α T : ℝ)
    (ρ : SysMat n q) : SysMat n q :=
  fwd (chainHam h) T (superExp (α ^ 2) (Leff β h) (fwd (chainHam h) T ρ))

/-- The averaged ideal channel `Φ̃^μ_α = E_T[Φ̃_{α,T}]` for a law `μ` of `T`, p.54. -/
noncomputable def idealChannelOf (β : ℝ) (h : Fin (n - 1) → SysMat n q) (α : ℝ)
    (μ : Measure ℝ) (ρ : SysMat n q) : SysMat n q :=
  matInt μ fun T => idealRound β h α T ρ

end SysBathGibbs


