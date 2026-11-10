-- Prove2me | Definitions.Def_HiddenHardCoreColoring_Mixing_Hidden
-- name    : HiddenHardCoreColoring_Mixing_Hidden
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:59:50.333783+00:00
-- url     : https://prove2.me/theorems/65e70a37-a8e8-4067-93b5-f4e7fe753963
-- title:
--   Hidden hard-core models: backgrounds, lifts, ghost-color averages, resolvent smoothing, W_c, Ξ, K
-- statement:
--   This file fixes the objects of §§6.2–6.4 (pp.18–21) and §§7.2–7.4 (pp.24–27) for a fixed color $c$.
--
--   1. $\Omega^{-c}=\{\eta\in\Omega:\eta_v\ne c\ \forall v\}$ (backgrounds). For a pair $(\eta,I)\in\Omega^{-c}\times\mathcal I$, $\pi_c(\eta,I)\in\Omega$ equals $c$ on $I$ and $\eta$ outside $I$.
--   2. A **lift** of $\sigma\in\Omega$ sets $I=\{v:\sigma_v=c\}$, draws ghost colors $\eta_v\in A_v^{-c}(\sigma)$ independently and uniformly for $v\in I$, and sets $\eta_v=\sigma_v$ elsewhere. $\hat\mu_c$ is the law of a lift of $\sigma\sim\mu$ and $\rho_c$ its $\eta$-marginal.
--   3. **Hidden activities** $\lambda_v(\eta)=1/(|A_v(\eta)|-1)$; $\nu_\eta$, $H_\eta$, $H_{\eta,v}$ are the hard-core objects of §3.3 with these activities.
--   4. $f^\uparrow(\eta,I)=f(\pi_c(\eta,I))$; $F_\eta=F(\eta,\cdot)$; $F^\downarrow(\sigma)=\mathbb E_{\hat\mu_c}[F(\eta,I)\mid\pi_c(\eta,I)=\sigma]$, the mean of $F$ over a random lift of $\sigma$.
--   5. For $a>0$: $(\hat R_cF)_\eta=R_\eta F_\eta$ with $R_\eta=(\mathrm{Id}+aH_\eta)^{-1}$, and the smoothed function $\tilde f_c=(\hat R_cf^\uparrow)^\downarrow$.
--   6. With $E_v^{-c}$ the average over $c'$ uniform in $A_v^{-c}(\eta)$,
--   $$W_{v,c}(F)=\tfrac12\,\mathbb E_{\hat\mu_c}\Big[\mathbf 1\{v\in V_{\mathrm{ubl}}(I)\setminus I\}\,p_v(\eta)\,E_v^{-c}\big(F(\eta^{v\leftarrow c'},I)-F(\eta,I)\big)^2\Big],\qquad W_c=\sum_vW_{v,c}.$$
--   7. $\Xi(f)=\sum_c\sum_u\mathbb E_{\eta\sim\rho_c}E_u^{-c}\big\langle f^\uparrow_{\eta^{u\leftarrow c'}}-f^\uparrow_\eta,\ H_\eta(f^\uparrow_{\eta^{u\leftarrow c'}}-f^\uparrow_\eta)\big\rangle_{\nu_\eta}$, and $K=\exp(\Delta/(q-\Delta-1))$.
--
--   These are actual finite kernels computed from $G$, $q$ and $c$: the lift law, the hidden activities and the resolvents are defined from the data, not assumed.
--
--   **Formalization Note** $\hat\mu_c(\eta,I)=\sum_\sigma\mu(\sigma)\,\kappa_\sigma(\eta,I)$ with $\kappa_\sigma$ the lift kernel, and $F^\downarrow(\sigma)=\sum_{(\eta,I)}\kappa_\sigma(\eta,I)F(\eta,I)$. Values of $F$ at recolored backgrounds are read through an extension by $0$ off $\Omega^{-c}$, which every summation range avoids. Expectations over $\rho_c$ and $\hat\mu_c$ are weighted sums.
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; §6.2, pp.18–19 (Ω^{-c}, lifts, µ̂_c, π_c, λ_v(η), ν_η, H_η, H_{η,v}); §6.3, p.20 (f↑, F↓, F_η, ρ_c); §6.4, p.21 (R_η, R̂_c, f̃_c); §7.2, pp.24–25 (K, W_{v,c}, W_c); §7.4, p.27 (Ξ)

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Coloring
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore

namespace HiddenHardCoreColoring.Mixing

open Finset Matrix

noncomputable section

/-!
# The hard-core model hidden in a color class: lifts, ghost colors, resolvent smoothing

Xiongxin Yang, *Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via
Hidden Hard-Core Models*, STOC 2027 submission #964 (October 2026): §6.2 (pp.18–19), §6.3 (p.20),
§6.4 (p.21), §7.2 (pp.24–25), §7.4 (p.27).

Fix a color `c`. A *pair* is an element of `Ω^{-c} × ℐ`, where `Ω^{-c} = Bg G q c` are the proper
colorings using no `c` and `ℐ = IndSet G`. Expectations `E_{η∼ρ_c}[X(η)]` are written
`∑_η ρ_c(η) X(η)`, and `E_{(η,I)∼µ̂_c}[X]` as `∑_{(η,I)} µ̂_c(η,I) X(η,I)`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ)

/-- `Ω^{-c} := {η ∈ Ω : η_v ≠ c for all v}`, the background colorings (§6.2, p.18). -/
abbrev Bg (c : Fin q) : Type _ :=
  {η : V → Fin q // MarkovMixing.IsProperColoring G η ∧ ∀ v, η v ≠ c}

variable {q}

/-- The assignment equal to `c` on `I` and to `η` outside `I`. -/
def piFun (c : Fin q) (η : V → Fin q) (I : Finset V) : V → Fin q :=
  fun v => if v ∈ I then c else η v

omit [Fintype V] [DecidableRel G.Adj] in
/-- `π_c(η, I)` is a proper coloring for every pair (§6.2, p.19). -/
theorem piFun_proper (c : Fin q) (η : Bg G q c) (I : IndSet G) :
    MarkovMixing.IsProperColoring G (piFun c η.1 I.1) := by
  intro v w hvw
  unfold piFun
  by_cases hv : v ∈ I.1 <;> by_cases hw : w ∈ I.1 <;> simp only [hv, hw, if_true, if_false]
  · exact absurd hvw (I.2 v hv w hw)
  · exact fun h => η.2.2 w h.symm
  · exact η.2.2 v
  · exact η.2.1 v w hvw

/-- `π_c(η, I) ∈ Ω`: the coloring equal to `c` on `I` and agreeing with `η` outside `I`
(§6.2, p.19). -/
def piC (c : Fin q) (η : Bg G q c) (I : IndSet G) : Col G q :=
  ⟨piFun c η.1 I.1, piFun_proper G c η I⟩

/-- **The lift kernel** (§6.2, p.18): the probability that a lift of `σ` is the pair `(η, I)`. A lift
of `σ` sets `I = {v : σ_v = c}`, chooses `η_v ∈ A_v^{-c}(σ)` independently and uniformly for each
`v ∈ I` (the ghost colors), and sets `η_v = σ_v` for `v ∉ I`. -/
def liftKer (c : Fin q) (σ : Col G q) (p : Bg G q c × IndSet G) : ℝ :=
  if (∀ v, v ∈ p.2.1 ↔ σ.1 v = c) ∧ (∀ v, v ∉ p.2.1 → p.1.1 v = σ.1 v) ∧
      (∀ v ∈ p.2.1, p.1.1 v ∈ availMinus G σ.1 v c) then
    ∏ v ∈ p.2.1, 1 / ((availMinus G σ.1 v c).card : ℝ)
  else 0

/-- `µ̂_c`: the law of a lift of `σ ∼ µ` on pairs (§6.2, p.19). -/
def muHat (c : Fin q) (p : Bg G q c × IndSet G) : ℝ :=
  ∑ σ : Col G q, colMu G q σ * liftKer G c σ p

/-- `ρ_c`: the marginal law of the background coloring under `µ̂_c` (§6.3, p.20). -/
def rho (c : Fin q) (η : Bg G q c) : ℝ := ∑ I : IndSet G, muHat G c (η, I)

/-- **The hidden activities** `λ_v(η) := 1/(|A_v(η)| − 1)` (§6.2, p.19). -/
def hiddenAct (c : Fin q) (η : Bg G q c) (v : V) : ℝ :=
  1 / (((avail G η.1 v).card : ℝ) - 1)

/-- The hidden model `ν_η`: the hard-core model on `G` with activities `λ(η)` (§6.2, p.19). -/
def nuEta (c : Fin q) (η : Bg G q c) : IndSet G → ℝ := hcLaw G (hiddenAct G c η)

/-- `H_η`: the operator `H` of §3.3 for the activities `λ(η)` (§6.2, p.19). -/
def Heta (c : Fin q) (η : Bg G q c) : Matrix (IndSet G) (IndSet G) ℝ := hcH G (hiddenAct G c η)

/-- `H_{η,v}`: the operator `H_v` of §3.3 for the activities `λ(η)` (§6.2, p.19). -/
def HetaV (c : Fin q) (η : Bg G q c) (v : V) : Matrix (IndSet G) (IndSet G) ℝ :=
  hcHv G (hiddenAct G c η) v

/-- `⟨h, g⟩_{ν_η}`. -/
def ipEta (c : Fin q) (η : Bg G q c) (h g : IndSet G → ℝ) : ℝ := ipNu G (hiddenAct G c η) h g

/-- The lift `f↑(η, I) := f(π_c(η, I))` (§6.3, p.20). -/
def up (c : Fin q) (f : Col G q → ℝ) (p : Bg G q c × IndSet G) : ℝ := f (piC G c p.1 p.2)

/-- `F_η := F(η, ·)`, a function on `ℐ` (§6.3, p.20). -/
def fiber {c : Fin q} (F : Bg G q c × IndSet G → ℝ) (η : Bg G q c) : IndSet G → ℝ :=
  fun I => F (η, I)

/-- **The ghost-color average** `F↓(σ) := E_{(η,I)∼µ̂_c}[F(η, I) | π_c(η, I) = σ]`, the expectation of
`F` at a random lift of `σ` (§6.3, p.20). -/
def down (c : Fin q) (F : Bg G q c × IndSet G → ℝ) (σ : Col G q) : ℝ :=
  ∑ p : Bg G q c × IndSet G, liftKer G c σ p * F p

/-- `R̂_c`: the resolvents `R_η = (Id + aH_η)⁻¹` applied fiberwise, `(R̂_c F)_η := R_η F_η`
(§6.4, p.21). -/
def Rhat (c : Fin q) (a : ℝ) (F : Bg G q c × IndSet G → ℝ) (p : Bg G q c × IndSet G) : ℝ :=
  (resolvent G (hiddenAct G c p.1) a *ᵥ fiber G F p.1) p.2

/-- **The smoothed function** `f̃_c := (R̂_c f↑)↓` (§6.4, p.21). -/
def smooth (c : Fin q) (a : ℝ) (f : Col G q → ℝ) : Col G q → ℝ :=
  down G c (Rhat G c a (up G c f))

/-- The value of `F` at `(x, I)` when `x ∈ Ω^{-c}`. Every use below evaluates it at a background
recoloring `η^{v←c'}` with `c' ∈ A_v^{-c}(η)`, which lies in `Ω^{-c}`; the value `0` is never
reached there. -/
def bgExt {c : Fin q} (F : Bg G q c × IndSet G → ℝ) (x : V → Fin q) (I : IndSet G) : ℝ :=
  if h : MarkovMixing.IsProperColoring G x ∧ ∀ v, x v ≠ c then F (⟨x, h⟩, I) else 0

/-- `W_{v,c}(F) := ½ E_{(η,I)∼µ̂_c}[1{v ∈ V_ubl(I) ∖ I} p_v(η) E_v^{-c}((F(η^{v←c'}, I) − F(η, I))²)]`,
with `E_v^{-c}` the average over `c'` uniform in `A_v^{-c}(η)` (§7.2, p.25). -/
def Wvc (v : V) (c : Fin q) (F : Bg G q c × IndSet G → ℝ) : ℝ :=
  (1 / 2) * ∑ p : Bg G q c × IndSet G, muHat G c p *
    (if v ∈ ubl G p.2 ∧ v ∉ p.2.1 then
      pv G p.1.1 v * ((1 / ((availMinus G p.1.1 v c).card : ℝ)) *
        ∑ c' ∈ availMinus G p.1.1 v c, (bgExt G F (Function.update p.1.1 v c') p.2 - F p) ^ 2)
    else 0)

/-- `W_c := ∑_v W_{v,c}` (§7.2, p.25). -/
def Wc (c : Fin q) (F : Bg G q c × IndSet G → ℝ) : ℝ := ∑ v, Wvc G v c F

/-- `Ξ(f) := ∑_c ∑_u E_{η∼ρ_c} E_{c' uniform in A_u^{-c}(η)}
⟨f↑_{η^{u←c'}} − f↑_η, H_η(f↑_{η^{u←c'}} − f↑_η)⟩_{ν_η}` (§7.4, p.27). -/
def Xi (f : Col G q → ℝ) : ℝ :=
  ∑ c : Fin q, ∑ u : V, ∑ η : Bg G q c, rho G c η *
    ((1 / ((availMinus G η.1 u c).card : ℝ)) *
      ∑ c' ∈ availMinus G η.1 u c,
        ipEta G c η (fun I => bgExt G (up G c f) (Function.update η.1 u c') I - up G c f (η, I))
          (Heta G c η *ᵥ
            fun I => bgExt G (up G c f) (Function.update η.1 u c') I - up G c f (η, I)))

/-- `K := exp(Δ/(q − Δ − 1))` (§7.2, p.24). -/
def Kconst (Δ q : ℕ) : ℝ := Real.exp ((Δ : ℝ) / ((q : ℝ) - Δ - 1))

end

end HiddenHardCoreColoring.Mixing


