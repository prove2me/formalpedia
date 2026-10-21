-- Prove2me | Definitions.Def_PowerFIPP_Charact_Model
-- name    : PowerFIPP_Charact_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:41.736089+00:00
-- url     : https://prove2.me/theorems/0589e788-e730-4fce-8147-942d3d02d39e
-- title:
--   §2–§3.2 — the market, (A_C), (A_D), 𝒞_0, 𝒬_M, Γ^Q_𝒞 (Def. 2.1), Q-FIPP (Def. 2.2), U, U^V, Φ^M_p (3.8) and conditions (i)–(iii) of Theorem 3.3
-- statement:
--   This file sets up the model of §2 and the objects of §3.1–3.2 of Bo, Capponi and Zhou, on top of the calculus layer `PowerFIPP.Charact.Calculus`.
--
--   1. **Market.** An $\mathbb R^n$-valued return process $R$ with differential characteristics $(b,c,F)$ under $P$ (2.2), a scalar process $D$ with characteristics $(b^D,c^D,F^D)$ under $P$, and a constraint set-valued process $\mathcal C_t(\omega)\subseteq\mathbb R^n$.
--   2. **Standing assumptions.** $P$ is a probability measure; $\mathbb F$ is right-continuous and complete, and $\mathcal F_0$ is $P$-trivial; $R_0=0$ almost surely; $R$ and $D$ are càdlàg semimartingales with the stated characteristics; $\mathcal C$ is predictable (its graph is measurable for the predictable $\sigma$-algebra times the Borel sets).
--   3. **(A_C)**: every $\mathcal C_t(\omega)$ is compact, convex and contains $0$. **(A_D)**: (i) $(e^v-1-h^D(v))*\nu^D$ or (ii) $e^v\mathbf 1_{\{v>1\}}*\nu^D$ has finite variation, i.e. the corresponding $dt$-integral of the absolute value is finite on every $[0,t]$, $P$-a.s.
--   4. $\mathcal C_0=\{\pi:F(\{u\ne0:\pi^\top u+1<0\})=0\}$ (2.9).
--   5. Lemma 3.1's processes (3.3): $V=\int_0^\cdot\big(b^D_s+\tfrac{c^D_s}{2}+\int(e^v-1-h^D(v))F^D_s(dv)\big)ds$ and $M=D^c+(e^v-1)*(\mu^D-\nu^D)$; the density process $\mathcal E(M)$, and $Q\in\mathcal Q_M$ (2.3): $Q\sim P$ with $dQ/dP|_{\mathcal F_t}=\mathcal E_t(M)$.
--   6. The random fields $U_t(x)=e^{D_t}x^p/p$ (3.1), $U_0(x)=e^{D_0}x^p/p$ and $U^V_t(x)=U_0(x)\mathcal E_t(V)$ (3.5), for $x>0$.
--   7. **Definition 2.1.** $\Gamma^Q_{\mathcal C}$ (for a field $U^Q$): predictable, $\mathcal C$-constrained, $R$-integrable $\pi$ with $\pi^\top\Delta R\ge-1$ $Q$-a.s. and $U^Q_t(x\mathcal E_t(\pi\cdot R))^-$ of class (DL) under $Q$ for every $x>0$.
--   8. **Definition 2.2.** $U^Q$ is a $Q$-FIPP with optimal $\pi^*\in\Gamma^Q_{\mathcal C}$ if $x\mapsto U^Q_t(x)$ is concave and increasing $Q$-a.s., $U^Q(X^{\pi,x})$ is a $Q$-supermartingale for every $x>0$ and $\pi\in\Gamma^Q_{\mathcal C}$, and $U^Q(X^{\pi^*,x})$ is a $Q$-martingale, where $X^{\pi,x}=x\mathcal E(\pi\cdot R)$.
--   9. **(3.8).** For $\pi\in\mathcal C_0$,
--   $$\Phi^M_p(\pi)=\pi^\top b^M+\frac{p-1}{2}\pi^\top c\pi+\int\Big\{p^{-1}(1+\pi^\top u)^p-p^{-1}-\pi^\top h(u)\Big\}F^M(du)\in\mathbb R\cup\{\pm\infty\},$$
--   and $\sup_{\pi\in\mathcal C\cap\mathcal C_0}\Phi^M_p(\pi)$.
--   10. **Conditions (i)–(iii) of Theorem 3.3.** (i) $\mathcal E\big(\beta^M\cdot R^{M,c}+\overline W^M(u)*(\mu-\nu^M)\big)\mathcal E(M)$ is a $P$-martingale, with $\beta^M=p\pi^*$ and $\overline W^M_t(u)=\{1+(\pi^*_t)^\top u\}^p-1$; (ii) $\Phi^M_p(\pi^*)=\sup_{\mathcal C\cap\mathcal C_0}\Phi^M_p$; (iii) equation (3.7), $\sup_{\mathcal C\cap\mathcal C_0}\Phi^M_p+p^{-1}\{b^D+c^D/2+(e^v-1-h^D(v))*F^D\}=0$; (ii) and (iii) $P(d\omega)\otimes dt$-a.s.
--
--   These definitions carry the paper's characterization of power forward performance processes.
--
--   **Formalization Note** Fields take values in $[-\infty,\infty)$: at wealth $0$ (reached when $\pi^\top\Delta R=-1$) they take their limit value, $0$ for $p>0$ and $-\infty$ for $p<0$, so such a strategy fails the class (DL) clause when $p<0$; the (super)martingale clauses use the real values, which are exact wherever wealth is positive. The stochastic integral $\pi\cdot R$ is computed with the $P$-characteristics of $R$; for $Q\sim P$ it is the same process under $Q$. $(b^M,F^M)$ and $R^{M,c}$ enter the theorems as the differential characteristics and continuous martingale part of $R$ under $Q^M$ (equal $Q^M\otimes dt$-a.e. to (2.7)–(2.8) by Jacod–Shiryaev III.3.24). $\Phi^M_p$ is computed in the extended reals as $\int g^+-\int g^-$, at most one of which is infinite for $\pi\in\mathcal C_0$; at $1+\pi^\top u=0$ the integrand is $-\infty$ when $p<0$. $U_0$ uses $D_0(\omega)$ pathwise ($D_0$ is a.s. constant). The integrals in (i) are required to exist; the $F^D$-integral in (iii) is required to be finite.
-- source:
--   Bo, Capponi & Zhou, Power forward performance in semimartingale markets with stochastic integrated factors, arXiv:1811.11899v4, pp. 4–9: §2 (2.1)–(2.3), Definitions 2.1–2.2, (2.7)–(2.9), (A_C), (A_D); §3 (3.1), (3.3)–(3.9), Theorem 3.3 (i)–(iii)

import Mathlib
import Definitions.Def_PowerFIPP_Charact_Calculus

namespace PowerFIPP.Charact

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

/-! # The market model, admissible strategies, FIPP, and the objects of Theorem 3.3
(Bo–Capponi–Zhou, arXiv:1811.11899v4, §2 pp. 4–7 and §3.1–3.2 pp. 8–9). -/

/-- The data of the model: the `n`-dimensional return process `R` with differential
characteristics `(b, c, F)` (2.2), the scalar process `D` with differential characteristics
`(b^D, c^D, F^D)` (p. 7), and the constraint set-valued process `C = 𝒞` (Definition 2.1). -/
structure Market (Ω : Type*) (n : ℕ) where
  /-- the return process `R` -/
  R : ℝ≥0 → Ω → Fin n → ℝ
  /-- drift rate `b` of `R` under `P` -/
  b : ℝ≥0 → Ω → Fin n → ℝ
  /-- diffusion rate `c` of `R` (also `c^M`) -/
  c : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ
  /-- jump kernel `F` of `R` under `P` -/
  F : ℝ≥0 → Ω → Measure (Fin n → ℝ)
  /-- the scalar factor `D` of the power random field -/
  D : ℝ≥0 → Ω → ℝ
  /-- drift rate `b^D` of `D` -/
  bD : ℝ≥0 → Ω → ℝ
  /-- diffusion rate `c^D` of `D` -/
  cD : ℝ≥0 → Ω → ℝ
  /-- jump kernel `F^D` of `D` -/
  FD : ℝ≥0 → Ω → Measure ℝ
  /-- the constraint sets `𝒞_t(ω)` -/
  C : ℝ≥0 → Ω → Set (Fin n → ℝ)

namespace Market

variable {Ω : Type*} {n : ℕ}

/-- `D` as an `ℝ¹`-valued process. -/
def Dvec (mkt : Market Ω n) : ℝ≥0 → Ω → Fin 1 → ℝ := fun t ω => ![mkt.D t ω]

/-- `b^D` as an `ℝ¹`-valued process. -/
def bDvec (mkt : Market Ω n) : ℝ≥0 → Ω → Fin 1 → ℝ := fun t ω => ![mkt.bD t ω]

/-- `c^D` as a `1 × 1` matrix. -/
def cDmat (mkt : Market Ω n) : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ := fun t ω => !![mkt.cD t ω]

/-- `F^D` transported to `ℝ¹`. -/
noncomputable def FDvec (mkt : Market Ω n) : ℝ≥0 → Ω → Measure (Fin 1 → ℝ) :=
  fun t ω => (mkt.FD t ω).map fun v => ![v]

/-- **Standing assumptions** of §2 (pp. 4–7):
1. `P` is a probability measure and `𝔽` satisfies the usual conditions (right-continuity,
   completeness: every `P`-null set lies in `𝓕_0`), with `𝓕_0` `P`-trivial (p. 4);
2. `R` starts at zero (as in (2.1)) and is a càdlàg semimartingale with differential
   characteristics `(b, c, F)` under `P` ((2.1)–(2.2), pp. 4–5);
3. `D` is a càdlàg semimartingale with differential characteristics `(b^D, c^D, F^D)` under `P`
   (p. 7);
4. `𝒞` is a predictable set-valued process: its graph is measurable for the product of the
   predictable σ-algebra and the Borel σ-algebra of `ℝⁿ` (p. 5). -/
def Standing [MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (mkt : Market Ω n) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ t : ℝ≥0, ℱ t = ⨅ (s : ℝ≥0) (_ : t < s), ℱ s) ∧
  (∀ A : Set Ω, P A = 0 → MeasurableSet[ℱ 0] A) ∧
  (∀ A : Set Ω, MeasurableSet[ℱ 0] A → P A = 0 ∨ P A = 1) ∧
  (∀ᵐ ω ∂P, mkt.R 0 ω = 0) ∧
  IsDiffChar P ℱ mkt.R mkt.b mkt.c mkt.F ∧
  IsDiffChar P ℱ mkt.Dvec mkt.bDvec mkt.cDmat mkt.FDvec ∧
  @MeasurableSet ((ℝ≥0 × Ω) × (Fin n → ℝ)) (@Prod.instMeasurableSpace _ _ ℱ.predictable _)
    {x | x.2 ∈ mkt.C x.1.1 x.1.2}

end Market

variable {Ω : Type*} {n : ℕ}

/-- **Assumption (A_C)** (p. 7): for every `(t, ω)`, `𝒞_t(ω)` is compact, convex and contains
the origin. -/
def AC (mkt : Market Ω n) : Prop :=
  ∀ t ω, IsCompact (mkt.C t ω) ∧ Convex ℝ (mkt.C t ω) ∧ (0 : Fin n → ℝ) ∈ mkt.C t ω

/-- **Assumption (A_D)** (p. 7): (i) `(e^v - 1 - h^D(v)) ∗ ν^D ∈ 𝒱^P` or (ii)
`e^v 1_{v > 1} ∗ ν^D ∈ 𝒱^P`. Since `ν^D(dt, dv) = F^D_t(dv) dt`, the integral process is
continuous and adapted, and it belongs to `𝒱^P` iff the integral of the absolute value is
pathwise finite on every `[0, t]`, `P`-a.s. -/
def AD [MeasurableSpace Ω] (P : Measure Ω) (mkt : Market Ω n) : Prop :=
  (∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∫⁻ s in Set.Icc 0 t,
      ∫⁻ v, ENNReal.ofReal |Real.exp v - 1 - truncD v| ∂mkt.FD s ω ∂leb < ∞) ∨
  (∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∫⁻ s in Set.Icc 0 t,
      ∫⁻ v, (Set.Ioi (1 : ℝ)).indicator (fun v => ENNReal.ofReal (Real.exp v)) v ∂mkt.FD s ω
        ∂leb < ∞)

/-- The budget-constraint set `𝒞_0 = {π ∈ ℝⁿ : F({u ∈ ℝⁿ₀ : π^⊤u + 1 < 0}) = 0}` (2.9), for a
jump kernel `F` (with `F^M` in place of `F` it is `𝒞^M_0`). -/
def Cnull (F : ℝ≥0 → Ω → Measure (Fin n → ℝ)) (t : ℝ≥0) (ω : Ω) : Set (Fin n → ℝ) :=
  {π | F t ω {u | u ≠ 0 ∧ π ⬝ᵥ u + 1 < 0} = 0}

/-- The process `V = B^D + C^D/2 + {e^v - 1 - h^D(v)} ∗ ν^D` of (3.3):
`V_t = ∫_0^t (b^D_s + c^D_s/2 + ∫ (e^v - 1 - h^D(v)) F^D_s(dv)) ds`. -/
noncomputable def V (mkt : Market Ω n) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Set.Icc 0 t,
    (mkt.bD s ω + mkt.cD s ω / 2 + ∫ v, (Real.exp v - 1 - truncD v) ∂mkt.FD s ω) ∂leb

/-- The process `M = D^c + (e^v - 1) ∗ (μ^D - ν^D)` of (3.3), given through its two terms: `Dc` is
the continuous martingale part of `D` under `P` and `J = (e^v - 1) ∗ (μ^D - ν^D)` under `P`. -/
def IsLemma31MV [MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (mkt : Market Ω n) (M Dc J : ℝ≥0 → Ω → ℝ) : Prop :=
  IsContPart P ℱ mkt.Dvec mkt.bDvec (fun t ω => ![Dc t ω]) ∧
  IsCompJumpIntegral P ℱ mkt.Dvec (fun _ _ v => Real.exp (v 0) - 1) J ∧
  ∀ t ω, M t ω = Dc t ω + J t ω

/-- The density process `𝓔(M)`, with `⟨M^c⟩ = ⟨D^c⟩ = ∫ c^D ds`. -/
noncomputable def EM (mkt : Market Ω n) (M : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  stochExp M fun t ω => ∫ s in Set.Icc 0 t, mkt.cD s ω ∂leb

/-- `Q ∈ 𝒬_M` (2.3): `Q` is a probability measure equivalent to `P` with
`dQ/dP |_{𝓕_t} = 𝓔(M)_t` for every `t ≥ 0`. -/
def IsQM [MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (mkt : Market Ω n) (M : ℝ≥0 → Ω → ℝ) (Q : Measure Ω) : Prop :=
  IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
  ∀ (t : ℝ≥0) (A : Set Ω), MeasurableSet[ℱ t] A →
    Q A = ∫⁻ ω in A, ENNReal.ofReal (EM mkt M t ω) ∂P

/-- The power random field (3.1), `U_t(x) = e^{D_t} x^p / p` for `x > 0`, extended to `x ≤ 0`
(wealth `0`, reached when `π^⊤ΔR = -1`) by its limit as `x ↓ 0`: `0` if `p > 0`, `-∞` if `p < 0`. -/
noncomputable def U (mkt : Market Ω n) (p : ℝ) (t : ℝ≥0) (x : ℝ) (ω : Ω) : EReal :=
  if 0 < x then ((Real.exp (mkt.D t ω) * x ^ p / p : ℝ) : EReal) else if 0 < p then 0 else ⊥

/-- The initial utility `U_0(x) = x^p e^{D_0} / p` (3.4), taken pathwise with `D_0(ω)`
(`D_0` is `P`-a.s. constant since `𝓕_0` is `P`-trivial). -/
noncomputable def U0 (mkt : Market Ω n) (p : ℝ) (x : ℝ) (ω : Ω) : ℝ :=
  Real.exp (mkt.D 0 ω) * x ^ p / p

/-- The random field `U^V_t(x) = U_0(x) 𝓔_t(V)` (3.5) for `x > 0` (`V` is continuous of finite
variation, `⟨V^c⟩ = 0`), with the same convention as `U` at `x ≤ 0`. -/
noncomputable def UV (mkt : Market Ω n) (p : ℝ) (t : ℝ≥0) (x : ℝ) (ω : Ω) : EReal :=
  if 0 < x then ((U0 mkt p x ω * stochExp (V mkt) (fun _ _ => 0) t ω : ℝ) : EReal)
  else if 0 < p then 0 else ⊥

/-- The wealth factor `𝓔(π · R)` for the stochastic integral `I = π · R`
(`⟨(π · R)^c⟩ = ∫ π^⊤ c π ds`); the wealth is `X^{π,x} = x 𝓔(π · R)`. -/
noncomputable def wealthExp (mkt : Market Ω n) (π : ℝ≥0 → Ω → Fin n → ℝ) (I : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ :=
  stochExp I (qv mkt.c π)

/-- **Definition 2.1**, the class `Γ^Q_𝒞` of admissible strategies associated with the random
field `Uf` under `Q`: `π` is predictable, `𝒞`-constrained at every `(t, ω)`, `R`-integrable, with
`π^⊤ΔR ≥ -1` `Q`-a.s., and for every `x > 0` the negative part `U_t(x 𝓔_t(π · R))^-` is of class
(DL) under `Q`. The stochastic integral `π · R` is computed with the `P`-characteristics of `R`:
for `Q ∼ P` it is the same process under `Q`. -/
def Gamma [MeasurableSpace Ω] (Q P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (mkt : Market Ω n) (Uf : ℝ≥0 → ℝ → Ω → EReal) : Set (ℝ≥0 → Ω → Fin n → ℝ) :=
  {π | IsStronglyPredictable ℱ π ∧ (∀ t ω, π t ω ∈ mkt.C t ω) ∧
    (∃ I, IsStochIntegral P ℱ mkt.R mkt.b mkt.c π I) ∧
    (∀ᵐ ω ∂Q, ∀ t, -1 ≤ π t ω ⬝ᵥ jump mkt.R t ω) ∧
    ∀ I, IsStochIntegral P ℱ mkt.R mkt.b mkt.c π I → ∀ x : ℝ, 0 < x →
      ClassDL Q ℱ fun t ω => (-Uf t (x * wealthExp mkt π I t ω) ω).toENNReal}

/-- **Definition 2.2** (FIPP): the random field `Uf` is a `Q`-FIPP with optimal trading strategy
`πstar ∈ Γ^Q_𝒞` if
(i) `Q`-a.s., for every `t`, `x ↦ Uf_t(x)` is concave and increasing on `(0, ∞)`;
(ii) for every `x > 0` and `π ∈ Γ^Q_𝒞`, `Uf(X^{π,x}) = (Uf_t(x 𝓔_t(π · R)))_{t ≥ 0}` is a
`Q`-supermartingale;
(iii) for every `x > 0`, `Uf(X^{π*,x})` is a `Q`-martingale.
`Uf` is real-valued on `(0, ∞)` for the fields `U` and `U^V` used here; the real processes are
taken through `EReal.toReal`, which is exact wherever the wealth is positive. -/
def IsFIPP [MeasurableSpace Ω] (Q P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (mkt : Market Ω n) (Uf : ℝ≥0 → ℝ → Ω → EReal) (πstar : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  πstar ∈ Gamma Q P ℱ mkt Uf ∧
  (∀ᵐ ω ∂Q, ∀ t, ConcaveOn ℝ (Set.Ioi 0) (fun x => (Uf t x ω).toReal) ∧
    MonotoneOn (fun x => (Uf t x ω).toReal) (Set.Ioi 0)) ∧
  (∀ x : ℝ, 0 < x → ∀ π ∈ Gamma Q P ℱ mkt Uf, ∀ I, IsStochIntegral P ℱ mkt.R mkt.b mkt.c π I →
    Supermartingale (fun t ω => (Uf t (x * wealthExp mkt π I t ω) ω).toReal) ℱ Q) ∧
  (∀ x : ℝ, 0 < x → ∀ I, IsStochIntegral P ℱ mkt.R mkt.b mkt.c πstar I →
    Martingale (fun t ω => (Uf t (x * wealthExp mkt πstar I t ω) ω).toReal) ℱ Q)

/-- The integrand of (3.8), `g_π(u) = p^{-1}(1 + π^⊤u)^p - p^{-1} - π^⊤h(u)`, `EReal`-valued:
at `1 + π^⊤u = 0` it is `-∞` for `p < 0` (`(0)^p = +∞`) and `-p^{-1} - π^⊤h(u)` for `p > 0`. On
`{1 + π^⊤u < 0}` (an `F`-null set for `π ∈ 𝒞_0`) the value is irrelevant. -/
noncomputable def phiIntegrand (p : ℝ) (π u : Fin n → ℝ) : EReal :=
  if 1 + π ⬝ᵥ u = 0 ∧ p < 0 then ⊥
  else ((p⁻¹ * (1 + π ⬝ᵥ u) ^ p - p⁻¹ - π ⬝ᵥ trunc u : ℝ) : EReal)

/-- **(3.8)** `Φ^M_p(π) = π^⊤b^M + ((p-1)/2) π^⊤cπ + {p^{-1}(1 + π^⊤u)^p - p^{-1} - π^⊤h(u)} ∗ F^M`
in `ℝ ∪ {±∞}`. The `F^M`-integral is `∫ g⁺ - ∫ g⁻` in `EReal`; for `π ∈ 𝒞_0` at most one of the
two is infinite (`g ≤ 0` near the origin and bounded below / above off it, Nutz 2012b, Lemma 5.3),
so `Φ^M_p(π) ∈ ℝ ∪ {sign(p) ∞}` (p. 10). -/
noncomputable def Phi (p : ℝ) (bM : Fin n → ℝ) (c : Matrix (Fin n) (Fin n) ℝ)
    (FM : Measure (Fin n → ℝ)) (π : Fin n → ℝ) : EReal :=
  ((π ⬝ᵥ bM + (p - 1) / 2 * (π ⬝ᵥ (c *ᵥ π)) : ℝ) : EReal) +
    (((∫⁻ u, (phiIntegrand p π u).toENNReal ∂FM : ℝ≥0∞) : EReal) -
      ((∫⁻ u, (-phiIntegrand p π u).toENNReal ∂FM : ℝ≥0∞) : EReal))

/-- `sup_{π ∈ 𝒞_t(ω) ∩ 𝒞_0(t, ω)} Φ^M_p(π)` (in `EReal`), with `𝒞_0` built from `F` as in (3.7). -/
noncomputable def supPhi (mkt : Market Ω n) (p : ℝ) (bM : ℝ≥0 → Ω → Fin n → ℝ)
    (FM : ℝ≥0 → Ω → Measure (Fin n → ℝ)) (t : ℝ≥0) (ω : Ω) : EReal :=
  ⨆ π ∈ mkt.C t ω ∩ Cnull mkt.F t ω, Phi p (bM t ω) (mkt.c t ω) (FM t ω) π

/-- `W̄^M_t(u) = {1 + (π*_t)^⊤u}^p - 1` (p. 9). At `1 + (π*)^⊤u = 0` the value is `-1`, the right
value for `p > 0`; for `p < 0` and `π* ∈ Γ` no jump of `R` reaches that set, `P`-a.s. -/
noncomputable def Wbar (p : ℝ) (πstar : ℝ≥0 → Ω → Fin n → ℝ) (t : ℝ≥0) (ω : Ω)
    (u : Fin n → ℝ) : ℝ :=
  (1 + πstar t ω ⬝ᵥ u) ^ p - 1

/-- `W^π_t(u) = p^{-1}(1 + π_t^⊤u)^p - p^{-1}` (3.9), with Lean's `0^p = 0` at `1 + π^⊤u = 0`;
for `π ∈ Γ` and `p < 0` no jump of `R` reaches that set, a.s. -/
noncomputable def Wpi (p : ℝ) (π : ℝ≥0 → Ω → Fin n → ℝ) (t : ℝ≥0) (ω : Ω) (u : Fin n → ℝ) : ℝ :=
  p⁻¹ * (1 + π t ω ⬝ᵥ u) ^ p - p⁻¹

/-- **Condition (i)** of Theorem 3.3: with `L1 = β^M · R^{M,c}` (`β^M = p π*`, under `Q^M`) and
`L2 = W̄^M(u) ∗ (μ - ν^M)` (under `Q^M`), the process `𝓔(L1 + L2) 𝓔(M)` is a `P`-martingale.
The integrals are required to exist (they are unique when they do). -/
def cond_i [MeasurableSpace Ω] (P Q : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (mkt : Market Ω n) (p : ℝ) (M : ℝ≥0 → Ω → ℝ) (RMc : ℝ≥0 → Ω → Fin n → ℝ)
    (πstar : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  ∃ L1 L2 : ℝ≥0 → Ω → ℝ,
    IsContIntegral Q ℱ RMc mkt.c (fun t ω => p • πstar t ω) L1 ∧
    IsCompJumpIntegral Q ℱ mkt.R (Wbar p πstar) L2 ∧
    Martingale (fun t ω => stochExp (fun s ω' => L1 s ω' + L2 s ω')
        (qv mkt.c fun s ω' => p • πstar s ω') t ω * EM mkt M t ω) ℱ P

/-- **Condition (ii)** of Theorem 3.3: `Φ^M_p(π*) = sup_{π ∈ 𝒞 ∩ 𝒞_0} Φ^M_p(π)`, `μ(dω) ⊗ dt`-a.s. -/
def cond_ii [MeasurableSpace Ω] (μ : Measure Ω) (mkt : Market Ω n) (p : ℝ)
    (bM : ℝ≥0 → Ω → Fin n → ℝ) (FM : ℝ≥0 → Ω → Measure (Fin n → ℝ))
    (πstar : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  ∀ᵐ x ∂(μ.prod leb),
    Phi p (bM x.2 x.1) (mkt.c x.2 x.1) (FM x.2 x.1) (πstar x.2 x.1) = supPhi mkt p bM FM x.2 x.1

/-- **Condition (iii)** of Theorem 3.3, equation (3.7), `μ(dω) ⊗ dt`-a.s.:
`sup_{π ∈ 𝒞 ∩ 𝒞_0} Φ^M_p(π) + p^{-1}{b^D + c^D/2 + (e^v - 1 - h^D(v)) ∗ F^D} = 0`, with the
`F^D`-integral required to exist. -/
def cond_iii [MeasurableSpace Ω] (μ : Measure Ω) (mkt : Market Ω n) (p : ℝ)
    (bM : ℝ≥0 → Ω → Fin n → ℝ) (FM : ℝ≥0 → Ω → Measure (Fin n → ℝ)) : Prop :=
  ∀ᵐ x ∂(μ.prod leb),
    Integrable (fun v => Real.exp v - 1 - truncD v) (mkt.FD x.2 x.1) ∧
    supPhi mkt p bM FM x.2 x.1 +
      ((p⁻¹ * (mkt.bD x.2 x.1 + mkt.cD x.2 x.1 / 2 +
        ∫ v, (Real.exp v - 1 - truncD v) ∂mkt.FD x.2 x.1) : ℝ) : EReal) = 0

end PowerFIPP.Charact


