-- Prove2me | Definitions.Def_GrothendieckPD_Digits_FiniteGames
-- name    : GrothendieckPD_Digits_FiniteGames
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:46.376293+00:00
-- url     : https://prove2.me/theorems/842fa3e9-1cef-40a4-8a2e-0d272e7e1807
-- title:
--   §2: Hermite projection games $v_n(q)$, $v_\infty(q)$, the sets $\mathcal C$, $\mathcal Q$, and the coefficients $q_m$ of (4.1)
-- statement:
--   Let $\gamma_n$ be the standard Gaussian measure on $\mathbb R^n$ and let $\psi_k=\mathrm{He}_k/\sqrt{k!}$ be the normalized probabilists' Hermite polynomials. For measurable $f,g:\mathbb R^n\to\mathbb R$ write $c_m(f,g)=\langle \Pi_m f,\Pi_m g\rangle$, where $\Pi_m$ is the orthogonal projection of $L^2(\gamma_n)$ onto the span of the degree-$m$ Hermite polynomials; it is computed as the moment sum of the published definition `GrothendieckLB.pmInner`.
--
--   1. **Hermite projection game.** For a coefficient sequence $q=(q_m)_{m\ge 0}$ and $Q=\sum_m q_m\Pi_m$, the payoff of a pair is $\langle f,Qg\rangle=\sum_{m\ge0}q_m c_m(f,g)$, and
--   $$v_n(q)=\sup_{f,g:\mathbb R^n\to\{\pm1\}}\ \sum_{m\ge 0} q_m\,c_m(f,g),\qquad v_\infty(q)=\sup_{n}v_n(q),$$
--   the supremum over measurable $\pm1$-valued $f,g$.
--   2. **The Appendix B value (B.1).** $v_n^{(B.1)}(q)=\sup_{f,g}|\langle f,Qg\rangle|$ over measurable $f,g:\mathbb R^n\to[-1,1]$, and $v^{(B.1)}_\infty(q)=\sup_n v^{(B.1)}_n(q)$. This is a different quantity from $v_n(q)$; Lemma B.1 and Proposition B.2 use it.
--   3. **Odd functions and schemes.** $f$ is odd when $f(-x)=-f(x)$ for $\gamma_n$-almost every $x$. A distribution $\mu$ on pairs of measurable $\pm1$-valued functions is a jointly measurable random pair $(F,G)$ over a probability space (published `GrothendieckLB.MixedScheme`); its coefficients are $c_m(\mu)=\mathbb E_{(f,g)\sim\mu}c_m(f,g)$. The scheme is odd when every pair in it is odd.
--   4. **The sets of Theorem 2.2.** $\mathcal C$ is the set of sequences $c(\mu)$ over all $n$ and all odd schemes $\mu$ on $\mathbb R^n$; $\mathcal Q=\{q:\ q_1=1,\ |q_m|\le1\ \forall m,\ q_{2m}=0\ \forall m\ge 0\}$; $\langle c,q\rangle=\sum_m c_mq_m$; and the Krivine value of $c$ is $c_1-\sum_{\text{odd }m\ge3}|c_m|$.
--   5. **The certificate sequence (4.1).** $q_1=1$, $q_3=-0.654509751718$, $q_5=-0.159925966134$, $q_7=0.047785078787$, $q_9=0.086465878916$, $q_{11}=0.076371662489$, $q_{13}=0.072282834573$, $q_{15}=-0.004420811526$, $q_{17}=-0.058106583958$, $q_{19}=-0.041412929910$, $q_{21}=0.016668224599$, and $q_m=0$ otherwise; every decimal is exact.
--
--   These objects carry the duality theory of Section 2 and the lower-bound certificate of Appendix B.
--
--   **Formalization Note** Suprema are real `sSup`/`iSup`; every set involved is nonempty and bounded by $\sup_m|q_m|$ (Lemma 2.5), so no junk value arises for the bounded $q$ used in the mission. Pointwise oddness is impossible for $\pm1$-valued functions, so oddness is almost-everywhere.
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, §2.1 pp. 3–4 (OPT(Q), v_n, v_∞, H_µ, c(µ)), Theorem 2.2 p. 4 (𝒞, 𝒬), Eq. (B.1) p. 19, Eq. (4.1) p. 11

import Mathlib
import Definitions.Def_GrothendieckConstantDefs
import Definitions.Def_GrothendieckLB_pmInner
import Definitions.Def_GrothendieckLB_MixedScheme
open MeasureTheory ProbabilityTheory

namespace GrothendieckPD.Digits

/-- The normalized probabilists' Hermite polynomial `ψ_k = He_k / √(k!)` evaluated at `s`
(Heilman–Jones–Malavolta, STOC 2027 submission #820, §3, p. 7). `Polynomial.hermite k` is the
monic probabilists' Hermite polynomial `He_k`. -/
noncomputable def psi (k : ℕ) (s : ℝ) : ℝ :=
  Polynomial.aeval s (Polynomial.hermite k) / Real.sqrt (k.factorial : ℝ)

/-- The standard Gaussian measure `γ_n` on `ℝ^n` (§2.1, p. 3). -/
noncomputable def gaussMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 1

/-- `f : ℝ^n → ℝ` is odd `γ_n`-almost everywhere: `f(-x) = -f(x)` for a.e. `x`. Pointwise
oddness is impossible for a `±1`-valued function (it would force `f(0) = -f(0)`). -/
def IsOddAE {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ᵐ x ∂gaussMeasure n, f (-x) = -f x

/-- The Hermite coefficient `c_m(f,g) = ⟨Π_m f, Π_m g⟩` on `L²(γ_n)` (§2.1, p. 4), given by the
published moment sum `GrothendieckLB.pmInner`. -/
noncomputable def coeff {n : ℕ} (m : ℕ) (f g : (Fin n → ℝ) → ℝ) : ℝ :=
  GrothendieckLB.pmInner m f g

/-- The payoff `⟨f, Q g⟩ = ∑_{m ≥ 0} q_m ⟨Π_m f, Π_m g⟩` of the Hermite projection game
`Q = ∑_m q_m Π_m` (§2.1, p. 3). -/
noncomputable def gamePayoff {n : ℕ} (q : ℕ → ℝ) (f g : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑' m, q m * coeff m f g

/-- `v_n(q) = OPT(Q) = sup_{f,g : ℝ^n → {±1}} ∑_m q_m ⟨Π_m f, Π_m g⟩`, the supremum over
measurable `±1`-valued `f, g` (§2.1, p. 3). -/
noncomputable def gameValue (n : ℕ) (q : ℕ → ℝ) : ℝ :=
  sSup {s : ℝ | ∃ f g : (Fin n → ℝ) → ℝ, GrothendieckLB.IsSignFn f ∧
    GrothendieckLB.IsSignFn g ∧ s = gamePayoff q f g}

/-- `v_∞(q) = sup_{n ∈ ℕ} v_n(q)` (§2.1, p. 3). -/
noncomputable def gameValueInf (q : ℕ → ℝ) : ℝ :=
  ⨆ n : ℕ, gameValue n q

/-- A measurable function `ℝ^n → [-1, 1]`. -/
def IsUnitBounded {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  Measurable f ∧ ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1

/-- The Appendix B game value (B.1), p. 19: `v_n(q) = sup_{f,g} |⟨f, Q g⟩|` over measurable
`f, g : ℝ^n → [-1, 1]`. It differs from `gameValue` (Boolean `f, g`, no absolute value). -/
noncomputable def gameValueB1 (n : ℕ) (q : ℕ → ℝ) : ℝ :=
  sSup {s : ℝ | ∃ f g : (Fin n → ℝ) → ℝ, IsUnitBounded f ∧ IsUnitBounded g ∧
    s = |gamePayoff q f g|}

/-- `v_∞(q) = sup_n v_n(q)` for the (B.1) value (Lemma B.1, p. 19). -/
noncomputable def gameValueB1Inf (q : ℕ → ℝ) : ℝ :=
  ⨆ n : ℕ, gameValueB1 n q

/-- The coefficient sequence `c_m(µ) = E_{(f,g)∼µ} ⟨Π_m f, Π_m g⟩` of a distribution `µ` on pairs
of measurable `±1`-valued functions on `ℝ^n` (§2.1, p. 4), the distribution given as a jointly
measurable random pair (`GrothendieckLB.MixedScheme`). -/
noncomputable def schemeCoeff {n : ℕ} (S : GrothendieckLB.MixedScheme n) (m : ℕ) : ℝ :=
  ∫ ω, coeff m (S.F ω) (S.G ω) ∂S.μ

/-- Every pair in the support of the scheme consists of (a.e.) odd functions. -/
def IsOddScheme {n : ℕ} (S : GrothendieckLB.MixedScheme n) : Prop :=
  ∀ ω, IsOddAE (S.F ω) ∧ IsOddAE (S.G ω)

/-- The set `𝒞` of Theorem 2.2 (p. 4): all sequences `c(µ)`, `n ∈ ℕ`, `µ` a distribution on pairs
of odd functions `f, g : ℝ^n → {±1}`. -/
def CSet : Set (ℕ → ℝ) :=
  {c | ∃ n : ℕ, ∃ S : GrothendieckLB.MixedScheme n, IsOddScheme S ∧ c = schemeCoeff S}

/-- The set `𝒬 = {q ∈ ℓ∞ : q_1 = 1, |q_m| ≤ 1 for all m, q_{2m} = 0}` of Theorem 2.2 (p. 4);
`m` ranges over `ℕ ∋ 0`, so `q_0 = 0`. Boundedness by `1` makes `q ∈ ℓ∞` automatic. -/
def QSet : Set (ℕ → ℝ) :=
  {q | q 1 = 1 ∧ (∀ m, |q m| ≤ 1) ∧ ∀ m, q (2 * m) = 0}

/-- The pairing `⟨c, q⟩ = ∑_m c_m q_m` of `ℓ1` and `ℓ∞`. -/
noncomputable def pairing (c q : ℕ → ℝ) : ℝ :=
  ∑' m, c m * q m

/-- `c_1 - ∑_{odd m ≥ 3} |c_m|`; the odd indices `m ≥ 3` are `2k + 3`, `k ∈ ℕ`. -/
noncomputable def krivineValue (c : ℕ → ℝ) : ℝ :=
  c 1 - ∑' k, |c (2 * k + 3)|

/-- The coefficients `q_m` of Eq. (4.1), p. 11: zero except at the listed odd degrees, every
decimal exact. -/
noncomputable def qCert : ℕ → ℝ
  | 1 => 1
  | 3 => -654509751718 / 10 ^ 12
  | 5 => -159925966134 / 10 ^ 12
  | 7 => 47785078787 / 10 ^ 12
  | 9 => 86465878916 / 10 ^ 12
  | 11 => 76371662489 / 10 ^ 12
  | 13 => 72282834573 / 10 ^ 12
  | 15 => -4420811526 / 10 ^ 12
  | 17 => -58106583958 / 10 ^ 12
  | 19 => -41412929910 / 10 ^ 12
  | 21 => 16668224599 / 10 ^ 12
  | _ => 0

end GrothendieckPD.Digits


