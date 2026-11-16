-- Prove2me | Definitions.Def_QVolTransducer_Supplement_perpVec
-- name    : QVolTransducer_Supplement_perpVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:32:31.801795+00:00
-- url     : https://prove2.me/theorems/99da2fe4-e08c-495f-9a12-cecfac0f9412
-- title:
--   States and variables of §3: reflections, $|\bar\chi\rangle$, $|\bar\varphi\rangle$, $|\bar\pi(Y)\rangle$, $|\pi^{(a)}\rangle$, quantiles, $Y_j^\pm$
-- statement:
--   This file collects the objects of Sections 3.2 and 3.3.
--
--   1. A bidirectional canonical transducer $R$ **reflects through** an input-dependent state $|\psi\rangle=|\psi_x\rangle$ if, for every input $x$, $|\psi_x\rangle\overset{R}{\rightsquigarrow}|\psi_x\rangle$ and $|\varphi\rangle\overset{R}{\rightsquigarrow}-|\varphi\rangle$ for every $|\varphi\rangle\perp|\psi_x\rangle$.
--   2. For states with $0<|\langle\chi|\varphi\rangle|<1$: $|\bar\chi\rangle=\dfrac{|\varphi\rangle-\langle\chi|\varphi\rangle|\chi\rangle}{\||\varphi\rangle-\langle\chi|\varphi\rangle|\chi\rangle\|}$ and $|\bar\varphi\rangle=-\dfrac{|\chi\rangle-\langle\varphi|\chi\rangle|\varphi\rangle}{\||\chi\rangle-\langle\varphi|\chi\rangle|\varphi\rangle\|}\cdot\dfrac{\langle\chi|\varphi\rangle}{|\langle\chi|\varphi\rangle|}$.
--   3. For a distribution $\pi$ on a finite set $\Omega$ and $Y:\Omega\to[0,1]$ with mean $\mu_Y=\mathbb E_{\omega\sim\pi}[Y(\omega)]$:
--   $$|\bar\pi(Y)\rangle=\sum_{\omega\in\Omega}\sqrt{\pi(\omega)}\,\frac{\mu_Y-Y(\omega)}{\sqrt{\mu_Y(1-\mu_Y)}}\,|\omega\rangle,\qquad |\pi^{(a)}\rangle=\sum_{\omega\in\Omega}\sqrt{\frac{\pi(\omega)a(\omega)}{A}}\,|\omega\rangle,\ A=\mathbb E_\pi[a].$$
--   4. The amplitude-oracle output $\sqrt{1-y}\,|0\rangle+\sqrt y\,|1\rangle$, the threshold variable $X_t=\tfrac14+\tfrac12\mathbb 1(X\le t)$, the probability $\mathbb P_{x\sim\pi}[X(x)\le t]$, the quantile $Q_X(p)=\inf\{t\in[0,M]:\mathbb P_{x\sim\pi}[X(x)\le t]\ge p\}$, means, variances and total variation distances on $\Omega$.
--   5. For Theorem 3.9: $k=\lceil\log_2(580/\epsilon)\rceil$ and the dyadic truncations
--   $$Y_j^\pm(\omega)=\frac{B_j}4+\Big(1-\frac{B_j}2\Big)\cdot\frac{\pm(X(\omega)-\tilde m)}{a_j}\cdot\mathbb 1_{\pm(X(\omega)-\tilde m)\in(a_{j-1},a_j]},\quad a_j=2^j\tilde\sigma,\ a_{-1}=0,\ B_j=\min\{1,580/2^{2j}\}.$$
--
--   These are the states and random variables on which the rejection-sampling, mean- and quantile-estimation transducers act.
--
--   **Formalization Note** The implicit input of p.14 is explicit in `IsReflectionThrough` (a family of states indexed by the input set, one transducer for all inputs). The sign $\pm$ of $Y_j^\pm$ is a Boolean (`true` is $+$). The paper writes $\lceil\log(580/\epsilon)\rceil$; the proof (p.28) uses $2^k\ge580/\epsilon$ and $2^k\le1160/\epsilon$, i.e. the base-2 logarithm.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), §3.2, p.22 (PDF p.24) and §3.3, Theorems 3.6–3.9, pp.24–27 (PDF pp.26–29)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QVolTransducer_BiCanonical

namespace QVolTransducer.Supplement

open QAlgorithms

/-- A bidirectional canonical transducer `R` **reflects through** the input-dependent state
`|ψ⟩ = |ψ_x⟩` (Cornelissen, Apers, Gribling, *Improved quantum volume estimation with transducers and
amortized quantum walks*, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…),
pp.20–24, the hypothesis of Corollary 3.4 and Theorems 3.5–3.9): for every input `x ∈ D`,
`|ψ_x⟩ ⇝_{R(O_x)} |ψ_x⟩` and `|φ⟩ ⇝_{R(O_x)} −|φ⟩` for every `|φ⟩ ⊥ |ψ_x⟩`.

**Formalization Note** The implicit input of p.14 is explicit: `D` is the input set, `O x` the
oracle of input `x`, and `ψ x` the state for input `x`; the transducer is chosen before `x`. -/
def IsReflectionThrough {V H W D : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
    [Fintype W] [DecidableEq W] (R : BiCanonical V H W) (O : D → Matrix.unitaryGroup H ℂ)
    (ψ : D → EuclideanSpace ℂ V) : Prop :=
  ∀ x, Transduces (R.apply (O x)) (ψ x) (ψ x) ∧
    ∀ φ : EuclideanSpace ℂ V, inner ℂ (ψ x) φ = 0 → Transduces (R.apply (O x)) φ (-φ)

/-- The state `|χ̄⟩ = (|φ⟩ − ⟨χ|φ⟩|χ⟩)/‖|φ⟩ − ⟨χ|φ⟩|χ⟩‖` of §3.2 (arXiv:2609.40217, p.22), the
normalized component of `|φ⟩` orthogonal to `|χ⟩`. -/
noncomputable def annealPerpChi {V : Type*} [Fintype V] (χ φ : EuclideanSpace ℂ V) :
    EuclideanSpace ℂ V :=
  ((‖φ - inner ℂ χ φ • χ‖ : ℝ) : ℂ)⁻¹ • (φ - inner ℂ χ φ • χ)

/-- The state `|φ̄⟩ = −(|χ⟩ − ⟨φ|χ⟩|φ⟩)/‖|χ⟩ − ⟨φ|χ⟩|φ⟩‖ · ⟨χ|φ⟩/|⟨χ|φ⟩|` of §3.2
(arXiv:2609.40217, p.22), the normalized component of `|χ⟩` orthogonal to `|φ⟩`, with the
printed sign and phase. -/
noncomputable def annealPerpPhi {V : Type*} [Fintype V] (χ φ : EuclideanSpace ℂ V) :
    EuclideanSpace ℂ V :=
  -((inner ℂ χ φ / ((‖inner ℂ χ φ‖ : ℝ) : ℂ)) * ((‖χ - inner ℂ φ χ • φ‖ : ℝ) : ℂ)⁻¹) •
    (χ - inner ℂ φ χ • φ)

/-- The mean `µ_Y = E_{ω∼π}[Y(ω)] = Σ_ω π(ω) Y(ω)` of a random variable on a finite set
(arXiv:2609.40217, §3.3, pp.24–27). -/
noncomputable def finMean {Ω : Type*} [Fintype Ω] (π : Ω → ℝ) (Y : Ω → ℝ) : ℝ :=
  ∑ ω, π ω * Y ω

/-- The variance `Var_{ω∼π}[Y] = Σ_ω π(ω) (Y(ω) − µ_Y)²` on a finite set (arXiv:2609.40217,
Theorem 3.9, p.27). -/
noncomputable def finVar {Ω : Type*} [Fintype Ω] (π : Ω → ℝ) (Y : Ω → ℝ) : ℝ :=
  ∑ ω, π ω * (Y ω - finMean π Y) ^ 2

/-- The total variation distance `‖π − π̃‖_TV = ½ Σ_ω |π(ω) − π̃(ω)|` of two distributions on a
finite set (arXiv:2609.40217, Theorem 3.9, p.27). -/
noncomputable def finTV {Ω : Type*} [Fintype Ω] (π π' : Ω → ℝ) : ℝ :=
  (1 / 2) * ∑ ω, |π ω - π' ω|

/-- The vector `|π̄(Y)⟩ = Σ_ω √π(ω) · (µ_Y − Y(ω))/√(µ_Y(1 − µ_Y)) |ω⟩`, `µ_Y = E_{ω∼π}[Y(ω)]`,
of a random variable `Y : Ω → [0, 1]` (arXiv:2609.40217, Theorem 3.8, p.26; it is `|π̄⟩` of
Theorem 3.6 with `Y = a`, p.24, and of Theorem 3.7 with `Y = X`, p.25, and `|π̄(Y)⟩` of Theorem 3.9
with `π̃` in place of `π`, p.27). -/
noncomputable def perpVec {Ω : Type*} [Fintype Ω] (π : Ω → ℝ) (Y : Ω → ℝ) : EuclideanSpace ℂ Ω :=
  WithLp.toLp 2 (fun ω => ((Real.sqrt (π ω) * (finMean π Y - Y ω) /
    Real.sqrt (finMean π Y * (1 - finMean π Y)) : ℝ) : ℂ))

/-- The rejection-sampled state `|π^(a)⟩ = Σ_ω √(π(ω) a(ω)/A) |ω⟩`, `A = E_{ω∼π}[a(ω)]`
(arXiv:2609.40217, Theorem 3.6, p.24). -/
noncomputable def rejVec {Ω : Type*} [Fintype Ω] (π : Ω → ℝ) (a : Ω → ℝ) : EuclideanSpace ℂ Ω :=
  WithLp.toLp 2 (fun ω => ((Real.sqrt (π ω * a ω / finMean π a) : ℝ) : ℂ))

/-- The qubit state `√(1 − y) |0⟩ + √y |1⟩ ∈ ℂ²` written by an amplitude oracle with value `y`
(arXiv:2609.40217, Theorems 3.6–3.9: `|ω⟩|0⟩ ⇝ |ω⟩(√y(ω) |1⟩ + √(1 − y(ω)) |0⟩)`). -/
noncomputable def coinVec (y : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  ((Real.sqrt (1 - y) : ℝ) : ℂ) • ket 0 + ((Real.sqrt y : ℝ) : ℂ) • ket 1

/-- The threshold variable `X_t := 1/4 + 1(X ≤ t)/2` (arXiv:2609.40217, Theorem 3.8, p.26). -/
noncomputable def threshVar {Ω : Type*} (X : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  1 / 4 + (if X ω ≤ t then 1 else 0) / 2

open Classical in
/-- The probability `P_{x∼π}[X(x) ≤ t] = Σ_{ω : X(ω) ≤ t} π(ω)` on a finite set
(arXiv:2609.40217, Theorem 3.8, p.26). -/
noncomputable def probLe {Ω : Type*} [Fintype Ω] (π : Ω → ℝ) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => X ω ≤ t), π ω

/-- The quantile function `Q_X(p) := inf{t ∈ [0, M] : P_{x∼π}[X(x) ≤ t] ≥ p}` of a random variable
`X : Ω → [0, M]` on a finite set (arXiv:2609.40217, Theorem 3.8, p.26). For `p ≤ 1` the set
contains `t = M`, so the infimum is over a nonempty set bounded below by `0`. -/
noncomputable def quantileFin {Ω : Type*} [Fintype Ω] (π : Ω → ℝ) (X : Ω → ℝ) (M p : ℝ) : ℝ :=
  sInf {t : ℝ | t ∈ Set.Icc 0 M ∧ p ≤ probLe π X t}

/-- The number `k = ⌈log₂(580/ϵ)⌉` of dyadic scales in Theorem 3.9 (arXiv:2609.40217, p.27).

**Formalization Note** The paper writes `⌈log(580/ϵ)⌉`; the proof (p.28) uses
`a_k = 2^k σ̃ ≥ 580 σ̃/ϵ` and `2^k ≤ 1160/ϵ`, which is the base-2 logarithm. -/
noncomputable def meanEstK (ϵ : ℝ) : ℕ :=
  ⌈Real.logb 2 (580 / ϵ)⌉₊

/-- The dyadic truncation `Y_j^±(ω) := B_j/4 + (1 − B_j/2) · ±(X(ω) − m̃)/a_j ·
1_{±(X(ω) − m̃) ∈ (a_{j−1}, a_j]}` of Theorem 3.9 (arXiv:2609.40217, p.27), with
`a_j = 2^j σ̃` for `j ≥ 0`, `a_{−1} = 0` and `B_j = min{1, 580/2^{2j}}`. The sign `±` is `s`:
`true` is `+` and `false` is `−`. -/
noncomputable def meanEstY {Ω : Type*} (X : Ω → ℝ) (mt σt : ℝ) (j : ℕ) (s : Bool) (ω : Ω) : ℝ :=
  let B : ℝ := min 1 (580 / 2 ^ (2 * j))
  let aj : ℝ := 2 ^ j * σt
  let ajm : ℝ := if j = 0 then 0 else 2 ^ (j - 1) * σt
  let u : ℝ := (if s then 1 else -1) * (X ω - mt)
  B / 4 + (1 - B / 2) * (u / aj) * (if ajm < u ∧ u ≤ aj then 1 else 0)

end QVolTransducer.Supplement


