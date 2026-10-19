-- Prove2me | Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems
-- name    : TwoStageSRO_AsymOpt_SampleProblems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:44.034981+00:00
-- url     : https://prove2.me/theorems/39173884-fe01-4f12-946f-05d56e66aefd
-- title:
--   §2–§4.2, pp. 6–17 — (SAA), (SRO), linear decision rules, (SP), (MP), Q^C_ϵ (Definition 1), Ξ*, D, η^C and L
-- statement:
--   Let $\xi^1,\xi^2,\dots$ be a sample path in $\mathbb R^d$, $N\ge 1$ a sample size and $\epsilon_N\ge0$ a radius, for the problem data of (OPT).
--
--   1. **Sample average approximation** (SAA): $\hat V^{SAA}_N(x)=c^\top x+\frac1N\sum_{i=1}^N Q(x,\xi^i)$ and $\hat v^{SAA}_N=\inf_x\hat V^{SAA}_N(x)$.
--   2. **Sample robust optimization** (SRO): with the uncertainty sets $U^i_N=\{\zeta\in\Xi:\|\zeta-\xi^i\|\le\epsilon_N\}$,
--   $$\hat V^{SRO}_N(x)=c^\top x+\frac1N\sum_{i=1}^N\sup_{\zeta\in U^i_N}Q(x,\zeta),\qquad \hat v^{SRO}_N=\inf_x\hat V^{SRO}_N(x).$$
--   3. **Policies.** A recourse policy is any function $y(\cdot):\mathbb R^d\to\mathbb R^r$; the linear decision rules are $\mathcal L=\{y(\cdot): y(\zeta)=y^0+Y\zeta \text{ for some } y^0\in\mathbb R^r,\ Y\in\mathbb R^{r\times d}\}$.
--   4. **Single-policy approximation** (SP) over a policy class $\Pi$: $\hat V^{SP}_N(x)$ is the infimum, over $y(\cdot)\in\Pi$ with $Tx+Wy(\zeta)\ge h(\zeta)$ for all $\zeta\in\bigcup_i U^i_N$, of $c^\top x+\frac1N\sum_i\sup_{\zeta\in U^i_N}q^\top y(\zeta)$.
--   5. **Multi-policy approximation** (MP): $\hat V^{MP}_N(x)$ is the infimum, over $N$ policies $y^1(\cdot),\dots,y^N(\cdot)\in\Pi$ with $Tx+Wy^i(\zeta)\ge h(\zeta)$ for all $\zeta\in U^i_N$ and $i\in[N]$, of
--   $$c^\top x+\frac1N\sum_{i=1}^N\sup_{\zeta\in U^i_N}q^\top y^i(\zeta).$$
--   Both are $+\infty$ when no feasible policies exist, and $\hat v^{SP}_N$, $\hat v^{MP}_N$ are their infima over $x$.
--   6. **Definition 1.** For a set $\mathcal C\subseteq\mathbb R^{r\times d}$ of recourse matrices,
--   $$Q^{\mathcal C}_\epsilon(x,\hat\zeta)=\inf_{y^0\in\mathbb R^r,\ Y\in\mathcal C}\ \sup_{\zeta\in B(\hat\zeta,\epsilon)\cap\Xi}q^\top(y^0+Y\zeta)\quad\text{s.t. } Tx+W(y^0+Y\zeta)\ge h(\zeta)\ \ \forall\zeta\in B(\hat\zeta,\epsilon)\cap\Xi.$$
--   7. For a first-stage decision $x^*$: $\Xi^*=\{\zeta\in\Xi:\exists y,\ Tx^*+Wy\ge h(\zeta)\}$; the dual polyhedron $D=\{\delta\in\mathbb R^m:W^\top\delta=q,\ \delta\ge0\}$ with extreme points $\mathrm{ext}(D)$; and
--   $$\eta^{\mathcal C}=\sup_{Y\in\mathcal C,\ \delta\in\mathrm{ext}(D)}\Big\{\|Y^\top q\|_*+\sum_{j=1}^m\delta_j\|h_j-Y^\top w_j\|_*\Big\},\qquad L=\max_{\delta\in\mathrm{ext}(D)}\|T^\top\delta\|,$$
--   where $h_j^\top$ and $w_j^\top$ are the $j$-th rows of $H$ and $W$.
--
--   (SRO) is the data-driven problem the paper studies; (SP) and (MP) are its tractable approximations, and $Q^{\mathcal C}_\epsilon$, $\Xi^*$, $D$, $\eta^{\mathcal C}$, $L$ are the quantities of the convergence proof.
--
--   **Formalization Note** The samples $\xi^1,\dots,\xi^N$ are `s 0, …, s (N-1)`, and the factor $1/N$ is the real number $N^{-1}$ cast to `EReal`. Every "min", "max", "sup" and "inf" is an `EReal` infimum or supremum (no attainment assumed); a supremum over an empty set is $-\infty$ and an infimum over an empty feasible set is $+\infty$. (MP) is stated as printed, with $N$ policies indexed by `Fin N`. $Q^{\mathcal C}_\epsilon$ is defined for every real $\epsilon$ (Definition 1 takes $\epsilon>0$, Lemma 3 uses $\epsilon\ge0$). $x^*$ is an arbitrary first-stage decision `xs`. $\eta^{\mathcal C}$ is an `EReal` supremum, hence $+\infty$ for unbounded $\mathcal C$; $L$ is a real supremum over the finite set $\mathrm{ext}(D)$.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, pp. 6–10, (SRO), (SAA), (SP), L, (MP); p. 14, Definition 1; pp. 16–17, Ξ*, D, Lemma 3 (η^C, L)

import Mathlib
import Definitions.Def_TwoStageSRO_AsymOpt_Model

open MeasureTheory Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

variable {n d r m mt : ℕ}

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 7, (SAA):
`V̂^SAA_N(x) = cᵀx + (1/N) Σ_{i=1}^N Q(x, ξⁱ)` on the sample path `s`.

**Formalization Note** The samples `ξ¹, …, ξᴺ` are `s 0, …, s (N-1)`. The factor `1/N` is the real
number `N⁻¹` cast to `EReal` (junk `0` at `N = 0`). -/
noncomputable def VSAA (M : Model n d r m mt) (s : ℕ → Fin d → ℝ) (N : ℕ) (x : Fin n → ℝ) : EReal :=
  ((M.c ⬝ᵥ x : ℝ) : EReal) + (((N : ℝ)⁻¹ : ℝ) : EReal) * ∑ i ∈ Finset.range N, Q M x (s i)

/-- arXiv:1907.07142v4, p. 7, (SAA): `v̂^SAA_N = inf_x V̂^SAA_N(x)` in `EReal`. -/
noncomputable def vSAA (M : Model n d r m mt) (s : ℕ → Fin d → ℝ) (N : ℕ) : EReal :=
  ⨅ x, VSAA M s N x

/-- arXiv:1907.07142v4, p. 6: the uncertainty set `U^i_N = {ζ ∈ Ξ : ‖ζ − ξⁱ‖ ≤ ε_N}` around the
sample `s i`. -/
def U (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] (ε : ℝ) (s : ℕ → Fin d → ℝ) (i : ℕ) :
    Set (Fin d → ℝ) :=
  ball p (s i) ε ∩ Xi M

/-- arXiv:1907.07142v4, p. 6, (SRO):
`V̂^SRO_N(x) = cᵀx + (1/N) Σ_{i=1}^N sup_{ζ ∈ U^i_N} Q(x, ζ)`. -/
noncomputable def VSRO (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] (ε : ℝ)
    (s : ℕ → Fin d → ℝ) (N : ℕ) (x : Fin n → ℝ) : EReal :=
  ((M.c ⬝ᵥ x : ℝ) : EReal) +
    (((N : ℝ)⁻¹ : ℝ) : EReal) * ∑ i ∈ Finset.range N, ⨆ ζ ∈ U M p ε s i, Q M x ζ

/-- arXiv:1907.07142v4, p. 6, (SRO): `v̂^SRO_N = inf_x V̂^SRO_N(x)` in `EReal`. -/
noncomputable def vSRO (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] (ε : ℝ)
    (s : ℕ → Fin d → ℝ) (N : ℕ) : EReal :=
  ⨅ x, VSRO M p ε s N x

/-- arXiv:1907.07142v4, p. 5: the space `R^{d,r}` of all recourse policies `y(·) : ℝᵈ → ℝʳ`. -/
abbrev Pol (d r : ℕ) := (Fin d → ℝ) → (Fin r → ℝ)

/-- arXiv:1907.07142v4, p. 8: the linear decision rules
`L = {y(·) : ∃ y⁰ ∈ ℝʳ, Y ∈ ℝ^{r×d}, y(ξ) = y⁰ + Yξ}`. -/
def LDR : Set (Pol d r) :=
  {y | ∃ (y0 : Fin r → ℝ) (Y : Matrix (Fin r) (Fin d) ℝ), ∀ ζ, y ζ = y0 + Y *ᵥ ζ}

/-- arXiv:1907.07142v4, pp. 8–9: the policy `y(·)` is robustly feasible for the first-stage decision
`x` on the set `S`: `Tx + Wy(ζ) ≥ h(ζ)` for all `ζ ∈ S`. -/
def robFeas (M : Model n d r m mt) (x : Fin n → ℝ) (S : Set (Fin d → ℝ)) (y : Pol d r) : Prop :=
  ∀ ζ ∈ S, M.h ζ ≤ M.T *ᵥ x + M.W *ᵥ y ζ

/-- arXiv:1907.07142v4, pp. 8–9: the worst-case second-stage cost `sup_{ζ ∈ S} qᵀy(ζ)` in `EReal`
(`−∞` for empty `S`). -/
noncomputable def robCost (M : Model n d r m mt) (S : Set (Fin d → ℝ)) (y : Pol d r) : EReal :=
  ⨆ ζ ∈ S, ((M.q ⬝ᵥ y ζ : ℝ) : EReal)

/-- arXiv:1907.07142v4, p. 8, (SP), and p. 10: `V̂^SP_N(x)`, the optimal cost of the single-policy
approximation with first-stage decision `x` over the policy class `PiC` (the paper's `Π`):
the infimum over `y(·) ∈ Π` with `Tx + Wy(ζ) ≥ h(ζ)` for all `ζ ∈ ⋃ᵢ U^i_N` of
`cᵀx + (1/N) Σᵢ sup_{ζ ∈ U^i_N} qᵀy(ζ)`; it is `+∞` when no such policy exists (p. 10). -/
noncomputable def VSP (M : Model n d r m mt) (PiC : Set (Pol d r)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (ε : ℝ) (s : ℕ → Fin d → ℝ) (N : ℕ) (x : Fin n → ℝ) : EReal :=
  ⨅ y ∈ {y : Pol d r | y ∈ PiC ∧ robFeas M x (⋃ i ∈ Finset.range N, U M p ε s i) y},
    ((M.c ⬝ᵥ x : ℝ) : EReal) +
      (((N : ℝ)⁻¹ : ℝ) : EReal) * ∑ i ∈ Finset.range N, robCost M (U M p ε s i) y

/-- arXiv:1907.07142v4, p. 8, (SP): `v̂^SP_N = inf_x V̂^SP_N(x)`. -/
noncomputable def vSP (M : Model n d r m mt) (PiC : Set (Pol d r)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (ε : ℝ) (s : ℕ → Fin d → ℝ) (N : ℕ) : EReal :=
  ⨅ x, VSP M PiC p ε s N x

/-- arXiv:1907.07142v4, p. 9, (MP), and p. 10: `V̂^MP_N(x)`, the optimal cost of the multi-policy
approximation with first-stage decision `x`: the infimum over `N` policies `y¹(·), …, yᴺ(·) ∈ Π`
with `Tx + Wyⁱ(ζ) ≥ h(ζ)` for all `ζ ∈ U^i_N`, `i ∈ [N]`, of
`cᵀx + (1/N) Σᵢ sup_{ζ ∈ U^i_N} qᵀyⁱ(ζ)`; `+∞` when no such policies exist (p. 10).

**Formalization Note** The policy `yⁱ` is `ys i` for `i : Fin N`, attached to the sample `s i`. -/
noncomputable def VMP (M : Model n d r m mt) (PiC : Set (Pol d r)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (ε : ℝ) (s : ℕ → Fin d → ℝ) (N : ℕ) (x : Fin n → ℝ) : EReal :=
  ⨅ ys ∈ {ys : Fin N → Pol d r | ∀ i, ys i ∈ PiC ∧ robFeas M x (U M p ε s i) (ys i)},
    ((M.c ⬝ᵥ x : ℝ) : EReal) +
      (((N : ℝ)⁻¹ : ℝ) : EReal) * ∑ i : Fin N, robCost M (U M p ε s i) (ys i)

/-- arXiv:1907.07142v4, p. 9, (MP): `v̂^MP_N = inf_x V̂^MP_N(x)`. -/
noncomputable def vMP (M : Model n d r m mt) (PiC : Set (Pol d r)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (ε : ℝ) (s : ℕ → Fin d → ℝ) (N : ℕ) : EReal :=
  ⨅ x, VMP M PiC p ε s N x

/-- arXiv:1907.07142v4, p. 14, Definition 1: for a set `C ⊆ ℝ^{r×d}` of recourse matrices,
`Q^C_ε(x, ζ̂) = min_{y⁰ ∈ ℝʳ, Y ∈ C} max_{ζ ∈ B(ζ̂,ε) ∩ Ξ} qᵀ(y⁰ + Yζ)` subject to
`Tx + W(y⁰ + Yζ) ≥ h(ζ)` for all `ζ ∈ B(ζ̂, ε) ∩ Ξ`.

**Formalization Note** "min"/"max" are `EReal` infimum/supremum (`+∞` when no `(y⁰, Y)` is feasible).
Defined for every real `ε`; the paper takes `ε > 0` in Definition 1 and `ε ≥ 0` in Lemma 3. -/
noncomputable def QC (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (C : Set (Matrix (Fin r) (Fin d) ℝ)) (ε : ℝ) (x : Fin n → ℝ) (zhat : Fin d → ℝ) : EReal :=
  ⨅ yY ∈ {yY : (Fin r → ℝ) × Matrix (Fin r) (Fin d) ℝ |
      yY.2 ∈ C ∧ robFeas M x (ball p zhat ε ∩ Xi M) (fun ζ => yY.1 + yY.2 *ᵥ ζ)},
    robCost M (ball p zhat ε ∩ Xi M) (fun ζ => yY.1 + yY.2 *ᵥ ζ)

/-- arXiv:1907.07142v4, p. 16: `Ξ* = {ζ ∈ Ξ : ∃ y ∈ ℝʳ, Tx* + Wy ≥ h(ζ)}`, the realizations for which
the first-stage decision `xs` (the paper's `x*`) has a feasible recourse. -/
def XiStar (M : Model n d r m mt) (xs : Fin n → ℝ) : Set (Fin d → ℝ) :=
  {ζ | ζ ∈ Xi M ∧ ∃ y : Fin r → ℝ, M.h ζ ≤ M.T *ᵥ xs + M.W *ᵥ y}

/-- arXiv:1907.07142v4, p. 17: the dual feasible set `D = {δ ∈ ℝᵐ : Wᵀδ = q, δ ≥ 0}`. -/
def Ddual (M : Model n d r m mt) : Set (Fin m → ℝ) :=
  {δ | M.Wᵀ *ᵥ δ = M.q ∧ 0 ≤ δ}

/-- arXiv:1907.07142v4, p. 17, Lemma 3:
`η^C = sup_{Y ∈ C, δ ∈ ext(D)} {‖Yᵀq‖_* + Σ_{j=1}^m δⱼ ‖hⱼ − Yᵀwⱼ‖_*}`, where `hⱼ` and `wⱼ` are the
`j`-th rows of `H` and `W`.

**Formalization Note** The supremum is taken in `EReal`, so `η^C = +∞` for an unbounded `C`. -/
noncomputable def etaC (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (C : Set (Matrix (Fin r) (Fin d) ℝ)) : EReal :=
  ⨆ Y ∈ C, ⨆ δ ∈ Set.extremePoints ℝ (Ddual M),
    (((dualNorm p (Yᵀ *ᵥ M.q) + ∑ j, δ j * dualNorm p (M.H j - Yᵀ *ᵥ M.W j) : ℝ)) : EReal)

/-- arXiv:1907.07142v4, p. 17, Lemma 3: `L = max_{δ ∈ ext(D)} ‖Tᵀδ‖` (the `ℓp`-norm on `ℝⁿ`).

**Formalization Note** A real `sSup` over the image of `ext(D)`; `ext(D)` is finite, and nonempty
when `D ≠ ∅`, so this is the printed maximum. -/
noncomputable def Lconst (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] : ℝ :=
  sSup ((fun δ => ‖WithLp.toLp p (M.Tᵀ *ᵥ δ)‖) '' Set.extremePoints ℝ (Ddual M))

end TwoStageSRO.AsymOpt


