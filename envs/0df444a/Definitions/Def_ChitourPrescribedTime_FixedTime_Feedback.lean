-- Prove2me | Definitions.Def_ChitourPrescribedTime_FixedTime_Feedback
-- name    : ChitourPrescribedTime_FixedTime_Feedback
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:05:35.998221+00:00
-- url     : https://prove2.me/theorems/4fb19870-a392-4a1c-a7bf-4726ff2abbdc
-- title:
--   The backstepping homogeneous feedback $\omega^H_\kappa$ (Definition 23)
-- statement:
--   For $y\in\mathbb R$ and $a>0$ write the **signed power** $\lceil y\rfloor^{a}:=\operatorname{sign}(y)\,|y|^{a}$, so $\lceil 0\rfloor^a=0$.
--
--   Fix gains $\ell_1,\dots,\ell_n>0$ and a degree parameter $\kappa$. Following Definition 23, define the **weights** $r_j=r_j(\kappa)=1+(j-1)\kappa$, $j=1,\dots,n$, and the exponents $\beta_j$ by $\beta_0=r_2$ and $(\beta_j+1)r_{j+1}=\beta_0+1$, that is,
--   $$\beta_j=\frac{2+\kappa}{r_{j+1}}-1 .$$
--   The **virtual controls** $v_j=v_j(x)$ are defined inductively by
--   $$v_0=0,\qquad v_j=-\ell_j\Big\lceil \lceil x_j\rfloor^{\beta_{j-1}}-\lceil v_{j-1}\rfloor^{\beta_{j-1}}\Big\rfloor^{\frac{r_j+\kappa}{r_j\beta_{j-1}}},\quad j=1,\dots,n,$$
--   and the **feedback law** (32) is $\omega^H_\kappa(x):=v_n(x)$. For instance $v_1=-\ell_1\lceil x_1\rfloor^{1+\kappa}$, and for $n=1$, $\omega^H_\kappa(x)=-\ell_1\lceil x_1\rfloor^{1+\kappa}$.
--
--   Finally, $D^{\mathbf r(\kappa)}_\mu=\operatorname{diag}(\mu^{r_j(\kappa)})$ is the family of dilations (Definition 6) associated with the weights $\mathbf r(\kappa)$.
--
--   This feedback, with the degree $\kappa$ later made state-dependent, is the controller of every result of §4.
--
--   **Formalization Note** The paper never defines $\lceil\cdot\rfloor^\alpha$; the standard sliding-mode reading $\operatorname{sign}(y)|y|^\alpha$ is used, with `Real.rpow` applied to $|y|\ge0$ only. The recursion is over `ℕ`: `vSeq ℓ κ x j` is $v_j$, `coord x j` is $x_{j+1}$ and `gain ℓ j` is $\ell_{j+1}$ (0-based, $0$ beyond $n$). `weight κ j` is $r_j$ for the paper's 1-based $j$, and `beta κ j` is $\beta_j$. The exponent is the one printed in (33), $(r_j+\kappa)/(r_j\beta_{j-1})$; the proof of Lemma 32 prints $(r_j+1)/(r_j\beta_{j-1})$, a slip (only (33) makes $v_j$ homogeneous of degree $r_{j+1}$).
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1033, §4.1, Definition 23, eqs. (32)–(33); p. 1026, Definition 6

import Mathlib

namespace ChitourPrescribedTime.FixedTime

/-- The signed power `⌈y⌋^a := sign(y) |y|^a` (so `⌈0⌋^a = 0` for `a > 0`). -/
noncomputable def sgnPow (y a : ℝ) : ℝ := Real.sign y * |y| ^ a

/-- The weights of Definition 23: `r_j(κ) = 1 + (j - 1) κ` for the 1-based index `j`. -/
noncomputable def weight (κ : ℝ) (j : ℕ) : ℝ := 1 + ((j : ℝ) - 1) * κ

/-- The exponents `β_j` of Definition 23: `β_0 = r_2`, `(β_j + 1) r_{j+1} = β_0 + 1`,
i.e. `β_j = (2 + κ) / r_{j+1}(κ) - 1` (which gives `β_0 = 1 + κ = r_2` at `j = 0`). -/
noncomputable def beta (κ : ℝ) (j : ℕ) : ℝ := (2 + κ) / weight κ (j + 1) - 1

/-- The coordinate `x_{j+1}` of `x ∈ ℝ^n` for the 0-based index `j < n` (and `0` otherwise). -/
noncomputable def coord {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (j : ℕ) : ℝ :=
  if h : j < n then x ⟨j, h⟩ else 0

/-- The gain `ℓ_{j+1}` for the 0-based index `j < n` (and `0` otherwise). -/
noncomputable def gain {n : ℕ} (ℓ : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then ℓ ⟨j, h⟩ else 0

/-- The backstepping virtual controls `v_j = v_j(x)` of (33):
`v_0 = 0` and, for `j ≥ 1`,
`v_j = -ℓ_j ⌈ ⌈x_j⌋^{β_{j-1}} - ⌈v_{j-1}⌋^{β_{j-1}} ⌋^{(r_j + κ)/(r_j β_{j-1})}`.
Here `vSeq ℓ κ x j` is `v_j` (the index of `v` is the paper's own). -/
noncomputable def vSeq {n : ℕ} (ℓ : Fin n → ℝ) (κ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℕ → ℝ
  | 0 => 0
  | j + 1 =>
      -(gain ℓ j) *
        sgnPow (sgnPow (coord x j) (beta κ j) - sgnPow (vSeq ℓ κ x j) (beta κ j))
          ((weight κ (j + 1) + κ) / (weight κ (j + 1) * beta κ j))

/-- The feedback law (32): `ω^H_κ(x) := v_n(x)`. -/
noncomputable def omegaH {n : ℕ} (ℓ : Fin n → ℝ) (κ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  vSeq ℓ κ x n

/-- The weighted dilation `D^{r(κ)}_μ = diag(μ^{r_j(κ)})` of Definition 6 with the weights
`r(κ)` of Definition 23, applied to `x` (0-based `i` has weight `r_{i+1}(κ)`). -/
noncomputable def dilK {n : ℕ} (κ μ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i : Fin n => μ ^ weight κ (i.val + 1) * x i)

end ChitourPrescribedTime.FixedTime


