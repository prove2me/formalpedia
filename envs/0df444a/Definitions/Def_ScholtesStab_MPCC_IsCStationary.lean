-- Prove2me | Definitions.Def_ScholtesStab_MPCC_IsCStationary
-- name    : ScholtesStab_MPCC_IsCStationary
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:10.692181+00:00
-- url     : https://prove2.me/theorems/041e4988-e5ec-4ba3-9d7f-085005dbabfc
-- title:
--   W- and C-stationarity of MPCC with multipliers $(\bar\sigma,\bar\varrho)$
-- statement:
--   Multipliers of MPCC at $\bar x$ are numbers $\bar\sigma_{1,j}$ ($j\in a_{01}(\bar x)$), $\bar\sigma_{2,j}$ ($j\in a_{10}(\bar x)$) and $\bar\varrho_{1,j},\bar\varrho_{2,j}$ ($j\in a_{00}(\bar x)$). A feasible point $\bar x\in M$ is **W-stationary** with multipliers $(\bar\sigma,\bar\varrho)$ if
--
--   $$
--   Df(\bar x)=\sum_{j\in a_{01}(\bar x)}\bar\sigma_{1,j}DF_{1,j}(\bar x)+\sum_{j\in a_{10}(\bar x)}\bar\sigma_{2,j}DF_{2,j}(\bar x)+\sum_{j\in a_{00}(\bar x)}\bigl(\bar\varrho_{1,j}DF_{1,j}(\bar x)+\bar\varrho_{2,j}DF_{2,j}(\bar x)\bigr), \tag{5}
--   $$
--
--   and it is **C-stationary** if moreover
--
--   $$
--   \bar\varrho_{1,j}\cdot\bar\varrho_{2,j}\ge 0\quad\text{for all } j\in a_{00}(\bar x). \tag{6}
--   $$
--
--   The module also defines `StatEq` (equation (5) alone) and `SameMult`: two multiplier tuples define the same multipliers at $\bar x$ when they agree on $a_{01}(\bar x)$ ($\bar\sigma_1$), on $a_{10}(\bar x)$ ($\bar\sigma_2$) and on $a_{00}(\bar x)$ ($\bar\varrho_1,\bar\varrho_2$).
--
--   **Formalization Note** The multipliers are a structure `MPCCMult κ` of four total functions `Fin κ → ℝ`; only their values on the index sets above are used. The paper's "C-stationary point" is $\exists$ multipliers with `IsCStationary`.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.5, Definition 2, (5), (6)

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_a01

namespace ScholtesStab

/-- MPCC multipliers `(σ̄, ϱ̄) = (σ̄₁, σ̄₂, ϱ̄₁, ϱ̄₂)` (p.5).

**Formalization Note.** Each is a total function `Fin κ → ℝ`. Only the values of `σ̄₁` on
`a₀₁(x̄)`, of `σ̄₂` on `a₁₀(x̄)` and of `ϱ̄₁, ϱ̄₂` on `a₀₀(x̄)` are the paper's multipliers;
the other values are never used. -/
structure MPCCMult (κ : ℕ) where
  /-- `σ̄₁,ⱼ`, used for `j ∈ a₀₁(x̄)` -/
  σ₁ : Fin κ → ℝ
  /-- `σ̄₂,ⱼ`, used for `j ∈ a₁₀(x̄)` -/
  σ₂ : Fin κ → ℝ
  /-- `ϱ̄₁,ⱼ`, used for `j ∈ a₀₀(x̄)` -/
  ϱ₁ : Fin κ → ℝ
  /-- `ϱ̄₂,ⱼ`, used for `j ∈ a₀₀(x̄)` -/
  ϱ₂ : Fin κ → ℝ

namespace MPCC

variable {n κ : ℕ}

/-- **The W-stationarity equation (5)** of Definition 2, Lämmel–Shikhman,
arXiv:2501.07383v2, p.5:
`Df(x̄) = Σ_{j∈a₀₁(x̄)} σ̄₁,ⱼ DF₁,ⱼ(x̄) + Σ_{j∈a₁₀(x̄)} σ̄₂,ⱼ DF₂,ⱼ(x̄)
        + Σ_{j∈a₀₀(x̄)} (ϱ̄₁,ⱼ DF₁,ⱼ(x̄) + ϱ̄₂,ⱼ DF₂,ⱼ(x̄))`.

**Formalization Note.** An equation of Fréchet derivatives `ℝⁿ →L[ℝ] ℝ`. -/
def StatEq (P : MPCC n κ) (x : E n) (m : MPCCMult κ) : Prop :=
  fderiv ℝ P.f x =
    ∑ j ∈ P.a01 x, m.σ₁ j • fderiv ℝ (P.F₁ j) x + ∑ j ∈ P.a10 x, m.σ₂ j • fderiv ℝ (P.F₂ j) x
      + ∑ j ∈ P.a00 x, (m.ϱ₁ j • fderiv ℝ (P.F₁ j) x + m.ϱ₂ j • fderiv ℝ (P.F₂ j) x)

/-- **Definition 2 (W-stationarity), with explicit multipliers** (p.5): `x̄ ∈ M` and (5). -/
def IsWStationary (P : MPCC n κ) (x : E n) (m : MPCCMult κ) : Prop :=
  x ∈ P.M ∧ P.StatEq x m

/-- **Definition 2 (C-stationarity), with explicit multipliers** (p.5): `x̄` is W-stationary
with multipliers `(σ̄, ϱ̄)` and (6) holds: `ϱ̄₁,ⱼ · ϱ̄₂,ⱼ ≥ 0` for all `j ∈ a₀₀(x̄)`. -/
def IsCStationary (P : MPCC n κ) (x : E n) (m : MPCCMult κ) : Prop :=
  P.IsWStationary x m ∧ ∀ j ∈ P.a00 x, 0 ≤ m.ϱ₁ j * m.ϱ₂ j

/-- Two multiplier tuples `m, m'` define the same multipliers `(σ̄, ϱ̄)` at `x̄`: they agree
where the paper's multipliers live, i.e. `σ̄₁` on `a₀₁(x̄)`, `σ̄₂` on `a₁₀(x̄)`, and `ϱ̄₁, ϱ̄₂`
on `a₀₀(x̄)` (p.5; used for "the unique multipliers", p.6 and p.8). -/
def SameMult (P : MPCC n κ) (x : E n) (m m' : MPCCMult κ) : Prop :=
  (∀ j ∈ P.a01 x, m.σ₁ j = m'.σ₁ j) ∧ (∀ j ∈ P.a10 x, m.σ₂ j = m'.σ₂ j) ∧
    ∀ j ∈ P.a00 x, m.ϱ₁ j = m'.ϱ₁ j ∧ m.ϱ₂ j = m'.ϱ₂ j

end MPCC

end ScholtesStab


