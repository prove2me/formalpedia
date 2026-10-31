-- Prove2me | Definitions.Def_ScholtesStab_MPCC_a01neg
-- name    : ScholtesStab_MPCC_a01neg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:16.992474+00:00
-- url     : https://prove2.me/theorems/e1f10e59-91d6-4803-b9bb-35dbbbd5519e
-- title:
--   Sign-split index subsets $a^{-}_{01},a^{0}_{01},a^{+}_{01},\dots,a^{+}_{00}$
-- statement:
--   For multipliers $(\bar\sigma,\bar\varrho)$ of a W-stationary point $\bar x\in M$, the active index sets are split by the signs of the multipliers:
--
--   $$
--   a^{-}_{01}(\bar x)=\{j\in a_{01}(\bar x)\mid\bar\sigma_{1,j}<0\},\quad a^{0}_{01}(\bar x)=\{j\in a_{01}(\bar x)\mid\bar\sigma_{1,j}=0\},\quad a^{+}_{01}(\bar x)=\{j\in a_{01}(\bar x)\mid\bar\sigma_{1,j}>0\},
--   $$
--
--   the analogous sets $a^{-}_{10},a^{0}_{10},a^{+}_{10}$ with $\bar\sigma_{2,j}$ on $a_{10}(\bar x)$, and
--
--   $$
--   a^{-}_{00}(\bar x)=\{j\in a_{00}(\bar x)\mid\bar\varrho_{1,j},\bar\varrho_{2,j}<0\},\quad
--   a^{0}_{00}(\bar x)=\{j\in a_{00}(\bar x)\mid\bar\varrho_{1,j}\cdot\bar\varrho_{2,j}=0\},\quad
--   a^{+}_{00}(\bar x)=\{j\in a_{00}(\bar x)\mid\bar\varrho_{1,j},\bar\varrho_{2,j}>0\}.
--   $$
--
--   These sets describe which constraints of the regularization $\mathcal S$ are active near $\bar x$ and enter the index bounds of Theorem 1.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.6

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_a01
import Definitions.Def_ScholtesStab_MPCC_IsCStationary

namespace ScholtesStab

namespace MPCC

variable {n κ : ℕ}

/-- **Sign-split index subsets** (Lämmel–Shikhman, arXiv:2501.07383v2, p.6), for multipliers
`(σ̄, ϱ̄)` of a W-stationary point `x̄`: `a⁻₀₁(x̄) = {j ∈ a₀₁(x̄) | σ̄₁,ⱼ < 0}`. -/
noncomputable def a01neg (P : MPCC n κ) (x : E n) (m : MPCCMult κ) : Finset (Fin κ) :=
  (P.a01 x).filter fun j => m.σ₁ j < 0

/-- `a⁰₀₁(x̄) = {j ∈ a₀₁(x̄) | σ̄₁,ⱼ = 0}` (p.6). -/
noncomputable def a01zero (P : MPCC n κ) (x : E n) (m : MPCCMult κ) : Finset (Fin κ) :=
  (P.a01 x).filter fun j => m.σ₁ j = 0

/-- `a⁺₀₁(x̄) = {j ∈ a₀₁(x̄) | σ̄₁,ⱼ > 0}` (p.6). -/
noncomputable def a01pos (P : MPCC n κ) (x : E n) (m : MPCCMult κ) : Finset (Fin κ) :=
  (P.a01 x).filter fun j => 0 < m.σ₁ j

/-- `a⁻₁₀(x̄) = {j ∈ a₁₀(x̄) | σ̄₂,ⱼ < 0}` (p.6). -/
noncomputable def a10neg (P : MPCC n κ) (x : E n) (m : MPCCMult κ) : Finset (Fin κ) :=
  (P.a10 x).filter fun j => m.σ₂ j < 0

/-- `a⁰₁₀(x̄) = {j ∈ a₁₀(x̄) | σ̄₂,ⱼ = 0}` (p.6). -/
noncomputable def a10zero (P : MPCC n κ) (x : E n) (m : MPCCMult κ) : Finset (Fin κ) :=
  (P.a10 x).filter fun j => m.σ₂ j = 0

/-- `a⁺₁₀(x̄) = {j ∈ a₁₀(x̄) | σ̄₂,ⱼ > 0}` (p.6). -/
noncomputable def a10pos (P : MPCC n κ) (x : E n) (m : MPCCMult κ) : Finset (Fin κ) :=
  (P.a10 x).filter fun j => 0 < m.σ₂ j

/-- `a⁻₀₀(x̄) = {j ∈ a₀₀(x̄) | ϱ̄₁,ⱼ, ϱ̄₂,ⱼ < 0}` (p.6). -/
noncomputable def a00neg (P : MPCC n κ) (x : E n) (m : MPCCMult κ) : Finset (Fin κ) :=
  (P.a00 x).filter fun j => m.ϱ₁ j < 0 ∧ m.ϱ₂ j < 0

/-- `a⁰₀₀(x̄) = {j ∈ a₀₀(x̄) | ϱ̄₁,ⱼ · ϱ̄₂,ⱼ = 0}` (p.6). -/
noncomputable def a00zero (P : MPCC n κ) (x : E n) (m : MPCCMult κ) : Finset (Fin κ) :=
  (P.a00 x).filter fun j => m.ϱ₁ j * m.ϱ₂ j = 0

/-- `a⁺₀₀(x̄) = {j ∈ a₀₀(x̄) | ϱ̄₁,ⱼ, ϱ̄₂,ⱼ > 0}` (p.6).

**Formalization Note.** The subsets depend only on the values of the multipliers on the index
set they refine. -/
noncomputable def a00pos (P : MPCC n κ) (x : E n) (m : MPCCMult κ) : Finset (Fin κ) :=
  (P.a00 x).filter fun j => 0 < m.ϱ₁ j ∧ 0 < m.ϱ₂ j

end MPCC

end ScholtesStab


