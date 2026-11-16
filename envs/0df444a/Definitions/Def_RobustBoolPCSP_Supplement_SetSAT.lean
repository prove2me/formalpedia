-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_SetSAT
-- name    : RobustBoolPCSP_Supplement_SetSAT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:26:43.681753+00:00
-- url     : https://prove2.me/theorems/a025a679-419d-4ac9-82a6-f0917be81394
-- title:
--   Co-singleton SetSAT $\Gamma_{q,g,k}$, criticality, $\Delta$ and $\beta$
-- statement:
--   Fix $q\ge2$ and $1\le g\le k$. For $b,x\in[q]^k$ let $M_b(x)=\#\{i:x_i=b_i\}$ and
--
--   $$P_b=\{x: M_b(x)\le k-g\},\qquad Q_b=[q]^k\setminus\{b\}.$$
--
--   $\Gamma_{q,g,k}$ has domain $[q]$ and the $q^k$ pairs $(P_b,Q_b)$. It is **critical** when $q\mid k$ and $g/k=(q-1)/q$. Also $\Delta=k/q-(k-g)$ and $\beta=\Pr[\mathrm{Bin}(k,1/q)>k-g]$.
--
--   This family has an intermediate robustness exponent at the critical threshold (Theorems 7.2, 7.3).
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §7.1, p.55

import Mathlib
import Definitions.Def_RobustBoolPCSP_Template

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- `M_b(x) = #{i : x_i = b_i}` (p.55). -/
def agreeCount {q k : ℕ} (b x : Fin k → Fin q) : ℕ :=
  (Finset.univ.filter (fun i => x i = b i)).card

/-- The **co-singleton SetSAT template `Γ_{q,g,k}`**.
Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03, sha256
fd1be0d0…), §7.1, p.55: "Fix integers q ≥ 2 and 1 ≤ g ≤ k. For b ∈ [q]^k and x ∈ [q]^k, let
M_b(x) = #{i : x_i = b_i}, and set P_b = {x ∈ [q]^k : M_b(x) ≤ k − g}, Q_b = [q]^k \ {b}. The template
Γ_{q,g,k} has domain A = B = [q] and the q^k relation pairs (P_b, Q_b)."

**Formalization Note.** `[q]` is `Fin q`; the relation pairs are indexed by `b : Fin k → Fin q`. The
constraints `q ≥ 2`, `1 ≤ g ≤ k` are hypotheses of the statements. -/
def SetSAT (q g k : ℕ) : Template (Fin k → Fin q) (Fin q) (Fin q) where
  r := fun _ => k
  P := fun b => {x | agreeCount b x ≤ k - g}
  Q := fun b => {x | x ≠ b}

/-- `Γ_{q,g,k}` is **critical** (p.55): "We call the template critical when q divides k and
g/k = (q − 1)/q, that is, when r₀ := k − g = k/q." The ratio condition is `g q = k (q − 1)`. -/
def SetSATCritical (q g k : ℕ) : Prop := q ∣ k ∧ g * q = k * (q - 1)

/-- `β = P[Bin(k, 1/q) > k − g]` (Theorem 7.3, p.55), the upper binomial tail. -/
noncomputable def setSATBeta (q g k : ℕ) : ℝ :=
  ∑ m ∈ (Finset.range (k + 1)).filter (fun m => k - g < m),
    (k.choose m : ℝ) * (1 / q : ℝ) ^ m * (1 - 1 / q : ℝ) ^ (k - m)

/-- `∆ = k/q − (k − g)` (Theorem 7.3, p.55), as a real number. -/
noncomputable def setSATDelta (q g k : ℕ) : ℝ := (k : ℝ) / q - ((k : ℝ) - g)

end RobustBoolPCSP.Supplement


