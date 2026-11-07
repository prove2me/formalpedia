-- Prove2me | Definitions.Def_PolyEulerFlow_IsCycleConstants
-- name    : PolyEulerFlow_IsCycleConstants
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:25.397479+00:00
-- url     : https://prove2.me/theorems/094b6a8d-f242-4b6d-9418-ff3ce0bd1641
-- title:
--   Admissible cycle states (36) and the cycle property of Lemma 35
-- statement:
--   For the compiled field of a separated affine program at scale $h$, with $\varepsilon=h^K$ and the clock constants $A_0,B_0$:
--
--   1. A state is **admissible above** a configuration $C$ ((36), p.32) when it lies in the scalar box (25), satisfies the entry conditions (29) of phase zero, and
--   $$\|Y-C\|_\infty\le r_0h,\quad\|Y^s-Y\|_\infty\le A\Delta_\varepsilon,\quad v_ju_j(Y,h)>0,\quad|v_j|\ge\kappa_0h,\qquad\kappa_0=\kappa/16 .$$
--   2. A **cycle start** above $C$ towards $C^+$: $C,C^+$ valid, the state admissible above $C$, and $\|D_\sigma Y_0+b_\sigma-C^+\|_\infty\le r_0h/2$, where $Y_0$ are its data and $\sigma$ the sign pattern selected at $C$.
--   3. The **cycle property** with constants $A,B,s_0$, a box $[lo,hi]$ and a duration constant $C_{cyc}$: for $s\ge s_0$, $0\le\nu\le\varepsilon^2$, every admissible mesh and every disturbance of level $\nu$, the execution from a cycle start (at index $0$) has its next four phase entries; at the fourth one, the next section, $\|Y-Y_*\|_\infty\le B\Delta_\varepsilon$ (37) with $Y_*=D_\sigma Y_0+b_\sigma$, $\|Y^s-Y\|_\infty\le A\Delta_\varepsilon$ (38), and the state is admissible above $C^+$; during the whole cycle data and shadows are within $B\Delta_\varepsilon$ of the segment $[Y_0,Y_*]$ and the state is in $[lo,hi]$; and the cycle lasts at most $C_{cyc}L$ physical time.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), (36) and Lemma 35, p.32 (PDF 34)

import Definitions.Def_PolyEulerFlow_IsUniformClock

namespace PolyEulerFlow

variable {m g : ℕ}

/-- A state at the entry of a cycle is admissible above `C` ((36), p.32): the scalar box and the entry conditions of phase zero hold, and
`‖Y - C‖ ≤ r₀h`, `‖Y^s - Y‖ ≤ A∆ε`, `v_j u_j(Y, h) > 0`, `|v_j| ≥ κ₀h` with `κ₀ = κ/16`.
Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), p.32. `A0`, `B0` are the constants of Lemma 31. -/
def IsAdmissibleAbove (prog : SeparatedAffineProgram m g) (K : ℕ) (A0 B0 A ν h : ℝ) (C : Fin m → ℝ)
    (Z : CompiledState m g) : Prop :=
  scalarBox (h ^ K) ν Z ∧ clockEntry A0 B0 (h ^ K) 0 (clockPart Z) ∧
    ‖dataY Z - C‖ ≤ prog.r0 * h ∧ ‖shadowY Z - dataY Z‖ ≤ A * deltaEps (h ^ K) ν ∧
    ∀ j, 0 < compV Z j * prog.test j (dataY Z) h ∧ prog.κ / 16 * h ≤ |compV Z j|

/-- The hypotheses of Lemma 35 on a cycle: `C`, `C⁺` are valid, the start is admissible above `C`, and the ideal image `Y∗ = D_σ Y₀ + b_σ`
(`σ` the source sign pattern at `C`) satisfies `‖Y∗ - C⁺‖ ≤ r₀h/2`. -/
def IsCycleStart (prog : SeparatedAffineProgram m g) (K : ℕ) (A0 B0 A ν h : ℝ) (C Cnext : Fin m → ℝ)
    (Z0 : CompiledState m g) : Prop :=
  C ∈ prog.valid h ∧ Cnext ∈ prog.valid h ∧ IsAdmissibleAbove prog K A0 B0 A ν h C Z0 ∧
    ‖prog.branch (prog.signPat h C) (dataY Z0) - Cnext‖ ≤ prog.r0 * h / 2

/-- The body of Lemma 35 (Mesh-uniform cycle, including perturbations), p.32, for given constants.
For `s ≥ s0`, `ε = h^K`, `0 ≤ ν ≤ ε²`, every admissible mesh and permitted disturbance, a cycle starting at index `0` in the hypotheses `IsCycleStart` has its four next
phase entries `k1 < k2 < k3 < k4`, with (37), (38), admissibility above `C⁺` at `k4`, data and shadows within `B∆ε` of the segment `[Y₀, Y∗]` during the whole cycle, all active coordinates
in the box `[lo, hi]`, and physical duration at most `Ccyc L`.
**Formalization Note.** Phase zero starts at index `0`: a later cycle is the orbit of the shifted mesh and disturbance. The mesh is variable (Corollary 39, p.34). -/
def IsCycleConstants (prog : SeparatedAffineProgram m g) (K : ℕ) (A0 B0 A B : ℝ) (s0 : ℕ) (lo hi : CompiledState m g)
    (Ccyc : ℝ) : Prop :=
  0 < A ∧ 0 < B ∧ 0 < Ccyc ∧ lo ≤ hi ∧
  ∀ s : ℕ, s0 ≤ s → ∀ ν : ℝ, 0 ≤ ν → ν ≤ (scale s ^ K) ^ 2 →
    ∀ (η : ℕ → ℝ) (ξ : ℕ → CompiledState m g) (C Cnext : Fin m → ℝ) (Z0 : CompiledState m g),
      IsAdmissibleMesh η → IsPermittedDisturbance ν ξ → IsCycleStart prog K A0 B0 A ν (scale s) C Cnext Z0 →
      let h := scale s
      let ε := h ^ K
      let z := eulerOrbit (compiledField prog K h) Z0 η ξ
      let Y0 := dataY Z0
      let Ystar := prog.branch (prog.signPat h C) Y0
      ∃ kk : ℕ → ℕ, IsPhaseEntriesUpTo phaseBit z 0 4 kk ∧
        ‖dataY (z (kk 4)) - Ystar‖ ≤ B * deltaEps ε ν ∧
        ‖shadowY (z (kk 4)) - dataY (z (kk 4))‖ ≤ A * deltaEps ε ν ∧
        IsAdmissibleAbove prog K A0 B0 A ν h Cnext (z (kk 4)) ∧
        (∀ k ≤ kk 4,
          (∃ θ ∈ Set.Icc (0 : ℝ) 1, ‖dataY (z k) - ((1 - θ) • Y0 + θ • Ystar)‖ ≤ B * deltaEps ε ν) ∧
          (∃ θ ∈ Set.Icc (0 : ℝ) 1, ‖shadowY (z k) - ((1 - θ) • Y0 + θ • Ystar)‖ ≤ B * deltaEps ε ν) ∧
          z k ∈ Set.Icc lo hi) ∧
        physTime η (kk 4) ≤ Ccyc * Real.log (1 / ε)

end PolyEulerFlow


