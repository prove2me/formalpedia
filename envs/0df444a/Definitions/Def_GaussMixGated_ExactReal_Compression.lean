-- Prove2me | Definitions.Def_GaussMixGated_ExactReal_Compression
-- name    : GaussMixGated_ExactReal_Compression
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:25:22.778207+00:00
-- url     : https://prove2.me/theorems/440f6f23-6791-4e60-a4c0-cd3b67dfb211
-- title:
--   Recursive co-isometries $\Phi_h=U_h(\Phi_{h-1}\otimes I_d)$, $s_h$, $e_h$, and the history oracles of Proposition 4.1
-- statement:
--   The compression of §4 builds co-isometries recursively: $\Phi_0=1$ and $\Phi_h=U_h(\Phi_{h-1}\otimes I_d)$ with $U_hU_h^{\top}=I$. Consequently $y_h(u)=\Phi_hu^{\otimes h}$ satisfies $y_0=1$ and $y_h(u)=U_h(y_{h-1}(u)\otimes u)$, and
--
--   $$s_h(u)=\|\Phi_hu^{\otimes h}\|^2,\qquad e_h(u)=\|u\|^2s_{h-1}(u)-s_h(u).$$
--
--   A construction stores, for each $h=1,\dots,D$, a block of description cells: the row count $r_h$ of $U_h$ (at most $k$) followed by the entries $U_h[a][b]$, $a<k$, $b<kd$. A stage is a **co-isometry stage** when $r_h$ is a natural number at most $k$ and the rows of $U_h$ (indexed by $a<r_h$, with columns $b<r_{h-1}d$) are orthonormal.
--
--   The construction of Proposition 4.1 has two oracle channels: fresh **view pairs** $(A,B)$, $A=u_I+\sqrt vG_A$, $B=u_I+\sqrt vG_B$, with $I\sim w$, and **evaluations of the prior history** $H_0(A,R_0)$ at a supplied gate input $A$ with fresh $R_0$, charged $c_0$ (the prior history's evaluation cost). A stored history evaluator receives the description and a gate input and returns the number of appended gates passed. With $H_0$ and the evaluator's randomness independent,
--
--   $$a_0(u)=\mathbb P(H_0\mid u),\qquad a_h(u)=\mathbb P\big(H_0\text{ and at least }h\text{ appended gates accept}\mid u\big),$$
--
--   for $A\sim N(u,vI_d)$. The histories are nested and test only the gate side.
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 11 (printed p. 9, §4 preamble), p. 12 (printed p. 10, Φ_h = U_h(Φ_{h−1} ⊗ I_d)); §3.1, PDF pp. 8–9

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Machine
import Definitions.Def_GaussMixGated_ExactReal_Jet

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GaussMixGated.ExactReal

/-!
# Recursive compression of accepted moments (Zheng–Xie–He, STOC 2027 #36, §4, PDF pp. 11–13)

The co-isometries are built recursively: `Φ₀ = 1` and `Φ_h = U_h (Φ_{h−1} ⊗ I_d)` with
`U_h U_hᵀ = I` (PDF p. 12). Hence `y_h(u) := Φ_h u^{⊗h}` satisfies `y_0(u) = 1` and
`y_h(u) = U_h (y_{h−1}(u) ⊗ u)`, where `(y ⊗ u)_{a d + i} = y_a u_i`; `s_h(u) = ‖y_h(u)‖²` and
`e_h(u) = ‖u‖² s_{h−1}(u) − s_h(u)` (§4 preamble, PDF p. 11).

**Output layout of the construction.** The description cells hold, for `h = 1, …, D`, a block
starting at `(h − 1)(1 + k · k d)`: its first cell is the row count `r_h` of `U_h` (a natural
number, `r_0 = 1`), followed by the entries `U_h[a][b]` (`a < k`, `b < k d`) in cell
`1 + a (k d) + b` of the block. `U_h` maps `ℝ^{r_{h−1} d}` to `ℝ^{r_h}`.
-/

/-- The first cell of the block of stage `h ≥ 1`. -/
def blockOffset (d k h : ℕ) : ℕ := (h - 1) * (1 + k * (k * d))

/-- The row count `r_h` read from the description (`r_0 = 1`). -/
def stageRows (D : List ℝ) (d k h : ℕ) : ℕ :=
  if h = 0 then 1 else ⌊D.getD (blockOffset d k h) 0⌋₊

/-- The entry `U_h[a][b]` read from the description. -/
def stageEntry (D : List ℝ) (d k h a b : ℕ) : ℝ :=
  D.getD (blockOffset d k h + 1 + a * (k * d) + b) 0

/-- `y_h(u) = Φ_h u^{⊗h}`, as a sequence supported on the first `r_h` indices. -/
def compressedTensor (D : List ℝ) (d k : ℕ) (u : Fin d → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun a => if a = 0 then 1 else 0
  | h + 1 => fun a =>
      if a < stageRows D d k (h + 1) then
        ∑ b ∈ Finset.range (stageRows D d k h * d),
          stageEntry D d k (h + 1) a b *
            (compressedTensor D d k u h (b / d) *
              (if hb : b % d < d then u ⟨b % d, hb⟩ else 0))
      else 0

/-- `s_h(u) = ‖Φ_h u^{⊗h}‖²`. -/
def compressedSq (D : List ℝ) (d k : ℕ) (u : Fin d → ℝ) (h : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (stageRows D d k h), compressedTensor D d k u h a ^ 2

/-- `e_h(u) = ‖u‖² s_{h−1}(u) − s_h(u)` (for `h ≥ 1`). -/
def compressionResidual (D : List ℝ) (d k : ℕ) (u : Fin d → ℝ) (h : ℕ) : ℝ :=
  sqNorm u * compressedSq D d k u (h - 1) - compressedSq D d k u h

/-- Stage `h ≥ 1` of the description is a co-isometry with at most `k` rows: the row-count cell
holds a natural number `r_h ≤ k`, and `U_h U_hᵀ = I_{r_h}` (rows indexed by `a < r_h`, columns by
`b < r_{h−1} d`). -/
def IsCoisometryStage (D : List ℝ) (d k h : ℕ) : Prop :=
  (∃ r : ℕ, r ≤ k ∧ D.getD (blockOffset d k h) 0 = r) ∧
    ∀ a < stageRows D d k h, ∀ a' < stageRows D d k h,
      ∑ b ∈ Finset.range (stageRows D d k (h - 1) * d),
        stageEntry D d k h a b * stageEntry D d k h a' b = if a = a' then 1 else 0

/-! ## The oracles of Proposition 4.1 -/

/-- The law of one fresh view pair: atom index `I ∼ w`, gate-side noise `G_A` and query-side
noise `G_B`, independent. -/
def viewPairLaw {s d : ℕ} (w : Fin s → ℝ) : Measure (Fin s × (Fin d → ℝ) × (Fin d → ℝ)) :=
  (atomLaw w).prod ((gaussVec d).prod (gaussVec d))

/-- The view-pair channel: the `t`-th call writes `A = u_I + √v G_A` (cells `0, …, d − 1` of the
block) and `B = u_I + √v G_B` (cells `d, …, 2d − 1`) for the `t`-th entry `(I, G_A, G_B)` of the
tape. It costs `1 + 2d` units. -/
def viewChannel {s d : ℕ} (v : ℝ) (u : Fin s → Fin d → ℝ)
    (ω : ℕ → Fin s × (Fin d → ℝ) × (Fin d → ℝ)) : Channel :=
  ⟨0, 2 * d, 0, fun t _ i =>
    if h : i < d then u (ω t).1 ⟨i, h⟩ + Real.sqrt v * (ω t).2.1 ⟨i, h⟩
    else if h' : i - d < d ∧ i < 2 * d then u (ω t).1 ⟨i - d, h'.1⟩ + Real.sqrt v * (ω t).2.2 ⟨i - d, h'.1⟩
    else 0⟩

/-- The prior-history channel: the `t`-th call reads a gate input `A ∈ ℝ^d` and writes `1` if
`H₀(A, R₀)` holds for the fresh randomness `R₀ = ω t`, else `0`. It is charged `c₀`
(the evaluation cost of the prior history) plus `2` units. -/
def historyChannel {d : ℕ} {Ω₀ : Type*} (H₀ : (Fin d → ℝ) → Ω₀ → Prop) (c₀ : ℕ) (ω : ℕ → Ω₀) :
    Channel :=
  open Classical in
  ⟨d, 1, c₀, fun t x _ => if H₀ (fun i => x i) (ω t) then 1 else 0⟩

/-- The construction's initial configuration: cells `0–6` hold `v, D, τ, ξ, δ′, d, k`; pointer
registers `0, 1, 2` hold `d, k, D`. -/
def compressionStart (d k D : ℕ) (v τ ξ δ' : ℝ) : State :=
  initState (listMem [v, (D : ℝ), τ, ξ, δ', (d : ℝ), (k : ℝ)])
    (listPtrs [(d : ℤ), (k : ℤ), (D : ℤ)])

/-- The construction's environment: Gaussian tape `g`, channel `0` = view pairs, channel `1` =
prior history. -/
def compressionEnv {s d : ℕ} (v : ℝ) (u : Fin s → Fin d → ℝ) {Ω₀ : Type*}
    (H₀ : (Fin d → ℝ) → Ω₀ → Prop) (c₀ : ℕ) (ω₀ : ℕ → Fin s × (Fin d → ℝ) × (Fin d → ℝ))
    (ω₁ : ℕ → Ω₀) (g : ℕ → ℝ) : Env :=
  ⟨g, [viewChannel v u ω₀, historyChannel H₀ c₀ ω₁]⟩

/-- The level reached by the stored history evaluator `Ev` on description `D`, gate input `A` and
fresh Gaussian tape `g`: `Ev` starts with `D` in cells `0, …` and `A` in cells `−1, …, −d`,
pointer register `0` holding `d`; at the halt pointer register `0` holds the number of appended
gates passed. -/
def historyLevel (Ev : Program) (D : List ℝ) {d : ℕ} (A : Fin d → ℝ) (g : ℕ → ℝ) : ℤ :=
  (final Ev (samplerEnv g) (initState (withPoint (listMem D) A) (listPtrs [(d : ℤ)]))).ptrs 0

/-- The evaluator's initial configuration on description `D` and gate input `A`. -/
def historyStart (D : List ℝ) {d : ℕ} (A : Fin d → ℝ) : State :=
  initState (withPoint (listMem D) A) (listPtrs [(d : ℤ)])

/-- `a_h(u) = P(H_h | u)`: for `A ∼ N(u, v I_d)`, prior-history randomness `R₀ ∼ λ₀` and fresh
evaluator randomness, all independent, `H₀ = {H₀(A, R₀)}` and, for `h ≥ 1`,
`H_h = H₀ ∩ {the evaluator passes at least h appended gates}`. The histories are nested,
`H₀ ⊇ H₁ ⊇ ⋯`, and test the gate side `A` only. -/
def historyAcceptance (Ev : Program) (D : List ℝ) {d : ℕ} (v : ℝ) {Ω₀ : Type*}
    [MeasurableSpace Ω₀] (lam₀ : Measure Ω₀) (H₀ : (Fin d → ℝ) → Ω₀ → Prop) (h : ℕ)
    (u : Fin d → ℝ) : ℝ :=
  ((gaussVec d).prod (lam₀.prod gaussTape)).real
    {p | H₀ (u + Real.sqrt v • p.1) p.2.1 ∧
      (h = 0 ∨ (h : ℤ) ≤ historyLevel Ev D (u + Real.sqrt v • p.1) p.2.2)}

end GaussMixGated.ExactReal


