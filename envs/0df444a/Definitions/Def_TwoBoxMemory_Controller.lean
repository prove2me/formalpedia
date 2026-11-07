-- Prove2me | Definitions.Def_TwoBoxMemory_Controller
-- name    : TwoBoxMemory_Controller
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:44.96968+00:00
-- url     : https://prove2.me/theorems/5d867e0c-a988-4410-8dd8-4c8bbab8bb0f
-- title:
--   $M$-label stochastic controllers, their risks, $V_M$ and the excess $\Delta_M$
-- statement:
--   An **$m$-label controller** is a probability row $\mu$ on labels $\{1,\dots,m\}$ and two nonnegative $m\times m$ matrices $K_A$, $K_B$ with $(K_A+K_B)\mathbf 1=\mathbf 1$: at label $i$ the entry $(K_a)_{ij}$ is the joint probability of choosing command $a$ and, after failure, moving to label $j$. It generates the cylinder probabilities
--
--   $$P(x_0\cdots x_{h-1})=\mu K_{x_0}\cdots K_{x_{h-1}}\mathbf 1 .$$
--
--   With $Q_A=rK_A+K_B$, $Q_B=K_A+sK_B$ and $c=CK_A\mathbf 1+DK_B\mathbf 1$, its conditional risks are $\sum_{n\ge0}\mu Q_h^n c\in[0,\infty]$, $h\in\{A,B\}$. A controller is **deterministic with a pure initial label** when $\mu$ is a point mass and all entries of $K_A,K_B$ are $0$ or $1$.
--
--   The memory-restricted value and the excess are
--
--   $$V_M=\inf_{\text{at most }M\text{ labels}}\max(J_A,J_B),\qquad \Delta_M=V_M-V .$$
--
--   The infimum allows arbitrary real nonnegative rows and arbitrary initial distributions on the counted labels.
--
--   **Formalization Note** Labels are `Fin m`, $K$ `0` $=K_A$, $K$ `1` $=K_B$; "at most $M$ labels" is $m\le M$. No rationality, determinism, reachability or finiteness of risk is imposed. The risk is the closed form of Appendix C, p.28. $\Delta_M$ is the real difference of the two values, both finite for $M\ge1$.
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), §2, p.2 (PDF 4); §B.1, p.21 (PDF 23); Appendix C, p.28 (PDF 30); p.26 (PDF 28) for deterministic rows

import Mathlib
import Definitions.Def_TwoBoxMemory_Risk

namespace TwoBoxMemory

/-!
# Finite-label stochastic controllers, their risks, `V_M` and the excess `Δ_M`

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
§2, p.2 (PDF 4); §B.1, p.21 (PDF 23); Appendix C, p.28 (PDF 30).

An `m`-label controller is a probability row `μ` and nonnegative `m × m` matrices `K_A`, `K_B`
with `(K_A + K_B) 1 = 1`; `(K_a)_{ij}` is the joint probability of choosing command `a` at label
`i` and, after failure, moving to label `j`. Its cylinder probabilities are
`P(x_0 ⋯ x_{h-1}) = μ K_{x_0} ⋯ K_{x_{h-1}} 1` (p.2). With `Q_A = r K_A + K_B`,
`Q_B = K_A + s K_B` and `c = C K_A 1 + D K_B 1`, its conditional risks are
`∑_{n ≥ 0} μ Q_h^n c ∈ [0, ∞]` (p.28). `V_M` is the infimum of the worst risk over controllers with
at most `M` labels, and `Δ_M = V_M − V`.

**Formalization Note.**
* Labels are `Fin m`; commands are `Fin 2` with `0 = A`, `1 = B`; `K 0 = K_A`, `K 1 = K_B`.
* Entries are arbitrary nonnegative reals: no rationality, determinism, reachability or finiteness
  of risk is imposed (an infinite-risk controller only raises the infimum).
* The controller risk is the closed form of p.28; it is the risk (B.4) of the cylinder law of
  p.2. Every term `μ Q_h^n c` is nonnegative, so `ENNReal.ofReal` loses nothing.
* "At most `M` labels" is `m ≤ M`. A controller has at least one label (`∑ μ = 1`).
* `IsDeterministic`: a pure initial label and all matrix entries in `{0, 1}` (p.26: "rows with
  entries zero and one"); with the row condition each label then has exactly one command and one
  successor.
* `gap` is `Δ_M` as a real number, `(V_M).toReal − V.toReal`; both are finite for `M ≥ 1` (the
  verification file proves `V_M < ⊤` and `V < ⊤`), so `toReal` is exact there.
-/

open MeasureTheory

noncomputable section

/-- An `m`-label controller: initial probability row `μ` and the joint command/transition matrices
`K 0 = K_A`, `K 1 = K_B`, nonnegative, with `K_A + K_B` row stochastic. -/
structure Controller (m : ℕ) where
  μ : Fin m → ℝ
  K : Fin 2 → Matrix (Fin m) (Fin m) ℝ
  μ_nonneg : ∀ i, 0 ≤ μ i
  μ_sum : ∑ i, μ i = 1
  K_nonneg : ∀ a i j, 0 ≤ K a i j
  K_row : ∀ i, ∑ j, (K 0 i j + K 1 i j) = 1

variable {m : ℕ}

/-- `Q_A = r K_A + K_B` and `Q_B = K_A + s K_B` (p.28). -/
def Qmat (r s : ℝ) (κ : Controller m) (h : Fin 2) : Matrix (Fin m) (Fin m) ℝ :=
  if h = 0 then r • κ.K 0 + κ.K 1 else κ.K 0 + s • κ.K 1

/-- The expected immediate cost vector `c = C K_A 1 + D K_B 1` (p.28). -/
def cvec (C D : ℝ) (κ : Controller m) : Fin m → ℝ :=
  C • Matrix.mulVec (κ.K 0) (fun _ => 1) + D • Matrix.mulVec (κ.K 1) (fun _ => 1)

/-- The controller's conditional risk `∑_{n ≥ 0} μ Q_h^n c ∈ [0, ∞]` at location `h` (p.28). -/
def ctrlRisk (r s C D : ℝ) (κ : Controller m) (h : Fin 2) : ENNReal :=
  ∑' n : ℕ, ENNReal.ofReal (dotProduct κ.μ (Matrix.mulVec (Qmat r s κ h ^ n) (cvec C D κ)))

/-- The worst conditional risk `max(J_A, J_B)` of a controller. -/
def worstRisk (r s C D : ℝ) (κ : Controller m) : ENNReal :=
  max (ctrlRisk r s C D κ 0) (ctrlRisk r s C D κ 1)

/-- The length-`n` prefix `w_0 ⋯ w_{n-1}` of a word, as a list. -/
def wordPrefix (w : ℕ → Fin 2) (n : ℕ) : List (Fin 2) :=
  List.ofFn fun k : Fin n => w k

/-- The cylinder probability `P(x_0 ⋯ x_{h-1}) = μ K_{x_0} ⋯ K_{x_{h-1}} 1` (p.2). -/
def cylProb (κ : Controller m) (x : List (Fin 2)) : ℝ :=
  dotProduct κ.μ (Matrix.mulVec (x.map κ.K).prod (fun _ => 1))

/-- A deterministic controller with a pure initial label: `μ` is a point mass and every entry of
`K_A`, `K_B` is `0` or `1`. -/
def IsDeterministic (κ : Controller m) : Prop :=
  (∃ i₀, ∀ i, κ.μ i = if i = i₀ then 1 else 0) ∧ ∀ a i j, κ.K a i j = 0 ∨ κ.K a i j = 1

/-- `V_M`: the infimum of the worst risk over all controllers with at most `M` labels. -/
def memValue (r s C D : ℝ) (M : ℕ) : ENNReal :=
  ⨅ (m : ℕ) (_ : m ≤ M) (κ : Controller m), worstRisk r s C D κ

/-- The excess `Δ_M = V_M − V`, as a real number. -/
def gap (r s C D : ℝ) (M : ℕ) : ℝ :=
  (memValue r s C D M).toReal - (value r s C D).toReal

end

end TwoBoxMemory


