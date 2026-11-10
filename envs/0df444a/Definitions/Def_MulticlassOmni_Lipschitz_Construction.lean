-- Prove2me | Definitions.Def_MulticlassOmni_Lipschitz_Construction
-- name    : MulticlassOmni_Lipschitz_Construction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:10:46.596994+00:00
-- url     : https://prove2.me/theorems/0d7f54bd-09b9-4f82-9370-e1a3fb908e87
-- title:
--   §4.1 — cost vectors, hard losses, soft-min smoothed losses and label mixtures of the Lipschitz lower-bound construction
-- statement:
--   Built on an enumerated domain $x_1,\dots,x_N$ (`x : Fin N → ℝ^k`), with $\eta$ as a parameter; $\pi:X\to\{0,1\}$ is `Fin N → Fin 2`. Actions are `Option (Fin N)`: `none` is $A$, `some i` is $B_i$.
--
--   - `eta k ε` $=\eta=8\sqrt{k\varepsilon\log(1/\varepsilon)}$ (16), natural log.
--   - `eOne k` $=e_1$; `bench x β i` $=f_\beta(x_i)$ with $f_1(x)=e_1$, $f_2(x)=x$.
--   - Costs (17): $c_A=\tfrac12\mathbf 1$, $c_{B_i}=c_A-k(x_i-\bar v)+(\tfrac1{256}-2\eta)\mathbf 1$ (`costA`, `costB`, `cost`).
--   - $A_\pi=\{A\}\cup\{B_i:\pi(x_i)=1\}$ (`avail`); $a_\pi(r)\in\arg\min_{a\in A_\pi}\langle r,c_a\rangle$ with ties broken by a fixed order: $A$ first, then the $B_i$ in the order of a permutation $\sigma$ (`aSel`); $\ell^{\mathrm{hard}}_\pi(r,y)=(c_{a_\pi(r)})_y$ (`hardLoss`) (18).
--   - $\gamma=\eta/(8\log(N+1))$ (19) (`gam`); $H_\pi(r)=-\gamma\log\sum_{a\in A_\pi}e^{-\langle r,c_a\rangle/\gamma}$ (20) (`softMin`); $w_a(r)=e^{-\langle r,c_a\rangle/\gamma}/\sum_{a'\in A_\pi}e^{-\langle r,c_{a'}\rangle/\gamma}$ (30) (`softWeight`); $\nabla H_\pi(r)=\sum_{a\in A_\pi}w_a(r)c_a$ (32) (`gradSoftMin`), the gradient of $H_\pi$ on $\mathbb R^k$.
--   - $\ell^{\mathrm{smooth}}_\pi(r,y)=\tfrac{64\varepsilon}{\eta}\big(H_\pi(r)+\langle\nabla H_\pi(r),e_y-r\rangle-\tfrac14+\tfrac\eta8\big)$ (21) (`smoothLoss`).
--   - $\alpha_b(x_i)=(3-2b)\eta/(\langle e_1,c_{B_i}-c_A\rangle+2\eta)$ (22) (`alpha`); $q_b(x_i)=\alpha_b(x_i)f_1(x_i)+(1-\alpha_b(x_i))f_2(x_i)$ (23) (`qLip`).
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), §4.1, pp. 16–17, equations (16)–(23); (30), (32) on p. 19

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses
import Definitions.Def_MulticlassOmni_Lipschitz_Packings

noncomputable section

open Classical

namespace MulticlassOmni.Lipschitz

/-! # The lower-bound construction of Section 4.1

Hu, Luo, Schneider, Yang (2026), *Sample Complexity of Multiclass Omniprediction*, supplied PDF,
§4.1, pp. 16–17, equations (16)–(24).

The construction is built on an enumerated domain `x : Fin N → ℝ^k` (`x i` is the source's
`x_{i+1}`); whether `x` is the truncated Lemma B.2 packing is the separate predicate
`IsSection41Packing`. The parameter `η` is an argument (Lemma B.3 treats it as the parameter); in
§4.1 it is `η = eta k ε = 8 √(k ε log(1/ε))` (16). Functions `π, θ : X → {0, 1}` are
`Fin N → Fin 2`, read at `x_i` as `π i`. Actions are `Option (Fin N)`: `none` is the action `A`
and `some i` is `B_i`. -/

variable {k N : ℕ}

/-- `η := 8 √(k ε log(1/ε))`, equation (16) (natural logarithm). -/
def eta (k : ℕ) (ε : ℝ) : ℝ := 8 * Real.sqrt ((k : ℝ) * ε * Real.log (1 / ε))

/-- The point mass `e_1` on the source's label `1` (the index `0`). -/
def eOne (k : ℕ) : Fin k → ℝ := fun y => if (y : ℕ) = 0 then 1 else 0

/-- The benchmarks `f_1(x) = e_1` and `f_2(x) = x` (p. 16), evaluated at `x_i`; `β ∈ {1, 2}` is the
source's index (any `β ≠ 1` gives `f_2`). -/
def bench (x : Fin N → Fin k → ℝ) (β : ℕ) (i : Fin N) : Fin k → ℝ :=
  if β = 1 then eOne k else x i

/-- `c_A := (1/2) 1`, equation (17). -/
def costA (k : ℕ) : Fin k → ℝ := fun _ => 1 / 2

/-- `c_{B_i} := c_A - k (x_i - v̄) + (1/256 - 2η) 1`, equation (17). -/
def costB (x : Fin N → Fin k → ℝ) (η : ℝ) (i : Fin N) : Fin k → ℝ :=
  fun y => costA k y - (k : ℝ) * (x i y - vbar k y) + (1 / 256 - 2 * η)

/-- The cost vector of an action: `c_A` for `A = none`, `c_{B_i}` for `B_i = some i`. -/
def cost (x : Fin N → Fin k → ℝ) (η : ℝ) : Option (Fin N) → Fin k → ℝ
  | none => costA k
  | some i => costB x η i

/-- The available action set `A_π := {A} ∪ {B_i : π(x_i) = 1}`, equation (18). -/
def avail (π : Fin N → Fin 2) : Finset (Option (Fin N)) :=
  insert none ((Finset.univ.filter (fun i => π i = 1)).image some)

/-- The action selector `a_π(r) ∈ argmin_{a ∈ A_π} ⟨r, c_a⟩`, equation (18), with ties broken by
a fixed total ordering of the actions in which `A` comes first and `B_i` precedes `B_j` when
`σ i < σ j`, for a permutation `σ` of the indices. -/
def aSel (x : Fin N → Fin k → ℝ) (η : ℝ) (π : Fin N → Fin 2) (σ : Equiv.Perm (Fin N))
    (r : Fin k → ℝ) : Option (Fin N) :=
  if ∀ a ∈ avail π, dot r (costA k) ≤ dot r (cost x η a) then none
  else
    let M := Finset.univ.filter
      (fun i => π i = 1 ∧ ∀ a ∈ avail π, dot r (costB x η i) ≤ dot r (cost x η a))
    if h : (M.image σ).Nonempty then some (σ.symm ((M.image σ).min' h)) else none

/-- The hard loss `ℓ^hard_π(r, y) := (c_{a_π(r)})_y`, equation (18). -/
def hardLoss (x : Fin N → Fin k → ℝ) (η : ℝ) (π : Fin N → Fin 2) (σ : Equiv.Perm (Fin N)) :
    Loss k :=
  fun r y => cost x η (aSel x η π σ r) y

/-- `γ := η / (8 log(N + 1))`, equation (19). -/
def gam (N : ℕ) (η : ℝ) : ℝ := η / (8 * Real.log ((N : ℝ) + 1))

/-- The soft-min `H_π(r) := -γ log ∑_{a ∈ A_π} exp(-⟨r, c_a⟩/γ)`, equation (20), as a function on
all of `ℝ^k`. -/
def softMin (x : Fin N → Fin k → ℝ) (η : ℝ) (π : Fin N → Fin 2) (r : Fin k → ℝ) : ℝ :=
  -(gam N η) * Real.log (∑ a ∈ avail π, Real.exp (-(dot r (cost x η a)) / gam N η))

/-- The soft-min weights `w_a(r) := exp(-⟨r, c_a⟩/γ) / ∑_{a' ∈ A_π} exp(-⟨r, c_{a'}⟩/γ)`,
equation (30). -/
def softWeight (x : Fin N → Fin k → ℝ) (η : ℝ) (π : Fin N → Fin 2) (r : Fin k → ℝ)
    (a : Option (Fin N)) : ℝ :=
  Real.exp (-(dot r (cost x η a)) / gam N η) /
    ∑ a' ∈ avail π, Real.exp (-(dot r (cost x η a')) / gam N η)

/-- The gradient `∇H_π(r) = ∑_{a ∈ A_π} w_a(r) c_a` of the ambient smooth function `H_π`
(equation (32)). -/
def gradSoftMin (x : Fin N → Fin k → ℝ) (η : ℝ) (π : Fin N → Fin 2) (r : Fin k → ℝ) :
    Fin k → ℝ :=
  ∑ a ∈ avail π, softWeight x η π r a • cost x η a

/-- The smoothed loss
`ℓ^smooth_π(r, y) := (64ε/η) (H_π(r) + ⟨∇H_π(r), e_y - r⟩ - 1/4 + η/8)`, equation (21). -/
def smoothLoss (x : Fin N → Fin k → ℝ) (η ε : ℝ) (π : Fin N → Fin 2) : Loss k :=
  fun r y => (64 * ε / η) *
    (softMin x η π r + dot (gradSoftMin x η π r) (unitVec y - r) - 1 / 4 + η / 8)

/-- The mixture coefficients `α_b(x_i) := (3 - 2b) η / (⟨e_1, c_{B_i} - c_A⟩ + 2η)`,
equation (22). -/
def alpha (x : Fin N → Fin k → ℝ) (η : ℝ) (b : Fin 2) (i : Fin N) : ℝ :=
  (3 - 2 * ((b : ℕ) : ℝ)) * η / (dot (eOne k) (costB x η i - costA k) + 2 * η)

/-- The label distributions `q_b(x_i) := α_b(x_i) f_1(x_i) + (1 - α_b(x_i)) f_2(x_i)`,
equation (23). -/
def qLip (x : Fin N → Fin k → ℝ) (η : ℝ) (b : Fin 2) (i : Fin N) : Fin k → ℝ :=
  alpha x η b i • eOne k + (1 - alpha x η b i) • x i

end MulticlassOmni.Lipschitz


