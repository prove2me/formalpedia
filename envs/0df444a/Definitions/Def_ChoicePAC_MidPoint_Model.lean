-- Prove2me | Definitions.Def_ChoicePAC_MidPoint_Model
-- name    : ChoicePAC_MidPoint_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:37.822613+00:00
-- url     : https://prove2.me/theorems/7905400c-2c81-4421-a45f-f501a8947f43
-- title:
--   Sec. 2 — network RM with customer choice, the DLP (2), and the PAC heuristic
-- statement:
--   **The model** (Jasin–Kumar, Sec. 2.1, p. 315). The selling horizon is $[0,1]$. There are $N$ customer types $q$, $n$ offers $j$ and $m$ resources $i$. Type $q$ arrives as a Poisson process of rate $\lambda_q \ge 0$, independently of the other types. Each offer $j$ belongs to one type $q(j)$; $P$ is the incidence matrix, $P_{q,j} = 1$ iff $q = q(j)$, and $S_q = \{j : q(j) = q\}$. When offer $j$ is presented it consumes a random vector $A^j$ of resources, with law $D_j$, i.i.d. across presentations, and earns $r_j(A^j)$, with $r_j(0) = 0$. The resource $i$ starts with capacity $C_i$. Write $\bar A = \mathbb E[A]$, $\bar r_j = \mathbb E[r_j(A^j)]$, and $\xi_{\max} = \max_j \xi_j$, where $\xi_j \ge A_{ij}$ almost surely.
--
--   **The DLP** (2), p. 316. For a capacity $c$ and demand $d$,
--   $$\mathrm{DLP}[c,d]:\quad \max\ \bar r^{\top}x \quad\text{s.t.}\quad \bar A x \le c,\ P x \le d,\ x \ge 0.$$
--   Its optimal value is written $\mathrm{dlpValue}(c,d)$, and $V^k_{\mathrm{DLP}} = \mathrm{dlpValue}(kC, k\lambda)$.
--
--   **Selectors.** An admissible selector $\mathrm{sel}$ maps a capacity $c \ge 0$ and a demand $d \ge 0$ to an optimal solution of $\mathrm{DLP}[c,d]$, and is measurable in $c$.
--
--   **PAC** (Sec. 2.3, pp. 316–317). Given re-solving times $0 = t_0 < t_1 < \dots < t_M < t_{M+1} = 1$, at each $t_\ell$ PAC solves $\mathrm{DLP}[C(t_\ell), (1-t_\ell)k\lambda]$, obtaining $Y$, and on $[t_\ell, t_{\ell+1})$ offers $j \in S_q$ to an arriving type-$q$ customer with probability $p_j = Y_j/((1-t_\ell)k\lambda_q)$ and presents it only if $C(t) - \xi_j \ge 0$ on every resource. In the $k$-th system (Sec. 2.4, p. 317) capacities are $kC$ and rates $k\lambda$. $\mathbb E[R^k_{\mathrm{PAC}}]$ is computed by backward recursion over the windows: on a window of length $\ell$, the number of arrivals is Poisson$(k\Lambda\ell)$, $\Lambda = \sum_q \lambda_q$, and arrival types are i.i.d. with law $\lambda_q/\Lambda$.
--
--   **Schedules.** Mid-point PAC uses $t_l = 1 - 2^{-l}$, $l = 1,\dots,M^k$, with $M^k$ the smallest integer such that $2^{-M^k} \le 1/k$. Periodic PAC with period $h>0$ uses $t_l = lh$, $l = 1,\dots,M$, with $M$ the unique integer such that $1-h \le Mh < 1$.
--
--   These are the objects of every statement in the mission.
--
--   **Formalization Note** Types are `Fin NT`, offers `Fin n`, resources `Fin m`; the instance bundles `typ`, `lam`, `C`, `D`, `ξ`, `rev`. The standing hypotheses (`IsValid`) are the disclosed reading of Sec. 2.1, p. 315, Sec. 2.3, p. 317 and Sec. 5.2, p. 327: printed are $\lambda_q \ge 0$, bounded nonnegative consumption and $r_j(0)=0$; read in are $C \ge 0$, consumption laws that are probability measures, $A_{ij} \le \xi_j$ almost surely (the page writes $\xi_j \ge A_{ij}$ on p. 317 and $A_{ij} < \xi_j$ on p. 327; the weaker $\le$ is used), measurable revenue functions, and revenue that is nonnegative and bounded by a common constant (implicit on the page, needed in App. C.4). The reading $\bar r_j = \mathbb E[r_j(A^j)]$ is fixed by App. A.1, p. 332 (the page never defines $\bar r$). Footnote 3, p. 316 leaves ties after time 0 open, so PAC is parametrized by every optimal selector; measurability in the capacity is a disclosed reading (it makes $R_{\mathrm{PAC}}$ a random variable; the lexicographically smallest optimum is such a selector). The window value uses the Poisson representation (superposition and marking), exact for a policy whose offer probabilities are constant on the window. `Nat.iterate` of the one-arrival operator is the value of $N$ arrivals. Step (iii)'s early stop changes no revenue and is not encoded. $M^k$ is `Nat.clog 2 k`; for $k=1$ there is no re-solve. The periodic $M$ is $\lceil 1/h\rceil - 1$. The Poisson weight clamps a negative mean to $0$ (never used). Lean's $x/0 = 0$ gives $p_j = 0$ when $\lambda_{q(j)} = 0$.
-- source:
--   Jasin, Kumar, A Re-Solving Heuristic with Bounded Revenue Loss for Network Revenue Management with Customer Choice, Math. Oper. Res. 37(2), 2012, Sec. 2.1–2.4, pp. 315–317, DLP (2)

import Mathlib

namespace ChoicePAC.MidPoint

open MeasureTheory Matrix

/-- An instance of network revenue management with customer choice (Jasin–Kumar, Sec. 2.1, p. 315):
`NT` customer types `q`, `n` offers `j`, `m` resources `i`.
* `typ j` is the customer type `q(j)` with which offer `j` is associated;
* `lam q` is the Poisson arrival rate `λ_q` of type `q`;
* `C i` is the initial capacity of resource `i`;
* `D j` is the law of the random consumption vector `A^j` (the `j`-th column of `A`);
* `ξ j` is the threshold of offer `j` used by the capacity check of PAC (`ξ_j ≥ A_ij`);
* `rev j a` is the revenue `r_j(a)` earned when offer `j` is presented and consumes `a`. -/
structure Instance (NT n m : ℕ) where
  typ : Fin n → Fin NT
  lam : Fin NT → ℝ
  C : Fin m → ℝ
  D : Fin n → Measure (Fin m → ℝ)
  ξ : Fin n → ℝ
  rev : Fin n → (Fin m → ℝ) → ℝ

namespace Instance

variable {NT n m : ℕ} (I : Instance NT n m)

/-- The incidence matrix `P`: `P q j = 1` iff `q = q(j)` (Sec. 2.1, p. 315). -/
def P : Matrix (Fin NT) (Fin n) ℝ := fun q j => if I.typ j = q then 1 else 0

/-- The set `S_q = {j : q(j) = q}` of offers of type `q`. -/
def S (q : Fin NT) : Finset (Fin n) := Finset.univ.filter (fun j => I.typ j = q)

/-- Standing hypotheses of the model (Sec. 2.1, p. 315; Sec. 2.3, p. 317; Sec. 5.2, p. 327):
nonnegative rates and capacities; each consumption law is a probability measure carried by
`{a : 0 ≤ a i ≤ ξ_j for all i}` (bounded, nonnegative consumption, below the threshold `ξ_j`);
measurable revenue functions with `r_j(0) = 0`, nonnegative and bounded by a common constant. -/
def IsValid : Prop :=
  0 ≤ I.lam ∧ 0 ≤ I.C ∧ (∀ j, IsProbabilityMeasure (I.D j)) ∧
    (∀ j, ∀ᵐ a ∂(I.D j), ∀ i, 0 ≤ a i ∧ a i ≤ I.ξ j) ∧
    (∀ j, Measurable (I.rev j)) ∧ (∀ j, I.rev j 0 = 0) ∧
    ∃ R : ℝ, ∀ j a, 0 ≤ I.rev j a ∧ I.rev j a ≤ R

/-- The mean consumption matrix `Ā = E[A]`: `Ā i j = E[A_ij]`. -/
noncomputable def Abar : Matrix (Fin m) (Fin n) ℝ := fun i j => ∫ a, a i ∂(I.D j)

/-- The mean revenue vector `r̄_j = E[r_j(A^j)]`. -/
noncomputable def rbar : Fin n → ℝ := fun j => ∫ a, I.rev j a ∂(I.D j)

/-- `ξ_max = max_j ξ_j` (Sec. 5.2, p. 327); for `n = 0` it is `0`. -/
noncomputable def ξmax : ℝ := ⨆ j, I.ξ j

/-- Feasibility for `DLP[c, d]` (2), p. 316: `Ā x ≤ c`, `P x ≤ d`, `x ≥ 0`. -/
def DLPFeasible (c : Fin m → ℝ) (d : Fin NT → ℝ) (x : Fin n → ℝ) : Prop :=
  I.Abar *ᵥ x ≤ c ∧ I.P *ᵥ x ≤ d ∧ 0 ≤ x

/-- `x` is an optimal solution of `DLP[c, d]`: feasible, and no feasible point has larger objective
`r̄ ⬝ x`. -/
def IsDLPOptimal (c : Fin m → ℝ) (d : Fin NT → ℝ) (x : Fin n → ℝ) : Prop :=
  I.DLPFeasible c d x ∧ ∀ y, I.DLPFeasible c d y → I.rbar ⬝ᵥ y ≤ I.rbar ⬝ᵥ x

/-- The optimal value of `DLP[c, d]` (2), p. 316: `sup {r̄ ⬝ x : Ā x ≤ c, P x ≤ d, x ≥ 0}`.
For `c ≥ 0`, `d ≥ 0` the set is nonempty (`x = 0`) and bounded above (`0 ≤ x_j ≤ d_{q(j)}`),
so this is the maximum. `V^k_DLP` is `dlpValue (k • C) (k • lam)`. -/
noncomputable def dlpValue (c : Fin m → ℝ) (d : Fin NT → ℝ) : ℝ :=
  sSup {v | ∃ x, I.DLPFeasible c d x ∧ v = I.rbar ⬝ᵥ x}

/-- An optimal-solution selector for the DLP: for every capacity `c ≥ 0` and demand `d ≥ 0`,
`sel c d` is an optimal solution of `DLP[c, d]`. It models PAC's "solve DLP" with an arbitrary
tie-breaking rule (footnote 3, p. 316). -/
def IsDLPSelector (sel : (Fin m → ℝ) → (Fin NT → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ c d, 0 ≤ c → 0 ≤ d → I.IsDLPOptimal c d (sel c d)

/-- An admissible selector: an optimal-solution selector that is measurable in the capacity, so
that the revenue of PAC is a random variable. -/
def IsAdmissibleSelector (sel : (Fin m → ℝ) → (Fin NT → ℝ) → (Fin n → ℝ)) : Prop :=
  I.IsDLPSelector sel ∧ ∀ d, Measurable (fun c => sel c d)

/-- The Poisson probability mass function `P(N = N₀) = e^{−μ} μ^{N₀} / N₀!` with mean `μ ≥ 0`
(a negative mean is read as `0`; it never occurs below). -/
noncomputable def poissonWeight (μ : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-(max μ 0)) * (max μ 0) ^ N / (N.factorial : ℝ)

/-- Total arrival rate `Λ = Σ_q λ_q`. -/
def Λ : ℝ := ∑ q, I.lam q

/-- One arrival under PAC (Sec. 2.3 (ii)(a)–(b), pp. 316–317), with offer probabilities `p` and
continuation value `W` of the remaining capacity. The arrival has type `q` with probability
`λ_q / Λ`; offer `j ∈ S_q` is picked with probability `p_j` (nothing with probability
`1 − Σ_{j∈S_q} p_j`); the offer is presented iff `ξ_j ≤ c_i` for every resource `i`, in which case
`A^j ~ D_j` is consumed and `r_j(A^j)` is earned. -/
noncomputable def pacStep (p : Fin n → ℝ) (W : (Fin m → ℝ) → ℝ) (c : Fin m → ℝ) : ℝ :=
  ∑ q, (I.lam q / I.Λ) *
    ((1 - ∑ j ∈ I.S q, p j) * W c +
      ∑ j ∈ I.S q, p j *
        (if ∀ i, I.ξ j ≤ c i then ∫ a, (I.rev j a + W (c - a)) ∂(I.D j) else W c))

/-- Expected value of a PAC window of length `ℓ` in the `k`-th system, starting with capacity `c`,
with constant offer probabilities `p`, followed by the continuation value `W` of the capacity left at
the end of the window. The window holds `N ~ Poisson(k Λ ℓ)` arrivals with i.i.d. types of law
`λ_q / Λ` (superposition and marking of independent Poisson processes). -/
noncomputable def windowValue (k : ℕ) (ℓ : ℝ) (p : Fin n → ℝ) (c : Fin m → ℝ)
    (W : (Fin m → ℝ) → ℝ) : ℝ :=
  ∑' N : ℕ, poissonWeight ((k : ℝ) * I.Λ * ℓ) N * (I.pacStep p)^[N] W c

end Instance

/-- A re-solving schedule `Γ = {0 < t_1 < ⋯ < t_M < 1}` (Sec. 2.3, p. 316). In Lean `t l` for
`l : Fin M` is the paper's `t_{l+1}`. -/
structure Schedule where
  M : ℕ
  t : Fin M → ℝ
  strictMono : StrictMono t
  pos : ∀ l, 0 < t l
  lt_one : ∀ l, t l < 1

namespace Schedule

/-- The paper's `t_l` for every `l : ℕ`, with `t_0 = 0` and `t_l = 1` for `l ≥ M + 1`. -/
def time (s : Schedule) (l : ℕ) : ℝ :=
  if l = 0 then 0 else if h : l - 1 < s.M then s.t ⟨l - 1, h⟩ else 1

end Schedule

/-- The mid-point schedule of the `k`-th system (Sec. 2.3, p. 316; Sec. 2.4, p. 317):
`t_l = 1 − 2^{−l}`, `l = 1, …, M^k`, with `M^k = Nat.clog 2 k` the smallest integer with
`2^{−M^k} ≤ 1/k`. -/
noncomputable def midpointSchedule (k : ℕ) : Schedule where
  M := Nat.clog 2 k
  t l := 1 - (1 / 2 : ℝ) ^ (l.val + 1)
  strictMono := by
    intro a b hab
    have hab' : a.val + 1 < b.val + 1 := by simpa using hab
    have := pow_lt_pow_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hab'
    linarith
  pos l := by
    have := pow_lt_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      (by omega : l.val + 1 ≠ 0)
    linarith
  lt_one l := by
    have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (l.val + 1)
    linarith

/-- The periodic schedule with period `h > 0` (Sec. 2.3, p. 316; Sec. 2.4, p. 317):
`t_l = l h`, `l = 1, …, M`, where `M = ⌈1/h⌉ − 1` is the unique integer with `1 − h ≤ M h < 1`
(it is `0` for `h ≥ 1`). -/
noncomputable def periodicSchedule (h : ℝ) (hh : 0 < h) : Schedule where
  M := Nat.ceil (1 / h) - 1
  t l := ((l.val : ℝ) + 1) * h
  strictMono := by
    intro a b hab
    have : (a.val : ℝ) < b.val := by exact_mod_cast hab
    nlinarith
  pos l := by positivity
  lt_one l := by
    have h1 : l.val + 1 < Nat.ceil (1 / h) := by have := l.isLt; omega
    have h2 : ((l.val + 1 : ℕ) : ℝ) < 1 / h := Nat.lt_ceil.mp h1
    push_cast at h2
    rwa [lt_div_iff₀ hh] at h2

namespace Instance

variable {NT n m : ℕ} (I : Instance NT n m)

/-- PAC's offer probabilities at re-solving time `τ` with remaining capacity `c` in the `k`-th
system: `Y = sel c ((1 − τ) k λ)` and `p_j = Y_j / ((1 − τ) k λ_{q(j)})` (Sec. 2.3 (ii)(a)). -/
noncomputable def pacProbs (sel : (Fin m → ℝ) → (Fin NT → ℝ) → (Fin n → ℝ)) (k : ℕ) (τ : ℝ)
    (c : Fin m → ℝ) : Fin n → ℝ :=
  fun j => sel c ((1 - τ) • ((k : ℝ) • I.lam)) j / ((1 - τ) * k * I.lam (I.typ j))

/-- Backward recursion of PAC over the windows `[t_ℓ, t_{ℓ+1})`: `pacAux sel k s d ℓ c` is the
expected revenue from time `t_ℓ` on, with capacity `c` at `t_ℓ`, when `d` windows remain. At `t_ℓ`
PAC re-solves `DLP[c, (1 − t_ℓ) k λ]` and uses the resulting offer probabilities on the window. -/
noncomputable def pacAux (sel : (Fin m → ℝ) → (Fin NT → ℝ) → (Fin n → ℝ)) (k : ℕ) (s : Schedule) :
    ℕ → ℕ → (Fin m → ℝ) → ℝ
  | 0, _, _ => 0
  | d + 1, ℓ, c =>
      I.windowValue k (s.time (ℓ + 1) - s.time ℓ) (I.pacProbs sel k (s.time ℓ) c) c
        (pacAux sel k s d (ℓ + 1))

/-- `E[R^k_PAC]`: the expected revenue of PAC over `[0, 1)` in the `k`-th system (capacity `k C`,
rates `k λ`) with re-solving schedule `s`, i.e. the `M + 1` windows started at time `0` with
capacity `k C`. -/
noncomputable def pacValue (sel : (Fin m → ℝ) → (Fin NT → ℝ) → (Fin n → ℝ)) (k : ℕ) (s : Schedule) :
    ℝ :=
  I.pacAux sel k s (s.M + 1) 0 ((k : ℝ) • I.C)

end Instance

end ChoicePAC.MidPoint


