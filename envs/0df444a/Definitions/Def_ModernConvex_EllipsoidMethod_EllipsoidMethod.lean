-- Prove2me | Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod
-- name    : ModernConvex_EllipsoidMethod_EllipsoidMethod
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:18.09868+00:00
-- url     : https://prove2.me/theorems/38655858-b4f8-42c4-8eb4-d597c369b9db
-- title:
--   Black box–represented convex programs, separation and first order oracles, and the Ellipsoid Method
-- statement:
--   Fix $n \ge 1$ and write vectors of $\mathbb R^n$ as functions $\{0,\dots,n-1\} \to \mathbb R$, with $\|x\|_2 = \sqrt{x^Tx}$. The file defines the objects of §5.2 of the book (pp. 342–348).
--
--   1. **The program** (5.2.9) $\min_x\{f(x) : x \in X \subset \mathbb R^n\}$ with **assumption A**: $f : \mathbb R^n \to \mathbb R$ is convex; $X$ is a closed, bounded, convex set with nonempty interior; $r, R \in (0,\infty)$; $X \subset \{x \mid \|x\|_2 \le R\}$, and $X \supset \{x \mid \|x - \bar x\|_2 \le r\}$ for some (unknown) $\bar x$.
--   2. A **separation oracle** for $X$: a map $\mathrm{Sep}$ that, at a query $x$, reports "$x \in X$" exactly when $x \in X$, and otherwise returns a vector $a \ne 0$ with $a^Tx \ge a^Ty$ for every $y \in X$ (5.2.10).
--   3. A **subgradient** of $f$ at $x$: a vector $\eta$ with $f(y) \ge f(x) + \eta^T(y - x)$ for all $y \in \mathbb R^n$ (5.2.11). A **first order oracle** $\mathcal O(f)$ returns, at every query $x$, the value $f(x)$ and a subgradient $f'(x)$ of $f$ at $x$.
--   4. The **ellipsoid** $E(c, B) = \{x = c + Bu \mid u^Tu \le 1\}$ for an $n \times n$ matrix $B$, the **half-ellipsoid** $\widehat E = \{x \in E(c,B) \mid a^Tx \le a^Tc\}$, and the update (5.2.13)/(5.2.16):
--   $$p = \frac{B^Ta}{\sqrt{a^TBB^Ta}},\qquad c^+ = c - \frac{1}{n+1}Bp,\qquad B^+ = \frac{n}{\sqrt{n^2-1}}B + \Big(\frac{n}{n+1} - \frac{n}{\sqrt{n^2-1}}\Big)(Bp)p^T,$$
--   and the radius $\rho(B) = |\operatorname{Det} B|^{1/n}$.
--   5. **The Ellipsoid Method** with accuracy $\epsilon > 0$ (pp. 346–348). Initialization: $c_0 = 0$, $B_0 = RI$, $L_0 = 0$. Step $t = 1, 2, \dots$: (1) query $\mathrm{Sep}$ at $c_{t-1}$; if it returns a separator $a$, the step is *nonproductive*, $a_t = a$, $L_t = L_{t-1}$. (2) Otherwise (a *productive* step) query $\mathcal O(f)$ at $c_{t-1}$; if the subgradient $a$ is $0$, terminate with result $c_{t-1}$; else $a_t = a$, $\ell_t = R\|a_t\|_2 - a_t^Tc_{t-1}$, $L_t = \max\{L_{t-1}, \ell_t\}$. (3) $c_t = c_{t-1}^+$, $B_t = B_{t-1}^+$ computed from $a_t$ as in item 4. (4) If $\rho(B_t)/r < \epsilon/(L_t + \epsilon)$ (5.2.17), terminate with result the best (smallest oracle value of $f$) of the search points $c_{\tau-1}$ of the productive steps $\tau \le t$ — undefined if there is none; otherwise go to step $t+1$.
--   6. The method **terminates at step $t$** with a given result if it was still running after $t-1$ steps and stopped in step $t$.
--
--   **Formalization Note** The Euclidean norm is defined explicitly because Mathlib's norm on `Fin n → ℝ` is the sup norm; volumes elsewhere in the mission are Lebesgue measure on `Fin n → ℝ`. The oracles are arbitrary functions of the query point satisfying their specifications, so every statement about the method holds for every such pair of oracles. The method is a function `run` from the number of performed steps to an outcome (`running` with the current $c_t, B_t, L_t$ and best productive point, or `stopped` with a result of type `Option`, `none` meaning "not defined"); a stopped run stays stopped. Among equally good productive points the earliest one is kept. $\ell_t$ is the book's closed form $R\|a_t\|_2 - a_t^Tc_{t-1}$, which the book shows equals $\max_{y \in E_0}[a_t^Ty - a_t^Tc_{t-1}]$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 342–343 ((5.2.9), assumption A, (5.2.10), (5.2.11), oracles), p. 344 ((5.2.13)), pp. 346–348 (The Ellipsoid Method, (5.2.16), (5.2.17))

import Mathlib

open Matrix

namespace ModernConvex.EllipsoidMethod

/-- The Euclidean norm `‖x‖₂ = √(xᵀx)` on `ℝⁿ = Fin n → ℝ` (Mathlib's own norm on `Fin n → ℝ`
is the sup norm, so it is not used). -/
noncomputable def eucNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (x ⬝ᵥ x)

/-- The setting of the convex program (5.2.9) `min_x {f(x) : x ∈ X ⊂ ℝⁿ}` with assumption **A**
(Ben-Tal–Nemirovski, p. 342): `f : ℝⁿ → ℝ` is convex, `X` is a closed and bounded convex set with
a nonempty interior, `r, R ∈ (0, ∞)`, `X` is contained in the ball `{x | ‖x‖₂ ≤ R}` centred at the
origin and contains some Euclidean ball `{x | ‖x − x̄‖₂ ≤ r}` (only `r` is known, not `x̄`). -/
def IsBlackBoxProgram {n : ℕ} (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧ Convex ℝ X ∧ IsClosed X ∧ Bornology.IsBounded X ∧
    (interior X).Nonempty ∧ 0 < r ∧ 0 < R ∧ X ⊆ {x | eucNorm x ≤ R} ∧
    ∃ xbar : Fin n → ℝ, {x | eucNorm (x - xbar) ≤ r} ⊆ X

/-- A separation oracle `Sep(X)` (p. 342): given `x ∈ ℝⁿ` it reports `x ∈ X` (`none`) exactly
when `x ∈ X`, and otherwise returns a vector `a ≠ 0` separating `x` from `X` in the sense of
(5.2.10), `aᵀx ≥ sup_{y ∈ X} aᵀy`. -/
def IsSeparationOracle {n : ℕ} (X : Set (Fin n → ℝ)) (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) :
    Prop :=
  ∀ x : Fin n → ℝ, (sep x = none ↔ x ∈ X) ∧
    ∀ a : Fin n → ℝ, sep x = some a → a ≠ 0 ∧ ∀ y ∈ X, a ⬝ᵥ y ≤ a ⬝ᵥ x

/-- `η` is a subgradient of `f` at `x` (5.2.11): `f(y) ≥ f(x) + ηᵀ(y − x)` for all `y ∈ ℝⁿ`. -/
def IsSubgradient {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x η : Fin n → ℝ) : Prop :=
  ∀ y : Fin n → ℝ, f x + η ⬝ᵥ (y - x) ≤ f y

/-- A first order oracle `O(f)` (p. 343): given `x ∈ ℝⁿ` it returns the value `f(x)` (first
component) and a subgradient `f′(x) ∈ ∂f(x)` (second component). -/
def IsFirstOrderOracle {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) : Prop :=
  ∀ x : Fin n → ℝ, (O x).1 = f x ∧ IsSubgradient f x (O x).2

/-- The ellipsoid `E = {x = c + Bu | uᵀu ≤ 1}` (p. 343). -/
def ellipsoid {n : ℕ} (c : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ u : Fin n → ℝ, u ⬝ᵥ u ≤ 1 ∧ x = c + B *ᵥ u}

/-- The half-ellipsoid `Ê = {x ∈ E | aᵀx ≤ aᵀc}` (pp. 343–344). -/
def halfEllipsoid {n : ℕ} (c : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | x ∈ ellipsoid c B ∧ a ⬝ᵥ x ≤ a ⬝ᵥ c}

/-- `p = Bᵀa / √(aᵀBBᵀa)` of (5.2.13) and (5.2.16). -/
noncomputable def cutDirection {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    Fin n → ℝ :=
  (1 / Real.sqrt (a ⬝ᵥ ((B * Bᵀ) *ᵥ a))) • (Bᵀ *ᵥ a)

/-- The new centre `c⁺ = c − (1/(n+1)) Bp` of (5.2.13) and (5.2.16). -/
noncomputable def nextCenter {n : ℕ} (c : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) : Fin n → ℝ :=
  c - (1 / ((n : ℝ) + 1)) • (B *ᵥ cutDirection B a)

/-- The new matrix `B⁺ = (n/√(n²−1)) B + (n/(n+1) − n/√(n²−1)) (Bp)pᵀ` of (5.2.13) and
(5.2.16). -/
noncomputable def nextMatrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) / Real.sqrt ((n : ℝ) ^ 2 - 1)) • B +
    ((n : ℝ) / ((n : ℝ) + 1) - (n : ℝ) / Real.sqrt ((n : ℝ) ^ 2 - 1)) •
      vecMulVec (B *ᵥ cutDirection B a) (cutDirection B a)

/-- `ρ = |Det B|^{1/n}`, the radius of the Euclidean ball with the volume of `{c + Bu | uᵀu ≤ 1}`
(p. 347). -/
noncomputable def radius {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  |B.det| ^ ((1 : ℝ) / (n : ℝ))

/-- The data the ellipsoid method carries from step `t` to step `t + 1` (p. 347): the ellipsoid
`E_t = {c_t + B_t u | uᵀu ≤ 1}`, the guess `L_t`, and the best (smallest value of `f`, as
reported by the first order oracle) of the search points `c_{τ−1}` of the productive steps
`τ ≤ t` (`none` while there is no productive step). -/
structure State (n : ℕ) where
  c : Fin n → ℝ
  B : Matrix (Fin n) (Fin n) ℝ
  L : ℝ
  best : Option (Fin n → ℝ)

/-- Initialization (p. 346): `c₀ = 0`, `B₀ = RI`, `L₀ = 0`, no search point yet
(`ρ₀ = R` is `radius B₀`). -/
noncomputable def initState {n : ℕ} (R : ℝ) : State n where
  c := 0
  B := R • (1 : Matrix (Fin n) (Fin n) ℝ)
  L := 0
  best := none

/-- Keep the better of the recorded best point and the new productive search point `x`,
comparing the values `f` reported by the first order oracle `O`. -/
noncomputable def updateBest {n : ℕ} (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ))
    (best : Option (Fin n → ℝ)) (x : Fin n → ℝ) : Option (Fin n → ℝ) :=
  match best with
  | none => some x
  | some y => if (O x).1 < (O y).1 then some x else some y

/-- The result of rules 1–3 of a step: either termination by rule 2 with the point `c_{t−1}`
(zero subgradient at a feasible centre), or the new data of rule 3. -/
inductive StepResult (n : ℕ) where
  | optimal (x : Fin n → ℝ)
  | next (s : State n)

/-- Rules 1–3 of step `t` of the ellipsoid method (p. 347), applied to the data `s` of step
`t − 1`.
1. Call `Sep(X)` at `c_{t−1}`; if it returns a separator `a`, the step is nonproductive:
   `a_t = a`, `L_t = L_{t−1}`.
2. Otherwise call `O(f)` at `c_{t−1}`; if the subgradient `a` is `0`, terminate with `c_{t−1}`;
   else `a_t = a`, `ℓ_t = R‖a_t‖₂ − a_tᵀc_{t−1}`, `L_t = max{L_{t−1}, ℓ_t}`, and `c_{t−1}` joins
   the productive search points.
3. `c_t, B_t` by (5.2.16). -/
noncomputable def step {n : ℕ} (sep : (Fin n → ℝ) → Option (Fin n → ℝ))
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (R : ℝ) (s : State n) : StepResult n :=
  match sep s.c with
  | some a => StepResult.next
      { c := nextCenter s.c s.B a, B := nextMatrix s.B a, L := s.L, best := s.best }
  | none =>
      if (O s.c).2 = 0 then StepResult.optimal s.c
      else StepResult.next
        { c := nextCenter s.c s.B (O s.c).2
          B := nextMatrix s.B (O s.c).2
          L := max s.L (R * eucNorm (O s.c).2 - (O s.c).2 ⬝ᵥ s.c)
          best := updateBest O s.best s.c }

/-- Where the method stands after `t` steps: still running with the data of step `t`, or
terminated with its result (`none` if the result is not defined). -/
inductive Outcome (n : ℕ) where
  | running (s : State n)
  | stopped (result : Option (Fin n → ℝ))

/-- The ellipsoid method with accuracy `ε` (pp. 346–348), run for `t` steps. Rule 4: after rule 3
of step `t`, terminate if `ρ_t / r < ε / (L_t + ε)` (5.2.17) and output the best of the
productive search points `c_{τ−1}`, `τ ≤ t`; else go to step `t + 1`. A terminated run stays
terminated. -/
noncomputable def run {n : ℕ} (sep : (Fin n → ℝ) → Option (Fin n → ℝ))
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (R r ε : ℝ) : ℕ → Outcome n
  | 0 => Outcome.running (initState R)
  | t + 1 =>
      match run sep O R r ε t with
      | Outcome.stopped x => Outcome.stopped x
      | Outcome.running s =>
          match step sep O R s with
          | StepResult.optimal x => Outcome.stopped (some x)
          | StepResult.next s' =>
              if radius s'.B / r < ε / (s'.L + ε) then Outcome.stopped s'.best
              else Outcome.running s'

/-- The method terminates at step `t ≥ 1` (by rule 2 or rule 4) with the given result: it was
still running after `t − 1` steps and has stopped after `t`. -/
def TerminatesAt {n : ℕ} (sep : (Fin n → ℝ) → Option (Fin n → ℝ))
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (R r ε : ℝ) (t : ℕ)
    (result : Option (Fin n → ℝ)) : Prop :=
  1 ≤ t ∧ (∃ s : State n, run sep O R r ε (t - 1) = Outcome.running s) ∧
    run sep O R r ε t = Outcome.stopped result

end ModernConvex.EllipsoidMethod


