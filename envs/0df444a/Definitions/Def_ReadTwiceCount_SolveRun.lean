-- Prove2me | Definitions.Def_ReadTwiceCount_SolveRun
-- name    : ReadTwiceCount_SolveRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:56.994604+00:00
-- url     : https://prove2.me/theorems/682a57a0-dc8b-4122-8cfc-c2d0e1dfdd5f
-- title:
--   Runs of the marginal procedure $\mathrm{Solve}(H,h,a)$ and their total cost
-- statement:
--   A **run** of the marginal procedure $\mathrm{Solve}(H,h,a)$ with global clause bound $n$, returning the rational upper value $U$, is one of the following.
--
--   1. **Exact:** the query is a recognized exact case (free, zero prefix, or terminal descriptor), and $U$ is its exact value.
--   2. **Coarse:** $a\ge1$ and $U=s+1$, where $s$ is the number of clauses of $H$.
--   3. **Active:** $0<a<1$, the query is not a recognized exact case, and the run consists of a positive block of $(H,h)$ meeting the stopping rule (12), with frozen weights $D_i$. For every EQ boundary $i$ with $s_i$ clauses:
--      - if $D_i\le\left(\dfrac{as}{s_i+1}\right)^2$ (18), the lower value is $\ell_i=1$;
--      - otherwise a rational $r_i$ with $\sqrt{D_i}\le r_i\le q\sqrt{D_i}$, $q=1+\frac{1}{10n}$ (17), gives $\eta_i=as/r_i$ and $a_i=\eta_i/(s_i+1)$ (19); a sub-run of $\mathrm{Solve}(H_i,h_i,a_i)$ returns $U_i$, and $\ell_i=\max\{1,U_i-\eta_i\}$ (20).
--
--      $U$ is the block value with these lower values and the upper cut values.
--
--   The **total cost** of a run with respect to a per-call cost is the sum of the costs of all calls of the run tree, each call counted separately.
--
--   **Formalization Note** A run is any run of the procedure: any positive block meeting the stopping rule (any expansion order) and any rational $r_i$ in the allowed interval. The paper fixes a deterministic expansion order and a dyadic grid for $r_i$ (§5.1, §7.2); its procedure produces one of these runs.
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §5, pp.6–9, displays (11), (17)–(20), steps 1–4

import Mathlib
import Definitions.Def_ReadTwiceCount_IsPositiveBlock

namespace ReadTwiceCount

variable {M : ℕ}

/-- The rounding factor `q = 1 + 1/(10n)`, display (17) (He, *A Deterministic Approximation Scheme
for Counting Read-Twice CNF Assignments*, STOC 2027 submission, manuscript sha256 7a2a9dcd…, §5.3,
p.8), fixed for all recursive calls arising from one initial query. -/
noncomputable def qFactor (n : ℕ) : ℝ := 1 + 1 / (10 * (n : ℝ))

/-- **The trivial boundary test (18)** (§5.3, p.8): the frozen weight of the EQ boundary `i` of a
block of an `s`-clause state satisfies `D_i ≤ (a s/(s_i + 1))²`. -/
def TrivialBoundary (a : ℚ) (H : Formula M) (h : Lit M) (T : DTree) (i : List ℕ) : Prop :=
  frozenD H h T i ≤ ((a : ℝ) * H.clauses.length / ((clauseCountAt H h i : ℝ) + 1)) ^ 2

/-- The error allowance `ηᵢ = a s/rᵢ` of a recursive boundary, display (19). -/
def etaOf (a : ℚ) (H : Formula M) (r : ℚ) : ℚ := a * H.clauses.length / r

/-- The child density `aᵢ = ηᵢ/(sᵢ + 1)`, display (19). -/
def subDensity (a : ℚ) (H : Formula M) (h : Lit M) (r : List ℕ → ℚ) (i : List ℕ) : ℚ :=
  etaOf a H (r i) / ((clauseCountAt H h i : ℚ) + 1)

/-- The lower boundary value `ℓᵢ`: `1` at a trivial boundary (18), and `max{1, Uᵢ − ηᵢ}` (20) at a
recursive boundary with returned upper value `Uᵢ`. -/
noncomputable def lowerValue (a : ℚ) (H : Formula M) (h : Lit M) (T : DTree)
    (r Usub : List ℕ → ℚ) (i : List ℕ) : ℝ := by
  classical
  exact if TrivialBoundary a H h T i then 1 else ((max 1 (Usub i - etaOf a H (r i)) : ℚ) : ℝ)

/-- **A run of the marginal procedure `Solve(H, h, a)`** with global clause bound `n` (He, STOC 2027
submission, manuscript sha256 7a2a9dcd…, §5, pp.6–9, steps 1–4), returning the rational upper value
`U`. `SolveRun n H h a U` is the type of run trees:

1. `exact`: a recognized free or constant query (step 1) returns its exact value;
2. `coarse`: a call with `a ≥ 1` returns `s + 1` (p.6);
3. `active`: a call with `0 < a < 1` that is not a recognized exact case builds a positive block `T`
   of `(H, h)` meeting the stopping rule (12) (step 2), freezes its weights `D_i` (step 3), and for
   every EQ boundary `i` either uses `ℓᵢ = 1` when (18) holds, or chooses a rational `rᵢ` with
   `√Dᵢ ≤ rᵢ ≤ q√Dᵢ`, `q = 1 + 1/(10n)` (19), runs `Solve(Hᵢ, hᵢ, aᵢ)` returning `Uᵢ`, and sets
   `ℓᵢ = max{1, Uᵢ − ηᵢ}` (20); it returns the block value with these lower values and the upper cut
   values (step 4).

**Formalization Note** The run is any run of the procedure: the block is any positive block meeting
the stopping rule (any expansion order), and each `rᵢ` is any rational in `[√Dᵢ, q√Dᵢ]` (the paper
fixes a deterministic order and a dyadic grid, §5.1 and §7.2). The global `n` is inherited by every
sub-run. -/
inductive SolveRun (n : ℕ) : Formula M → Lit M → ℚ → ℚ → Type
  | exact {H : Formula M} {h : Lit M} {a r : ℚ} (hr : exactValue H h = some r) :
      SolveRun n H h a r
  | coarse {H : Formula M} {h : Lit M} {a : ℚ} (ha : 1 ≤ a) :
      SolveRun n H h a ((H.clauses.length : ℚ) + 1)
  | active {H : Formula M} {h : Lit M} {a U : ℚ} (ha0 : 0 < a) (ha1 : a < 1)
      (hex : exactValue H h = none) (T : DTree) (hT : IsPositiveBlock H h T)
      (hstop : StoppingRule n (a : ℝ) H h T) (r Usub : List ℕ → ℚ)
      (hr : ∀ i ∈ T.boundaries, ¬TrivialBoundary a H h T i →
        Real.sqrt (frozenD H h T i) ≤ (r i : ℝ) ∧
          (r i : ℝ) ≤ qFactor n * Real.sqrt (frozenD H h T i))
      (sub : ∀ i ∈ T.boundaries, ¬TrivialBoundary a H h T i →
        SolveRun n (stateAt H h i).1 (stateAt H h i).2 (subDensity a H h r i) (Usub i))
      (hU : (U : ℝ) = blockValue H h T (lowerValue a H h T r Usub)) :
      SolveRun n H h a U

namespace SolveRun

variable {n : ℕ}

/-- **The total cost of a run**: the sum, over all calls of the run tree (each call counted
separately, p.12), of the nonrecursive cost `cost` assigned to that call. `cost H h a U R` may depend
on the call's arguments and on its whole run `R`. -/
noncomputable def totalCost
    (cost : (H : Formula M) → (h : Lit M) → (a U : ℚ) → SolveRun n H h a U → ℝ) :
    {H : Formula M} → {h : Lit M} → {a U : ℚ} → SolveRun n H h a U → ℝ
  | H, h, a, U, R@(.exact _) => cost H h a U R
  | H, h, a, _, R@(.coarse _) => cost H h a _ R
  | H, h, a, U, R@(.active _ _ _ T _ _ _ _ _ sub _) =>
      cost H h a U R + ∑ i ∈ T.boundaries.attach, (by
        classical
        exact if hi : TrivialBoundary a H h T i.1 then 0
          else totalCost cost (sub i.1 i.2 hi))

/-- **Every call of the run** satisfies the predicate `P`. -/
def AllCalls (P : (H : Formula M) → (h : Lit M) → (a U : ℚ) → SolveRun n H h a U → Prop) :
    {H : Formula M} → {h : Lit M} → {a U : ℚ} → SolveRun n H h a U → Prop
  | H, h, a, U, R@(.exact _) => P H h a U R
  | H, h, a, _, R@(.coarse _) => P H h a _ R
  | H, h, a, U, R@(.active _ _ _ T _ _ _ _ _ sub _) =>
      P H h a U R ∧ ∀ i (hi : i ∈ T.boundaries) (ht : ¬TrivialBoundary a H h T i),
        AllCalls P (sub i hi ht)

end SolveRun

end ReadTwiceCount


