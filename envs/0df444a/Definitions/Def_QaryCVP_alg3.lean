-- Prove2me | Definitions.Def_QaryCVP_alg3
-- name    : QaryCVP_alg3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:59:53.133654+00:00
-- url     : https://prove2.me/theorems/1a853142-9331-4a63-9a12-36b0c1032339
-- title:
--   A mathematical model of Algorithm 3 ($\gamma$-CVP)
-- statement:
--   Algorithm 3 takes $H\in(\mathbb Z/q\mathbb Z)^{m\times n}$ and $y\in\mathbb Q^n$ ($q\ge2$, $n\ge1$, $m\ge0$, $\delta\le3/2$) and returns a point of $\Lambda$:
--
--   1. $z=\lfloor y\rceil$; if $m=0$ return $z$. If $q^{8m}\le2^n$ return $A(H,y)$, an exact closest point (Lemma 4.1).
--   2. $\hat x=q\lfloor y/q\rceil$. If $q=2$ and $m\ge3n/4$: return $\hat x$ if $\dim\ker H>\max\{0,n-m\}+\lceil n^{2/3}\rceil$; otherwise return the closest of $\hat x$ and $x+2\lfloor(y-x)/2\rceil$ over $x\in\ker H\subseteq\mathbb F_2^n$.
--   3. Choose $\beta,c$ from $(n,m,q)$, and set $d=\min\{n,\lceil\log_2 q^m\rceil\}$ ($q\ge3$) or $d=n$ ($q=2$), $\ell=\lceil d^{2/3}\rceil$, $\ell'=\lceil\ell/\beta\rceil$, $n_0=d-\ell-\ell'$ (15). Fall back to $A$ if $n_0\le0$, if $q=2$ and $n_0\le m$, or if $q\ge3$ and the feasibility checks fail.
--   4. Run the exact search $E_{\gamma^{-2}}$ in the ball of squared radius $b=(\|z-y\|^2+cd)/\gamma^2$ around $y$; return its output if it finds a lattice point.
--   5. Otherwise, with $s=-Hz$, make $r=\lceil Cn\rceil$ correction attempts (short solver $S$ for $q\ge3$, $S_2$ for $q=2$), each with fresh randomness, and return the closest of $\hat x$ and the candidates $z+w$, replacing the current point only by a strictly closer one.
--
--   The subprocedures $A$, $E_{\gamma^{-2}}$, $S$, $S_2$, the parameter choice $(\beta,c)$, the feasibility checks and $C$ are parameters of the model. The randomness $\omega$ is the product of the $r$ attempts' choices, each with the law of one attempt.
--
--   This is the algorithm whose correctness is Theorem 4.7.
--
--   **Formalization Note** The kernel is scanned in a fixed enumeration of its elements rather than as $B\alpha$ over a basis $B$; this changes only which point is returned among equally close candidates. $\dim\ker H>\kappa$ is tested as $|\ker H|>2^\kappa$. The feasibility checks are an arbitrary predicate of $(n,m,q)$: Theorem 4.7 does not depend on them, since every fallback is exact. $\ell'$ is taken as $\max\{1,\lceil\ell/\beta\rceil\}$, which equals $\lceil\ell/\beta\rceil$ whenever $\ell\ge1$; the two differ only when $d=0$, where the algorithm falls back before any attempt.
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Algorithm 3, p.33; §4.1, pp.33–35; (15), p.34

import Mathlib
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_corrAttempt

open MeasureTheory ProbabilityTheory

namespace QaryCVP

/-- The correction length `d` of (15), p.34: `d = min{n, ⌈δn⌉}` for `q ≥ 3` (computed as
`min{n, ⌈log₂(qᵐ)⌉}`, p.35) and `d = n` for `q = 2`. -/
def corrD (n m q : ℕ) : ℕ := if q = 2 then n else min n (Nat.clog 2 (q ^ m))

/-- `ℓ = ⌈d^{2/3}⌉` (15), p.34. -/
noncomputable def ellOf (d : ℕ) : ℕ := ⌈(d : ℝ) ^ ((2 : ℝ) / 3)⌉₊

/-- `ℓ′ = ⌈ℓ/β⌉` (15), p.34. -/
noncomputable def ell'Of (ℓ : ℕ) (β : ℚ) : ℕ := ⌈(ℓ : ℚ) / β⌉₊

/-- `ℓ` at the instance `(n, m, q)`. -/
noncomputable def ellA (n m q : ℕ) : ℕ := ellOf (corrD n m q)

/-- `ℓ′` at the instance `(n, m, q)`, with the parameter `β` chosen from `(n, m, q)`.

**Formalization Note.** `max 1 ⌈ℓ/β⌉`: equal to `⌈ℓ/β⌉` whenever `ℓ ≥ 1` and `β > 0`. The two differ
only when `d = 0` (so `ℓ = 0`), where `n₀ ≤ 0` and Algorithm 3 falls back to `A` before any attempt;
the `max` keeps the uniform law of `j ∈ [ℓ′]` a probability measure in that case. -/
noncomputable def ell'A (β : ℕ → ℕ → ℕ → ℚ) (n m q : ℕ) : ℕ :=
  max 1 (ell'Of (ellA n m q) (β n m q))

/-- `n₀ = d − ℓ − ℓ′` (15), p.34, as an integer (it may be `≤ 0`). -/
noncomputable def n0A (β : ℕ → ℕ → ℕ → ℚ) (n m q : ℕ) : ℤ :=
  (corrD n m q : ℤ) - ellA n m q - ell'A β n m q

/-- The number of attempts `r = ⌈Cn⌉` (p.35). -/
noncomputable def rOf (C : ℚ) (n : ℕ) : ℕ := ⌈C * n⌉₊

/-- The closest of `init` and the candidates of `L`, scanning `L` in order and replacing the
current point only by a strictly closer one (Algorithm 3, lines 9 and 26). -/
def bestOf {n : ℕ} (y : Fin n → ℚ) (init : Fin n → ℤ) (L : List (Fin n → ℤ)) : Fin n → ℤ :=
  L.foldl (fun xh x => if sqDist x y < sqDist xh y then x else xh) init

/-- The instance `(n, m, q)` reaches the correction branch of Algorithm 3 (lines 1–16, p.33):
`m ≥ 1`, `q^{8m} > 2ⁿ`, not (`q = 2` and `m ≥ 3n/4`), `n₀ > 0`, not (`q = 2` and `n₀ ≤ m`), and for
`q ≥ 3` the feasibility checks pass. -/
def ReachesCorr (β : ℕ → ℕ → ℕ → ℚ) (feas : ℕ → ℕ → ℕ → Prop) (n m q : ℕ) : Prop :=
  1 ≤ m ∧ 2 ^ n < q ^ (8 * m) ∧ ¬ (q = 2 ∧ 3 * n ≤ 4 * m) ∧ 0 < n0A β n m q ∧
    ¬ (q = 2 ∧ n0A β n m q ≤ m) ∧ (3 ≤ q → feas n m q)

/-- The randomness `ω` of Algorithm 3: the `r = ⌈Cn⌉` attempts' choices, one block per attempt
(Theorem 4.7: "ω consists of the correction attempts' random bits"). -/
abbrev Alg3Coins (C : ℚ) (β : ℕ → ℕ → ℕ → ℚ) (n m q : ℕ) (Ω : Type) :=
  Fin (rOf C n) → AttSample (ellA n m q) (ell'A β n m q) Ω

/-- The law of `ω`: independent attempts, each with law `attMeasure` (fresh independent bits,
including the solver's, p.35). -/
noncomputable def alg3Measure (C : ℚ) (β : ℕ → ℕ → ℕ → ℚ) (n m q : ℕ) {Ω : Type}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Measure (Alg3Coins C β n m q Ω) :=
  Measure.pi fun _ => attMeasure (ellA n m q) (ell'A β n m q) μ

open Classical in
/-- A mathematical model of Algorithm 3 (γ-CVP, p.33), lines 1–29, run on `(H, y)` with the coins
`ω`. It is parametrized by the subprocedures and the parameter choice:

* `Aex` — the exact procedure `A(H, y)` of Lemma 4.1;
* `Eex` — the exact search `E_{γ^{−2}}(H, y, b)` of Definition 3.4 (`none` is `⊥`);
* `S`, `S₂` — the short solvers for `q ≥ 3` and `q = 2`, randomized functions of `(A, t)` and
  their randomness, indexed by the dimension `n` (the parameters may depend on it);
* `β c : ℕ → ℕ → ℕ → ℚ` — the correction parameters chosen from `(n, m, q)` (line 13);
* `feas` — the feasibility checks of line 16;
* `C` — the attempt constant, `r = ⌈Cn⌉`.

Line by line: 1 return `⌊y⌉` if `m = 0`; 2 return `A(H, y)` if `q^{8m} ≤ 2ⁿ`; 3 `x̂ = q⌊y/q⌉`;
4–11 for `q = 2`, `m ≥ 3n/4`, return `x̂` if `dim ker H > max{0, n−m} + ⌈n^{2/3}⌉`, else the
closest of `x̂` and `x + 2⌊(y − x)/2⌉` over `x ∈ ker H ⊆ F₂ⁿ`; 13–16 set `d, ℓ, ℓ′, n₀` and fall
back to `A`; 17–19 exact search with `b = (‖z − y‖² + cd)/γ²`; 20–29 `r` attempts, keeping the
closest candidate `z + w` strictly better than the current one.
Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Algorithm 3, p.33,
and §4.1, pp.33–35.

**Formalization Note.** The kernel `ker H` is scanned in a fixed enumeration of its elements
rather than as `Bα` over a basis `B`; this changes only which point is returned among equally
close candidates. `dim ker H > κ` is tested as `|ker H| > 2^κ`. Indices are 0-based. -/
noncomputable def alg3 {Ω : Type} (γ C : ℚ) (β c : ℕ → ℕ → ℕ → ℚ) (feas : ℕ → ℕ → ℕ → Prop)
    (Aex : ∀ {m n q : ℕ}, Matrix (Fin m) (Fin n) (ZMod q) → (Fin n → ℚ) → (Fin n → ℤ))
    (Eex : ∀ {m n q : ℕ}, Matrix (Fin m) (Fin n) (ZMod q) → (Fin n → ℚ) → ℚ →
      Option (Fin n → ℤ))
    (S S₂ : ℕ → ∀ {m n0 q : ℕ}, Matrix (Fin m) (Fin n0) (ZMod q) → (Fin m → ZMod q) → Ω →
      Option (Fin n0 → ℤ))
    {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ)
    (ω : Alg3Coins C β n m q Ω) : Fin n → ℤ :=
  let z := roundVec y
  if m = 0 then z else
  if q ^ (8 * m) ≤ 2 ^ n then Aex H y else
  let xhat : Fin n → ℤ := fun i => (q : ℤ) * roundQ (y i / q)
  if hq : q = 2 ∧ 3 * n ≤ 4 * m then
    haveI : NeZero q := ⟨by omega⟩
    let K := Finset.univ.filter (fun v : Fin n → ZMod q => H.mulVec v = 0)
    if 2 ^ ((n - m) + ⌈(n : ℝ) ^ ((2 : ℝ) / 3)⌉₊) < K.card then xhat else
      bestOf y xhat (K.toList.map fun v =>
        fun i => ((v i).val : ℤ) + 2 * roundQ ((y i - ((v i).val : ℚ)) / 2))
  else
  if n0A β n m q ≤ 0 ∨ (q = 2 ∧ n0A β n m q ≤ m) then Aex H y else
  if 3 ≤ q ∧ ¬ feas n m q then Aex H y else
  let b : ℚ := (sqDist z y + c n m q * corrD n m q) / γ ^ 2
  match Eex H y b with
  | some x => x
  | none =>
    let s : Fin m → ZMod q := -(H.mulVec (fun i => (z i : ZMod q)))
    let Sq : ∀ {n0 : ℕ}, Matrix (Fin m) (Fin n0) (ZMod q) → (Fin m → ZMod q) → Ω →
        Option (Fin n0 → ℤ) := fun A t w => if q = 2 then S₂ n A t w else S n A t w
    bestOf y xhat ((List.finRange (rOf C n)).filterMap fun i =>
      (corrAttempt Sq H (n0A β n m q).toNat (ellA n m q) (ell'A β n m q) s (ω i)).map
        (fun w => z + w))

end QaryCVP


