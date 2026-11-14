-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Alg_Defs
-- name    : BCFGJPSSV26_Greedy_Alg_Defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:54:59.509253+00:00
-- url     : https://prove2.me/theorems/66795a6e-146c-4b52-94a7-8395245e39ef
-- title:
--   BCFGJPSSV26.Greedy.Alg.Defs — The algorithm: the core
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Alg.Defs` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The algorithm of [BCFGJPSSV26a, Section 5 and Appendix D] on a **core input**: `n` clients, `m`
--   facilities, `k`, and the `n × m` table of client–facility distances, which lie in `[1, M]`.
--   Everything is computed exactly, in rational arithmetic, on lists and natural numbers;
--   `Greedy/Alg/Bridge.lean` relates it to the analysis.
--
--   * **Parameters** (`BCFGJPSSV26.Greedy.ipar`): from constants `δ`, `ε` (the paper's `ε`, here
--     `εg`) and `ε'` (the scaling, `εp`) and from `n, m, k`: `M = 8 n² / ε' + 1`, `η = δ² / (100 n²)`,
--     `f̂ ∈ [δ, 4 n M]`, `R = ⌈1/ε²⌉ ⌈log₂ ⌈5 n M⌉⌉ + 1` phases (sequences `0, …, 2R - 1`), the cap
--     `K = 2 θ R`, the grids `f̂ b = δ + (4 n M - δ) b / 2^Pf` (`b ≤ 2^Pf`) and `u g = K g / 2^Pu`
--     (`g ≤ 2^Pu`), with steps at most `η`, and the budget `L = m + 4` of the loops.
--   * **Atoms** (`BCFGJPSSV26.Greedy.AAtom`): `(i, 0)` is the regular facility `i`, `(i, g + 1)` a free
--     copy of `i` at offset `u g`.
--   * **Tests** (`BCFGJPSSV26.Greedy.Ctx.test1`, `BCFGJPSSV26.Greedy.Ctx.test2`): the exact tests of
--     `Greedy/Openable.lean`, on lists.
--   * **CompleteSequence and CompleteSolution** (`BCFGJPSSV26.Greedy.Ctx.completeSeq`,
--     `BCFGJPSSV26.Greedy.Ctx.complete`): add the first facility that passes the test, `L` times; then
--     complete a partial solution to `2R` sequences. Deterministic: the merge needs that the
--     completion depends only on the profile of the prefix.
--   * **Bisection** on `f̂` (`BCFGJPSSV26.Greedy.Ctx.bisect`) and the **merge** of two solutions
--     (`BCFGJPSSV26.Greedy.Ctx.merge`), after [CGLSS25, Section 3.5] and [BCFGJPSSV26a, Appendix D.1]:
--     one phase per sequence (`BCFGJPSSV26.Greedy.Ctx.phase`): make the parameters agree (step A), walk
--     the sequence of one solution towards that of the other (step B,
--     `BCFGJPSSV26.Greedy.Ctx.walkB`), remove extra facilities (step C,
--     `BCFGJPSSV26.Greedy.Ctx.stepC`), and search the offset of a new free facility
--     (`BCFGJPSSV26.Greedy.Ctx.binSearch`). There are always `2R` sequences: the phases go on after
--     all clients are inactive.
--   * **Output** (`BCFGJPSSV26.Greedy.core`): the facilities of the merged solution, free copies
--     replaced by their originals.
--
--   **Contents.** The module is published as a whole: 64 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Defs`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/Defs.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Space
public import Definitions.Def_BCFGJPSSV26_Combine_Algorithm
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Rat.Floor

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Alg.Defs` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The algorithm: the core

The algorithm of [BCFGJPSSV26a, Section 5 and Appendix D] on a **core input**: `n` clients, `m`
facilities, `k`, and the `n × m` table of client–facility distances, which lie in `[1, M]`.
Everything is computed exactly, in rational arithmetic, on lists and natural numbers;
`Greedy/Alg/Bridge.lean` relates it to the analysis.

* **Parameters** (`BCFGJPSSV26.Greedy.ipar`): from constants `δ`, `ε` (the paper's `ε`, here
  `εg`) and `ε'` (the scaling, `εp`) and from `n, m, k`: `M = 8 n² / ε' + 1`, `η = δ² / (100 n²)`,
  `f̂ ∈ [δ, 4 n M]`, `R = ⌈1/ε²⌉ ⌈log₂ ⌈5 n M⌉⌉ + 1` phases (sequences `0, …, 2R - 1`), the cap
  `K = 2 θ R`, the grids `f̂ b = δ + (4 n M - δ) b / 2^Pf` (`b ≤ 2^Pf`) and `u g = K g / 2^Pu`
  (`g ≤ 2^Pu`), with steps at most `η`, and the budget `L = m + 4` of the loops.
* **Atoms** (`BCFGJPSSV26.Greedy.AAtom`): `(i, 0)` is the regular facility `i`, `(i, g + 1)` a free
  copy of `i` at offset `u g`.
* **Tests** (`BCFGJPSSV26.Greedy.Ctx.test1`, `BCFGJPSSV26.Greedy.Ctx.test2`): the exact tests of
  `Greedy/Openable.lean`, on lists.
* **CompleteSequence and CompleteSolution** (`BCFGJPSSV26.Greedy.Ctx.completeSeq`,
  `BCFGJPSSV26.Greedy.Ctx.complete`): add the first facility that passes the test, `L` times; then
  complete a partial solution to `2R` sequences. Deterministic: the merge needs that the
  completion depends only on the profile of the prefix.
* **Bisection** on `f̂` (`BCFGJPSSV26.Greedy.Ctx.bisect`) and the **merge** of two solutions
  (`BCFGJPSSV26.Greedy.Ctx.merge`), after [CGLSS25, Section 3.5] and [BCFGJPSSV26a, Appendix D.1]:
  one phase per sequence (`BCFGJPSSV26.Greedy.Ctx.phase`): make the parameters agree (step A), walk
  the sequence of one solution towards that of the other (step B,
  `BCFGJPSSV26.Greedy.Ctx.walkB`), remove extra facilities (step C,
  `BCFGJPSSV26.Greedy.Ctx.stepC`), and search the offset of a new free facility
  (`BCFGJPSSV26.Greedy.Ctx.binSearch`). There are always `2R` sequences: the phases go on after
  all clients are inactive.
* **Output** (`BCFGJPSSV26.Greedy.core`): the facilities of the merged solution, free copies
  replaced by their originals.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

/-! ### Inputs and parameters -/

/-- A **core input**: `n`, `m`, `k` and the `n × m` table of client–facility distances. -/
abbrev CoreIn : Type := ℕ × ℕ × ℕ × List (List ℚ)

/-- The **constants** fixed by `ε`: `δ`, the paper's `ε` (`εg`) and the scaling `ε'` (`εp`). -/
structure Consts where
  /-- The paper's `δ`. -/
  δ : ℚ
  /-- The paper's `ε`. -/
  εg : ℚ
  /-- The scaling `ε'` of the distance reduction. -/
  εp : ℚ

/-- The conditions on the constants. -/
structure Consts.Good (c : Consts) : Prop where
  δ_pos : 0 < c.δ
  δ_le : c.δ ≤ 1 / 100
  εg_eq : c.εg = c.δ / 10
  εp_pos : 0 < c.εp
  εp_le : c.εp ≤ 1

/-- The **parameters** of the core. -/
structure IPar where
  n : ℕ
  m : ℕ
  k : ℕ
  δ : ℚ
  ε : ℚ
  M : ℚ
  η : ℚ
  K : ℚ
  fmin : ℚ
  fmax : ℚ
  R : ℕ
  Pf : ℕ
  Pu : ℕ
  L : ℕ

/-- The largest distance `M = 8 n² / ε' + 1` after the reduction. -/
def Mof (c : Consts) (n : ℕ) : ℚ := 8 * (n : ℚ) ^ 2 / c.εp + 1

/-- The number of phases: `R = ⌈1/ε²⌉ ⌈log₂ ⌈5 n M⌉⌉ + 1`. -/
def Rof (c : Consts) (n : ℕ) : ℕ := ⌈1 / c.εg ^ 2⌉₊ * Nat.clog 2 ⌈5 * (n : ℚ) * Mof c n⌉₊ + 1

/-- The parameters of the core for the constants `c` and the input `x`. -/
def ipar (c : Consts) (x : CoreIn) : IPar :=
  let n := x.1
  let M := Mof c n
  let η : ℚ := c.δ ^ 2 / (100 * (n : ℚ) ^ 2)
  let fmax : ℚ := 4 * n * M
  let R := Rof c n
  let K : ℚ := 2 * (1 + c.εg ^ 2) ^ R
  { n := n, m := x.2.1, k := x.2.2.1, δ := c.δ, ε := c.εg, M := M, η := η, K := K,
    fmin := c.δ, fmax := fmax, R := R, Pf := Nat.clog 2 ⌈fmax / η⌉₊,
    Pu := Nat.clog 2 ⌈K / η⌉₊, L := x.2.1 + 4 }

/-! ### Atoms and the context -/

/-- An **atom** of the algorithm: `(i, 0)` is the regular facility `i`, `(i, g + 1)` a free copy of
`i` at offset `u g`. -/
abbrev AAtom : Type := ℕ × ℕ

/-- The number of regular atoms of a solution. -/
def nRegA (H : List (List AAtom)) : ℕ := (H.flatten.filter fun a ↦ a.2 == 0).length

/-- The number of regular atoms of a sequence. -/
def nRegSeq (S : List AAtom) : ℕ := (S.filter fun a ↦ a.2 == 0).length

/-- The number of free atoms of a sequence. -/
def nFreeSeqA (S : List AAtom) : ℕ := (S.filter fun a ↦ a.2 != 0).length

/-- The **context** of the core: its parameters and its table. -/
structure Ctx where
  /-- The parameters. -/
  ip : IPar
  /-- The `n × m` table of distances. -/
  tab : List (List ℚ)

/-- The context for the constants `c` and the input `x`. -/
def ctx (c : Consts) (x : CoreIn) : Ctx := ⟨ipar c x, x.2.2.2⟩

/-- Whether `a` sandwiches `k` with `b`: `a < k < b` or `b < k < a`. -/
def sandwich (a b k : ℕ) : Bool :=
  (decide (a < k) && decide (k < b)) || (decide (b < k) && decide (k < a))

namespace Ctx

variable (C : Ctx)

/-- The distance from client `j` to facility `i`. -/
def dist (j i : ℕ) : ℚ := (C.tab.getD j []).getD i 0

/-- The offset `u g = K g / 2^Pu`. -/
def off (g : ℕ) : ℚ := C.ip.K * g / 2 ^ C.ip.Pu

/-- The offset of an atom: `0` if regular. -/
def aoff (a : AAtom) : ℚ := if a.2 = 0 then 0 else C.off (a.2 - 1)

/-- The distance from client `j` to an atom. -/
def adist (j : ℕ) (a : AAtom) : ℚ := C.dist j a.1 + C.aoff a

/-- The **profile** of a list of atoms: `min (K, min_a d(j, a))` for each client `j < n`. -/
def prof (S : List AAtom) : List ℚ :=
  (List.range C.ip.n).map fun j ↦ S.foldr (fun a acc ↦ min (C.adist j a) acc) C.ip.K

/-- The time of phase `r`. -/
def θ (r : ℕ) : ℚ := (1 + C.ip.ε ^ 2) ^ r

/-- The time of sequence `p`. -/
def θseq (p : ℕ) : ℚ := C.θ (p / 2)

/-- The time after a raise. -/
def θplus (θ : ℚ) : ℚ := (1 + C.ip.ε ^ 2) * θ

/-- A sum over the clients. -/
def sumC (g : ℕ → ℚ) : ℚ := ((List.range C.ip.n).map g).sum

/-! ### The tests -/

/-- The value of client `j`: `min (θ, (1 - δ) D j)`. -/
def mval (θ : ℚ) (D : List ℚ) (j : ℕ) : ℚ := min θ ((1 - C.ip.δ) * D.getD j 0)

/-- The left side of type 1. -/
def lhs1 (θ : ℚ) (D : List ℚ) (i : ℕ) : ℚ :=
  C.sumC fun j ↦ bid (C.mval θ D j) ((1 - C.ip.δ) * C.dist j i)

/-- The bid of an active client at distance `e` (see `BCFGJPSSV26.Greedy.gT`). -/
def gT (θ e T : ℚ) : ℚ :=
  if e ≤ C.ip.ε * θ then max θ (min T ((1 + C.ip.ε) * θ - e)) else θ

/-- The bid of client `j` for facility `i` (see `BCFGJPSSV26.Greedy.mT`). -/
def mT (θ : ℚ) (D : List ℚ) (i : ℕ) (T : ℚ) (j : ℕ) : ℚ :=
  min ((1 - C.ip.δ) * D.getD j 0) (C.gT θ (C.dist j i) T)

/-- The left side of (iii). -/
def lhs3 (θ : ℚ) (D : List ℚ) (i : ℕ) (T : ℚ) : ℚ :=
  C.sumC fun j ↦ bid (C.mT θ D i T j) ((1 - C.ip.δ / 2) * C.dist j i)

/-- The left side of (iv). -/
def lhs4 (θ : ℚ) (D : List ℚ) (i : ℕ) (T : ℚ) (i₀ : ℕ) : ℚ :=
  C.sumC fun j ↦ bid (C.mT θ D i T j) (C.dist j i₀)

/-- The active clients near `i`. -/
def nearL (θ : ℚ) (D : List ℚ) (i : ℕ) : List ℕ :=
  (List.range C.ip.n).filter fun j ↦
    decide (C.dist j i ≤ C.ip.ε * θ) && decide (θ < (1 - C.ip.δ) * D.getD j 0)

/-- The largest bid of a near active client. -/
def cnear (θ : ℚ) (D : List ℚ) (i : ℕ) (j : ℕ) : ℚ :=
  min ((1 - C.ip.δ) * D.getD j 0) ((1 + C.ip.ε) * θ - C.dist j i)

/-- What the near active clients must pay (see `BCFGJPSSV26.Greedy.need`). -/
def need (f θ : ℚ) (D : List ℚ) (i : ℕ) : ℚ :=
  f - (((List.range C.ip.n).filter fun j ↦ !(C.nearL θ D i).contains j).map fun j ↦
      bid (C.mval θ D j) ((1 - C.ip.δ / 2) * C.dist j i)).sum +
    ((C.nearL θ D i).map fun j ↦ γ * ((1 - C.ip.δ / 2) * C.dist j i)).sum

/-- The candidate value of `T` for `j₀` (see `BCFGJPSSV26.Greedy.candT`). -/
def candT (f θ : ℚ) (D : List ℚ) (i : ℕ) (j₀ : ℕ) : ℚ :=
  (C.need f θ D i - (((C.nearL θ D i).filter fun j ↦
      decide (C.cnear θ D i j < C.cnear θ D i j₀)).map (C.cnear θ D i)).sum) /
    ((C.nearL θ D i).filter fun j ↦ decide (C.cnear θ D i j₀ ≤ C.cnear θ D i j)).length

/-- The least `T ≥ θ` at which (iii) holds (see `BCFGJPSSV26.Greedy.tstar`). -/
def tstar (f θ : ℚ) (D : List ℚ) (i : ℕ) : ℚ :=
  ((C.nearL θ D i).map (C.candT f θ D i)).foldl max θ

/-- The test of type 1. -/
def test1 (f θ : ℚ) (D : List ℚ) (i : ℕ) : Bool := decide (f ≤ C.lhs1 θ D i)

/-- The test of type 2. -/
def test2 (f θ : ℚ) (D : List ℚ) (i : ℕ) : Bool :=
  let T := C.tstar f θ D i
  decide (T ≤ C.θplus θ) && decide (f ≤ C.lhs3 θ D i T) &&
    (List.range C.ip.m).all fun i₀ ↦ decide (C.lhs4 θ D i T i₀ ≤ f)

/-- The test of type 1 (`true`) or 2 (`false`). -/
def testT (b : Bool) (f θ : ℚ) (D : List ℚ) (i : ℕ) : Bool :=
  cond b (C.test1 f θ D i) (C.test2 f θ D i)

/-! ### Completion -/

/-- The first facility that passes the test after the atoms `S`. -/
def firstOpen (b : Bool) (f θ : ℚ) (S : List AAtom) : Option ℕ :=
  (List.range C.ip.m).find? fun i ↦ C.testT b f θ (C.prof S) i

/-- One step of CompleteSequence: add the first facility that passes the test, if any. -/
def seqStep (b : Bool) (f θ : ℚ) (pre cur : List AAtom) : List AAtom :=
  match C.firstOpen b f θ (pre ++ cur) with
  | some i => cur ++ [(i, 0)]
  | none => cur

/-- **CompleteSequence**: `L` steps of `seqStep` from `cur`, after the atoms `pre`. -/
def completeSeq (b : Bool) (f θ : ℚ) (pre cur : List AAtom) : List AAtom :=
  (C.seqStep b f θ pre)^[C.ip.L] cur

/-- **CompleteSolution**: complete a partial solution to `2R` sequences. -/
def complete (f : ℚ) (H : List (List AAtom)) : List (List AAtom) :=
  (List.range (2 * C.ip.R)).foldl (fun H p ↦
    if H.length = p then H ++ [C.completeSeq (typ1 p) f (C.θseq p) H.flatten []] else H) H

/-- The opening cost of grid point `b`: `f̂ b = fmin + (fmax - fmin) b / 2^Pf`. -/
def fhat (b : ℕ) : ℚ := C.ip.fmin + (C.ip.fmax - C.ip.fmin) * b / 2 ^ C.ip.Pf

/-- The solution of the greedy algorithm at grid point `b`. -/
def sol (b : ℕ) : List (List AAtom) := C.complete (C.fhat b) []

/-- The number of regular atoms of the completion of `pre ++ [W]`. -/
def cnt (f : ℚ) (pre : List (List AAtom)) (W : List AAtom) : ℕ := nRegA (C.complete f (pre ++ [W]))

/-! ### Bisection -/

/-- A pair of solutions: `H` (the dominant one) at grid point `b`, `H'` at `b'`. -/
structure Pair where
  H : List (List AAtom)
  H' : List (List AAtom)
  b : ℕ
  b' : ℕ

/-- The result of a step of the merge: a solution with exactly `k` regular atoms (or the first
endpoint), or a pair to continue with. -/
inductive Res where
  | done (H : List (List AAtom)) (b : ℕ)
  | cont (pr : Pair)

/-- One step of a binary search for a count `c` that equals `k` or flips across it: on
`(lo, hi, none)` with `hi - lo ≥ 2`, test the middle. -/
def searchStep (k : ℕ) (c : ℕ → ℕ) : ℕ × ℕ × Option ℕ → ℕ × ℕ × Option ℕ
  | (lo, hi, none) =>
    if hi - lo ≤ 1 then (lo, hi, none)
    else
      let mid := (lo + hi) / 2
      if c mid = k then (lo, hi, some mid)
      else if decide (c mid < k) = decide (c lo < k) then (mid, hi, none) else (lo, mid, none)
  | st => st

/-- **Bisection** on `f̂`: return `sol 0` if it has at most `k` regular atoms, a solution with
exactly `k` if one is found, and otherwise two solutions at adjacent grid points, the one at the
larger `f̂` (fewer than `k` regular atoms) first. -/
def bisect : Res :=
  if nRegA (C.sol 0) ≤ C.ip.k then .done (C.sol 0) 0
  else if nRegA (C.sol (2 ^ C.ip.Pf)) = C.ip.k then .done (C.sol (2 ^ C.ip.Pf)) (2 ^ C.ip.Pf)
  else
    match (searchStep C.ip.k (fun b ↦ nRegA (C.sol b)))^[C.ip.Pf] (0, 2 ^ C.ip.Pf, none) with
    | (_, _, some b) => .done (C.sol b) b
    | (lo, hi, none) => .cont ⟨C.sol hi, C.sol lo, hi, lo⟩

/-! ### The merge -/

/-- **BinSearch**: search the offset of a new free copy of `z` appended to `base`, between the
counts at offset `0` and at offset `K` (where it is invisible). -/
def binSearch (f : ℚ) (b : ℕ) (pre : List (List AAtom)) (base : List AAtom) (z : ℕ) : Res :=
  let W : ℕ → List AAtom := fun g ↦ base ++ [(z, g + 1)]
  let cg : ℕ → ℕ := fun g ↦ C.cnt f pre (W g)
  if cg 0 = C.ip.k then .done (C.complete f (pre ++ [W 0])) b
  else if cg (2 ^ C.ip.Pu) = C.ip.k then .done (C.complete f (pre ++ [W (2 ^ C.ip.Pu)])) b
  else
    match (searchStep C.ip.k cg)^[C.ip.Pu] (0, 2 ^ C.ip.Pu, none) with
    | (_, _, some g) => .done (C.complete f (pre ++ [W g])) b
    | (lo, hi, none) => .cont ⟨C.complete f (pre ++ [W lo]), C.complete f (pre ++ [W hi]), b, b⟩

/-- The first index `t` at which consecutive counts sandwich `k`. -/
def firstFlip (k : ℕ) (cs : List ℕ) : Option ℕ :=
  (List.range (cs.length - 1)).find? fun t ↦ sandwich (cs.getD t 0) (cs.getD (t + 1) 0) k

/-- **Step C** (remove extra facilities): between `before = X ++ h? ++ Y` and
`after = X ++ Y ++ Z`, the sequences `X ++ Y ++ Z.drop r ++ F` with `F` a free copy of `h` at
offset `0`. -/
def stepC (f : ℚ) (b : ℕ) (pre : List (List AAtom)) (X : List AAtom) (h : Option AAtom)
    (Y Z : List AAtom) (dflt : Res) : Res :=
  let F : List AAtom := match h with
    | some h => [(h.1, 1)]
    | none => []
  let after := X ++ Y ++ Z
  let Pr : ℕ → List AAtom := fun r ↦ X ++ Y ++ Z.drop r ++ F
  let pts := after :: (List.range (Z.length + 1)).map Pr
  match pts.find? (fun W ↦ C.cnt f pre W = C.ip.k) with
  | some W => .done (C.complete f (pre ++ [W])) b
  | none =>
    match firstFlip C.ip.k (pts.map (C.cnt f pre)) with
    | some 0 => C.binSearch f b pre after (match h with
      | some h => h.1
      | none => 0)
    | some (t + 1) =>
      let z := (Z.getD t (0, 0)).1
      let W₀ := Pr (t + 1) ++ [(z, 1)]
      if C.cnt f pre W₀ = C.ip.k then .done (C.complete f (pre ++ [W₀])) b
      else C.binSearch f b pre (Pr (t + 1)) z
    | none => dflt

/-- The kind of a point of the walk of step B. -/
inductive WKind where
  | init
  | appendFree (z : ℕ)
  | removeComplete (X : List AAtom) (h : AAtom) (Y Z : List AAtom)
  | toRegular

/-- The length of the common prefix of two lists. -/
def commonPrefixLen : List AAtom → List AAtom → ℕ
  | a :: l, b :: l' => if a = b then commonPrefixLen l l' + 1 else 0
  | _, _ => 0

/-- One deletion of the walk: remove the atom at position `q`, complete the sequence, record it. -/
def delStep (p : ℕ) (f : ℚ) (pre : List (List AAtom)) (q : ℕ)
    (st : List AAtom × List (List AAtom × WKind)) : List AAtom × List (List AAtom × WKind) :=
  let X := st.1.take q
  let h := st.1.getD q (0, 0)
  let Y := st.1.drop (q + 1)
  let Z := (C.completeSeq (typ1 p) f (C.θseq p) pre.flatten (X ++ Y)).drop (X.length + Y.length)
  let cur := (X ++ Y ++ Z).take C.ip.L
  (cur, st.2 ++ [(cur, .removeComplete X h Y Z)])

/-- One round of the walk of step B towards `Hp`: append a free copy (offset `0`) of the first
facility of `Hp` not in the common prefix, delete the atoms after the common prefix one by one
(completing after each), and make the free copy regular. -/
def roundB (p : ℕ) (f : ℚ) (pre : List (List AAtom)) (Hp : List AAtom)
    (st : List AAtom × List (List AAtom × WKind)) : List AAtom × List (List AAtom × WKind) :=
  if Hp.isPrefixOf st.1 then st
  else
    let q := commonPrefixLen Hp st.1
    let z := (Hp.getD q (0, 0)).1
    let cur₁ := st.1 ++ [(z, 1)]
    let st₂ := (C.delStep p f pre q)^[st.1.length - q] (cur₁, st.2 ++ [(cur₁, .appendFree z)])
    let cur₃ := st₂.1.set q (z, 0)
    (cur₃, st₂.2 ++ [(cur₃, .toRegular)])

/-- **The walk of step B** from `H'p` to a sequence with prefix `Hp`: the list of its points. -/
def walkB (p : ℕ) (f : ℚ) (pre : List (List AAtom)) (Hp H'p : List AAtom) :
    List (List AAtom × WKind) :=
  ((C.roundB p f pre Hp)^[C.ip.L] (H'p, [(H'p, .init)])).2

/-- **Step B** and the dispatch to step C or BinSearch at the first flip of the walk. -/
def walkPhase (p : ℕ) (f : ℚ) (b : ℕ) (pre : List (List AAtom)) (Hp H'p : List AAtom)
    (dflt : Res) : Res :=
  let pts := C.walkB p f pre Hp H'p
  match pts.find? (fun w ↦ C.cnt f pre w.1 = C.ip.k) with
  | some w => .done (C.complete f (pre ++ [w.1])) b
  | none =>
    match firstFlip C.ip.k (pts.map fun w ↦ C.cnt f pre w.1) with
    | some t =>
      match (pts.getD (t + 1) ([], .init)).2 with
      | .appendFree z => C.binSearch f b pre (pts.getD t ([], .init)).1 z
      | .removeComplete X h Y Z => C.stepC f b pre X (some h) Y Z dflt
      | _ => dflt
    | none =>
      let cur := (pts.getLast?.getD ([], .init)).1
      C.stepC f b pre Hp none [] (cur.drop Hp.length) dflt

/-- **Phase `p` of the merge**: step A (complete the prefix of `H` with sequence `p` of `H'` at
the parameter of `H`), then steps B and C if needed. -/
def phase (p : ℕ) (pr : Pair) : Res :=
  let f := C.fhat pr.b
  let pre := pr.H.take p
  let H'' := C.complete f (pre ++ [pr.H'.getD p []])
  if nRegA H'' = C.ip.k then .done H'' pr.b
  else if sandwich (nRegA H'') (nRegA pr.H') C.ip.k then .cont ⟨H'', pr.H', pr.b, pr.b'⟩
  else C.walkPhase p f pr.b pre (pr.H.getD p []) (H''.getD p []) (.done pr.H pr.b)

/-- One step of the merge. -/
def mergeStep (r : Res) (p : ℕ) : Res :=
  match r with
  | .done H b => .done H b
  | .cont pr => C.phase p pr

/-- The result of the merge after the phases `0, …, q - 1`. -/
def mergeUpTo (q : ℕ) : Res := (List.range q).foldl C.mergeStep C.bisect

/-- **The merge**: the solution (with its grid point) after the phases `0, …, 2R - 1`. -/
def merge : List (List AAtom) × ℕ :=
  match C.mergeUpTo (2 * C.ip.R) with
  | .done H b => (H, b)
  | .cont pr => (pr.H, pr.b)

end Ctx

/-- The facilities of a solution, free copies replaced by their originals, without repetitions. -/
def toCenters (H : List (List AAtom)) : List ℕ := (H.flatten.map Prod.fst).eraseDups

/-- **The core**: the facilities of the merged solution. -/
def core (c : Consts) (x : CoreIn) : List ℕ := toCenters (ctx c x).merge.1

/-- The exact cost of a list of facilities on a core input. -/
def coreCost (x : CoreIn) (S : List ℕ) : ℚ :=
  ((List.range x.1).map fun j ↦ Combine.minQ (S.map fun i ↦ (x.2.2.2.getD j []).getD i 0)).sum

end BCFGJPSSV26.Greedy


