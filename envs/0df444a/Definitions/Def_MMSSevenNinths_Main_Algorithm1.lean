-- Prove2me | Definitions.Def_MMSSevenNinths_Main_Algorithm1
-- name    : MMSSevenNinths_Main_Algorithm1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:47:10.079079+00:00
-- url     : https://prove2.me/theorems/baf1c6e9-264e-46ec-a755-6357f256c220
-- title:
--   Algorithm 1 (ALG) with residual reductions, recipient rules and the §8.1 test log
-- statement:
--   Algorithm 1 on an ordered instance $V$ with an arbitrary real threshold vector $\alpha$ (§§2.1, 3, 8.1).
--
--   * Residual state $(A,U)$: active agents $A$ and unallocated real goods $U$; `resGood U r` is $u_r$, the $r$-th good of $U$ in the common order ($r\ge1$), and positions $0$ or beyond $|U|$ are zero-valued dummies (`none`). `resBundle U rs` is the set of real goods at the positions `rs`; dummies are dropped and are never members of $U$.
--   * `Satisfies V α i T` is $v_i(T)\ge\frac79\alpha_i$; `eligible V α A T` is the set of active agents for whom $T$ is satisfactory.
--   * A `Chooser` picks, in round $r$, an agent from a nonempty eligible set; `Chooser.Valid` says it always picks an eligible one. `leastIndexChooser` picks the smallest index (§8.1).
--   * `roundStep` is one round with $k=|A|$. **Pair branch** if $\{u_1,u_{k+1}\}$ is satisfactory to some active agent: test $R_0^\alpha=\{u_1\}$, $R_1^\alpha=\{u_k,u_{k+1}\}$, $R_2^\alpha=\{u_{2k-1},u_{2k},u_{2k+1}\}$ in this order and apply the first applicable one; otherwise scan $j=2,\dots,|U|$ in increasing order, testing $\{u_1,u_j\}$, and allocate $T=\{u_1,u_\ell\}$ for the largest satisfactory $\ell$. **Triple branch** if $\{u_1,u_{k+1},u_{2k+1}\}$ is satisfactory: test $R_2^\alpha$; otherwise scan $j=2,\dots,|U|$ testing $\{u_1,u_j,u_{\max(j+1,2k+1)}\}$ and allocate the largest satisfactory one. **Bag-filling branch**: test $R_3^\alpha=\{u_{3k-2},u_{3k-1},u_{3k},u_{3k+1}\}$; otherwise *tail filling*: test $T=\{u_1,u_{k+1},u_{2k+1}\}$, then $T\cup\{u_{3k+1}\}$, $T\cup\{u_{3k+1},u_{3k+2}\}$, … through $u_{|U|}$, stopping at the first satisfactory bag; if none is satisfactory the call returns FAILURE. A satisfactory bundle goes to the agent the chooser picks among the eligible ones. Every tested bundle is recorded, either before tail filling (`preTests`) or during it (`tailTests`).
--   * `callLoop`/`alg1`: start from $A=N$, $U=M$, all $B_i=\emptyset$; while $A\ne\emptyset$ run a round; an allocation removes the agent from $A$ and the bundle's goods from $U$ and sets $B_i=T$; a failure stops with $F=A$ and keeps the bundles assigned so far. `CallResult` records success, the bundles $B$, the failed set $F$ ($\emptyset$ on success), the full test log (each tested bundle with the active set at that moment), the log from the first tail-filling step on, and the state $(A,U)$ at the first tail-filling step. The fuel $n+1$ never runs out because each round serves an agent or fails.
--   * `alg1Det` uses `leastIndexChooser` (the §8.1 implementation). `unsatMax V α i L` is the largest $\frac97v_i(T)$ over logged tests $(A,T)$ with $i\in A$ and $v_i(T)<\frac79\alpha_i$ (`none` if there is none), and `failureBound V α i` is $b_i$, this maximum over the whole log of `alg1Det V α`. For a failed agent the final failed bag is such a test.
-- source:
--   Huang and Zhou (2026), A Strongly Polynomial-Time 7/9-Approximation Algorithm for Maximin Share Allocations, held STOC 2027 submission, SHA-256 428b298d196be354cea02bcd3b7278ffac7f04104c4bc290b02b6385aa0e405b, Definition 2.5 (printed pp. 4–5, PDF 7–8), Algorithm 1 (printed p. 6, PDF 9), §8.1 (printed p. 24, PDF 27)

import Mathlib
import Definitions.Def_MMSSevenNinths_Main_Instance

open scoped Classical

namespace MMSSevenNinths.Main

/-! Algorithm 1 `ALG(I, (α_i)_{i ∈ N})` of Huang and Zhou (2026), §2.1 and §3,
printed pp. 4–6 (PDF 7–9), instrumented as in §8.1 (printed p. 24, PDF 27).
Goods of the ordered instance are `Fin m` in the permanent common order. A residual state is
`(A, U)`: active agents `A : Finset (Fin n)` and unallocated real goods `U : Finset (Fin m)`. -/

/-- The residual good `u_r` at (one-based) position `r` of `U` in the common order, or `none`
for a zero-valued dummy (position `0` or beyond `|U|`). -/
def resGood {m : ℕ} (U : Finset (Fin m)) : ℕ → Option (Fin m)
  | 0 => none
  | r + 1 => (U.sort (· ≤ ·))[r]?

/-- The set of real goods at the given positions; dummies are dropped and a repeated position
contributes one good. -/
def resBundle {m : ℕ} (U : Finset (Fin m)) (rs : List ℕ) : Finset (Fin m) :=
  (rs.filterMap (resGood U)).toFinset

/-- Agent `i` finds bundle `T` satisfactory at thresholds `α`: `v_i(T) ≥ (7/9) α_i`. -/
def Satisfies {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (α : Fin n → ℝ) (i : Fin n)
    (T : Finset (Fin m)) : Prop :=
  (7 / 9 : ℝ) * α i ≤ V i T

/-- The active agents who find `T` satisfactory. -/
noncomputable def eligible {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (α : Fin n → ℝ)
    (A : Finset (Fin n)) (T : Finset (Fin m)) : Finset (Fin n) :=
  A.filter (fun i => Satisfies V α i T)

/-- A recipient rule: in round `r`, given the nonempty set of eligible agents, pick one. -/
def Chooser (n : ℕ) : Type :=
  ℕ → (E : Finset (Fin n)) → E.Nonempty → Fin n

/-- A recipient rule is valid when it always picks an eligible agent. Quantifying over all
valid rules covers every execution of the paper's "choose an arbitrary eligible agent". -/
def Chooser.Valid {n : ℕ} (c : Chooser n) : Prop :=
  ∀ r E h, c r E h ∈ E

/-- §8.1's fixed rule: the eligible agent with the smallest original index. -/
noncomputable def leastIndexChooser (n : ℕ) : Chooser n :=
  fun _ E h => E.min' h

/-- What a round does: give bundle `T` to agent `i`, or return `FAILURE`. -/
inductive RoundOutcome (n m : ℕ) where
  | assign (i : Fin n) (T : Finset (Fin m))
  | fail

/-- The result of one round: its outcome, the bundles tested before tail filling begins
(branch tests, reduction tests, candidate scans), the partial bags tested during tail filling,
and whether the round reached tail filling (bag-filling branch with `R₃^α` inapplicable). -/
structure RoundResult (n m : ℕ) where
  outcome : RoundOutcome n m
  preTests : List (Finset (Fin m))
  tailTests : List (Finset (Fin m))
  tail : Bool

/-- Give `T` to the agent chosen among the eligible ones (the `fail` fallback is unreachable
where it is used: every call site has checked that `T` is satisfactory to some active agent). -/
noncomputable def give {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (α : Fin n → ℝ)
    (c : Chooser n) (r : ℕ) (A : Finset (Fin n)) (T : Finset (Fin m)) : RoundOutcome n m :=
  if h : (eligible V α A T).Nonempty then .assign (c r _ h) T else .fail

/-- One round of Algorithm 1 at residual state `(A, U)` (`A ≠ ∅`, `k = |A|`), round index `r`.
* Pair branch, if `{u_1, u_{k+1}}` is satisfactory to some active agent: test `R₀^α = {u_1}`,
  `R₁^α = {u_k, u_{k+1}}`, `R₂^α = {u_{2k-1}, u_{2k}, u_{2k+1}}` in this order and apply the first
  applicable one; otherwise scan `j = 2, …, |U|` in increasing order, testing `{u_1, u_j}`, and
  allocate `T = {u_1, u_ℓ}` for the largest satisfactory `ℓ`.
* Triple branch, if `{u_1, u_{k+1}, u_{2k+1}}` is satisfactory: test `R₂^α`; otherwise scan
  `j = 2, …, |U|`, testing `{u_1, u_j, u_{max(j+1, 2k+1)}}`, and allocate the largest satisfactory.
* Bag-filling branch: test `R₃^α = {u_{3k-2}, u_{3k-1}, u_{3k}, u_{3k+1}}`; otherwise tail filling:
  test `T = {u_1, u_{k+1}, u_{2k+1}}`, then `T ∪ {u_{3k+1}}`, `T ∪ {u_{3k+1}, u_{3k+2}}`, … up to
  `u_{|U|}`, stopping at the first satisfactory bag; if none is satisfactory, `FAILURE`.
Every listed test is recorded (for all active agents, §8.1). -/
noncomputable def roundStep {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (α : Fin n → ℝ)
    (c : Chooser n) (r : ℕ) (A : Finset (Fin n)) (U : Finset (Fin m)) : RoundResult n m :=
  let k := A.card
  let ok : Finset (Fin m) → Prop := fun T => (eligible V α A T).Nonempty
  let P := resBundle U [1, k + 1]
  let Tr := resBundle U [1, k + 1, 2 * k + 1]
  let R0 := resBundle U [1]
  let R1 := resBundle U [k, k + 1]
  let R2 := resBundle U [2 * k - 1, 2 * k, 2 * k + 1]
  let R3 := resBundle U [3 * k - 2, 3 * k - 1, 3 * k, 3 * k + 1]
  let js := List.range' 2 (U.card - 1)
  if ok P then
    if ok R0 then ⟨give V α c r A R0, [P, R0], [], false⟩
    else if ok R1 then ⟨give V α c r A R1, [P, R0, R1], [], false⟩
    else if ok R2 then ⟨give V α c r A R2, [P, R0, R1, R2], [], false⟩
    else
      let cands := js.map (fun j => resBundle U [1, j])
      let T := ((cands.filter (fun T => decide (ok T))).getLast?).getD P
      ⟨give V α c r A T, [P, R0, R1, R2] ++ cands, [], false⟩
  else if ok Tr then
    if ok R2 then ⟨give V α c r A R2, [P, Tr, R2], [], false⟩
    else
      let cands := js.map (fun j => resBundle U [1, j, max (j + 1) (2 * k + 1)])
      let T := ((cands.filter (fun T => decide (ok T))).getLast?).getD Tr
      ⟨give V α c r A T, [P, Tr, R2] ++ cands, [], false⟩
  else if ok R3 then ⟨give V α c r A R3, [P, Tr, R3], [], false⟩
  else
    let bags := (List.range (U.card - 3 * k + 1)).map
      (fun t => resBundle U ([1, k + 1, 2 * k + 1] ++ (List.range t).map (fun s => 3 * k + 1 + s)))
    match bags.find? (fun T => decide (ok T)) with
    | some T => ⟨give V α c r A T, [P, Tr, R3],
        bags.takeWhile (fun T => !decide (ok T)) ++ [T], true⟩
    | none => ⟨.fail, [P, Tr, R3], bags, true⟩

/-- The record of one call of Algorithm 1.
* `success`: `SUCCESS` (all agents served) or `FAILURE`;
* `bundles`: the bundles `B_i` assigned so far (`∅` for an agent never served);
* `failed`: the failed set `F` (the active agents at failure; `∅` on success);
* `log`: every tested bundle, in order, paired with the active agents at the time of the test
  (each active agent compares it with her threshold);
* `tailLog`: the part of `log` from the first tail-filling step of the call onward;
* `firstTail`: the residual state `(A, U)` when the call first reaches tail filling. -/
structure CallResult (n m : ℕ) where
  success : Bool
  bundles : Fin n → Finset (Fin m)
  failed : Finset (Fin n)
  log : List (Finset (Fin n) × Finset (Fin m))
  tailLog : List (Finset (Fin n) × Finset (Fin m))
  firstTail : Option (Finset (Fin n) × Finset (Fin m))

/-- The main loop of Algorithm 1, with a fuel counter (each round either serves one agent or
fails, so fuel `n + 1` never runs out; the fuel-exhausted clause is unreachable from `alg1`). -/
noncomputable def callLoop {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (α : Fin n → ℝ)
    (c : Chooser n) :
    ℕ → ℕ → Finset (Fin n) → Finset (Fin m) → (Fin n → Finset (Fin m)) →
      List (Finset (Fin n) × Finset (Fin m)) → List (Finset (Fin n) × Finset (Fin m)) →
      Option (Finset (Fin n) × Finset (Fin m)) → CallResult n m
  | 0, _, A, _, B, log, tl, ft => ⟨decide (A = ∅), B, A, log, tl, ft⟩
  | fuel + 1, r, A, U, B, log, tl, ft =>
    if A = ∅ then ⟨true, B, ∅, log, tl, ft⟩
    else
      let res := roundStep V α c r A U
      let pre := res.preTests.map (fun T => (A, T))
      let tails := res.tailTests.map (fun T => (A, T))
      let ft' := if ft.isNone && res.tail then some (A, U) else ft
      let tl' := tl ++ (if ft.isSome then pre ++ tails else tails)
      let log' := log ++ pre ++ tails
      match res.outcome with
      | .fail => ⟨false, B, A, log', tl', ft'⟩
      | .assign i T => callLoop V α c fuel (r + 1) (A.erase i) (U \ T)
          (Function.update B i T) log' tl' ft'

/-- Algorithm 1 with recipient rule `c`: start from `A = N`, `U = M`, all `B_i = ∅`. -/
noncomputable def alg1 {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (α : Fin n → ℝ)
    (c : Chooser n) : CallResult n m :=
  callLoop V α c (n + 1) 0 Finset.univ Finset.univ (fun _ => ∅) [] [] none

/-- The deterministic implementation of §8.1 (smallest-index recipient). -/
noncomputable def alg1Det {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (α : Fin n → ℝ) :
    CallResult n m :=
  alg1 V α (leastIndexChooser n)

/-- The largest value `9 v_i(T)/7` over the tests `(A, T)` of a log with `i ∈ A` and `T`
unsatisfactory to `i` (`v_i(T) < 7α_i/9`); `none` if there is no such test. -/
noncomputable def unsatMax {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (α : Fin n → ℝ)
    (i : Fin n) (L : List (Finset (Fin n) × Finset (Fin m))) : Option ℝ :=
  ((L.filter (fun p => decide (i ∈ p.1 ∧ ¬ Satisfies V α i p.2))).map
    (fun p => (9 / 7 : ℝ) * V i p.2)).max?

/-- `b_i` (§8.1, printed p. 24; Algorithm 14): the largest `9 v_i(T)/7` over the bundles
`T` tested in the deterministic call at thresholds `α` with `v_i(T) < 7α_i/9`. For `i ∈ F` the
final failed bag is such a test; the fallback `α i` only applies to agents with no such test. -/
noncomputable def failureBound {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (α : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  (unsatMax V α i (alg1Det V α).log).getD (α i)

end MMSSevenNinths.Main


