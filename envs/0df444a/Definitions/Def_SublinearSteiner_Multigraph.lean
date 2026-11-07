-- Prove2me | Definitions.Def_SublinearSteiner_Multigraph
-- name    : SublinearSteiner_Multigraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:39:23.758864+00:00
-- url     : https://prove2.me/theorems/9024ac40-c9b0-4fd6-a508-cb9e32f7eae8
-- title:
--   Multigraphs, the random-greedy matching and the local oracles $\mathrm{EO}$, $\mathrm{VO}$
-- statement:
--   A finite loopless multigraph $H$ on a vertex set $U$ with $m=|U|$ and $p$ labeled edge copies. A uniformly random order of the copies defines the **random-greedy maximal matching**, which scans the copies by increasing rank and adds a copy whenever both endpoints are free.
--
--   The **local oracles**: for a copy $e$ with endpoint $u$, $\mathrm{EO}(e,u)$ decides whether $u$ is still unmatched just before the rank of $e$. It scans the other copies $f$ at $u$ of smaller rank in increasing order, calls $\mathrm{EO}(f,u_f)$ for their other endpoints $u_f$, and answers "no" at the first positive call. $\mathrm{VO}(v)$ scans the copies $e=vu$ at $v$ in increasing order and returns the first with $\mathrm{EO}(e,u)$ = "yes", or "unmatched". Answers are memoized within one call of $\mathrm{VO}$.
--
--   The module also defines independent sets, matchings, maximal matchings, and the expected random-greedy matching size $\mu$.
--
--   **Formalization Note.** An order is an equivalence from the copies to their ranks. The oracles are executable functions returning an answer and a state; the state holds the memo table and a counter of invocations of each directed state, cached invocations included. The recursion runs on a fuel equal to the number of copies, and each recursive call lowers the rank, so the fuel does not run out. A sanity file checks by computation that $\mathrm{VO}$ reports the greedy matching's copy on a triangle with a parallel edge under all orders.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Section 4.2, p.21

import Mathlib

namespace SublinearSteiner

/-!
# Local random-greedy matching on multigraphs

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), Section 4.2, p.21.

A finite loopless multigraph with labeled edge copies, a uniformly random order (ranks), the random-greedy maximal
matching, and the local oracles: `EO(e, u)` decides whether `u` is still unmatched just before the rank of `e`, and
`VO(v)` returns the matched copy of `v` or "unmatched". Answers are memoized within one call of `VO`.

**Formalization Note.**
* An order is an equivalence `E ≃ Fin |E|`, the rank of a copy being its image.
* `eoFuel` is a recursion on a fuel, and every recursive call strictly lowers the rank. `|E|` units of fuel are never
  exhausted, so the `0` branch is unreachable from `eo` (checked by the sanity file on an example).
* `OracleState.count` counts every invocation of `EO`, cached ones included. A cached invocation does no recursion.
* The oracles are executable. They mention no machine: their cost is the count alone.
-/

/-- A finite loopless multigraph: vertices `U`, labeled edge copies `E`, and the two endpoints of each copy. -/
structure Multigraph (U E : Type) where
  /-- One endpoint. -/
  src : E → U
  /-- The other endpoint. -/
  tgt : E → U
  ne : ∀ e, src e ≠ tgt e

namespace Multigraph

variable {U E : Type} [DecidableEq U]

/-- `u` is an endpoint of the copy `e`. -/
def Incident (H : Multigraph U E) (e : E) (u : U) : Prop := H.src e = u ∨ H.tgt e = u

instance (H : Multigraph U E) (e : E) (u : U) : Decidable (H.Incident e u) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The endpoint of `e` other than `u`. -/
def other (H : Multigraph U E) (e : E) (u : U) : U := if H.src e = u then H.tgt e else H.src e

variable [Fintype E] [DecidableEq E]

/-- An order of the copies: `π e` is the rank of `e`. -/
abbrev Order (E : Type) [Fintype E] := E ≃ Fin (Fintype.card E)

/-- The copies in increasing rank. -/
def byRank (π : Order E) : List E := (List.finRange (Fintype.card E)).map π.symm

/-- One step of the random-greedy matching: add `e` when both endpoints are free. -/
def greedyStep (H : Multigraph U E) (M : Finset E) (e : E) : Finset E :=
  if (∀ f ∈ M, ¬ H.Incident f (H.src e)) ∧ (∀ f ∈ M, ¬ H.Incident f (H.tgt e)) then insert e M else M

/-- The random-greedy maximal matching for the order `π`: scan the copies by increasing rank, adding a copy whenever
both endpoints are free. -/
def greedy (H : Multigraph U E) (π : Order E) : Finset E :=
  (byRank π).foldl (greedyStep H) ∅

/-- The memo table and the invocation counters of one call of `VO`. -/
structure OracleState (U E : Type) where
  /-- The memoized answers of `EO`. -/
  cache : E × U → Option Bool
  /-- The number of invocations of each directed state, cached ones included. -/
  count : E × U → ℕ

/-- The state at the start of a call of `VO`. -/
def OracleState.init : OracleState U E := ⟨fun _ => none, fun _ => 0⟩

/-- Count one invocation. -/
def OracleState.bump (st : OracleState U E) (q : E × U) : OracleState U E :=
  ⟨st.cache, Function.update st.count q (st.count q + 1)⟩

/-- Memoize one answer. -/
def OracleState.store (st : OracleState U E) (q : E × U) (b : Bool) : OracleState U E :=
  ⟨Function.update st.cache q (some b), st.count⟩

/-- The other copies at `u` of smaller rank than `e`, in increasing order. -/
def lowerCopies (H : Multigraph U E) (π : Order E) (e : E) (u : U) : List E :=
  (byRank π).filter fun f => f ≠ e ∧ H.Incident f u ∧ π f < π e

/-- The scan of `EO`: call `EO(f, u_f)` for the listed copies `f` at `u` and their other endpoints `u_f`, answering "no"
(`false`) at the first positive call and "yes" (`true`) if there is none. -/
def scanLower (H : Multigraph U E) (call : E → U → OracleState U E → Bool × OracleState U E) (u : U) :
    List E → OracleState U E → Bool × OracleState U E
  | [], st => (true, st)
  | f :: fs, st =>
      let r := call f (H.other f u) st
      if r.1 then (false, r.2) else scanLower H call u fs r.2

/-- `EO` with a fuel bound on the recursion depth. Every invocation is counted; a memoized answer returns at once. -/
def eoFuel (H : Multigraph U E) (π : Order E) :
    ℕ → E → U → OracleState U E → Bool × OracleState U E
  | 0, _, _, st => (true, st)
  | k + 1, e, u, st =>
      let st₁ := st.bump (e, u)
      match st₁.cache (e, u) with
      | some b => (b, st₁)
      | none =>
          let r := scanLower H (eoFuel H π k) u (lowerCopies H π e u) st₁
          (r.1, r.2.store (e, u) r.1)

/-- The directed oracle `EO(e, u)`: whether `u` is still unmatched just before the rank of `e`. -/
def eo (H : Multigraph U E) (π : Order E) (e : E) (u : U) (st : OracleState U E) :
    Bool × OracleState U E :=
  eoFuel H π (Fintype.card E) e u st

/-- The scan of `VO(v)`: the first listed copy `e = vu` with `EO(e, u) = yes`, or `none`. -/
def scanVertex (H : Multigraph U E) (π : Order E) (v : U) :
    List E → OracleState U E → Option E × OracleState U E
  | [], st => (none, st)
  | e :: es, st =>
      let r := eo H π e (H.other e v) st
      if r.1 then (some e, r.2) else scanVertex H π v es r.2

/-- The vertex oracle `VO(v)`, as one call with a fresh memo table: the matched copy of `v` (or `none`), and the final
state, whose counters are the invocations made during this call. -/
def vo (H : Multigraph U E) (π : Order E) (v : U) : Option E × OracleState U E :=
  scanVertex H π v ((byRank π).filter fun e => H.Incident e v) OracleState.init

/-- `I` is independent: no copy has both endpoints in `I`. -/
def IsIndependent (H : Multigraph U E) (I : Finset U) : Prop :=
  ∀ e, ¬ (H.src e ∈ I ∧ H.tgt e ∈ I)

/-- `M` is a matching: distinct copies share no endpoint. -/
def IsMatching (H : Multigraph U E) (M : Finset E) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ¬ H.Incident f (H.src e) ∧ ¬ H.Incident f (H.tgt e)

/-- `M` is a maximal matching: no further copy can be added. -/
def IsMaximalMatching (H : Multigraph U E) (M : Finset E) : Prop :=
  H.IsMatching M ∧ ∀ e, e ∉ M → ¬ H.IsMatching (insert e M)

/-- The expectation of a real function over a uniformly random order. -/
noncomputable def avgOrder (f : Order E → ℝ) : ℝ :=
  (Fintype.card (Order E) : ℝ)⁻¹ * ∑ π : Order E, f π

/-- `μ`: the expected size of the random-greedy matching. -/
noncomputable def expectedMatching (H : Multigraph U E) : ℝ :=
  avgOrder fun π => ((greedy H π).card : ℝ)

end Multigraph

end SublinearSteiner


