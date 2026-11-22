-- Prove2me | Definitions.Def_DecrNbhdCover_Supplement_TerminalCore
-- name    : DecrNbhdCover_Supplement_TerminalCore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:28:10.074796+00:00
-- url     : https://prove2.me/theorems/9f7da788-1756-4960-b617-008b22e5b2d4
-- title:
--   The interface of the terminal-core algorithm (Theorem 5.3)
-- statement:
--   The input is a connected $n$-vertex graph $G$ with positive integer lengths and $m_0$ edges, a set $T\subseteq V(G)$ of $q$ **terminals**, and rationals $\epsilon,d,\eta$ with $2/(\log_2 q)^{1/12}<\epsilon<1/400$, $1/\epsilon$ an integer, $d>1$, $\eta>1$, and $q>q_0$ for a threshold $q_0$.
--
--   **FAIL witness.** Disjoint $T_1,T_2\subseteq T$ and a set $E'$ of edges of $G$ with
--   $$|T_1|=|T_2|\ge\frac{q^{1-4\epsilon^3}}{4},\qquad |E'|\le\frac{d\,|T_1|}{\eta},\qquad \mathrm{dist}_{G\setminus E'}(t,t')>d\ \text{ for all }t\in T_1,\ t'\in T_2.$$
--
--   **Continuing run.** After an initialization that outputs a set $S\subseteq T$, the graph undergoes at most $\Lambda=|T|^{1-11\epsilon}/\eta$ edge deletions, and the algorithm maintains a decremental $S'\subseteq S$ with $|S'|\ge q/2^{6/\epsilon}$ at all times. A query $(x,y)$ with $x,y\in S'$ returns a path $P$ from $x$ to $y$ in the current $G$ of length at most $d\cdot2^{C/\epsilon^6}$, in at most $C(|E(P)|+1)$ steps, and $P$ is a concatenation of non-empty segments, each a simple path between two distinct terminals. The time after initialization is at most $C\,n^{1+C\epsilon}$. The initialization bound is $C(\log_2(2+n+m_0))^C\,m_0^{1+C\epsilon}\,\eta\,d^3$.
--
--   **Formalization Note** The initialization window outputs exactly one report: the FAIL witness, or $S$. Later windows may only report that a vertex leaves $S'$. For $x=y$ the empty path with no segment is allowed. The segment condition is on the edge list: it is the concatenation of the edge lists of simple paths of the current $G$, each with at least one edge and with two distinct terminals as endpoints.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 5.3, pp.36–37 (PDF 40–41)

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Common

set_option autoImplicit false

namespace DecrNbhdCover.Supplement

open DynConnWC
open scoped ENNReal

/-! # The terminal-core problem of Theorem 5.3

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Theorem 5.3, pp.36–37 (PDF 40–41).

**Formalization Note.** Input words: `n`, the edge list of `G`, `q, t₁, …, t_q` (the terminals), then `ϵ`, `d`, `η` as rationals. The
initialization window outputs exactly one report: `0, |T₁|, T₁, |T₂|, T₂, |E′|, E′` ("FAIL" with its witness; the run then ends, and nothing
is required of later windows), or `1, |S|, S` (the initial set `S`, and `S′ = S`). Later windows may only report `2, v` (`v` leaves `S′`),
so `S′ ⊆ S` is decremental by construction. Sets are output as lists; a repeated entry counts once. Operations: `0, e` (delete edge `e`),
`1, x, y` (short-path query, answered with `k, e₁, …, e_k`). A path "can be decomposed into a sequence σ₁, …, σ_r of non-empty segments,
where each segment σ_i is a simple path connecting a pair of distinct vertices of T": its edge list is the concatenation of the edge lists
of `r` simple paths with at least one edge, each between two distinct terminals; for `x = y` the empty path with `r = 0` is allowed. -/

/-- A report of the terminal-core algorithm. -/
inductive TCReport where
  | fail (T₁ T₂ E' : List ℕ)
  | core (S : List ℕ)
  | leave (v : ℕ)

/-- The words of a report. -/
def TCReport.words : TCReport → List ℕ
  | .fail T₁ T₂ E' => 0 :: T₁.length :: T₁ ++ T₂.length :: T₂ ++ E'.length :: E'
  | .core S => 1 :: S.length :: S
  | .leave v => [2, v]

/-- The effect of a report on `S′` (`none` before `S` is computed): `S` is computed once; a vertex leaves `S′` only if it is in it; a
"FAIL" report is not a state change of a continuing run. -/
def tcStep (s : Option (Finset ℕ)) : TCReport → Option (Option (Finset ℕ))
  | .core S => match s with
    | none => some (some S.toFinset)
    | some _ => none
  | .leave v => match s with
    | some c => if v ∈ c then some (some (c.erase v)) else none
    | none => none
  | .fail _ _ _ => none

/-- An operation: an edge deletion, or a short-path query. -/
inductive TCOp where
  | del (e : ℕ)
  | query (x y : ℕ)

namespace TCOp

/-- The words of an operation. -/
def words : TCOp → List ℕ
  | .del e => [0, e]
  | .query x y => [1, x, y]

/-- The updates of `G`. -/
def gPart : TCOp → List GUpdate
  | .del e => [.delE e]
  | .query _ _ => []

/-- Whether an operation is a query. -/
def isQ : TCOp → Bool
  | .del _ => false
  | .query _ _ => true

end TCOp

/-- The protocol of Theorem 5.3. -/
def tcProtocol : Protocol TCOp TCReport (Option (Finset ℕ)) where
  opWords := TCOp.words
  isQuery := TCOp.isQ
  enc := TCReport.words
  step := tcStep
  st₀ := none

/-- The input of Theorem 5.3. -/
structure TCInput where
  n : ℕ
  edges : List (ℕ × ℕ × ℕ)
  T : List ℕ
  eps : ℚ
  d : ℚ
  eta : ℚ

namespace TCInput

variable (I : TCInput)

/-- The number `m₀` of initial edges. -/
def m : ℕ := I.edges.length

/-- The number `q` of terminals. -/
def q : ℕ := I.T.length

/-- The initial graph. -/
def G₀ : Graph ℕ ℕ := ofEdges I.n I.edges

/-- The conditions of Theorem 5.3, for the threshold `q₀`: `G` is connected, `T` is a set of `q > q₀` vertices, `1/ϵ` is an integer,
`2/(log q)^{1/12} < ϵ < 1/400`, `d > 1` and `η > 1`. -/
structure Ok (q₀ : ℕ) : Prop where
  edges_ok : EdgesOk I.n I.edges
  connected : ∀ u v, u < I.n → v < I.n → I.G₀.dist u v ≠ ⊤
  T_sub : ∀ t ∈ I.T, t < I.n
  T_nodup : I.T.Nodup
  q_gt : q₀ < I.q
  eps_inv : ∃ r : ℕ, I.eps = 1 / (r : ℚ)
  eps_gt : 2 / Real.logb 2 (I.q : ℝ) ^ ((1 : ℝ) / 12) < (I.eps : ℝ)
  eps_lt : I.eps < 1 / 400
  d_gt : 1 < I.d
  eta_gt : 1 < I.eta

/-- The initialization words. -/
def words : List ℕ :=
  I.n :: edgeWords I.edges ++ I.T.length :: I.T ++ ratWords I.eps ++ ratWords I.d ++ ratWords I.eta

/-- `G` after the first `t` operations. -/
def Gt (σ : List TCOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt I.G₀ (σ.map TCOp.gPart) t

/-- Valid operations: at most `Λ = |T|^{1−11ϵ}/η` edge deletions in all, each of a present edge, and queries on two vertices of the
current `S′`. -/
def Valid (W : ℕ) (P : Program) (σ : List TCOp) : Prop :=
  (((σ.filter (fun o => !o.isQ)).length : ℕ) : ℝ) ≤ (I.q : ℝ) ^ (1 - 11 * (I.eps : ℝ)) / (I.eta : ℝ) ∧
  ∀ (t : ℕ) (o : TCOp), σ[t]? = some o →
    match o with
    | .del e => e ∈ (I.Gt σ t).E
    | .query x y => ∃ c, tcProtocol.state W P I.words σ t = some (some c) ∧ x ∈ c ∧ y ∈ c

/-- The "FAIL" witness satisfies properties 1–3: disjoint `T₁, T₂ ⊆ T` with `|T₁| = |T₂| ≥ q^{1−4ϵ³}/4`, a set `E′` of edges of `G` with
`|E′| ≤ d·|T₁|/η`, and `dist_{G∖E′}(t, t′) > d` for all `t ∈ T₁`, `t′ ∈ T₂`. -/
structure FailOk (T₁ T₂ E' : List ℕ) : Prop where
  T₁_sub : ∀ t ∈ T₁, t ∈ I.T
  T₂_sub : ∀ t ∈ T₂, t ∈ I.T
  disj : Disjoint T₁.toFinset T₂.toFinset
  card_eq : T₁.toFinset.card = T₂.toFinset.card
  card_ge : (I.q : ℝ) ^ (1 - 4 * (I.eps : ℝ) ^ 3) / 4 ≤ (T₁.toFinset.card : ℝ)
  E_sub : ∀ e ∈ E', e ∈ I.G₀.E
  E_card : (E'.toFinset.card : ℝ) ≤ (I.d : ℝ) * (T₁.toFinset.card : ℝ) / (I.eta : ℝ)
  far : ∀ t ∈ T₁, ∀ t' ∈ T₂,
    ENNReal.ofReal (I.d : ℝ) < (((({ I.G₀ with E := I.G₀.E \ {e | e ∈ E'} } : Graph ℕ ℕ)).dist t t' : ℕ∞) : ℝ≥0∞)

end TCInput

/-- `es` is a walk of `G` from `x` to `y` that is the concatenation of non-empty simple paths, each joining two distinct vertices of `T`. -/
def TerminalSegments (G : Graph ℕ ℕ) (T : List ℕ) (x : ℕ) (es : List ℕ) (y : ℕ) : Prop :=
  G.WalkFromTo x es y ∧
    ∃ segs : List (List ℕ × List ℕ), es = (segs.map Prod.snd).flatten ∧
      ∀ seg ∈ segs, G.IsPath seg.1 seg.2 ∧ seg.2 ≠ [] ∧
        ∃ a b, seg.1.head? = some a ∧ seg.1.getLast? = some b ∧ a ∈ T ∧ b ∈ T ∧ a ≠ b

/-- The clauses of Theorem 5.3 after a non-failing initialization that computed `S`, with the constant `C`. -/
structure TCHolds (C W : ℕ) (P : Program) (I : TCInput) (σ : List TCOp) : Prop where
  runs : RunsThrough W P (tcProtocol.blocks I.words σ)
  /-- At all times `|S′| ≥ q/2^{6/ϵ}`. -/
  log : ∀ t ≤ σ.length, ∃ c, tcProtocol.state W P I.words σ t = some (some c) ∧
    (I.q : ℝ) / (2 : ℝ) ^ (6 / (I.eps : ℝ)) ≤ (c.card : ℝ)
  /-- Short-path queries: a path in the current `G` made of terminal-to-terminal segments, of length at most `d·2^{C/ϵ⁶}`, in time
  `C·(|E(P)| + 1)`. -/
  query : ∀ (t x y : ℕ), σ[t]? = some (.query x y) →
    ∃ es, tcProtocol.answer W P I.words σ t = some es ∧
      TerminalSegments (I.Gt σ t) I.T x es y ∧
      ((I.Gt σ t).walkLen es : ℝ) ≤ (I.d : ℝ) * (2 : ℝ) ^ ((C : ℝ) / (I.eps : ℝ) ^ 6) ∧
      (tcProtocol.opTime W P I.words σ t : ℝ) ≤ (C : ℝ) * ((es.length : ℝ) + 1)
  /-- The total update time after initialization is at most `C·n^{1+Cϵ}`. -/
  time : (laterTime tcProtocol W P I.words σ : ℝ) ≤ (C : ℝ) * (I.n : ℝ) ^ (1 + (C : ℝ) * (I.eps : ℝ))

/-- The run reaches the read of the first word after the initialization input, so the initialization window, its output and its time are
determined. -/
def InitEnds (W : ℕ) (P : Program) (blocks : List (List ℕ)) : Prop :=
  (readStep W P blocks.flatten (zeroTape W) (startRead blocks 1)).isSome

/-- The initialization time bound `C·log₂(2+n+m₀)^C·m₀^{1+Cϵ}·η·d³`. -/
noncomputable def tcInitBound (C : ℕ) (I : TCInput) : ℝ :=
  polylog C I.n I.m * (I.m : ℝ) ^ (1 + (C : ℝ) * (I.eps : ℝ)) * (I.eta : ℝ) * (I.d : ℝ) ^ 3

end DecrNbhdCover.Supplement


