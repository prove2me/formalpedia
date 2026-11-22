-- Prove2me | Definitions.Def_DecrNbhdCover_Supplement_Emulator
-- name    : DecrNbhdCover_Supplement_Emulator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:25:50.630714+00:00
-- url     : https://prove2.me/theorems/2a8588dc-02b3-45ec-bfa4-f8fabbfd46e9
-- title:
--   The interface of the emulator of a decremental graph (Theorem 3.24)
-- statement:
--   The input is an $n$-vertex, $m$-edge graph $G$ with positive integer lengths, and rationals $0<\epsilon<1$ and $0<d<D$ with $D>4d\cdot2^{1/\epsilon^{c'}}$, where $c'$ is a parameter of the condition. $G$ undergoes edge deletions.
--
--   The algorithm reports once a value $d^*>0$, and it reports a dynamic graph $H$ whose edges carry positive integer multipliers: an edge with multiplier $\ell$ has length $\ell\cdot d^*$ in $H$. With a constant $C$, the clauses are:
--
--   1. $d^*$ is reported at initialization and $d/C\le d^*\le C\,d$.
--   2. At all times $V(G)\subseteq V(H)$ and, for all $x,y\in V(G)$,
--   $$\mathrm{dist}_G(x,y)\le \mathrm{dist}_H(x,y)\le(1+\epsilon)\,\mathrm{dist}_G(x,y)+\epsilon D.$$
--   3. The number of edges that ever lie in $H$ is at most $C\,m^{1+C\epsilon}$.
--   4. A transform query gives a (possibly non-simple) path $P$ of the current $H$ between distinct $x,y\in V(G)$ whose inner vertices all lie outside $V(G)$. The answer is a (possibly non-simple) path $P'$ of $G$ from $x$ to $y$ with $\ell_G(P')\le\ell_H(P)$ and $|E(P)|\le C(\log_2(2+m))^C|E(P')|$, in at most $C(\log_2(2+n+m))^C(|E(P')|+1)$ steps.
--   5. The total update time is at most $C\left(n+m^{1+C\epsilon}\cdot2^{C/\epsilon^C}\right)$.
--
--   This is the object that Theorem 3.24 asserts an algorithm for.
--
--   **Formalization Note** $H$ is any reported dynamic graph: it is not required to be well-structured. Reporting integer multipliers of one value $d^*$, which can be reported only once, is how "all edge lengths in $H$ are integral multiples of a value $d^*$ that remains fixed" is expressed. Distances are extended naturals, compared in $[0,\infty]$. Input words: $n$, the edge list, then $\epsilon,d,D$ as numerator and denominator.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.24, p.27 (PDF 31)

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Common

set_option autoImplicit false

namespace DecrNbhdCover.Supplement

open DynConnWC
open scoped ENNReal

/-! # The emulator of a decremental graph (Theorem 3.24)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Theorem 3.24, p.27 (PDF 31).

**Formalization Note.** Input words: `n`, the edge list of `G`, then `ϵ`, `d`, `D` as rationals. Operations: `0, e` deletes edge `e` of
`G`; `1, x, y, k, f₁, …, f_k` asks to transform the path of `H` with edges `f₁ … f_k`, answered with `k′, e₁, …, e_{k′}` (edges of `G`).
The program reports `d*` once, as `4, p, q` (the rational `p/q > 0`), and `H` as a reported dynamic graph whose edge "lengths" are the
multipliers: an edge reported with `ℓ` has length `ℓ·d*` in `H`. So every length of `H` is an integral multiple of the one value `d*`,
which can be reported only once and so stays fixed, and `dist_H = d*·dist` of the multiplier graph. `H` may have vertices of any
number; `V(G) = {0, …, n-1}` must be among them. -/

/-- A report: `d* = p/q`, or an update of `H`. -/
inductive EmuReport where
  | dstar (p q : ℕ)
  | upd (r : DynReport)

/-- The words of a report. -/
def EmuReport.words : EmuReport → List ℕ
  | .dstar p q => [4, p, q]
  | .upd r => r.words

/-- The reported `d*` (`none` before it is reported) and the reported `H`, with multipliers as edge lengths. -/
structure EmuState where
  dstar : Option ℚ
  h : DynState

open Classical in
/-- The effect of a report: `d*` is reported once, and positive. -/
noncomputable def emuStep (s : EmuState) : EmuReport → Option EmuState
  | .dstar p q => if s.dstar = none ∧ q ≠ 0 ∧ 0 < p then some { s with dstar := some ((p : ℚ) / (q : ℚ)) } else none
  | .upd r => (s.h.step r).map (fun h => { s with h := h })

/-- An operation: an edge deletion from `G`, or a transform-path query. -/
inductive EmuOp where
  | del (e : ℕ)
  | query (x y : ℕ) (es : List ℕ)

namespace EmuOp

/-- The words of an operation. -/
def words : EmuOp → List ℕ
  | .del e => [0, e]
  | .query x y es => 1 :: x :: y :: es.length :: es

/-- The updates of `G`. -/
def gPart : EmuOp → List GUpdate
  | .del e => [.delE e]
  | .query _ _ _ => []

/-- Whether an operation is a query. -/
def isQ : EmuOp → Bool
  | .del _ => false
  | .query _ _ _ => true

end EmuOp

/-- The protocol of Theorem 3.24. -/
noncomputable def emuProtocol : Protocol EmuOp EmuReport EmuState where
  opWords := EmuOp.words
  isQuery := EmuOp.isQ
  enc := EmuReport.words
  step := emuStep
  st₀ := ⟨none, DynState.empty⟩

/-- The input of Theorem 3.24. -/
structure EmuInput where
  n : ℕ
  edges : List (ℕ × ℕ × ℕ)
  eps : ℚ
  d : ℚ
  D : ℚ

namespace EmuInput

variable (I : EmuInput)

/-- The number of edges. -/
def m : ℕ := I.edges.length

/-- The conditions of Theorem 3.24, for the constant `c′`: `n ≥ 1`, `0 < ϵ < 1`, `0 < d < D`, and `D > 4d·2^{1/ϵ^{c′}}`. -/
structure Ok (c' : ℕ) : Prop where
  n_pos : 1 ≤ I.n
  edges_ok : EdgesOk I.n I.edges
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1
  d_pos : 0 < I.d
  d_lt : I.d < I.D
  D_gt : 4 * (I.d : ℝ) * (2 : ℝ) ^ (1 / (I.eps : ℝ) ^ c') < (I.D : ℝ)

/-- The initialization words. -/
def words : List ℕ :=
  I.n :: edgeWords I.edges ++ ratWords I.eps ++ ratWords I.d ++ ratWords I.D

/-- `G` after the first `t` operations. -/
def Gt (σ : List EmuOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map EmuOp.gPart) t

/-- Valid operations: a present edge is deleted; a query is on a (possibly non-simple) path of the `H` reported so far that connects
two distinct vertices `x, y` of `G` and whose inner vertices all lie outside `V(G)`. -/
def Valid (W : ℕ) (P : Program) (σ : List EmuOp) : Prop :=
  ∀ (t : ℕ) (o : EmuOp), σ[t]? = some o →
    match o with
    | .del e => e ∈ (I.Gt σ t).E
    | .query x y es => ∃ s, emuProtocol.state W P I.words σ t = some s ∧
        x ∈ (I.Gt σ t).V ∧ y ∈ (I.Gt σ t).V ∧ x ≠ y ∧
        ∃ vs, s.h.g.IsWalk vs es ∧ vs.head? = some x ∧ vs.getLast? = some y ∧
          ∀ w ∈ vs.tail.dropLast, w ∉ (I.Gt σ t).V

end EmuInput

/-- The clauses of Theorem 3.24 with the constant `C`. -/
structure EmuHolds (C W : ℕ) (P : Program) (I : EmuInput) (σ : List EmuOp) : Prop where
  runs : RunsThrough W P (emuProtocol.blocks I.words σ)
  /-- `d*` is reported at initialization, with `d/C ≤ d* ≤ C·d`. -/
  dstar : ∃ s x, emuProtocol.state W P I.words σ 0 = some s ∧ s.dstar = some x ∧
    (I.d : ℝ) / (C : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ (C : ℝ) * (I.d : ℝ)
  /-- At all times `V(G) ⊆ V(H)` and `distG(x, y) ≤ distH(x, y) ≤ (1 + ϵ)distG(x, y) + ϵD` for `x, y ∈ V(G)`. -/
  log : ∀ t ≤ σ.length, ∃ s x, emuProtocol.state W P I.words σ t = some s ∧ s.dstar = some x ∧
    (I.Gt σ t).V ⊆ s.h.g.V ∧
    ∀ u ∈ (I.Gt σ t).V, ∀ v ∈ (I.Gt σ t).V,
      (((I.Gt σ t).dist u v : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (x : ℝ) * ((s.h.g.dist u v : ℕ∞) : ℝ≥0∞) ∧
      ENNReal.ofReal (x : ℝ) * ((s.h.g.dist u v : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (1 + (I.eps : ℝ)) * (((I.Gt σ t).dist u v : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal ((I.eps : ℝ) * (I.D : ℝ))
  /-- The number of edges that ever lie in `H` is at most `C·m^{1+Cϵ}`. -/
  edges : ∃ s, emuProtocol.state W P I.words σ σ.length = some s ∧
    ((s.h.ever.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((C : ℝ) * (I.m : ℝ) ^ (1 + (C : ℝ) * (I.eps : ℝ)))
  /-- Transform-path queries: a walk `P′` in `G` from `x` to `y` with `ℓG(P′) ≤ ℓH(P)` and `|E(P)| ≤ C·log₂(2+m)^C·|E(P′)|`, in time
  `C·log₂(2+n+m)^C·(|E(P′)| + 1)`. -/
  query : ∀ (t x y : ℕ) (es : List ℕ) (s : EmuState) (dx : ℚ), σ[t]? = some (.query x y es) →
    emuProtocol.state W P I.words σ t = some s → s.dstar = some dx →
    ∃ es', emuProtocol.answer W P I.words σ t = some es' ∧
      (I.Gt σ t).WalkFromTo x es' y ∧
      ((I.Gt σ t).walkLen es' : ℝ) ≤ (dx : ℝ) * (s.h.g.walkLen es : ℝ) ∧
      (es.length : ℝ) ≤ (C : ℝ) * lg (I.m : ℝ) ^ C * (es'.length : ℝ) ∧
      (emuProtocol.opTime W P I.words σ t : ℝ) ≤ polylog C I.n I.m * ((es'.length : ℝ) + 1)
  /-- The total update time `C·(n + m^{1+Cϵ}·2^{C/ϵ^C})`. -/
  time : (emuProtocol.updateTime W P I.words σ : ℝ) ≤
    (C : ℝ) * ((I.n : ℝ) + (I.m : ℝ) ^ (1 + (C : ℝ) * (I.eps : ℝ)) * expEps C (I.eps : ℝ))

end DecrNbhdCover.Supplement


