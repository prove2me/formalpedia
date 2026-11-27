-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_Supplement_Algorithm3
-- name    : AccelNewtonDinkelbach_Supplement_Algorithm3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:01:36.666819+00:00
-- url     : https://prove2.me/theorems/785507ac-bbf7-46e9-a975-848db4253852
-- title:
--   Algorithm 3, the label-correcting algorithm for M2VPI systems, with the Grapevine oracle
-- statement:
--   This definition encodes the executions of **Algorithm 3** (p.15) on an M2VPI system $(G,c,\gamma)$, including the run of the look-ahead Newton–Dinkelbach method (Algorithm 1, p.7) that line 14 performs with Grapevine as value and supergradient oracle.
--
--   1. **Outer loop.** Labels start at $y_v=+\infty$. The nodes are processed in an arbitrary order; in phase $k$ the node $u$ is processed and $G^{(k)}=G^{(k-1)}\cup\delta^+(u)$. Line 6 sets $y_u\leftarrow\min_{uv\in\delta^+(u)} c_{uv}+\gamma_{uv}y_v$ (which is $+\infty$ over an empty arc set); if $y_u=+\infty$ and $G^{(k)}$ has a flow-absorbing cycle $C$ at $u$, line 8 sets $y_u\leftarrow c(C)/(1-\gamma(C))$ for any such $C$. If $y_u<\infty$, Grapevine runs on the split graph $G^{(k)}_u$ from $\bar y_{u'}=y_u$, $\bar y_v=y_v$, returning labels and a walk $P$; the phase returns `INFEASIBLE` if an arc of $G_u^{(k)}$ is violated or if $P$ is nontrivial with $\gamma(P)\ge 1$.
--   2. **Oracle.** A query at $\delta$ runs Grapevine on $G^{(k)}_u$ from the current labels with $\bar y_{u'}:=\delta$. If the returned labels $\bar z$ violate an arc, it reports $f(\delta)=-\infty$; otherwise it reports $f(\delta)=\bar z_u-\delta$ and the supergradient $\gamma(P)-1$ if $P$ ends at $u'$, and $-1$ otherwise.
--   3. **Line 14.** Algorithm 1 starts at $\delta^{(1)}=y_u$ with $g^{(1)}=\gamma(P)-1$ and value $\bar z_u-y_u$. Each iteration queries the Newton point $\delta=\delta^{(i)}-f(\delta^{(i)})/g^{(i)}$ and the look-ahead point $2\delta-\delta^{(i)}$, returns NO ROOT if $f(\delta)=-\infty$ or ($f(\delta)<0$ and $g\ge 0$), and accepts the look-ahead point when its value and supergradient are both negative. A NO ROOT return makes the phase return `INFEASIBLE`; a root return sets $y\leftarrow\bar y_V$ (line 17).
--   4. A run returns `INFEASIBLE` at the first phase that does so, and otherwise returns the labels after the last phase.
--
--   **Formalization Note** Every free choice is existential at the point where it is made: the node order, the cycle of line 8, and every Grapevine tie-break (hence every oracle answer). The paper says that Grapevine "continues to update $\bar y$ throughout the execution of Algorithm 1" (p.16), which is ambiguous at a failed look-ahead query. The encoding follows the label state both proofs use (p.16, and "the sequence of node labels at the start of every iteration", p.17): both queries of an iteration warm-start from the labels of the current iterate, a query's returned labels are kept exactly when its point becomes the next iterate, and line 17 uses the final iterate's labels. Algorithm 1 is run on the oracle's answers, as the algorithm executes it. Iterates are 1-indexed; phases are indexed $0,\dots,n-1$, so phase $k$ here uses $G^{(k+1)}$ in the paper's numbering.
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Algorithm 3 and surrounding text, pp.15–16

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_Supplement_M2VPICycles
import Definitions.Def_AccelNewtonDinkelbach_Supplement_Grapevine

namespace AccelNewtonDinkelbach.Supplement

set_option autoImplicit false

/-! # Algorithm 3 (label-correcting algorithm for M2VPI systems)

Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Algorithm 3, p.15, with the oracle of line 14
described on p.14 (last paragraph) and p.15–16 ("The value and supergradient oracle for the
parametric function f(δ) is Grapevine"), and Algorithm 1 (Look-aheadNewton), p.7.

**Formalization Note**
1. Every free choice of the pseudocode is existentially chosen at the point where it is made:
   the node order of line 3 (any bijection `Fin n → Fin n`), the cycle `C` of line 8, every
   Grapevine tie-break (`Grapevine` is a relation), and hence every oracle answer.
2. The oracle at a query point `δ` runs Grapevine on `G_u^(k)` from the current labels with
   `ȳ_u′ := δ`; it reports `f(δ) = −∞` if the returned labels violate an arc of `G_u^(k)`, and
   otherwise the value `z̄_u − δ` and the supergradient `γ(P) − 1` if the returned walk `P` ends
   at `u′`, `−1` otherwise (p.14, last paragraph).
3. Label state inside line 14 (a source ambiguity, p.16: "Grapevine continues to update ȳ
   throughout the execution of Algorithm 1"). The encoding follows the reading both proofs use
   (proof of Theorem 4.8, p.16, and "the sequence of node labels at the start of every iteration
   of Algorithm 1", proof of Theorem 4.11, p.17): both oracle calls of an iteration warm-start
   from the labels of the current iterate `δ(i)`; the labels a call returns are kept exactly when
   its query point becomes `δ(i+1)`; line 17 uses the labels of the final iterate.
4. Algorithm 1 inside line 14 is run on the oracle's answers, exactly as the algorithm executes
   it: the stored value `val` of an iterate is the oracle's value at it. Line 14 starts it at
   `δ(1) = ȳ_u′ = y_u` with `g(1) = γ(P) − 1` and value `z̄_u − y_u` from the line-11 call.
5. Iterates are 1-indexed. Line 6's minimum over an empty arc set is `⊤ = ∞` (`sInf ∅`). -/

namespace M2VPI

variable {n m : ℕ} (M : M2VPI n m)

/-- The two possible outputs of Algorithm 3: node labels in `ℝ̄^n`, or `INFEASIBLE`. -/
inductive Algorithm3Result (n : ℕ)
  | labels (y : Fin n → EReal)
  | infeasible

/-- The arc set of `G^(k)` for the node order `order`: the outgoing arcs of the first `k`
processed nodes (line 5, `G^(k) ← G^(k−1) ∪ δ⁺(u)`). -/
def PhaseEdges (order : Fin n → Fin n) (k : ℕ) (e : Fin m) : Prop :=
  ∃ i : Fin n, i.val < k ∧ M.tail e = order i

/-- The number of arcs of an arc set, `|E(G^(k))|` for `A = PhaseEdges order k`. -/
noncomputable def activeArcCount (A : Fin m → Prop) : ℕ := Nat.card {e : Fin m // A e}

/-- An arc `e = (v,w)` of `G_u` (with `A e`) is violated w.r.t. labels `L` if
`L_v > c_e + γ_e L_w` (p.13). -/
def HasViolatedArc (A : Fin m → Prop) (u : Fin n) (L : SplitNode n → EReal) : Prop :=
  ∃ e, A e ∧ (M.cost e : EReal) + (M.gain e : EReal) * L (M.splitHead u e) < L (M.splitTail e)

/-- One call of the Grapevine oracle at query point `δ`, warm-started from labels `L`
(with `ȳ_u′` replaced by `δ`).  `ans = none` reports `f(δ) = −∞`; `ans = some (val, g)` reports
the value and supergradient; `L'` are the labels Grapevine returns. -/
def OracleCall (A : Fin m → Prop) (u : Fin n) (L : SplitNode n → EReal) (δ : ℝ)
    (ans : Option (ℝ × ℝ)) (L' : SplitNode n → EReal) : Prop :=
  ∃ P : M.SplitWalk A u, M.Grapevine A u (Function.update L none (δ : EReal)) L' P ∧
    ((M.HasViolatedArc A u L' ∧ ans = none) ∨
      (¬ M.HasViolatedArc A u L' ∧ ∃ z : ℝ, L' (some u) = (z : EReal) ∧
        ans = some (z - δ, if P.finish = none then P.walkGain - 1 else -1)))

/-- The state of Algorithm 1 at an iterate: the point `δ(i)`, the supergradient `g(i)`, the
oracle value `f(δ(i))`, and the Grapevine labels kept with the iterate. -/
structure InnerState (n : ℕ) where
  delta : ℝ
  g : ℝ
  val : ℝ
  labels : SplitNode n → EReal

/-- One iteration (lines 2–11 of Algorithm 1) that does not return: from `s` to `s'`. -/
def InnerStep (A : Fin m → Prop) (u : Fin n) (s s' : InnerState n) : Prop :=
  s.val < 0 ∧
    let d := s.delta - s.val / s.g
    let ℓ := 2 * d - s.delta
    ∃ (fd gd : ℝ) (Ld : SplitNode n → EReal), M.OracleCall A u s.labels d (some (fd, gd)) Ld ∧
      ¬ (fd < 0 ∧ 0 ≤ gd) ∧
      ∃ (aℓ : Option (ℝ × ℝ)) (Lℓ : SplitNode n → EReal), M.OracleCall A u s.labels ℓ aℓ Lℓ ∧
        ((∃ fℓ gℓ : ℝ, aℓ = some (fℓ, gℓ) ∧ fℓ < 0 ∧ gℓ < 0 ∧
            s' = ⟨ℓ, gℓ, fℓ, Lℓ⟩) ∨
          ((¬ ∃ fℓ gℓ : ℝ, aℓ = some (fℓ, gℓ) ∧ fℓ < 0 ∧ gℓ < 0) ∧
            s' = ⟨d, gd, fd, Ld⟩))

/-- Algorithm 1 returns NO ROOT at state `s` (lines 2–6). -/
def InnerNoRoot (A : Fin m → Prop) (u : Fin n) (s : InnerState n) : Prop :=
  s.val < 0 ∧
    ∃ (ad : Option (ℝ × ℝ)) (Ld : SplitNode n → EReal),
      M.OracleCall A u s.labels (s.delta - s.val / s.g) ad Ld ∧
      (ad = none ∨ ∃ fd gd : ℝ, ad = some (fd, gd) ∧ fd < 0 ∧ 0 ≤ gd)

/-- `s 1, …, s N` are the first `N` iterates of an execution of Algorithm 1 (with the Grapevine
oracle). -/
def InnerRun (A : Fin m → Prop) (u : Fin n) (s : ℕ → InnerState n) (N : ℕ) : Prop :=
  1 ≤ N ∧ ∀ i, 1 ≤ i → i < N → M.InnerStep A u (s i) (s (i + 1))

/-- A complete execution of Algorithm 1 from `s0`: `out = some L` if it returns the root
`δ(N)` (line 13) with final labels `L`, `out = none` if it returns NO ROOT. -/
def InnerOutcome (A : Fin m → Prop) (u : Fin n) (s0 : InnerState n)
    (out : Option (SplitNode n → EReal)) : Prop :=
  ∃ (s : ℕ → InnerState n) (N : ℕ), s 1 = s0 ∧ M.InnerRun A u s N ∧
    ((0 ≤ (s N).val ∧ out = some (s N).labels) ∨ (M.InnerNoRoot A u (s N) ∧ out = none))

/-- Lines 6–8 of phase `k` (node `u = order k`, graph `G^(k)`): the new label `yu` of `u`. -/
def Line6to8 (order : Fin n → Fin n) (k : Fin n) (y : Fin n → EReal) (yu : EReal) : Prop :=
  let u := order k
  let A := M.PhaseEdges order (k.val + 1)
  let y6 : EReal := sInf {z : EReal | ∃ e, M.tail e = u ∧
    z = (M.cost e : EReal) + (M.gain e : EReal) * y (M.head e)}
  (y6 = ⊤ ∧ ∃ C : M.Walk, C.IsCycleAt u ∧ C.UsesOnly M A ∧ C.FlowAbsorbing ∧
      yu = ((C.walkCost / (1 - C.walkGain) : ℝ) : EReal)) ∨
    (¬ (y6 = ⊤ ∧ M.HasAbsorbingCycleAt A u) ∧ yu = y6)

/-- Lines 6–11 of phase `k` with `y_u = δ1 < ∞`: Grapevine on `G_u^(k)` from
`ȳ_u′ := δ1`, `ȳ_v := y_v` (with `y_u` updated) returns `(L, P)`. -/
def Line11 (order : Fin n → Fin n) (k : Fin n) (y : Fin n → EReal) (δ1 : ℝ)
    (L : SplitNode n → EReal) (P : M.SplitWalk (M.PhaseEdges order (k.val + 1)) (order k)) :
    Prop :=
  M.Line6to8 order k y (δ1 : EReal) ∧
    M.Grapevine (M.PhaseEdges order (k.val + 1)) (order k)
      (fun v => match v with
        | none => (δ1 : EReal)
        | some w => Function.update y (order k) (δ1 : EReal) w) L P

/-- The test of line 12. -/
def Line12Fails (order : Fin n → Fin n) (k : Fin n) (L : SplitNode n → EReal)
    (P : M.SplitWalk (M.PhaseEdges order (k.val + 1)) (order k)) : Prop :=
  M.HasViolatedArc (M.PhaseEdges order (k.val + 1)) (order k) L ∨
    (P.edges ≠ [] ∧ 1 ≤ P.walkGain)

/-- Phase `k` reaches line 14 and starts Algorithm 1 at state `s0`: `δ(1) = ȳ_u′ = y_u`,
`g(1) = γ(P) − 1`, value `z̄_u − y_u`, labels `L` from line 11. -/
def Line14Start (order : Fin n → Fin n) (k : Fin n) (y : Fin n → EReal)
    (s0 : InnerState n) : Prop :=
  ∃ (δ1 : ℝ) (L : SplitNode n → EReal)
    (P : M.SplitWalk (M.PhaseEdges order (k.val + 1)) (order k)),
    M.Line11 order k y δ1 L P ∧ ¬ M.Line12Fails order k L P ∧
      ∃ z : ℝ, L (some (order k)) = (z : EReal) ∧ s0 = ⟨δ1, P.walkGain - 1, z - δ1, L⟩

/-- A complete execution of phase `k` (lines 4–17) from labels `y`: `r = some y'` if the phase
ends with labels `y'`, `r = none` if it returns INFEASIBLE (line 13 or 16). -/
def PhaseStep (order : Fin n → Fin n) (k : Fin n) (y : Fin n → EReal)
    (r : Option (Fin n → EReal)) : Prop :=
  (M.Line6to8 order k y ⊤ ∧ r = some (Function.update y (order k) ⊤)) ∨
  (∃ (δ1 : ℝ) (L : SplitNode n → EReal)
      (P : M.SplitWalk (M.PhaseEdges order (k.val + 1)) (order k)),
      M.Line11 order k y δ1 L P ∧ M.Line12Fails order k L P ∧ r = none) ∨
  (∃ s0 : InnerState n, M.Line14Start order k y s0 ∧
    ∃ out : Option (SplitNode n → EReal),
      M.InnerOutcome (M.PhaseEdges order (k.val + 1)) (order k) s0 out ∧
      ((out = none ∧ r = none) ∨ ∃ L, out = some L ∧ r = some (fun v => L (some v))))

/-- `Algorithm3Returns M result`: some execution of Algorithm 3 on `M` (some node order, cycle
choices, tie-breaks) returns `result`.  `ys k` are the labels at the start of phase `k`. -/
def Algorithm3Returns (result : Algorithm3Result n) : Prop :=
  ∃ order : Fin n → Fin n, Function.Bijective order ∧
    ∃ ys : ℕ → Fin n → EReal, ys 0 = (fun _ => ⊤) ∧
      ((∃ k : Fin n, (∀ j : Fin n, j < k → M.PhaseStep order j (ys j.val) (some (ys (j.val + 1)))) ∧
          M.PhaseStep order k (ys k.val) none ∧ result = .infeasible) ∨
        ((∀ j : Fin n, M.PhaseStep order j (ys j.val) (some (ys (j.val + 1)))) ∧
          result = .labels (ys n)))

end M2VPI

end AccelNewtonDinkelbach.Supplement


