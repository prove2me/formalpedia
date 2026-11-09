-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_Retrieval
-- name    : NearLinearRSP_TwoResources_Retrieval
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:13.200195+00:00
-- url     : https://prove2.me/theorems/ef5f05e9-7da3-4ff6-922f-e6d4eb427448
-- title:
--   Fresh adaptive Poisson retrieval and deterministic potential minimization
-- statement:
--   For an inner call let $z=(1+\delta/2)/(1+\delta)$ and let $M_\ell(u,v)=\exp(\lambda_\ell\ell(uv)(z-1))$, with the analogous $M_c$. These factors are strictly positive, including for a zero-weight edge. For a current suffix $P$ starting at $u$ and counters $i,j$, define
--   $$
--   \Phi(u,i,j,P)=\mathrm{DP}(u,i,j)+\frac{z^i}{8\prod_{xy\in P}M_\ell(x,y)}+\frac{z^j}{8\prod_{xy\in P}M_c(x,y)}.
--   $$
--   Products retain edge occurrences, and empty products are one. The state also stores the two multiplicatively updated potential terms, initially $1/8$ each. A virtual parent increments its labelled counter without adding an edge. An edge parent prepends its predecessor and chooses the first minimizing pair in $\{0,\ldots,q-i-1\}\times\{0,\ldots,q-j-1\}$ for the displayed conditional-expectation score of Section 6.
--
--   The deterministic routine is a bounded simulation with explicit failure for bad trajectories. Its fuel is $(2q+1)(a+1)$, where $a$ is the number of active vertices. Successful output, a valid path and resource bounds are not assumed. They are supplied by Lemma 6.2.
--
--   The random routine is defined separately as a finite probability tree: each traversal uses the current edge's fresh product-Poisson marginal, with all overflowing outcomes grouped into one atom. New transition probabilities are multiplied at each node of the adaptive tree; repeated traversals do not reuse a sampled edge label. Virtual moves expose no random draw. This supplies the process used for soundness without a potentially nonintegrable real expectation.
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), p.8, Random Path Retrieval; pp.10–12, Section 6, potential and Deterministic Path Retrieval

import Definitions.Def_NearLinearRSP_TwoResources_Inner

set_option autoImplicit false

namespace NearLinearRSP.TwoResources

noncomputable def lengthPGF (A : InnerInput) (u v : ℕ) : ℝ :=
  Real.exp (lengthRate A * A.I.length u v * (zValue A - 1))
noncomputable def costPGF (A : InnerInput) (u v : ℕ) : ℝ :=
  Real.exp (costRate A * A.I.cost u v * (zValue A - 1))

structure RetrievalState where
  front : ℕ
  path : List ℕ
  i : ℕ
  j : ℕ
  Hlength : ℝ
  Hcost : ℝ

noncomputable def retrievalStart (t : ℕ) : RetrievalState := ⟨t, [t], 0, 0, 1 / 8, 1 / 8⟩

noncomputable def potential (A : InnerInput) (S : RetrievalState) : ℝ :=
  dpValue A (buildTable A) S.front S.i S.j +
    zValue A ^ S.i / (8 * ((S.path.zip S.path.tail).map
      (fun e => lengthPGF A e.1 e.2)).prod) +
    zValue A ^ S.j / (8 * ((S.path.zip S.path.tail).map
      (fun e => costPGF A e.1 e.2)).prod)

/-- The rectangle excludes saturated states; order is a-major and then b-major. -/
noncomputable def incrementPairs (A : InnerInput) (S : RetrievalState) : List (ℕ × ℕ) :=
  (List.range (tickLimit A - S.i)).flatMap (fun a =>
    (List.range (tickLimit A - S.j)).map (fun b => (a, b)))

noncomputable def retrievalScore (A : InnerInput) (S : RetrievalState) (u : ℕ)
    (ab : ℕ × ℕ) : ℝ :=
  dpValue A (buildTable A) u (S.i + ab.1) (S.j + ab.2) +
    zValue A ^ ab.1 * S.Hlength / lengthPGF A u S.front +
    zValue A ^ ab.2 * S.Hcost / costPGF A u S.front

noncomputable def crossEdge (A : InnerInput) (S : RetrievalState) (u a b : ℕ) : RetrievalState :=
  ⟨u, u :: S.path, S.i + a, S.j + b,
    zValue A ^ a * S.Hlength / lengthPGF A u S.front,
    zValue A ^ b * S.Hcost / costPGF A u S.front⟩

/-- Failure is explicit on arbitrary bad trajectories; no success invariant is assumed. -/
noncomputable def retrievalStep (A : InnerInput) (S : RetrievalState) : Option RetrievalState :=
  if tickLimit A ≤ S.i ∨ tickLimit A ≤ S.j then none else
  match (buildTable A S.front S.i S.j).parent with
  | .none => none
  | .lengthTick => some { S with i := S.i + 1, Hlength := zValue A * S.Hlength }
  | .costTick => some { S with j := S.j + 1, Hcost := zValue A * S.Hcost }
  | .edge u =>
    match incrementPairs A S with
    | [] => none
    | p :: _ =>
      let ab := firstMin (retrievalScore A S u) (incrementPairs A S) p
      some (crossEdge A S u ab.1 ab.2)

noncomputable def retrievalRun (A : InnerInput) : ℕ → RetrievalState → Option RetrievalState
  | 0, S => if S.front = A.I.source ∧ S.i < tickLimit A ∧ S.j < tickLimit A then some S else none
  | fuel + 1, S =>
    if S.front = A.I.source ∧ S.i < tickLimit A ∧ S.j < tickLimit A then some S else
      (retrievalStep A S).bind (retrievalRun A fuel)

/-- Countdown/rank fuel; not a claim that the run succeeds. -/
noncomputable def retrievalFuel (A : InnerInput) : ℕ :=
  (2 * tickLimit A + 1) * ((activeVertices A.I).length + 1)

noncomputable def retrieve (A : InnerInput) (t : ℕ) : Option RetrievalState :=
  retrievalRun A (retrievalFuel A) (retrievalStart t)

/-- Finite marginal of the fresh Poisson draws for one adaptive step.
The last atom is overflow. Artificial ticks expose no random draw. -/
noncomputable def randomStepLaw (A : InnerInput) (S : RetrievalState) :
    List (Option RetrievalState × ℝ) :=
  if tickLimit A ≤ S.i ∨ tickLimit A ≤ S.j then [(none, 1)] else
  match (buildTable A S.front S.i S.j).parent with
  | .none => [(none, 1)]
  | .lengthTick => [(some { S with i := S.i + 1 }, 1)]
  | .costTick => [(some { S with j := S.j + 1 }, 1)]
  | .edge u =>
    let pairs := incrementPairs A S
    pairs.map (fun ab => (some (crossEdge A S u ab.1 ab.2), edgeMass A u S.front ab.1 ab.2)) ++
      [(none, 1 - (pairs.map (fun ab => edgeMass A u S.front ab.1 ab.2)).sum)]

/-- Fresh draws at each node of the adaptive probability tree, never an edge-indexed tape. -/
noncomputable def randomRetrievalLaw (A : InnerInput) :
    ℕ → RetrievalState → List (Option RetrievalState × ℝ)
  | 0, S => [(if S.front = A.I.source ∧ S.i < tickLimit A ∧ S.j < tickLimit A then some S else none, 1)]
  | fuel + 1, S =>
    if S.front = A.I.source ∧ S.i < tickLimit A ∧ S.j < tickLimit A then [(some S, 1)] else
      (randomStepLaw A S).flatMap (fun ow => match ow.1 with
        | none => [(none, ow.2)]
        | some S' => (randomRetrievalLaw A fuel S').map (fun ow' => (ow'.1, ow.2 * ow'.2)))

end NearLinearRSP.TwoResources


