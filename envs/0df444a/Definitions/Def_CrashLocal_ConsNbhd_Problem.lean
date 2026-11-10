-- Prove2me | Definitions.Def_CrashLocal_ConsNbhd_Problem
-- name    : CrashLocal_ConsNbhd_Problem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:59:11.765652+00:00
-- url     : https://prove2.me/theorems/c261ccab-6940-43b7-ab24-adf1b7dfb576
-- title:
--   The consistent neighborhoods problem Π_CN(R) and solving it in T rounds
-- statement:
--   Definition 3 and the correctness notion of §3.2. CNOutputs G id lab R S faultFree out holds when (Termination and radius) every v ∈ S outputs a view H_v that represents a labeled subgraph K of G with v ∈ V(K) ⊆ B_G(v, R), the center carrying v's identifier; (Edge validity) for adjacent u, v ∈ S both H_u and H_v contain the edge {id u, id v}; (Consistency) for adjacent u, v ∈ S, H_u[S_u(v)] = H_v[S_v(u)] as labeled graphs, where S_u(v) = B_{H_u}(u, R−1) ∪ B_{H_u}(v, R−1) and S_v(u) = B_{H_v}(u, R−1) ∪ B_{H_v}(v, R−1) are computed inside the views; (Fault-free completeness) if no node crashes, every node v outputs H_v = G[B_G(v, R)]. SolvesCNWithin G id lab P R T admissible: for every admissible adversary, including crashes after T, each surviving node produces its first output at some round t ≤ T, and these first outputs satisfy CNOutputs with S the nodes that never crash; this is 'P solves Π_CN(R) on G in T rounds' (admissible = all adversaries for 'any number of crashes', crashCount ≤ f for a known crash bound f).
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, §3.2 and Definitions 2–3, pp. 14, 17–18

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Model

noncomputable section
open Classical

namespace CrashLocal.ConsNbhd

variable {V L : Type}

/-- The four properties of Definition 3 for the outputs `out` of the surviving set `S`
(`faultFree`: no node crashed). Termination and radius; edge validity; consistency on the
comparison sets of Definition 2; fault-free completeness. -/
def CNOutputs (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (R : ℕ) (S : Set V)
    (faultFree : Prop) (out : V → Option (View L)) : Prop :=
  (∀ v ∈ S, ∃ H, out v = some H ∧
      ∃ K : G.Subgraph, Represents id lab H K ∧ v ∈ K.verts ∧ K.verts ⊆ gBall G v R) ∧
  (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → ∀ Hu Hv, out u = some Hu → out v = some Hv →
      s(id u, id v) ∈ Hu.edges ∧ s(id u, id v) ∈ Hv.edges) ∧
  (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → ∀ Hu Hv, out u = some Hu → out v = some Hv →
      View.LabEq (Hu.induce (Hu.compSet R (id u) (id v)))
        (Hv.induce (Hv.compSet R (id u) (id v)))) ∧
  (faultFree → ∀ v, ∃ H, out v = some H ∧
      Represents id lab H ((⊤ : G.Subgraph).induce (gBall G v R)))

/-- The program `P` solves `Π_CN(R)` on `G` (identifiers `id`, labels `lab`) within `T` rounds:
in every admissible execution, every surviving node produces its first output by round `T`,
and these outputs satisfy Definition 3. Crash times are unrestricted, including after `T`.
The first non-`none` output is the node's reported result; later state observations do not
replace that result. Crashed nodes have no output requirement. -/
def SolvesCNWithin (G : SimpleGraph V) (id : V → ℕ) (lab : V → L)
    (P : NodeProgram L (View L)) (R T : ℕ) (admissible : Adversary V → Prop) : Prop :=
  ∀ adv : Adversary V, admissible adv → ∃ out : V → Option (View L),
    (∀ v ∈ adv.survivors, ∃ t ≤ T, outputAt G id lab P adv t v = out v ∧
      ∀ s < t, outputAt G id lab P adv s v = none) ∧
    CNOutputs G id lab R adv.survivors (∀ v, adv.crashTime v = none) out

end CrashLocal.ConsNbhd


