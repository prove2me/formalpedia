-- Prove2me | Definitions.Def_Max3CutHard_Jnat
-- name    : Max3CutHard_Jnat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:21.427569+00:00
-- url     : https://prove2.me/theorems/d76321e4-d573-4d6a-8d63-a799f5484d0f
-- title:
--   The reduction graph of an encodable instance as an $\mathbb N$-weighted multigraph
-- statement:
--   For an encodable instance $\Phi$ with $m$ listed equations, the graph $J(\Phi)$ built from the family $(2E,N,N)$ has weights $\lambda_e c=c/m$, where $c\in\{1,2,3\}$ is a gadget weight. Multiplying all weights by $m$ gives a multigraph with integer weights; it is written as a loopless multigraph on $\{0,\dots,n-1\}$ in which an edge of weight $c$ is listed $c$ times.
--
--   The vertices are numbered as follows:
--   1. the variables $u\in U$ come first, then the variables $w\in W$;
--   2. then the three globals;
--   3. then the auxiliary vertices of each equation's copy, equation by equation.
--
--   This is the graph to which the main theorem's reduction maps an instance of Håstad's problem.
--
--   **Formalization Note** Every listed pair has distinct endpoints in range, because $w_e\ne w'_e$ and $U$, $W$ and the auxiliary blocks are disjoint; the final `filterMap` only packages the pairs with the published `WMaxCut` loopless proof.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, The reduction, p.5; Proof of Theorem 1.1, p.6

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_Max3CutHard_LinInst
import Definitions.Def_Max3CutHard_family0
open OptInapprox.MaxCut

namespace Max3CutHard

/-- **The reduction graph of an encodable instance, as an ℕ-weighted multigraph.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2,
The reduction, p.5, and Proof of Theorem 1.1, p.6: `J(Φ)` for the family `(2E, N, N)`.

**Formalization Note.** Each equation's copy is taken at the gadget's own integer weights, i.e.
the weights `λ_e · c = c/m` of `J(Φ)` are multiplied by `m`, the number of listed equations; an
edge of weight `c ∈ {1, 2, 3}` is listed `c` times (`⌊c⌋₊`). Vertices are numbered: `u ↦ u`,
`w ↦ nU + w`, global `g ↦ nU + nW + g`, auxiliary `a` of the `i`-th equation ↦
`nU + nW + 3 + (aux counts of the equations before i) + a`. Every resulting pair is in range and
has distinct endpoints (because `w_e ≠ w′_e` and the roles are disjoint); the `filterMap` only
packages this as `Fin n` pairs with the loopless proof. -/
noncomputable def Jnat (Φ : LinInst) : WMaxCut :=
  let m := Φ.eqs.length
  let auxOf : Eqn (Fin Φ.nU) (Fin Φ.nW) → ℕ := fun e => (family0 e.t).aux
  let offset : ℕ → ℕ := fun i => ((Φ.eqs.take i).map auxOf).sum
  let n := Φ.nU + Φ.nW + 3 + (Φ.eqs.map auxOf).sum
  let natEdges : List (ℕ × ℕ) := (List.finRange m).flatMap fun i =>
    let e := Φ.eqs.get i
    let vtx : Fin 3 ⊕ Fin 3 ⊕ Fin (family0 e.t).aux → ℕ :=
      Sum.elim (fun j => ![(e.u : ℕ), Φ.nU + (e.w : ℕ), Φ.nU + (e.w' : ℕ)] j)
        (Sum.elim (fun g => Φ.nU + Φ.nW + (g : ℕ)) fun a => Φ.nU + Φ.nW + 3 + offset i + (a : ℕ))
    (family0 e.t).edges.flatMap fun ed => List.replicate ⌊ed.2⌋₊ (vtx ed.1.1, vtx ed.1.2)
  { n := n
    edges := natEdges.filterMap fun ab =>
      if h : ab.1 < n ∧ ab.2 < n ∧ ab.1 ≠ ab.2 then some (⟨ab.1, h.1⟩, ⟨ab.2, h.2.1⟩) else none
    loopless := by
      intro e he
      rw [List.mem_filterMap] at he
      obtain ⟨ab, -, hab⟩ := he
      split_ifs at hab with h
      cases hab; exact fun h' => h.2.2 (congrArg Fin.val h') }

end Max3CutHard


