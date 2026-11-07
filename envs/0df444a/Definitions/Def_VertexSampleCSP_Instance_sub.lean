-- Prove2me | Definitions.Def_VertexSampleCSP_Instance_sub
-- name    : VertexSampleCSP_Instance_sub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:35.022335+00:00
-- url     : https://prove2.me/theorems/ac94adf3-f401-4730-8639-cd9f52d8c624
-- title:
--   Subinstance $\mathcal I[S]$ on the variables of $S$
-- statement:
--   For $S\subseteq V$, the **subinstance** $\mathcal I[S]$ is the instance whose variables are the elements of $S$ and whose tables are the tables $f_e$ of $\mathcal I$ with $e\subseteq S$. If $|S|<r$ it has no tables and value $0$.
--
--   The estimator of the mission solves $\mathcal I[S]$ for a random $S$ and rescales its optimum.
--
--   **Formalization Note** The subinstance lives on the subtype $\uparrow S$, so it has exactly $|S|$ variables. Setting the tables outside $S$ to zero while keeping all of $V$ would change the factor $N^{(r-2)/2}$ of Proposition C.2, whose $N$ is the number of variables of the instance it is applied to.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "Instances", p.13 (PDF p.15); §1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance

namespace VertexSampleCSP

/-- A point of the image of a subset `e'` of `↥S` in `V` lies in `S`. -/
theorem mem_of_mem_map_subtype {V : Type*} {S : Finset V} {e' : Finset S} {x : V}
    (hx : x ∈ e'.map (Function.Embedding.subtype (· ∈ S))) : x ∈ S := by
  obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
  exact y.2

/-- A point of the image of a subset `e'` of `↥S` in `V` comes from `e'`. -/
theorem mk_mem_of_mem_map_subtype {V : Type*} {S : Finset V} {e' : Finset S} {x : V}
    (hx : x ∈ e'.map (Function.Embedding.subtype (· ∈ S))) :
    (⟨x, mem_of_mem_map_subtype hx⟩ : S) ∈ e' := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
  simpa using hy

/-- **Subinstance `I[S]`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction Problems*,
STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "Instances", p.13 (PDF p.15): "For
S ⊆ V, I[S] is the instance on S with the tables fe, e ⊆ S; if |S| < r it has no tables and value 0."
Also §1.1, p.2: "the subinstance I[S] keeps the tables fe with e ⊆ S".

`I.sub S` is an instance whose variables are the elements of `S` (the subtype `↥S`, with `|S|`
variables). The table of a subset `e'` of `↥S` is the table of `I` on the image of `e'` in `V`, read
through the identification of that image with `e'`.

**Formalization Note.** The subinstance lives on the subtype `↥S`, not on `V` with the tables outside
`S` set to zero: Proposition C.2 and Lemma B.3 carry the factor `N^{(r−2)/2}` with `N` the number of
variables of the instance, and the proof of Theorem C.4 applies them to `I[S_j]` with `N = |S_j|`. If
`|S| < r` there is no `r`-subset of `↥S`, so `I.sub S` has no tables and every assignment has value
`0`. -/
noncomputable def Instance.sub {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (S : Finset V) : Instance S r q where
  f e' a := I.f (e'.map (Function.Embedding.subtype (· ∈ S)))
    (fun x => a ⟨⟨x.1, mem_of_mem_map_subtype x.2⟩, mk_mem_of_mem_map_subtype x.2⟩)

end VertexSampleCSP


