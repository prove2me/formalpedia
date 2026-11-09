-- Prove2me | Definitions.Def_WeldedPath_Nb
-- name    : WeldedPath_Nb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:04:05.834282+00:00
-- url     : https://prove2.me/theorems/1b66d8e2-72d4-472b-8387-0459e2595a8d
-- title:
--   Color-preserving edge permutations and the neighbor function $\mathrm{Nb}_{\sigma_{\mathrm{edge}}}$
-- statement:
--   The edge randomness is $\sigma_{\mathrm{edge}}=\prod_{b\in B_{\mathrm{edge}}}\sigma_b$ with $\sigma_b$ a permutation of the class $E_b$. Given it, the **neighbor function** of a structural index $v$ in direction $\alpha$, with $e=e_\alpha(v)$, is
--   $$
--   \mathrm{Nb}_{\sigma_{\mathrm{edge}}}(v,\alpha)=\begin{cases} v & v\notin V_n \text{ or } e=\bot,\\ \mathrm{head}(e) & e\neq\bot,\ b_{\mathrm{edge}}(e)=\bot,\ v=\mathrm{tail}(e),\\ \mathrm{tail}(e) & e\neq\bot,\ b_{\mathrm{edge}}(e)=\bot,\ v=\mathrm{head}(e),\\ \mathrm{head}(\sigma_{b_{\mathrm{edge}}(e)}(e)) & b_{\mathrm{edge}}(e)\neq\bot,\ v=\mathrm{tail}(e),\\ \mathrm{tail}(\sigma^{-1}_{b_{\mathrm{edge}}(e)}(e)) & b_{\mathrm{edge}}(e)\neq\bot,\ v=\mathrm{head}(e).\end{cases}
--   $$
--   Permuting the edges of a class rewires the middle columns and the weld while keeping every vertex in its column and every parent color.
--
--   **Formalization Note** $\sigma_{\mathrm{edge}}$ is encoded as one permutation of $E_n$ that maps each class $E_b$ onto itself and fixes every edge with $b_{\mathrm{edge}}(e)=\bot$; restriction to the classes is a bijection onto $\prod_b \mathrm{Sym}(E_b)$.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), p.16, (23), and p.17, (25)

import Mathlib
import Definitions.Def_WeldedPath_bEdge

namespace WeldedPath

namespace WeldedInstance

variable {n : ℕ}

/-- `π` is a color-preserving edge permutation with support in the middle columns and the weld,
i.e. an element `σ_edge = ∏_{b ∈ B_edge} σ_b` of `S_edge = ∏_{b ∈ B_edge} S_b` (arXiv:2611.05912
(sha256 b31400a0…), (23) and p.16).

**Formalization Note.** `σ_edge` is encoded as one permutation of the edge set `E_n` that maps
every class `E_b` onto itself and fixes every edge with `b_edge(e) = ⊥`. Restriction to the
classes is a bijection from these permutations onto `∏_b Sym(E_b)`, so the uniform distribution
on them is the product distribution of p.16. -/
def IsEdgePerm (l : ℕ) (G : WeldedInstance n) (π : Equiv.Perm G.edges) : Prop :=
  ∀ e : G.edges, G.bEdge l (π e).1 = G.bEdge l e.1 ∧ (G.bEdge l e.1 = none → π e = e)

/-- The neighbor function `Nb_{σ_edge}(v, α)` (25) (arXiv:2611.05912 (sha256 b31400a0…), p.17),
with `e = e_α(v)`:
`v` if `v ∉ V_n` or `e = ⊥`; `head(e)` / `tail(e)` if `b_edge(e) = ⊥` and `v = tail(e)` /
`v = head(e)`; `head(σ_b(e))` if `b = b_edge(e) ≠ ⊥` and `v = tail(e)`; `tail(σ_b^{-1}(e))` if
`b_edge(e) ≠ ⊥` and `v = head(e)`.

**Formalization Note.** `σ_b` is the restriction of the edge permutation `π` to `E_b`
(`IsEdgePerm`). The final fallback `v` (an edge of `e_α(v)` that is not incident to `v`, or not an
edge of the instance) never occurs. -/
noncomputable def Nb (l : ℕ) (G : WeldedInstance n) (π : Equiv.Perm G.edges) (v : ℕ)
    (α : Fin 3) : ℕ :=
  if ¬ IsVertex n v then v
  else
    match G.eAlpha v α with
    | none => v
    | some e =>
      if he : e ∈ G.edges then
        if G.bEdge l e = none then
          (if v = e.tail then e.head n else if v = e.head n then e.tail else v)
        else
          (if v = e.tail then (π ⟨e, he⟩).1.head n
            else if v = e.head n then (π.symm ⟨e, he⟩).1.tail else v)
      else v

end WeldedInstance

end WeldedPath


