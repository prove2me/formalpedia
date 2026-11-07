-- Prove2me | Definitions.Def_MISInducedMinor_maxCut
-- name    : MISInducedMinor_maxCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:29.473758+00:00
-- url     : https://prove2.me/theorems/d153acc9-991e-4207-bf9b-a21b956bedcd
-- title:
--   Cut size and $\mathrm{MaxCut}(F)$
-- statement:
--   Let $F$ be a finite graph. For $A\subseteq V(F)$, the **size of the cut** $(A,V(F)\setminus A)$ is the number of edges of $F$ with exactly one endpoint in $A$. **$\mathrm{MaxCut}(F)$** is the number of edges in a maximum-cardinality cut:
--
--   $$\mathrm{MaxCut}(F)=\max_{A\subseteq V(F)}\bigl|\{uv\in E(F):u\in A,\ v\notin A\}\bigr|.$$
--
--   Max Cut is the problem the paper reduces from, and Lemma 3.2 expresses $\alpha(G_F)$ through $\mathrm{MaxCut}(F)$.
--
--   **Formalization Note** The cut size counts the ordered pairs $(a,b)\in A\times A^{\mathrm c}$ with $ab\in E(F)$, one per cut edge. The maximum is a finite maximum over all $2^{|V(F)|}$ subsets.
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), §2.1, p.5

import Mathlib

set_option autoImplicit false

namespace MISInducedMinor

/-- The **size of the cut** `(A, V ∖ A)` of a finite graph `F`: the number of edges of `F` with
exactly one endpoint in `A`. Each such edge is counted once, as the ordered pair
`(a, b) ∈ A × Aᶜ` with `F.Adj a b`. -/
def cutCount {V : Type*} [Fintype V] [DecidableEq V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (A : Finset V) : ℕ :=
  ((A ×ˢ Aᶜ).filter fun p => F.Adj p.1 p.2).card

/-- `MaxCut(F)`, **the number of edges in a maximum-cardinality cut** of `F`.
arXiv:2609.11285 (sha256 e378b906…), §2.1, p.5.

**Formalization Note.** The maximum over all `2^|V|` vertex subsets `A` of `cutCount F A`, a
finite maximum (`Finset.sup` over `Finset.univ`), so it is attained. -/
def maxCut {V : Type*} [Fintype V] [DecidableEq V] (F : SimpleGraph V) [DecidableRel F.Adj] : ℕ :=
  (Finset.univ : Finset (Finset V)).sup fun A => cutCount F A

end MISInducedMinor


