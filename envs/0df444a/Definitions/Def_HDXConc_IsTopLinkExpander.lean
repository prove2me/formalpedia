-- Prove2me | Definitions.Def_HDXConc_IsTopLinkExpander
-- name    : HDXConc_IsTopLinkExpander
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:10.171206+00:00
-- url     : https://prove2.me/theorems/7a99f178-c7eb-418a-8e98-a67c7c1aea79
-- title:
--   $\lambda$-top-link expander
-- statement:
--   Let $X$ be a pure $d$-dimensional complex with top density $\pi_d$. The complex is a **$\lambda$-top-link expander** if
--
--   1. for every face $s$ with $d-2$ vertices, the underlying graph of the link $X_s$, with the weights induced by $\pi_d$, has second walk eigenvalue at most $\lambda$; and
--   2. for every face $s$ with at most $d-2$ vertices, including $s=\emptyset$, the underlying graph of $X_s$ is connected.
--
--   This is the only spectral hypothesis of the mission's main theorem. It is much weaker than asking for expansion of every link.
--
--   **Formalization Note.** Definition 2.4 asks connectivity of "every link (including the whole complex)". The links of $(d-1)$-faces are edgeless, so that literal reading would exclude the complete complex and the paper's own example on p.18. Footnote 2 of p.3 and the only use of connectivity (Theorem 2.3) concern the links stated above, which is also the weaker hypothesis. The range $\lambda\in[0,1)$ of Definition 2.4 is not part of the predicate, and the main theorem's value lies in it.
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), Definition 2.4, p.13; footnote 2, p.3

import Mathlib
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_HDXConc_SecondEigLE

namespace HDXConc

/-!
# Top-link expanders

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission
(manuscript sha256 ea5bee5f…), Definition 2.4, p.13.

**Formalization Note.** Definition 2.4 asks that "the underlying graph of every link (including the whole complex)
is connected". Read over every face this would include the `(d-1)`-faces, whose links are edgeless, and so exclude
the complete complex and the paper's own example of p.18. Footnote 2 of p.3 and the only use (Theorem 2.3) concern
the links of faces with at most `d - 2` vertices, including `∅`. `LinksConnected` asks exactly that. It is the
weaker hypothesis, so the theorems using it are the stronger ones. The range `λ ∈ [0, 1)` of Definition 2.4 is not
part of the predicate; Theorem 1.1's `λ = (1 - η) / (d - 1)` lies in it for `η ∈ (0, 1]` and `d ≥ 2`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The underlying graph of the link of `s`: its vertices are `X_s(1)`, and distinct `u, v` are adjacent when
`s ∪ {u, v} ∈ X`. -/
def linkGraph (X : Finset (Finset V)) (s : Finset V) : SimpleGraph {v // v ∈ linkVerts X s} where
  Adj u v := (u : V) ≠ (v : V) ∧ s ∪ {(u : V), (v : V)} ∈ X
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- The underlying graph of the link of every face with at most `d - 2` vertices, including `∅`, is connected. -/
def LinksConnected (X : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ s ∈ X, s.card + 2 ≤ d → (linkGraph X s).Connected

/-- `X` is a `lam`-top-link expander (Definition 2.4, p.13): the link of every `s ∈ X(d - 2)` has second walk
eigenvalue at most `lam`, and links are connected. -/
structure IsTopLinkExpander (X : Finset (Finset V)) (d : ℕ) (π : Finset V → ℝ) (lam : ℝ) : Prop where
  /-- `λ(X_s) ≤ lam` for every `s ∈ X(d - 2)`. -/
  link_le : ∀ s ∈ X, s.card + 2 = d → SecondEigLE (linkVerts X s) (linkWeight X d π s) lam
  /-- The links of the faces with at most `d - 2` vertices are connected. -/
  connected : LinksConnected X d

end HDXConc


