-- Prove2me | Definitions.Def_SemAC02_Supplement_fphpG
-- name    : SemAC02_Supplement_fphpG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:44:29.196847+00:00
-- url     : https://prove2.me/theorems/9af8b6ee-e560-4d35-b8ac-2184926b3d9b
-- title:
--   The graph functional pigeonhole principle FPHP(G) and G + M
-- statement:
--   For a bipartite graph $G=(L\sqcup R,E)$ of pigeons and holes, $\mathrm{FPHP}(G)$ over $\mathbb F_2$ has a variable $x_{u,v}$ for every edge and the axioms
--
--   1. pigeon axioms $P_u=\prod_{v\in N_G(u)}(1+x_{u,v})$, $u\in L$;
--   2. functionality axioms $x_{u,v}x_{u,v'}$, $v\neq v'$;
--   3. hole axioms $x_{u,v}x_{u',v}$, $u\neq u'$;
--
--   quadratic axioms only when both edges are in $E$. $\mathrm{FPHP}^m_n=\mathrm{FPHP}(K_{m,n})$. For a matching $M$ covering all holes, $G+M=(L\sqcup R,E\cup M)$.
--
--   Theorems 6.12 and 6.18 concern these systems.
--
--   **Formalization Note** Graphs are the published `PCNonBool.BipGraph`. The matching is $\{(\mu(v),v)\}$ for an injective $\mu:R\to L$.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Definition 6.6, p.43 (PDF p.45); §6.2, pp.43–44 (PDF pp.45–46)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn

namespace SemAC02.Supplement

open MvPolynomial

/-- The edges of a bipartite graph, the variables `x_{u,v}`, `(u, v) ∈ E`, of the graph pigeonhole
principles (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong
Semantic Proof Systems*, manuscript (STOC 2027 submission), Definition 6.6, p.43 and §7.2, p.52). -/
abbrev Edge {L R : Type} (G : PCNonBool.BipGraph L R) : Type := {e : L × R // G.Adj e.1 e.2}

/-- The variable `x_{u,v}` of an edge as a polynomial over `𝔽₂`. -/
noncomputable def xE {L R : Type} (G : PCNonBool.BipGraph L R) (u : L) (v : R)
    (h : G.Adj u v) : MvPolynomial (Edge G) (ZMod 2) :=
  X ⟨(u, v), h⟩

/-- The **graph functional pigeonhole principle** `FPHP(G)` over `𝔽₂` (Definition 6.6, p.43): the
variables `x_{u,v}` for `(u, v) ∈ E`, and the axioms

* (15) pigeon axioms `P_u = ∏_{v ∈ N_G(u)} (1 + x_{u,v})`, `u ∈ L`;
* (16) functionality axioms `x_{u,v} x_{u,v'}`, `v ≠ v'`, both edges in `E`;
* (17) hole axioms `x_{u,v} x_{u',v}`, `u ≠ u'`, both edges in `E`.

`FPHP^m_n = FPHP(K_{m,n})`. -/
noncomputable def fphpG {L R : Type} [Fintype R] (G : PCNonBool.BipGraph L R) :
    Set (MvPolynomial (Edge G) (ZMod 2)) :=
  {p | (∃ u : L, p = ∏ v ∈ (PCNonBool.nbrOn G Finset.univ u).attach,
          (1 + xE G u v.1 (by simpa [PCNonBool.nbrOn] using v.2))) ∨
       (∃ (u : L) (v v' : R) (h : G.Adj u v) (h' : G.Adj u v'), v ≠ v' ∧
          p = xE G u v h * xE G u v' h') ∨
       (∃ (u u' : L) (v : R) (h : G.Adj u v) (h' : G.Adj u' v), u ≠ u' ∧
          p = xE G u v h * xE G u' v h')}

/-- The graph `G + M = (L ⊔ R, E ∪ M)` for the matching `M = {(μ v, v) : v ∈ R}` covering all
holes (§6.2, p.43–44); `μ` injective means that `M` is a matching. -/
def addMatching {L R : Type} [DecidableEq L] (G : PCNonBool.BipGraph L R) (μ : R → L) :
    PCNonBool.BipGraph L R :=
  { Adj := fun u v => G.Adj u v ∨ μ v = u }

/-- The complete bipartite graph `K_{m,n}` on `[m] ⊔ [n]`. -/
def completeBip (m n : ℕ) : PCNonBool.BipGraph (Fin m) (Fin n) :=
  { Adj := fun _ _ => True }

end SemAC02.Supplement


