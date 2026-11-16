-- Prove2me | Definitions.Def_SemAC02_Supplement_phpG
-- name    : SemAC02_Supplement_phpG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:45:03.876395+00:00
-- url     : https://prove2.me/theorems/f20529eb-7488-4dc0-b7ae-04587a03743e
-- title:
--   The graph pigeonhole principle PHP(G), Lemma 7.4's conclusions, and PHP′(G)
-- statement:
--   For a bipartite graph $G=(L\sqcup R,E)$, $\mathrm{PHP}(G)$ over $\mathbb F_2$ has a variable $x_{u,v}$ per edge, the pigeon axioms $P_u=\prod_{v\in N_G(u)}(1-x_{u,v})$ and the hole axioms $x_{u,v}x_{u',v}$ ($u\neq u'$, $v\in N_G(u)\cap N_G(u')$); there are no functionality axioms, and $\mathrm{PHP}^m_n=\mathrm{PHP}(K_{m,n})$.
--
--   A graph with $2n$ pigeons and $n$ holes **satisfies the conclusions of Lemma 7.4** if, with $\Delta=\lceil 24\ln(2n)\rceil$ and $s=\lfloor n/(4\Delta)\rfloor$, it is an $(s,\Delta/4)$-boundary expander, every pigeon has degree at most $2\Delta$ and every hole degree at most $4\Delta$.
--
--   With $D=4\Delta$, the class of each hole $v$ is padded with auxiliary variables to a class $C_v$ of size $D$; $F_0=\bigcup_v\{xy:x\neq y\in C_v\}$ and
--
--   $$
--   \mathrm{PHP}'(G)=F_0\cup\{P_u:u\in L\}.
--   $$
--
--   These are the systems of Theorems 7.5 and 7.14.
--
--   **Formalization Note** The padded variables are $(v,j)$, $j\in[D]$; an injection places the edge variables of each hole in its class.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §7.2, pp.52–53 (PDF pp.54–55), Lemma 7.4, p.52, (29)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_SemAC02_Supplement_fphpG
import Definitions.Def_SemAC02_Supplement_expansionRank

namespace SemAC02.Supplement

open MvPolynomial

/-- The **graph pigeonhole principle** `PHP(G)` over `𝔽₂` (Alekseev–Gryaznov–Itsykson–Pitassi–
Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027
submission), §7.2, p.52): the variables `x_{u,v}`, `(u, v) ∈ E`, the pigeon axioms
`P_u = ∏_{v ∈ N_G(u)} (1 − x_{u,v})` (`u ∈ L`) and the hole axioms `x_{u,v} x_{u',v}`
(`u ≠ u'`, `v ∈ N_G(u) ∩ N_G(u')`); no functionality axioms. `PHP^m_n = PHP(K_{m,n})`. -/
noncomputable def phpG {L R : Type} [Fintype R] (G : PCNonBool.BipGraph L R) :
    Set (MvPolynomial (Edge G) (ZMod 2)) :=
  {p | (∃ u : L, p = ∏ v ∈ (PCNonBool.nbrOn G Finset.univ u).attach,
          (1 - xE G u v.1 (by simpa [PCNonBool.nbrOn] using v.2))) ∨
       (∃ (u u' : L) (v : R) (h : G.Adj u v) (h' : G.Adj u' v), u ≠ u' ∧
          p = xE G u v h * xE G u' v h')}

/-- `Δ = ⌈24 ln(2n)⌉` (Lemma 7.4, p.52). -/
noncomputable def php74Delta (n : ℕ) : ℕ := ⌈24 * Real.log (2 * (n : ℝ))⌉₊

/-- `G` **satisfies the conclusions of Lemma 7.4** (p.52): `G` has `2n` pigeons and `n` holes, and
with `Δ = ⌈24 ln(2n)⌉` and `s = ⌊n/(4Δ)⌋`, `G` is an `(s, Δ/4)`-boundary expander, every pigeon has
degree at most `2Δ` and every hole has degree at most `4Δ`. -/
def Lemma74Concl {n : ℕ} (G : PCNonBool.BipGraph (Fin (2 * n)) (Fin n)) : Prop :=
  IsBdryExp G (⌊(n : ℝ) / (4 * (php74Delta n : ℝ))⌋₊ : ℝ) ((php74Delta n : ℝ) / 4) ∧
  (∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ 2 * php74Delta n) ∧
  (∀ v, (Finset.univ.filter (fun u => G.Adj u v)).card ≤ 4 * php74Delta n)

/-- The padded system `PHP′(G) = F₀ ∪ {P_u : u ∈ L}` (29), p.52: the edge variables of every hole
`v` are placed, by the injection `ι v`, among `D` variables `(v, j)`, `j ∈ [D]`, forming the class
`C_v` (the other variables of `C_v` are the auxiliary padding variables);
`F₀ = ⋃_v {xy : x ≠ y ∈ C_v}` and `P_u = ∏_{v ∈ N_G(u)} (1 − x_{(v, ι_v(u))})`. -/
noncomputable def phpPadded {L : Type} {n D : ℕ} (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) :
    Set (MvPolynomial (Fin n × Fin D) (ZMod 2)) :=
  {p | (∃ (v : Fin n) (j j' : Fin D), j ≠ j' ∧ p = X (v, j) * X (v, j')) ∨
       (∃ u : L, p = ∏ v ∈ (PCNonBool.nbrOn G Finset.univ u).attach,
          (1 - X (v.1, ι v.1 ⟨u, by simpa [PCNonBool.nbrOn] using v.2⟩)))}

end SemAC02.Supplement


