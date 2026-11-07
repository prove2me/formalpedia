-- Prove2me | Definitions.Def_PCNonBool_Step
-- name    : PCNonBool_Step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:35:08.919195+00:00
-- url     : https://prove2.me/theorems/d5491139-1aee-4552-9f83-ce7908b15262
-- title:
--   One round of Algorithm 1 (PigeonDegreeReduction)
-- statement:
--   One round $\ell$ of **Algorithm 1** (PigeonDegreeReduction$(\pi,G,D)$) transforms the state $(\pi_{\ell-1},U_{\ell-1},V_{\ell-1},C_{\ell-1})$ into $(\pi_\ell,U_\ell,V_\ell,C_\ell)$ as follows.
--
--   1. (line 10) Choose a pigeon $i\in U_{\ell-1}$ and holes $j\ne j'\in N_{G_{\ell-1}}(i)$ such that $(x_{i,j},x_{i,j'})$ touches the largest number of pairs in $\mathrm{PPHigh}_D(\pi_{\ell-1})$, pairwise pigeon degree taken in $G_{\ell-1}$.
--   2. (lines 11, 15–17) $\pi'_\ell=\mathrm{PigeonSplit}_{i,j,j'}(\pi_{\ell-1})$, $U'_\ell=U_{\ell-1}\setminus\{i\}$, $V'_\ell=V_{\ell-1}\setminus\{j,j'\}$, $G'_\ell=G[U'_\ell\sqcup V'_\ell]$.
--   3. (line 20) $S_\ell$ is a maximal set in $U'_\ell$ with $|S_\ell|\le s$ and $|\partial_{G'_\ell}S_\ell|\le(c-1)|S_\ell|$.
--   4. (line 21) $M_\ell$ is a matching of $S_\ell$ in $G'_\ell$.
--   5. (lines 12–14, 21–25) $\pi_\ell=\pi'_\ell\restriction\rho_\ell$, $U_\ell=U'_\ell\setminus S_\ell$, $V_\ell=V'_\ell\setminus M_\ell(S_\ell)$, $C_\ell=C_{\ell-1}\cup S_\ell$.
--
--   **Formalization Note** The round is a relation: all ties and choices are arbitrary and results hold for every run. "Maximal" is inclusion-maximal. The FAIL test (lines 18–19) is not part of the round; the proof of Theorem 5.1 shows it never fires.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Algorithm 1 (PigeonDegreeReduction), p.30 (PDF p.33)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_boundaryOn
import Definitions.Def_PCNonBool_touchSetOn
import Definitions.Def_PCNonBool_restrict
import Definitions.Def_PCNonBool_splitSeq
import Definitions.Def_PCNonBool_AlgState
import Definitions.Def_PCNonBool_stepAssignment

namespace PCNonBool

/-- One round `ℓ` of Algorithm 1, PigeonDegreeReduction(π, G, D)
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.30 (PDF p.33)), as a relation between the state after round `ℓ - 1` and after
round `ℓ`:

* line 10: a pigeon `i ∈ U_{ℓ-1}` and holes `j ≠ j'` of `i` in `V_{ℓ-1}` such that
  `(x_{i,j}, x_{i,j'})` touches the most pairs of `PPHigh_D(π_{ℓ-1})` (in `G_{ℓ-1}`);
* lines 11, 15–17: `π'_ℓ = PigeonSplit_{i,j,j'}(π_{ℓ-1})`, `U'_ℓ = U_{ℓ-1} \ {i}`,
  `V'_ℓ = V_{ℓ-1} \ {j, j'}`;
* line 20: `S_ℓ` an inclusion-maximal set in `U'_ℓ` with `|S_ℓ| ≤ s` and
  `|∂_{G'_ℓ} S_ℓ| ≤ (c - 1)|S_ℓ|`;
* line 21: a matching `M_ℓ` of `S_ℓ` into `V'_ℓ` along edges;
* lines 12–14, 21–25: `π_ℓ = π'_ℓ↾ρ_ℓ` (`stepAssignment`), `U_ℓ = U'_ℓ \ S_ℓ`,
  `V_ℓ = V'_ℓ \ M_ℓ(S_ℓ)`, and `C_ℓ = C_{ℓ-1} ∪ S_ℓ`.

**Formalization Note** The algorithm is a relation, not a function: ties at line 10 and the
choices of `S_ℓ` and `M_ℓ` are arbitrary, and statements quantify over every run. "Maximal" at
line 20 is read as inclusion-maximal (every cardinality-maximal set is inclusion-maximal; the
proof of Proposition 5.12 uses only that no proper superset qualifies). The FAIL test of lines
18–19 is not part of the step (it never fires, as the proof of Theorem 5.1 shows); the header's
size assumption on `π` is not part of the algorithm's operation. -/
def Step {F : Type*} [Field F] {U V : Type*} [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (s : ℕ) (c D : ℝ) (st st' : AlgState (F := F) G) : Prop :=
  ∃ (i : U) (j j' : V), i ∈ st.Ua ∧ j ∈ nbrOn G st.Va i ∧ j' ∈ nbrOn G st.Va i ∧ j ≠ j' ∧
    (∀ (i₀ : U) (j₀ j₀' : V), i₀ ∈ st.Ua → j₀ ∈ nbrOn G st.Va i₀ → j₀' ∈ nbrOn G st.Va i₀ →
      j₀ ≠ j₀' → (touchSetOn G st.Ua st.Va D i₀ j₀ j₀' st.π).card ≤
        (touchSetOn G st.Ua st.Va D i j j' st.π).card) ∧
    ∃ (S : Finset U) (M : U → V),
      S ⊆ st.Ua.erase i ∧ S.card ≤ s ∧
      ((boundaryOn G (st.Va \ {j, j'}) S).card : ℝ) ≤ (c - 1) * S.card ∧
      (∀ S' : Finset U, S ⊂ S' → S' ⊆ st.Ua.erase i → S'.card ≤ s →
        (c - 1) * (S'.card : ℝ) < (boundaryOn G (st.Va \ {j, j'}) S').card) ∧
      Set.InjOn M S ∧ (∀ u ∈ S, M u ∈ st.Va \ {j, j'} ∧ G.Adj u (M u)) ∧
      st'.π = (splitSeq G i j j' st.π).map
        (restrict (stepAssignment G st.Ua st.Va i j j' S M)) ∧
      st'.Ua = st.Ua.erase i \ S ∧ st'.Va = (st.Va \ {j, j'}) \ S.image M ∧
      st'.C = st.C ∪ S

end PCNonBool


