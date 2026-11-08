-- Prove2me | Definitions.Def_BipColorHard_PhaseLabeling
-- name    : BipColorHard_PhaseLabeling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:44.557861+00:00
-- url     : https://prove2.me/theorems/72db8746-cd3b-4cf1-b226-f4632cc494f4
-- title:
--   Bipartite phase labeling: labels $\Omega$, weight $W_u$, the partition function $Z_{W_u}$, and instances
-- statement:
--   Fix $q=2k+1$ and let $\Omega=\binom{[q]}{k}$ be the set of $k$-element subsets of the colors. An instance of **bipartite phase labeling** (Definition 7) is a bipartite multigraph $H$. Each vertex carries a label in $\Omega$, and an edge whose endpoints have labels $S,T$ contributes
--   $$W_u(S,T)=1-u|S\cap T|.$$
--   The partition function is
--   $$Z_{W_u}(H)=\sum_{\sigma:V(H)\to\Omega}\ \prod_{\{v,w\}\in E(H)}W_u(\sigma(v),\sigma(w)),$$
--   where $E(H)$ is a multiset, and degrees count edge multiplicities.
--
--   The model is the intermediate problem between gap MAX-CUT and coloring counting: Proposition 8 reduces the former to it and Proposition 9 reduces it to the latter.
--
--   **Formalization Note** An instance is the number of left vertices, the number of right vertices, and a list of edges, parallel edges being repeated entries. The two sizes are encoded in **unary**. With binary sizes a short string could name exponentially many isolated vertices, and the coloring graph, with one gadget per vertex, could not be written in polynomial time, which would make Proposition 9 false. The partition function is also defined for multisets of edges on arbitrary finite vertex types, which is how $H_F$ uses it.
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Definition 7, (11), (12), p.7 (PDF p.9); §3, p.6 (PDF p.8)

import Definitions.Def_NSWApxHard_Reduction_Welfare

set_option autoImplicit false

namespace BipColorHard

/-- `Ω = ([q] choose k)`: the `k`-element subsets of the colour set `[q]`, `q = 2k + 1`. Galanis, Guo,
He, Štefankovič, Vigoda, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), §3, p.6 (PDF p.8). -/
abbrev Omega (k : ℕ) : Type := {S : Finset (Fin (2 * k + 1)) // S.card = k}

/-- The interaction `W_u(S, T) = 1 - u |S ∩ T|`, (11), Definition 7, p.7 (PDF p.9). -/
noncomputable def W (k : ℕ) (u : ℝ) (S T : Omega k) : ℝ :=
  1 - u * ((S.1 ∩ T.1).card : ℝ)

/-- The partition function (12), Definition 7, p.7 (PDF p.9), of a bipartite multigraph with left
vertices `A`, right vertices `B` and the multiset of edges `E`: the sum over all labelings of the
product over `E` (with multiplicity) of `W_u`. -/
noncomputable def multiZ (k : ℕ) (u : ℝ) {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (E : Multiset (A × B)) : ℝ :=
  ∑ σA : A → Omega k, ∑ σB : B → Omega k, (E.map fun e => W k u (σA e.1) (σB e.2)).prod

/-- Maximum degree at most `D`, the degree of a vertex counting edge multiplicities (Definition 7,
p.7 (PDF p.9)). -/
def MultiDegLe {A B : Type} [DecidableEq A] [DecidableEq B] (E : Multiset (A × B)) (D : ℕ) : Prop :=
  (∀ x : A, (E.filter fun e => e.1 = x).card ≤ D) ∧ ∀ y : B, (E.filter fun e => e.2 = y).card ≤ D

/-- An instance of bipartite phase labeling (Definition 7, p.7 (PDF p.9)): a bipartite multigraph with
`nL` left and `nR` right vertices.

**Formalization Note.** `edges` is a list, so parallel edges are repeated entries. -/
structure PhaseInst where
  nL : ℕ
  nR : ℕ
  edges : List (Fin nL × Fin nR)

/-- The encoding of a phase labeling instance.

**Formalization Note.** `nL` and `nR` are in **unary**. This is what the reductions need: with binary
sizes a short string would name an instance with exponentially many isolated vertices, and the
colouring graph of Proposition 9, one gadget per vertex, could not be written in polynomial time.
Edges follow, each endpoint by the self-delimiting `natBits`. -/
def encPhase (H : PhaseInst) : List Bool :=
  List.replicate H.nL true ++ false :: (List.replicate H.nR true ++ false ::
    H.edges.flatMap fun e =>
      NSWApxHard.Reduction.natBits e.1 ++ NSWApxHard.Reduction.natBits e.2)

/-- `Z_{W_u}(H)`, (12), Definition 7, p.7 (PDF p.9). -/
noncomputable def phaseZ (k : ℕ) (u : ℝ) (H : PhaseInst) : ℝ :=
  multiZ k u (H.edges : Multiset (Fin H.nL × Fin H.nR))

/-- The instance has maximum degree at most `D`, counting multiplicities. -/
def PhaseInst.DegLe (H : PhaseInst) (D : ℕ) : Prop :=
  MultiDegLe (H.edges : Multiset (Fin H.nL × Fin H.nR)) D

end BipColorHard


