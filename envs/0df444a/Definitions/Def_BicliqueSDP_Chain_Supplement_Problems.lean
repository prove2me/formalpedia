-- Prove2me | Definitions.Def_BicliqueSDP_Chain_Supplement_Problems
-- name    : BicliqueSDP_Chain_Supplement_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:14:44.615857+00:00
-- url     : https://prove2.me/theorems/e5781a6e-5a72-4511-a19a-eaf9f9f3dc8a
-- title:
--   Problems 1–3 — graph encodings and the three decision languages
-- statement:
--   The three decision problems use the fixed alphabet $\{0,1\}$. A general graph code is $1^n0$ followed by the $n^2$ row-major adjacency bits of a simple graph on $\{0,\ldots,n-1\}$. A bipartite graph code is $1^r0\,1^s0$ followed by its $rs$ cross-edge bits, so both parts are part of the input.
--
--   $$\begin{aligned}
--   \mathrm{HSC}&=\{\langle G\rangle: |V|\text{ even and }G\text{ has a clique of size }|V|/2\},\\
--   \mathrm{HSCE}&=\{\langle G\rangle\in\mathrm{HSC}:4|E|=|V|(|V|-2)\},\\
--   \alpha\text{-}\mathrm{BAL}\text{-}\mathrm{BIP}&=\{\langle E\rangle:\alpha(E)=\alpha_{\mathrm{bal}}(E)\}.
--   \end{aligned}$$
--
--   Strings without a valid encoding, odd-order graphs for the clique languages, and graphs with an incorrect edge count for HSCE are rejected. Clique existence uses $2|S|=|V|$, avoiding truncated division. These are languages, not promise problems.
--
--   The published Cook framework supplies Turing machines, step-count polynomial computation, NP and polynomial-time many-one reductions. Dense adjacency codes with unary size headers are polynomially equivalent to the usual explicit graph encodings; no complexity assertion is built into language membership.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 7, Problems 1–3 and polynomial-time reducibility

import Definitions.Def_BicliqueSDP_Chain_Supplement_Gadget
import Definitions.Def_CookPvsNP_defs
set_option autoImplicit false

namespace BicliqueSDP.Chain.Supplement
noncomputable section

/-- Unary size header followed by a delimiter. -/
def sizeHeader (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Fixed dense graph code: unary n, delimiter, n² row-major adjacency bits.
Only symmetric loopless matrices have a graph preimage. -/
def graphCode {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List Bool :=
  sizeHeader n ++ (List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => decide (G.Adj i j)

/-- A bipartite graph is encoded with BOTH side sizes, then all r*s cross-edge bits. -/
def bipCode {r s : ℕ} (E : Fin r → Fin s → Prop) [DecidableRel E] : List Bool :=
  sizeHeader r ++ sizeHeader s ++ (List.finRange r).flatMap fun i =>
    (List.finRange s).map fun j => decide (E i j)

/-- Exact half-size clique predicate. No truncated division is used. -/
def HasHalfClique {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ S : Finset V, G.IsClique (S : Set V) ∧ 2 * S.card = Fintype.card V

/-- HALF-SIZE-CLIQUE, with odd-size and malformed strings rejected. -/
def halfSizeClique : CookPvsNP.Lang Bool :=
  {x | ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (d : DecidableRel G.Adj),
    x = @graphCode n G d ∧ Even n ∧ HasHalfClique G}

/-- HALF-SIZE-CLIQUE-EDGE. Evenness makes the natural subtraction exact, including n=0. -/
def halfSizeCliqueEdge : CookPvsNP.Lang Bool :=
  {x | ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (d : DecidableRel G.Adj),
    x = @graphCode n G d ∧ Even n ∧
    4 * Nat.card G.edgeSet = n * (n - 2) ∧
    HasHalfClique G}

/-- α-BAL-BIP, using the immutable base α and α_bal definitions. -/
def alphaBalBip : CookPvsNP.Lang Bool :=
  {x | ∃ (r s : ℕ) (E : Fin r → Fin s → Prop) (d : DecidableRel E),
    x = @bipCode r s E d ∧ @alpha (Fin r) (Fin s) _ _ _ _ E d =
      @alphaBal (Fin r) (Fin s) _ _ _ _ E d}

end
end BicliqueSDP.Chain.Supplement


