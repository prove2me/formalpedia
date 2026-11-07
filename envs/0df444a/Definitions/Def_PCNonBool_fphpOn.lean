-- Prove2me | Definitions.Def_PCNonBool_fphpOn
-- name    : PCNonBool_fphpOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:34.833337+00:00
-- url     : https://prove2.me/theorems/17e73474-0513-4aa6-80ef-e49f726225cb
-- title:
--   Functional pigeonhole axioms FPHP$(G[U_a\sqcup V_a])$ in the $\pm1$ encoding
-- statement:
--   Let $G=(U\sqcup V,E)$ be a bipartite graph and $U_a\subseteq U$, $V_a\subseteq V$. The **graph functional pigeonhole principle** on the induced subgraph $G[U_a\sqcup V_a]$, in the $\pm1$ encoding, consists of the polynomials (writing $N_a(i)=N(i)\cap V_a$)
--
--   1. (33a) $x_{i,j}^2-1$ for $i\in U_a$, $j\in N_a(i)$ (range axioms);
--   2. (33b) $\prod_{j\in N_a(i)}(x_{i,j}+1)$ for $i\in U_a$ (every pigeon flies to some hole);
--   3. (33c) $(x_{i,j}-1)(x_{i',j}-1)$ for $i\ne i'\in U_a$, $j\in N_a(i)\cap N_a(i')$ (no two pigeons share a hole);
--   4. (33d) $(x_{i,j}-1)(x_{i,j'}-1)$ for $i\in U_a$, $j\ne j'\in N_a(i)$ (no pigeon flies to two holes).
--
--   Here $x_{i,j}=-1$ if and only if pigeon $i$ flies to hole $j$. The axioms have a common root if and only if $G[U_a\sqcup V_a]$ has a matching covering $U_a$.
--
--   **Formalization Note** The polynomials live in the ring of all edge variables of $G$; Algorithm 1's shrinking instances FPHP$(G_\ell)$ are these sets with $U_a=U_\ell$, $V_a=V_\ell$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5, (33a)–(33d), p.25 (PDF p.28)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_xv

namespace PCNonBool

/-- The axioms (33a)–(33d) of the graph functional pigeonhole principle on the induced subgraph
`G[Ua ⊔ Va]`, in the `±1` encoding where `x_{i,j} = -1` means "pigeon `i` flies to hole `j`"
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5, (33a)–(33d), p.25 (PDF p.28)):

* (33a) `x_{i,j}² - 1` for `i ∈ Ua`, `j ∈ N(i) ∩ Va` (range axioms);
* (33b) `∏_{j ∈ N(i) ∩ Va} (x_{i,j} + 1)` for `i ∈ Ua` (pigeon `i` flies somewhere);
* (33c) `(x_{i,j} - 1)(x_{i',j} - 1)` for `i ≠ i' ∈ Ua`, `j ∈ N(i) ∩ N(i') ∩ Va`;
* (33d) `(x_{i,j} - 1)(x_{i,j'} - 1)` for `i ∈ Ua`, `j ≠ j' ∈ N(i) ∩ Va` (functionality).

**Formalization Note** The polynomials live in the ring of all edge variables of `G`; the edges
outside `G[Ua ⊔ Va]` carry no axiom. Algorithm 1's instances `FPHP(G_ℓ)` are `fphpOn G U_ℓ V_ℓ`.
The empty product in (33b) is `1`. -/
def fphpOn {F : Type*} [Field F] {U V : Type*} (G : BipGraph U V) (Ua : Finset U)
    (Va : Finset V) : Set (MvPolynomial (Var G) F) :=
  {p | (∃ e : Var G, e.1.1 ∈ Ua ∧ e.1.2 ∈ Va ∧ p = MvPolynomial.X e ^ 2 - 1) ∨
       (∃ i ∈ Ua, p = ∏ j ∈ nbrOn G Va i, (xv G i j + 1)) ∨
       (∃ i ∈ Ua, ∃ i' ∈ Ua, i ≠ i' ∧ ∃ j ∈ nbrOn G Va i, j ∈ nbrOn G Va i' ∧
          p = (xv G i j - 1) * (xv G i' j - 1)) ∨
       (∃ i ∈ Ua, ∃ j ∈ nbrOn G Va i, ∃ j' ∈ nbrOn G Va i, j ≠ j' ∧
          p = (xv G i j - 1) * (xv G i j' - 1))}

end PCNonBool


