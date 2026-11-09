-- Prove2me | Definitions.Def_SemAC02_IsGadget
-- name    : SemAC02_IsGadget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:57.383716+00:00
-- url     : https://prove2.me/theorems/d6c7638a-5c53-4c53-9132-db780578abb1
-- title:
--   Gadget conditions of §8.1
-- statement:
--   Fix $d\ge2$. A **gadget** is an AND/OR circuit $g$ on $m$ variables with the following properties.
--
--   1. The depth of $g$ is at most $d+1$.
--   2. $g$ is AND-rooted: $g=\bigwedge_{j\in J}H_{0,j}$ with $J$ nonempty.
--   3. $g$ is antitone: $X\le Y$ coordinatewise implies $g(Y)\le g(X)$.
--   4. $g(X)\wedge g(\overline X)=0$ for every $X\in\{0,1\}^m$.
--
--   With $g_0(X)=g(X)$ and $g_1(X)=g(\overline X)$, property 4 says $g_0$ and $g_1$ are never true together. The gadget replaces the literals of a base CNF in the lifting construction.
--
--   **Formalization Note** The circuit is required to be in the paper's normal form (flattened, no repeated children), so no child of the AND root is an AND gate; the root children are the conjuncts $H_{0,j}$.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §8.1, p.62 (PDF p.64)

import Mathlib
import Definitions.Def_SemAC02_Circ

namespace SemAC02

/-- The **gadget conditions** of §8.1 (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard
Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), §8.1, p.62): for
`d ≥ 2`, an AND/OR circuit `g` on `m` variables such that

1. the depth of `g` is at most `d + 1`;
2. `g` is AND-rooted (with at least one child: `J` is nonempty, p.63);
3. `g` is antitone;
4. `g(X) ∧ g(X̄) = 0` for every `X ∈ {0,1}^m`.

**Formalization Note** `g` is required to be in the paper's normal form (`IsReduced`: flattened,
no repeated children, p.17); in particular no child of the AND root is itself an AND gate, so the
root children are the paper's `H_{0,j}`. `X̄` is `fun j => !X j`; antitone is `Antitone` for the
pointwise order on `Fin m → Bool`. -/
def IsGadget (d : ℕ) {m : ℕ} (g : Circ (Fin m)) : Prop :=
  NoXor g ∧ IsReduced g ∧ g.depth ≤ d + 1 ∧
  (∃ cs : List (Circ (Fin m)), cs ≠ [] ∧ g = Circ.and cs) ∧
  Antitone (fun X : Fin m → Bool => g.eval X) ∧
  ∀ X : Fin m → Bool, ¬ (g.eval X = true ∧ g.eval (fun j => !X j) = true)

end SemAC02


