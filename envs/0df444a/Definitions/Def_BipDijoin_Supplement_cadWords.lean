-- Prove2me | Definitions.Def_BipDijoin_Supplement_cadWords
-- name    : BipDijoin_Supplement_cadWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:52:08.278252+00:00
-- url     : https://prove2.me/theorems/58a5852b-86b9-48d2-9439-ff1e8f4aa80d
-- title:
--   Input and output layouts of the implementation of Algorithm 3: supplied matching, $\nu$, $h$; history, terminal quotient, matching
-- statement:
--   The layouts of the implementation interface (Theorem 6.24).
--
--   **Input words.** The arc list of the bipartite multigraph ($a,\ b,\ m,\ \ell_0,\ r_0,\dots$, as in the base mission), then $|M_0|$ and the arc indices of the supplied initial matching $M_0$ ("after the initial matching is supplied"), then the integers $\nu\ge1$ (the volume budget of §6.4.2) and $h\ge1$ (the truncation depth of §6.4.3).
--
--   **Output words.** The decomposition history (the number of records, then each record $s,\ |U|,\ U,\ |P|,\ P$ in current vertex names), then the full terminal quotient $H$ ($|V(H)|$, its vertices, $|E(H)|$, and for each edge identity $e$ of $H$ the words $e$, its left end and its right end in $H$), then $|M|$ and the edge identities of the final matching $M$. Inactive vertices are vertices of $H$ like the others.
--
--   This is the representation named in Theorem 6.24: "a compact decomposition history, the full terminal quotient, and its perfect matching, including inactive vertices".
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Theorem 6.24, p.40 (PDF p.42); §6.4.2, p.35 (PDF p.37); §6.4.3, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsPartialDecomp
import Definitions.Def_BipDijoin_ofInput

set_option autoImplicit false

namespace BipDijoin

namespace Supplement

/-!
# Input and output layouts of the implementation of Algorithm 3 (Theorem 6.24)

Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6), Theorem 6.24, p.40
(PDF p.42): "the four subroutines of Algorithm 3 can be implemented in … total time after the
initial matching is supplied. … The output can be represented by a compact decomposition history,
the full terminal quotient, and its perfect matching, including inactive vertices." The integers
`ν ≥ 1` (§6.4.2, p.35, PDF p.37: "Fix an integer volume budget ν ≥ 1") and `h ≥ 1` (§6.4.3, p.37,
PDF p.39: "Fix an integer h ≥ 1") are parameters of the implementation.

**Formalization Note.**
* **Input words** (`cadInputWords`): the base arc-list words `a, b, m, ℓ₀, r₀, …` of the graph
  (`inputWords`), then `|M₀|` and the arc indices of the supplied initial matching `M₀`, then `ν`
  and `h`.
* **Output words** (`CADOutWords`): the number of records and the records (base `RecWords`:
  `s, |U|, U, |P|, P`, vertices in current names with representatives `n, n + 1, …`), then the
  terminal quotient `H` (`QuotientWords`: `|V(H)|`, its vertices, `|E(H)|`, and for each edge
  identity `e` of `H` the three words `e, tl e, hd e`), then `|M|` and the edge identities of the
  final matching `M` of `H`. Inactive vertices are vertices of `H` like the others.
-/

/-- The input words of Theorem 6.24. -/
def cadInputWords (a b : ℕ) (es : List (ℕ × ℕ)) (M₀ : List ℕ) (ν h : ℕ) : List ℕ :=
  inputWords a b es ++ (M₀.length :: M₀) ++ [ν, h]

/-- The words `ws` list the graph `H`: its vertices, then each edge identity with its two ends. -/
def QuotientWords (H : BipGraph) (ws : List ℕ) : Prop :=
  ∃ (Vl : List ℕ) (El : List (ℕ × ℕ × ℕ)),
    Vl.Nodup ∧ Vl.toFinset = H.V ∧ (El.map Prod.fst).Nodup ∧ (El.map Prod.fst).toFinset = H.E ∧
    (∀ t ∈ El, t.2.1 = H.tl t.1 ∧ t.2.2 = H.hd t.1) ∧
    ws = (Vl.length :: Vl) ++ (El.length :: El.flatMap (fun t => [t.1, t.2.1, t.2.2]))

/-- The words `ws` encode the decomposition history `recs`, the terminal quotient `H` and the
matching `M`. -/
def CADOutWords (recs : List Rec) (H : BipGraph) (M : Finset ℕ) (ws : List ℕ) : Prop :=
  ∃ (chunks : List (List ℕ)) (qws : List ℕ) (Ml : List ℕ),
    List.Forall₂ RecWords recs chunks ∧ QuotientWords H qws ∧ Ml.Nodup ∧ Ml.toFinset = M ∧
    ws = recs.length :: chunks.flatten ++ qws ++ (Ml.length :: Ml)

end Supplement

end BipDijoin


