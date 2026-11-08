-- Prove2me | Definitions.Def_PercCubeCycles_Packing
-- name    : PercCubeCycles_Packing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:43.468014+00:00
-- url     : https://prove2.me/theorems/571a04d5-3904-42d6-a621-63d1a0f9da77
-- title:
--   Hypotheses and conclusion of Theorem 3 (cycle packing in locally expanding graphs)
-- statement:
--   For an integer $k\ge1$ and reals $0<c\le C$, let $I=[I_{\min},I_{\max}]$ with
--   $$I_{\min}=\min\{ck/10,\ ck/(10C)\},\qquad I_{\max}=\max\{10Ck/c,\ 10Ck\}.$$
--   The hypothesis of Theorem 3 is that $G$ is connected on more than $k$ vertices and that every almost connected $W$ with $|W|\in I$ has (P1) $c|W|\le|N(W)|\le C|W|$ and (P2) $e(W,Z)\le|Z|+c^2k/10$ for every $Z\subseteq N(W)$.
--
--   The conclusion asks for pairwise vertex disjoint cycles of length at least $\lceil ck/10\rceil$ covering at least $\frac17\frac cC|V(G)|$ vertices.
--
--   **Formalization Note** The printed $ck/10C$ is read as $ck/(10C)$. The other parse would give $I_{\min}<m$ in the application on p.10. The program receives $k$, $\lceil ck/10\rceil$, $\lceil h/2\rceil$, $\lfloor h\rfloor$ with $h=\max\{k,ck\}$, the only integers the procedure of p.11 compares with.
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Theorem 3, p.4

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation
import Definitions.Def_PercCubeCycles_MachineIO

set_option autoImplicit false

namespace PercCubeCycles

/-!
# The hypotheses and the conclusion of Theorem 3

Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…), Theorem 3, p.4.

**Formalization Note.** `ck/10C` in `I_min` is read as `ck/(10C)`, the counterpart of `10Ck/c` in
`I_max`. The other parse `(ck/10)·C` would break the application on p.10, where `c = ε/5000`,
`C = 2001ε`, `k = 2^{αd}`: there `I_min` must be at least `m = ε²k`.
-/

variable {V : Type*}

/-- Theorem 3: `I_min = min{ck/10, ck/(10C)}`. -/
noncomputable def iMin (k : ℕ) (c C : ℝ) : ℝ := min (c * k / 10) (c * k / (10 * C))

/-- Theorem 3: `I_max = max{10Ck/c, 10Ck}`. -/
noncomputable def iMax (k : ℕ) (c C : ℝ) : ℝ := max (10 * C * k / c) (10 * C * k)

/-- The graph hypotheses of Theorem 3: `G` is a connected graph on more than `k` vertices such that
every almost connected set `W ⊆ V(G)` with `|W| ∈ I` satisfies (P1) and (P2). -/
def PackingHyp [Fintype V] (k : ℕ) (c C : ℝ) (G : SimpleGraph V) : Prop :=
  G.Connected ∧ k < Fintype.card V ∧
    ∀ W : Finset V, IsAlmostConnectedSet G W →
      iMin k c C ≤ (W.card : ℝ) → (W.card : ℝ) ≤ iMax k c C →
      (c * W.card ≤ ((nbhd G W).card : ℝ) ∧ ((nbhd G W).card : ℝ) ≤ C * W.card) ∧
      ∀ Z : Finset V, Z ⊆ nbhd G W →
        (eBetween G W Z : ℝ) ≤ Z.card + c ^ 2 * k / 10

/-- The conclusion of Theorem 3: `F` is a family of pairwise vertex disjoint cycles of `G` of length
at least `⌈ℓ⌉`, `ℓ = ck/10`, covering at least `(1/7)(c/C)|V(G)|` vertices. -/
def IsCyclePacking [Fintype V] (k : ℕ) (c C : ℝ) (G : SimpleGraph V) (F : List (List V)) : Prop :=
  (∀ l ∈ F, IsCycleList G l ∧ ⌈c * k / 10⌉₊ ≤ l.length) ∧
    F.Pairwise List.Disjoint ∧
    (1 / 7 : ℝ) * (c / C) * Fintype.card V ≤ ((F.map List.length).sum : ℝ)

/-- The input for Theorem 3: the graph, then `k`, `⌈ck/10⌉`, `⌈h/2⌉`, `⌊h⌋` for `h = max{k, ck}`
(p.11). These integers are the only way the real numbers `c`, `C` enter the procedure. -/
noncomputable def packingInput {n : ℕ} (k : ℕ) (c : ℝ) (G : SimpleGraph (Fin n)) : List ℤ :=
  ((n : ℤ) :: edgeWords G) ++
    [(k : ℤ), (⌈c * k / 10⌉₊ : ℤ), (⌈max (k : ℝ) (c * k) / 2⌉₊ : ℤ), (⌊max (k : ℝ) (c * k)⌋₊ : ℤ)]

end PercCubeCycles


