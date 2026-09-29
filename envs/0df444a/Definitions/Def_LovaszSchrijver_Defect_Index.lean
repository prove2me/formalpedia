-- Prove2me | Definitions.Def_LovaszSchrijver_Defect_Index
-- name    : LovaszSchrijver_Defect_Index
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:52:55.902184+00:00
-- url     : https://prove2.me/theorems/935510ee-c594-4744-9ea7-088dca9b67a8
-- title:
--   The N-index and the defect of a stable set inequality, FRAC-maximizers, and the tight-edge graph (V, E′) (Section 2.c)
-- statement:
--   Let $G = (V,E)$ be a graph with no isolated nodes, and let $a^{\mathsf T}x \le b$ be an inequality.
--
--   1. **N-index** (p. 179). "Let $a^{\mathsf T}x \le b$ be any inequality valid for $\mathrm{STAB}(G)$. By Theorem 1.4, there exists an $r \ge 0$ such that $a^{\mathsf T}x \le b$ is valid for $N^r(G)$. Let the N-index of the inequality be defined as the least $r$ for which this is true." A natural number $k$ is the N-index of $a^{\mathsf T}x\le b$ when $k$ is the least element of $\{t \in \mathbb N : a^{\mathsf T}x \le b \text{ is valid for } N^t(G)\}$.
--   2. **Defect** (p. 180). "Let $a^{\mathsf T}x \le b$ be any constraint valid for $\mathrm{STAB}(G)$ ($a \in \mathbb Z_+^V$, $b \in \mathbb Z_+$). Define the defect of this inequality as $2 \times \max\{a^{\mathsf T}x - b : x \in \mathrm{FRAC}(G)\}$. The factor 2 in front guarantees that this is an integer." A real number $r$ is the defect of $a^{\mathsf T}x\le b$ when $r$ is the greatest element of
--   $$\{\,2\,(a^{\mathsf T}x - b) : x \in \mathrm{FRAC}(G)\,\},$$
--   i.e. the maximum exists and equals $r$.
--   3. **Maximizers.** A vector $y$ maximizes $a^{\mathsf T}x$ over $\mathrm{FRAC}(G)$ if $y \in \mathrm{FRAC}(G)$ and $a^{\mathsf T}x \le a^{\mathsf T}y$ for every $x \in \mathrm{FRAC}(G)$.
--   4. **The graph $(V, E')$** (p. 181, Lemma 2.11). "Let $E'$ be the set of those edges $ij$ for which $y_i + y_j = 1$ holds for every vector $y \in \mathrm{FRAC}(G)$ maximizing $a^{\mathsf T}x$." The graph $(V, E')$ is the spanning subgraph of $G$ with edge set $E'$.
--
--   The N-index measures how many rounds of the $N$ operator are needed to derive a valid inequality; the defect measures how far $\mathrm{FRAC}(G)$ is from satisfying it. Theorem 2.13 relates the two.
--
--   **Formalization Note** Neither index is a supremum or infimum: both are predicates on a candidate value (`IsLeast`, `IsGreatest`), so no default value arises when a set is empty or unbounded. The defect is defined for real $a$ and $b$ (so that the contraction's right-hand side $b - a_v$ needs no natural-number subtraction); the paper's integer data are cast into $\mathbb R$. $\mathrm{FRAC}(G)$ is a nonempty polytope when $G$ has no isolated nodes, so the maximum defining the defect exists; that is a fact, not part of the definition.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 179, Section 2.c (N-index); p. 180, Section 2.c (defect); p. 181, Lemma 2.11 (E′)

import Mathlib
import Definitions.Def_LovaszSchrijver_Defect_StableSet

namespace LovaszSchrijver.Defect

/-- `k` is the N-index of `aᵀx ≤ b` (p. 179): the least `t` with `aᵀx ≤ b` valid for `Nᵗ(G)`. -/
def IsNIndex {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (a : V → ℝ) (b : ℝ) (k : ℕ) : Prop :=
  IsLeast {t : ℕ | Valid (NG t G) a b} k

/-- `r` is the defect of `aᵀx ≤ b` (p. 180): `r = 2 · max{aᵀx − b : x ∈ FRAC(G)}`, the maximum
being attained. -/
def IsDefect {V : Type} [Fintype V] (G : SimpleGraph V) (a : V → ℝ) (b r : ℝ) : Prop :=
  IsGreatest {s : ℝ | ∃ x ∈ FRAC G, s = 2 * (a ⬝ᵥ x - b)} r

/-- `y ∈ FRAC(G)` maximizes `aᵀx` over `FRAC(G)`. -/
def IsFRACMaximizer {V : Type} [Fintype V] (G : SimpleGraph V) (a y : V → ℝ) : Prop :=
  y ∈ FRAC G ∧ ∀ x ∈ FRAC G, a ⬝ᵥ x ≤ a ⬝ᵥ y

/-- The graph `(V, E′)` of Lemma 2.11 (p. 181): `E′` is the set of edges `ij` of `G` with
`yᵢ + yⱼ = 1` for every `y ∈ FRAC(G)` maximizing `aᵀx`. -/
def tightGraph {V : Type} [Fintype V] (G : SimpleGraph V) (a : V → ℝ) : SimpleGraph V where
  Adj i j := G.Adj i j ∧ ∀ y, IsFRACMaximizer G a y → y i + y j = 1
  symm := ⟨fun i j h => ⟨h.1.symm, fun y hy => by rw [add_comm]; exact h.2 y hy⟩⟩
  loopless := ⟨fun i h => G.loopless.irrefl i h.1⟩

end LovaszSchrijver.Defect


