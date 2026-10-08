-- Prove2me | Definitions.Def_ObfImpossibility_PseudoOracle_Setting
-- name    : ObfImpossibility_PseudoOracle_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:27:40.612411+00:00
-- url     : https://prove2.me/theorems/a81c5303-d333-418c-b025-6441f063b587
-- title:
--   Query distinguishers $D^G$, the probabilities of (7), the set $L_G$ and Properties (1)–(3) of Claim B.1.1 (App. B, pp. A:43–A:44)
-- statement:
--   This file fixes the objects of Appendix B of Barak et al., *On the (Im)possibility of Obfuscating Programs*: a distinguisher $D$ that receives an element $y\in[L]$, may query an oracle $G:[K]\to[L]$ adaptively, and outputs a bit. Throughout, $[K]$ and $[L]$ are finite sets with $K$ and $L$ elements (in Lean, $\{0,\dots,K-1\}$ and $\{0,\dots,L-1\}$; the indexing is immaterial).
--
--   1. **Query trees.** A query tree is either a leaf carrying an output bit $b$, or a node carrying a query point $z\in[K]$ and, for every possible answer $a\in[L]$, a subtree. Running a tree against an oracle $G$ means: at a node with query $z$, continue in the subtree for the answer $G(z)$; at a leaf, output its bit. A distinguisher is a family $D=(D_y)_{y\in[L]}$ of query trees, one per input, and $D^G(y)$ is the output of $D_y$ run against $G$. Every deterministic algorithm with a bounded number of adaptive oracle queries, whatever its computational power between queries, is of this form.
--   2. **Query complexity.** The depth of a tree is the largest number of queries on a root-to-leaf path, over all possible oracle answers. "$D$ makes at most $q$ oracle queries" means that every $D_y$ has depth at most $q$.
--   3. **Queries in a set.** For $S\subseteq[K]$, the run of $D_y$ against $G$ *queries its oracle at an element of $S$* if some query point on that run lies in $S$.
--   4. **The simulation $M$.** For $S\subseteq[K]$, the run of $D_y$ *avoiding $S$* answers a query $z\notin S$ with $G(z)$ and halts with output $0$ at the first query $z\in S$. It reads $G$ only on $[K]\setminus S$.
--   5. **Probabilities.** For a finite set $s$ and a Boolean function $f$, $\Pr_{a\in s}[f(a)=1]$ is the fraction of $a\in s$ with $f(a)=1$ (taken to be $0$ when $s=\emptyset$). For an injective $G:[K]\to[L]$,
--   $$p_X(D,G)=\Pr_{x\in[K]}\big[D^G(G(x))=1\big],\qquad p_Y(D,G)=\Pr_{y\in[L]}\big[D^G(y)=1\big].$$
--   6. **The set $L_G$.** For $S_G\subseteq[K]$, $L_G=[L]\setminus G([K]\setminus S_G)$.
--   7. **Properties (1)–(3) of Claim B.1.1.** For $\delta>0$, $\gamma=K^{-3\delta}$ and $S\subseteq[K]$, a set $S_G$ is *good* for $G$ if (1) $S_G\subseteq S$ and $|S_G|\ge(1-\gamma)|S|$; (2) for every $x\in S_G$, $D^G(G(x))$ never queries its oracle at an element of $S_G$; (3) $\big|\Pr_{x\in S_G}[D^G(G(x))=1]-\Pr_{y\in L_G}[D^G(y)=1]\big|>\frac{1}{2K^\delta}$.
--
--   These are the objects in which Lemma B.1 and the steps of its proof are stated.
--
--   **Formalization Note** `QTree K L` is an inductive type with constructors `out : Bool → QTree K L` and `query : Fin K → (Fin L → QTree K L) → QTree K L`; `run`, `depth`, `hits` and `runAvoid` are defined by structural recursion. The output bit $1$ is `true`. A tree whose deep branches are reachable only through answers no function $G$ gives can be pruned to an equivalent tree of smaller depth, so bounding the depth over all answers loses nothing. Property (1) is read as $|S_G|\ge(1-\gamma)|S|$ rather than with equality, since $(1-\gamma)|S|$ need not be an integer. The distinguisher is deterministic; randomized distinguishers are not modelled.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, pp. A:43–A:44, Appendix B (Lemma B.1, inequality (7), Claim B.1.1 Properties (1)–(3) and L_G, the algorithm M in the proof of Claim B.1.2)

import Mathlib

namespace ObfImpossibility.PseudoOracle

/-- An adaptive query algorithm with oracle `G : [K] → [L]` that outputs a bit, as a
decision tree (App. B, p. A:43). A leaf `out b` halts with output `b`; a node `query z k`
asks the oracle for `G z` and continues with the subtree `k (G z)`. Every deterministic
algorithm with a bounded number of adaptive oracle queries (and unbounded computational
power between queries) is such a tree. `Fin K`, `Fin L` stand for the paper's `[K]`, `[L]`. -/
inductive QTree (K L : ℕ) : Type
  | out : Bool → QTree K L
  | query : Fin K → (Fin L → QTree K L) → QTree K L

namespace QTree

variable {K L : ℕ}

/-- The output of the tree run against the oracle `G`. -/
def run : QTree K L → (Fin K → Fin L) → Bool
  | out b, _ => b
  | query z k, G => (k (G z)).run G

/-- The query complexity: the largest number of queries on any root-to-leaf path
(over all possible oracle answers). -/
def depth : QTree K L → ℕ
  | out _ => 0
  | query _ k => (Finset.univ.sup fun y => (k y).depth) + 1

/-- `hits t G S = true` iff the run of `t` against `G` queries its oracle at some
element of `S`. -/
def hits : QTree K L → (Fin K → Fin L) → Finset (Fin K) → Bool
  | out _, _, _ => false
  | query z k, G, S => decide (z ∈ S) || (k (G z)).hits G S

/-- The run of `t` in which queries outside `S` are answered by `G` and the first query
inside `S` halts the run with output `0` (`false`). This is the algorithm `M` of the
proof of Claim B.1.2 (p. A:44) with `S = S_G`; it reads `G` only on `[K] \ S`. -/
def runAvoid : QTree K L → (Fin K → Fin L) → Finset (Fin K) → Bool
  | out b, _, _ => b
  | query z k, G, S => if z ∈ S then false else (k (G z)).runAvoid G S

end QTree

/-- `Pr_{a ∈ s}[f(a) = 1]`: the fraction of the elements `a` of the finite set `s` with
`f a = true`, for a uniformly random `a ∈ s`. It is `0` when `s = ∅`. -/
noncomputable def avg {α : Type} (s : Finset α) (f : α → Bool) : ℝ :=
  ((s.filter fun a => f a = true).card : ℝ) / (s.card : ℝ)

/-- `Pr_{x ∈ [K]}[D^G(G(x)) = 1]`. -/
noncomputable def prX {K L : ℕ} (D : Fin L → QTree K L) (G : Fin K ↪ Fin L) : ℝ :=
  avg Finset.univ fun x => (D (G x)).run G

/-- `Pr_{y ∈ [L]}[D^G(y) = 1]`. -/
noncomputable def prY {K L : ℕ} (D : Fin L → QTree K L) (G : Fin K ↪ Fin L) : ℝ :=
  avg Finset.univ fun y => (D y).run G

/-- `L_G := [L] \ G([K] \ S_G)` (Claim B.1.1, p. A:43). -/
def LG {K L : ℕ} (G : Fin K ↪ Fin L) (SG : Finset (Fin K)) : Finset (Fin L) :=
  Finset.univ \ (Finset.univ \ SG).map G

/-- Properties (1)–(3) of Claim B.1.1 (p. A:43) for a set `S_G ⊆ S`, with
`γ = K^{-3δ}` and `|S_G| = (1-γ)|S|` read as `|S_G| ≥ (1-γ)|S|`:
(1) `S_G ⊆ S` and `|S_G| ≥ (1 - K^{-3δ}) |S|`;
(2) for `x ∈ S_G`, `D^G(G(x))` never queries its oracle at an element of `S_G`;
(3) `|Pr_{x∈S_G}[D^G(G(x)) = 1] - Pr_{y∈L_G}[D^G(y) = 1]| > 1/(2K^δ)`. -/
def GoodSubset {K L : ℕ} (D : Fin L → QTree K L) (δ : ℝ) (S : Finset (Fin K))
    (G : Fin K ↪ Fin L) (SG : Finset (Fin K)) : Prop :=
  SG ⊆ S ∧
  (1 - (K : ℝ) ^ (-(3 * δ))) * (S.card : ℝ) ≤ (SG.card : ℝ) ∧
  (∀ x ∈ SG, (D (G x)).hits G SG = false) ∧
  1 / (2 * (K : ℝ) ^ δ) <
    |avg SG (fun x => (D (G x)).run G) - avg (LG G SG) (fun y => (D y).run G)|

end ObfImpossibility.PseudoOracle


