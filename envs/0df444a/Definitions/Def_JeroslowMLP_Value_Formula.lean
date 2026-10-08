-- Prove2me | Definitions.Def_JeroslowMLP_Value_Formula
-- name    : JeroslowMLP_Value_Formula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:38:36.010257+00:00
-- url     : https://prove2.me/theorems/83c635ec-f0e1-49e1-93f9-ac478277ddbd
-- title:
--   §3, pp. 150–151 — propositional formulas, the system L_F of (3.1), and the Σ_p sentence (3.3)
-- statement:
--   **Formulas.** Propositional formulas over a set of atoms are built from atoms with $\neg$, $\wedge$, $\vee$. The **length** $L$ of a formula counts atoms and connectives: an atom has length $1$, $\neg G$ has length $L(G)+1$, and $G\wedge H$, $G\vee H$ have length $L(G)+L(H)+1$. A formula is evaluated under a truth assignment as usual.
--
--   **The system $L_G$** (p. 150). Each non-atomic subformula occurrence $G$ gets a real variable $x(G)$; for an atom $A$, $x(A)$ is the atom's own variable. The constraints are, recursively (the systems of the subformulas being retained),
--   $$\begin{aligned}
--   G=G_1\vee G_2:&\quad x(G)\le x(G_1)+x(G_2),\ \ x(G)\ge x(G_1),\ \ x(G)\ge x(G_2), &(3.1a)\\
--   G=G_1\wedge G_2:&\quad x(G)\le x(G_1),\ \ x(G)\le x(G_2),\ \ x(G)\ge x(G_1)+x(G_2)-1, &(3.1b)\\
--   G=\neg G_1:&\quad x(G)=1-x(G_1), &(3.1c)
--   \end{aligned}$$
--   together with $0\le x(A),x(G)\le 1$ for every atom $A$ and non-atomic subformula $G$ occurring in $F$.
--
--   **Blocks and the sentence (3.3).** The atoms are split into $p$ blocks $X_1,\dots,X_p$, block $X_k$ having $n_k$ atoms $X_{k1},\dots,X_{kn_k}$ ($n_k=0$ is allowed). Block $X_k$ carries the quantifier $Q_k=\exists$ if $p-k$ is even and $Q_k=\forall$ otherwise, so $Q_p=\exists$ and $Q_1=\exists$ iff $p$ is odd. For $0\le k\le p$ and a truth assignment $\alpha$, `QHolds k α` is the truth of
--   $$(Q_kX_k)\cdots(Q_1X_1)\,[F(X_1,\dots,X_k,\alpha^{k+1},\dots,\alpha^p)=1],$$
--   the blocks above $k$ keeping their values under $\alpha$. At $k=p$ this is the $\Sigma_p$ sentence
--   $$(\exists X_p)(\forall X_{p-1})\cdots(Q_1X_1)\,[F(X_1,\dots,X_p)=1]. \qquad (3.3)$$
--
--   These objects carry the reduction from quantified Boolean formulas to multi-level games.
--
--   **Formalization Note** Blocks are 0-based in Lean: block `k : Fin p` is the paper's $X_{k+1}$. The node variables are indexed by the non-atomic subformula occurrences of $F$ (type `F.Node`); `nodeVal` returns $x(G)$ and `LSys` is the system above. The paper also allows $\to$ (rewritten by the paper itself as $\neg G_1\vee G_2$) and mentions $\leftrightarrow$; every formula has an equivalent over $\{\neg,\wedge,\vee\}$, so they are omitted. The paper fixes the length only through "an atom has $L\ge1$" and $L_1+L_2\le L$ (proof of Lemma 4.1); the definition above satisfies both. `rootAtom` and `isRootNode` locate the variable $x(F)$.
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), p. 150, (3.1a)–(3.1c), and p. 151, (3.3)

import Mathlib

namespace JeroslowMLP.Value

/-- Propositional formulas over atoms `α`, built with `¬`, `∧`, `∨` (§3, p. 150). -/
inductive Formula (α : Type) where
  | var (a : α)
  | neg (G : Formula α)
  | and (G H : Formula α)
  | or (G H : Formula α)

namespace Formula

variable {α : Type}

/-- Truth value of a formula under a truth assignment of its atoms. -/
def eval : Formula α → (α → Bool) → Bool
  | var a, β => β a
  | neg G, β => !(G.eval β)
  | and G H, β => G.eval β && H.eval β
  | or G H, β => G.eval β || H.eval β

/-- The length `L` of a formula: an atom has length `1`, and each connective adds `1`. -/
def length : Formula α → ℕ
  | var _ => 1
  | neg G => G.length + 1
  | and G H => G.length + H.length + 1
  | or G H => G.length + H.length + 1

/-- The atoms occurring in a formula. -/
def atoms : Formula α → Set α
  | var a => {a}
  | neg G => G.atoms
  | and G H => G.atoms ∪ H.atoms
  | or G H => G.atoms ∪ H.atoms

/-- The non-atomic subformula occurrences (nodes) of a formula: `none` is the root node of a
compound formula, `some _` a node of an immediate subformula. An atom has no node. -/
def Node : Formula α → Type
  | var _ => Empty
  | neg G => Option (Node G)
  | and G H => Option (Node G ⊕ Node H)
  | or G H => Option (Node G ⊕ Node H)

/-- `Fintype` instance for the nodes, by recursion on the formula. -/
instance instFintypeNode : (G : Formula α) → Fintype (Node G)
  | var _ => (inferInstance : Fintype Empty)
  | neg G => @instFintypeOption _ (instFintypeNode G)
  | and G H =>
      @instFintypeOption _ (@instFintypeSum _ _ (instFintypeNode G) (instFintypeNode H))
  | or G H =>
      @instFintypeOption _ (@instFintypeSum _ _ (instFintypeNode G) (instFintypeNode H))

/-- `x(G)`: given values `xa` of the atom variables and `xn` of the node variables of `G`,
the value of the variable attached to `G` itself (the atom's variable if `G` is atomic, the root
node's variable otherwise). -/
def nodeVal : (G : Formula α) → (α → ℝ) → (Node G → ℝ) → ℝ
  | var a, xa, _ => xa a
  | neg _, _, xn => xn none
  | and _ _, _, xn => xn none
  | or _ _, _, xn => xn none

/-- The linear system `L_G` of (3.1a)–(3.1c), p. 150, with every atom and node variable
restricted to `[0, 1]`: for each non-atomic subformula occurrence the inequalities of its
connective, the systems of its immediate subformulas being retained. -/
def LSys : (G : Formula α) → (α → ℝ) → (Node G → ℝ) → Prop
  | var a, xa, _ => 0 ≤ xa a ∧ xa a ≤ 1
  | neg G, xa, xn =>
      LSys G xa (fun g => xn (some g)) ∧
      xn none = 1 - G.nodeVal xa (fun g => xn (some g)) ∧
      0 ≤ xn none ∧ xn none ≤ 1
  | and G H, xa, xn =>
      LSys G xa (fun g => xn (some (Sum.inl g))) ∧
      LSys H xa (fun g => xn (some (Sum.inr g))) ∧
      xn none ≤ G.nodeVal xa (fun g => xn (some (Sum.inl g))) ∧
      xn none ≤ H.nodeVal xa (fun g => xn (some (Sum.inr g))) ∧
      G.nodeVal xa (fun g => xn (some (Sum.inl g))) +
        H.nodeVal xa (fun g => xn (some (Sum.inr g))) - 1 ≤ xn none ∧
      0 ≤ xn none ∧ xn none ≤ 1
  | or G H, xa, xn =>
      LSys G xa (fun g => xn (some (Sum.inl g))) ∧
      LSys H xa (fun g => xn (some (Sum.inr g))) ∧
      xn none ≤ G.nodeVal xa (fun g => xn (some (Sum.inl g))) +
        H.nodeVal xa (fun g => xn (some (Sum.inr g))) ∧
      G.nodeVal xa (fun g => xn (some (Sum.inl g))) ≤ xn none ∧
      H.nodeVal xa (fun g => xn (some (Sum.inr g))) ≤ xn none ∧
      0 ≤ xn none ∧ xn none ≤ 1

/-- The atom of an atomic formula, `none` for a compound one. -/
def rootAtom : Formula α → Option α
  | var a => some a
  | _ => none

/-- Whether a node is the root node of the formula. -/
def isRootNode : (G : Formula α) → Node G → Bool
  | var _, g => nomatch g
  | neg _, g => g.isNone
  | and _ _, g => g.isNone
  | or _ _, g => g.isNone

end Formula

/-- Atoms split into `p` blocks: `⟨k, j⟩` is the logical variable `X_{k+1, j+1}` of block
`X_{k+1}` (blocks are 0-based here, the paper's are 1-based). -/
abbrev Atom (p : ℕ) (n : Fin p → ℕ) : Type := (k : Fin p) × Fin (n k)

/-- Replace the values of block `k` of a truth assignment by `β`. -/
def setBlock {p : ℕ} {n : Fin p → ℕ} (α : Atom p n → Bool) (k : Fin p)
    (β : Fin (n k) → Bool) : Atom p n → Bool :=
  fun a => if h : a.1 = k then β (Fin.cast (by rw [h]) a.2) else α a

/-- Quantified truth `QHolds p n F k α`: the blocks `0, …, k - 1` (the paper's `X₁, …, X_k`)
are quantified, innermost block `0`, and every other block keeps its value under `α`. The
paper's block `X_{i}` (0-based block `i - 1`) carries `∃` iff `p - i` is even, so `X_p` is
existential and `X₁` is existential iff `p` is odd ((3.3), p. 151). -/
def QHolds (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) :
    ℕ → (Atom p n → Bool) → Prop
  | 0, α => F.eval α = true
  | k + 1, α =>
      if h : k < p then
        (if Even (p - (k + 1)) then
          ∃ β : Fin (n ⟨k, h⟩) → Bool, QHolds p n F k (setBlock α ⟨k, h⟩ β)
        else
          ∀ β : Fin (n ⟨k, h⟩) → Bool, QHolds p n F k (setBlock α ⟨k, h⟩ β))
      else QHolds p n F k α

/-- The `Σ_p` sentence (3.3), p. 151:
`(∃X_p)(∀X_{p-1}) … (Q₁X₁)[F(X₁, …, X_p) = 1]`. All blocks are quantified, so the assignment
passed to `QHolds` is irrelevant. -/
def Sentence33 (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) : Prop :=
  QHolds p n F p (fun _ => false)

end JeroslowMLP.Value


