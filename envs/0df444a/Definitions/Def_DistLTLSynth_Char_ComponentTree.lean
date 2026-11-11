-- Prove2me | Definitions.Def_DistLTLSynth_Char_ComponentTree
-- name    : DistLTLSynth_Char_ComponentTree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:16:33.18619+00:00
-- url     : https://prove2.me/theorems/874ec237-c579-4d24-95bb-4016afd6bc45
-- title:
--   Block automaton specification (Lemma 3.7), positions, output labelings, K^(D)_live, uncompressed component trees (Definition 3.8), runs, acceptance, effectively given trees
-- statement:
--   Fix a block length $D$ and a deterministic parity automaton $B$ over blocks $\Sigma^D\times\Omega^D$ with a set $Q_{\mathrm{live}}$ of states satisfying Lemma 3.7: $B$ accepts exactly the executions, grouped into blocks, that satisfy $\varphi$ or whose graph history is outside $A$, and after any finite sequence of blocks $B$ is in $Q_{\mathrm{live}}$ iff the graph history read so far is in $\mathrm{Pref}(A)$.
--
--   An edge $e(h)=\{v_1(h),v_2(h)\}$ of a view complex is identified with its history $h$ (the pair of views determines it); $eu = e(hu)$. A node label carries a **position** $(K,q)$ — a finite set of edges with a state $q(e)$ each — and an **output labeling** $\lambda$ giving $\lambda_p(v)\in Y_p$ to every process-$p$ vertex of $K^{(t)}$, $1\le t\le D$. For $u\in\Sigma^D$, $q_\lambda(e,u)$ is the $B$-successor of $q(e)$ on the block $u$ with outputs $\lambda(e,u[\ldots1]),\dots,\lambda(e,u)$, and $E(K^{(D)}_{\mathrm{live}}) = \{eu \mid e\in E(K),\,u\in\Sigma^D,\,q_\lambda(e,u)\in Q_{\mathrm{live}}\}$; edges are adjacent when they share a view.
--
--   An **uncompressed component tree** is a rooted finitely branching tree whose root carries $(\{e_{\mathrm{init}}\}, e_{\mathrm{init}}\mapsto q_{\mathrm{init}})$, $e_{\mathrm{init}}=e(\varepsilon)$, and in which, at a node carrying $(K,q)$ and $\lambda$, every connected component $K'$ of $K^{(D)}_{\mathrm{live}}$ gives exactly one child, carrying $(K', eu\mapsto q_\lambda(e,u))$, and these are all its children. A **run** is an infinite branch with edges $e_n\in E(K_n)$ and blocks $u_n$ with $e_0=e_{\mathrm{init}}$, $e_{n+1}=e_nu_n$ (Eq. 5); the tree is **accepting** if $(q_n(e_n))_{n\ge0}$ satisfies $B$'s parity condition for every run. A tree is **effectively given** by a partial recursive code that maps every valid node address to the node's label and number of children.
--
--   **Formalization Note.** Node addresses are lists of child numbers; labels are finite lists (edge, state) and (view, output), read by first match; outputs default to a fixed element on vertices outside $\lambda$'s domain, which the covering condition rules out.
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), pp. 12–13 (PDF 13–14), §3.3.1–3.3.2, Lemma 3.7, Definition 3.8, Eq. (5), 'effectively given'

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Automata

namespace DistLTLSynth.Char

/-- An infinite word grouped into blocks of length `D`: block `n` is
`(e (nD), …, e (nD + D - 1))`. -/
def toBlocks {α : Type} (D : ℕ) (e : ℕ → α) : ℕ → Fin D → α :=
  fun n i => e (n * D + i.val)

/-- The specification of the block automaton `B = (Q, q_init, δ, χ)` over `Σ^D × Ω^D` with
its set `Q_live` (Lemma 3.7, p. 13): `B` accepts exactly the executions, grouped into blocks,
that satisfy `ϕ` or whose graph history is outside `A`; and after any finite sequence of
blocks, `B` is in `Q_live` iff the graph history read so far extends to an infinite graph
history in `A`. -/
structure IsBlockAutomaton {X1 X2 Y1 Y2 QB : Type} (A : Set (ℕ → CommGraph))
    (φ : Formula X1 X2 Y1 Y2) (D : ℕ) (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2)))
    (Qlive : Set QB) : Prop where
  accepts : ∀ e : ℕ → Signal X1 X2 × (Y1 × Y2),
    B.Accepts (toBlocks D e) ↔ (graphOfExec e ∉ A ∨ φ.Sat e)
  live : ∀ (e : ℕ → Signal X1 X2 × (Y1 × Y2)) (n : ℕ),
    B.run (toBlocks D e) n ∈ Qlive ↔ pre (graphOfExec e) (n * D) ∈ Pref A

/-- The label of a node of a component tree (Definition 3.8, p. 13), as finite data:
the position `(K, q)` as the list of the edges of `K` with their states (an edge
`e(h) = {v₁(h), v₂(h)}` is represented by its history `h`, which it determines), and the
output labeling `λ = (λ₁, λ₂)` as lists of (view, output) pairs. -/
abbrev NodeLabel (X1 X2 Y1 Y2 QB : Type) : Type :=
  List (List (Signal X1 X2) × QB) × List (View X1 X2 × Y1) × List (View X1 X2 × Y2)

section Labels

variable {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2]

/-- `E(K)`. -/
def NodeLabel.edges (L : NodeLabel X1 X2 Y1 Y2 QB) : Set (List (Signal X1 X2)) :=
  {h | ∃ s, (h, s) ∈ L.1}

/-- `q(e)` (the default `d` is never read on an edge of `K`). -/
def NodeLabel.state (L : NodeLabel X1 X2 Y1 Y2 QB) (d : QB) (h : List (Signal X1 X2)) : QB :=
  (L.1.lookup h).getD d

/-- `λ₁(v)`. -/
def NodeLabel.lam1 [Inhabited Y1] (L : NodeLabel X1 X2 Y1 Y2 QB) (v : View X1 X2) : Y1 :=
  (L.2.1.lookup v).getD default

/-- `λ₂(v)`. -/
def NodeLabel.lam2 [Inhabited Y2] (L : NodeLabel X1 X2 Y1 Y2 QB) (v : View X1 X2) : Y2 :=
  (L.2.2.lookup v).getD default

/-- `λ` is an output labeling from `K`: it gives an output to every process-`p` vertex
`(eu)_p` of every extension graph `K^(t)`, `1 ≤ t ≤ D`. -/
def NodeLabel.Covers (D : ℕ) (L : NodeLabel X1 X2 Y1 Y2 QB) : Prop :=
  ∀ e ∈ L.edges, ∀ u : List (Signal X1 X2), 1 ≤ u.length → u.length ≤ D →
    (∃ y, (view1 (e ++ u), y) ∈ L.2.1) ∧ (∃ y, (view2 (e ++ u), y) ∈ L.2.2)

/-- `λ(e, u) := (λ₁((eu)₁), λ₂((eu)₂))`. -/
def NodeLabel.out [Inhabited Y1] [Inhabited Y2] (L : NodeLabel X1 X2 Y1 Y2 QB)
    (e w : List (Signal X1 X2)) : Y1 × Y2 :=
  (L.lam1 (view1 (e ++ w)), L.lam2 (view2 (e ++ w)))

/-- `q_λ(e, u)`: the successor of `q(e)` in `B` on the block `u ∈ Σ^D` with the successive
outputs `λ(e, u[...1]), …, λ(e, u)`. -/
def NodeLabel.qLam [Inhabited Y1] [Inhabited Y2] {D : ℕ}
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))) (L : NodeLabel X1 X2 Y1 Y2 QB)
    (e : List (Signal X1 X2)) (u : Fin D → Signal X1 X2) : QB :=
  B.step (L.state B.init e) (fun i => (u i, L.out e ((List.ofFn u).take (i.val + 1))))

/-- `E(K^(D)_live) := {eu | e ∈ E(K), u ∈ Σ^D, q_λ(e, u) ∈ Q_live}`. -/
def NodeLabel.liveExt [Inhabited Y1] [Inhabited Y2] {D : ℕ}
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))) (Qlive : Set QB)
    (L : NodeLabel X1 X2 Y1 Y2 QB) : Set (List (Signal X1 X2)) :=
  {h | ∃ e ∈ L.edges, ∃ u : Fin D → Signal X1 X2, h = e ++ List.ofFn u ∧ L.qLam B e u ∈ Qlive}

end Labels

/-- Two edges share a vertex: the same view of process 1 or the same view of process 2. -/
def EdgeAdj {X1 X2 : Type} (h h' : List (Signal X1 X2)) : Prop :=
  view1 h = view1 h' ∨ view2 h = view2 h'

/-- `C` is (the edge set of) a connected component of the graph with edge set `S`. -/
def IsComponentOf {X1 X2 : Type} (S C : Set (List (Signal X1 X2))) : Prop :=
  ∃ c ∈ S, C = {h | Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ EdgeAdj a b) c h}

/-- A rooted, finitely branching labeled tree: node addresses are lists of child numbers,
the children of node `a` are `a ++ [i]` for `i < nChildren a`. -/
structure LabeledTree (L : Type) : Type where
  label : List ℕ → L
  nChildren : List ℕ → ℕ

/-- `a` is a node of `t`. -/
def LabeledTree.Valid {L : Type} (t : LabeledTree L) (a : List ℕ) : Prop :=
  ∀ (i : ℕ) (hi : i < a.length), a[i] < t.nChildren (a.take i)

section Trees

variable {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2] [Inhabited Y1]
  [Inhabited Y2]

/-- An uncompressed component tree (Definition 3.8, p. 13) for block length `D`, block
automaton `B` and `Q_live`: the root carries `(K₀, q₀) = ({e_init}, e_init ↦ q_init)`
(`e_init = e(ε)`); every node carries an output labeling `λ` from its `K`; and at a node
carrying `(K, q)` and `λ`, every connected component `K'` of `K^(D)_live` gives exactly one
child, which carries `(K', q')` with `q'(eu) := q_λ(e, u)`; these are all its children. -/
def IsUncompressedComponentTree {D : ℕ} (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2)))
    (Qlive : Set QB) (t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)) : Prop :=
  (t.label []).edges = {[]} ∧
  (∀ h s, (h, s) ∈ (t.label []).1 → s = B.init) ∧
  ∀ a, t.Valid a →
    (t.label a).Covers D ∧
    (∀ i < t.nChildren a,
      IsComponentOf ((t.label a).liveExt B Qlive) (t.label (a ++ [i])).edges ∧
      ∀ h s, (h, s) ∈ (t.label (a ++ [i])).1 → ∀ e ∈ (t.label a).edges,
        ∀ u : Fin D → Signal X1 X2, h = e ++ List.ofFn u → s = (t.label a).qLam B e u) ∧
    (∀ C, IsComponentOf ((t.label a).liveExt B Qlive) C →
      ∃! i, i < t.nChildren a ∧ (t.label (a ++ [i])).edges = C)

/-- The tree is accepting (Definition 3.8, Eq. (5)): for every run — an infinite branch
`a₀ = root, a_{n+1} = aₙ ++ [iₙ]`, edges `eₙ ∈ E(Kₙ)` and blocks `uₙ ∈ Σ^D` with
`e₀ = e_init`, `e_{n+1} = eₙ uₙ` — the state sequence `(qₙ(eₙ))_{n ≥ 0}` satisfies the parity
condition of `B`. -/
def IsAcceptingTree {D : ℕ} (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2)))
    (t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)) : Prop :=
  ∀ (a : ℕ → List ℕ) (e : ℕ → List (Signal X1 X2)) (u : ℕ → Fin D → Signal X1 X2),
    a 0 = [] → (∀ n, t.Valid (a n) ∧ ∃ i, a (n + 1) = a n ++ [i]) →
    e 0 = [] → (∀ n, e (n + 1) = e n ++ List.ofFn (u n)) →
    (∀ n, e n ∈ (t.label (a n)).edges) →
    ParityCond (fun n => B.prio ((t.label (a n)).state B.init (e n)))

/-- The tree is effectively given by the code `c` (p. 13): on (the code of) any valid node
address, `c` returns (the code of) the node's label and its number of children. -/
def EffectivelyGiven [Encodable X1] [Encodable X2] [Encodable Y1] [Encodable Y2]
    [Encodable QB] (t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)) (c : Nat.Partrec.Code) : Prop :=
  ∀ a, t.Valid a →
    c.eval (Encodable.encode a) = Part.some (Encodable.encode (t.label a, t.nChildren a))

end Trees

end DistLTLSynth.Char


