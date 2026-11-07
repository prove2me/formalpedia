-- Prove2me | Definitions.Def_RefWPHP_sigma
-- name    : RefWPHP_sigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:25.971299+00:00
-- url     : https://prove2.me/theorems/5c295a38-d574-4dd2-bd0c-54d1aca6e716
-- title:
--   The block grid, the depth-2 formulas (3.1a)–(3.1f) and the substitution $\sigma_{\pi,s}$ of (3.2)–(3.3)
-- statement:
--   Let $\pi$ be a layered refutation and $W \in \mathbb N$. Over the variables $p_{C,b}$ of $\mathrm{PHP}^L_W$, for a layer $k$, holes $b, c$, a literal $\ell$, an index $i$ and a clause number $A$, put
--
--   $$
--   E_{k,b} = \bigvee_{C\in\pi_k} p_{C,b},\quad P^{\mathrm{left}}_{k,b,c} = \bigvee_{C\in\pi_k} (p_{C,b}\wedge p_{\mathrm{left}_\pi(C),c}),\quad P^{\mathrm{right}}_{k,b,c} = \bigvee_{C\in\pi_k} (p_{C,b}\wedge p_{\mathrm{right}_\pi(C),c}),
--   $$
--
--   $$
--   L_{k,b,\ell} = \bigvee_{C\in\pi_k,\ \ell\in C} p_{C,b},\quad W_{k,b,A} = \bigvee_{C\in\pi_k,\ C \text{ weakens } A} p_{C,b},\quad R_{k,b,i} = \bigvee_{C\in\pi_k,\ C \text{ resolves } x_i} p_{C,b}.
--   $$
--
--   Set $W = \lfloor s/D\rfloor$ and arrange the blocks of $\mathrm{Ref}_s(\varphi)$ in a grid $B_{k,b}$ of $D$ layers with $W$ blocks each, plus the root block and possibly leftover blocks. The substitution $\sigma_{\pi,s}$ is:
--
--   1. on $B_{k,b}$: $\mathrm{enable} \mapsto E_{k,b}$, $\mathrm{derived} \mapsto \bigvee_i R_{k,b,i}$, $\mathrm{weak}_A \mapsto W_{k,b,A}$, $\mathrm{lit}_\ell \mapsto L_{k,b,\ell}$, $\mathrm{res}_{x_i} \mapsto R_{k,b,i}$, the pointers to $B_{k+1,c}$ $\mapsto P^{\mathrm{left}}_{k,b,c}$ and $P^{\mathrm{right}}_{k,b,c}$, and every other pointer $\mapsto \bot$;
--   2. on the root: $\mathrm{enable}, \mathrm{derived} \mapsto \top$; $\mathrm{lit}, \mathrm{weak} \mapsto \bot$; $\mathrm{res}_{x_i} \mapsto \top$ exactly for $i = i_\emptyset$; the pointers to $B_{1,c}$ $\mapsto p_{C_\emptyset^{\mathrm{left}},c}$ and $p_{C_\emptyset^{\mathrm{right}},c}$; every other pointer $\mapsto \bot$;
--   3. on a leftover block: every variable $\mapsto \bot$.
--
--   The auxiliary formulas $T_{C,b,c} = p_{C,b}\wedge p_{C',c}$ (p.21, p.25), $R_{k,b} = \bigvee_i R_{k,b,i}$, the list $W_{k,b}$ of the $W_{k,b,A}$, and the list $Q^{\mathrm{left}}_{k,b}$ of the $P^{\mathrm{left}}_{k,b,c}$ (pp.23–24) are also defined. This substitution is the reduction of the paper: it uses a purported injection of $[L]$ into $[W]$ to compress all layers of $\pi$ at once.
--
--   **Formalization Note** The paper fixes no numbering of the grid. Here $B_{k,b}$ with $k$ in `Fin D` has index $(D-1-k)W + b$ in `Fin (s+1)`, so deeper layers get smaller indices and every pointer goes to a smaller block, as the pointer variables require. Indices $DW, \dots, s-1$ are the leftover blocks and $s$ is the root. (3.1b) and (3.1c) range over the derived $C \in \pi_k$, for which the premises exist. In the substituted cedents (3.22) and (3.26) the disjunctions over $A$ and $c$ are the disjunctions of the cedents (3.21) and (3.25), so $W_{k,b}$ and $Q^{\mathrm{left}}_{k,b}$ are lists of formulas; as one formula, $Q^{\mathrm{left}}_{k,b}$ would have depth 3. A negative literal goes to the dual through `subst`.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §3.1, (3.1a)–(3.1f) p.19 (PDF p.21), (3.2a)–(3.3g) p.20 (PDF p.22); T p.21, R, W, Q pp.23–24

import Mathlib
import Definitions.Def_RefWPHP_PKFormula
import Definitions.Def_RefWPHP_LayeredRef
import Definitions.Def_RefWPHP_refCNF

namespace RefWPHP

open PKFormula

/-- The block number of the grid position `B_{k,b}` (layer `k : Fin D`, position `b : Fin W`) used
in §3.1, p.20 (PDF 22), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…): the block with index
`(D − 1 − k)·W + b` of `Fin (s+1)`.

**Formalization Note.** The paper fixes no numbering of the grid. This one puts deeper layers at
smaller indices, so that every pointer `B_{k,b} → B_{k+1,c}` goes to a smaller block, as the pointer
variables `lpoint^B_{B'}`, `B' < B`, require. Indices `D·W, …, s − 1` are the leftover blocks and
`s` is the root block. -/
def gridIndex (D W : ℕ) (k : Fin D) (b : Fin W) : ℕ := (D - 1 - k.val) * W + b.val

/-- The inverse of `gridIndex`: the grid position of block index `j`, if `j < D·W`. -/
def gridOf (D W j : ℕ) : Option (Fin D × Fin W) :=
  if h : j < D * W then
    have hD : 0 < D := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
    have hW : 0 < W := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
    some (⟨D - 1 - j / W, lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hD Nat.one_pos)⟩, ⟨j % W, Nat.mod_lt _ hW⟩)
  else none

/-- Case split on a block `B` of `Ref_s(φ)` under the grid of p.20: the root block (index `s`),
a grid block `B_{k,b}`, or a leftover block. -/
def atBlock {X : Type} (D W s : ℕ) (B : Fin (s + 1)) (root : X) (grid : Fin D → Fin W → X)
    (other : X) : X :=
  if B.val = s then root else
    match gridOf D W B.val with
    | some (k, b) => grid k b
    | none => other

/-- The left premise of a resolution step. -/
def RStep.left? {n m L : ℕ} : RStep n m L → Option (Fin L)
  | .ax _ => none
  | .res _ l _ => some l

/-- The right premise of a resolution step. -/
def RStep.right? {n m L : ℕ} : RStep n m L → Option (Fin L)
  | .ax _ => none
  | .res _ _ r => some r

/-- The pivot of a resolution step. -/
def RStep.pivot? {n m L : ℕ} : RStep n m L → Option (Fin n)
  | .ax _ => none
  | .res i _ _ => some i

variable {n m : ℕ} {φ : Fin m → Finset (Lit n)} {L D : ℕ}

/-- The slots of layer `k` that hold a clause of `π` (the set `π_{k+1}` of p.19), in increasing
order. -/
def layerSlots (π : LayeredRef φ L D) (k : Fin D) : List (Fin L) :=
  (List.finRange L).filter (π.used k)

/-- `T_{C,b,c} = p_{C,b} ∧ p_{C',c}` for a clause `C` and its premise `C'` (pp.21, 25): with
`C' = left_π(C)` it is `T^left_{C,b,c}`, with `C' = right_π(C)` it is `T^right_{C,b,c}`. -/
def Tpair {L W : ℕ} (C C' : Fin L) (b c : Fin W) : PKFormula (Fin L × Fin W) :=
  and [pos (C, b), pos (C', c)]

/-- (3.1a), p.19: `E_{k,b} = ⋁_{C ∈ π_k} p_{C,b}`. -/
def E (π : LayeredRef φ L D) (W : ℕ) (k : Fin D) (b : Fin W) : PKFormula (Fin L × Fin W) :=
  or ((layerSlots π k).map fun C => pos (C, b))

/-- (3.1b), p.19: `P^left_{k,b,c} = ⋁_{C ∈ π_k} (p_{C,b} ∧ p_{left_π(C),c})`.

**Formalization Note.** The disjunction is over the derived `C ∈ π_k`, the clauses for which
`left_π(C)` is defined. -/
def Pleft (π : LayeredRef φ L D) (W : ℕ) (k : Fin D) (b c : Fin W) : PKFormula (Fin L × Fin W) :=
  or ((layerSlots π k).filterMap fun C => ((π.step k C).left?).map fun l => Tpair C l b c)

/-- (3.1c), p.19: `P^right_{k,b,c} = ⋁_{C ∈ π_k} (p_{C,b} ∧ p_{right_π(C),c})`, over the derived
`C ∈ π_k`. -/
def Pright (π : LayeredRef φ L D) (W : ℕ) (k : Fin D) (b c : Fin W) : PKFormula (Fin L × Fin W) :=
  or ((layerSlots π k).filterMap fun C => ((π.step k C).right?).map fun r => Tpair C r b c)

/-- (3.1d), p.19: `L_{k,b,ℓ} = ⋁_{C ∈ π_k, ℓ ∈ C} p_{C,b}`. -/
def Lsub (π : LayeredRef φ L D) (W : ℕ) (k : Fin D) (b : Fin W) (ℓ : Lit n) :
    PKFormula (Fin L × Fin W) :=
  or (((layerSlots π k).filter fun C => decide (ℓ ∈ π.clause k C)).map fun C => pos (C, b))

/-- (3.1e), p.19: `W_{k,b,A} = ⋁_{C ∈ π_k, C weakens A} p_{C,b}`. -/
def Wsub (π : LayeredRef φ L D) (W : ℕ) (k : Fin D) (b : Fin W) (A : Fin m) :
    PKFormula (Fin L × Fin W) :=
  or (((layerSlots π k).filter fun C => decide (π.step k C = RStep.ax A)).map fun C => pos (C, b))

/-- (3.1f), p.19: `R_{k,b,i} = ⋁_{C ∈ π_k, C resolves x_i} p_{C,b}`. -/
def Rsub (π : LayeredRef φ L D) (W : ℕ) (k : Fin D) (b : Fin W) (i : Fin n) :
    PKFormula (Fin L × Fin W) :=
  or (((layerSlots π k).filter fun C => decide ((π.step k C).pivot? = some i)).map
    fun C => pos (C, b))

/-- `R_{k,b} = ⋁_{i ∈ [n]} R_{k,b,i}`, p.23. -/
def Rall (π : LayeredRef φ L D) (W : ℕ) (k : Fin D) (b : Fin W) : PKFormula (Fin L × Fin W) :=
  or ((List.finRange n).map fun i => Rsub π W k b i)

/-- `W_{k,b} = ⋁_{A ∈ [m]} W_{k,b,A}`, p.23, as the part `W_{k,b,1}, …, W_{k,b,m}` of a cedent.

**Formalization Note.** In the substituted cedent (3.22) of (Ref-5) the disjunction over `A` is
the disjunction of the cedent (3.21), so `W_{k,b}` is the list of the formulas `W_{k,b,A}`, not
one formula. -/
def Wall (π : LayeredRef φ L D) (W : ℕ) (k : Fin D) (b : Fin W) :
    List (PKFormula (Fin L × Fin W)) :=
  (List.finRange m).map fun A => Wsub π W k b A

/-- `Q^left_{k,b} = ⋁_{c ∈ [W]} P^left_{k,b,c}`, p.24, as the part `P^left_{k,b,1}, …,
P^left_{k,b,W}` of a cedent.

**Formalization Note.** In (3.26) the disjunction over `c` is the disjunction of the cedent
(3.25), so `Q^left_{k,b}` is the list of the depth-2 formulas `P^left_{k,b,c}`. As one formula
`⋁_c P^left_{k,b,c}` it would have depth 3 and could not occur in a PK_2-derivation. -/
def Qleft (π : LayeredRef φ L D) (W : ℕ) (k : Fin D) (b : Fin W) :
    List (PKFormula (Fin L × Fin W)) :=
  (List.finRange W).map fun c => Pleft π W k b c

/-- The substitution `σ_{π,s}` of (3.2a)–(3.2i) and (3.3a)–(3.3g), p.20 (PDF 22), from the
variables of `Ref_s(φ)` to formulas over the variables `p_{C,b}` of `PHP^L_W`, `W = ⌊s/D⌋`.

On a grid block `B_{k,b}`: `enable ↦ E_{k,b}`, `derived ↦ ⋁ᵢ R_{k,b,i}`, `weak_A ↦ W_{k,b,A}`,
`lit_ℓ ↦ L_{k,b,ℓ}`, `res_{x_i} ↦ R_{k,b,i}`, `lpoint^{B_{k,b}}_{B_{k+1,c}} ↦ P^left_{k,b,c}`,
`rpoint^{B_{k,b}}_{B_{k+1,c}} ↦ P^right_{k,b,c}`, and every other pointer `↦ ⊥`. On the root block:
`enable, derived ↦ ⊤`, `lit, weak ↦ ⊥`, `res_{x_i} ↦ ⊤` iff `i = i_∅`,
`lpoint_{B_{1,c}} ↦ p_{C_∅^left,c}`, `rpoint_{B_{1,c}} ↦ p_{C_∅^right,c}`, other pointers `↦ ⊥`.
On a leftover block every variable `↦ ⊥` (p.20: "enable ≔ ⊥. The remaining variables in B can be
set to ⊥, or any other value"). A negative literal `¬v` is sent to the dual of `σ(v)` by `subst`.

**Formalization Note.** Layer `k : Fin D` is the paper's layer `k+1`; the root's pointers go to the
paper's layer 1, here layer `0`. Grid positions are numbered by `gridIndex`. -/
def sigma (π : LayeredRef φ L D) (s : ℕ) : RefVar n m s → PKFormula (Fin L × Fin (s / D))
  | .enable B => atBlock D (s / D) s B top (fun k b => E π (s / D) k b) bot
  | .derived B => atBlock D (s / D) s B top (fun k b => Rall π (s / D) k b) bot
  | .weak B A => atBlock D (s / D) s B bot (fun k b => Wsub π (s / D) k b A) bot
  | .lit B ℓ => atBlock D (s / D) s B bot (fun k b => Lsub π (s / D) k b ℓ) bot
  | .res B i => atBlock D (s / D) s B (if i = π.rootPivot then top else bot)
      (fun k b => Rsub π (s / D) k b i) bot
  | .lpoint B B' => atBlock D (s / D) s B
      (atBlock D (s / D) s B' bot
        (fun k' c => if k'.val = 0 then pos (π.rootLeft, c) else bot) bot)
      (fun k b => atBlock D (s / D) s B' bot
        (fun k' c => if k'.val = k.val + 1 then Pleft π (s / D) k b c else bot) bot)
      bot
  | .rpoint B B' => atBlock D (s / D) s B
      (atBlock D (s / D) s B' bot
        (fun k' c => if k'.val = 0 then pos (π.rootRight, c) else bot) bot)
      (fun k b => atBlock D (s / D) s B' bot
        (fun k' c => if k'.val = k.val + 1 then Pright π (s / D) k b c else bot) bot)
      bot

end RefWPHP


