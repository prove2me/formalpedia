-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
-- name    : OAI_Combinatorics_ParityLifts_Detection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:13:08.411282+00:00
-- url     : https://prove2.me/theorems/65834012-46f4-456c-b115-d2ff6e2ba4ef
-- title:
--   Counting template homomorphisms through main cliques and common neighbours
-- statement:
--   Let $G$ be a graph on a finite vertex set $V$. The template $T_t$ has a clique on the main vertices $[t]=\{0,\dots,t-1\}$ and, for each $i<j$ and $\ell\notin\{i,j\}$, a helper $h_{ij;\ell}$ adjacent exactly to $i$, $j$ and $\ell$.
--
--   1. **Triple counts.** For $a,b,c\in V$,
--   $$
--   q_G(a,b,c)=\bigl|\{v\in V:\ v\sim a,\ v\sim b,\ v\sim c\}\bigr| ,
--   $$
--   the number of common neighbours of $a$, $b$, $c$.
--   2. **Main cliques.** A tuple $z\in V^{[t]}$ is a main clique if $z_i\sim z_j$ for all $i\ne j$.
--   3. **Template extensions.**
--   $$
--   E_G(z)=\begin{cases}\displaystyle\prod_{h_{ij;\ell}}q_G(z_i,z_j,z_\ell)&\text{if } z \text{ is a main clique},\\ 0&\text{otherwise,}\end{cases}
--   $$
--   the product running over all helpers of $T_t$.
--   4. **Homomorphisms by main images.** Restricting to the main vertices gives a bijection between $\mathrm{Hom}(T_t,G)$ and the pairs consisting of a main clique $z$ and, for every helper $h_{ij;\ell}$, a common neighbour of $z_i$, $z_j$, $z_\ell$. Consequently $\hom(T_t,G)=\sum_{z\in V^{[t]}}E_G(z)$.
--   5. **Extended tuples and faces.** For $x\in V^{k}$ and $v\in V$, $(x,v)\in V^{k+1}$ appends $v$ as a last coordinate, and appending is a bijection $V^k\times V\cong V^{k+1}$. For $i\in[k]$, the face map $[k+1]\to[k]$ sends the last position to $i$ and fixes the other positions; read through it, the replaced tuple $x[i\leftarrow v]$ agrees with $(x,v)$ at every position other than $i$.
--   6. **Joint template value.** For $x\in V^k$,
--   $$
--   J_G(x)=\sum_{v\in V}E_G\bigl((x,v)\bigr),
--   $$
--   the number of homomorphisms $T_{k+1}\to G$ whose first $k$ main vertices are mapped to $x_0,\dots,x_{k-1}$.
--
--   These quantities make the template count visible to $k$-variable Weisfeiler–Leman refinement. For $k\ge4$, every pair and every triple of main positions avoids some coordinate, so results built on these definitions show that the round-one colour of a $k$-tuple under separate-coordinate refinement determines $E_G$ (with $t=k$), and that its round-two colour under joint refinement determines $J_G$ (with $t=k+1$). Summing over all tuples recovers $\hom(T_k,G)$ and $\hom(T_{k+1},G)$, which is how a successful choice is detected after one separate or two joint rounds.
--
--   **Formalization Note** The definitions are `tripleCount`, `MainClique`, `templateExtensions`, `templateHomsEquiv` (item 4), `extendTuple`, `faceIndex`, `extendTupleEquiv` and `jointTemplateValue`. Positions are `Fin t`, and the new position of an extended tuple is `Fin.last k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Detection.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Detection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section Detection

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

noncomputable def tripleCount (a b c : V) : ℕ :=
  Fintype.card {v : V // G.Adj v a ∧ G.Adj v b ∧ G.Adj v c}

def MainClique {t : ℕ} (z : Fin t → V) : Prop :=
  ∀ i j, i ≠ j → G.Adj (z i) (z j)

noncomputable def templateExtensions {t : ℕ} (z : Fin t → V) : ℕ :=
  if MainClique G z then
    ∏ h : Helper t, tripleCount G (z h.1.1.1.1) (z h.1.1.1.2) (z h.1.2) else 0

noncomputable def templateHomsEquiv (t : ℕ) :
    ((template t) →g G) ≃
      ((z : {z : Fin t → V // MainClique G z}) ×
        ((h : Helper t) → {v : V // G.Adj v (z.1 h.1.1.1.1) ∧
          G.Adj v (z.1 h.1.1.1.2) ∧ G.Adj v (z.1 h.1.2)})) where
  toFun f := ⟨⟨fun i => f (.inl i), fun i j hij => f.map_adj hij⟩,
    fun h => ⟨f (.inr h), f.map_adj (Or.inl rfl), f.map_adj (Or.inr (Or.inl rfl)),
      f.map_adj (Or.inr (Or.inr rfl))⟩⟩
  invFun f :=
    { toFun := fun v => match v with | .inl i => f.1.1 i | .inr h => (f.2 h).1
      map_rel' := by
        intro a b hab
        cases a with
        | inl i =>
          cases b with
          | inl j => exact f.1.2 i j hab
          | inr h =>
            rcases hab with hi | hi | hi <;> subst i
            · exact (f.2 h).2.1.symm
            · exact (f.2 h).2.2.1.symm
            · exact (f.2 h).2.2.2.symm
        | inr h =>
          cases b with
          | inl i =>
            rcases hab with hi | hi | hi <;> subst i
            · exact (f.2 h).2.1
            · exact (f.2 h).2.2.1
            · exact (f.2 h).2.2.2
          | inr h' => exact hab.elim }
  left_inv f := by apply RelHom.ext; intro v; cases v <;> rfl
  right_inv f := by rcases f with ⟨⟨z, hz⟩, f⟩; rfl

def extendTuple {k : ℕ} (x : Fin k → V) (v : V) : Fin (k + 1) → V :=
  Fin.lastCases v x

def faceIndex {k : ℕ} (i : Fin k) : Fin (k + 1) → Fin k := Fin.lastCases i id

noncomputable def jointTemplateValue {k : ℕ} (x : Fin k → V) : ℕ :=
  ∑ v : V, templateExtensions G (extendTuple x v)

def extendTupleEquiv (k : ℕ) : ((Fin k → V) × V) ≃ (Fin (k + 1) → V) where
  toFun q := extendTuple q.1 q.2
  invFun z := (fun i => z i.castSucc, z (Fin.last k))
  left_inv q := by rcases q with ⟨x, v⟩; simp [extendTuple]
  right_inv z := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [extendTuple]

end Detection

end ParityWL

end OAI


