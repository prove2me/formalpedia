-- Prove2me | Definitions.Def_PermSymQuery_Quadratic_Supplement_Encoding
-- name    : PermSymQuery_Quadratic_Supplement_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:39:32.695565+00:00
-- url     : https://prove2.me/theorems/773033fb-d557-4b79-b10d-a53443163160
-- title:
--   Uncolored hypergraph encoding $H_z$ and the invariant promise problem $F_g$
-- statement:
--   Fix integers $k\ge2$, $b$ and $m$, and put $d=2^b-1$. The vertex set is $V=X\cup A$ with data vertices $X=\{x_w:w\in\{0,1\}^b\setminus\{0^b\}\}$ and address vertices $A=\{a_1,\dots,a_b\}$, so $|V|=d+b$. Let $X^*=\{x_w:w_1=w_2=1\}$. The tree $T$ on $A$ has center $a_1$ and the three paths $(a_1,a_2)$, $(a_1,a_3,a_4)$, $(a_1,a_5,a_6,\dots,a_b)$. Data positions are given by an injective map $e:[m]\to\binom{X^*}k$.
--
--   For $z\in\{0,1\}^m$ and $E\in\binom Vk$, the hypergraph $H_z$ of (23) is
--   $$H_z(E)=\begin{cases}z_j,& E=e(j),\\ \bigvee_{x_w\in Y}w_i,& E=\{a_i\}\cup Y,\ Y\in\binom X{k-1},\\ \mathbb 1[\{a_i,a_j\}\in E(T)],& E=\{a_i,a_j\}\cup C,\ i<j,\ C\in\binom X{k-2},\\ 0,&\text{otherwise.}\end{cases}$$
--
--   Fix an identification $\sigma:V\to[N]$ of the canonical vertex set with $[N]$, and transport $H_z$ to $[N]$ by $\sigma$. For a source promise problem $g:D_g\subseteq\{0,1\}^m\to\{0,1\}$, the promise is
--   $$D_{F_g}=\{H_z^\pi: z\in D_g,\ \pi\in S_N\},$$
--   and $F_g(H)=1$ exactly when $H=H_z^\pi$ for some $z\in D_g$ and $\pi\in S_N$ with $g(z)=1$. By Lemma 6.1 this agrees with the paper's $F_g(H_z^\pi)=g(z)$ on the whole promise.
--
--   These objects are the encoding of §6 used by Lemmas 6.1 and 6.2.
--
--   **Formalization Note** Address vertex $a_{i+1}$ is `Sum.inr i` for `i : Fin b`, and bit $w_{i+1}$ is `w i`; $X^*$ is the set of data vertices whose bits `0` and `1` are both set. The cases of (23) are distinguished by the number of address vertices in $E$ (zero, one or two), which is how the paper's cases are disjoint.
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), §6.1, (23), and §6.2 definition of D_{F_g} and F_g (PDF p. 27, printed p. 25), PDF p. 25 (printed p. 23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Supplement_Hypergraph

namespace PermSymQuery.Quadratic.Supplement

/-- §6.1, PDF p.25: the data vertices `X = {x_w : w ∈ {0,1}^b \ {0^b}}`, indexed by their
nonzero binary address `w` (bit `i` is `w i`, with `i : Fin b` standing for the paper's `i+1`). -/
abbrev EncX (b : ℕ) := {w : Fin b → Bool // ∃ i, w i = true}

/-- §6.1, PDF p.25: the vertex set `V = X ∪ A` with `A = {a_1, …, a_b}`; `Sum.inr i` is the
address vertex `a_{i+1}`. It has `d + b = 2^b − 1 + b` vertices. -/
abbrev EncV (b : ℕ) := EncX b ⊕ Fin b

/-- §6.1, PDF p.25: `X* = {x_w : w_1 = w_2 = 1}` (the first two address bits are `1`). -/
def IsXStar {b : ℕ} : EncV b → Prop
  | Sum.inl x => ∀ i : Fin b, i.val < 2 → x.1 i = true
  | Sum.inr _ => False

/-- The address vertices of a vertex set, as indices in `Fin b`. -/
noncomputable def aPart {b : ℕ} (E : Finset (EncV b)) : Finset (Fin b) :=
  E.preimage Sum.inr Sum.inr_injective.injOn

/-- The data vertices of a vertex set. -/
noncomputable def xPart {b : ℕ} (E : Finset (EncV b)) : Finset (EncX b) :=
  E.preimage Sum.inl Sum.inl_injective.injOn

/-- §6.1, PDF p.25: the edges `{a_i, a_j}` (`i < j`) of the tree `T` on `A` with center `a_1`
and paths `(a_1,a_2)`, `(a_1,a_3,a_4)`, `(a_1,a_5,a_6,…,a_b)`, in 0-based indices:
`{0,1}`, `{0,2}`, `{2,3}`, `{0,4}`, `{4,5}`, …, `{b−2,b−1}`. -/
def treeEdge {b : ℕ} (i j : Fin b) : Prop :=
  (i.val = 0 ∧ (j.val = 1 ∨ j.val = 2 ∨ j.val = 4)) ∨ (i.val = 2 ∧ j.val = 3) ∨
    (4 ≤ i.val ∧ j.val = i.val + 1)

instance {b : ℕ} (i j : Fin b) : Decidable (treeEdge i j) := by
  unfold treeEdge; infer_instance

/-- Sanity checks for `b = 7`: `{a_1,a_5}`, `{a_5,a_6}`, `{a_6,a_7}` are tree edges,
`{a_2,a_3}` and `{a_4,a_5}` are not. -/
example : treeEdge (0 : Fin 7) 4 ∧ treeEdge (4 : Fin 7) 5 ∧ treeEdge (5 : Fin 7) 6 ∧
    ¬ treeEdge (1 : Fin 7) 2 ∧ ¬ treeEdge (3 : Fin 7) 4 := by decide

/-- The data positions: `e : [m] → (X* choose k)` is injective and every `e(j)` consists of
vertices of `X*` (§6.1, PDF p.25). -/
def IsDataEnumeration {b k m : ℕ} (e : Fin m → KSet (EncV b) k) : Prop :=
  Function.Injective e ∧ ∀ j, ∀ v ∈ (e j).1, IsXStar v

/-- (23), PDF p.25: the uncolored k-uniform hypergraph `H_z` on `V`:
* `H_z(E) = z_j` if `E = e(j)`;
* `H_z({a_i} ∪ Y) = ⋁_{x_w ∈ Y} w_i` for `Y` a `(k−1)`-subset of `X`;
* `H_z({a_i, a_j} ∪ C) = 1[{a_i, a_j} ∈ E(T)]` for `i < j`, `C` a `(k−2)`-subset of `X`;
* `H_z(E) = 0` otherwise. -/
noncomputable def Hz {b k m : ℕ} (e : Fin m → KSet (EncV b) k) (z : Fin m → Bool) :
    Hypergraph (EncV b) k := fun E =>
  open Classical in
  if h : ∃ j, e j = E then z h.choose
  else if (aPart E.1).card = 1 then
    decide (∃ i ∈ aPart E.1, ∃ x ∈ xPart E.1, x.1 i = true)
  else if (aPart E.1).card = 2 then
    decide (∃ i ∈ aPart E.1, ∃ j ∈ aPart E.1, i < j ∧ treeEdge i j)
  else false

/-- `H_z` on `[N]`, through a fixed identification `σ : V ≃ [N]` of the canonical vertex set
with `[N]` (§6.2, PDF p.27): `(HzFin σ e z)(σ(E)) = H_z(E)`. -/
noncomputable def HzFin {b k m N : ℕ} (σ : EncV b ≃ Fin N) (e : Fin m → KSet (EncV b) k)
    (z : Fin m → Bool) : Hypergraph (Fin N) k :=
  fun E => Hz e z (KSet.map σ.symm E)

/-- §6.2, PDF p.27: the promise `D_{F_g} = {H_z^π : z ∈ D_g, π ∈ S_N}`. -/
def FgDomain {b k m N : ℕ} (σ : EncV b ≃ Fin N) (e : Fin m → KSet (EncV b) k)
    (Dg : Set (Fin m → Bool)) : Set (Hypergraph (Fin N) k) :=
  {H | ∃ z ∈ Dg, ∃ π : Equiv.Perm (Fin N), H = relabel (HzFin σ e z) π}

/-- §6.2, PDF p.27: `F_g(H_z^π) = g(z)`, written as "`H = H_z^π` for some `z ∈ D_g` and `π`
with `g(z) = 1`"; by Lemma 6.1 this agrees with `g(z)` on the whole promise. -/
noncomputable def Fg {b k m N : ℕ} (σ : EncV b ≃ Fin N) (e : Fin m → KSet (EncV b) k)
    (Dg : Set (Fin m → Bool)) (g : (Fin m → Bool) → Bool) : Hypergraph (Fin N) k → Bool :=
  open Classical in
  fun H => decide (∃ z ∈ Dg, ∃ π : Equiv.Perm (Fin N), H = relabel (HzFin σ e z) π ∧ g z = true)

end PermSymQuery.Quadratic.Supplement


