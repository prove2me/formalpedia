-- Prove2me | Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Construction
-- name    : AlgoPrinciplesMulticlass_NoEnvelope_Construction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:28:12.707493+00:00
-- url     : https://prove2.me/theorems/c3564b56-0586-4a2e-8003-bdc81787e0ed
-- title:
--   The trees T_d, the domain X, the labels Y, the class H = {h_{d,b,u}}, the improper learner A and Conditions 1–2 (§3.1)
-- statement:
--   **Trees and domain.** For $d\ge1$, $T_d$ is the infinite complete $2^d$-ary tree whose children are indexed by $\{0,1\}^d$: a node at depth $k$ is a sequence $v=(b_1,\dots,b_k)$ with $b_i\in\{0,1\}^d$, the root is $\varnothing$, and $v$ has the children $(v,b)$, $b\in\{0,1\}^d$. For every $d\ge1$, every node $v$ of $T_d$ and every $j\in[d]$ there is a domain point $x_{d,v,j}$, all distinct, and
--   $$X=\bigcup_{d\ge1}\bigcup_{v\in T_d}\{x_{d,v,j}: j\in[d]\}.$$
--   The **block** of $v$ is $E_{d,v}=\{x_{d,v,j}:j\in[d]\}$.
--
--   **Hypotheses and labels.** For $d\ge1$, $\ell\ge1$, $b=(b_1,\dots,b_\ell)\in(\{0,1\}^d)^\ell$ and $u=(u_1,\dots,u_\ell)\in[d]^\ell$,
--   $$h_{d,b,u}(x)=\begin{cases} b_i(u_i) & \text{if } x=x_{d,(b_1,\dots,b_{i-1}),u_i}\text{ for some } i\in[\ell],\\ \alpha_{d,b,u} & \text{otherwise,}\end{cases}$$
--   where $b_i(u_i)$ is the $u_i$-th coordinate of $b_i$. The labels $\alpha_{d,b,u}$ (**private labels**) are pairwise distinct and distinct from the **public labels** $0,1$; $Y=\{0,1\}\cup\{\alpha_{d,b,u}\}$ and $\mathcal H=\{h_{d,b,u}: d\ge1,\ \ell\ge1,\ b,\ u\}$. A hypothesis emits its private label at every point outside its $\ell$ public points, in every tree.
--
--   **The improper learner $A$** (p. 17). Given a sample $S$: (1) if a private label $\alpha_{d,b,u}$ appears in $S$, output $h_{d,b,u}$; (2) otherwise choose an example $(x_{d,v,j},y)$ with $|v|$ maximal, write $v=(b_1,\dots,b_{i^*-1})$, and output $h_S$ with $h_S(x_{d,v,j})=y$, $h_S(x_{d,(b_1,\dots,b_{i-1}),j'})=b_i(j')$ for $i<i^*$ and $j'\in[d]$, and $h_S(x)=0$ elsewhere. Where the page leaves the choice open, the formal learner takes the first private label in sample order, the first example of maximal depth in sample order, and the constant $0$ on the empty sample.
--
--   **Conditions 1 and 2** (Lemma 3.3, p. 18). A vector $c\in\{0,1\}^d$ is identified with the function $x_{d,v,j}\mapsto c(j)$ on $E_{d,v}$, and $F{\restriction}E_{d,v}$ **contains** $c$ if some $f\in F$ has $f(x_{d,v,j})=c(j)$ for all $j\in[d]$. For a class $F\subseteq Y^X$: *Condition 1* says some node $v\in T_d$ has every $c\in\{0,1\}^d$ contained in $F{\restriction}E_{d,v}$; *Condition 2* says there is an infinite sequence $b_1,b_2,\dots\in\{0,1\}^d$ with $b_i\notin F{\restriction}E_{d,(b_1,\dots,b_{i-1})}$ for every $i\ge1$.
--
--   **Formalization Note.** `Pt` has fields `d`, `v : List (Fin d → Bool)` (the node, root `[]`) and `j : Fin d`; $\{0,1\}$ is `Bool` (`false = 0`) and $[d]$ is `Fin d` (0-based); `d = 0` contributes no point. `Param` holds `d`, `ℓ ≥ 1`, `b : Fin ℓ → Fin d → Bool`, `u : Fin ℓ → Fin d` (0-based: the public point of index `i` is `⟨d, (List.ofFn b).take i, u i⟩` with label `b i (u i)`). `Label` is the inductive type `pub (c : Bool) | priv (p : Param)`, so private labels are distinct by construction. `hyp p` is $h_{d,b,u}$, `H = Set.range hyp`, `refLearner` is $A$, `reconstruct` is $h_S$, `block d v` is $j\mapsto x_{d,v,j}$, and Condition 2's sequence is `b : ℕ → Fin d → Bool` with `b 0` $=b_1$.
-- source:
--   Asilis, Dughmi, Sharan, Sun, Teng, Wang, Algorithmic Principles For Multiclass Learning Are Hard To Come By, STOC 2027 submission (manuscript sha256 03e91e8f…), p. 16 (Construction), p. 17 (An improper learner), p. 18 (Lemma 3.3)

import Mathlib
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_PAC

namespace AlgoPrinciplesMulticlass.NoEnvelope

/-!
# The construction of §3.1 (pp. 16–18)

Asilis, Dughmi, Sharan, Sun, Teng, Wang, *Algorithmic Principles For Multiclass Learning Are
Hard To Come By*, STOC 2027 submission (manuscript sha256 03e91e8f…), pp. 16–18.

* For `d ≥ 1`, `T_d` is the complete `2^d`-ary tree: a node at depth `k` is a list
  `[b₁, …, b_k]` of vectors `bᵢ : Fin d → Bool` (`{0,1}^d`, with `false = 0`, `true = 1`); the
  root is `[]`. Coordinates `j ∈ [d]` are `Fin d` (0-based).
* The domain `X` (`Pt`) has one point `x_{d,v,j}` for every `d`, every node `v` of `T_d` and
  every `j : Fin d` (all distinct; `d = 0` contributes no point since `Fin 0` is empty). The block
  of `v` is `E_{d,v} = {x_{d,v,j} : j ∈ [d]}`.
* A parameter `(d, ℓ, b, u)` (`Param`) has `ℓ ≥ 1`, `b = (b₁, …, b_ℓ)`, `u = (u₁, …, u_ℓ)`
  (0-based: `b i`, `u i` for `i : Fin ℓ`). Its `i`-th public point (0-based `i`) is
  `x_{d,(b₁,…,b_i),u_{i+1}}`, the point `u_{i+1}` of the block at depth `i` on the path.
* Labels `Y` (`Label`) are the public labels `pub false = 0`, `pub true = 1` and one private
  label `priv p = α_{d,b,u}` per parameter; private labels are pairwise distinct and distinct
  from the public ones (constructors of an inductive type).
* `hyp p = h_{d,b,u}` labels its public points by `bᵢ(uᵢ)` and every other point of `X` (in
  every tree) by `α_{d,b,u}`; `H = {h_{d,b,u}}`.
-/

/-- The domain `X`: the point `x_{d,v,j}` with `v` a node of `T_d` (a list of vectors in
`{0,1}^d`, root `[]`) and `j ∈ [d]` (0-based). -/
structure Pt where
  /-- the tree index `d` -/
  d : ℕ
  /-- the node `v = (b₁, …, b_k)` of `T_d` -/
  v : List (Fin d → Bool)
  /-- the coordinate `j` within the block of `v` -/
  j : Fin d

/-- A hypothesis parameter `(d, b, u)` with path length `ℓ ≥ 1`, `b ∈ ({0,1}^d)^ℓ`,
`u ∈ [d]^ℓ` (0-based indices). -/
structure Param where
  /-- the tree index -/
  d : ℕ
  /-- the path length `ℓ` -/
  ℓ : ℕ
  /-- `ℓ ≥ 1` -/
  one_le : 1 ≤ ℓ
  /-- the path vectors `b₁, …, b_ℓ` -/
  b : Fin ℓ → Fin d → Bool
  /-- the chosen coordinates `u₁, …, u_ℓ` -/
  u : Fin ℓ → Fin d

/-- The label set `Y = {0, 1} ∪ {α_{d,b,u}}`. -/
inductive Label where
  /-- a public label `0 = pub false`, `1 = pub true` -/
  | pub (c : Bool)
  /-- the private label `α_{d,b,u}` of the parameter `p = (d, b, u)` -/
  | priv (p : Param)

/-- The block `E_{d,v}` of the node `v` of `T_d`, as the sequence `j ↦ x_{d,v,j}`. -/
def block (d : ℕ) (v : List (Fin d → Bool)) : Fin d → Pt :=
  fun j => ⟨d, v, j⟩

/-- The `i`-th public point of `h_{d,b,u}` (0-based `i`): `x_{d,(b₁,…,b_i),u_{i+1}}`. -/
def Param.publicPoint (p : Param) (i : Fin p.ℓ) : Pt :=
  ⟨p.d, (List.ofFn p.b).take i, p.u i⟩

open Classical in
/-- The hypothesis `h_{d,b,u}`: `bᵢ(uᵢ)` at its `i`-th public point, `α_{d,b,u}` everywhere else.
(The index `i` of a public point is unique: it is the depth of the point's node.) -/
noncomputable def hyp (p : Param) : Pt → Label := fun x =>
  if h : ∃ i : Fin p.ℓ, x = p.publicPoint i then
    Label.pub (p.b h.choose (p.u h.choose))
  else Label.priv p

/-- The hypothesis class `H = {h_{d,b,u} : d ≥ 1, ℓ ≥ 1, b, u}`. -/
def H : Set (Pt → Label) :=
  Set.range hyp

/-- The parameter of a private label, if any. -/
def Label.privParam : Label → Option Param
  | .pub _ => none
  | .priv p => some p

open Classical in
/-- The classifier `h_S` of step 2 of the learner (p. 17), built from the reference example
`(x_{d,v,j}, y)`: it returns `y` at `x_{d,v,j}`, `bᵢ(j')` at `x_{d,(b₁,…,b_{i−1}),j'}` for every
proper prefix `(b₁,…,b_{i−1})` of `v = (b₁,…,b_{i*−1})` and every `j'`, and `0` elsewhere. -/
noncomputable def reconstruct (r : Pt) (y : Label) : Pt → Label := fun x =>
  if x = r then y
  else if h : x.d = r.d then
    if hp : (h ▸ x.v : List (Fin r.d → Bool)) <+: r.v ∧ x.v.length < r.v.length then
      Label.pub ((r.v.get ⟨x.v.length, hp.2⟩) (h ▸ x.j))
    else Label.pub false
  else Label.pub false

/-- The improper learner `A` of p. 17, made total.
1. If a private label `α_{d,b,u}` appears in `S`, output `h_{d,b,u}` (the first private label in
   sample order, if several appear).
2. Otherwise output `h_S` built from an example `(x_{d,v,j}, y)` with `|v|` maximal (the first
   such example in sample order); on the empty sample output the constant `0`. -/
noncomputable def refLearner : Learner Pt Label := fun m S =>
  match (List.finRange m).findSome? (fun i => (S i).2.privParam) with
  | some p => hyp p
  | none =>
    match (List.finRange m).argmax (fun i => (S i).1.v.length) with
    | some i => reconstruct (S i).1 (S i).2
    | none => fun _ => Label.pub false

/-- `F↾E_{d,v}` contains the vector `c ∈ {0,1}^d`, viewed as the function `x_{d,v,j} ↦ c(j)`:
some `f ∈ F` has `f(x_{d,v,j}) = c(j)` for every `j ∈ [d]`. -/
def RealizesOnBlock (F : Set (Pt → Label)) (d : ℕ) (v : List (Fin d → Bool))
    (c : Fin d → Bool) : Prop :=
  ∃ f ∈ F, ∀ j : Fin d, f (block d v j) = Label.pub (c j)

/-- Condition 1 of Lemma 3.3 (p. 18): some node `v ∈ T_d` has every `c ∈ {0,1}^d` realized on
its block by some `f_c ∈ F`. -/
def Condition1 (F : Set (Pt → Label)) (d : ℕ) : Prop :=
  ∃ v : List (Fin d → Bool), ∀ c : Fin d → Bool, RealizesOnBlock F d v c

/-- Condition 2 of Lemma 3.3 (p. 18): an infinite sequence `b₁, b₂, …` (0-based `b 0, b 1, …`)
with `b_i ∉ F↾E_{d,(b₁,…,b_{i−1})}` for every `i ≥ 1`. -/
def Condition2 (F : Set (Pt → Label)) (d : ℕ) : Prop :=
  ∃ b : ℕ → Fin d → Bool, ∀ i : ℕ,
    ¬ RealizesOnBlock F d (List.ofFn fun k : Fin i => b k) (b i)

end AlgoPrinciplesMulticlass.NoEnvelope


