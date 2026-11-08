-- Prove2me | Definitions.Def_GenCountSampleLLL_insertionChain
-- name    : GenCountSampleLLL_insertionChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:50:49.281816+00:00
-- url     : https://prove2.me/theorems/8831b692-7dfe-41cf-abbe-e1194442a0ce
-- title:
--   The insertion chain: state space $\mathsf S(\mathcal D,a)$, kernels $P_{\mathcal D,a}$ and $K^\beta_{\mathcal D,a}$ (Algorithm 3), weights $w$, $\tilde w$, $M$, $\pi$, $\mu^\pm$, edges, capacities
-- statement:
--   Fix $a\in\mathcal D\subseteq\mathcal C$. The state space $\mathsf S(\mathcal D,a)$ (§5.1) has an input state $\mathsf I(\sigma)$ for $\sigma\in\mathrm{Good}(\mathcal D^-)$, an output state $\mathsf O(\sigma)$ for $\sigma\in\mathrm{Good}(\mathcal D)$, a tree state $\mathsf T_{\mathcal T}(\sigma)$ for $\mathcal T\in\mathfrak T_{\mathcal D,a}$ and $\sigma\in E^\star_{\mathcal T}$, layer states $\mathsf L^e_i(\sigma)$ for $e=(\mathcal T,z)$, $z\in E_{\mathcal T}$, $0\le i\le\ell(\mathcal T)$, $\sigma\in\mathrm{Good}(\mathcal D_{\mathcal T,i})$, and, for $1\le i\le\ell(\mathcal T)$, the internal states $(e,i,X)$ of a copy of $\mathsf S(\mathcal D_{\mathcal T,i},b_{\mathcal T,i})$, whose input and output states are identified with the layers $i-1$ and $i$ by the embedding $\psi_{e,i}$.
--
--   The kernel $P=P_{\mathcal D,a}$ (§5.2) holds with probability $1/2$ and otherwise applies FORWARDS, BACKWARDS or RESET, each with probability $1/6$, as in Algorithm 3: resampling $U_{\mathcal T}$ at a tree state, the pairing $\iota_\sigma$, moves along a corridor through the smaller copies, a fresh list $\mathbf L$ at an input state and the conditioned list $\mathbf L^e$ at a last layer. $K=K^\beta_{\mathcal D,a}$ agrees with $P$ except at the outer output states, where
--   $$
--   K(\mathsf O(\sigma),\mathsf I(\sigma))=\beta/6,\qquad K(\mathsf O(\sigma),\mathsf O(\sigma))=1-\beta/6.
--   $$
--   The weights are $w(\mathsf I(\sigma))=w(\mathsf O(\sigma))=w(\mathsf T_{\mathcal T}(\sigma))=\nu(\sigma)$, $w(\mathsf L^e_i(\sigma))=\nu_{U_{\mathcal T}}(z)\nu(\sigma)$, $w((e,i,X))=\nu_{U_{\mathcal T}}(z)w(X)$; $\tilde w=w/\beta$ on the outer output states and $w$ elsewhere, $M=\sum_X\tilde w(X)$, $\pi=\tilde w/M$. The input and target distributions are $\mu^-(\mathsf I(\sigma))=\mu_{\mathcal D^-}(\sigma)$ and $\mu^+(\mathsf O(\sigma))=\mu_{\mathcal D}(\sigma)$. An edge is a pair of distinct states with $P(X,Y)>0$, and $\mathrm{cap}(X,Y)=w(X)P(X,Y)$.
--
--   This chain is the engine of the sampler (Proposition 2.2).
--
--   **Formalization Note** A state is the list of the labels $(e,i)$ of the copies containing it, outermost first, and a base state of the innermost instance (p.30). A copy's input or output state under a label is not a state: it is its parent's layer. Transition probabilities are computed exactly from the laws of the list experiment and of $\nu$. $z\in E_{\mathcal T}$ is stored as a full assignment set to $0$ outside $U_{\mathcal T}$.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), §5.1–§5.2, pp.17–20 (Algorithm 3, p.20); §6.2–§6.3, pp.22–25

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace GenCountSampleLLL

noncomputable section

open Classical

/-!
# The insertion chain: state space `S(D, a)`, kernels `P = P_{D,a}` and `K = K^β_{D,a}`, weights

Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671
(held file sha256 cd449f83…), §5.1–§5.2 (pp.17–20), Algorithm 3 (p.20), §6.2–§6.3 (pp.22–25).

Algorithm 3, `Step(D, a, s; rule)`, p.20:
```
1 if s = I(σ) then
2   if rule = FORWARDS then
3     if σ ∉ Ba then return O(σ)
4     return T{a}(σ)
5   else if rule = RESET then
6     Generate L
7     if L ≠ ∅ then
8       Choose e = (T, z) uniformly from L
9       return Le_ℓ(T)(σ)
10 else if s = O(σ) then
11   if rule = BACKWARDS then return I(σ)
12 else if s = TT(σ) then
13   if rule = FORWARDS then
14     Write σ = (y, z) and draw u ∼ νUT
15     Set e = (T, z)
16     return Le_0(y, u)
17   else if rule = BACKWARDS then
18     if Q(σ) = {a} then return I(σ)
19     return Tισ(T)(σ)
20 else if s = Le_i(σ) then
21   if rule = BACKWARDS then
22     if i > 0 then return Le_{i−1}(σ)
23     Write σ = (y, u)
24     return TT(y, z)
25   else if i < ℓ(T) then
26     X′ ← Step(DT,i+1, bT,i+1, I(σ); rule)
27     return ψe,i+1(X′)
28   else if rule = FORWARDS then
29     Generate Le
30     Choose an entry e′ uniformly from this list
31     if e′ = e then return I(σ)
32 else if s = (e, i, X) then
33   X′ ← Step(DT,i, bT,i, X; rule)
34   return ψe,i(X′)
35 return s    ▷ In all other cases, the state is unchanged.
```
Under `P` the chain stays put with probability `1/2`, and otherwise applies one of the three rules,
chosen uniformly (p.19). `K^β` changes only the outer output states:
`K(O(σ), I(σ)) = β/6`, `K(O(σ), O(σ)) = 1 − β/6` (p.19).

**Formalization Note.** A state is a list of corridor labels `(T, z, i)`, outermost first (the
copies `(e, i)` containing it, `e = (T, z)`), and a base state `I(σ)`, `O(σ)`, `T_T(σ)` or
`L^e_i(σ)` of the innermost instance (p.30: "A state consists of its assignment, its type, and the
labels (e, i) of the copies containing it"). The embedding `ψ_{e,i}` prepends the label, except
that the input and output states of a copy are its parent's layers `i − 1` and `i` (p.18); a
copy's input or output state under a label is therefore not a state. The finite set
`states D.card D a` is built by recursion on `|D|`, exactly as in §5.1, and `S D a` is its
subtype. A label `z ∈ E_T ⊆ Ω_{U_T}` is a full assignment normalized to `0` outside `U_T`.
Transition probabilities are computed exactly from the experiment laws: the probability that a
rule leads to `Y` is a function `St → ℝ`, and `push e` transports such a function from a copy to
its parent along `ψ`. `P` and `K` are matrices indexed by `S D a`. Edges and capacities follow
p.23 and p.25: an edge is a pair of distinct states `X, Y` with `P(X, Y) > 0`, and
`cap(X, Y) = w(X) P(X, Y)`.
-/

/-- The three rules of the insertion chain. -/
inductive Rule
  | fwd
  | bwd
  | reset

namespace Inst

variable (I : Inst)

/-- The base states of an instance: `I(σ)`, `O(σ)`, `T_T(σ)` and the layer state `L^e_i(σ)`,
`e = (T, z)`. -/
inductive Base (I : Inst) : Type
  | inp (σ : I.Assign)
  | out (σ : I.Assign)
  | tree (T : Finset (Fin I.m)) (σ : I.Assign)
  | lay (T : Finset (Fin I.m)) (z : I.Assign) (i : ℕ) (σ : I.Assign)

/-- A corridor label `(e, i) = ((T, z), i)`. -/
abbrev Label : Type := Finset (Fin I.m) × I.Assign × ℕ

/-- A state: the labels of the copies containing it, outermost first, and its base state in the
innermost instance. -/
structure St (I : Inst) : Type where
  /-- The labels `(e, i)` of the copies containing the state, outermost first. -/
  labels : List I.Label
  /-- The base state in the innermost copy. -/
  base : I.Base

/-- The point mass at `X`, as a function of the resulting state. -/
def dirac (X : I.St) : I.St → ℝ := fun Y => if Y = X then 1 else 0

/-- `X` is an input or output state of its own instance (no labels). -/
def isIO (X : I.St) : Prop :=
  X.labels = [] ∧ ((∃ σ, X.base = Base.inp σ) ∨ ∃ σ, X.base = Base.out σ)

/-- The state space of §5.1, by recursion with fuel: input states, output states, tree states,
layer states, and the internal states `(e, i, X)` of the smaller copies `S(D_{T,i}, b_{T,i})`. -/
def states : ℕ → Finset (Fin I.m) → Fin I.m → Finset I.St
  | 0, _, _ => ∅
  | k + 1, D, a =>
    (I.Good (D.erase a)).image (fun σ => ⟨[], Base.inp σ⟩) ∪
    (I.Good D).image (fun σ => ⟨[], Base.out σ⟩) ∪
    (I.twoTrees D a).biUnion (fun T => (I.Estar D a T).image fun σ => ⟨[], Base.tree T σ⟩) ∪
    (I.twoTrees D a).biUnion (fun T => (I.labelsE D a T).biUnion fun z =>
      (Finset.range (I.ell D a T + 1)).biUnion fun i =>
        (I.Good (I.DTi D a T i)).image fun σ => ⟨[], Base.lay T z i σ⟩) ∪
    (I.twoTrees D a).biUnion (fun T => (I.labelsE D a T).biUnion fun z =>
      (Finset.Icc 1 (I.ell D a T)).biUnion fun i =>
        ((states k (I.DTi D a T i) (I.bT D a T i)).filter fun X => ¬ I.isIO X).image
          fun X => ⟨(T, z, i) :: X.labels, X.base⟩)

/-- `S(D, a)`, the state space of the insertion chain (§5.1, p.17). -/
abbrev S (D : Finset (Fin I.m)) (a : Fin I.m) : Type := {X // X ∈ I.states D.card D a}

/-- The inverse of `ψ_{e,i}` (p.18) on the parent's states, for the label `(T, z, i)`: the copy's
state that `ψ_{e,i}` maps to `Y`, if any. -/
def psiInv (l : I.Label) : I.St → Option I.St
  | ⟨l' :: ls, b⟩ => if l' = l then some ⟨ls, b⟩ else none
  | ⟨[], Base.lay T z j σ⟩ =>
    if T = l.1 ∧ z = l.2.1 ∧ j + 1 = l.2.2 then some ⟨[], Base.inp σ⟩
    else if T = l.1 ∧ z = l.2.1 ∧ j = l.2.2 then some ⟨[], Base.out σ⟩
    else none
  | _ => none

/-- The law of `ψ_{e,i}(X′)` when `X′` has law `f` in the copy with label `l = (T, z, i)`. -/
def push (l : I.Label) (f : I.St → ℝ) : I.St → ℝ := fun Y =>
  match I.psiInv l Y with
  | some X => f X
  | none => 0

/-- The expected value `E[f(L)]` of a function of the fresh list `L` of `(D, a)`. -/
def expL (D : Finset (Fin I.m)) (a : Fin I.m)
    (f : Finset (Finset (Fin I.m) × I.Assign) → ℝ) : ℝ :=
  ∑ ω, (I.expLaw ω).toReal * f (I.Llist D a ω)

/-- `E[1/|L_e|]` for the conditioned list `L_e`, `e = (T, z)` (p.19). -/
def retProb (D : Finset (Fin I.m)) (a : Fin I.m) (e : Finset (Fin I.m) × I.Assign) : ℝ :=
  ∑ ω, (I.expLaw ω).toReal / ((I.Le D a e ω).card : ℝ)

/-- Algorithm 3, lines 1–9: the law of `Step(D, a, I(σ); rule)`. -/
def iRule (D : Finset (Fin I.m)) (a : Fin I.m) (σ : I.Assign) : Rule → I.St → ℝ
  | Rule.fwd => if I.bad a σ then I.dirac ⟨[], Base.tree {a} σ⟩ else I.dirac ⟨[], Base.out σ⟩
  | Rule.bwd => I.dirac ⟨[], Base.inp σ⟩
  | Rule.reset => fun Y => I.expL D a fun L =>
      if L = ∅ then I.dirac ⟨[], Base.inp σ⟩ Y
      else ∑ e ∈ L, I.dirac ⟨[], Base.lay e.1 e.2 (I.ell D a e.1) σ⟩ Y / (L.card : ℝ)

/-- Algorithm 3 at a base state of the instance `(D, a)` (no labels): lines 1–31 and 35. -/
def baseRule (D : Finset (Fin I.m)) (a : Fin I.m) : I.Base → Rule → I.St → ℝ
  | Base.inp σ, r => I.iRule D a σ r
  | Base.out σ, Rule.bwd => I.dirac ⟨[], Base.inp σ⟩
  | Base.out σ, _ => I.dirac ⟨[], Base.out σ⟩
  | Base.tree T σ, Rule.fwd => fun Y => ∑ τ, I.nuA τ *
      I.dirac ⟨[], Base.lay T (I.restr (I.UT D T) σ) 0 (I.merge (I.UT D T) τ σ)⟩ Y
  | Base.tree T σ, Rule.bwd =>
    if I.Qv D σ = {a} then I.dirac ⟨[], Base.inp σ⟩
    else I.dirac ⟨[], Base.tree (I.iota D a T σ) σ⟩
  | Base.tree T σ, Rule.reset => I.dirac ⟨[], Base.tree T σ⟩
  | Base.lay T z i σ, Rule.bwd =>
    if 0 < i then I.dirac ⟨[], Base.lay T z (i - 1) σ⟩
    else I.dirac ⟨[], Base.tree T (I.merge (I.UT D T) z σ)⟩
  | Base.lay T z i σ, r =>
    if i < I.ell D a T then
      I.push (T, z, i + 1) (I.iRule (I.DTi D a T (i + 1)) (I.bT D a T (i + 1)) σ r)
    else
      match r with
      | Rule.fwd => fun Y => I.retProb D a (T, z) * I.dirac ⟨[], Base.inp σ⟩ Y +
          (1 - I.retProb D a (T, z)) * I.dirac ⟨[], Base.lay T z i σ⟩ Y
      | _ => I.dirac ⟨[], Base.lay T z i σ⟩

/-- Algorithm 3, `Step(D, a, s; rule)`, as the law of the resulting state; lines 32–34 recurse
into the copy named by the outermost label. -/
def stepRule : Finset (Fin I.m) → Fin I.m → List I.Label → I.Base → Rule → I.St → ℝ
  | D, a, [], b, r => I.baseRule D a b r
  | D, a, (T, z, i) :: ls, b, r =>
    I.push (T, z, i) (stepRule (I.DTi D a T i) (I.bT D a T i) ls b r)

/-- The auxiliary kernel `P = P_{D,a}` (p.19): hold with probability `1/2`, otherwise apply
FORWARDS, BACKWARDS or RESET, each with probability `1/6`. -/
def Pker (D : Finset (Fin I.m)) (a : Fin I.m) : Matrix (I.S D a) (I.S D a) ℝ := fun X Y =>
  (1 / 2 : ℝ) * (if X = Y then 1 else 0) +
    (1 / 6 : ℝ) * (I.stepRule D a X.1.labels X.1.base Rule.fwd Y.1 +
      I.stepRule D a X.1.labels X.1.base Rule.bwd Y.1 +
      I.stepRule D a X.1.labels X.1.base Rule.reset Y.1)

/-- `X` is an outer output state `O(σ)`, `σ ∈ Good(D)`. -/
def isOut (X : I.St) : Prop := ∃ σ, X = ⟨[], Base.out σ⟩

/-- The kernel `K = K^β_{D,a}` (p.19): `K(O(σ), I(σ)) = β/6`, `K(O(σ), O(σ)) = 1 − β/6` at the
outer output states, and `K = P` at every other state. -/
def Kker (β : ℝ) (D : Finset (Fin I.m)) (a : Fin I.m) : Matrix (I.S D a) (I.S D a) ℝ :=
  fun X Y =>
    match X.1 with
    | ⟨[], Base.out σ⟩ =>
      (if Y.1 = ⟨[], Base.inp σ⟩ then β / 6 else 0) + (if X = Y then 1 - β / 6 else 0)
    | _ => I.Pker D a X Y

/-- The weights `w` of §6.2 (p.22), by recursion on the labels: `w(I(σ)) = w(O(σ)) =
w(T_T(σ)) = ν(σ)`, `w(L^e_i(σ)) = ν_{U_T}(z) ν(σ)`, `w((e, i, X)) = ν_{U_T}(z) w(X)`. -/
def wt : Finset (Fin I.m) → Fin I.m → List I.Label → I.Base → ℝ
  | _, _, [], Base.inp σ => I.nuA σ
  | _, _, [], Base.out σ => I.nuA σ
  | _, _, [], Base.tree _ σ => I.nuA σ
  | D, _, [], Base.lay T z _ σ => I.nuU (I.UT D T) z * I.nuA σ
  | D, a, (T, z, i) :: ls, b => I.nuU (I.UT D T) z * wt (I.DTi D a T i) (I.bT D a T i) ls b

/-- `w(X)` for `X ∈ S(D, a)`. -/
def w (D : Finset (Fin I.m)) (a : Fin I.m) (X : I.S D a) : ℝ :=
  I.wt D a X.1.labels X.1.base

/-- `w̃(X) = w(X)/β` at the outer output states and `w(X)` elsewhere (p.22). -/
def wtil (β : ℝ) (D : Finset (Fin I.m)) (a : Fin I.m) (X : I.S D a) : ℝ :=
  if I.isOut X.1 then I.w D a X / β else I.w D a X

/-- `M = Σ_{X ∈ S(D,a)} w̃(X)` (p.22). -/
def Mtot (β : ℝ) (D : Finset (Fin I.m)) (a : Fin I.m) : ℝ := ∑ X, I.wtil β D a X

/-- `π(X) = w̃(X)/M` (Lemma 6.4, p.22). -/
def piDist (β : ℝ) (D : Finset (Fin I.m)) (a : Fin I.m) (X : I.S D a) : ℝ :=
  I.wtil β D a X / I.Mtot β D a

/-- The input distribution `µ⁻(I(σ)) = µ_{D⁻}(σ)`, zero elsewhere (p.18). -/
def muMinus (D : Finset (Fin I.m)) (a : Fin I.m) (X : I.S D a) : ℝ :=
  match X.1 with
  | ⟨[], Base.inp σ⟩ => I.mu (D.erase a) σ
  | _ => 0

/-- The target distribution `µ⁺(O(σ)) = µ_D(σ)`, zero elsewhere (p.18). -/
def muPlus (D : Finset (Fin I.m)) (a : Fin I.m) (X : I.S D a) : ℝ :=
  match X.1 with
  | ⟨[], Base.out σ⟩ => I.mu D σ
  | _ => 0

/-- `{X, Y}` is an edge: distinct states connected by the transition rules, `P(X, Y) > 0`
(p.23). -/
def IsEdge (D : Finset (Fin I.m)) (a : Fin I.m) (X Y : I.S D a) : Prop :=
  X ≠ Y ∧ 0 < I.Pker D a X Y

/-- The capacity `cap(X, Y) = w(X) P(X, Y)` (p.25). -/
def cap (D : Finset (Fin I.m)) (a : Fin I.m) (X Y : I.S D a) : ℝ :=
  I.w D a X * I.Pker D a X Y

end Inst

end

end GenCountSampleLLL


