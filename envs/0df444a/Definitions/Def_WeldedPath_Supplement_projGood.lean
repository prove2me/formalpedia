-- Prove2me | Definitions.Def_WeldedPath_Supplement_projGood
-- name    : WeldedPath_Supplement_projGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:16:24.62394+00:00
-- url     : https://prove2.me/theorems/69482780-58b9-4e63-ad44-1dc6c63db08c
-- title:
--   The good space and its projector $\Pi^{\mathrm{good}}_t$, and $\eta^{\mathrm{step}}_t$ (§4.1, (61))
-- statement:
--   Let $V_{\mathrm{mid}}=\{v:n-l<\mathrm{col}(v)<n+l\}$, $V_{\mathrm{bd}}=\mathrm{col}(n-l-1)\cup\mathrm{col}(n-l)\cup\mathrm{col}(n+l)\cup\mathrm{col}(n+l+1)$ and $V_{\mathrm{weld}}=\mathrm{col}(n)\cup\mathrm{col}(n+1)$. For $e=e_\alpha(u)$ and $b=b_{\mathrm{edge}}(e)\in B_{\mathrm{edge}}$, $\kappa_\alpha(u,v)=1/|E_b|$ if $u=\mathrm{tail}(e)$ and $v$ is the head of an edge of $E_b$, or $u=\mathrm{head}(e)$ and $v$ is the tail of an edge of $E_b$; otherwise $\kappa_\alpha(u,v)=0$.
--
--   An **abstract forest** $H=(U,E(H),\mathrm{Color}_H,\lambda_H)$ has a finite vertex set $U$, a forest $E(H)$, a proper edge coloring and an injective partial labeling $\lambda_H:U\rightharpoonup[M]$, and each component has a label or an edge. For an **assignment** $\phi:U\to[M]$ an edge is a **weld** if both endpoints go to $V_{\mathrm{weld}}$; $C^{\mathrm{tree}}_u$ is the component of $u$ after deleting weld edges, $S^{\mathrm{fix}}_u$ adds the vertices across incident welds, and the **fixed data** is $W^{\mathrm{fix}}_u(\phi)=(C^{\mathrm{tree}}_u,\phi|_{C^{\mathrm{tree}}_u},(v,\phi(v))_{v\in S^{\mathrm{fix}}_u\setminus C^{\mathrm{tree}}_u})$. The **reference distribution** of a component $H_i$ with edges is
--   $$
--   \mu^{\mathrm{ref}}_i(\phi)=\frac{1}{Z^{\mathrm{ref}}_i\,|V_{\mathrm{mid}}\cup V_{\mathrm{bd}}|}\prod_{uv\in E(H_i)}\kappa_{\mathrm{Color}_H(uv)}(\phi(u),\phi(v)),\qquad \phi:U_i\to V_{\mathrm{mid}}\cup V_{\mathrm{bd}},
--   $$
--   normalized by $Z^{\mathrm{ref}}_i$; a single-vertex component is uniform on $[M]$, and $\mu^{\mathrm{ref}}$ is the product over components.
--
--   A **description** $D=(B,H,(u_i,w_i)_i)$ picks one vertex $u_i$ and fixed data $w_i$ per component. $\phi$ is **good** for $D$ if $\mu^{\mathrm{ref}}(\phi)>0$, $W^{\mathrm{fix}}_{u_i}(\phi)=w_i$, $\phi(U_i\setminus C^{\mathrm{tree}}_{u_i})\cap B=\emptyset$ for every $i$, and $\phi$ is injective. Such $\phi$ gives a database $I_\phi=(L_\phi,C_\phi)$: $L_\phi(\phi(u))=\lambda_H(u)$, and each edge of color $\alpha$ records $e_\alpha(\text{tail side})\mapsto e_\alpha(\text{head side})$. The **canonical good vector** is
--   $$
--   |g_D\rangle=\sum_{\phi\,\text{good for }D}\sqrt{\mu^{\mathrm{ref}}(\phi)}\;|L_\phi,C_\phi\rangle ,
--   $$
--   the **good space** is the span of the $|g_D\rangle$ with boundary $B$ and $|E(H)|+|\mathrm{Dom}(\lambda_H)|\le t$, $\Pi^{\mathrm{good}}_t(B)$ is its orthogonal projector, and $\Pi^{\mathrm{good}}_t=\Pi^{\mathrm{good}}_t(V_{\mathrm{bd}})$. Finally $(\eta^{\mathrm{step}}_t)^2=\epsilon_l+n(t+1)/N$ with $\epsilon_l=2^{-l}$, $N=2^n$.
--
--   The good space holds database states from which no crossing can be read; Theorem 4.9 shows that one compressed query leaves it only by $O(\eta^{\mathrm{step}}_t)$.
--
--   **Formalization Note** $U=\mathrm{Fin}\,k$; each abstract edge is stored once as $(u,v)$ with $u<v$; assignments take values in $[0,M]$ and $\mu^{\mathrm{ref}}$ vanishes off the source's domain. The fixed data $w_i$ are given as $W^{\mathrm{fix}}_{u_i}(\phi_0)$ for an assignment $\phi_0$, which spans the same space. $\Pi^{\mathrm{good}}_t$ acts as the identity on $X\otimes Y$.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), §4.1, (50)–(52) and the good space, pp.26–27; (61), p.32

import Mathlib
import Definitions.Def_WeldedPath_Supplement_cpWT

namespace WeldedPath

namespace Supplement

open QAlgorithms WeldedInstance InjDb

variable {n : ℕ}

/-! ### Vertex sets and edge weights (50) -/

/-- `V_mid = {v ∈ V_n : n − l < col(v) < n + l}` (Carolan, Childs, Coudron, Gilani, Miloschewsky,
Podder, arXiv:2611.05912 (sha256 b31400a0…), §4.1, p.26). -/
def Vmid (n l : ℕ) : Finset ℕ :=
  (Finset.range (numV n)).filter fun v => n - l < col n v ∧ col n v < n + l

/-- `V_bd = col(n − l − 1) ∪ col(n − l) ∪ col(n + l) ∪ col(n + l + 1)` (arXiv:2611.05912
(sha256 b31400a0…), p.26). -/
def Vbd (n l : ℕ) : Finset ℕ :=
  (Finset.range (numV n)).filter fun v =>
    col n v = n - l - 1 ∨ col n v = n - l ∨ col n v = n + l ∨ col n v = n + l + 1

/-- `V_weld = col(n) ∪ col(n + 1)` (arXiv:2611.05912 (sha256 b31400a0…), p.26). -/
def Vweld (n : ℕ) : Finset ℕ :=
  (Finset.range (numV n)).filter fun v => col n v = n ∨ col n v = n + 1

open Classical in
/-- `κ_α(u, v)` (50) (arXiv:2611.05912 (sha256 b31400a0…), p.26), for `e = e_α(u)`,
`b = b_edge(e)`: `1/|E_b|` if `b ∈ B_edge`, `u = tail(e)` and `v ∈ {head(g) : g ∈ E_b}`;
`1/|E_b|` if `b ∈ B_edge`, `u = head(e)` and `v ∈ {tail(g) : g ∈ E_b}`; `0` otherwise. -/
noncomputable def kappa (l : ℕ) (G : WeldedInstance n) (α : Fin 3) (u v : ℕ) : ℝ :=
  match permData l G u α with
  | some ⟨b, _, isTail⟩ =>
    if (isTail = true ∧ v ∈ (G.classEdges l b.1).image (fun g => g.head n)) ∨
        (isTail = false ∧ v ∈ (G.classEdges l b.1).image Edge.tail) then
      1 / (classSize l G b : ℝ)
    else 0
  | none => 0

/-! ### Abstract forests -/

/-- An abstract forest `H = (U, E(H), Color_H, λ_H)` (arXiv:2611.05912 (sha256 b31400a0…), p.26),
with abstract vertex set `U = Fin k`.

**Formalization Note.** Each abstract edge `{u, v}` is stored once, as the pair `(u, v)` with
`u < v`; `color` is `Color_H`; `lab` is the partial labeling `λ_H : U ⇀ [M]`, with the label
`i + 1` written as the index `i : Fin M` (as in `LabelDb`). The conditions are in
`AbsForest.IsValid`. -/
structure AbsForest (n : ℕ) where
  /-- The number of abstract vertices. -/
  k : ℕ
  /-- The abstract edges `E(H)`, each as `(u, v)` with `u < v`. -/
  E : Finset (Fin k × Fin k)
  /-- The edge coloring `Color_H`. -/
  color : Fin k × Fin k → Fin 3
  /-- The partial labeling `λ_H`. -/
  lab : Fin k → Option (Fin (labelBound n))

namespace AbsForest

/-- The underlying graph of `H` on its abstract vertices. -/
def graph (H : AbsForest n) : SimpleGraph (Fin H.k) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ H.E

/-- The conditions of p.26 (arXiv:2611.05912 (sha256 b31400a0…)): the edges form a forest,
`Color_H` is a proper edge coloring, `λ_H` is injective, and every connected component has at
least one label or edge.

**Formalization Note.** A connected component without edges is a single vertex, so "every
component has a label or an edge" is "every abstract vertex is labeled or lies on an edge". -/
def IsValid (H : AbsForest n) : Prop :=
  (∀ p ∈ H.E, p.1 < p.2) ∧ H.graph.IsAcyclic ∧
  (∀ p ∈ H.E, ∀ p' ∈ H.E, p ≠ p' →
      (p.1 = p'.1 ∨ p.1 = p'.2 ∨ p.2 = p'.1 ∨ p.2 = p'.2) → H.color p ≠ H.color p') ∧
  (∀ u v i, H.lab u = some i → H.lab v = some i → u = v) ∧
  (∀ u, (H.lab u).isSome ∨ ∃ p ∈ H.E, p.1 = u ∨ p.2 = u)

/-- The number of records `|E(H)| + |Dom(λ_H)|` (arXiv:2611.05912 (sha256 b31400a0…), p.27). -/
def records (H : AbsForest n) : ℕ :=
  H.E.card + (Finset.univ.filter fun u => (H.lab u).isSome).card

open Classical in
/-- The vertex set `U_i` of the connected component of `H` containing `u`. -/
noncomputable def comp (H : AbsForest n) (u : Fin H.k) : Finset (Fin H.k) :=
  Finset.univ.filter fun v => H.graph.Reachable u v

/-- `u` is the least vertex of its connected component; the components `H_1, …, H_k` of p.27 are
indexed by these vertices. -/
def IsCompRoot (H : AbsForest n) (u : Fin H.k) : Prop :=
  ∀ v, H.graph.Reachable u v → u ≤ v

/-- The edge `p` of `H` is a weld under the assignment `ϕ`: both endpoints are placed in
`V_weld` (arXiv:2611.05912 (sha256 b31400a0…), p.26). -/
def IsWeldUnder (H : AbsForest n) (ϕ : Fin H.k → Label n) (p : Fin H.k × Fin H.k) : Prop :=
  (ϕ p.1).1 ∈ Vweld n ∧ (ϕ p.2).1 ∈ Vweld n

/-- `H` with the weld edges (under `ϕ`) removed. -/
def treeGraph (H : AbsForest n) (ϕ : Fin H.k → Label n) : SimpleGraph (Fin H.k) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ H.E ∧ ¬ H.IsWeldUnder ϕ (a, b)

open Classical in
/-- The tree component `C^tree_u`: the connected component containing `u` of `H` with the weld
edges removed (arXiv:2611.05912 (sha256 b31400a0…), p.26). -/
noncomputable def Ctree (H : AbsForest n) (ϕ : Fin H.k → Label n) (u : Fin H.k) :
    Finset (Fin H.k) :=
  Finset.univ.filter fun v => (H.treeGraph ϕ).Reachable u v

open Classical in
/-- The fixed set `S^fix_u`: `C^tree_u` and the vertices immediately across the welds incident to
`C^tree_u` (arXiv:2611.05912 (sha256 b31400a0…), p.26). -/
noncomputable def Sfix (H : AbsForest n) (ϕ : Fin H.k → Label n) (u : Fin H.k) :
    Finset (Fin H.k) :=
  H.Ctree ϕ u ∪ Finset.univ.filter fun y => ∃ p ∈ H.E, H.IsWeldUnder ϕ p ∧
    ((p.1 ∈ H.Ctree ϕ u ∧ p.2 = y) ∨ (p.2 ∈ H.Ctree ϕ u ∧ p.1 = y))

open Classical in
/-- The fixed data `W^fix_u(ϕ) = (C^tree_u, ϕ|_{C^tree_u}, (v, ϕ(v))_{v ∈ S^fix_u ∖ C^tree_u})`
(arXiv:2611.05912 (sha256 b31400a0…), p.26), as a value: the set `C^tree_u`, the graph of `ϕ` on
it, and the graph of `ϕ` on `S^fix_u ∖ C^tree_u`. -/
noncomputable def Wfix (H : AbsForest n) (ϕ : Fin H.k → Label n) (u : Fin H.k) :
    Finset (Fin H.k) × Finset (Fin H.k × ℕ) × Finset (Fin H.k × ℕ) :=
  (H.Ctree ϕ u, (H.Ctree ϕ u).image fun v => (v, (ϕ v).1),
    (H.Sfix ϕ u \ H.Ctree ϕ u).image fun v => (v, (ϕ v).1))

open Classical in
/-- The reference distribution `µ^ref_i` (51) of the component `H_i` with least vertex `s`
(arXiv:2611.05912 (sha256 b31400a0…), p.27), evaluated at (the restriction to `U_i` of) `ϕ`:
for a component with edges,
`µ^ref_i(ϕ) = (1/Z^ref_i)(1/|V_mid ∪ V_bd|) Π_{uv ∈ E(H_i)} κ_{Color_H(uv)}(ϕ(u), ϕ(v))` for
`ϕ : U_i → V_mid ∪ V_bd` (and `0` if some `ϕ(u) ∉ V_mid ∪ V_bd`), with
`Z^ref_i = (1/|V_mid ∪ V_bd|) Σ_{ϕ : U_i → V_mid ∪ V_bd} Π_{uv ∈ E(H_i)} κ_{Color_H(uv)}(ϕ(u), ϕ(v))`;
for a single-vertex component, the uniform distribution on `[M]`.

**Formalization Note.** Assignments take values in `[0, M]` (`Label n`); the sum defining
`Z^ref_i` runs over the maps `U_i → V_mid ∪ V_bd`, written as assignments that vanish off `U_i`.
If `Z^ref_i = 0` (no placement of `H_i` has every edge permuted) the division gives `0`, so `H_i`
has no good assignment, as in the source where `µ^ref_i` is then undefined. -/
noncomputable def muComp (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) (s : Fin H.k)
    (ϕ : Fin H.k → Label n) : ℝ :=
  let U := H.comp s
  let V := Vmid n l ∪ Vbd n l
  let wt : (Fin H.k → Label n) → ℝ := fun ψ =>
    ∏ p ∈ H.E.filter (fun p => p.1 ∈ U), kappa l G (H.color p) (ψ p.1).1 (ψ p.2).1
  if U.card = 1 then (if 1 ≤ (ϕ s).1 then 1 / (labelBound n : ℝ) else 0)
  else
    let Z : ℝ := (1 / (V.card : ℝ)) *
      ∑ ψ ∈ Finset.univ.filter (fun ψ : Fin H.k → Label n =>
          (∀ u ∈ U, (ψ u).1 ∈ V) ∧ (∀ u, u ∉ U → ψ u = 0)), wt ψ
    if ∀ u ∈ U, (ϕ u).1 ∈ V then (1 / Z) * (1 / (V.card : ℝ)) * wt ϕ else 0

open Classical in
/-- The reference distribution `µ^ref`, the product of the `µ^ref_i` over the connected components
of `H` (arXiv:2611.05912 (sha256 b31400a0…), p.27). -/
noncomputable def muRef (l : ℕ) (G : WeldedInstance n) (H : AbsForest n)
    (ϕ : Fin H.k → Label n) : ℝ :=
  ∏ s ∈ Finset.univ.filter (fun s => H.IsCompRoot s), H.muComp l G s ϕ

/-- `I_ϕ = (L_ϕ, C_ϕ)` is the database of the assignment `ϕ` (arXiv:2611.05912
(sha256 b31400a0…), p.27): every labeled abstract vertex `u` has `L_ϕ(ϕ(u)) = λ_H(u)`, and every
abstract edge `uv` of color `α` contributes the record `C_{ϕ,b}(e_α(x)) = e_α(y)`, where
`{x, y} = {ϕ(u), ϕ(v)}` with `x = tail(e_α(x))` and `y = head(e_α(y))` ("going from tail to head"),
and there are no other records.

**Formalization Note.** The record `e_α(x) ↦ e_α(y)` is in the class `b` containing both edges.
For a good assignment exactly one database satisfies this predicate (`gVec` sums over it). -/
def IsDbOf (l : ℕ) (G : WeldedInstance n) (H : AbsForest n) (ϕ : Fin H.k → Label n)
    (I : Db l G) : Prop :=
  (∀ i j : Fin (labelBound n), I.1 i = some j ↔ ∃ u, (ϕ u).1 = i.1 + 1 ∧ H.lab u = some j) ∧
  (∀ (b : PClass n l) (j j' : Fin (classSize l G b)), I.2 b j = some j' ↔
    ∃ p ∈ H.E,
      let e₁ := ((edgeIdx l G b).symm j).1
      let e₂ := ((edgeIdx l G b).symm j').1
      let α := H.color p
      (G.eAlpha (ϕ p.1).1 α = some e₁ ∧ G.eAlpha (ϕ p.2).1 α = some e₂ ∧
          (ϕ p.1).1 = e₁.tail ∧ (ϕ p.2).1 = e₂.head n) ∨
        (G.eAlpha (ϕ p.2).1 α = some e₁ ∧ G.eAlpha (ϕ p.1).1 α = some e₂ ∧
          (ϕ p.2).1 = e₁.tail ∧ (ϕ p.1).1 = e₂.head n))

end AbsForest

/-! ### Descriptions and the good space (52) -/

/-- A description `D = (B, H, (u_i, w_i)_{i ∈ [k]})` (arXiv:2611.05912 (sha256 b31400a0…), p.27),
without its boundary `B` (a separate argument): an abstract forest, the chosen vertices `u_i`, one
per connected component, and their fixed data `w_i`.

**Formalization Note.** The fixed data are given as `w_i = W^fix_{u_i}(ϕ₀)` for an assignment
`ϕ₀`. A tuple `(w_i)_i` that is not of this form for any good assignment gives `|g_D⟩ = 0`, and
one that is takes the form with `ϕ₀` that assignment, so the span of the `|g_D⟩` is the same. -/
structure Description (n : ℕ) where
  /-- The abstract forest `H`. -/
  H : AbsForest n
  /-- The chosen vertices `u_i`. -/
  sel : Finset (Fin H.k)
  /-- The assignment whose fixed data at the `u_i` are the `w_i`. -/
  ϕ₀ : Fin H.k → Label n

namespace Description

/-- `H` is an abstract forest and `sel` has exactly one vertex in each connected component. -/
def IsValid (D : Description n) : Prop :=
  D.H.IsValid ∧ ∀ u, ∃! s, s ∈ D.sel ∧ D.H.graph.Reachable u s

/-- `G_D(ϕ)` (52) for the boundary `B` (arXiv:2611.05912 (sha256 b31400a0…), p.27):
`µ^ref(ϕ) > 0`; `W^fix_{u_i}(ϕ) = w_i` for every `i`; `ϕ(U_i ∖ C^tree_{u_i}) ∩ B = ∅` for every
`i`; and `ϕ(u) ≠ ϕ(v)` for all distinct `u, v ∈ U`. -/
def IsGood (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) (D : Description n)
    (ϕ : Fin D.H.k → Label n) : Prop :=
  0 < D.H.muRef l G ϕ ∧
  (∀ s ∈ D.sel, D.H.Wfix ϕ s = D.H.Wfix D.ϕ₀ s) ∧
  (∀ s ∈ D.sel, ∀ u, D.H.graph.Reachable s u → u ∉ D.H.Ctree ϕ s → (ϕ u).1 ∉ B) ∧
  Function.Injective ϕ

open Classical in
/-- The canonical good vector `|g_D⟩ = Σ_{ϕ : G_D(ϕ) = 1} √µ^ref(ϕ) |L_ϕ, C_ϕ⟩` (arXiv:2611.05912
(sha256 b31400a0…), p.27). -/
noncomputable def gVec (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) (D : Description n) :
    Hil (Db l G) :=
  ∑ ϕ ∈ Finset.univ.filter (fun ϕ => D.IsGood l G B ϕ),
    ((Real.sqrt (D.H.muRef l G ϕ) : ℝ) : ℂ) •
      ∑ I ∈ Finset.univ.filter (fun I => D.H.IsDbOf l G ϕ I), ket I

end Description

/-- The good space for databases with at most `t` records and boundary `B` (arXiv:2611.05912
(sha256 b31400a0…), p.27): the span of the canonical good vectors `|g_D⟩` over the descriptions
with boundary `B` and `|E(H)| + |Dom(λ_H)| ≤ t`.

**Formalization Note.** The span runs over abstract forests of every size; each component has a
label or an edge, so `|U| ≤ 2t` automatically. The generators are not orthogonal. -/
noncomputable def goodSpace (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) (t : ℕ) :
    Submodule ℂ (Hil (Db l G)) :=
  Submodule.span ℂ
    {v | ∃ D : Description n, D.IsValid ∧ D.H.records ≤ t ∧ v = D.gVec l G B}

/-- The orthogonal projector `Π^good_t(B)` onto the good space, acting as the identity on the
query registers `X ⊗ Y` (arXiv:2611.05912 (sha256 b31400a0…), p.27). -/
noncomputable def projGoodB (l : ℕ) (G : WeldedInstance n) (B : Finset ℕ) (t : ℕ) :
    Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G) :=
  opTensor (1 : Hil (QReg n) →L[ℂ] Hil (QReg n)) (goodSpace l G B t).starProjection

/-- `Π^good_t := Π^good_t(V_bd)` (arXiv:2611.05912 (sha256 b31400a0…), p.27). -/
noncomputable def projGood (l : ℕ) (G : WeldedInstance n) (t : ℕ) :
    Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G) :=
  projGoodB l G (Vbd n l) t

/-- `η^step_t`, the nonnegative square root of `(η^step_t)² = ϵ_l + n(t + 1)/N` (61), with
`ϵ_l = 2^{−l}` and `N = 2^n` (arXiv:2611.05912 (sha256 b31400a0…), p.32). -/
noncomputable def etaStep (n l t : ℕ) : ℝ :=
  Real.sqrt (1 / (2 : ℝ) ^ l + (n : ℝ) * ((t : ℝ) + 1) / (2 : ℝ) ^ n)

end Supplement

end WeldedPath


