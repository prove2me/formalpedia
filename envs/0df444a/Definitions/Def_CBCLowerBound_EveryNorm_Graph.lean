-- Prove2me | Definitions.Def_CBCLowerBound_EveryNorm_Graph
-- name    : CBCLowerBound_EveryNorm_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:04.591202+00:00
-- url     : https://prove2.me/theorems/380172f0-d4ac-4efa-8cfb-0eedcfced4c5
-- title:
--   The Bubeck–Coester–Rabani graphs $G_r$, their copies, depths, branch functions and the map $\Psi$
-- statement:
--   **Parameters** (p.4). Fix natural numbers $m_0\le m_1\le m_2\le\cdots$ and reals $C_r\ge1$ with $m_r\ge C_r$ and $C_0=1$; put $b_r=C_r/m_r\in[1/m_r,1]$.
--
--   **Graphs** (pp.4–5). $G_0$ is a single edge of length $1$ from the source $s_0$ to the target $t_0$. $G_{r+1}$ has a source $s_{r+1}$, a target $t_{r+1}$ and two branches $L,R$ sharing only $s_{r+1},t_{r+1}$. Each branch consists, in order, of an entrance edge of length $b_r$ from $s_{r+1}$; $m_r^2$ copies of $G_r$, each scaled to source-to-target distance $1/m_r$ ("small copies"); and $2m_r$ copies scaled to source-to-target distance $1$ ("large copies"). The end of the entrance edge is the source of the first copy, consecutive copies are glued target to source, and the target of the last copy on each branch is $t_{r+1}$. Scaling multiplies all edge lengths of $G_r$ by the target length divided by $L_r=d_{G_r}(s_r,t_r)$. The metric $d_G$ of $G=G_r$ is its **shortest-path distance**, the infimum of the total edge length of walks.
--
--   **Copies, depths** (pp.5, 8). A copy $H$ of $G_s$ inside $G=G_r$ ($s\le r$; for $s=r$ it is $G$ itself) has source $s_H$ and target $t_H$; a vertex lies on branch $a$ of $H$ if it lies on that branch of $G_s$ ($s_H,t_H$ lie on both branches). All lengths are measured in the full graph $G$: the depth is $h(v)=d_G(s_G,v)$, the local depth $h_H(v)=d_G(s_H,v)$, the local length $L_H=d_G(s_H,t_H)$, and for $v\in H$
--   $$g_H(v)=\min\{h_H(v),\,L_H-h_H(v)\}.$$
--
--   **Branch functions and $\Psi$** (pp.8–9). For $1\le s\le r$ and $a\in\{L,R\}$, $\phi_{H,a}(v)=g_H(v)$ if $v$ lies on branch $a$ of $H$, and $0$ otherwise (eq. (3)); $\psi_{s,a}(v)=\sum_{H}\phi_{H,a}(v)$ over all copies $H$ of $G_s$ (eq. (4)); and
--   $$\Psi(v)=\big(h(v),\ (\psi_{s,L}(v),\psi_{s,R}(v))_{s=1}^r\big)\in\mathbb R^D,\qquad D=2r+1\quad\text{(eq. (5))}.$$
--
--   These objects carry every milestone of the mission: the discrete instance lives on $G_r$ and the convex instance on $\Psi(G_r)$.
--
--   **Formalization Note** Vertices of $G_{r+1}$ other than $s_{r+1},t_{r+1}$ are encoded as $(a,j,\mathrm{none})$, the source of the $j$-th copy on branch $a$ (for $j=0$, the end of the entrance edge), and $(a,j,x)$, the inner vertex $x$ of the $j$-th copy; the target of copy $j$ is the source of copy $j+1$, or $t_{r+1}$ for the last copy. Branch `false` is $L$ and `true` is $R$; indices $j<m_r^2$ are the small copies. A copy of $G_s$ in $G_r$ is a path of (branch, index) choices, and `Contains` is the prefix order on these addresses. Coordinates of $\Psi$ are $0$-based: coordinate $0$ is $h$, coordinate $2s-1$ is $\psi_{s,L}$, coordinate $2s$ is $\psi_{s,R}$ (the paper's $(2s+\mathbf 1_{a=R})$-th coordinate counted from $1$, p.12). Vectors in `Fin D → ℝ` carry the sup norm. The equality $L_{r+1}=3m_r+b_r$ (eq. (1)) is a property of these definitions, not part of them.
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), pp.4–6, §2.1 (parameters, graphs G_r, Figure 1, eq. (1), depth, eq. (2)); pp.8–9, §3 (g_H, eqs. (3)–(5)); p.12 (coordinate indexing), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib

namespace CBCLowerBound.EveryNorm

/-! # The recursive graphs `G_r` of Bubeck–Coester–Rabani and the map `Ψ`
(Christianson, STOC 2027 #674, §2.1, pp.4–6, and §3, pp.8–9) -/

/-! ## Shortest-path distance of a finite weighted graph -/

section PathDist

variable {V : Type}

/-- `IsWalk E u w v`: the list `w` of edges `(x, y, ℓ)` is a walk from `u` to `v` in the
undirected weighted graph with edge list `E`; each step uses an edge of `E` in either direction. -/
def IsWalk (E : List (V × V × ℝ)) : V → List (V × V × ℝ) → V → Prop
  | u, [], v => u = v
  | u, e :: w, v => (e ∈ E ∨ (e.2.1, e.1, e.2.2) ∈ E) ∧ e.1 = u ∧ IsWalk E e.2.1 w v

/-- The length `∑ ℓ` of a walk. -/
def walkLength (w : List (V × V × ℝ)) : ℝ :=
  (w.map fun e => e.2.2).sum

/-- The **shortest-path distance** `d(u, v)`: the infimum of the lengths of walks from `u`
to `v`. -/
noncomputable def pathDist (E : List (V × V × ℝ)) (u v : V) : ℝ :=
  sInf {c : ℝ | ∃ w, IsWalk E u w v ∧ c = walkLength w}

end PathDist

/-! ## Parameters of the construction (p.4) -/

/-- The parameter sequences of the construction (p.4): natural numbers `m₀ ≤ m₁ ≤ ⋯` and reals
`C_r ≥ 1` with `m_r ≥ C_r` and `C₀ = 1`. -/
structure Params where
  /-- `m_r`, the number parameter of level `r`. -/
  m : ℕ → ℕ
  /-- `m₀ ≤ m₁ ≤ m₂ ≤ ⋯`. -/
  m_mono : Monotone m
  /-- `C_r`. -/
  C : ℕ → ℝ
  /-- `C_r ≥ 1`. -/
  one_le_C : ∀ r, 1 ≤ C r
  /-- `m_r ≥ C_r`. -/
  C_le_m : ∀ r, C r ≤ m r
  /-- `C₀ = 1`. -/
  C_zero : C 0 = 1

namespace Params

variable (θ : Params)

/-- The number of copies of `G_r` on each branch of `G_{r+1}`: `m_r²` small and `2m_r` large. -/
def n (r : ℕ) : ℕ := θ.m r ^ 2 + 2 * θ.m r

/-- The entrance-edge length `b_r = C_r / m_r`. -/
noncomputable def b (r : ℕ) : ℝ := θ.C r / θ.m r

theorem m_pos (r : ℕ) : 0 < θ.m r := by
  have h1 := θ.one_le_C r
  have h2 := θ.C_le_m r
  exact_mod_cast (show (0 : ℝ) < θ.m r by linarith)

theorem n_pos (r : ℕ) : 0 < θ.n r := by
  have := θ.m_pos r
  unfold n; positivity

end Params

/-! ## Vertices -/

/-- Vertices of `G_r` other than its source and target. A vertex of `G_{r+1}` other than
`s_{r+1}, t_{r+1}` is `(a, j, none)`, the source of the `j`-th copy of `G_r` on branch `a`
(for `j = 0` the end of the entrance edge), or `(a, j, some x)`, the vertex `x` of the `j`-th
copy. Branch `false` is the left branch `L`, `true` the right branch `R`; copies
`j < m_r²` are the small copies, `m_r² ≤ j < m_r² + 2m_r` the large ones. -/
def Inner (θ : Params) : ℕ → Type
  | 0 => Empty
  | r + 1 => Bool × Fin (θ.n r) × Option (Inner θ r)

instance instFintypeInner (θ : Params) : (r : ℕ) → Fintype (Inner θ r)
  | 0 => by unfold Inner; infer_instance
  | r + 1 => by haveI := instFintypeInner θ r; unfold Inner; infer_instance

instance instDecidableEqInner (θ : Params) : (r : ℕ) → DecidableEq (Inner θ r)
  | 0 => by unfold Inner; infer_instance
  | r + 1 => by haveI := instDecidableEqInner θ r; unfold Inner; infer_instance

/-- A vertex type with a designated source and target. -/
inductive Pt (I : Type) where
  | src : Pt I
  | tgt : Pt I
  | inner (x : I) : Pt I
  deriving DecidableEq

/-- `Pt I ≃ Option (Option I)`. -/
def Pt.equivOption (I : Type) : Pt I ≃ Option (Option I) where
  toFun | .src => none | .tgt => some none | .inner x => some (some x)
  invFun | none => .src | some none => .tgt | some (some x) => .inner x
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | _ <;> rfl

instance {I : Type} [Fintype I] : Fintype (Pt I) :=
  Fintype.ofEquiv _ (Pt.equivOption I).symm

/-- The vertex set of `G_r`: source `s_r`, target `t_r` and the inner vertices. -/
abbrev Vert (θ : Params) (r : ℕ) : Type := Pt (Inner θ r)

/-- The embedding of `G_r` as the `j`-th copy on branch `a` of `G_{r+1}` (pp.4–5): its source is
`(a, j, none)`; its target is the source of the next copy, or `t_{r+1}` for the last copy;
consecutive copies are glued target to source. -/
def embed (θ : Params) {r : ℕ} (a : Bool) (j : Fin (θ.n r)) : Vert θ r → Vert θ (r + 1)
  | .src => .inner (a, j, none)
  | .tgt => if h : j.val + 1 < θ.n r then .inner (a, ⟨j.val + 1, h⟩, none) else .tgt
  | .inner x => .inner (a, j, some x)

/-! ## Edges and the metric -/

/-- The weighted edges of `G_r` (pp.4–5). `G₀` is one edge of length one from `s₀` to `t₀`.
Each branch `a` of `G_{r+1}` consists of the entrance edge from `s_{r+1}` to `(a, 0, none)`
of length `b_r = C_r/m_r`, then `m_r²` copies of `G_r` scaled to source-to-target distance
`1/m_r`, then `2m_r` copies scaled to source-to-target distance `1`. Scaling multiplies every
edge length of `G_r` by `(target length)/L_r`, where `L_r = d_{G_r}(s_r, t_r)`. -/
noncomputable def edges (θ : Params) : (r : ℕ) → List (Vert θ r × Vert θ r × ℝ)
  | 0 => [(.src, .tgt, 1)]
  | r + 1 =>
    [false, true].flatMap fun a =>
      ((.src : Vert θ (r + 1)), (.inner (a, ⟨0, θ.n_pos r⟩, none) : Vert θ (r + 1)), θ.b r) ::
      (List.finRange (θ.n r)).flatMap fun j =>
        (edges θ r).map fun e =>
          (embed θ a j e.1, embed θ a j e.2.1,
            e.2.2 * ((if j.val < θ.m r ^ 2 then 1 / (θ.m r : ℝ) else 1) /
              pathDist (edges θ r) .src .tgt))

/-- The shortest-path metric `d_G` of `G = G_r`. -/
noncomputable def dist (θ : Params) (r : ℕ) : Vert θ r → Vert θ r → ℝ :=
  pathDist (edges θ r)

/-- `L_r = d_{G_r}(s_r, t_r)`, the source-to-target distance of `G_r`. -/
noncomputable def L (θ : Params) (r : ℕ) : ℝ :=
  dist θ r .src .tgt

/-- The depth `h(v) = d_G(s_G, v)` of a vertex of `G = G_r` (p.5). -/
noncomputable def depth (θ : Params) (r : ℕ) (v : Vert θ r) : ℝ :=
  dist θ r .src v

/-! ## Copies of `G_s` inside `G_r` -/

/-- The copies of `G_s` inside `G_r`. For `s = r` the only copy is `G_r` itself; for `s ≤ r`,
a copy inside `G_{r+1}` is a branch `a`, an index `j` of a copy of `G_r` on that branch, and a
copy of `G_s` inside that copy of `G_r`. There are no copies for `s > r`. -/
def Copy (θ : Params) : ℕ → ℕ → Type
  | 0, s => {_u : Unit // s = 0}
  | r + 1, s => {_u : Unit // s = r + 1} ⊕ (Bool × Fin (θ.n r) × Copy θ r s)

instance instFintypeCopy (θ : Params) : (r s : ℕ) → Fintype (Copy θ r s)
  | 0, _ => by unfold Copy; infer_instance
  | r + 1, s => by haveI := instFintypeCopy θ r s; unfold Copy; infer_instance

namespace Copy

variable {θ : Params}

/-- The vertex embedding `G_s → G_r` of a copy. -/
def emb : {r s : ℕ} → Copy θ r s → Vert θ s → Vert θ r
  | 0, _, ⟨_, h⟩, v => h ▸ v
  | _ + 1, _, .inl ⟨_, h⟩, v => h ▸ v
  | _ + 1, _, .inr (a, j, H), v => embed θ a j (emb H v)

/-- `G_r` as a copy of itself. -/
def self : (r : ℕ) → Copy θ r r
  | 0 => ⟨(), rfl⟩
  | _ + 1 => .inl ⟨(), rfl⟩

/-- The address of a copy: the list of (branch, copy index) choices from the top level down. -/
def addr : {r s : ℕ} → Copy θ r s → List (Bool × ℕ)
  | 0, _, _ => []
  | _ + 1, _, .inl _ => []
  | _ + 1, _, .inr (a, j, H) => (a, j.val) :: addr H

/-- `H.Contains H'`: the copy `H'` lies inside the copy `H` (its address extends `H`'s). -/
def Contains {r s s' : ℕ} (H : Copy θ r s) (H' : Copy θ r s') : Prop :=
  H.addr <+: H'.addr

variable {r s : ℕ}

/-- The source `s_H`. -/
def src (H : Copy θ r s) : Vert θ r := H.emb .src

/-- The target `t_H`. -/
def tgt (H : Copy θ r s) : Vert θ r := H.emb .tgt

/-- For a copy `H` of `G_{s+1}`, the source of the `j`-th copy of `G_s` on branch `a` of `H`
(for `j = 0`, the terminal endpoint `u_a` of the entrance edge on branch `a`). Indices are read
modulo the number `m_s² + 2m_s` of copies on a branch. -/
def junc (H : Copy θ r (s + 1)) (a : Bool) (j : ℕ) : Vert θ r :=
  H.emb (.inner ((a, ⟨j % θ.n s, Nat.mod_lt _ (θ.n_pos s)⟩, none) : Inner θ (s + 1)))

/-- `v` is a vertex of the copy `H`. -/
def Mem (H : Copy θ r s) (v : Vert θ r) : Prop := ∃ w, H.emb w = v

end Copy

/-- The branch (`false = L`, `true = R`) of an inner vertex of `G_s`, `s ≥ 1`. -/
def innerBranch {θ : Params} : {s : ℕ} → Inner θ s → Bool
  | 0, x => nomatch x
  | _ + 1, x => x.1

/-- `v` lies on branch `a` of `G_s`: the source and the target lie on both branches. -/
def OnBranchLocal {θ : Params} {s : ℕ} (a : Bool) : Vert θ s → Prop
  | .src => True
  | .tgt => True
  | .inner x => innerBranch x = a

namespace Copy

variable {θ : Params} {r s : ℕ}

/-- `v` lies on branch `a` of the copy `H` (its endpoints lie on both branches). -/
def OnBranch (H : Copy θ r s) (a : Bool) (v : Vert θ r) : Prop :=
  ∃ w, H.emb w = v ∧ OnBranchLocal a w

/-- The local depth `h_H(v) = d_G(s_H, v)`, measured in the full graph `G = G_r` (p.5). -/
noncomputable def localDepth (H : Copy θ r s) (v : Vert θ r) : ℝ := dist θ r H.src v

/-- The local source-to-target length `L_H = d_G(s_H, t_H)`. -/
noncomputable def length (H : Copy θ r s) : ℝ := dist θ r H.src H.tgt

/-- `g_H(v) = min{h_H(v), L_H − h_H(v)}` (p.8). -/
noncomputable def g (H : Copy θ r s) (v : Vert θ r) : ℝ :=
  min (H.localDepth v) (H.length - H.localDepth v)

open Classical in
/-- The branch function `ϕ_{H,a}` (eq. (3), p.9): `g_H(v)` if `v` lies on branch `a` of `H`,
and `0` elsewhere. -/
noncomputable def phi (H : Copy θ r s) (a : Bool) (v : Vert θ r) : ℝ :=
  if H.OnBranch a v then H.g v else 0

end Copy

/-- The aggregate branch function `ψ_{s,a}(v) = ∑_{copies H of G_s} ϕ_{H,a}(v)` (eq. (4), p.9). -/
noncomputable def psi (θ : Params) (r s : ℕ) (a : Bool) (v : Vert θ r) : ℝ :=
  ∑ H : Copy θ r s, H.phi a v

/-- The map `Ψ : G → ℝ^D`, `D = 2r + 1` (eq. (5), p.9):
`Ψ(v) = (h(v), ψ_{1,L}(v), ψ_{1,R}(v), …, ψ_{r,L}(v), ψ_{r,R}(v))`. With `0`-based coordinates,
coordinate `0` is the depth, coordinate `2s − 1` is `ψ_{s,L}` and coordinate `2s` is `ψ_{s,R}`.
Vectors in `Fin D → ℝ` carry the sup norm. -/
noncomputable def Psi (θ : Params) (r : ℕ) (v : Vert θ r) : Fin (2 * r + 1) → ℝ := fun i =>
  if i.val = 0 then depth θ r v else psi θ r ((i.val + 1) / 2) (decide (i.val % 2 = 0)) v

end CBCLowerBound.EveryNorm


