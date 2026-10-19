-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_Rectangle
-- name    : OAI_Combinatorics_Hamiltonian_Rectangle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:01:11.017148+00:00
-- url     : https://prove2.me/theorems/bc43f219-ba62-4614-952e-61e9f1088ee3
-- title:
--   Rectangular grid networks, their dual networks, and grids as boxes of the square lattice
-- statement:
--   A *network* with vertex set $X$ and edge set $Y$ is a pair of maps $\mathrm{tail},\mathrm{head}:Y\to X$; its underlying graph is the simple graph on $X$ in which $x\ne x'$ are adjacent iff some edge $y$ has endpoint pair $\{\mathrm{tail}(y),\mathrm{head}(y)\}=\{x,x'\}$. For a statement $P$, $[P]$ is $1$ if $P$ holds and $0$ otherwise. Fix $n,m\in\mathbb{N}$. The file defines the following objects.
--
--   1. **Grid index sets.** The vertices are the points $(i,j)$ with $0\le i\le n$ and $0\le j\le m$. The edges are the horizontal edges $h_{i,j}$ with $0\le i<n$, $0\le j\le m$, and the vertical edges $v_{i,j}$ with $0\le i\le n$, $0\le j<m$. The faces are the $nm$ unit squares $s_{i,j}$ with $0\le i<n$, $0\le j<m$, together with one outer face $s_\infty$.
--
--   2. **Primal network.** It has the grid vertices and the grid edges, oriented in the positive coordinate directions (written tail $\to$ head):
--   $$h_{i,j}:\ (i,j)\to(i+1,j),\qquad v_{i,j}:\ (i,j)\to(i,j+1).$$
--
--   3. **Dual network.** It has the faces as vertices and the same edges. With the convention that $s_{i,j}$ means the outer face $s_\infty$ whenever an index leaves its range ($i\in\{-1,n\}$ or $j\in\{-1,m\}$),
--   $$h_{i,j}:\ s_{i,j-1}\to s_{i,j},\qquad v_{i,j}:\ s_{i,j}\to s_{i-1,j}.$$
--   Thus every dual edge crosses its primal edge from the square on one side to the square on the other side, in the direction obtained by turning the primal direction counterclockwise by a right angle (from below to above for horizontal edges, from right to left for vertical edges).
--
--   4. **Auxiliary functions on a path.** For $N\in\mathbb{N}$ and $f:\{0,\dots,N-1\}\to\mathbb{R}$ define on $\{0,\dots,N\}$
--   $$f^{\downarrow}(k)=\begin{cases}0,&k=0,\\ f(k-1),&k\ge1,\end{cases}\qquad f^{\uparrow}(k)=\begin{cases}f(k),&k<N,\\ 0,&k=N,\end{cases}$$
--   and the step coefficients $\sigma(k,e)=[e+1=k]-[e=k]$ for $0\le k\le N$, $0\le e<N$, which form the incidence matrix of the directed path $0\to1\to\cdots\to N$. For a function $f$ on the unit squares, its potential $\hat f$ is the extension by zero to all faces: $\hat f(s_{i,j})=f(i,j)$ and $\hat f(s_\infty)=0$.
--
--   5. **Pulling back minor models.** A minor model of a graph $G$ (vertex set $V$) in a graph $H$ (vertex set $W$) is a family of finite, pairwise disjoint sets $B_v\subseteq W$, $v\in V$, each inducing a connected subgraph of $H$, such that for every edge $vw$ of $G$ some vertex of $B_v$ is adjacent in $H$ to some vertex of $B_w$. If $J$ is a graph on a finite vertex set $U$ and $\varphi:U\to W$ is an induced embedding ($\varphi$ injective and $\varphi(a)\varphi(b)\in E(H)$ iff $ab\in E(J)$) whose image contains every branch set $B_v$, then $(\varphi^{-1}(B_v))_{v\in V}$ is a minor model of $G$ in $J$.
--
--   6. **Grids as boxes of the square lattice.** The square lattice graph on $\mathbb{Z}^2$ joins $(a,b)$ and $(a',b')$ iff $|a-a'|=1$ and $b=b'$, or $|b-b'|=1$ and $a=a'$. The file proves that the underlying graph of the primal network obeys exactly this adjacency rule on the grid points $(i,j)$, and defines for $r\in\mathbb{N}$ the map
--   $$\pi_r(i,j)=(i-r,\ j-r)\in\mathbb{Z}^2\qquad(0\le i,j\le 2r),$$
--   an injective induced embedding of the underlying graph of the $2r\times 2r$ primal grid into the square lattice graph, with image the box $\{-r,\dots,r\}^2$.
--
--   The rectangular primal and dual networks form an explicit pair of mutually dual plane networks, and the functions of item 4 are the bookkeeping used to compute dual gradients of face potentials when this duality is verified. Items 5 and 6 transport a minor model in the infinite square lattice, whose finitely many finite branch sets lie in some box $\{-r,\dots,r\}^2$, to a minor model in a finite rectangular grid.
--
--   **Formalization Note** The index types are `Vertex n m = Fin (n+1) × Fin (m+1)`, `Edge n m = (Fin n × Fin (m+1)) ⊕ (Fin (n+1) × Fin m)` (left summand horizontal, right summand vertical) and `Face n m = Option (Fin n × Fin m)` with `none` the outer face. The networks are `primal n m` and `dual n m`; the out-of-range convention is implemented by `lower = Fin.cases none some` and `upper = Fin.lastCases none some`. The functions of item 4 are `lowerValue`, `upperValue`, `stepCoeff` and `potential`. Pulling back is `MinorModel.pullHost`, which takes a Mathlib graph embedding `J ↪g H`; the adjacency rule is `primal_adj_iff`, and $\pi_r$ is `latticePoint r`, packaged as the embedding `latticeEmbedding r` into `SquareGrid.graph`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Rectangle.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Rectangle.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_SquareGrid
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Corridors
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorModel

namespace OAI

/-! Rectangular primal and dual networks and finite lattice containment. -/

namespace Barnette.RectangularDual
noncomputable section

abbrev Vertex (n m : ℕ) := Fin (n + 1) × Fin (m + 1)
abbrev Edge (n m : ℕ) := (Fin n × Fin (m + 1)) ⊕ (Fin (n + 1) × Fin m)
abbrev Face (n m : ℕ) := Option (Fin n × Fin m)

def primal (n m : ℕ) : Network (Vertex n m) (Edge n m) where
  tail := Sum.elim (fun e => (e.1.castSucc, e.2)) (fun e => (e.1, e.2.castSucc))
  head := Sum.elim (fun e => (e.1.succ, e.2)) (fun e => (e.1, e.2.succ))

def lower {n : ℕ} : Fin (n + 1) → Option (Fin n) := Fin.cases none some
def upper {n : ℕ} : Fin (n + 1) → Option (Fin n) := Fin.lastCases none some

def dual (n m : ℕ) : Network (Face n m) (Edge n m) where
  tail := Sum.elim
    (fun e => (lower e.2).map (fun j => (e.1, j)))
    (fun e => (upper e.1).map (fun i => (i, e.2)))
  head := Sum.elim
    (fun e => (upper e.2).map (fun j => (e.1, j)))
    (fun e => (lower e.1).map (fun i => (i, e.2)))

def lowerValue {n : ℕ} (f : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cases 0 f
def upperValue {n : ℕ} (f : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.lastCases 0 f

def stepCoeff {n : ℕ} (v : Fin (n + 1)) (e : Fin n) : ℝ :=
  (if e.succ = v then 1 else 0) - (if e.castSucc = v then 1 else 0)

def potential {n m : ℕ} (f : Fin n × Fin m → ℝ) : Face n m → ℝ :=
  fun z => z.elim 0 f

end
end Barnette.RectangularDual

namespace Barnette.MinorModel
noncomputable section
open scoped Classical
variable {V W U : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  {J : SimpleGraph U} [Fintype U]

def pullHost (M : MinorModel G H) (f : J ↪g H)
    (hf : ∀ v, M.branch v ⊆ Set.range f) : MinorModel G J where
  branch v := f ⁻¹' M.branch v
  branch_finite _ := Set.toFinite _
  branch_connected v := by
    let g : {x // f x ∈ M.branch v} → M.branch v := fun x => ⟨f x.val, x.property⟩
    have hg : Function.Bijective g := by
      refine ⟨?_, ?_⟩
      · intro x y hxy
        apply Subtype.ext
        exact f.injective (congrArg Subtype.val hxy)
      · intro y
        obtain ⟨x, hx⟩ := hf v y.property
        refine ⟨⟨x, hx ▸ y.property⟩, ?_⟩
        exact Subtype.ext hx
    let e : J.induce (f ⁻¹' M.branch v) ≃g H.induce (M.branch v) :=
      { toEquiv := Equiv.ofBijective g hg
        map_rel_iff' := by intro x y; exact f.map_rel_iff }
    exact e.connected_iff.mpr (M.branch_connected v)
  branches_disjoint v w hvw := (M.branches_disjoint v w hvw).preimage f
  adjacency v w h := by
    obtain ⟨a, ha, b, hb, hab⟩ := M.adjacency v w h
    obtain ⟨a', rfl⟩ := hf v ha
    obtain ⟨b', rfl⟩ := hf w hb
    exact ⟨a', ha, b', hb, f.map_rel_iff.mp hab⟩
end
end Barnette.MinorModel

namespace Barnette.RectangularDual
noncomputable section
open scoped Classical

lemma primal_adj_iff {n m : ℕ} (p q : Vertex n m) :
    (primal n m).graph.Adj p q ↔
      ((p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val) ∧ p.2 = q.2) ∨
      ((p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val) ∧ p.1 = q.1) := by
  constructor
  · rintro ⟨_, e, he⟩
    rcases e with ⟨i, j⟩ | ⟨i, j⟩ <;>
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [primal]
  · have hx (a b : Vertex n m) (h : a.1.val + 1 = b.1.val) (hj : a.2 = b.2) :
        (primal n m).graph.Adj a b := by
      have hi : a.1.val < n := by have := b.1.isLt; omega
      refine ⟨?_, .inl (⟨a.1.val, hi⟩, a.2), Or.inl ⟨?_, ?_⟩⟩
      · intro he; have hh := congrArg (fun x : Vertex n m => x.1.val) he; omega
      · apply Prod.ext <;> rfl
      · apply Prod.ext
        · apply Fin.ext; exact h
        · exact hj
    have hy (a b : Vertex n m) (h : a.2.val + 1 = b.2.val) (hi : a.1 = b.1) :
        (primal n m).graph.Adj a b := by
      have hj : a.2.val < m := by have := b.2.isLt; omega
      refine ⟨?_, .inr (a.1, ⟨a.2.val, hj⟩), Or.inl ⟨?_, ?_⟩⟩
      · intro he; have hh := congrArg (fun x : Vertex n m => x.2.val) he; omega
      · apply Prod.ext <;> rfl
      · apply Prod.ext
        · exact hi
        · apply Fin.ext; exact h
    rintro (⟨h | h, hj⟩ | ⟨h | h, hi⟩)
    · exact hx p q h hj
    · exact (hx q p h hj.symm).symm
    · exact hy p q h hi
    · exact (hy q p h hi.symm).symm

def latticePoint (r : ℕ) (p : Vertex (2 * r) (2 * r)) : ℤ × ℤ :=
  ((p.1.val : ℤ) - r, (p.2.val : ℤ) - r)

lemma latticePoint_injective (r : ℕ) : Function.Injective (latticePoint r) := by
  intro p q h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [latticePoint] at h₁ h₂
  apply Prod.ext <;> apply Fin.ext <;> omega

def latticeEmbedding (r : ℕ) : (primal (2 * r) (2 * r)).graph ↪g SquareGrid.graph where
  toFun := latticePoint r
  inj' := latticePoint_injective r
  map_rel_iff' := by
    intro p q
    rw [primal_adj_iff]
    change SquareGrid.graph.Adj (latticePoint r p) (latticePoint r q) ↔ _
    simp only [SquareGrid.graph, latticePoint, Fin.ext_iff]
    omega

end
end Barnette.RectangularDual

end OAI


