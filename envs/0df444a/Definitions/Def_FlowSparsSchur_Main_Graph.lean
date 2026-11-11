-- Prove2me | Definitions.Def_FlowSparsSchur_Main_Graph
-- name    : FlowSparsSchur_Main_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:23:02.708945+00:00
-- url     : https://prove2.me/theorems/42f19aba-2547-405b-9f9a-3f8ab0cef6af
-- title:
--   Capacitated multigraphs with conductances: incidence matrix, Laplacian, pseudoinverse, spectral approximation, Schur complement, Schur projection, combinations of graphs
-- statement:
--   A **graph** $G$ on a finite vertex set $V$ is a finite list of edges indexed by a finite set $E$; edge $e$ has a fixed orientation $e = v \to w$ (tail $\mathrm{src}(e)=v$, head $\mathrm{dst}(e)=w$), a **capacity** $u_G(e)$ and a **conductance** $c_G(e)$. Parallel edges are distinct indices. The standing assumptions of the paper (§4.1) are separate predicates: no self-loops ($\mathrm{src}(e)\ne\mathrm{dst}(e)$), $u_G>0$, $c_G>0$, and connectivity (every two vertices are joined by a path of edges, used in either direction).
--
--   The **incidence matrix** $B_G\in\mathbb R^{E\times V}$ has row $b_e=\chi_v-\chi_w$ for $e=v\to w$; $U_G=\mathrm{diag}(u_G)$, $C_G=\mathrm{diag}(c_G)$, $C_G^{1/2}=\mathrm{diag}(\sqrt{c_G})$. The **Laplacian** and the **weighted incidence matrix** are
--   $$L_G=B_G^\top C_GB_G,\qquad D_G=C_G^{1/2}B_G .$$
--   $A^\dagger$ is the Moore–Penrose pseudoinverse (the unique $X$ with $AXA=A$, $XAX=X$, $(AX)^\top=AX$, $(XA)^\top=XA$). For symmetric $A,B$, $A\preceq B$ means $x^\top Ax\le x^\top Bx$ for all $x$, and $A$ **$\xi$-spectrally approximates** $B$ if $\xi^{-1}B\preceq A\preceq \xi B$. The **capacity ratio** is $\mathcal U=\max_e u_G(e)/\min_e u_G(e)$.
--
--   For $S\subseteq V$ and $U=V\setminus S$, write $L_G$ in blocks $L_{SS},L_{SU},L_{US},L_{UU}$. The **Schur complement** of $G$ onto $S$ has Laplacian
--   $$L_{\mathrm{Schur}(G,S)}=L_{SS}-L_{SU}L_{UU}^{-1}L_{US},$$
--   the **Schur projection** is $P_{G\to S}=[\,I\ \ -L_{SU}L_{UU}^{-1}\,]\in\mathbb R^{S\times V}$ (its transpose is the harmonic extension), and $P_{H\to V(G)}=[\,I;\,0\,]\in\mathbb R^{V\times S}$ pads a vector on $S$ with zeros. For $S=V$ the block $L_{UU}$ is empty, so $L_{\mathrm{Schur}(G,V)}=L_G$ and $P_{G\to V}=I$, the convention of Definitions 9.14–9.15. $G_c$ is $G$ with conductances $c$, and $H(\nu)=H_\nu$ is $H$ with capacities $\nu$ (same edges, orientation and conductances).
--
--   The **combination** $H_\lambda=\sum_i\lambda_iH_i$ of graphs $H_i$ on the same vertex set has all their edges, an edge of $H_i$ carrying capacity $\lambda_iu_{H_i}(e)$.
--
--   **Formalization Note** `CGraph V E` stores `src`, `dst`, `cap`, `cond`. Graphs on the terminal set use the subtype `↥S` of a `Finset` as vertex type. $L_{UU}^{-1}$ is Mathlib's `Matrix.inv`, which is the inverse whenever $L_{UU}$ is invertible (always the case for a connected $G$ with $S\ne\emptyset$). `pinv` is defined through the Penrose equations. In `combo`, edges shared by two graphs are kept as parallel copies instead of merged; parallel capacities add for routing, so the routing properties are those of the merged graph. The conductances of a combination are those of the summands; no statement uses them.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), pp. 12–15, §4.1, §4.3, §4.4; pp. 31–33, Definitions 9.14, 9.15, 9.18

import Mathlib

/-!
# Capacitated graphs with conductances, Laplacians, Schur complements and projections

Goranci, Henzinger, Momeni, Räcke, Sricharan, *Breaking the Quadratic Time Barrier for Flow
Sparsifiers via Schur Complement Localization*, STOC 2027 submission (manuscript of November 3,
2026), §4 (pp. 12–15), Definitions 9.14, 9.15, 9.18 (pp. 31–33).

A graph is a finite multigraph on a vertex type `V` whose edges are indexed by a type `E`; edge `e`
carries the fixed orientation `src e → dst e` (§4.1, "choose an arbitrary orientation"), a capacity
`cap e` and a conductance `cond e`. Parallel edges are distinct indices. The standing assumptions of
§4.1 (no self-loops, positive capacities/conductances, connected) are separate predicates so that
every statement lists the ones it uses.
-/

namespace FlowSparsSchur.Main

open Matrix

/-- A multigraph on vertices `V` with edges indexed by `E`: edge `e` is oriented `src e → dst e` and
carries a capacity `cap e` and a conductance `cond e`. -/
structure CGraph (V E : Type) where
  src : E → V
  dst : E → V
  cap : E → ℝ
  cond : E → ℝ

namespace CGraph

variable {V E : Type}

/-- No self-loops (§4.1). -/
def NoLoops (G : CGraph V E) : Prop := ∀ e, G.src e ≠ G.dst e

/-- All capacities are positive (§4.1, `u(G) ∈ ℝ^{E(G)}_{>0}`). -/
def PosCap (G : CGraph V E) : Prop := ∀ e, 0 < G.cap e

/-- All conductances are positive (§4.1, `c(G) ∈ ℝ^{E(G)}_{>0}`). -/
def PosCond (G : CGraph V E) : Prop := ∀ e, 0 < G.cond e

/-- `u` and `v` are joined by an edge (in either orientation). -/
def Adj (G : CGraph V E) (u v : V) : Prop :=
  ∃ e, (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u)

/-- The graph is connected: every two vertices are joined by a path. -/
def Connected (G : CGraph V E) : Prop := ∀ u v, Relation.ReflTransGen G.Adj u v

/-- The standing assumptions of §4.1 for a graph with conductances: no self-loops, positive
conductances, connected. -/
def IsCondGraph (G : CGraph V E) : Prop := G.NoLoops ∧ G.PosCond ∧ G.Connected

/-- The standing assumptions of §4.1 for a capacitated graph with conductances. -/
def IsCapCondGraph (G : CGraph V E) : Prop := G.IsCondGraph ∧ G.PosCap

/-- The same graph (same edges, orientation and conductances) with capacities `ν`: `H(ν) = H_ν`. -/
def withCap (G : CGraph V E) (ν : E → ℝ) : CGraph V E := { G with cap := ν }

/-- The same graph (same edges, orientation and capacities) with conductances `c`: `G_c`. -/
def withCond (G : CGraph V E) (c : E → ℝ) : CGraph V E := { G with cond := c }

/-- The `|E| × |V|` incidence matrix `B_G`: row `e = v → w` is `χ_v − χ_w`. -/
def incidence [DecidableEq V] (G : CGraph V E) : Matrix E V ℝ :=
  fun e v => (if v = G.src e then 1 else 0) - (if v = G.dst e then 1 else 0)

/-- `U_G = diag(u(G))`. -/
noncomputable def capMat [DecidableEq E] (G : CGraph V E) : Matrix E E ℝ := diagonal G.cap

/-- `C_G = diag(c(G))`. -/
noncomputable def condMat [DecidableEq E] (G : CGraph V E) : Matrix E E ℝ := diagonal G.cond

/-- `C_G^{1/2} = diag(√c(G))`. -/
noncomputable def sqrtCondMat [DecidableEq E] (G : CGraph V E) : Matrix E E ℝ :=
  diagonal fun e => Real.sqrt (G.cond e)

/-- The Laplacian `L_G = B_Gᵀ C_G B_G`. -/
noncomputable def lap [Fintype E] [DecidableEq V] [DecidableEq E] (G : CGraph V E) :
    Matrix V V ℝ :=
  G.incidenceᵀ * G.condMat * G.incidence

/-- The weighted incidence matrix `D_G = C_G^{1/2} B_G` (Definition 9.18). -/
noncomputable def wInc [Fintype E] [DecidableEq V] [DecidableEq E] (G : CGraph V E) : Matrix E V ℝ :=
  G.sqrtCondMat * G.incidence

/-- The capacity ratio `𝒰 = u_max / u_min` (§4.1; Theorem 1.1, footnote 1). Used only for graphs
with at least one edge. -/
noncomputable def capRatio [Fintype E] (G : CGraph V E) : ℝ :=
  (⨆ e, G.cap e) / (⨅ e, G.cap e)

/-- The combination `H_λ = Σ_i λ_i H_i` of graphs on the same vertex set (§4.1, Lemmas 5.4–5.5):
the edges of all `H_i` side by side, an edge of `H_i` with capacity `λ_i · u_i(e)`; orientation and
conductance are kept. Parallel copies are kept as separate edges instead of merged (their
capacities add for routing). -/
def combo {T : Type} {Eι : T → Type} (lam : T → ℝ) (H : ∀ i, CGraph V (Eι i)) :
    CGraph V (Σ i, Eι i) where
  src x := (H x.1).src x.2
  dst x := (H x.1).dst x.2
  cap x := lam x.1 * (H x.1).cap x.2
  cond x := (H x.1).cond x.2

end CGraph

/-- The entrywise absolute value `M̄` of a matrix (§4, Notation). -/
def absM {m n : Type} (A : Matrix m n ℝ) : Matrix m n ℝ := fun i j => |A i j|

/-- `X` satisfies the four Penrose equations for `A`. -/
def IsPenroseInverse {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ)
    (X : Matrix n m ℝ) : Prop :=
  A * X * A = A ∧ X * A * X = X ∧ (A * X)ᵀ = A * X ∧ (X * A)ᵀ = X * A

/-- The Moore–Penrose pseudoinverse `A^†`: the unique matrix satisfying the four Penrose equations
(it exists for every real matrix). -/
noncomputable def pinv {n : Type} [Fintype n] (A : Matrix n n ℝ) : Matrix n n ℝ := by
  classical
  exact if h : ∃ X, IsPenroseInverse A X then h.choose else 0

/-- Loewner order of quadratic forms: `A ⪯ B` iff `xᵀAx ≤ xᵀBx` for all `x` (§4.4). -/
def LoewnerLe {V : Type} [Fintype V] (A B : Matrix V V ℝ) : Prop :=
  ∀ x : V → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)

/-- `ξ`-spectral approximation of Laplacians: `ξ⁻¹ B ⪯ A ⪯ ξ B` (§4.4: `G ≈_ξ G'` with
`A = L_G`, `B = L_{G'}`). -/
def SpecApprox {V : Type} [Fintype V] (ξ : ℝ) (A B : Matrix V V ℝ) : Prop :=
  LoewnerLe (ξ⁻¹ • B) A ∧ LoewnerLe A (ξ • B)

section Schur

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The block `L_SS`. -/
def blockSS (L : Matrix V V ℝ) (S : Finset V) : Matrix S S ℝ :=
  L.submatrix (fun s : S => s.val) (fun s : S => s.val)

/-- The block `L_SU`, `U = V \ S`. -/
def blockSU (L : Matrix V V ℝ) (S : Finset V) : Matrix S {v // v ∉ S} ℝ :=
  L.submatrix (fun s : S => s.val) (fun u : {v // v ∉ S} => u.val)

/-- The block `L_US`. -/
def blockUS (L : Matrix V V ℝ) (S : Finset V) : Matrix {v // v ∉ S} S ℝ :=
  L.submatrix (fun u : {v // v ∉ S} => u.val) (fun s : S => s.val)

/-- The block `L_UU`. -/
def blockUU (L : Matrix V V ℝ) (S : Finset V) : Matrix {v // v ∉ S} {v // v ∉ S} ℝ :=
  L.submatrix (fun u : {v // v ∉ S} => u.val) (fun u : {v // v ∉ S} => u.val)

/-- The Schur complement `L_SS − L_SU L_UU⁻¹ L_US` of `L` onto `S` (§4.3, Definition 9.14). For
`S = V` the block `L_UU` is empty and this is `L` itself, the convention of Definition 9.14. -/
noncomputable def schurOf (L : Matrix V V ℝ) (S : Finset V) : Matrix S S ℝ :=
  blockSS L S - blockSU L S * (blockUU L S)⁻¹ * blockUS L S

/-- The Schur projection `P_{G→S} = [I  −L_SU L_UU⁻¹] ∈ ℝ^{S × V}` (§4.3, Definition 9.15); its
transpose is the harmonic extension. For `S = V` it is the identity. -/
noncomputable def schurProjOf (L : Matrix V V ℝ) (S : Finset V) : Matrix S V ℝ :=
  fun s v =>
    if h : v ∈ S then (if s.val = v then 1 else 0)
    else -(blockSU L S * (blockUU L S)⁻¹) s ⟨v, h⟩

/-- The padding map `P_{H→V(G)} = [I; 0] ∈ ℝ^{V × S}` (§4.3): extends a vector on `S` by zeros. -/
def padOf (S : Finset V) : Matrix V S ℝ := fun v s => if v = s.val then 1 else 0

/-- `L_{Schur(G,S)}`, the Laplacian of the Schur complement of `G` onto `S`. -/
noncomputable def schurLap {E : Type} [Fintype E] [DecidableEq E] (G : CGraph V E)
    (S : Finset V) : Matrix S S ℝ :=
  schurOf G.lap S

/-- `P_{G→S}` for the Laplacian of `G`. -/
noncomputable def schurProj {E : Type} [Fintype E] [DecidableEq E] (G : CGraph V E)
    (S : Finset V) : Matrix S V ℝ :=
  schurProjOf G.lap S

end Schur

end FlowSparsSchur.Main


