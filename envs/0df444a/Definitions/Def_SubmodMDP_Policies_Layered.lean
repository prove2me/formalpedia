-- Prove2me | Definitions.Def_SubmodMDP_Policies_Layered
-- name    : SubmodMDP_Policies_Layered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:23.792368+00:00
-- url     : https://prove2.me/theorems/819cf8bd-88af-4bff-ad63-568207dc0a95
-- title:
--   Layered graphs, $Q^{(r)}$, conditioning $x^{|v}$, Algorithm 1 ($\mathrm{RRR}$), linear constraints and encodings
-- statement:
--   **Layered graphs.** A layered graph has vertex set $V=V_1\cup\dots\cup V_H$ (each vertex in exactly one layer) and arcs only from a layer $V_i$ to $V_{i+1}$. A *layer-spanning path* is a sequence $v_1,\dots,v_H$ with $v_i\in V_i$ and $(v_i,v_{i+1})$ an arc for all $i$.
--
--   **The relaxation $Q^{(r)}$.** For $r\in\mathbb Z_{\ge0}$ the variables are $x_I$ for $I\subseteq V$, $|I|\le r+1$, and $Q^{(r)}$ consists of the points satisfying
--   $$\begin{aligned}
--   x_{I\cup\{u\}}+x_{I\cup\{v\}}&\le x_I && (u,v)\in(V_i\times V_{i+1})\setminus A,\ i\in\{1,\dots,H-1\},\ |I|\le r,\\
--   \textstyle\sum_{v\in V_i}x_{I\cup\{v\}}&=x_I && i\in\{1,\dots,H\},\ |I|\le r,\\
--   x_{I\cup\{v\}}&\le x_I && v\in V,\ |I|\le r,\\
--   x_\emptyset&=1,\qquad x_I\ge0 && |I|\le r+1.
--   \end{aligned}$$
--   For a vertex set $P$, $\mathbf 1^{(r)}_P$ is the lift with $(\mathbf 1^{(r)}_P)_I=\prod_{i\in I}\mathbf 1_P(i)$, i.e. $1$ if $I\subseteq P$ and $0$ otherwise. For $x_v>0$ the conditioning is $x^{|v}_I=x_{I\cup\{v\}}/x_v$. A linear function on $\mathbb R^{\binom{V}{\le r+1}}$ is $\ell(y)=\sum_{|I|\le r+1}\ell_Iy_I$.
--
--   **Algorithm 1 (recursive randomized rounding).** With $H=d^r$: if $H=1$, sample $v\in V_1$ with $\mathbb P[v=w]=x_w$. Otherwise split the layers into $d$ consecutive blocks $L_1,\dots,L_d$ of $H/d$ layers, round $x$ recursively on $L_1$ to a path $P_1$, and for $i=2,\dots,d$ round $x^{|u}$ recursively on $L_i$ to $P_i$, where $u$ is the last vertex of $P_{i-1}$; return $P_1\circ\dots\circ P_d$. $\mathrm{RRR}(x)$ is the output law. The algorithm is formalized as a partial randomized procedure: it fails (outcome *none*) on a run where the weights of line 2 are not a probability vector or where it conditions on a vertex $u$ with $x_u=0$.
--
--   **Linear constraints.** For an integer matrix $D\in\mathbb Z^{m\times\binom{V}{\le r+1}}$ and $b\in\mathbb Z^m$, a distribution $\mathcal O$ over layer-spanning paths is *feasible* if $\mathbb E_{\mathrm{OPT}\sim\mathcal O}[D\mathbf 1^{(r)}_{\mathrm{OPT}}]\le b$. $\langle D,b\rangle$ is the sum over all entries of one plus their bit length.
--
--   **Encodings.** Graphs, rational points, $D,b$, and the outputs of the algorithms of Lemmas 5, 7, 8 and 9 are encoded as integer lists in fixed formats (vertex sets of size at most $k$ in a fixed order by size and lexicographically).
--
--   **Formalization Note** Algorithm 1 is run on the whole point $x$ rather than its projections $x[L_i]$; it reads only coordinates of vertex sets inside the current block, so the output law is the same. Layers are 1-based as in the paper.
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), §2, pp. 4–6 (PDF pp. 5–7): (Q), (2), (3), Q^(r), the lift x^(r), the conditioning x^{|v}, Algorithm 1 and RRR(x); §2.4, p. 13 (PDF p. 14): Dy ≤ b, ⟨D,b⟩, distributions O

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Machine

namespace SubmodMDP.Policies

noncomputable section

open Classical

/-! # Layered graphs, the relaxation `Q^(r)` and recursive randomized rounding (§2, PDF pp. 4–9)

Vertices are `Fin N`; `layer v ∈ {1, …, H}` is the (1-based) layer of `v`, and arcs go from
one layer to the next. A point `x` of the lifted space `ℝ^{(V choose ≤ r+1)}` is stored as a
function on all vertex sets; only the coordinates `x_I` with `|I| ≤ r + 1` are ever read. -/

/-- A layered digraph: `N` vertices, `H` layers, the layer of each vertex, and the arc relation. -/
structure LGraph where
  N : ℕ
  H : ℕ
  layer : Fin N → ℕ
  arc : Fin N → Fin N → Bool

/-- Well-formedness: every vertex lies in a layer `1, …, H`, and every arc goes from a layer `i`
to the layer `i + 1`. -/
def LGraph.WF (G : LGraph) : Prop :=
  (∀ v, 1 ≤ G.layer v ∧ G.layer v ≤ G.H) ∧ ∀ u v, G.arc u v = true → G.layer v = G.layer u + 1

/-- A layer-spanning path: one vertex in each layer `1, …, H`, in order, consecutive vertices
joined by arcs. -/
def IsLSPath (G : LGraph) (P : List (Fin G.N)) : Prop :=
  P.length = G.H ∧ (∀ (i : ℕ) (h : i < P.length), G.layer P[i] = i + 1) ∧
    ∀ (i : ℕ) (h : i + 1 < P.length), G.arc P[i] P[i + 1] = true

/-- The extended formulation `Q^(r)` of (2)–(3) and the following constraints (PDF p. 5):
* (2) `x_{I∪{u}} + x_{I∪{v}} ≤ x_I` for `(u,v) ∈ (V_i × V_{i+1}) ∖ A`, `i ∈ {1, …, H-1}`, `|I| ≤ r`;
* (3) `∑_{v ∈ V_i} x_{I∪{v}} = x_I` for `i ∈ {1, …, H}`, `|I| ≤ r`;
* `x_{I∪{v}} ≤ x_I` for `v ∈ V`, `|I| ≤ r`;
* `x_∅ = 1`;
* `x_I ≥ 0` for `|I| ≤ r + 1`. -/
def InQ (G : LGraph) (r : ℕ) (x : Finset (Fin G.N) → ℝ) : Prop :=
  (∀ i, 1 ≤ i → i ≤ G.H - 1 → ∀ u v, G.layer u = i → G.layer v = i + 1 → G.arc u v = false →
    ∀ I : Finset (Fin G.N), I.card ≤ r → x (insert u I) + x (insert v I) ≤ x I) ∧
  (∀ i, 1 ≤ i → i ≤ G.H → ∀ I : Finset (Fin G.N), I.card ≤ r →
    ∑ v ∈ Finset.univ.filter (fun v => G.layer v = i), x (insert v I) = x I) ∧
  (∀ v (I : Finset (Fin G.N)), I.card ≤ r → x (insert v I) ≤ x I) ∧
  x ∅ = 1 ∧
  (∀ I : Finset (Fin G.N), I.card ≤ r + 1 → 0 ≤ x I)

/-- The conditioning `x^{|v}_I = x_{I∪{v}} / x_v` (PDF p. 5). -/
def cond {N : ℕ} (x : Finset (Fin N) → ℝ) (v : Fin N) : Finset (Fin N) → ℝ :=
  fun I => x (insert v I) / x {v}

/-- The lift `1_P^(r)` of the incidence vector of a vertex set `P`: `(1_P^(r))_I = ∏_{i∈I} 1_P(i)`,
i.e. `1` if `I ⊆ P` and `0` otherwise. -/
def liftInd {V : Type} [DecidableEq V] (P : Finset V) : Finset V → ℝ :=
  fun I => if I ⊆ P then 1 else 0

/-- A linear function `ℓ(y) = ∑_{I ∈ (V choose ≤ r+1)} ℓ_I y_I` evaluated at `y`. -/
def linEval {V : Type} [Fintype V] [DecidableEq V] (r : ℕ) (ℓ y : Finset V → ℝ) : ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Finset V)).filter (fun I => I.card ≤ r + 1), ℓ I * y I

/-! ## Algorithm 1: recursive randomized rounding (PDF p. 6)

`rrr G d h off x` runs Algorithm 1 on the `d^h` layers `off + 1, …, off + d^h` with point `x`;
its law is over `Option` paths, `none` meaning that the algorithm is not well defined on this run
(the sampled layer weights are not a probability vector, or it conditions on a vertex `u` with
`x_u = 0`). -/

/-- Line 2 of Algorithm 1: the law `P[v = w] = x_w` on the layer `i`, if these weights form a
probability vector. -/
def layerDist (G : LGraph) (x : Finset (Fin G.N) → ℝ) (i : ℕ) : Option (PMF (Fin G.N)) :=
  if h : (∀ w, G.layer w = i → 0 ≤ x {w}) ∧
      ∑ w, (if G.layer w = i then ENNReal.ofReal (x {w}) else 0) = 1 then
    some (PMF.ofFintype (fun w => if G.layer w = i then ENNReal.ofReal (x {w}) else 0) h.2)
  else none

/-- Lines 7–9 of Algorithm 1: with the current path `acc`, `k` remaining pieces of `blk` layers
starting after layer `off`, condition `x` on the last vertex `u` of `acc` and recurse. -/
def rrrTail (G : LGraph) (blk : ℕ)
    (sub : ℕ → (Finset (Fin G.N) → ℝ) → PMF (Option (List (Fin G.N))))
    (x : Finset (Fin G.N) → ℝ) : ℕ → ℕ → List (Fin G.N) → PMF (Option (List (Fin G.N)))
  | 0, _, acc => PMF.pure (some acc)
  | k + 1, off, acc =>
    match acc.getLast? with
    | none => PMF.pure none
    | some u =>
      if x {u} = 0 then PMF.pure none
      else (sub off (cond x u)).bind (fun o =>
        match o with
        | none => PMF.pure none
        | some Pi => rrrTail G blk sub x k (off + blk) (acc ++ Pi))

/-- Algorithm 1 on the layers `off + 1, …, off + d^h`. -/
def rrr (G : LGraph) (d : ℕ) : ℕ → ℕ → (Finset (Fin G.N) → ℝ) → PMF (Option (List (Fin G.N)))
  | 0, off, x =>
    match layerDist G x (off + 1) with
    | none => PMF.pure none
    | some μ => μ.map (fun v => some [v])
  | h + 1, off, x =>
    (rrr G d h off x).bind (fun o =>
      match o with
      | none => PMF.pure none
      | some P₁ => rrrTail G (d ^ h) (rrr G d h) x (d - 1) (off + d ^ h) P₁)

/-- `RRR(x)`: the output law of Algorithm 1 on `G` with `H = d^r` and `x ∈ Q^(r)`. -/
def RRR (G : LGraph) (d r : ℕ) (x : Finset (Fin G.N) → ℝ) : PMF (Option (List (Fin G.N))) :=
  rrr G d r 0 x

/-- `f(P)` for an optional path (`0` on `none`). -/
def fOpt {N : ℕ} (f : Finset (Fin N) → ℚ) : Option (List (Fin N)) → ℝ
  | none => 0
  | some P => (f P.toFinset : ℝ)

/-! ## Linear constraints `Dy ≤ b` and comparison distributions (§2.4, PDF p. 13) -/

/-- `Dy ≤ b` for an integer matrix `D ∈ ℤ^{m × (V choose ≤ r+1)}` and `b ∈ ℤ^m`. -/
def SatDb {N : ℕ} (r m : ℕ) (D : Fin m → Finset (Fin N) → ℤ) (b : Fin m → ℤ)
    (y : Finset (Fin N) → ℝ) : Prop :=
  ∀ j, linEval r (fun I => (D j I : ℝ)) y ≤ (b j : ℝ)

/-- A distribution `O` over layer-spanning paths with `E_{OPT∼O}[D 1^(r)_OPT] ≤ b`. -/
def FeasibleDist (G : LGraph) (r m : ℕ) (D : Fin m → Finset (Fin G.N) → ℤ) (b : Fin m → ℤ)
    (O : PMF (List (Fin G.N))) : Prop :=
  (∀ P ∈ O.support, IsLSPath G P) ∧
  ∀ j, pmfExp O (fun P => linEval r (fun I => (D j I : ℝ)) (liftInd P.toFinset)) ≤ (b j : ℝ)

/-! ## Encodings of the inputs and outputs of §2's algorithms -/

/-- All vertex sets of size at most `k`, in a fixed order (by size, then lexicographically). -/
def subsetsLe (N k : ℕ) : List (Finset (Fin N)) :=
  (List.range (k + 1)).flatMap (fun j => (List.sublistsLen j (List.finRange N)).map List.toFinset)

/-- Encoding of a layered graph: `[N, H]`, the layers, and the `N × N` arc matrix (0/1). -/
def encGraph (G : LGraph) : List ℤ :=
  [(G.N : ℤ), G.H] ++ (List.finRange G.N).map (fun v => (G.layer v : ℤ)) ++
    (List.finRange G.N).flatMap (fun u =>
      (List.finRange G.N).map (fun v => if G.arc u v then (1 : ℤ) else 0))

/-- Encoding of a rational point of `ℚ^{(V choose ≤ k)}` in the order of `subsetsLe N k`. -/
def encPoint (N k : ℕ) (x : Finset (Fin N) → ℚ) : List ℤ :=
  (subsetsLe N k).flatMap (fun I => encRat (x I))

/-- Encoding of `D, b`: `[m]`, the rows of `D` (coordinates in the order of `subsetsLe N (r+1)`),
then `b`. -/
def encDb (N r m : ℕ) (D : Fin m → Finset (Fin N) → ℤ) (b : Fin m → ℤ) : List ℤ :=
  [(m : ℤ)] ++ (List.finRange m).flatMap (fun j => (subsetsLe N (r + 1)).map (D j)) ++
    (List.finRange m).map b

/-- `⟨D, b⟩`: the encoding size of `D` and `b` (one plus the bit length of every entry). -/
def sizeDb (N r m : ℕ) (D : Fin m → Finset (Fin N) → ℤ) (b : Fin m → ℤ) : ℕ :=
  ∑ j, ∑ I ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun I => I.card ≤ r + 1),
      (1 + bitLen (D j I)) + ∑ j, (1 + bitLen (b j))

/-- Parse a rational point of `ℚ^{(V choose ≤ k)}` (coordinates outside are `0`). -/
def parsePoint (N k : ℕ) : Parser (Finset (Fin N) → ℚ) := do
  let L ← (subsetsLe N k).mapM (fun I => do let q ← pRat; pure (I, q))
  pure (tableFn L 0)

/-- Decode a rational point of `ℚ^{(V choose ≤ k)}` from a whole output. -/
def decodePoint (N k : ℕ) (out : List ℤ) : Option (Finset (Fin N) → ℚ) :=
  parseAll (parsePoint N k) out

/-- The vertices `t ∈ V_H` with `x_t > 0`, in increasing order. -/
def lastLayerSupport (G : LGraph) (x : Finset (Fin G.N) → ℚ) : List (Fin G.N) :=
  (List.finRange G.N).filter (fun t => G.layer t = G.H ∧ 0 < x {t})

/-- Output format of Lemma 5's algorithm: for each `t` of `lastLayerSupport G x` (in order) the
`H` vertices of the path `P_t`, then the coefficients of `ℓ` in the order of `subsetsLe N (r+1)`. -/
def decodeL5 (G : LGraph) (r : ℕ) (x : Finset (Fin G.N) → ℚ) (out : List ℤ) :
    Option ((Fin G.N → List (Fin G.N)) × (Finset (Fin G.N) → ℚ)) :=
  parseAll (do
    let ps ← (lastLayerSupport G x).mapM (fun t => do
      let P ← (List.range G.H).mapM (fun _ => pFin G.N)
      pure (t, P))
    let ℓ ← parsePoint G.N (r + 1)
    pure (tableFn ps [], ℓ)) out

/-- Output format of Lemma 8's algorithm: the indicator of `U` (`N` entries `0`/`1`), the point
`x` in the order of `subsetsLe N (r+1)`, and the positive integer `c_D`. -/
def decodeL8 (N r : ℕ) (out : List ℤ) : Option (Finset (Fin N) × (Finset (Fin N) → ℚ) × ℕ) :=
  parseAll (do
    let u ← (List.finRange N).mapM (fun v => do
      let z ← pInt
      if z = 0 ∨ z = 1 then pure (v, z = 1) else failure)
    let x ← parsePoint N (r + 1)
    let c ← pNat
    pure ((Finset.univ.filter (fun v => tableFn u false v = true)), x, c)) out

/-- Output format of Lemma 9's algorithm: the non-negative integer coefficients `ℓ̄_I` in the
order of `subsetsLe N (r+1)`, then `T̄`. -/
def decodeL9 (N r : ℕ) (out : List ℤ) : Option ((Finset (Fin N) → ℕ) × ℕ) :=
  parseAll (do
    let L ← (subsetsLe N (r + 1)).mapM (fun I => do let z ← pNat; pure (I, z))
    let T ← pNat
    pure (tableFn L 0, T)) out

/-- Expectation of a function of the output under a program's output law (`0` on `none`). -/
def outExp (μ : PMF (Option (List ℤ))) (g : List ℤ → ℝ) : ℝ :=
  pmfExp μ (fun o => match o with
    | none => 0
    | some σ => g σ)

end

end SubmodMDP.Policies


