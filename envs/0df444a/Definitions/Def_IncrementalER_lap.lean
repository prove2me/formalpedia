-- Prove2me | Definitions.Def_IncrementalER_lap
-- name    : IncrementalER_lap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:30.613203+00:00
-- url     : https://prove2.me/theorems/2384dc8e-30a2-4195-b6ff-256edf3c33df
-- title:
--   Graphs as conductance functions: Laplacian, degrees, $R_{\mathrm{eff}}$, leverage degree $\ell^G$, excess $q^G$
-- statement:
--   A graph $G=(V,E,c)$ on a finite vertex set $V$ is given by its conductances $c(x,y)=c(y,x)\ge0$, with $c(x,x)=0$; parallel edges are merged by adding their capacities. $G$ is **connected** if the graph $x\sim y\iff c(x,y)>0$ is connected; $G$ is connected on $W\subseteq V$ if it is supported on $W$ and connected there. For $v\in V$:
--
--   1. the Laplacian: $L_G(x,x)=\sum_{w\neq x}c(x,w)$ and $L_G(x,y)=-c(x,y)$ for $x\neq y$;
--   2. the combinatorial degree $\deg(v)=|\{w\neq v: c(v,w)>0\}|$ and the capacitated degree $d_v=\sum_w c(v,w)$;
--   3. the effective resistance $R_{\mathrm{eff}}(u,v)=(\mathbf 1_u-\mathbf 1_v)^\top L_G^\dagger(\mathbf 1_u-\mathbf 1_v)$;
--   4. the leverage degree and the excess
--
--   $$\ell^G(v)=\sum_{w\neq v}c(v,w)\,R_{\mathrm{eff}}(v,w),\qquad q^G(v)=\ell^G(v)-2 .$$
--
--   The leverage degree is the sum of the leverage scores $\tau_e=c_eR_{\mathrm{eff}}(e)$ of the edges at $v$ (Definition 3.5).
--
--   **Formalization Note** Merging parallel edges changes neither $L_G$, $R_{\mathrm{eff}}$, $\ell^G$ nor the random walk. It makes $\deg(v)$ the number of distinct neighbours, at most the multigraph degree. $d_v$ is the published `MarkovMixing.vertexConductance`.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), §3: notation, p.10; Reff and leverage scores, p.11; Definition 3.5, p.12

import Mathlib
import Definitions.Def_mm_network
import Definitions.Def_IncrementalER_energy

open Matrix

namespace IncrementalER

/-!
# Graphs as conductance functions: Laplacian, degrees, resistance, leverage degree, excess

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), §3: notation (p.10),
`Reff` and leverage scores (p.11), Definition 3.5 (leverage degree and excess, p.12).

**Formalization Note.**
* A graph `G = (V, E, c)` on a finite vertex type is its conductance function `c : V → V → ℝ`:
  symmetric, nonnegative (the published `MarkovMixing.IsConductance`) and zero on the diagonal.
  A multigraph is represented by the sum of its parallel capacities; the Laplacian, effective
  resistances, leverage degrees and the random walk are unchanged by this collapse. The
  combinatorial degree `deg(v)` becomes the number of distinct neighbours, which is at most the
  multigraph degree.
* The capacitated degree `d_v = ∑_w c(v, w)` is `MarkovMixing.vertexConductance`.
* "Connected" is connectivity of the simple graph `x ~ y ⟺ x ≠ y ∧ c(x, y) > 0`; Mathlib's
  `Connected` includes nonemptiness. `IsConnectedOn c W` says `c` is supported on `W` and connected
  there; it is used for graphs living on a subset of the vertices.
* `Reff(u, v) = (1u − 1v)⊤ L† (1u − 1v)` with the published pseudoinverse (p.11). The leverage
  degree `ℓ^G(v) = ∑_{e ∋ v} c_e Reff(e)` sums over the neighbours `w ≠ v` (a loop has resistance
  `0`).
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `c` is a graph: a symmetric nonnegative conductance function with zero diagonal. -/
def IsGraph (c : V → V → ℝ) : Prop :=
  MarkovMixing.IsConductance c ∧ ∀ x, c x x = 0

/-- The simple graph of `c`: `x ~ y` iff `x ≠ y` and `c(x, y) > 0` (or `c(y, x) > 0`). -/
def adj (c : V → V → ℝ) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => 0 < c x y

/-- `G` is connected (the standing assumption of p.10). -/
def Connected (c : V → V → ℝ) : Prop :=
  (adj c).Connected

/-- `c` is supported on `W` and the graph it induces on `W` is connected. -/
def IsConnectedOn (c : V → V → ℝ) (W : Finset V) : Prop :=
  (∀ x y, c x y ≠ 0 → x ∈ W ∧ y ∈ W) ∧ ((adj c).induce (W : Set V)).Connected

/-- The graph Laplacian `L_G`: `L(x, x) = ∑_{w ≠ x} c(x, w)`, `L(x, y) = −c(x, y)` for `x ≠ y`. -/
def lap (c : V → V → ℝ) : Matrix V V ℝ :=
  fun x y => if x = y then ∑ w ∈ Finset.univ.erase x, c x w else -c x y

/-- The combinatorial degree `deg(v)`: the number of neighbours `w ≠ v` with `c(v, w) > 0`. -/
noncomputable def deg (c : V → V → ℝ) (v : V) : ℕ :=
  (Finset.univ.filter fun w => w ≠ v ∧ 0 < c v w).card

/-- The capacitated degree `d_v = ∑_w c(v, w)` (p.10). -/
noncomputable def capDeg (c : V → V → ℝ) (v : V) : ℝ :=
  MarkovMixing.vertexConductance c v

/-- The effective resistance `Reff(u, v) = (1u − 1v)⊤ L_G† (1u − 1v)` (p.11). -/
noncomputable def reff (c : V → V → ℝ) (u v : V) : ℝ :=
  energy (lap c) (Pi.single u 1 - Pi.single v 1)

/-- The leverage degree `ℓ^G(v) = ∑_{e = (v, w)} τ_e = ∑_{w ≠ v} c(v, w) Reff(v, w)`
(Definition 3.5, p.12). -/
noncomputable def levDeg (c : V → V → ℝ) (v : V) : ℝ :=
  ∑ w ∈ Finset.univ.erase v, c v w * reff c v w

/-- The excess `q^G(v) = ℓ^G(v) − 2` (Definition 3.5, p.12). -/
noncomputable def excess (c : V → V → ℝ) (v : V) : ℝ :=
  levDeg c v - 2

end IncrementalER


