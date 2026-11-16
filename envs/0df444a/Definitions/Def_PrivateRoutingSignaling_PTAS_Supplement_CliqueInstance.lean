-- Prove2me | Definitions.Def_PrivateRoutingSignaling_PTAS_Supplement_CliqueInstance
-- name    : PrivateRoutingSignaling_PTAS_Supplement_CliqueInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:43:37.732472+00:00
-- url     : https://prove2.me/theorems/82bd0a0c-72f3-4d1a-ac63-f86a8084e34f
-- title:
--   The §4 CLIQUE construction: hard state $H$, dual $Y$, auxiliary states $P_\ell,Q_\ell$ and priors
-- statement:
--   Let $G$ be a simple graph on vertices $1,\dots,N$ with symmetric adjacency matrix $M$ and degrees $d_i$. The network has $n=2N$ parallel arcs (paths) $1,\dots,2N$.
--
--   1. The **hard state** $H$ has $c_i^H(x)=\frac{N}{3N+d_i}x$ and $c_{N+i}^H(x)=x$ for $i\in[N]$.
--   2. The **designated dual solution** has $Y_{i,N+i}=2$, $Y_{i,N+j}=M_{ij}/N$ for $i\neq j$, and all other entries zero.
--   3. With $Z=\frac1{4N}$ and $S_\ell=\{j:Y_{\ell,N+j}>0\}$, state $P_\ell$ has $c_\ell=Z$, $c_{N+j}(x)=\frac{Z(3+d_\ell/N)}{Y_{\ell,N+j}}x$ for $j\in S_\ell$, and every other arc constant $1$.
--   4. State $Q_\ell$ has $c_{N+\ell}=0$ and every other arc constant $1$.
--   5. With $\Delta=\frac1{4N^3}$, $T=\frac1{2^{12}N^4}$ and $\lambda_H=\frac{T\Delta}2$, the priors are $\lambda_H$ on $H$, $\frac1{4N^2}$ on each $P_\ell$, $\frac1{2N}$ on each $Q_\ell$, and $\frac12-\frac1{4N}-\lambda_H$ on a dummy state with zero latency on every arc.
--
--   The auxiliary dual objective is
--
--   $$
--   D^{\mathrm{aux}}(y)=\frac1{4N^2}\sum_{\ell=1}^ND^{P_\ell}(y)+\frac1{2N}\sum_{\ell=1}^ND^{Q_\ell}(y).
--   $$
--
--   This is the private signaling instance of Lemma 4.8, used in the reduction from CLIQUE behind Theorem 4.9.
--
--   **Formalization Note** Arcs are numbered $0,\dots,2N-1$ and states $0=H$, $1+\ell=P_\ell$, $N+1+\ell=Q_\ell$ (for $0\le\ell<N$), $2N+1$ the dummy. A dual matrix on arcs is read on paths through their single arc.
-- source:
--   Yu Cheng, Tianle Jiang, The Complexity of Private Signaling in Nonatomic Routing Games, STOC 2027 submission #439 (October 2026), proof of Theorem 4.2 p. 16 (a_i, y), §4.2 p. 17 (H, Δ), §4.3 p. 19 (Q_ℓ, P_ℓ, Z, S_ℓ), §4.4 pp. 22–23 (priors, D^aux, T, λ_H, dummy state); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf; SHA-256 766b4afa05d6c7c4c106ed83a73221ca4d951eeca5cce863930177ed26fd4e61

import Mathlib
import Definitions.Def_PrivateRoutingSignaling_PTAS_Supplement_Dual

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS.Supplement

open PrivateRoutingSignaling.PTAS

/-- A parallel network: `n` arcs from the source (node 0) to the sink (node 1), so its paths are
exactly the `n` one-arc paths (§4, p. 15). -/
def parallelNetwork (n : ℕ) : RoutingNetwork :=
  ⟨2, n, ⟨fun _ => 0, fun _ => 1⟩, 0, 1, 1⟩

/-- An arc-indexed matrix, read on paths through their (single) arcs; entries between paths that
are not single arcs are zero (there are none in a parallel network). -/
def liftSingle {N : RoutingNetwork} (Y : Fin N.arcs → Fin N.arcs → ℝ) : DualMatrix N :=
  fun p q => match pathArcs N p, pathArcs N q with
    | [i], [j] => Y i j
    | _, _ => 0

namespace Clique

variable (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

/-- Degree `d_i = deg_G(i)` of the vertex with index `i < N` (zero for other indices). -/
def deg (i : ℕ) : ℝ := if h : i < N then (G.degree ⟨i, h⟩ : ℝ) else 0

/-- Adjacency matrix entry `M_{ij}` for vertex indices `i, j < N` (zero otherwise). -/
def adj (i j : ℕ) : ℝ :=
  if h : i < N ∧ j < N then (if G.Adj ⟨i, h.1⟩ ⟨j, h.2⟩ then 1 else 0) else 0

/-- The designated dual solution of the proof of Theorem 4.2 (p. 16), on arc indices
`0, …, 2N−1`: `Y_{i,N+i} = 2`, `Y_{i,N+j} = M_{ij}/N` for `i ≠ j`, all other entries zero. -/
noncomputable def Yn (i j : ℕ) : ℝ :=
  if i < N ∧ j = N + i then 2
  else if i < N ∧ N ≤ j ∧ j ≠ N + i then adj N G i (j - N) / N else 0

noncomputable def Y : DualMatrix (parallelNetwork (2 * N)) :=
  liftSingle (fun a b => Yn N G a.val b.val)

/-- `Z = 1/(4N)` (p. 19). -/
noncomputable def Z : ℝ := 1 / (4 * N)

/-- `Δ = 1/(4N³)` (p. 17). -/
noncomputable def gap : ℝ := 1 / (4 * (N : ℝ) ^ 3)

/-- `T = 1/(2¹² N⁴)` (p. 23). -/
noncomputable def T : ℝ := 1 / (2 ^ 12 * (N : ℝ) ^ 4)

/-- `λ_H = TΔ/2` (p. 23). -/
noncomputable def priorH : ℝ := T N * gap N / 2

/-- Hard state `H` (p. 17): `c_i(x) = N/(3N+d_i)·x`, `c_{N+i}(x) = x`. -/
noncomputable def hardLatency (a : ℕ) (x : ℝ) : ℝ :=
  if a < N then (N : ℝ) / (3 * N + deg N G a) * x else x

/-- State `P_ℓ` (p. 19): `c_ℓ = Z`, `c_{N+j}(x) = Z(3+d_ℓ/N)/Y_{ℓ,N+j}·x` for
`j ∈ S_ℓ = {j : Y_{ℓ,N+j} > 0}`, every other arc constant one. -/
noncomputable def pLatency (ℓ a : ℕ) (x : ℝ) : ℝ :=
  if a = ℓ then Z N
  else if N ≤ a ∧ 0 < Yn N G ℓ a then Z N * (3 + deg N G ℓ / N) / Yn N G ℓ a * x
  else 1

/-- State `Q_ℓ` (p. 19): `c_{N+ℓ} = 0`, every other arc constant one. -/
def qLatency (ℓ a : ℕ) (_x : ℝ) : ℝ := if a = N + ℓ then 0 else 1

/-- States `0 = H`, `1+ℓ = P_ℓ`, `N+1+ℓ = Q_ℓ` (`ℓ < N`), and `2N+1` = the zero-latency dummy. -/
noncomputable def latency (θ : Fin (2 * N + 2)) (a : Fin (2 * N)) (x : ℝ) : ℝ :=
  if θ.val = 0 then hardLatency N G a.val x
  else if θ.val ≤ N then pLatency N G (θ.val - 1) a.val x
  else if θ.val ≤ 2 * N then qLatency N (θ.val - N - 1) a.val x
  else 0

/-- Priors (p. 23): `λ_H`, `λ_{P_ℓ} = 1/(4N²)`, `λ_{Q_ℓ} = 1/(2N)`, dummy `1/2 − 1/(4N) − λ_H`. -/
noncomputable def prior (θ : Fin (2 * N + 2)) : ℝ :=
  if θ.val = 0 then priorH N
  else if θ.val ≤ N then 1 / (4 * (N : ℝ) ^ 2)
  else if θ.val ≤ 2 * N then 1 / (2 * N)
  else 1 / 2 - 1 / (4 * N) - priorH N

/-- The private signaling instance of §4.4 (p. 23) built from the CLIQUE graph `G`. -/
noncomputable def inst : Instance where
  network := parallelNetwork (2 * N)
  states := 2 * N + 2
  prior := prior N
  latency := latency N G

def hState : Fin (2 * N + 2) := ⟨0, by omega⟩
def pState (ℓ : Fin N) : Fin (2 * N + 2) := ⟨1 + ℓ.val, by omega⟩
def qState (ℓ : Fin N) : Fin (2 * N + 2) := ⟨N + 1 + ℓ.val, by omega⟩

/-- `D^aux(y) = (1/(4N²)) ∑_ℓ D^{P_ℓ}(y) + (1/(2N)) ∑_ℓ D^{Q_ℓ}(y)` (p. 22). -/
noncomputable def daux (y : DualMatrix (parallelNetwork (2 * N))) : ℝ :=
  ∑ ℓ : Fin N, dualValue (inst N G) (pState N ℓ) y / (4 * (N : ℝ) ^ 2) +
    ∑ ℓ : Fin N, dualValue (inst N G) (qState N ℓ) y / (2 * N)

end Clique

end PrivateRoutingSignaling.PTAS.Supplement


