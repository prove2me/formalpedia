-- Prove2me | Definitions.Def_FracColorLocal_KrFree_Walk
-- name    : FracColorLocal_KrFree_Walk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:12:20.333699+00:00
-- url     : https://prove2.me/theorems/66fcf5b6-8dd9-4fe4-8837-2bafdaba12ad
-- title:
--   Neighbourhood walks P_x, Q_x, K^j_x, the laws ν and τ, H_j, the sets S_i(v), B_v and tests (8.10)–(8.11)
-- statement:
--   Let $F$ be a finite graph with positive vertex weights $w$ and parameters $\theta$, $t\ge 32$ an integer and $R_t=2^t$. Write $C_{xv}=w(N(x)\cap N(v))$ and $T=T_F(w)$ (each unordered triangle once).
--
--   - **Walks** (§8.2): on $N(x)$, $P_x(v,z)=w(z)\mathbf 1_{vz\in E(F)}/C_{xv}$, $Q_x=(I+P_x)/2$, $K^j_x=P_xQ_x^j$ ($j\ge 0$).
--   - **Laws**: $\nu(x,v)=w(x)w(v)C_{xv}/(6T)$ on directed edges and $\tau(x,v,z)=w(x)w(v)w(z)/(6T)$ on ordered triangles (8.6).
--   - **Averaged entropy**: $H_j=\mathbb E_{(x,v)\sim\nu}H_{s_x}(K^j_x(v,\cdot))$ with $s_x(y)=w(y)/\theta_x$ on $N(x)$, and the averaged distance $\mathbb E_{(x,v,z)\sim\tau}\|K^j_x(v,\cdot)-K^j_x(z,\cdot)\|_{\mathrm{TV}}$.
--   - **Sets** (§8.3): $S_0(v)=N(v)$, $S_{i+1}(v)=S_i(v)\cup\{y: w(N(y)\cap S_i(v))\ge\theta_v/(t^7R_t^2)\}$; and $B_v=\{x\in N(v): w(N(x)\cap S_t(v))>t^{10}\theta_x\}$.
--   - **Tests** at $v$:
--     $$e_w(N(v),S_t(v))\le 24\big(30t^3 b(N(v))+\theta_v^2 2^{-30t^3}\big)\ \ (8.10),\qquad e_w(B_v,N(v))\le 24\big(2t\,b(B_v)+\theta_v^2 2^{-2t}\big)\ \ (8.11).$$
--
--   **Formalization Note** $P_x,Q_x,K^j_x$ are $V\times V$ real matrices whose entries vanish outside $N(x)\times N(x)$ (rows $v\in N(x)$ are the walk's transition probabilities); $\nu$ and $\tau$ are real functions, zero off directed edges and ordered triangles; expectations are the corresponding finite sums. $S_i(v)$ is defined for every $i$ by recursion (only $i\le t$ is used).
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), pp. 34–37 (PDF 35–38), §8.2–§8.5, (8.6), (8.10), (8.11)

import Mathlib
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_FracColorLocal_KrFree_Constants
import Definitions.Def_FracColorLocal_KrFree_Dichotomy
import Definitions.Def_FracColorLocal_KrFree_Entropy

namespace FracColorLocal.KrFree

open OAI.CliqueFreeIndependence.WeightedGraph

variable {V : Type*} [Fintype V]

/-- The neighbourhood walk at the centre `x` (§8.2):
`P_x(v, z) := w(z) 1_{vz ∈ E} / C_xv` for `v, z ∈ N(x)`, with `C_xv := w(N(x) ∩ N(v))`
(`commonMass`); rows and columns outside `N(x)` are zero. -/
noncomputable def walkP (G : SimpleGraph V) (w : V → ℝ) (x : V) : Matrix V V ℝ := by
  classical
  exact fun v z => if G.Adj x v ∧ G.Adj x z ∧ G.Adj v z then w z / commonMass G w x v else 0

/-- The lazy walk `Q_x := (I + P_x)/2` (§8.2). -/
noncomputable def walkQ (G : SimpleGraph V) (w : V → ℝ) (x : V) : Matrix V V ℝ := by
  classical
  exact (1 / 2 : ℝ) • (1 + walkP G w x)

/-- The kernel `K^j_x := P_x Q_x^j` (§8.2). -/
noncomputable def walkK (G : SimpleGraph V) (w : V → ℝ) (x : V) (j : ℕ) : Matrix V V ℝ := by
  classical
  exact walkP G w x * walkQ G w x ^ j

/-- `ν(x, v) := w(x) w(v) C_xv / (6T)` on directed edges `(x, v)` (zero otherwise), with
`T := T_G(w)` the triangle weight (§8.2). -/
noncomputable def edgeLaw (G : SimpleGraph V) (w : V → ℝ) (x v : V) : ℝ := by
  classical
  exact if G.Adj x v then w x * w v * commonMass G w x v / (6 * triangleMass G w) else 0

/-- `τ(x, v, z) := w(x) w(v) w(z) / (6T)` on ordered triangles (zero otherwise) (8.6). -/
noncomputable def triangleLaw (G : SimpleGraph V) (w : V → ℝ) (x v z : V) : ℝ := by
  classical
  exact if G.Adj x v ∧ G.Adj v z ∧ G.Adj x z then w x * w v * w z / (6 * triangleMass G w) else 0

/-- The averaged entropy `H_j := E_{(x,v) ∼ ν} H_{s_x}(K^j_x(v, ·))` with `s_x(y) := w(y)/θ_x` on
`N(x)` (§8.5). -/
noncomputable def avgEntropy (G : SimpleGraph V) (w θ : V → ℝ) (j : ℕ) : ℝ :=
  ∑ x, ∑ v, edgeLaw G w x v *
    entropyOn (neighbors G x) (fun y => w y / θ x) (fun y => walkK G w x j v y)

/-- `E_{(x,v,z) ∼ τ} ‖K^j_x(v, ·) - K^j_x(z, ·)‖_TV` (8.18). -/
noncomputable def avgTriangleTV (G : SimpleGraph V) (w : V → ℝ) (j : ℕ) : ℝ :=
  ∑ x, ∑ v, ∑ z, triangleLaw G w x v z * tvDist (walkK G w x j v) (walkK G w x j z)

/-- The sets `S_i(v)` of §8.3: `S_0(v) := N(v)` and
`S_{i+1}(v) := S_i(v) ∪ {y : w(N(y) ∩ S_i(v)) ≥ θ_v / (t⁷ R_t²)}`. -/
noncomputable def reachSet (G : SimpleGraph V) (w θ : V → ℝ) (t : ℕ) (v : V) : ℕ → Finset V := by
  classical
  exact fun i => Nat.rec (neighbors G v)
    (fun _ S => S ∪ Finset.univ.filter
      (fun y => θ v / ((t : ℝ) ^ 7 * (Rt t : ℝ) ^ 2) ≤ mass w (neighbors G y ∩ S))) i

/-- `B_v := {x ∈ N(v) : w(N(x) ∩ S_t(v)) > t^{10} θ_x}` (§8.4). -/
noncomputable def exceptionalSet (G : SimpleGraph V) (w θ : V → ℝ) (t : ℕ) (v : V) : Finset V := by
  classical
  exact (neighbors G v).filter
    (fun x => (t : ℝ) ^ 10 * θ x < mass w (neighbors G x ∩ reachSet G w θ t v t))

/-- Test (8.10) at `v`: `e_w(N(v), S_t(v)) ≤ 24 (30 t³ b(N(v)) + θ_v² 2^{-30 t³})`. -/
def Test810 (G : SimpleGraph V) (w θ : V → ℝ) (t : ℕ) (v : V) : Prop :=
  crossMass G w (neighbors G v) (reachSet G w θ t v t) ≤
    24 * (30 * (t : ℝ) ^ 3 * bMass θ w (neighbors G v) +
      θ v ^ 2 * (2 : ℝ) ^ (-((30 * t ^ 3 : ℕ) : ℤ)))

/-- Test (8.11) at `v`: `e_w(B_v, N(v)) ≤ 24 (2t b(B_v) + θ_v² 2^{-2t})`. -/
def Test811 (G : SimpleGraph V) (w θ : V → ℝ) (t : ℕ) (v : V) : Prop :=
  crossMass G w (exceptionalSet G w θ t v) (neighbors G v) ≤
    24 * (2 * (t : ℝ) * bMass θ w (exceptionalSet G w θ t v) +
      θ v ^ 2 * (2 : ℝ) ^ (-((2 * t : ℕ) : ℤ)))

end FracColorLocal.KrFree


