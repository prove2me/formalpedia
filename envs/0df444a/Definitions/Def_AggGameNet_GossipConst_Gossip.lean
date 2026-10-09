-- Prove2me | Definitions.Def_AggGameNet_GossipConst_Gossip
-- name    : AggGameNet_GossipConst_Gossip
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:30.587877+00:00
-- url     : https://prove2.me/theorems/b98301ec-d546-4d63-9c37-73021bf54d47
-- title:
--   §4.1 gossip draws and constant-step run
-- statement:
--   A static undirected graph $G$ connects the $N$ players. A waking player $I^k$ is uniform and contacts a neighbour $J^k$ with probability $p_{I^kJ^k}>0$; the pairs are independent across ticks. The matrix $W(k)=I-\tfrac12(e_{I^k}-e_{J^k})(e_{I^k}-e_{J^k})^\top$ averages the two contacted estimates. If $v_i^k$ is player $i$'s estimate, let $\hat v_i^k=\sum_j W(k)_{ij}v_j^k$ and $y^k=N^{-1}\sum_i v_i^k$. The update probability is $p_i=N^{-1}(1+\sum_jp_{ji})$.
--
--   A **gossip run** starts at a common deterministic profile $v^0=x^0\in K$. At every tick, only the contacted players project $x_i^k-\alpha_iF_i(x_i^k,N\hat v_i^k)$ onto $K_i$; all estimates obey $v_i^{k+1}=\hat v_i^k+x_i^{k+1}-x_i^k$. The file also defines $D(k)=W(k)-N^{-1}\mathbf1\mathbf1^\top$ on Euclidean player-coordinate vectors and the mean-square contraction property (30).
--
--   **Formalization Note** The Poisson clocks are represented by their discrete-time independent draws. A deterministic initial profile preserves independence of future draws from the current state. Projection is relational; nonempty compact convex $K_i$ makes it single-valued. The dimension-$N$ norm in (30) is Euclidean.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, (23)–(31), pp. 15–18; §4.3, p. 24

import Mathlib
import Definitions.Def_AggGameNet_GossipConst_Game
import Definitions.Def_AggGameNet_Gossip_Setting

open MeasureTheory ProbabilityTheory

namespace AggGameNet.GossipConst

noncomputable section

def gossipW {N : ℕ} (a b : Fin N) : Matrix (Fin N) (Fin N) ℝ :=
  1 - (1 / 2 : ℝ) • Matrix.vecMulVec (Pi.single a 1 - Pi.single b 1)
    (Pi.single a 1 - Pi.single b 1)

def W {N : ℕ} {Ω : Type*} (I J : ℕ → Ω → Fin N)
    (k : ℕ) (ω : Ω) : Matrix (Fin N) (Fin N) ℝ :=
  gossipW (I k ω) (J k ω)

def IsGossipRun {N n : ℕ} {Ω : Type*} (K : Fin N → Set (AggGameNet.Sync.E n))
    (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n) (I J : ℕ → Ω → Fin N)
    (alpha : Fin N → ℝ) (x v : ℕ → Ω → Fin N → AggGameNet.Sync.E n) : Prop :=
  ∃ x₀ : Fin N → AggGameNet.Sync.E n,
    (∀ i, x₀ i ∈ K i) ∧
    (∀ ω, x 0 ω = x₀ ∧ v 0 ω = x₀) ∧
    ∀ ω k i,
      (AggGameNet.Gossip.upd I J k ω i →
        AggGameNet.Gossip.IsProj (K i)
          (x k ω i - alpha i • F i (x k ω i) ((N : ℝ) • AggGameNet.Gossip.vhat I J v k ω i))
          (x (k+1) ω i)) ∧
      (¬ AggGameNet.Gossip.upd I J k ω i → x (k+1) ω i = x k ω i) ∧
      v (k+1) ω i = AggGameNet.Gossip.vhat I J v k ω i + x (k+1) ω i - x k ω i

def Dk {N : ℕ} {Ω : Type*} (I J : ℕ → Ω → Fin N)
    (k : ℕ) (ω : Ω) (z : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm
    (fun i => ∑ j, (W I J k ω i j - (1 / (N : ℝ))) * z j)

def coord {N n : ℕ} {Ω : Type*} (v : ℕ → Ω → Fin N → AggGameNet.Sync.E n)
    (k : ℕ) (ω : Ω) (ell : Fin n) : EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm (fun i => v k ω i ell)

def centeredCoord {N n : ℕ} {Ω : Type*}
    (v : ℕ → Ω → Fin N → AggGameNet.Sync.E n) (k : ℕ) (ω : Ω) (ell : Fin n) :
    EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm
    (fun i => v k ω i ell - AggGameNet.Gossip.yavg v k ω ell)

def Contraction30 {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (I J : ℕ → Ω → Fin N) (lam : ℝ) : Prop :=
  ∀ k (z : EuclideanSpace ℝ (Fin N)),
    (∫⁻ ω, ENNReal.ofReal (‖Dk I J k ω z‖ ^ 2) ∂P) ≤
      ENNReal.ofReal (lam * ‖z‖ ^ 2)

end
end AggGameNet.GossipConst


