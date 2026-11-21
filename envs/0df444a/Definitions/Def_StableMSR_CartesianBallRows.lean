-- Prove2me | Definitions.Def_StableMSR_CartesianBallRows
-- name    : StableMSR_CartesianBallRows
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-20T20:27:31.431833+00:00
-- url     : https://prove2.me/theorems/ec1ef5ee-5cb6-4024-91d7-d20c9898329b
-- title:
--   Cartesian products of center and radius witnesses
-- statement:
--   Enumerate all ordered pairs of centers and radial witnesses in base n. A row has two digits for each cluster. A separate one-row catalog represents the singleton partition.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1 and Theorem 1.1. Finite deterministic RAM implementation and ball-cover certification.

import Definitions.Def_StableMSR_BallCoverCatalog
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
namespace StableMSR.Recovery.CartesianBallRows
def digit (n r j : ℕ) := r / n^j % n
def rows (n k : ℕ) := n^(2*k)
def pairs (x : World) : Prop := x.rows=rows x.n x.k ∧
  ∀r < x.rows,∀j < x.k,center x r j=(digit x.n r (2*j):ℤ) ∧ witness x r j=(digit x.n r (2*j+1):ℤ)
def identityPairs (x : World) : Prop := x.rows=1 ∧ ∀j < x.k,center x 0 j=(j:ℤ) ∧ witness x 0 j=(j:ℤ)
def runSpec (e : ℚ) (a b : ℕ) (cmd : Cmd) (n k : ℕ) (d : Point n→Point n→ℝ) : Prop :=
  ∃s z H,Executes d cmd (initialStore n k) s z ∧
    z ≤ a*n^(b*parameterEnvelope (e:ℝ)) ∧ H ≤ a*n^(b*parameterEnvelope (e:ℝ)) ∧
    let x := worldOf k H d s
    Ready x s ∧ endpoints x ∧ ∀O,Stable d k (1+(e:ℝ)) O →
      ∃r < H,good x r ∧ score x r ≤ cost d O
end StableMSR.Recovery.CartesianBallRows


