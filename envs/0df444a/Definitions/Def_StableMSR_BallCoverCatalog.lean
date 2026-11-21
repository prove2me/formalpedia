-- Prove2me | Definitions.Def_StableMSR_BallCoverCatalog
-- name    : StableMSR_BallCoverCatalog
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-20T20:23:00.457569+00:00
-- url     : https://prove2.me/theorems/b19d7ea4-8f54-4bce-b0bf-94e793c60b67
-- title:
--   Ball-cover certificates for stable sum-of-radii recovery
-- statement:
--   Rows store pairs of centers and points determining radii. Valid rows have distinct centers and cover the instance. The selector minimizes the nominal sum of the radii, assigns each center to itself, and writes a fallback labeling when no row is valid.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1 and Theorem 1.1. Finite deterministic RAM implementation and ball-cover certification.

import Definitions.Def_StableMSR_OracleQueries
set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
namespace StableMSR.Recovery.BallCoverCatalog
def addr (k r j : ℕ) := 3+2*(r*k+j)
def center (x : World) (r j : ℕ) := x.mem (addr x.k r j)
def witness (x : World) (r j : ℕ) := x.mem (addr x.k r j+1)
noncomputable def charge (x : World) (r j : ℕ) :=
  MinSumFPT.oracleAnswer x.dist (center x r j) (witness x r j)
noncomputable def hits (x : World) (r i j : ℕ) : Prop :=
  MinSumFPT.oracleAnswer x.dist (center x r j) (i:ℤ) ≤ charge x r j
def endpoints (x : World) := ∀r < x.rows,∀j < x.k,∃ c w : Fin x.n,
  center x r j=(c.val:ℤ) ∧ witness x r j=(w.val:ℤ)
noncomputable def good (x : World) (r : ℕ) : Prop :=
  (∀j < x.k,∀l < x.k,center x r j=center x r l → j=l) ∧
  ∀i < x.n,∃j < x.k,hits x r i j
noncomputable def score (x : World) (r : ℕ) := ∑j ∈ Finset.range x.k,charge x r j
noncomputable def wins (x : World) (r : ℕ) := good x r ∧ ∀u < x.rows,good x u →
  score x r < score x u ∨ score x r=score x u ∧ r ≤ u
noncomputable def first (k : ℕ) (P : ℕ→Prop) : ℤ :=
  ∑j ∈ Finset.range k,if P j ∧ ∀l < k,l < j → ¬P l then (j:ℤ) else 0
noncomputable def assigned (x : World) (r i : ℕ) : ℤ :=
  if ∃j < x.k,center x r j=(i:ℤ) then first x.k (fun j=>center x r j=(i:ℤ))
  else first x.k (fun j=>hits x r i j)
noncomputable def output (x : World) (i : ℕ) : ℤ :=
  if ∃r < x.rows,good x r then ∑r ∈ Finset.range x.rows,if wins x r then assigned x r i else 0
  else if (i:ℤ) < (x.k:ℤ) then (i:ℤ) else (x.k:ℤ)-1
def worldOf {n : ℕ} (k rows : ℕ) (d : Point n→Point n→ℝ) (s : Store) : World :=
  ⟨n,k,rows,d,fun i=>s.imem (i:ℤ)⟩
def HasCatalog (e : ℚ) (a b : ℕ) (cmd : Cmd) := ∀ (n k : ℕ) (d : Point n→Point n→ℝ),
  1 ≤ k → k ≤ n → IsMetricArray d →
    ∃s z rows,Executes d cmd (initialStore n k) s z ∧
      z ≤ a*n^(b*parameterEnvelope (e:ℝ)) ∧ rows ≤ a*n^(b*parameterEnvelope (e:ℝ)) ∧
      let x := worldOf k rows d s
      Ready x s ∧ endpoints x ∧ ∀O,Stable d k (1+(e:ℝ)) O →
        ∃r < rows,good x r ∧ score x r ≤ cost d O
end StableMSR.Recovery.BallCoverCatalog


