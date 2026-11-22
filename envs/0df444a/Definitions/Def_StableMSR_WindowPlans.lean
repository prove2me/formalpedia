-- Prove2me | Definitions.Def_StableMSR_WindowPlans
-- name    : StableMSR_WindowPlans
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-21T16:07:50.474079+00:00
-- url     : https://prove2.me/theorems/6f47ff4a-8784-4faf-8255-600bbab708af
-- title:
--   Bounded binary tree plans for pairwise assignments of regional windows
-- statement:
--   A plan realizes a regional window system if its number of bags, table entries and raw join candidates satisfy explicit finite bounds and every attainable cluster count has a minimizing table entry realized by compatible window choices.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Lemmas 3.3, 3.8, 3.9(iii), 4.4, Proposition 4.2, Algorithm 1, and Appendix A.4–A.6. Alternative pairwise formulation using bounded-overlap window traces in the mission’s real-distance model.

import Definitions.Def_StableMSR_WindowCSP
import Definitions.Def_StableMSR_BinaryTreeDP_Recurrence
set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.TreeDP StableMSR.Recovery.OracleQueries StableMSR.Recovery.Supplement
namespace StableMSR.Recovery.WindowCSP
def admissible {V X : Type} (G : SimpleGraph V) (D : V→Finset X) (test : V→V→X→X→Prop) (f : V→X) :=
  (∀v,f v∈D v) ∧ ∀v w,G.Adj v w → test v w (f v) (f w)
def bagBound (x : World) (h w : ℕ) :=
  ((h+1)*CartesianBallRows.rows x.n (h+1)+1)^(w+1)
noncomputable def realizesWindows (x : World) (W : Cluster x.n) (R : ℝ) (h w : ℕ)
    (p : TreeDP.Plan ↥(greedyNet x.dist R W) (Partition x.n)) : Prop :=
  p.Coherent ∧ p.Local ∧ p.nodes≤2*x.n+1 ∧
  p.AllData (fun d=>d.bag.card≤w+1 ∧ d.choices.card≤bagBound x h w) ∧
  (∀cap,p.tableVolume cap≤(2*x.n+1)*(bagBound x h w*(cap+1)) ∧
    p.rawCandidateVolume cap≤(2*x.n+1)*((bagBound x h w)^3*(cap+1)^2)) ∧
  ∀cap j,j≤cap → ∀P : Pick x.n,valid x W R h P → number x W R P=j →
    ∃u∈TreeDP.solve cap p,∃Q : Pick x.n,
      u.2.1=j ∧ valid x W R h Q ∧ number x W R Q=j ∧ price x W R Q=u.2.2 ∧
      ∀P' : Pick x.n,valid x W R h P' → number x W R P'=j → u.2.2≤price x W R P'
end StableMSR.Recovery.WindowCSP


