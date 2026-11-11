-- Prove2me | Definitions.Def_LeeCutCertificates_Certificate_CutQueries
-- name    : LeeCutCertificates_Certificate_CutQueries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:17.591935+00:00
-- url     : https://prove2.me/theorems/d6e3fb22-3aca-40ed-8d1b-472c9d2c7324
-- title:
--   Exact cut queries, value certificates and witness certificates
-- statement:
--   Let $G$ be an undirected graph on $V=\{0,\ldots,n-1\}$ with arbitrary nonnegative real capacities. Parallel edge records contribute their summed capacity $w_G(u,v)$ to a distinct unordered pair; $w_G(v,v)=0$, so loops contribute nothing. A query shore $S\subseteq V$ returns its exact cut capacity $c_G(S)$. Write $\lambda(G)$ for the least capacity of a nonempty proper shore.
--
--   Two graphs agree on a finite family $Q$ when $c_{G'}(S)=c_G(S)$ for every $S\in Q$. A **value certificate** satisfies
--
--   $$\forall G'\ge0,\quad G'\text{ agrees on }Q\ \Longrightarrow\ \lambda(G')=\lambda(G).$$
--
--   Competitors have the same vertices but may use any edge records, including new positive pairs. A **witness certificate** additionally has a shore $S^*\in Q$ that is a minimum cut of $G$ and remains a minimum cut of every consistent nonnegative competitor. The certificate complexity $\operatorname{cert}(G)$ is the least cardinality of a value certificate. This is the exact optimization certificate interface used by the goal.
--
--   **Formalization Note** The graph, cut capacity and minimum-cut notions reuse the published graph module without its separate positivity, connectivity or aggregation predicates. Cardinalities and $\lceil\log_2 a\rceil$ are natural numbers; the logarithm is `Nat.clog 2`, with value zero at $a=0$. Certificate cardinality is a natural infimum; the goal asserts its attainment. All shores give a certificate. Theorems assume $n\ge2$, so the real minimum-cut value is finite and the published conversion from an extended-real minimum does not take its fallback value.
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), §§1–2 and Eq. (1), printed pp.1–3 (PDF pp.2–4); §6, printed p.17 (PDF p.18); Appendix A, printed p.53 (PDF p.54); pinned PDF sha256 853e2745e72c36e8e0567917faa6eedd8dfe99b4078a34a70d8d4b81516c372d (citation_basis: published, submission artifact, not an acceptance claim).

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph

set_option autoImplicit false
open scoped BigOperators
open SunMinCut.Cactus
open Classical

namespace LeeCutCertificates.Certificate

/-- Nonnegative edge-record capacities; no support or connectivity restriction. -/
def Nonnegative {n m : ℕ} (G : Graph n m) : Prop := ∀ e, 0 ≤ G.u e

/-- Aggregate capacity of a distinct unordered pair; loops contribute zero. -/
noncomputable def pairWeight {n m : ℕ} (G : Graph n m) (u v : Fin n) : ℝ :=
  if u = v then 0 else ∑ e ∈ Finset.univ.filter (fun e => G.ends e = s(u, v)), G.u e

/-- Exact cut-oracle agreement, allowing arbitrary competitor edge records. -/
def Agrees {n m k : ℕ} (G : Graph n m) (H : Graph n k)
    (Q : Finset (Finset (Fin n))) : Prop := ∀ S ∈ Q, cutw H S = cutw G S

/-- Equation (1): all nonnegative completions have the original optimum value. -/
def ValueCertificate {n m : ℕ} (G : Graph n m) (Q : Finset (Finset (Fin n))) : Prop :=
  ∀ (k : ℕ) (H : Graph n k), Nonnegative H → Agrees G H Q → lam H = lam G

/-- The queried shore is optimal in the input and in every nonnegative completion. -/
def WitnessCertificate {n m : ℕ} (G : Graph n m)
    (Q : Finset (Finset (Fin n))) (S : Finset (Fin n)) : Prop :=
  ValueCertificate G Q ∧ S ∈ Q ∧ IsMinCut G S ∧
    ∀ (k : ℕ) (H : Graph n k), Nonnegative H → Agrees G H Q → IsMinCut H S

/-- Least certificate cardinality. All shores form a certificate; the minimum is attained. -/
noncomputable def cert {n m : ℕ} (G : Graph n m) : ℕ :=
  sInf {k : ℕ | ∃ Q : Finset (Finset (Fin n)), ValueCertificate G Q ∧ Q.card = k}

/-- Ceiling of the base-two logarithm, with the conventional value zero at zero. -/
def ceilLog2 (a : ℕ) : ℕ := Nat.clog 2 a

end LeeCutCertificates.Certificate


