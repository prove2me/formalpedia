-- Prove2me | Definitions.Def_LeeCutCertificates_Certificate_Supplement_Quotients
-- name    : LeeCutCertificates_Certificate_Supplement_Quotients
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:02:36.790625+00:00
-- url     : https://prove2.me/theorems/7024fd3e-e3b7-4324-b72e-7a3f32087de1
-- title:
--   Quotient partitions, safety and learned-tree output
-- statement:
--   A partition $P$ assigns every original vertex to one of finitely many nonempty labeled blocks. The quotient maps edge endpoints to their blocks, sums parallel capacities in cuts and ignores loops. If $A$ is a set of blocks, its lift is their union and
--
--   $$c_{G/P}(A)=c_G\!\left(\bigcup_{B\in A}B\right).$$
--
--   Safety requires that every original minimum-cut shore is such a union and that the minimum-cut value is preserved. The learned-tree output stores a partition and a capacitated tree whose terminals are precisely its block labels. Its correctness predicate requires safety, the all-shore $\alpha$ approximation and at most $8n$ tree nodes.
--
--   **Formalization Note** A surjective map into `Fin parts` labels the blocks without changing the set of partitions. Contracted loops remain harmless zero-cut records. No safety or approximation condition is stored as an output-type field.
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), §3.1, printed p.7 (PDF p.8); Theorem 7, printed p.12 (PDF p.13); §11.7, printed pp.40–41 (PDF pp.41–42)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_TerminalTrees

set_option autoImplicit false
open Classical
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

/-- Nonempty blocks labeled by Fin parts; labels carry no mathematical order. -/
structure QuotientPartition (n : ℕ) where
  parts : ℕ
  block : Fin n → Fin parts
  onto : Function.Surjective block

/-- Contract endpoints. Parallel records aggregate in cutw, and loops contribute zero. -/
def QuotientPartition.graph {n m : ℕ} (P : QuotientPartition n) (G : Graph n m) :
    Graph P.parts m where
  ends e := (G.ends e).map P.block
  u := G.u

noncomputable def QuotientPartition.lift {n : ℕ} (P : QuotientPartition n)
    (S : Finset (Fin P.parts)) : Finset (Fin n) :=
  Finset.univ.filter fun v => P.block v ∈ S

/-- Every original optimum survives, and the exact optimum value is unchanged. -/
def QuotientPartition.Safe {n m : ℕ} (P : QuotientPartition n) (G : Graph n m) : Prop :=
  lam (P.graph G) = lam G ∧ ∀ S, IsMinCut G S → ∃ A, P.lift A = S

/-- Data only: neither safety nor approximation is built into the output type. -/
structure LearnedTree (n : ℕ) where
  partition : QuotientPartition n
  sparsifier : CapacitatedTree partition.parts

def CorrectLearnedTree {n m : ℕ} (G : Graph n m) (α : ℝ) (o : LearnedTree n) : Prop :=
  o.partition.Safe G ∧ Approximates (o.partition.graph G) o.sparsifier α ∧
    o.sparsifier.nodes ≤ 8 * n

end LeeCutCertificates.Certificate.Supplement


