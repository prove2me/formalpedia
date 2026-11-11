-- Prove2me | Definitions.Def_SparsestCutOracle_Main_SDP
-- name    : SparsestCutOracle_Main_SDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:03.842319+00:00
-- url     : https://prove2.me/theorems/ab88b873-0dc0-4075-974f-01afd18aa732
-- title:
--   Path flows, weighted sparsest-cut SDP, and oracle responses
-- statement:
--   For vertices $u,v$, let $L_{uv}=(e_u-e_v)(e_u-e_v)^\top$. A sequence $p$ has path matrix $T_p$, the sum of consecutive edge Laplacians minus its endpoint Laplacian. Empty and singleton sequences have zero path matrix. The sequence length bound is $c_Pn$, with $c_P\ge1$ chosen as in the paper. Repeated vertices and traversals are retained.
--
--   For $D_\pi=\operatorname{diag}\pi$, $J_\pi=\pi\pi^\top$, and $K_\pi=\Pi D_\pi-J_\pi$, SDP feasibility means
--
--   $$X\succeq0,\quad T_p\mathbin\bullet X\ge0,\quad J_\pi\mathbin\bullet X=0,\quad D_\pi\mathbin\bullet X=\Pi.$$
--
--   Nonnegative path multipliers have their edge-load and endpoint-demand Laplacians, with traversal multiplicity counted. A response stores these multipliers, $z$, an auxiliary matrix $F$, and an augmented graph. Algebraic validity and the bound on added capacity are separate predicates, so Lemma 4 does not silently assume the capacity conclusion it cannot establish.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 8, 16–20, SDP 2 and Equation (7)

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_FairFlow

namespace SparsestCutOracle.Main

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def dot {n : ℕ} (A B : Mat n) : ℝ := Matrix.trace (A * B)

def LePSD {n : ℕ} (A B : Mat n) : Prop := (B - A).PosSemidef

def edgeLaplacian {n : ℕ} (u v : Fin n) : Mat n :=
  fun i j => ((if i = u then 1 else 0) - (if i = v then 1 else 0)) *
    ((if j = u then 1 else 0) - (if j = v then 1 else 0))

noncomputable def laplacian {n : ℕ} (G : ClusterDecomp.WGraph (Fin n)) : Mat n :=
  (1 / 2 : ℝ) • ∑ i, ∑ j, G.w i j • edgeLaplacian i j

def D {n : ℕ} (π : Fin n → ℝ) : Mat n := Matrix.diagonal π

def J {n : ℕ} (π : Fin n → ℝ) : Mat n := fun i j => π i * π j

def K {n : ℕ} (π : Fin n → ℝ) : Mat n := totalWeight π • D π - J π

def pathEdges {n : ℕ} (p : List (Fin n)) : Mat n :=
  ((p.zip p.tail).map fun e => edgeLaplacian e.1 e.2).sum

def pathDemand {n : ℕ} (p : List (Fin n)) : Mat n :=
  match p.head?, p.getLast? with
  | some u, some v => edgeLaplacian u v
  | _, _ => 0

/-- Empty and singleton sequences have matrix zero. Repetitions are retained. -/
def pathMatrix {n : ℕ} (p : List (Fin n)) : Mat n := pathEdges p - pathDemand p

structure PathFlow (n cP : ℕ) where
  coeff : List (Fin n) →₀ ℝ
  nonneg : ∀ p, 0 ≤ coeff p
  length_le : ∀ p, coeff p ≠ 0 → p.length ≤ cP * n

noncomputable def edgeLoad {n cP : ℕ} (F : PathFlow n cP) (i j : Fin n) : ℝ :=
  if i = j then 0 else F.coeff.sum fun p x =>
    x * ((p.zip p.tail).countP (fun e =>
      (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i)) : ℝ)

noncomputable def endpointLoad {n cP : ℕ} (F : PathFlow n cP) (i j : Fin n) : ℝ :=
  if i = j then 0 else F.coeff.sum fun p x =>
    if (p.head? = some i ∧ p.getLast? = some j) ∨
      (p.head? = some j ∧ p.getLast? = some i) then x else 0

noncomputable def edgeLoadMatrix {n cP : ℕ} (F : PathFlow n cP) : Mat n :=
  F.coeff.sum fun p x => x • pathEdges p

noncomputable def demandMatrix {n cP : ℕ} (F : PathFlow n cP) : Mat n :=
  F.coeff.sum fun p x => x • pathDemand p

noncomputable def pathSum {n cP : ℕ} (F : PathFlow n cP) : Mat n :=
  F.coeff.sum fun p x => x • pathMatrix p

def PathFeasible {n cP : ℕ} (G : ClusterDecomp.WGraph (Fin n)) (F : PathFlow n cP) : Prop :=
  ∀ i j, edgeLoad F i j ≤ G.w i j

def BoundedEndpoints {n cP : ℕ} (π : Fin n → ℝ) (d : ℝ) (F : PathFlow n cP) : Prop :=
  ∀ i, (∑ j, endpointLoad F i j) ≤ d * π i

def SDPFeasible {n : ℕ} (cP : ℕ) (π : Fin n → ℝ) (X : Mat n) : Prop :=
  X.PosSemidef ∧ dot (J π) X = 0 ∧ dot (D π) X = totalWeight π ∧
  ∀ p : List (Fin n), p.length ≤ cP * n → 0 ≤ dot (pathMatrix p) X

noncomputable def sparsity {n : ℕ} (G : ClusterDecomp.WGraph (Fin n))
    (π : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  cut G S Sᶜ / min (mass π S) (mass π Sᶜ)

/-- Used only with n≥2 and π>0: the infimum is over a nonempty finite family of real values. -/
noncomputable def sparsest {n : ℕ} (G : ClusterDecomp.WGraph (Fin n)) (π : Fin n → ℝ) : ℝ :=
  sInf {x : ℝ | ∃ S : Finset (Fin n), S.Nonempty ∧ S ≠ Finset.univ ∧ x = sparsity G π S}

structure Response (n cP : ℕ) where
  paths : PathFlow n cP
  z : ℝ
  F : Mat n
  augmented : ClusterDecomp.WGraph (Fin n)

noncomputable def feedback {n cP : ℕ} (π : Fin n → ℝ) (α : ℝ) (r : Response n cP) : Mat n :=
  r.F - (α / totalWeight π) • D π + r.z • J π - pathSum r.paths

/-- All algebraic response conditions; the extra-capacity bound is deliberately separate. -/
def AlgebraicResponse {n cP : ℕ} (G : ClusterDecomp.WGraph (Fin n))
    (π : Fin n → ℝ) (X : Mat n) (α : ℝ) (r : Response n cP) : Prop :=
  0 ≤ r.z ∧ r.F.IsSymm ∧
  (∀ i j, G.w i j ≤ r.augmented.w i j) ∧
  LePSD (laplacian G) (laplacian r.augmented) ∧ LePSD r.F (laplacian r.augmented) ∧
  dot (pathSum r.paths - r.F) X - r.z * dot (J π) X ≤ -α

noncomputable def extraCapacity {n : ℕ} (G H : ClusterDecomp.WGraph (Fin n)) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, if i = j then 0 else H.w i j - G.w i j

def ValidResponse {n cP : ℕ} (G : ClusterDecomp.WGraph (Fin n))
    (π : Fin n → ℝ) (X : Mat n) (α β Cadd : ℝ) (r : Response n cP) : Prop :=
  AlgebraicResponse G π X α r ∧ extraCapacity G r.augmented ≤ Cadd * α * β

/-- The paper's explicit response computed from the path flow, not an unrelated existential matrix. -/
noncomputable def flowResponse {n cP : ℕ}
    (H : ClusterDecomp.WGraph (Fin n)) (F : PathFlow n cP) : Response n cP :=
  ⟨F, 0, edgeLoadMatrix F, H⟩

end SparsestCutOracle.Main


