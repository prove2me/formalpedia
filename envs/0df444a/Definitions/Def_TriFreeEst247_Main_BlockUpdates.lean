-- Prove2me | Definitions.Def_TriFreeEst247_Main_BlockUpdates
-- name    : TriFreeEst247_Main_BlockUpdates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:24.166298+00:00
-- url     : https://prove2.me/theorems/e3d9b812-326d-4a58-83e6-484c67982ac0
-- title:
--   Color blocks and the sampled retained-edge process
-- statement:
--   A coloring $c:V\to[L]$ is balanced when every two class sizes differ by at most one. Let $B_c$ be the input edges whose endpoint colors agree, and let $G_c=(V,E(G)\setminus B_c)$. Partition its edges into $E_i$ by the endpoint-color sum modulo $L$.
--
--   Given a retained set $H$, a shared sample $u_1,\ldots,u_t$ from $V$, and $e=xy$, define
--
--   $$\widehat d(e)=\frac1t\sum_q1[xu_q\in H]1[yu_q\in H],\qquad d(e)=\frac1n|\{z:xz,yz\in H\}|.$$
--
--   A block update replaces its decisions by retaining exactly the edges with $\lambda\widehat d(e)\le1$:
--
--   $$H'=(H\setminus E_i)\cup\{e\in E_i:\lambda\widehat d(e)\le1\}.$$
--
--   Starting from $D_0=D^*\cup B_c$ and $H_0=E(G)\setminus D_0$, process blocks in order, each with a fresh shared sample of length $t_0$. The final deletion set is $D_L=E(G)\setminus H_L$. The expected one-stage increase averages over every function $[t_0]\to V$, which is independent uniform sampling with replacement.
--
--   These definitions give the process used by Lemmas 3.8 and 3.9. Balance and optimality of $D^*$ are hypotheses of their appropriate statements, not fields assuming their conclusions.
--
--   **Formalization Note** Stages and blocks are zero-based. After the last block the total recursive helper leaves the state unchanged. Empty-sample averages have their total value zero; all sampled-update theorems use $n\ge3$ and strictly positive $t_0$.
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.12–13, Definitions 3.4, 3.6 and 3.7

import Mathlib
import Definitions.Def_TriFreeEst247_Main_LabelConstruction

noncomputable section

namespace TriFreeEst247.Main

/-- Definition 3.4, p.12: no balance condition on a generic coloring. -/
def balanced {n L : ℕ} (c : Fin n → Fin L) : Prop :=
  ∀ a b, (Finset.univ.filter (fun x => c x = a)).card ≤
    (Finset.univ.filter (fun x => c x = b)).card + 1


def monochromatic {n L : ℕ} (G : Graph n) (c : Fin n → Fin L) : EdgeSet n := by
  classical
  exact (edges G).filter (fun e => ∃ x y, e = s(x,y) ∧ c x = c y)

def coloredEdges {n L : ℕ} (G : Graph n) (c : Fin n → Fin L) : EdgeSet n :=
  edges G \ monochromatic G c

def edgeBlock {n L : ℕ} (G : Graph n) (c : Fin n → Fin L) (i : Fin L) : EdgeSet n := by
  classical
  exact (coloredEdges G c).filter (fun e => ∃ x y, e = s(x,y) ∧ blockIndex (c x) (c y) = i)

/-- Definition 3.7, p.13: a shared sample, with replacement. -/
def sampledDensity {n t : ℕ} (H : EdgeSet n) (u : Fin t → Fin n) (x y : Fin n) : ℝ := by
  classical
  exact (∑ q, if s(x,u q) ∈ H ∧ s(y,u q) ∈ H then (1 : ℝ) else 0) / (t : ℝ)

def commonDensity {n : ℕ} (H : EdgeSet n) (x y : Fin n) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun z => s(x,z) ∈ H ∧ s(y,z) ∈ H)).card : ℝ) / (n : ℝ)

/-- Only current-block edges change; the comparison includes equality. -/
def update {n L t : ℕ} (G : Graph n) (lam : ℝ) (c : Fin n → Fin L)
    (i : Fin L) (H : EdgeSet n) (u : Fin t → Fin n) : EdgeSet n := by
  classical
  exact (H \ edgeBlock G c i) ∪ (edgeBlock G c i).filter
    (fun e => ∃ x y, e = s(x,y) ∧ lam * sampledDensity H u x y ≤ 1)

/-- Conditional expectation over the fresh uniform t-sample only. n≥3 and t>0
in its theorem; thus the finite sample space is nonempty. -/
def expectedIncrease {n L t : ℕ} (G : Graph n) (lam : ℝ) (c : Fin n → Fin L)
    (i : Fin L) (H : EdgeSet n) : ℝ :=
  (∑ u : Fin t → Fin n,
    score G lam (edges G \ update G lam c i H u) - score G lam (edges G \ H)) /
      (Fintype.card (Fin t → Fin n) : ℝ)

/-- Definition 3.6, pp.12--13. Stage k has completed precisely the first k blocks.
The total extension beyond L makes no further changes and is never used by the milestones. -/
def retainedAfter {n : ℕ} (G : Graph n) (lam η : ℝ)
    (c : Fin n → Fin (colorCount η)) (Dstar : EdgeSet n)
    (u : Fin (colorCount η) → Fin (sampleCount lam η) → Fin n) : ℕ → EdgeSet n
  | 0 => edges G \ (Dstar ∪ monochromatic G c)
  | k + 1 => if h : k < colorCount η then
      update G lam c ⟨k,h⟩ (retainedAfter G lam η c Dstar u k) (u ⟨k,h⟩)
    else retainedAfter G lam η c Dstar u k

def finalDeletion {n : ℕ} (G : Graph n) (lam η : ℝ)
    (c : Fin n → Fin (colorCount η)) (Dstar : EdgeSet n)
    (u : Fin (colorCount η) → Fin (sampleCount lam η) → Fin n) : EdgeSet n :=
  edges G \ retainedAfter G lam η c Dstar u (colorCount η)

end TriFreeEst247.Main


