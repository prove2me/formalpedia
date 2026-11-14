-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_AtomicProfiles
-- name    : ConsistentSubmodular_Deterministic_Certificates_AtomicProfiles
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:13.639204+00:00
-- url     : https://prove2.me/theorems/378d4f57-509b-44e5-bfd7-bacb323c658c
-- title:
--   Atomic profiles: baseline, residual, designated value, benchmark, value on the simplex; canonical profiles, safe paths, checkpoint statement
-- statement:
--   **Support.** `supportCard p` is the number of nonzero coordinates $|\{i: p_i\neq 0\}|$ of $p\in\mathbb R^{m+1}$.
--
--   **Atomic profiles.** An `AtomicProfile m N` is a finite family of atoms $a<N$ with a pool $\pi_a\in\{0,\dots,m\}$, a nonempty label set $L_a\subseteq\{0,\dots,m\}$ and a weight $c_a\ge 0$, such that $i\le\pi_a$ for every $i\in L_a$ (the triangular condition), and such that every atom with $c_a>0$ and $\pi_a=m$ contains the terminal label $m$ in $L_a$. For stages $t,i\in\{0,\dots,m\}$ and a point $p$:
--
--   - `baseline P t` $=\sum_a c_a\mathbf 1[\pi_a<t]$: the weight of atoms already closed at stage $t$.
--   - `residual P i t` $=\sum_a c_a\mathbf 1[t\le\pi_a,\ i\in L_a]$: the weight of atoms still open at stage $t$ that label $i$ covers.
--   - `designated P t` $=\mathrm{residual}(t,t)$.
--   - `benchmark P t` $=\mathrm{baseline}(t)+\mathrm{designated}(t)$.
--   - `value P t p` $=\mathrm{baseline}(t)+\sum_a\mathbf 1[t\le\pi_a]\,c_a\big(1-\prod_{i\in L_a}(1-p_i)\big)$: the value at stage $t$ of the mixture $p$, in which each label $i$ is selected independently with probability $p_i$.
--   - `Canonical P`: $\mathrm{designated}(0)=1$ and $\mathrm{residual}(i,t)\le\mathrm{designated}(t)$ for all $t,i$.
--
--   **Safe paths.** `SafePath P t ℓ γ` means that at every node of the polygonal path $\gamma$ and at every point of every piece the point lies in the simplex $\Delta$ and has $\mathrm{value}(t,\cdot)\ge\ell$. The nodes are checked explicitly, so a path with no pieces is not vacuously safe.
--
--   **Checkpoint statement.** `FiniteCheckpointGoal` asserts that for every canonical profile there exist an anchor $p\in\Delta$ with $|\mathrm{supp}\,p|\le 2$ and $\mathrm{value}(t,p)\ge\frac34\,\mathrm{benchmark}(t)$ for all $t$, an entry path from $\delta_0$ to $p$ that is safe at stage $0$ at level $3/4$, and an exit path from $p$ to $\delta_m$ that is safe at stage $m$ at level $\frac34\,\mathrm{benchmark}(m)$, with at most $(m+1)+2$ pieces in total.
--
--   Atomic profiles model the window instances by finitely many coverage atoms. The checkpoint statement is the finite form of the checkpoint reduction behind the $3/4$ certificates (Theorem 7) of Section 3 and Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/AtomicProfiles.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

def supportCard {m : ℕ} (p : Point m) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => p i ≠ 0)).card

/-- Finite atoms; positive terminal atoms contain the prescribed terminal label. -/
structure AtomicProfile (m atomCount : ℕ) where
  pool : Fin atomCount → Fin (m + 1)
  labels : Fin atomCount → Finset (Fin (m + 1))
  weight : Fin atomCount → ℝ
  weight_nonnegative : ∀ a, 0 ≤ weight a
  labels_nonempty : ∀ a, (labels a).Nonempty
  triangular : ∀ a i, i ∈ labels a → i ≤ pool a
  terminal : ∀ a,
    0 < weight a → pool a = Fin.last m → Fin.last m ∈ labels a

namespace AtomicProfile

variable {m atomCount : ℕ}

def baseline (P : AtomicProfile m atomCount) (t : Fin (m + 1)) : ℝ :=
  ∑ a, if P.pool a < t then P.weight a else 0

def residual (P : AtomicProfile m atomCount)
    (i t : Fin (m + 1)) : ℝ :=
  ∑ a, if t ≤ P.pool a ∧ i ∈ P.labels a then P.weight a else 0

def designated (P : AtomicProfile m atomCount) (t : Fin (m + 1)) : ℝ :=
  P.residual t t

def benchmark (P : AtomicProfile m atomCount) (t : Fin (m + 1)) : ℝ :=
  P.baseline t + P.designated t

def value (P : AtomicProfile m atomCount) (t : Fin (m + 1))
    (p : Point m) : ℝ :=
  P.baseline t + ∑ a,
    if t ≤ P.pool a then
      P.weight a * (1 - ∏ i ∈ P.labels a, (1 - p i))
    else 0

def Canonical (P : AtomicProfile m atomCount) : Prop :=
  P.designated 0 = 1 ∧
  ∀ (t i : Fin (m + 1)), P.residual i t ≤ P.designated t

end AtomicProfile

/-- Nodes are checked explicitly, so a zero-piece path is not vacuously safe. -/
def SafePath {m atomCount : ℕ} (P : AtomicProfile m atomCount)
    (t : Fin (m + 1)) (level : ℝ) (γ : PolygonalPath m) : Prop :=
  (∀ j, IsSimplex (γ.node j) ∧ level ≤ P.value t (γ.node j)) ∧
  ∀ (j : Fin γ.pieces) (x : ℝ), 0 ≤ x → x ≤ 1 →
    IsSimplex (mix (γ.node j.castSucc) (γ.node j.succ) x) ∧
    level ≤ P.value t (mix (γ.node j.castSucc) (γ.node j.succ) x)

/-- The finite checkpoint statement, including endpoint safety, support, and
piece budget. -/
def FiniteCheckpointGoal : Prop :=
  ∀ m atomCount : ℕ, ∀ P : AtomicProfile m atomCount,
    P.Canonical →
    ∃ (p : Point m) (entry exit : PolygonalPath m),
      IsSimplex p ∧ supportCard p ≤ 2 ∧
      (∀ t, (3 : ℝ) / 4 * P.benchmark t ≤ P.value t p) ∧
      entry.node 0 = vertex 0 ∧
      entry.node (Fin.last entry.pieces) = p ∧
      exit.node 0 = p ∧
      exit.node (Fin.last exit.pieces) = vertex (Fin.last m) ∧
      SafePath P 0 ((3 : ℝ) / 4) entry ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) exit ∧
      entry.pieces + exit.pieces ≤ (m + 1) + 2

end ConsistentSubmodular

end


