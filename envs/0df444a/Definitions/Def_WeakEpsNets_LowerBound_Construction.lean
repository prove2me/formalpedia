-- Prove2me | Definitions.Def_WeakEpsNets_LowerBound_Construction
-- name    : WeakEpsNets_LowerBound_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:49.328389+00:00
-- url     : https://prove2.me/theorems/7bd0da50-dedf-4dc2-8efd-ba38b331ad23
-- title:
--   Shifted grid, indexed hyperplanes, quadratic lift, and hull families
-- statement:
--   Fix integers $s\ge1$ and even $q\ge2$, and put $\tau=1/(9q^5)$ and $D_s=(s^2+5s)/2$. Define
--   $$P_0^{+\tau}=\{(x_1,\ldots,x_s,y+\tau):x\in[q]^s,\ y\in[(s+1)q^2]\},$$
--   $$H_{a,b}=\{p:p_{s+1}=\sum_{i=1}^s a_i p_i+b+\tau\},\qquad a\in[q]^s,\ b\in[q^2],\qquad B_H=P_0^{+\tau}\cap H.$$
--   The lift keeps $x_1,\ldots,x_{s-1}$ and all products $x_i x_j$ with $1\le i\le j\le s+1$:
--   $$\phi_s(p)=(x_1,\ldots,x_{s-1},(x_ix_j)_{i\le j}),\qquad P^{+\tau}=\phi_s(P_0^{+\tau}).$$
--   Finally,
--   $$\mathcal C_H=\{\operatorname{conv}(\phi_s(S)):S\subseteq B_H,\ |S|=q^s/2\}.$$
--   These are the paper's concrete objects for the replacement and counting milestones. The labelled output coordinates have cardinality $D_s$; the input and parameter indices are zero based, with integer grid values and hyperplane coefficients obtained by adding one. Theorems only use the above nondegenerate parameter range, so $q^s/2$ is an integer.
-- source:
--   Bhore, Browne, Zheng, Strong Lower Bounds for Weak Epsilon-Nets, STOC 2027 submission #301 (October 2026), §3, pp. 9–10, lines 278–290; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/301.pdf

import Mathlib
import Definitions.Def_WeakEpsNets_LowerBound_Parameters

noncomputable section

namespace WeakEpsNets.LowerBound

/-- Quadratic coordinate labels, zero-based indices for 1 ≤ i ≤ j ≤ s+1. -/
abbrev QuadraticIndex (s : ℕ) := {ij : Fin (s + 1) × Fin (s + 1) // ij.1 ≤ ij.2}

/-- s-1 linear coordinates, followed by all quadratic coordinates; source p. 9, line 286.
For s ≥ 1 this has exactly D_s coordinates. -/
abbrev LiftIndex (s : ℕ) := Fin (s - 1) ⊕ QuadraticIndex s

abbrev LiftSpace (s : ℕ) := LiftIndex s → ℝ

/-- The exact paper lift: omit x_s and x_{s+1}, retain every quadratic monomial. -/
def phi (s : ℕ) (p : Fin (s + 1) → ℝ) : LiftSpace s
  | Sum.inl i => p ⟨i.val, by omega⟩
  | Sum.inr ij => p ij.val.1 * p ij.val.2

/-- Shifted grid P₀^{+τ}, source p. 9, line 282. -/
def shiftedGrid (s q : ℕ) : Finset (Fin (s + 1) → ℝ) := by
  classical
  exact Finset.univ.image
    (fun t : (Fin s → Fin q) × Fin ((s + 1) * q ^ 2) =>
      fun i : Fin (s + 1) =>
        if hi : i.val < s then (((t.1 ⟨i.val, hi⟩).val + 1 : ℕ) : ℝ)
        else ((t.2.val + 1 : ℕ) : ℝ) + tau q)

/-- Index every hyperplane once by its positive integer slopes and intercept. -/
abbrev HyperplaneIndex (s q : ℕ) :=
  (Fin s → Fin q) × Fin (q ^ 2)

/-- H_{a,b}: x_{s+1} = ∑ a_i x_i + b + τ; source p. 9, line 283. -/
def hyperplane (s q : ℕ) (h : HyperplaneIndex s q) : Set (Fin (s + 1) → ℝ) :=
  {p | p (Fin.last s) = (∑ i : Fin s, (((h.1 i).val + 1 : ℕ) : ℝ) * p i.castSucc) +
    ((h.2.val + 1 : ℕ) : ℝ) + tau q}

/-- B_H = P₀^{+τ} ∩ H, source p. 9, line 284. -/
def block (s q : ℕ) (h : HyperplaneIndex s q) : Finset (Fin (s + 1) → ℝ) := by
  classical
  exact (shiftedGrid s q).filter (fun p => p ∈ hyperplane s q h)

/-- P^{+τ} = φ_s(P₀^{+τ}), source p. 10, line 287. -/
def liftedGrid (s q : ℕ) : Finset (LiftSpace s) := by
  classical
  exact (shiftedGrid s q).image (phi s)

/-- Lifted B_H, the permitted universe of replacement points. -/
def liftedBlock (s q : ℕ) (h : HyperplaneIndex s q) : Finset (LiftSpace s) := by
  classical
  exact (block s q h).image (phi s)

/-- C_H consists of convex hulls of exactly q^s/2 lifted points on H;
source p. 10, lines 287–289. Statements using this require s ≥ 1 and even q ≥ 2. -/
def hullFamily (s q : ℕ) (h : HyperplaneIndex s q) : Set (Set (LiftSpace s)) := by
  classical
  exact {C | ∃ S : Finset (Fin (s + 1) → ℝ),
    S ⊆ block s q h ∧ S.card = q ^ s / 2 ∧
      C = convexHull ℝ (↑(S.image (phi s)) : Set (LiftSpace s))}

end WeakEpsNets.LowerBound


