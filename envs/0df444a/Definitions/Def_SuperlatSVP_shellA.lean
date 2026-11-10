-- Prove2me | Definitions.Def_SuperlatSVP_shellA
-- name    : SuperlatSVP_shellA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:06.960308+00:00
-- url     : https://prove2.me/theorems/ff5b7d0f-3c67-4935-8880-68fe842b1beb
-- title:
--   The shells $H$, $A$, $E_z$, the filter caps $H_s(u)$, the slack $q$ and the mean shell count $m_\Lambda$
-- statement:
--   Fix the dimension $n$ and a length estimate $\lambda>0$. Section 4 uses:
--
--   1. the **target shell** $H=\{x:|\|x\|-\lambda|\le\lambda n^{-1/3}\}$, that is, $1-n^{-1/3}\le\|x\|/\lambda\le1+n^{-1/3}$ ((4.1), (4.11));
--   2. the **midpoint shell** $A=\{w:\sqrt3\lambda/2-\lambda n^{-2}\le\|w\|\le\sqrt3\lambda/2+\lambda n^{-2}\}$ (4.6);
--   3. for a difference $z$, the **pair set** $E_z=\{x: x\in H,\ x-z\in H,\ x-z/2\in A\}$ (4.17), the points $x$ for which the pair $(x,x-z)$ lies in $H$ and has its midpoint in $A$;
--   4. for a unit vector $s$ and $u>0$, the **filter cap** $H_s(u)=\{x\in H:\langle s,x\rangle\ge\sqrt u\,\|x\|\}$ (§4.3);
--   5. the **slack** $q=2^a$ with $a=\lceil n/\log_2 n\rceil$;
--   6. for a full-rank lattice $\Lambda=B_\Lambda\mathbb Z^n$, the **mean shell count** $m_\Lambda=\operatorname{vol}(A)/\det\Lambda$ (4.8).
--
--   All of them are centered at the origin and depend on $n$ and $\lambda$.
--
--   **Formalization Note** Volumes are Lebesgue measure on $\mathbb R^n$ with values in $[0,\infty]$, and $\det\Lambda=|\det B_\Lambda|$. The slack $q$ is used only for $n\ge2$, where $\log_2 n>0$.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4, (4.1), p.29; (4.6), (4.8), p.32; (4.11), p.35; (4.17), p.37; §4.3, p.44

import Mathlib
import Definitions.Def_SuperlatSVP_lat

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace SuperlatSVP

/-- The target shell `H = {x : |‖x‖ − λ| ≤ λ n^{−1/3}}` of §4 ((4.1), p.29; (4.11), p.35), which
for `λ > 0` is `{x : 1 − n^{−1/3} ≤ ‖x‖/λ ≤ 1 + n^{−1/3}}`. -/
def shellH (n : ℕ) (lam : ℝ) : Set (E n) :=
  {x | |‖x‖ - lam| ≤ lam * (n : ℝ) ^ (-(1 / 3 : ℝ))}

/-- The midpoint shell `A = {w : √3λ/2 − λn^{−2} ≤ ‖w‖ ≤ √3λ/2 + λn^{−2}}` ((4.6), p.32). -/
def shellA (n : ℕ) (lam : ℝ) : Set (E n) :=
  {w | Real.sqrt 3 * lam / 2 - lam * ((n : ℝ) ^ 2)⁻¹ ≤ ‖w‖ ∧
       ‖w‖ ≤ Real.sqrt 3 * lam / 2 + lam * ((n : ℝ) ^ 2)⁻¹}

/-- The pair set `E_z = {x : x, x − z ∈ H, x − z/2 ∈ A}` of a difference `z` ((4.17), p.37). -/
def pairShell (n : ℕ) (lam : ℝ) (z : E n) : Set (E n) :=
  {x | x ∈ shellH n lam ∧ x - z ∈ shellH n lam ∧ x - (1 / 2 : ℝ) • z ∈ shellA n lam}

/-- The filter cap `H_s(u) = {x ∈ H : ⟨s, x⟩ ≥ √u ‖x‖}` (§4.3, p.44). -/
def capShell (n : ℕ) (lam : ℝ) (s : E n) (u : ℝ) : Set (E n) :=
  {x | x ∈ shellH n lam ∧ Real.sqrt u * ‖x‖ ≤ ⟪s, x⟫}

/-- The slack `q = 2^a`, `a = ⌈n / log₂ n⌉` (§4.1.1, p.32). Used for `n ≥ 2`. -/
noncomputable def chainQ (n : ℕ) : ℕ := 2 ^ (Nat.ceil ((n : ℝ) / Real.logb 2 n))

/-- The expected shell count `m_Λ = vol(A)/det Λ` ((4.8), p.32) for `Λ = B_Λℤⁿ`, `det Λ = |det B_Λ|`,
in `ℝ≥0∞`. -/
noncomputable def shellMass (n : ℕ) (lam : ℝ) (B : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  volume (shellA n lam) / ENNReal.ofReal |B.det|

end SuperlatSVP


