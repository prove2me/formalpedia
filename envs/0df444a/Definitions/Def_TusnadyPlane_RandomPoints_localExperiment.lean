-- Prove2me | Definitions.Def_TusnadyPlane_RandomPoints_localExperiment
-- name    : TusnadyPlane_RandomPoints_localExperiment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:47.896875+00:00
-- url     : https://prove2.me/theorems/c55ba757-2e50-4040-92db-c0f37f4a2957
-- title:
--   Fixed local data and independent uniform refinement
-- statement:
--   Fix the colors and heights of $n$ points and their categories relative to a horizontal interval: left, inside, or right. The old weight of a point is respectively $1,1/2,0$. For an inside point choose a child index $r_i\in\{0,\ldots,b-1\}$ independently and uniformly. Its weight in child $k$ is $1$ for $r_i<k$, $1/2$ for $r_i=k$, and $0$ for $r_i>k$; outside points retain weight $1$ or $0$ in every child.
--   $$a(y)=\sum_i\chi_i w_i\mathbf1\{V_i\le y\},\qquad a_k(y)=\sum_i\chi_i w_{ik}\mathbf1\{V_i\le y\}.$$
--   For $J=[\ell,u)$, the count $m_R$ includes precisely inside-category points with heights in $[\ell+(u-\ell)/b,u-(u-\ell)/b)$. All points, including those outside $J$, occur in the functions. Heights may be arbitrary real numbers, including block endpoints; the local theorem separately assumes distinctness. Expectation is the exact finite average
--   $$b^{-n}\sum_{r\in\{0,\ldots,b-1\}^n}\sum_k\operatorname{osc}_J a_k.$$
--   Unused child indices for outside points integrate out. Horizontal interval lengths disappear because endpoint weights depend only on categories and child order.
-- source:
--   Zhewei Wei, Tight Bounds for Tusnády’s Problem in the Plane, STOC 2027 submission #313 (October 2026), printed p. 4–6 (PDF p. 5–7), §§2.1–2.3, (2), local experiment

import Mathlib
import Definitions.Def_TusnadyPlane_RandomPoints_oscillation
import Definitions.Def_TusnadyPlane_RandomPoints_sample

noncomputable section

namespace TusnadyPlane.RandomPoints

/-- Category 0: left, 1: inside, 2: right. Heights and colors are fixed. §2.3. -/
structure LocalData (n : ℕ) where
  height : Fin n → ℝ
  category : Fin n → Fin 3
  color : Coloring n

def oldWeight (c : Fin 3) : ℝ := if c.val = 0 then 1 else if c.val = 1 then 1/2 else 0

def childWeight (c : Fin 3) (r k : ℕ) : ℝ :=
  if c.val = 0 then 1 else if c.val = 2 then 0
  else if r < k then 1 else if r = k then 1/2 else 0

def oldFunction {n : ℕ} (d : LocalData n) (y : ℝ) : ℝ :=
  ∑ i : Fin n, if d.height i ≤ y then sign (d.color i) * oldWeight (d.category i) else 0

def childFunction {n b : ℕ} (d : LocalData n) (r : Fin n → Fin b) (k : Fin b) (y : ℝ) : ℝ :=
  ∑ i : Fin n, if d.height i ≤ y then
    sign (d.color i) * childWeight (d.category i) (r i).val k.val else 0

/-- All points remain in the endpoint functions, including those outside J. -/
def localInnerCount {n : ℕ} (d : LocalData n) (lo hi : ℝ) (b : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => (d.category i).val = 1 ∧
    d.height i ∈ Set.Ico (lo + (hi-lo)/b) (hi - (hi-lo)/b))).card

/-- Independent uniform child indices; unused outside-point indices integrate out. -/
def localExpectedOscillation {n : ℕ} (d : LocalData n) (lo hi : ℝ) (b : ℕ) : ℝ :=
  ((b : ℝ) ^ n)⁻¹ * ∑ r : Fin n → Fin b,
    ∑ k : Fin b, oscillation (Set.Ico lo hi) (childFunction d r k)

end TusnadyPlane.RandomPoints


