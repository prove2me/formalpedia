-- Prove2me | Definitions.Def_GibbsTransition_SizeCopies_Interval
-- name    : GibbsTransition_SizeCopies_Interval
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T21:50:57.437771+00:00
-- url     : https://prove2.me/theorems/b1696fe2-f499-4129-82a4-68bdd6c4aa8e
-- title:
--   Exact overlapping interval search
-- statement:
--   For a sequence of comparison bits $Z_k$, start at $I_0=[1/4,3/4]$. Write $I_k=[\ell_k,r_k]$, $\phi_k=(\ell_k+r_k)/2$ and $\gamma_k=(r_k-\ell_k)/8$. The update is
--
--   $$I_{k+1}=\begin{cases}[\ell_k,\phi_k+\gamma_k],&Z_k=1,\\[\phi_k-\gamma_k,r_k],&Z_k=0.\end{cases}$$
--
--   Stop after $K=\lceil\log(1/(4\varepsilon))/\log(8/5)\rceil$ rounds and output the midpoint of $I_K$. All interval arithmetic is rational. The search itself is deterministic given the comparison sequence; this file does not define a quantum learner, an effective sample schedule, or a classical running time.
--
--   These updates are the common geometric component of the source's upper learners.
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), §3.1, Equation (16), printed p. 6 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib

namespace GibbsTransition.SizeCopies

/-- The overlapping interval update of (16), on exact rational coordinates. -/
def searchInterval (z : ℕ → Bool) : ℕ → ℚ × ℚ
  | 0 => (1/4, 3/4)
  | k+1 =>
    let I := searchInterval z k
    let phi := (I.1 + I.2) / 2
    let gamma := (I.2 - I.1) / 8
    if z k then (I.1, phi + gamma) else (phi - gamma, I.2)

def searchField (z : ℕ → Bool) (k : ℕ) : ℚ :=
  ((searchInterval z k).1 + (searchInterval z k).2) / 2

def searchMargin (z : ℕ → Bool) (k : ℕ) : ℚ :=
  ((searchInterval z k).2 - (searchInterval z k).1) / 8

noncomputable def searchRounds (epsilon : ℚ) : ℕ :=
  ⌈Real.log (1 / (4 * (epsilon : ℝ))) / Real.log (8 / 5)⌉₊

def searchOutput (z : ℕ → Bool) (K : ℕ) : ℚ := searchField z K

end GibbsTransition.SizeCopies


