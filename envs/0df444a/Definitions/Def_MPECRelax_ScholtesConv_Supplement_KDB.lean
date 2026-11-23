-- Prove2me | Definitions.Def_MPECRelax_ScholtesConv_Supplement_KDB
-- name    : MPECRelax_ScholtesConv_Supplement_KDB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:29:22.36941+00:00
-- url     : https://prove2.me/theorems/67287d57-2a85-4d9e-824b-36a07cae710b
-- title:
--   §3.3, p. 14 — the Kadrani et al. relaxation R^KDB(t) and the index set I^00_Φ(x, t) of (10)
-- statement:
--   For the MPEC (1) and a parameter $t>0$, the relaxed program of Kadrani, Dussault and Benchakroun is
--   $$R^{KDB}(t):\quad \min f(x)\ \ \text{s.t.}\ \ g_i(x)\le0,\ h_j(x)=0,\ G_i(x)\ge-t,\ H_i(x)\ge-t,\ (G_i(x)-t)(H_i(x)-t)\le0,$$
--   with $i=1,\dots,m$, $j=1,\dots,p$ and $i=1,\dots,l$ for the last three families. Its feasible set is $X^{KDB}(t)$. For $x\in X^{KDB}(t)$, display (10) defines
--   $$I^{00}_\Phi(x,t)=\{i\in I_\Phi(x,t) : G_i(x)-t=H_i(x)-t=0\},\qquad I_\Phi(x,t)=\{i : (G_i(x)-t)(H_i(x)-t)=0\}.$$
--
--   This is the program of Theorems 3.7 and 3.8.
--
--   **Formalization Note** $R^{KDB}(t)$ is an NLP with inequality constraints $g_i\le0$, $-G_i-t\le0$, $-H_i-t\le0$, $(G_i-t)(H_i-t)\le0$ (in this order) and equality constraints $h_j=0$. $I^{00}_\Phi(x,t)$ is written as $\{i : G_i(x)-t=0,\ H_i(x)-t=0\}$; membership in $I_\Phi(x,t)$ follows from the two equalities.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 14, R^KDB(t) and display (10)

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC

namespace MPECRelax.ScholtesConv.Supplement

variable {n m p l : ℕ}

/-- The relaxed program R^KDB(t) of Kadrani, Dussault and Benchakroun (p. 14) as an NLP.
Inequality constraints, in this order: `g_i ≤ 0` (index `inl i`), `−G_i − t ≤ 0`
(`inr (inl i)`, i.e. `G_i ≥ −t`), `−H_i − t ≤ 0` (`inr (inr (inl i))`, i.e. `H_i ≥ −t`),
`(G_i − t)(H_i − t) ≤ 0` (`inr (inr (inr i))`); equality constraints `h_j = 0`.
Its feasible set `X^KDB(t)` is `{x | (RKDB P t).Feasible x}`. -/
def RKDB (P : MPEC n m p l) (t : ℝ) : NLP n (Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l) (Fin p) where
  f := P.f
  g := Sum.elim P.g (Sum.elim (fun i x => -P.G i x - t)
         (Sum.elim (fun i x => -P.H i x - t) (fun i x => (P.G i x - t) * (P.H i x - t))))
  h := P.h

/-- (10), p. 14: `I^{00}_Φ(x, t) = {i ∈ I_Φ(x, t) | G_i(x) − t = H_i(x) − t = 0}`, where
`I_Φ(x, t) = {i | (G_i(x) − t)(H_i(x) − t) = 0}`; membership in `I_Φ(x, t)` is implied by the
two equalities. -/
def I00Phi (P : MPEC n m p l) (x : E n) (t : ℝ) : Set (Fin l) :=
  {i | P.G i x - t = 0 ∧ P.H i x - t = 0}

end MPECRelax.ScholtesConv.Supplement


