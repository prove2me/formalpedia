-- Prove2me | Definitions.Def_RevisitXor_mm
-- name    : RevisitXor_mm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:15.459619+00:00
-- url     : https://prove2.me/theorems/fee256b9-9318-41f1-bf30-e515d639158e
-- title:
--   Maiorana–McFarland function $f_\pi(x,y)=x\cdot\pi(y)$
-- statement:
--   Let $n=2m$ and let $\pi:[2]^m\to[2]^m$ be an involution ($\pi\pi x=x$) with no fixed points ($\pi x\ne x$); equivalently, a perfect matching of the complete graph on $[2]^m$. The **Maiorana–McFarland function** of $\pi$ is
--
--   $$f_\pi:[2]^{2m}\ni(x,y)\mapsto x\cdot\pi(y)\in[2],$$
--
--   where $x\cdot z=\sum_i x_iz_i$ is the inner product modulo $2$. These are bent functions: their correlation with every parity is $\pm2^{-m}$. The counterexample of Theorem 1 is $f_\pi$ for a suitable $\pi$.
--
--   **Formalization Note** $\pi$ ranges over the published `OAI.MatchingSmoothing.Pairing`, the permutations that are involutions with no fixed point, which is exactly the paper's condition. The input $(x,y)\in[2]^{2m}$ is a pair in $[2]^m\times[2]^m$.
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), §1, p.6

import Mathlib
import Definitions.Def_RevisitXor_corr
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings

namespace RevisitXor

open OAI.MatchingSmoothing

/-- **Maiorana–McFarland function `f_π`.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission
(manuscript of August 25, 2026, sha256 3b49e10d…716), §1, p.6: "Let n := 2m and consider the
Maiorana-McFarland functions (cf [CM16]) fπ : [2]^{2m} ∋ (x, y) → x.π(y) ∈ [2] where . is inner
product modulo 2, and π : [2]^m → [2]^m is an involution (ππx = x) with no fixed points (πx ≠ x)."

**Formalization Note.** `π` is a `Pairing ([2]^m)` (the published `OAI.MatchingSmoothing.Pairing`:
a permutation that is an involution with no fixed points, exactly the paper's condition). The input
`(x, y) ∈ [2]^{2m}` is the pair `(x, y) : [2]^m × [2]^m`, and `.` is the dot product over `ZMod 2`. -/
def mm {m : ℕ} (π : Pairing (Cube m)) : Cube m × Cube m → ZMod 2 :=
  fun p => p.1 ⬝ᵥ π.1 p.2

end RevisitXor


