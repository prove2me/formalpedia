-- Prove2me | Definitions.Def_SeqExpDiffusion_IsHatC2
-- name    : SeqExpDiffusion_IsHatC2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:43.139567+00:00
-- url     : https://prove2.me/theorems/d4249043-f79b-4717-89a6-e5693fa49e67
-- title:
--   The class $\widehat{\mathcal C}^2$
-- statement:
--   The class
--
--   $$\widehat{\mathcal C}^2:=\big\{f\in\mathcal C^1[0,1]:\ \text{there exists a finite set }N_f\subseteq[0,1]\text{ such that }f''(\delta)\text{ exists }\forall\delta\in[0,1]\setminus N_f\big\}$$
--
--   of once continuously differentiable functions on $[0,1]$ with a second derivative off a finite set. The verification theorem applies to solutions of the QVI in this class, and Theorem 2 shows the candidate value $\tilde V$ lies in it.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, display (13), p.17

import Mathlib
import Definitions.Def_SeqExpDiffusion_IsHatC2With

namespace SeqExpDiffusion

/-- The class `Ĉ² := {f ∈ C¹[0, 1] : there is a finite set N_f ⊆ [0, 1] such that f″(δ) exists
for all δ ∈ [0, 1] \ N_f}`, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, display (13), p.17. -/
def IsHatC2 (f : ℝ → ℝ) : Prop := ∃ N : Set ℝ, IsHatC2With f N

end SeqExpDiffusion


