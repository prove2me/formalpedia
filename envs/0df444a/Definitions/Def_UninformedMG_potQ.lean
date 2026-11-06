-- Prove2me | Definitions.Def_UninformedMG_potQ
-- name    : UninformedMG_potQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:07.430221+00:00
-- url     : https://prove2.me/theorems/cb0938ad-2602-4950-ae85-453153632670
-- title:
--   Proof quantities: $Y^k$, the effective kernel $T^k$, $M^k_{h,s,v}$ and the OMD potential $Q^k$
-- statement:
--   For an opponent policy $\nu$ and a value table $v$, the **true normalized remaining loss** is
--   $$Y_{h,s,v,a}=\sum_b\nu_h(b\mid s)\Big[\frac{\ell_h(s,a,b)}H+P_hv_{h+1}(s,a,b)\Big],$$
--   and the **effective kernel** is $T_h(s'\mid s,a)=\sum_b\nu_h(b\mid s)P_h(s'\mid s,a,b)$. In episode $k$ these are $Y^k$ and $T^k$, computed from $\nu^k$. For iterate policies $\pi$ and a loss vector $g$,
--   $$M_{h,s,v}=\sum_a\pi_h(a\mid s,v)e^{-\lambda g_{h,s,v,a}},\qquad Q=\sum_vw(v)\Big(\prod_{h,s}M_{h,s,v}\Big)^{1/H}.$$
--
--   These are the objects of the OMD analysis (Lemmas B.1–B.4).
--
--   **Formalization Note** The exponent $1/H$ is the real power with exponent $H^{-1}$. On a run every $M_{h,s,v}$ is positive, so this equals $\exp(H^{-1}\sum_{h,s}\log M_{h,s,v})$, the paper's other form.
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Appendix B, p.16 (PDF p.18) ($Y^k$); p.17 (PDF p.19) ($M^k$, $Q^k$); effective kernel p.8 (PDF p.10)

import Mathlib
import Definitions.Def_UninformedMG_enr
import Definitions.Def_UninformedMG_Phi

namespace UninformedMG

variable {H : ℕ}

/-- **True normalized remaining loss** (Appendix B, p.16 = PDF p.18): for an opponent policy `ν`
and a value table `v`, `Y_{h,s,v,a} = ∑_b ν_h(b|s) [ℓ_h(s,a,b)/H + P_h v_{h+1}(s,a,b)]`. In episode
`k`, `Y^k` is `Ytab G ν^k (val v)`. -/
noncomputable def Ytab (G : Game H) (ν : OPolicy G) (vt : (h : Fin (H + 1)) → G.St h → ℝ)
    (h : Fin H) (s : G.St h.castSucc) (a : G.Act h) : ℝ :=
  ∑ b, ν h s b * (G.loss h s a b / (H : ℝ) + PV G h (vt h.succ) s a b)

/-- The **effective transition kernel** of an opponent policy (p.8):
`T_h(s' | s, a) = ∑_b ν_h(b|s) P_h(s'|s,a,b)`. `T^k` is `effKernel G ν^k`. -/
noncomputable def effKernel (G : Game H) (ν : OPolicy G) : Kernel G :=
  fun h s a s' => ∑ b, ν h s b * G.trans h s a b s'

/-- `M_{h,s,v} = ∑_a π_h(a | s, v) e^{−λ g_{h,s,v,a}}` (p.17 = PDF p.19). -/
noncomputable def Mk {G : Game H} (V : CandClass G) (lam : ℝ) (π : CPolicy V)
    (g : (h : Fin H) → G.St h.castSucc → V.C → G.Act h → ℝ) (h : Fin H) (s : G.St h.castSucc)
    (v : V.C) : ℝ :=
  ∑ a, π h s v a * Real.exp (-lam * g h s v a)

/-- **OMD potential** `Q = ∑_v w(v) (∏_{h,s} M_{h,s,v})^{1/H}` (p.17 = PDF p.19).

**Formalization Note.** The exponent `1/H` is `Real.rpow` with exponent `(H : ℝ)⁻¹`; on a run
every `M_{h,s,v}` is positive, so this equals `exp(H⁻¹ ∑_{h,s} log M_{h,s,v})`, the form the paper
also uses (p.17). Named `potQ` to distinguish it from the feasible set `Q(z)` (`feasibleMix`). -/
noncomputable def potQ {G : Game H} (V : CandClass G) (lam : ℝ) (w : V.C → ℝ) (π : CPolicy V)
    (g : (h : Fin H) → G.St h.castSucc → V.C → G.Act h → ℝ) : ℝ :=
  ∑ v, w v * (∏ h : Fin H, ∏ s, Mk V lam π g h s v) ^ ((H : ℝ)⁻¹)

end UninformedMG


