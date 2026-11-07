-- Prove2me | Definitions.Def_OWFLocalDesc_pSC
-- name    : OWFLocalDesc_pSC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:47:03.910302+00:00
-- url     : https://prove2.me/theorems/ac84bda5-f410-4a75-b11c-ea0b8c44907d
-- title:
--   Public-randomness sample-compression quantile $\mathrm{pSC}^t_\theta$ (Definition 2.5)
-- statement:
--   For $0<\theta\le1$, the **public-randomness sample-compression quantile** of a dataset $(x,y)$ at clock $t$ is
--   $$\mathrm{pSC}^t_\theta(x,y)=\min\Big\{s\in\mathbb Z_{\ge0} : \Pr_{w}\big[g^t_w(x,y)\le s\big]\ge\theta\Big\},$$
--   where $w$ is uniform on $\{0,1\}^t$ and the minimum of the empty set is $\infty$. It is the smallest $s$ such that, on at least a $\theta$ fraction of public tapes, some valid certificate has price at most $s$; the certificate may depend on the tape.
--
--   **Formalization Note** The value is in `ℕ∞` and equals $\infty$ (not $0$) when no $s$ qualifies, for instance on a dataset whose repeated point carries two labels. The helper `tapeProb` is $\Pr_w[g^t_w(x,y)\le s]$, a counting fraction over $\{0,1\}^t$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.5, p.13

import Mathlib
import Definitions.Def_OWFLocalDesc_gmin
set_option autoImplicit false

namespace OWFLocalDesc

/-- The fraction `Pr_w[g^t_w(x,y) ≤ s]` of public tapes `w ∈ {0,1}^t` on which some valid
certificate has charged length at most `s`. -/
noncomputable def tapeProb (U : Decoder) (t : ℕ) {m n : ℕ} (x : Fin m → Fin n → Bool)
    (y : Fin m → Bool) (s : ℕ) : ℝ :=
  open Classical in
  ((Finset.univ.filter fun w : Fin t → Bool => gmin U t x y (List.ofFn w) ≤ (s : ℕ∞)).card : ℝ) /
    (2 : ℝ) ^ t

/-- **Public-randomness sample-compression quantile `pSC^t_θ` (Definition 2.5).**
Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Definition 2.5, p.13: "For 0 < θ ≤ 1, the public-randomness
sample-compression quantile is pSC^t_θ(x,y) = min { s ∈ Z≥0 : Pr_w[g^t_w(x,y) ≤ s] ≥ θ }, where w
is uniform on {0,1}^t and the minimum of an empty set is ∞."

**Formalization Note.** The value is in `ℕ∞` (`⊤ = ∞` when no `s` qualifies); the clock `t`
is both the tape length and the step bound. Statements use it only for `0 < θ ≤ 1`. -/
noncomputable def pSC (U : Decoder) (t : ℕ) (θ : ℝ) {m n : ℕ} (x : Fin m → Fin n → Bool)
    (y : Fin m → Bool) : ℕ∞ :=
  ⨅ (s : ℕ) (_ : θ ≤ tapeProb U t x y s), (s : ℕ∞)

end OWFLocalDesc


