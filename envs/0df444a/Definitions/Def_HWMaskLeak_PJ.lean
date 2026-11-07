-- Prove2me | Definitions.Def_HWMaskLeak_PJ
-- name    : HWMaskLeak_PJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:06.433439+00:00
-- url     : https://prove2.me/theorems/4e740027-6d89-4883-9291-167c4e9b55e1
-- title:
--   Doubling orbit $\varphi_j=\{2^jt/N\}$ and partial products $P_J(\theta)$
-- statement:
--   For a residue $t\in\mathbb Z/N\mathbb Z$, identified with its representative in $\{0,\dots,N-1\}$, let
--   $$
--   \varphi_j:=\Bigl\{\frac{2^j t}{N}\Bigr\}\quad(j\ge0),
--   $$
--   the fractional parts along the orbit of the doubling map. For $J\subseteq\Omega=\{0,\dots,n-1\}$ and real $p,\theta$,
--   $$
--   P_J(\theta):=\prod_{j\in J}L_p(\theta+2\pi\varphi_j).
--   $$
--   The integral $I$ of Lemma 4.11 is $\int_{-\pi}^{\pi}P_\Omega(\theta)\,d\theta$; Claim C.1 bounds $P_J$ on a short interval $J$.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §4.4, p.24, and App. C.4, p.45

import Mathlib
import Definitions.Def_HWMaskLeak_Lp

namespace HWMaskLeak

/-- **The doubling orbit `φ_j = {2ʲt/N}`** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their
Weight: From Additive Sharing to Learning with Physical Rounding*, preprint (version of October 31,
2026, sha256 ab686360…), §4.4, p.24, and App. C.4, p.45): the fractional part of `2ʲ t / N`, where the
residue `t` is identified with its representative in `{0, …, N − 1}`.

**Formalization Note** `t.val` is the representative and `Int.fract` the fractional part of the real
number `2ʲ · t.val / N`. -/
noncomputable def phi (N : ℕ) (t : ZMod N) (j : ℕ) : ℝ :=
  Int.fract ((2 : ℝ) ^ j * (t.val : ℝ) / N)

/-- **The partial product `P_J(θ)`** (same preprint, §4.4, p.24, and App. C.4, p.45): for a set
`J ⊆ Ω = {0, …, n − 1}` of bit indices, `P_J(θ) := Π_{j ∈ J} L_p(θ + 2πφ_j)`. -/
noncomputable def PJ (p : ℝ) (N : ℕ) (t : ZMod N) (J : Finset ℕ) (θ : ℝ) : ℝ :=
  ∏ j ∈ J, Lp p (θ + 2 * Real.pi * phi N t j)

end HWMaskLeak


