-- Prove2me | Definitions.Def_RGGDetect_Zsup
-- name    : RGGDetect_Zsup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:59.222352+00:00
-- url     : https://prove2.me/theorems/fb0c5ee0-cc00-4945-b1bd-178c292bb97e
-- title:
--   The bounded-degree class $\mathcal H_{\le 2M}$, the ratio $X(D)$, the supremum $Z$, and the scales $g_t$
-- statement:
--   1. (78) $\mathcal H_{\le2M}$ is the set of nonzero $D\in\mathcal H_{\boldsymbol\ell}$, over all $V\subseteq[n]$ and positive multidegrees $\boldsymbol\ell$ on $V$ with $\|\boldsymbol\ell\|_1=2t$, $1\le t\le2M$; $t(D)=\|\boldsymbol\ell\|_1/2$.
--   2. (79) $X(D)=\dfrac{\mathrm{Post}(D)}{g(D)\,(np)^{(t(D)-M)_+}}$.
--   3. (80) $Z=\sup_{D\in\mathcal H_{\le2M}}X(D)$; by (81), $Z\le1/p<\infty$.
--   4. (21) $\nu_1=1$, $\nu_t=2t$ for $t\ge2$, and $g_t=pL^{\nu_t}/d^t$, $L=\log(1/p)$.
--
--   $Z$ is the quantity of the self-bounding argument: Proposition 2 shows $Z\le C(1+\Delta/p)$.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$ over the class, indexed by $(V,\boldsymbol\ell,D)$ (the multidegree is determined by a nonzero $D$). $(t-M)_+$ is natural-number subtraction.
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), §4, eqs. (78)–(81), p.22 (PDF p.24); (21), p.8 (PDF p.10)

import Mathlib
import Definitions.Def_RGGDetect_cavity
import Definitions.Def_RGGDetect_harmPoly

open MeasureTheory

namespace RGGDetect

/-- Membership in the bounded-degree class `H_{≤2M}` (78): `D` is a nonzero element of `H_ℓ` for some
`V ⊆ [n]` and positive multidegree `ℓ : V → ℕ` with `‖ℓ‖₁ = 2t`, `1 ≤ t ≤ 2M`
(arXiv:2610.08517, held version, §4, p.22, eq. (78)). -/
def InClass {n d : ℕ} (M : ℕ) (V : Finset (Fin n)) (ℓ : Fin n → ℕ) (D : Config n d → ℝ) : Prop :=
  (∀ v ∈ V, 1 ≤ ℓ v) ∧ (∃ t : ℕ, 1 ≤ t ∧ t ≤ 2 * M ∧ ∑ v ∈ V, ℓ v = 2 * t) ∧
    D ∈ tensorHarm V ℓ ∧ D ≠ 0

/-- `t(D) = ‖ℓ‖₁/2`, half the total degree (arXiv:2610.08517, held version, §3, p.9). -/
def tD {ι : Type*} (V : Finset ι) (ℓ : ι → ℕ) : ℕ := (∑ v ∈ V, ℓ v) / 2

/-- `X(D) := Post(D)/(g(D)(np)^{(t(D)-M)_+})` (79), `p = capProb d τ`
(arXiv:2610.08517, held version, §4, p.22, eq. (79)). -/
noncomputable def Xratio {n d : ℕ} (τ : ℝ) (M : ℕ) (V : Finset (Fin n)) (ℓ : Fin n → ℕ)
    (D : Config n d → ℝ) : ℝ :=
  Post τ D / (gD τ V ℓ D * ((n : ℝ) * capProb d τ) ^ (tD V ℓ - M))

/-- `Z := sup_{D ∈ H_{≤2M}} X(D)` (80) (arXiv:2610.08517, held version, §4, p.22, eq. (80)).

**Formalization Note** The supremum is taken in `[0, ∞]` over the class (78), with `X(D) ≥ 0`;
by (81) it is at most `1/p`, so it is the paper's real supremum. The multidegree `(V, ℓ)` is part of the
index (it is determined by a nonzero `D`, footnote 3). `(t - M)_+` is natural-number subtraction. -/
noncomputable def Zsup (n d : ℕ) (τ : ℝ) (M : ℕ) : ENNReal :=
  ⨆ (V : Finset (Fin n)) (ℓ : Fin n → ℕ) (D : Config n d → ℝ) (_ : InClass M V ℓ D),
    ENNReal.ofReal (Xratio τ M V ℓ D)

/-- `ν₁ = 1`, `ν_t = 2t` for `t ≥ 2` (21) (arXiv:2610.08517, held version, §2.4, p.8, eq. (21)). -/
def nuT (t : ℕ) : ℕ := if t = 1 then 1 else 2 * t

/-- `g_t = p L^{ν_t}/d^t` (21), `L = log(1/p)`, `p = capProb d τ` (arXiv:2610.08517, held version,
§2.4, p.8, eq. (21)). -/
noncomputable def gT (d : ℕ) (τ : ℝ) (t : ℕ) : ℝ :=
  capProb d τ * Real.log (1 / capProb d τ) ^ nuT t / (d : ℝ) ^ t

end RGGDetect


