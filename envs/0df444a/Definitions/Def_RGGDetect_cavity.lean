-- Prove2me | Definitions.Def_RGGDetect_cavity
-- name    : RGGDetect_cavity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:38:49.250201+00:00
-- url     : https://prove2.me/theorems/5d9de0d3-3588-44bc-a301-130a6d8e92fd
-- title:
--   Cavity objects: $\Lambda_{u,I}$, $r_{u,I,D}$, $T_I$, $\phi_\nu$, $\eta_{D,S}$, $\nu(D)$ and $g(D)$
-- statement:
--   Fix a marked vertex $u$, a set $I$ of vertices, and a function $D$ of the configuration; $Q_I=\mathrm{Bern}(p)^{\otimes I}$, $L=\log(1/p)$.
--
--   1. (31) $\Lambda_{u,I}(y)=\mathbb P(Y_I=y\mid G_{-u})/Q_I(y)$ and $r_{u,I,D}(y)=\mathbb E(D\,\mathbf 1\{Y_I=y\}\mid G_{-u})/Q_I(y)$.
--   2. For a set $W\subseteq\{0,1\}^I$ (possibly depending on $G_{-u}$), the quantity $\mathbb E\big[\int_W r_{u,I,D}^2/\Lambda_{u,I}\,dQ_I\big]$, the integrand being $0$ where $\Lambda_{u,I}=0$.
--   3. (34) $T_I=\{y_I:\sum_{i\in I}y_i\le\min\{|I|,\lceil2|I|p+100\log n\rceil\}\}$.
--   4. (40) $\phi_\nu(s)=0$ for $s=0$, $s\log^\nu(e/s)$ for $0<s<1$, $1$ for $s\ge1$.
--   5. (45) $\eta_{D,S}(x_{V\setminus u},x_S)=\mathbb E_{x_u}\big[D(x_u,x_{V\setminus u})\prod_{j\in S}\kappa(\langle x_u,x_j\rangle)\big]$.
--   6. (24) $\nu(D)=1$ if $D=c\langle x_u,x_v\rangle$ for some $c\ne0$, and $\nu(D)=2t(D)=\|\boldsymbol\ell\|_1$ otherwise.
--   7. (25) $g(D)=\mathbb E(D^2)\,p\,L^{\nu(D)}$, the target scale for $\mathrm{Post}(D)$.
--
--   **Formalization Note** The multidegree $(V,\boldsymbol\ell)$ of $D$ is passed as data (it is determined by a nonzero $D$). $\phi_\nu$ is sent to $0$ on negative arguments, which never occur. The conditioning on $G_{-u}$ is a finite sum over its values.
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), §3, eqs. (24)–(25), p.10 (PDF p.12); (31), (34), p.13 (PDF p.15); (40), p.14 (PDF p.16); (45), p.16 (PDF p.18)

import Mathlib
import Definitions.Def_RGGDetect_postMoment
import Definitions.Def_RGGDetect_kappa

open MeasureTheory
open scoped Classical

namespace RGGDetect

/-- `Λ_{u,I}(y) := P(Y_I = y | G_{-u})/Q_I(y)` (31), evaluated on the event `G_{-u} = g`
(arXiv:2610.08517, held version, §3.2, p.13), with `Q_I = Bern(p)^{⊗I}` and `p = capProb d τ`. -/
noncomputable def lamUI (n d : ℕ) (τ : ℝ) (u : Fin n) (I : Finset (Fin n))
    (g : SimpleGraph (Fin n)) (y : I → Bool) : ℝ :=
  (prior n d).real {x | graphMinus τ u x = g ∧ rowY τ u I x = y} /
    ((prior n d).real {x | graphMinus τ u x = g} * bernProd (capProb d τ) y)

/-- `r_{u,I,D}(y) := E(D(x_V) 1{Y_I = y} | G_{-u})/Q_I(y)` (31), evaluated on the event `G_{-u} = g`
(arXiv:2610.08517, held version, §3.2, p.13). -/
noncomputable def rUID (n d : ℕ) (τ : ℝ) (u : Fin n) (I : Finset (Fin n)) (D : Config n d → ℝ)
    (g : SimpleGraph (Fin n)) (y : I → Bool) : ℝ :=
  (∫ x in {x | graphMinus τ u x = g ∧ rowY τ u I x = y}, D x ∂(prior n d)) /
    ((prior n d).real {x | graphMinus τ u x = g} * bernProd (capProb d τ) y)

/-- `E[∫_{W} r²_{u,I,D}/Λ_{u,I} dQ_I]`: the average over `G_{-u}` of the integral of `r²/Λ` against
`Q_I` over the set `W(G_{-u}) ⊆ {0,1}^I` (which may depend on `G_{-u}`), the integrand being `0`
where `Λ_{u,I} = 0` (arXiv:2610.08517, held version, (33), (35), (41), (46), pp.13–16). -/
noncomputable def cavInt (n d : ℕ) (τ : ℝ) (u : Fin n) (I : Finset (Fin n)) (D : Config n d → ℝ)
    (W : SimpleGraph (Fin n) → (I → Bool) → Prop) : ℝ :=
  ∑ g : SimpleGraph (Fin n), (prior n d).real {x | graphMinus τ u x = g} *
    ∑ y : I → Bool, if W g y then
      rUID n d τ u I D g y ^ 2 / lamUI n d τ u I g y * bernProd (capProb d τ) y else 0

/-- The local truncation (34), `T_I = {y_I : ∑_{i∈I} y_i ≤ min{|I|, ⌈2|I|p + 100 log n⌉}}`
(arXiv:2610.08517, held version, §3.3, p.13, eq. (34)). -/
def TI (n : ℕ) (p : ℝ) (I : Finset (Fin n)) : Set (I → Bool) :=
  {y | (Finset.univ.filter fun i => y i = true).card ≤
    min I.card ⌈2 * (I.card : ℝ) * p + 100 * Real.log n⌉₊}

/-- `ϕ_ν(s)` (40): `0` for `s = 0`, `s log^ν(e/s)` for `0 < s < 1`, `1` for `s ≥ 1`
(arXiv:2610.08517, held version, §3.4, p.14, eq. (40)).

**Formalization Note** The paper defines `ϕ_ν` on `[0, ∞)`; negative arguments (never used: `Δ ≥ 0`)
are sent to `0`. -/
noncomputable def phi (ν : ℕ) (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else if s < 1 then s * Real.log (Real.exp 1 / s) ^ ν else 1

/-- `η_{D,S}(x_{V∖u}, x_S) := E_{x_u}[D(x_u, x_{V∖u}) ∏_{j∈S} κ(⟨x_u, x_j⟩)]` (45), (102): the
marked coordinate `x_u` is averaged out (arXiv:2610.08517, held version, §3.5, p.16, eq. (45); §5,
p.26, eq. (102)). The result does not depend on `x_u`. -/
noncomputable def etaDS {ι : Type*} [DecidableEq ι] (d : ℕ) (τ : ℝ) (D : (ι → Sph d) → ℝ) (u : ι)
    (S : Finset ι) (x : ι → Sph d) : ℝ :=
  ∫ z, D (Function.update x u z) * ∏ j ∈ S, kappa d τ (ip z (x j)) ∂(unifSphere d)

/-- `ν(D)` (24): `1` if `D = c⟨x_u, x_v⟩` for some `c ≠ 0` (and distinct `u, v`), and the total degree
`2t(D) = ‖ℓ‖₁ = ∑_{v∈V} ℓ_v` otherwise (arXiv:2610.08517, held version, §3, p.10, eq. (24)).

**Formalization Note** The multidegree `(V, ℓ)` is passed as data; for nonzero `D` it is determined
by `D` (footnote 3, p.7). -/
noncomputable def nuD {ι : Type*} {d : ℕ} (V : Finset ι) (ℓ : ι → ℕ) (D : (ι → Sph d) → ℝ) : ℕ :=
  if ∃ c : ℝ, c ≠ 0 ∧ ∃ u v : ι, u ≠ v ∧ D = fun x => c * ip (x u) (x v) then 1
  else ∑ v ∈ V, ℓ v

/-- The target scale (25), `g(D) := E(D²) p L^{ν(D)}` with `L = log(1/p)`, `p = capProb d τ`
(arXiv:2610.08517, held version, §3, p.10, eq. (25)). -/
noncomputable def gD {n d : ℕ} (τ : ℝ) (V : Finset (Fin n)) (ℓ : Fin n → ℕ) (D : Config n d → ℝ) :
    ℝ :=
  (∫ x, D x ^ 2 ∂(prior n d)) * capProb d τ * Real.log (1 / capProb d τ) ^ nuD V ℓ D

end RGGDetect


