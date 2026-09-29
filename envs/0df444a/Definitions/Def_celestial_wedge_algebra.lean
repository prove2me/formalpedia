-- Prove2me | Definitions.Def_celestial_wedge_algebra
-- name    : celestial_wedge_algebra
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T02:31:35.161633+00:00
-- url     : https://prove2.me/theorems/b247ff85-24fe-471d-b000-2fa1ce110bca
-- title:
--   Celestial $w_{1+\infty}$ wedge algebra: wedge range, bracket (7.8), Poisson realisation (7.9), soft modes (7.5)–(7.6)
-- statement:
--   Definitions for the celestial $w_{1+\infty}$ wedge algebra of Section 7.1.
--
--   - **Wedge range** (Eqs. (7.6)–(7.7)): $(p,m)\in\mathbb Q^2$ with $p+m-1\in\mathbb N$ and $p-m-1\in\mathbb N$; equivalently $p\in\{1,\tfrac32,2,\dots\}$, $1-p\le m\le p-1$, $m$ in integer steps.
--   - **$W$**: the complex vector space with basis $w^p_m$, $(p,m)$ in the wedge.
--   - **Bracket** (Eq. (7.8)): $[w^p_m,w^q_n]=\bigl(m(q-1)-n(p-1)\bigr)w^{p+q-2}_{m+n}$, read as $0$ if $(p+q-2,m+n)$ is not in the wedge, extended bilinearly.
--   - **Poisson bracket** (Eq. (7.9)) on $\mathbb C[u,v]$: $\{f,g\}=\partial_uf\,\partial_vg-\partial_vf\,\partial_ug$, and the monomials $u^{p+m-1}v^{p-m-1}$ together with the linear map $w^p_m\mapsto u^{p+m-1}v^{p-m-1}$.
--   - **Soft graviton modes** (Eqs. (7.1)–(7.3)): the label range $k\in\{2,1,0,\dots\}$, $\tfrac{k-2}{2}\le m\le\tfrac{2-k}{2}$; the coefficient of Eq. (7.5)
--   $$-\frac\kappa2\bigl[n(2-k)-m(2-l)\bigr]\frac{\bigl(\tfrac{2-k}2-m+\tfrac{2-l}2-n-1\bigr)!}{\bigl(\tfrac{2-k}2-m\bigr)!\bigl(\tfrac{2-l}2-n\bigr)!}\cdot\frac{\bigl(\tfrac{2-k}2+m+\tfrac{2-l}2+n-1\bigr)!}{\bigl(\tfrac{2-k}2+m\bigr)!\bigl(\tfrac{2-l}2+n\bigr)!};$$
--   and the rescaling (7.6) $w^p_m=\tfrac1\kappa(p-m-1)!(p+m-1)!\,H^{-2p+4}_m$.
--
--   Factorials of rational arguments are taken of the truncation to a natural number.
-- source:
--   Bin Zhu, Topics in Celestial holography: A bottom-up perspective, arXiv:2606.24285v3 [hep-th] (invited review for Physics Reports), https://arxiv.org/abs/2606.24285, Section 7.1, pp. 38–40, Eqs. (7.1)–(7.9)

import Mathlib

/-!
Celestial `w_{1+∞}` wedge algebra, following Bin Zhu, *Topics in Celestial holography:
A bottom-up perspective*, arXiv:2606.24285v3, Section 7.1, Eqs. (7.5)–(7.9).
-/

namespace CelestialWedge

open MvPolynomial

/-- Wedge range, Eqs. (7.6)–(7.7): `p ∈ {1, 3/2, 2, 5/2, …}`, `1 - p ≤ m ≤ p - 1`, and
`m` runs in integer steps from `1 - p`.  Equivalently, both `p + m - 1` and `p - m - 1`
are natural numbers. -/
def InWedge (p m : ℚ) : Prop :=
  ∃ a b : ℕ, p + m - 1 = a ∧ p - m - 1 = b

/-- The labels `(p, m)` of the wedge generators `w^p_m`. -/
def WedgeIndex : Type := {x : ℚ × ℚ // InWedge x.1 x.2}

/-- The complex vector space with basis `{w^p_m}` indexed by the wedge range. -/
abbrev WedgeSpace : Type := WedgeIndex →₀ ℂ

/-- The basis element `w^p_m`. -/
noncomputable def gen (x : WedgeIndex) : WedgeSpace := Finsupp.single x 1

/-- The structure constant `m (q - 1) - n (p - 1)` of Eq. (7.8). -/
def structConst (p m q n : ℚ) : ℚ := m * (q - 1) - n * (p - 1)

open Classical in
/-- Eq. (7.8) on basis elements:
`[w^p_m, w^q_n] = (m (q - 1) - n (p - 1)) w^{p+q-2}_{m+n}`,
where the right-hand side is read as `0` if `(p + q - 2, m + n)` lies outside the wedge. -/
noncomputable def bracketGen (x y : WedgeIndex) : WedgeSpace :=
  if h : InWedge (x.1.1 + y.1.1 - 2) (x.1.2 + y.1.2) then
    ((structConst x.1.1 x.1.2 y.1.1 y.1.2 : ℚ) : ℂ) • Finsupp.single ⟨(x.1.1 + y.1.1 - 2, x.1.2 + y.1.2), h⟩ 1
  else 0

/-- The bracket of Eq. (7.8), extended bilinearly to all of `WedgeSpace`. -/
noncomputable def bracket : WedgeSpace →ₗ[ℂ] WedgeSpace →ₗ[ℂ] WedgeSpace :=
  Finsupp.linearCombination ℂ fun x => Finsupp.linearCombination ℂ fun y => bracketGen x y

/-- The Poisson bracket of Eq. (7.9) on polynomials in the phase-space variables
`u = X 0` and `v = X 1`: `{f, g} = ∂_u f ∂_v g - ∂_v f ∂_u g`. -/
noncomputable def poisson (f g : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  pderiv 0 f * pderiv 1 g - pderiv 1 f * pderiv 0 g

/-- The monomial `u^{p+m-1} v^{p-m-1}` of Eq. (7.9).  (The exponents are natural numbers on
the wedge; outside the wedge the truncation `⌊·⌋₊` is used.) -/
noncomputable def monomialOf (p m : ℚ) : MvPolynomial (Fin 2) ℂ :=
  X 0 ^ ⌊p + m - 1⌋₊ * X 1 ^ ⌊p - m - 1⌋₊

/-- The linear map `w^p_m ↦ u^{p+m-1} v^{p-m-1}` of Eq. (7.9). -/
noncomputable def toPoly : WedgeSpace →ₗ[ℂ] MvPolynomial (Fin 2) ℂ :=
  Finsupp.linearCombination ℂ fun x => monomialOf x.1.1 x.1.2

/-- The index set of the conformally soft graviton modes `H^k_m` of Eqs. (7.1)–(7.3):
`k ∈ {2, 1, 0, -1, …}` and `(k - 2)/2 ≤ m ≤ (2 - k)/2` in integer steps.  This is exactly
the wedge condition for `p = (4 - k)/2`, cf. Eq. (7.6). -/
def InSoftRange (k m : ℚ) : Prop := InWedge ((4 - k) / 2) m

/-- The structure coefficient of Eq. (7.5):
`-(κ/2) [n (2 - k) - m (2 - l)] ((2-k)/2 - m + (2-l)/2 - n - 1)! ((2-k)/2 + m + (2-l)/2 + n - 1)!
 / ( ((2-k)/2 - m)! ((2-l)/2 - n)! ((2-k)/2 + m)! ((2-l)/2 + n)! )`.
Factorials are applied to `⌊·⌋₊` of their (rational) arguments. -/
noncomputable def softCoeff (κ : ℂ) (k l m n : ℚ) : ℂ :=
  -(κ / 2) * ((n * (2 - k) - m * (2 - l) : ℚ) : ℂ) *
    ((Nat.factorial ⌊(2 - k) / 2 - m + ((2 - l) / 2 - n) - 1⌋₊ : ℂ) /
      ((Nat.factorial ⌊(2 - k) / 2 - m⌋₊ : ℂ) * (Nat.factorial ⌊(2 - l) / 2 - n⌋₊ : ℂ))) *
    ((Nat.factorial ⌊(2 - k) / 2 + m + ((2 - l) / 2 + n) - 1⌋₊ : ℂ) /
      ((Nat.factorial ⌊(2 - k) / 2 + m⌋₊ : ℂ) * (Nat.factorial ⌊(2 - l) / 2 + n⌋₊ : ℂ)))

/-- The rescaling of Eq. (7.6):
`w^p_m = (1/κ) (p - m - 1)! (p + m - 1)! H^{-2p+4}_m`. -/
noncomputable def rescale {V : Type*} [AddCommGroup V] [Module ℂ V]
    (κ : ℂ) (H : ℚ → ℚ → V) (p m : ℚ) : V :=
  (κ⁻¹ * ((Nat.factorial ⌊p - m - 1⌋₊ : ℂ) * (Nat.factorial ⌊p + m - 1⌋₊ : ℂ))) •
    H (-2 * p + 4) m

end CelestialWedge


