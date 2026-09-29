-- Prove2me | Definitions.Def_THDM_potential
-- name    : THDM_potential
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T23:48:23.241508+00:00
-- url     : https://prove2.me/theorems/c303b85e-7ac9-4c00-8062-52e6f1f969cb
-- title:
--   THDM: the potential in the variables $(K_0,k)$ and the functions $f,f',g,I$
-- statement:
--   The general THDM potential written in gauge-invariant variables, together with the notions used in the stability analysis of Section 4 of arXiv:hep-ph/0605184.
--
--   With $k=K/K_0$ one has $J_2(k)=\xi_0+\xi^{\mathsf T}k$ (4.2) and $J_4(k)=\eta_{00}+2\eta^{\mathsf T}k+k^{\mathsf T}Ek$ (4.3), so that the potential is $V(K_0,k)=K_0J_2(k)+K_0^2J_4(k)$ on the domain $K_0\ge0$, $|k|\le1$. **Stability** means that $V$ is bounded from below on that domain. Stability *in the strong sense* (4.4) is $J_4>0$ on the closed unit ball; *in the weak sense* (4.7) it is $J_4>0$, or $J_4=0$ together with $J_2>0$, at every point of the ball; the *marginal case* is the variant with $J_2\ge0$ in which $J_4=J_2=0$ actually occurs. The region $B_3$ of (4.9) and the condition that the quartic part vanishes identically are also recorded.
--
--   The stability-determining functions are $f(u)=u+\eta_{00}-\eta^{\mathsf T}(E-u)^{-1}\eta$ (4.19), $f'(u)=1-\eta^{\mathsf T}(E-u)^{-2}\eta$ (4.20) and $g(u)=\xi_0-\xi^{\mathsf T}(E-u)^{-1}\eta$ (4.40). Since these formulas are meaningful only where $E-u$ is invertible, each function is paired with a value function that evaluates the formula at regular $u$ and takes the limit at an eigenvalue of $E$. The set $I$ of (4.38) collects the regular $u$ with $f'(u)=0$, the point $u=0$ when it is regular with $f'(0)>0$, and the eigenvalues of $E$ at which $f$ and $f'$ have finite limits with $f'\ge0$. Finally, $\xi_\perp(\mu)$ of (4.44) is characterised as the orthogonal projection of $\xi$ onto the eigenspace of $E$ for the eigenvalue $\mu$.
-- source:
--   M. Maniatis, A. von Manteuffel, O. Nachtmann, F. Nagel, 'Stability and Symmetry Breaking in the General Two-Higgs-Doublet Model', Eur. Phys. J. C 48 (2006) 805-823, arXiv:hep-ph/0605184v3, https://arxiv.org/abs/hep-ph/0605184, Sect. 4 (eqs. 4.1-4.9, 4.19, 4.20, 4.38, 4.40, 4.44)

import Definitions.Def_THDM_basic

/-!
# The THDM potential in the gauge-invariant variables, and the stability functions

Notions from Sections 3 and 4 of arXiv:hep-ph/0605184.
-/

open scoped BigOperators
open Matrix

namespace THDM

/-! ### The potential -/

/-- `J₂(k) = ξ₀ + ξᵀ k`, see (4.2). -/
def J2 (xi0 : ℝ) (xi k : Fin 3 → ℝ) : ℝ := xi0 + dot3 xi k

/-- `J₄(k) = η₀₀ + 2 ηᵀ k + kᵀ E k`, see (4.3). -/
def J4 (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 3 → ℝ) : ℝ :=
  eta00 + 2 * dot3 eta k + quad3 E k k

/-- The potential written in the gauge-invariant variables `(K₀, k)`, `k = K/K₀`:
`V(K₀, k) = K₀ J₂(k) + K₀² J₄(k)`, see (3.12) with (4.1)–(4.3). -/
def Vpot (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (k0 : ℝ) (k : Fin 3 → ℝ) : ℝ :=
  k0 * J2 xi0 xi k + k0 ^ 2 * J4 eta00 eta E k

/-- Stability of the potential: `V` is bounded from below on its physical domain
`K₀ ≥ 0`, `|k| ≤ 1`. -/
def Stable (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∃ C : ℝ, ∀ k0 : ℝ, ∀ k ∈ ballK, 0 ≤ k0 → C ≤ Vpot xi0 xi eta00 eta E k0 k

/-- Stability in the strong sense (4.4): `J₄(k) > 0` for all `|k| ≤ 1`. -/
def StrongStable (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ k ∈ ballK, 0 < J4 eta00 eta E k

/-- Stability in the weak sense (4.7): for every `|k| ≤ 1` either `J₄(k) > 0`, or
`J₄(k) = 0` and `J₂(k) > 0`. -/
def WeakStable (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ k ∈ ballK, 0 < J4 eta00 eta E k ∨ (J4 eta00 eta E k = 0 ∧ 0 < J2 xi0 xi k)

/-- The marginal case (b.4): for every `|k| ≤ 1` either `J₄(k) > 0`, or `J₄(k) = 0`
and `J₂(k) ≥ 0`, while `J₄(k) = J₂(k) = 0` happens for at least one such `k`. -/
def MarginalCase (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  (∀ k ∈ ballK, 0 < J4 eta00 eta E k ∨ (J4 eta00 eta E k = 0 ∧ 0 ≤ J2 xi0 xi k)) ∧
    (∃ k ∈ ballK, J4 eta00 eta E k = 0 ∧ J2 xi0 xi k = 0)

/-- The region `B₃ = {k ; |k| ≤ 1, J₄(k) > 0, J₂(k) < 0}` of (4.9). -/
def B3region (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) : Set (Fin 3 → ℝ) :=
  {k | k ∈ ballK ∧ 0 < J4 eta00 eta E k ∧ J2 xi0 xi k < 0}

/-- The quartic part of the potential vanishes identically. -/
def V4Trivial (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  eta00 = 0 ∧ eta = 0 ∧ E = 0

/-! ### The functions `f`, `f'` and `g`, and the set `I` -/

/-- `u` is a regular value, i.e. `det (E - u · 1) ≠ 0`. -/
def Reg (E : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) : Prop :=
  IsUnit (E - u • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det

/-- The resolvent `(E - u)⁻¹`.  At a non-regular `u` the Mathlib inverse returns the
zero matrix, so this expression is only meaningful for regular `u`. -/
noncomputable def resolv (E : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (E - u • (1 : Matrix (Fin 3) (Fin 3) ℝ))⁻¹

/-- `f(u) = u + η₀₀ - ηᵀ (E - u)⁻¹ η`, see (4.19). -/
noncomputable def fFun (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ)
    (u : ℝ) : ℝ :=
  u + eta00 - dot3 eta (resolv E u *ᵥ eta)

/-- `f'(u) = 1 - ηᵀ (E - u)⁻² η`, see (4.20). -/
noncomputable def fPrime (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) : ℝ :=
  1 - dot3 eta ((resolv E u * resolv E u) *ᵥ eta)

/-- `g(u) = ξ₀ - ξᵀ (E - u)⁻¹ η`, see (4.40). -/
noncomputable def gFun (xi0 : ℝ) (xi eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ)
    (u : ℝ) : ℝ :=
  xi0 - dot3 xi (resolv E u *ᵥ eta)

open Classical in
/-- The limit of a real function `F` at `u` along the punctured neighbourhood
`{u}ᶜ` of `u`, if such a limit exists, and `0` otherwise.  This is used below to give
`f`, `f'` and `g` a value at the eigenvalues of `E`, where the formulas (4.19), (4.20)
and (4.40) are not directly applicable. -/
noncomputable def punctLim (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  if h : ∃ L : ℝ, Filter.Tendsto F (nhdsWithin u {u}ᶜ) (nhds L) then h.choose else 0

open Classical in
/-- The value of `f` at `u`: the value of the formula (4.19) at a regular `u`, and the
limit of `f` at `u` when `u` is an eigenvalue of `E` at which `f` stays finite.  (If no
such limit exists the value is unspecified, namely `0`.) -/
noncomputable def fVal (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ)
    (u : ℝ) : ℝ :=
  if Reg E u then fFun eta00 eta E u
  else punctLim (fFun eta00 eta E) u

open Classical in
/-- The value of `f'` at `u`, defined like `fVal`. -/
noncomputable def fPrimeVal (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) : ℝ :=
  if Reg E u then fPrime eta E u
  else punctLim (fPrime eta E) u

open Classical in
/-- The value of `g` at `u`, defined like `fVal`. -/
noncomputable def gVal (xi0 : ℝ) (xi eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ)
    (u : ℝ) : ℝ :=
  if Reg E u then gFun xi0 xi eta E u
  else punctLim (gFun xi0 xi eta E) u

/-- The set `I` of (4.38): all regular `u` with `f'(u) = 0`; the point `u = 0` if it is
regular and `f'(0) > 0`; and every eigenvalue `μ` of `E` at which `f` and `f'` have
finite limits with `f'(μ) ≥ 0`. -/
noncomputable def Iset (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) :
    Set ℝ :=
  {u | Reg E u ∧ fPrime eta E u = 0} ∪
  {u | u = 0 ∧ Reg E 0 ∧ 0 < fPrime eta E 0} ∪
  {u | ¬ Reg E u ∧
        (∃ L : ℝ, Filter.Tendsto (fFun eta00 eta E) (nhdsWithin u {u}ᶜ) (nhds L)) ∧
        (∃ L : ℝ, Filter.Tendsto (fPrime eta E) (nhdsWithin u {u}ᶜ) (nhds L)) ∧
        0 ≤ fPrimeVal eta E u}

/-- `p` is the orthogonal projection `ξ⊥(μ)` of `ξ` onto the eigenspace of `E` for the
eigenvalue `μ`, see (4.44): `p` lies in that eigenspace and `ξ - p` is orthogonal to it. -/
def IsEigenProj (E : Matrix (Fin 3) (Fin 3) ℝ) (mu : ℝ) (xi p : Fin 3 → ℝ) : Prop :=
  (E - mu • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ p = 0 ∧
    ∀ w : Fin 3 → ℝ, (E - mu • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ w = 0 → dot3 (xi - p) w = 0

end THDM


