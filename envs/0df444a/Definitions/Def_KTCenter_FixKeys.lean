-- Prove2me | Definitions.Def_KTCenter_FixKeys
-- name    : KTCenter_FixKeys
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:43.199443+00:00
-- url     : https://prove2.me/theorems/bcc7fa43-2a37-4418-a6c4-7274a7261491
-- title:
--   §5.3 FixKeys: $\gamma,\kappa,\ell,\theta$, the fixed set $F$, residual blocks $\mathcal B^\prime$, small/large blocks and the cost $\tilde C^\varphi_i$
-- statement:
--   For a cost instance and a rational $0<\xi<1$, (28) sets
--
--   $$\gamma=\xi/2,\quad \kappa=\min\{1,\gamma/C_0\},\quad \ell=\lceil\log_2(20(n+1))\rceil,\quad \theta=\frac{\gamma^2W}{4C_1\ell},\quad F=\{v\in U:\lambda_v>\theta\}.$$
--
--   Let $U'=U\setminus F$, $\mathcal B'=\{B\setminus F:B\in\mathcal B,\ B\setminus F\ne\emptyset\}$, $L_B=\sum_{v\in B}\lambda_v$, $\mathcal B_s=\{B\in\mathcal B':L_B\le\theta\}$ and $\mathcal B_\ell=\{B\in\mathcal B':L_B>\theta\}$. For $\varphi\in\mathcal P(F)$ and $p'\in\mathcal P(U')$, $\varphi\cup p'$ is the combined assignment; (29)–(31) define $A'_i=A_i+\sum_{v\in F}u_{iv}(\varphi_v)+\sum_{u<v\in F}q_i(u,\varphi_u,v,\varphi_v)$, $u'_{iv}(a)=u_{iv}(a)+\sum_{u\in F}q_i(v,a,u,\varphi_u)$ and
--
--   $$\tilde C^\varphi_i(p')=A'_i+\sum_{v\in U'}u'_{iv}(p'_v)+\sum_{B\in\mathcal B'}\sum_{\substack{u,v\in B\\u<v}}q_i(u,p'_u,v,p'_v).$$
--
--   Fixing the few influential keys $F$ by enumeration leaves only keys of small individual effect.
--
--   **Formalization Note** $\lceil\log_2 x\rceil$ for a natural number is `Nat.clog 2`. Assignments on a subset are dependent functions on its subtype.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), §5.3, eqs. (28)–(31), pp.37–38 (PDF pp.39–40)

import Mathlib
import Definitions.Def_KTCenter_CostInstance

namespace KTCenter

namespace CostInstance

variable {K : ℕ} {C₀ C₁ : ℚ} (I : CostInstance K C₀ C₁) (ξ : ℚ)

/-- `γ = ξ/2`, eq. (28), p.37 (PDF p.39).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…), §5.3. -/
def gamma (ξ : ℚ) : ℚ := ξ / 2

/-- `κ = min{1, γ/C₀}`, eq. (28). -/
def kappa (_I : CostInstance K C₀ C₁) (ξ : ℚ) : ℚ := min 1 (gamma ξ / C₀)

/-- `ℓ = ⌈log₂(20(n + 1))⌉`, eq. (28). -/
def ell : ℕ := Nat.clog 2 (20 * (I.n + 1))

/-- `θ = γ²W/(4C₁ℓ)`, eq. (28). -/
def theta : ℚ := gamma ξ ^ 2 * I.W / (4 * C₁ * (I.ell : ℚ))

/-- `F = {v ∈ U : λ_v > θ}`, eq. (28). -/
def F : Finset (Fin I.N) := Finset.univ.filter fun v => I.theta ξ < I.lam v

/-- `U′ = U \ F`, p.37. -/
def Ures : Finset (Fin I.N) := (I.F ξ)ᶜ

/-- `ℬ′ = {B \ F : B ∈ ℬ, B \ F ≠ ∅}`, p.37. -/
def blocksRes : Finset (Finset (Fin I.N)) :=
  (I.blocks.image fun B => B \ I.F ξ).filter fun B => B.Nonempty

/-- `L_B = Σ_{v∈B} λ_v`, p.37. -/
def LB (B : Finset (Fin I.N)) : ℚ := ∑ v ∈ B, I.lam v

/-- The small subsets `ℬ_s = {B ∈ ℬ′ : L_B ≤ θ}`, p.37. -/
def bSmall : Finset (Finset (Fin I.N)) := (I.blocksRes ξ).filter fun B => I.LB B ≤ I.theta ξ

/-- The large subsets `ℬ_ℓ = {B ∈ ℬ′ : L_B > θ}`, p.37. -/
def bLarge : Finset (Finset (Fin I.N)) := (I.blocksRes ξ).filter fun B => I.theta ξ < I.LB B

/-- `𝒫(A)`, p.37: the assignments on `A ⊆ U`, as key indices. -/
abbrev AssignOn (A : Finset (Fin I.N)) : Type := (v : {v // v ∈ A}) → Fin (I.k v)

/-- `φ ∪ p′`, p.37: the assignment on `U` giving `φ_v` on `F` and `p′_v` on `U′`. -/
def union (φ : I.AssignOn (I.F ξ)) (p' : I.AssignOn (I.Ures ξ)) : I.Assign := fun v =>
  if h : v ∈ I.F ξ then φ ⟨v, h⟩ else p' ⟨v, by simpa [Ures] using h⟩

/-- `A′ᵢ`, eq. (29), p.37: `Aᵢ + Σ_{v∈F} uᵢᵥ(φ_v) + Σ_{u<v in F} qᵢ(u, φ_u, v, φ_v)`. -/
def Aprime (φ : I.AssignOn (I.F ξ)) (i : Fin I.n) : ℚ :=
  I.A i + ∑ v : {v // v ∈ I.F ξ}, I.u i v (φ v) +
    ∑ x ∈ Finset.univ.filter (fun x : {v // v ∈ I.F ξ} × {v // v ∈ I.F ξ} => x.1.1 < x.2.1),
      I.q i x.1 (φ x.1) x.2 (φ x.2)

/-- `u′ᵢᵥ(a)`, eq. (30), p.38 (PDF p.40): `uᵢᵥ(a) + Σ_{u∈F} qᵢ(v, a, u, φ_u)`. -/
def uprime (φ : I.AssignOn (I.F ξ)) (i : Fin I.n) (v : Fin I.N) (a : Fin (I.k v)) : ℚ :=
  I.u i v a + ∑ u : {v // v ∈ I.F ξ}, I.q i v a u (φ u)

/-- `C̃^φᵢ(p′)`, eq. (31), p.38:
`A′ᵢ + Σ_{v∈U′} u′ᵢᵥ(p′_v) + Σ_{B∈ℬ′} Σ_{u<v in B} qᵢ(u, p′_u, v, p′_v)`.

**Formalization Note.** The inner pair sum runs over `U′ × U′` with both components in `B`, since
`p′` is defined on `U′` and `B ⊆ U′`. -/
def costPhi (φ : I.AssignOn (I.F ξ)) (i : Fin I.n) (p' : I.AssignOn (I.Ures ξ)) : ℚ :=
  I.Aprime ξ φ i + ∑ v : {v // v ∈ I.Ures ξ}, I.uprime ξ φ i v (p' v) +
    ∑ B ∈ I.blocksRes ξ,
      ∑ x ∈ Finset.univ.filter (fun x : {v // v ∈ I.Ures ξ} × {v // v ∈ I.Ures ξ} =>
          x.1.1 ∈ B ∧ x.2.1 ∈ B ∧ x.1.1 < x.2.1),
        I.q i x.1 (p' x.1) x.2 (p' x.2)

end CostInstance

end KTCenter


