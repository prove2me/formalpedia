-- Prove2me | Definitions.Def_QuasilinearAG_Encoding_Fibre
-- name    : QuasilinearAG_Encoding_Fibre
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:40:59.489195+00:00
-- url     : https://prove2.me/theorems/472c3213-e9bd-49ca-887d-b32c99068daa
-- title:
--   The root algebra $k[Z]/(Z^{Q_*}-\tau)$, fibre paths (A1.2), root levels (4.3) and the fibre matrix $U_h$ (4.4) for an ambient extraction count $\kappa$
-- statement:
--   Fix $q$, the field $k$, an extraction count $\kappa\ge0$, $Q_*=q^\kappa$, a good base value $\beta$ and $\tau=L(\beta)=\beta^q+\beta$.
--
--   - The **root algebra** is $\mathcal A=k[Z]/(Z^{Q_*}-\tau)$ (4.2); $\operatorname{coeff}_{Z^0}$ is the coefficient of $Z^0$ in the unique representative of degree $<Q_*$.
--   - $\phi(d)=d^q(1+d^{q-1})^{-1}$ in $\mathcal A$, and $\phi(\alpha)=\alpha^q/(1+\alpha^{q-1})$ in $k$.
--   - **Paths** (A1.2): with $\theta\in k$, $\theta^q+\theta=1$, and an enumeration $\omega(0),\dots,\omega(q-1)$ of $C=\ker(X^q+X)$, the children of $\alpha$ are $\theta\phi(\alpha)+\omega(c)$, $c<q$. The path with index $v<q^h$ has $\alpha_0=\beta$ and $\alpha_{i+1}=\theta\phi(\alpha_i)+\omega(c_{i+1})$, where $c_{i+1}$ is the base-$q$ digit $i$ of $v$ (first digit least significant, so the last branch label changes slowest).
--   - **Root levels** (4.3): $d_{i,0}=\alpha_i$; $d_{0,l}=Z^{Q_*/q^l}-d_{0,l-1}$ and $d_{i,l}=\phi(d_{i-1,l})-d_{i,l-1}$ for $1\le l\le\kappa$.
--   - The **fibre matrix** $U_h$ is the $D\times D$ matrix, $D=q^h$, with
--   $$U_h[v,u]=\operatorname{coeff}_{Z^0}\prod_{i=1}^h d_{i,\kappa}(P_v)^{a_i(u)},$$
--   where $a_i(u)$ is the base-$q$ digit $i-1$ of $u$ (4.4): coefficient vectors are ordered with the last digit changing slowest.
--
--   For the extraction count of (3.2) this is the matrix $U_\beta$ of (3.5) in the path order; Proposition 4.2 concerns it for an arbitrary ambient $\kappa$.
--
--   **Formalization Note** The inverse of $1+d^{q-1}$ is `Ring.inverse`, the true inverse whenever the element is a unit; on the values used it is (its residue is $1+\alpha^{q-1}\neq0$, p. 12). $\theta$ and the enumeration $\omega$ are parameters: the paper fixes some deterministic choice, and the statements hold for every admissible one.
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), §4.1 pp. 12–13 (PDF 14–15), (4.2)–(4.4); §A1.1 p. 44 (PDF 46), (A1.2); §5.3 p. 20 (PDF 22); §A3 p. 50 (PDF 52)

import Mathlib

namespace QuasilinearAG.Encoding

/-!
# The root algebra, fibre paths and the fibre matrix `U_h` for an ambient extraction count `κ`

Chao, Liu, Li, Ma, Wang, *Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier
Bases*, STOC 2027 submission (manuscript sha256 355c15dc…), §4.1 pp. 12–13 (PDF 14–15), (4.2)–(4.4);
§A1.1 p. 44 (PDF 46), (A1.2); §5.3 p. 20 (PDF 22) and §A3 p. 50 (PDF 52) for the orders.

Fix `q`, the field `k` (`F_{q²}` in the paper), a good base value `β` (`L(β) = β^q + β ≠ 0`),
an extraction count `κ ≥ 0`, `Q* = q^κ` and `τ = L(β)`.

* `RootAlg Qs τ = A = k[Z]/(Z^{Q*} - τ)` (4.2), and `coeff0 a` is the coefficient of `Z⁰` in the
  unique representative of degree `< Q*` ("constant coefficient", p. 12).
* `phiRoot q d = ϕ(d) = d^q (1 + d^{q-1})⁻¹` in `A` (`Ring.inverse`; on the values used the
  denominator is a unit, p. 12).
* `phiK q α = ϕ(α) = α^q/(1 + α^{q-1})` in `k`.
* Paths (A1.2): the children of `α` are `θ ϕ(α) + γ`, `γ ∈ C = ker(X^q + X)`, listed as
  `θ ϕ(α) + ω c` for `c < q`, where `θ^q + θ = 1` and `ω : Fin q → k` enumerates `C`.
  `pathVal q θ ω β v i = α_i` for the path with index `v`, whose branch label at level `i + 1` is
  the base-`q` digit `i` of `v` (first digit least significant, so the last branch label changes
  slowest; §5.3, §A3).
* `rootLevels q κ τ θ ω β v i l = d_{i,l}` of (4.3): `d_{i,0} = α_i`,
  `d_{0,l} = Z^{Q*/q^l} - d_{0,l-1}`, `d_{i,l} = ϕ(d_{i-1,l}) - d_{i,l-1}`.
* `fibreMatrix q κ θ ω β h` is the `D × D` matrix `U_h` (`D = q^h`): row `v` (a path), column `u`
  (the monomial whose exponent of `x_i` is digit `i - 1` of `u`), entry
  `coeff_{Z⁰} Π_{i=1}^h d_{i,κ}^{a_i}` (4.4).
-/

variable {k : Type*} [Field k]

/-- `Z^{Q*} - τ`. -/
noncomputable def rootPoly (Qs : ℕ) (τ : k) : Polynomial k :=
  Polynomial.X ^ Qs - Polynomial.C τ

/-- The root algebra `A = k[Z]/(Z^{Q*} - τ)`. -/
abbrev RootAlg (Qs : ℕ) (τ : k) := AdjoinRoot (rootPoly Qs τ)

/-- The coefficient of `Z⁰` in the representative of degree `< Q*`. -/
noncomputable def coeff0 {Qs : ℕ} {τ : k} (a : RootAlg Qs τ) : k := by
  classical
  exact if hm : (rootPoly Qs τ).Monic then (AdjoinRoot.modByMonicHom hm a).coeff 0 else 0

/-- `ϕ(d) = d^q (1 + d^{q-1})⁻¹` in a commutative ring. -/
noncomputable def phiRoot {R : Type*} [CommRing R] (q : ℕ) (d : R) : R :=
  d ^ q * Ring.inverse (1 + d ^ (q - 1))

/-- `ϕ(α) = α^q / (1 + α^{q-1})` in `k`. -/
noncomputable def phiK (q : ℕ) (α : k) : k := α ^ q / (1 + α ^ (q - 1))

/-- The base-`q` digit `i` of `v` (digit `0` least significant). -/
def digit (q v i : ℕ) : ℕ := v / q ^ i % q

/-- The branch value for label `c`: `ω c` for `c < q`. -/
def branchVal {q : ℕ} (ω : Fin q → k) (c : ℕ) : k :=
  if hc : c < q then ω ⟨c, hc⟩ else 0

/-- `α_i` on the path with index `v` above `β`: `α_0 = β`,
`α_{i+1} = θ ϕ(α_i) + ω(digit i of v)`. -/
noncomputable def pathVal (q : ℕ) (θ : k) (ω : Fin q → k) (β : k) (v : ℕ) : ℕ → k
  | 0 => β
  | i + 1 => θ * phiK q (pathVal q θ ω β v i) + branchVal ω (digit q v i)

/-- The levels `d_{0,l}`: `d_{0,0} = β`, `d_{0,l+1} = Z^{q^{κ-(l+1)}} - d_{0,l}`. -/
noncomputable def rootRow0 (q κ : ℕ) (τ β : k) : ℕ → RootAlg (q ^ κ) τ
  | 0 => algebraMap k _ β
  | l + 1 => AdjoinRoot.root (rootPoly (q ^ κ) τ) ^ (q ^ (κ - (l + 1))) - rootRow0 q κ τ β l

/-- The levels `d_{i,l}` of a coordinate with value `α`, from the levels `prev` of the previous
coordinate: `d_{i,0} = α`, `d_{i,l+1} = ϕ(d_{i-1,l+1}) - d_{i,l}`. -/
noncomputable def rootRowNext {Qs : ℕ} {τ : k} (q : ℕ) (prev : ℕ → RootAlg Qs τ) (α : k) :
    ℕ → RootAlg Qs τ
  | 0 => algebraMap k _ α
  | l + 1 => phiRoot q (prev (l + 1)) - rootRowNext q prev α l

/-- `d_{i,l}` (4.3) on the path with index `v` above `β`, with `τ = L(β)`. -/
noncomputable def rootLevels (q κ : ℕ) (θ : k) (ω : Fin q → k) (β : k) (v : ℕ) :
    ℕ → ℕ → RootAlg (q ^ κ) (β ^ q + β)
  | 0 => rootRow0 q κ (β ^ q + β) β
  | i + 1 => rootRowNext q (rootLevels q κ θ ω β v i) (pathVal q θ ω β v (i + 1))

/-- The fibre matrix `U_h` (4.4) for the ambient extraction count `κ`: entry `(v, u)` is
`coeff_{Z⁰} Π_{i=1}^h d_{i,κ}(P_v)^{a_i(u)}`, `a_i(u)` the digit `i - 1` of `u`. -/
noncomputable def fibreMatrix (q κ : ℕ) (θ : k) (ω : Fin q → k) (β : k) (h : ℕ) :
    Matrix (Fin (q ^ h)) (Fin (q ^ h)) k :=
  fun v u => coeff0 (∏ i ∈ Finset.range h,
    rootLevels q κ θ ω β v (i + 1) κ ^ digit q u i)

end QuasilinearAG.Encoding


