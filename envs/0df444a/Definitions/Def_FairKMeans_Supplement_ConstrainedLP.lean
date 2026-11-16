-- Prove2me | Definitions.Def_FairKMeans_Supplement_ConstrainedLP
-- name    : FairKMeans_Supplement_ConstrainedLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:59:37.418491+00:00
-- url     : https://prove2.me/theorems/4c396507-a0f7-424f-bf8e-eac4811dff1e
-- title:
--   Weighted relaxed-solution quantities and the two linear programs with constraints (40)
-- statement:
--   For an instance with homogeneous cluster constraints and a fractional assignment $\phi$ of $P$ to a candidate family $T$, the quantities of Algorithm 1 are taken in their weighted form (Remark 44): the cluster weight $w(t)=\sum_p w(p)\phi(p,t)$, the centroid $\pi(t)=w(t)^{-1}\sum_p w(p)\phi(p,t)\,p$, the weighted mean $\nu_p=\sum_t\phi(p,t)\pi(t)$ (unchanged, since rows sum to one), $C_T=\sum_p\sum_t w(p)\phi(p,t)\|p-\pi(t)\|^2$, $C_\nu=\sum_p w(p)\|p-\nu_p\|^2$, the linearized cost
--
--   $$L(\phi')=C_{T'}+2\lambda\sum_p w(p)\,(\nu_p-p)^\top(\nu_p(\phi')-p),\qquad\lambda=\frac{\rho}{1+\rho},$$
--
--   and the shifted points $u_p=\lambda(\nu_p-p)$, $p_\lambda=p-u_p$.
--
--   The two linear programs read "fair" as "feasible": the **feasible assignment LP** of a center family (minimize the weighted cost over feasible fractional assignments) and **LP (29)**: minimize $\sum_{c}z_c$ over fractional assignments $\phi$ to $T'$ satisfying (40) for every column and $z_c\ge\sum_p w(p)\phi(p,c)(\|p_\lambda-c\|^2-\|u_p-v\|^2)$ for all $c\in T'$, $v\in V$. An exact LP oracle returns an optimal solution whenever one exists. The feasible assignment LP of $s$ centers has $ns$ variables and $n+ns+rs$ constraints; LP (29) with $|T'|=s$, $|V|=v$ has $(n+1)s$ variables and $n+ns+sv+rs$ constraints.
--
--   **Formalization Note** The centroid of a zero column is Lean's junk value $0$, always multiplied by a zero entry. The oracle types are the published ones of `FairKMeans.LPOracles`; constraint counts include the nonnegativity constraints.
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), (18)–(23), p.22 (PDF p.24); (26), p.23 (PDF p.25); LP (29), p.24 (PDF p.26); proof of Theorem 32, pp.37–38 (PDF pp.39–40); Remark 44, p.48 (PDF p.50); LP sizes, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_RelaxedSolution
import Definitions.Def_FairKMeans_LPOracles
import Definitions.Def_FairKMeans_Supplement_Constrained

namespace FairKMeans.Supplement

/-!
# Weighted relaxed solutions and the two linear programs, for homogeneous cluster constraints

Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…): the quantities
(18)–(23), p.22 (PDF 24), and (26), p.23 (PDF 25), in the weighted form of Remark 44, p.48
(PDF 50); the fair assignment LP (Definition 12, p.18, PDF 20) and LP (29) (p.24, PDF 26) with
the constraints (40) in place of fairness (proof of Theorem 32, p.37, PDF 39); their sizes
(proof of Proposition 29, p.36, PDF 38, with `2m` replaced by `r`, p.38, PDF 40).

**Formalization Note.** Remark 44: every summand over input points is multiplied by `w(p)`:
`w(t) = ∑_p w(p) φ(p,t)`, `π(t) = w(t)⁻¹ ∑_p w(p) φ(p,t) p`, `C_T`, `C_ν`, the linearized
cost `L`, the objective of the assignment LP and the `z`-constraints of LP (29). The weighted
mean `ν_p = ∑_t φ(p,t) π(t)` is unchanged (rows still sum to one), and so are `u_p` and `p_λ`,
which involve no sum over points. The centroid of a zero column is Lean's junk value
`0⁻¹ • 0 = 0`, always multiplied by a zero entry. The oracle types are the published
`FairLPOracle` and `LP29Oracle`; their specifications are new: "returns an optimal solution
whenever an optimal solution exists". Sizes count variables and constraints, nonnegativity
included; copying the coefficients `a_j(p)` is not arithmetic.
-/

open FairKMeans

variable {d n r : ℕ}

/-- The weight `w(t) = ∑_p w(p) φ(p,t)` of the fragment cluster of `t` ((11) weighted). -/
def hclusterWeight {s : ℕ} (I : HInstance d n r) (φ : Fin n → Fin s → ℝ) (t : Fin s) : ℝ :=
  ∑ p, I.w p * φ p t

/-- The weighted centroid `π(t) = (1/w(t)) ∑_p w(p) φ(p,t) p` ((18), Remark 44). -/
noncomputable def hcen {s : ℕ} (I : HInstance d n r) (φ : Fin n → Fin s → ℝ) (t : Fin s) :
    E d :=
  (hclusterWeight I φ t)⁻¹ • ∑ p, (I.w p * φ p t) • I.pts p

/-- The weighted mean `ν_p = ∑_t φ(p,t) π(t)` ((19); unchanged by weights, Remark 44). -/
noncomputable def hnu {s : ℕ} (I : HInstance d n r) (φ : Fin n → Fin s → ℝ) (p : Fin n) : E d :=
  ∑ t, φ p t • hcen I φ t

/-- `C_T = ∑_p ∑_t w(p) φ(p,t) ‖p − π(t)‖²` ((20), weighted). -/
noncomputable def hCT {s : ℕ} (I : HInstance d n r) (φ : Fin n → Fin s → ℝ) : ℝ :=
  ∑ p, ∑ t, I.w p * φ p t * ‖I.pts p - hcen I φ t‖ ^ 2

/-- The drift `C_ν = ∑_p w(p) ‖p − ν_p‖²` ((21), weighted). -/
noncomputable def hCnu {s : ℕ} (I : HInstance d n r) (φ : Fin n → Fin s → ℝ) : ℝ :=
  ∑ p, I.w p * ‖I.pts p - hnu I φ p‖ ^ 2

/-- The linearized cost at `φ` of `φ'` ((23), weighted):
`L(φ') = C_{T'} + 2λ ∑_p w(p) (ν_p − p)ᵀ(ν_p(φ') − p)`. -/
noncomputable def hlinCost {s s' : ℕ} (I : HInstance d n r) (ρ : ℝ) (φ : Fin n → Fin s → ℝ)
    (φ' : Fin n → Fin s' → ℝ) : ℝ :=
  hCT I φ' + 2 * lam ρ * ∑ p, I.w p * inner ℝ (hnu I φ p - I.pts p) (hnu I φ' p - I.pts p)

/-- `u_p = λ (ν_p − p)` ((26)). -/
noncomputable def huvec {s : ℕ} (I : HInstance d n r) (ρ : ℝ) (φ : Fin n → Fin s → ℝ)
    (p : Fin n) : E d :=
  lam ρ • (hnu I φ p - I.pts p)

/-- The shifted point `p_λ = p − u_p` ((26)). -/
noncomputable def hplam {s : ℕ} (I : HInstance d n r) (ρ : ℝ) (φ : Fin n → Fin s → ℝ)
    (p : Fin n) : E d :=
  I.pts p - huvec I ρ φ p

/-- The feasible-assignment LP oracle solves the LP of every center family exactly whenever it
has an optimal solution. -/
def IsHLPOracle (I : HInstance d n r) (O : FairLPOracle d n) : Prop :=
  ∀ (s : ℕ) (S : Fin s → E d), (∃ φ, IsOptFeasAssign I S φ) → IsOptFeasAssign I S (O s S)

/-- `(φ, z)` is feasible for the weighted LP (29) with constraints (40): rows sum to one,
entries nonnegative, `z_c ≥ ∑_p w(p) φ(p,c)(‖p_λ − c‖² − ‖u_p − v‖²)` for all `c ∈ T'`,
`v ∈ V`, and (40) for every column. -/
def IsHLP29Feasible {s v : ℕ} (I : HInstance d n r) (pl u : Fin n → E d) (T' : Fin s → E d)
    (V : Fin v → E d) (φ : Fin n → Fin s → ℝ) (z : Fin s → ℝ) : Prop :=
  IsAssignment φ ∧
    (∀ (c : Fin s) (b : Fin v),
      ∑ p, I.w p * φ p c * (‖pl p - T' c‖ ^ 2 - ‖u p - V b‖ ^ 2) ≤ z c) ∧
    IsFeasible I φ

/-- `(φ, z)` is an optimal solution of the weighted LP (29): feasible and minimizing `∑_c z_c`. -/
def IsHLP29Optimal {s v : ℕ} (I : HInstance d n r) (pl u : Fin n → E d) (T' : Fin s → E d)
    (V : Fin v → E d) (φ : Fin n → Fin s → ℝ) (z : Fin s → ℝ) : Prop :=
  IsHLP29Feasible I pl u T' V φ z ∧
    ∀ (φ' : Fin n → Fin s → ℝ) (z' : Fin s → ℝ), IsHLP29Feasible I pl u T' V φ' z' →
      ∑ c, z c ≤ ∑ c, z' c

/-- The LP (29) oracle returns an optimal solution of the weighted LP (29) whenever one exists. -/
def IsHLP29Oracle (I : HInstance d n r) (O : LP29Oracle d n) : Prop :=
  ∀ (s v : ℕ) (pl u : Fin n → E d) (T' : Fin s → E d) (V : Fin v → E d),
    (∃ φ z, IsHLP29Optimal I pl u T' V φ z) →
      IsHLP29Optimal I pl u T' V (O s v pl u T' V).1 (O s v pl u T' V).2

/-- (variables, constraints) of the feasible assignment LP of `s` centers: `n·s` variables;
`n` row, `n·s` nonnegativity and `r·s` constraints (40). -/
def hLPSize (n r s : ℕ) : ℕ × ℕ := (n * s, n + n * s + r * s)

/-- (variables, constraints) of LP (29) with `|T'| = s`, `|V| = v`: `(n+1)·s` variables;
`n` row, `n·s` nonnegativity, `s·v` `z`-constraints and `r·s` constraints (40). -/
def hlp29Size (n r s v : ℕ) : ℕ × ℕ := ((n + 1) * s, n + n * s + s * v + r * s)

end FairKMeans.Supplement


